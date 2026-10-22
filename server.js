const express = require("express");
const http = require("http");
const crypto = require("crypto");
const fs = require("fs");
const path = require("path");
const multer = require("multer");
const { Server } = require("socket.io");

const PORT = process.env.PORT || 3000;
const app = express();
const server = http.createServer(app);
const io = new Server(server, {
  cors: { origin: "*", methods: ["GET", "POST"] },
});

// Default party rooms. The server also accepts state rooms (e.g. "state-texas")
// and any other sanitized room name, so the game can add rooms without a redeploy.
const DEFAULT_ROOMS = ["neon-club", "rooftop-lounge", "beach-bash", "game-arcade"];

function cleanRoomName(room) {
  const r = String(room || "")
    .toLowerCase()
    .replace(/[^a-z0-9-]/g, "")
    .slice(0, 40);
  return r || DEFAULT_ROOMS[0];
}

// socket.id -> { id, name, avatar, room, x, y, dancing, photoUrl }
const players = new Map();
// socket.id -> recent chat timestamps (spam protection)
const chatTimes = new Map();
// room -> live auction state (Whatnot-style bidding)
const auctions = new Map();

// ---------------------------------------------------------------------------
// Voice (walkie-talkie) signaling + floor control.
// Channels: "room:<room>" for public voice rooms (Chaos Room),
// "dm:<idA>:<idB>" (ids sorted) for matched-player talk.
// Floor: one talker per channel at a time. Matches are session-scoped.
// ---------------------------------------------------------------------------
const voiceFloors = new Map(); // channel -> socket.id holding the floor
const matches = new Set(); // "idA:idB" sorted, mutual matches

function dmKey(a, b) {
  return [String(a), String(b)].sort().join(":");
}
function channelMembers(channel) {
  if (channel.startsWith("room:")) {
    const room = channel.slice(5);
    return [...players.values()].filter((p) => p.room === room).map((p) => p.id);
  }
  if (channel.startsWith("dm:")) {
    return channel.slice(3).split(":");
  }
  return [];
}
function releaseFloorsHeldBy(socketId) {
  for (const [ch, holder] of voiceFloors) {
    if (holder !== socketId) continue;
    voiceFloors.delete(ch);
    const members = channelMembers(ch).filter((id) => id !== socketId);
    if (members.length)
      io.to(members).emit("voice-floor-released", { channel: ch, by: socketId });
  }
}

// Simple profanity filter. Extend this list as needed.
const BANNED_WORDS = [
  "fuck", "shit", "bitch", "asshole", "dick", "pussy",
  "cunt", "whore", "slut", "nigger", "faggot", "retard",
];

function cleanName(name) {
  return (
    String(name || "Guest").replace(/[<>&"']/g, "").trim().slice(0, 16) ||
    "Guest"
  );
}

function cleanAvatar(a) {
  const out = {};
  if (a && typeof a === "object") {
    for (const k of ["skin", "hair", "hairColor", "top", "bottom"]) {
      if (typeof a[k] === "string") out[k] = a[k].slice(0, 32);
    }
  }
  return out;
}

function filterProfanity(text) {
  let t = text;
  for (const w of BANNED_WORDS) {
    t = t.replace(new RegExp(w, "gi"), "***");
  }
  return t;
}

function roomState(room) {
  return [...players.values()].filter((p) => p.room === room);
}

// ---------------------------------------------------------------------------
// Profile photos: upload -> Railway Volume (disk) -> auto-moderation -> URL
//
// Setup (all in Railway):
//   1. party-server service -> Volumes -> New Volume, mount path: /data
//      (Without a volume, photos vanish on every redeploy.)
//   2. Variables -> PHOTO_DIR = /data/photos
//   HIVE_API_KEY   optional; free tier at thehive.ai for auto-moderation.
//                  Without it, uploads are accepted but logged as UNREVIEWED
//                  — point the report system somewhere you check.
// ---------------------------------------------------------------------------
const PHOTO_DIR = process.env.PHOTO_DIR || path.join(__dirname, "photos");
fs.mkdirSync(PHOTO_DIR, { recursive: true });
app.use("/photos", express.static(PHOTO_DIR));

// ---------------------------------------------------------------------------
// The Rizz Plaza game itself (static site in ./public) — served at the root
// so the custom domain (rizzplaza.com) opens the game directly. Also serves
// /audio/*.mp3 (the game's licensed music tracks live in public/audio).
// Registered before the plain-text "/" fallback below, which it shadows.
// ---------------------------------------------------------------------------
app.use(express.static(path.join(__dirname, "public")));

// ---------------------------------------------------------------------------
// Email/phone signups for reminders & special-event invites.
// Stored as JSON on the same volume as photos (survives redeploys).
// Sending itself is done separately (email/SMS provider) — this only collects.
// ---------------------------------------------------------------------------
app.use(express.json({ limit: "16kb" }));
app.use(express.urlencoded({ extended: false }));
const SUBSCRIBERS_FILE =
  process.env.SUBSCRIBERS_FILE ||
  path.join(path.dirname(PHOTO_DIR), "subscribers.json");
function readSubscribers() {
  try {
    const arr = JSON.parse(fs.readFileSync(SUBSCRIBERS_FILE, "utf8"));
    return Array.isArray(arr) ? arr : [];
  } catch {
    return [];
  }
}
function writeSubscribers(list) {
  fs.writeFileSync(SUBSCRIBERS_FILE, JSON.stringify(list, null, 2));
}
app.post("/api/subscribe", (req, res) => {
  const { email, phone, displayName, consent } = req.body || {};
  const em = String(email || "").trim().toLowerCase().slice(0, 120);
  const ph = String(phone || "").replace(/\D/g, "").slice(-10);
  if (!/^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(em))
    return res.status(400).json({ ok: false, error: "Invalid email" });
  if (ph.length !== 10)
    return res.status(400).json({ ok: false, error: "Invalid phone" });
  if (consent !== true)
    return res.status(400).json({ ok: false, error: "Consent required" });
  const list = readSubscribers();
  const now = new Date().toISOString();
  const existing = list.find((s) => s.email === em || s.phone === ph);
  if (existing) {
    existing.email = em;
    existing.phone = ph;
    existing.displayName = cleanName(displayName);
    existing.subscribed = true;
    existing.updatedAt = now;
  } else {
    list.push({
      email: em,
      phone: ph,
      displayName: cleanName(displayName),
      subscribed: true,
      createdAt: now,
      updatedAt: now,
    });
  }
  writeSubscribers(list);
  res.json({ ok: true });
});

// ---------------------------------------------------------------------------
// Help & Support messages from the in-app support sheet.
// Stored as JSON next to the subscribers file (same volume, survives
// redeploys) and mirrored to the server log, so the owner can read them in
// the Railway logs. The game also opens the sender's own email app addressed
// to the owner, so the message lands in the owner's inbox directly — this
// endpoint is the server-side copy of record.
// ---------------------------------------------------------------------------
const SUPPORT_FILE =
  process.env.SUPPORT_FILE ||
  path.join(path.dirname(PHOTO_DIR), "support-messages.json");
function readSupport() {
  try {
    const arr = JSON.parse(fs.readFileSync(SUPPORT_FILE, "utf8"));
    return Array.isArray(arr) ? arr : [];
  } catch {
    return [];
  }
}
app.post("/api/support", (req, res) => {
  const { name, email, category, message } = req.body || {};
  const nm = String(name || "").trim().slice(0, 80);
  const em = String(email || "").trim().toLowerCase().slice(0, 120);
  const cats = [
    "Question",
    "Something's broken",
    "Auction or store issue",
    "Account help",
    "Other",
  ];
  const cat = cats.includes(category) ? category : "Other";
  const msg = String(message || "").trim().slice(0, 2000);
  if (msg.length < 3)
    return res.status(400).json({ ok: false, error: "Message too short" });
  if (em && !/^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(em))
    return res.status(400).json({ ok: false, error: "Invalid email" });
  const entry = {
    name: nm,
    email: em,
    category: cat,
    message: msg,
    createdAt: new Date().toISOString(),
  };
  const list = readSupport();
  list.push(entry);
  while (list.length > 500) list.shift();
  try {
    fs.writeFileSync(SUPPORT_FILE, JSON.stringify(list, null, 2));
  } catch (e) {
    console.error("support save failed", e);
  }
  console.log(
    "[support]",
    entry.category,
    "|",
    entry.name || "(no name)",
    "|",
    entry.email || "(no email)",
    "|",
    entry.message.slice(0, 300)
  );
  res.json({ ok: true });
});

app.post("/api/unsubscribe", (req, res) => {
  const { email, phone } = req.body || {};
  const em = String(email || "").trim().toLowerCase();
  const ph = String(phone || "").replace(/\D/g, "").slice(-10);
  const list = readSubscribers();
  let changed = false;
  for (const s of list) {
    if ((em && s.email === em) || (ph && s.phone === ph)) {
      s.subscribed = false;
      s.updatedAt = new Date().toISOString();
      changed = true;
    }
  }
  if (changed) writeSubscribers(list);
  res.json({ ok: true });
});
// ---------------------------------------------------------------------------
// RP-V7.0: real server accounts + in-app reminders.
// Accounts live in accounts.json on the same volume as photos/subscribers
// (survives redeploys). Passwords are scrypt-hashed with per-user salts —
// plaintext is never stored or logged. Session tokens are 32 random bytes;
// only their sha256 is kept server-side. No new npm dependencies.
// ---------------------------------------------------------------------------
const ACCOUNTS_FILE =
  process.env.ACCOUNTS_FILE ||
  path.join(path.dirname(PHOTO_DIR), "accounts.json");
function emptyAccounts() {
  return { users: [], tokens: {} };
}
function readAccounts() {
  try {
    const d = JSON.parse(fs.readFileSync(ACCOUNTS_FILE, "utf8"));
    if (d && Array.isArray(d.users) && d.tokens && typeof d.tokens === "object")
      return d;
    return emptyAccounts();
  } catch {
    return emptyAccounts();
  }
}
function writeAccounts(db) {
  const tmp = ACCOUNTS_FILE + ".tmp";
  fs.writeFileSync(tmp, JSON.stringify(db, null, 2));
  fs.renameSync(tmp, ACCOUNTS_FILE);
}
function hashPassword(password, salt) {
  return crypto.scryptSync(String(password), salt, 64).toString("hex");
}
function newAccountToken(db, userId) {
  const token = crypto.randomBytes(32).toString("hex");
  const key = crypto.createHash("sha256").update(token).digest("hex");
  const now = Date.now();
  db.tokens[key] = {
    userId,
    createdAt: now,
    expiresAt: now + 90 * 24 * 3600 * 1000,
  };
  return token;
}
function accountForToken(db, req) {
  const h = String(req.headers.authorization || "");
  const m = h.match(/^Bearer\s+(.+)$/i);
  if (!m) return null;
  const key = crypto.createHash("sha256").update(m[1].trim()).digest("hex");
  const rec = db.tokens[key];
  if (!rec) return null;
  if (rec.expiresAt < Date.now()) {
    delete db.tokens[key];
    writeAccounts(db);
    return null;
  }
  return db.users.find((u) => u.id === rec.userId) || null;
}
function publicAccount(u) {
  return { id: u.id, name: u.name, email: u.email, phone: u.phone };
}
function ageFromDob(dob) {
  const parts = String(dob || "").split("-");
  const y = parseInt(parts[0], 10),
    m = parseInt(parts[1], 10),
    d = parseInt(parts[2], 10);
  const birth = new Date(y, m - 1, d);
  if (
    !y || !m || !d || isNaN(birth.getTime()) ||
    birth.getFullYear() !== y || birth.getMonth() !== m - 1 || birth.getDate() !== d
  )
    return -1;
  const now = new Date();
  let age = now.getFullYear() - y;
  if (now.getMonth() < m - 1 || (now.getMonth() === m - 1 && now.getDate() < d))
    age--;
  return age;
}
function seedWelcomeReminders(user) {
  const now = new Date().toISOString();
  user.reminders.push(
    {
      id: crypto.randomBytes(8).toString("hex"),
      kind: "welcome",
      text: "🎉 Welcome to Rizz Plaza, " + user.name + "!",
      at: now,
      read: false,
    },
    {
      id: crypto.randomBytes(8).toString("hex"),
      kind: "profile",
      text: "📸 Finish your profile — add a photo so people can find you",
      at: now,
      read: false,
    }
  );
}
// Inert mail hook: when the owner later sets SMTP_URL or RESEND_API_KEY on
// the server, this is where the welcome email goes out. Until then reminders
// live in-app only (the 🔔 bell) and this just logs. No credentials here.
function sendAccountEmail(user, kind) {
  if (process.env.SMTP_URL || process.env.RESEND_API_KEY) {
    console.log(
      "[accounts] " + kind + " email would send to " + user.email +
        " (provider configured — sending not wired in v7.0)"
    );
  } else {
    console.log(
      "[accounts] " + kind + " email queued (no mail provider configured) for " +
        user.email
    );
  }
}
const loginAttempts = new Map(); // ip -> [timestamps]
function loginRateLimited(ip) {
  const now = Date.now();
  const arr = (loginAttempts.get(ip) || []).filter(
    (t) => now - t < 10 * 60 * 1000
  );
  loginAttempts.set(ip, arr);
  return arr.length >= 10;
}
function noteLoginAttempt(ip) {
  const arr = loginAttempts.get(ip) || [];
  arr.push(Date.now());
  loginAttempts.set(ip, arr);
}
function requireAccount(req, res) {
  const db = readAccounts();
  const user = accountForToken(db, req);
  if (!user) {
    res.status(401).json({ ok: false, error: "Not signed in" });
    return null;
  }
  return { db, user };
}
app.post("/api/account/signup", (req, res) => {
  const b = req.body || {};
  const name = String(b.name || "").replace(/[<>&"']/g, "").trim().slice(0, 40);
  const email = String(b.email || "").trim().toLowerCase().slice(0, 120);
  const phone = String(b.phone || "").replace(/\D/g, "").slice(-10);
  const password = String(b.password || "");
  const dob = String(b.dob || "").trim().slice(0, 10);
  if (!/^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(email))
    return res.status(400).json({ ok: false, error: "Invalid email" });
  if (password.length < 8)
    return res
      .status(400)
      .json({ ok: false, error: "Password must be at least 8 characters" });
  if (!dob)
    return res.status(400).json({ ok: false, error: "Date of birth required" });
  const age = ageFromDob(dob);
  if (age < 0)
    return res
      .status(400)
      .json({ ok: false, error: "That date of birth doesn't look right" });
  if (age < 18)
    return res.status(403).json({ ok: false, error: "Accounts require 18+" });
  const db = readAccounts();
  if (db.users.some((u) => u.email === email))
    return res.status(409).json({
      ok: false,
      error: "That email already has an account — log in instead",
    });
  const now = new Date().toISOString();
  const salt = crypto.randomBytes(16).toString("hex");
  const user = {
    id: crypto.randomBytes(12).toString("hex"),
    name: name || email.split("@")[0],
    email,
    phone,
    passHash: hashPassword(password, salt),
    salt,
    dob,
    createdAt: now,
    lastLoginAt: now,
    reminders: [],
  };
  seedWelcomeReminders(user);
  db.users.push(user);
  const token = newAccountToken(db, user.id);
  writeAccounts(db);
  sendAccountEmail(user, "welcome");
  console.log("[accounts] signup", user.email);
  res.status(201).json({ ok: true, token, user: publicAccount(user) });
});
app.post("/api/account/login", (req, res) => {
  const ip = req.ip || "unknown";
  if (loginRateLimited(ip))
    return res.status(429).json({
      ok: false,
      error: "Too many attempts — try again in a few minutes",
    });
  const b = req.body || {};
  const email = String(b.email || "").trim().toLowerCase().slice(0, 120);
  const password = String(b.password || "");
  const db = readAccounts();
  const user = db.users.find((u) => u.email === email);
  let ok = false;
  if (user) {
    const calc = Buffer.from(hashPassword(password, user.salt), "hex");
    const stored = Buffer.from(user.passHash, "hex");
    ok = calc.length === stored.length && crypto.timingSafeEqual(calc, stored);
  }
  if (!ok) {
    noteLoginAttempt(ip);
    return res
      .status(401)
      .json({ ok: false, error: "Wrong email or password" });
  }
  user.lastLoginAt = new Date().toISOString();
  const token = newAccountToken(db, user.id);
  writeAccounts(db);
  console.log("[accounts] login", user.email);
  res.json({ ok: true, token, user: publicAccount(user) });
});
app.get("/api/account/me", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  const unread = ctx.user.reminders.filter((r) => !r.read).length;
  res.json({ ok: true, user: publicAccount(ctx.user), unread });
});
app.get("/api/account/reminders", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  const list = [...ctx.user.reminders].sort((a, b2) =>
    String(b2.at).localeCompare(String(a.at))
  );
  res.json({ ok: true, reminders: list });
});
app.post("/api/account/reminders/read", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  const ids = Array.isArray((req.body || {}).ids)
    ? req.body.ids.map(String)
    : [];
  let changed = false;
  for (const r of ctx.user.reminders) {
    if (!r.read && (ids.includes(r.id) || ids.includes("*"))) {
      r.read = true;
      changed = true;
    }
  }
  if (changed) writeAccounts(ctx.db);
  const unread = ctx.user.reminders.filter((r) => !r.read).length;
  res.json({ ok: true, unread });
});
app.post("/api/account/logout", (req, res) => {
  const h = String(req.headers.authorization || "");
  const m = h.match(/^Bearer\s+(.+)$/i);
  if (m) {
    const db = readAccounts();
    const key = crypto.createHash("sha256").update(m[1].trim()).digest("hex");
    if (db.tokens[key]) {
      delete db.tokens[key];
      writeAccounts(db);
    }
  }
  res.json({ ok: true });
});
app.post("/api/account/welcome-resend", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  ctx.user.reminders.push({
    id: crypto.randomBytes(8).toString("hex"),
    kind: "welcome",
    text: "🎉 Welcome to Rizz Plaza, " + ctx.user.name + "!",
    at: new Date().toISOString(),
    read: false,
  });
  writeAccounts(ctx.db);
  res.json({ ok: true });
});

const upload = multer({
  storage: multer.diskStorage({
    destination: (req, file, cb) => cb(null, PHOTO_DIR),
    filename: (req, file, cb) => {
      const name = `${Date.now()}-${crypto.randomBytes(4).toString("hex")}.${extFor(file.mimetype)}`;
      cb(null, name);
    },
  }),
  limits: { fileSize: 5 * 1024 * 1024 }, // 5 MB max
  fileFilter: (req, file, cb) => {
    if (file.mimetype && file.mimetype.startsWith("image/")) cb(null, true);
    else cb(new Error("Only image files are allowed"));
  },
});

function extFor(mimetype) {
  const m = { "image/jpeg": "jpg", "image/png": "png", "image/webp": "webp", "image/gif": "gif" };
  return m[mimetype] || "jpg";
}

// Returns { ok: true } or { ok: false, reason }.
async function moderateImage(publicUrl) {
  const key = process.env.HIVE_API_KEY;
  if (!key) return { ok: true, unreviewed: true };
  try {
    const res = await fetch("https://api.thehive.ai/api/v2/task/sync", {
      method: "POST",
      headers: {
        authorization: `token ${key}`,
        "content-type": "application/json",
      },
      body: JSON.stringify({ url: publicUrl }),
    });
    const data = await res.json();
    const classes = (data.status && data.status[0] && data.status[0].response
      && data.status[0].response.output && data.status[0].response.output[0]
      && data.status[0].response.output[0].classes) || [];
    const bad = classes.find(
      (c) => c.score > 0.7 && /sexual|nudity|explicit|porn/i.test(c.class || "")
    );
    if (bad) return { ok: false, reason: `flagged: ${bad.class}` };
    return { ok: true };
  } catch (e) {
    console.log("MODERATION ERROR (accepting as unreviewed):", e.message);
    return { ok: true, unreviewed: true };
  }
}

// Upload a profile photo. The uploader must be a joined player (playerId =
// their socket id). On success the photo URL is saved on the player and
// broadcast to everyone in their room.
app.post("/api/profile-photo", upload.single("photo"), async (req, res) => {
  try {
    const player = players.get(String(req.body.playerId || ""));
    if (!player) {
      if (req.file) fs.unlink(req.file.path, () => {});
      return res.status(400).json({ error: "Join the party before uploading a photo." });
    }
    if (!req.file) {
      return res.status(400).json({ error: "No image file received." });
    }

    // Railway always serves public domains over HTTPS.
    const publicUrl = `https://${req.get("host")}/photos/${req.file.filename}`;

    const mod = await moderateImage(publicUrl);
    if (!mod.ok) {
      fs.unlink(req.file.path, () => {});
      console.log("PHOTO REJECTED:", player.name, mod.reason);
      return res.status(422).json({
        error: "That photo didn't pass our safety check. Please try a different one.",
      });
    }
    if (mod.unreviewed) {
      console.log("PHOTO UNREVIEWED (no HIVE_API_KEY):", player.name, publicUrl);
    }

    player.photoUrl = publicUrl;
    io.to(player.room).emit("player-photo", { id: player.id, photoUrl: publicUrl });
    return res.json({ ok: true, photoUrl: publicUrl });
  } catch (e) {
    console.log("UPLOAD ERROR:", e.message);
    return res.status(500).json({ error: "Upload failed. Please try again." });
  }
});


// ---------------------------------------------------------------------------
// Social sign-in (Google / Apple). Inert until the owner sets env keys on the
// server: GOOGLE_CLIENT_ID + GOOGLE_CLIENT_SECRET (free, Google Cloud) and
// APPLE_CLIENT_ID + APPLE_CLIENT_SECRET (Apple Developer). Without keys the
// routes bounce back with ?auth=off and the game explains + falls back to
// email + phone sign-up. Success returns /?auth=google|apple&name=&email=.
// ---------------------------------------------------------------------------
function siteOrigin(req) {
  const proto = String(req.headers["x-forwarded-proto"] || "https").split(",")[0].trim();
  return proto + "://" + req.headers.host;
}
app.get("/auth/google", (req, res) => {
  const cid = process.env.GOOGLE_CLIENT_ID;
  if (!cid) return res.redirect("/?auth=off");
  const ru = siteOrigin(req) + "/auth/google/callback";
  res.redirect("https://accounts.google.com/o/oauth2/v2/auth?client_id=" + encodeURIComponent(cid) +
    "&redirect_uri=" + encodeURIComponent(ru) + "&response_type=code&scope=" + encodeURIComponent("openid email profile") +
    "&prompt=select_account");
});
app.get("/auth/google/callback", async (req, res) => {
  try {
    const cid = process.env.GOOGLE_CLIENT_ID, sec = process.env.GOOGLE_CLIENT_SECRET;
    if (!cid || !sec || !req.query.code) return res.redirect("/?auth=err");
    const ru = siteOrigin(req) + "/auth/google/callback";
    const tokRes = await fetch("https://oauth2.googleapis.com/token", { method: "POST",
      headers: { "Content-Type": "application/x-www-form-urlencoded" },
      body: new URLSearchParams({ code: String(req.query.code), client_id: cid, client_secret: sec, redirect_uri: ru, grant_type: "authorization_code" }) });
    const tok = await tokRes.json();
    if (!tok.id_token) return res.redirect("/?auth=err");
    const infoRes = await fetch("https://oauth2.googleapis.com/tokeninfo?id_token=" + encodeURIComponent(tok.id_token));
    const info = await infoRes.json();
    if (!info || info.aud !== cid || !info.email) return res.redirect("/?auth=err");
    res.redirect("/?auth=google&name=" + encodeURIComponent(info.name || "") + "&email=" + encodeURIComponent(info.email));
  } catch (e) { res.redirect("/?auth=err"); }
});
app.get("/auth/apple", (req, res) => {
  const cid = process.env.APPLE_CLIENT_ID;
  if (!cid) return res.redirect("/?auth=off");
  const ru = siteOrigin(req) + "/auth/apple/callback";
  res.redirect("https://appleid.apple.com/auth/authorize?client_id=" + encodeURIComponent(cid) +
    "&redirect_uri=" + encodeURIComponent(ru) + "&response_type=" + encodeURIComponent("code id_token") +
    "&response_mode=form_post&scope=" + encodeURIComponent("name email"));
});
app.post("/auth/apple/callback", async (req, res) => {
  try {
    const cid = process.env.APPLE_CLIENT_ID;
    const idt = (req.body || {}).id_token;
    if (!cid || !idt) return res.redirect("/?auth=err");
    const parts = String(idt).split(".");
    if (parts.length !== 3) return res.redirect("/?auth=err");
    const header = JSON.parse(Buffer.from(parts[0], "base64url").toString("utf8"));
    const keysRes = await fetch("https://appleid.apple.com/auth/keys");
    const keys = await keysRes.json();
    const jwk = (keys.keys || []).find((k) => k.kid === header.kid);
    if (!jwk) return res.redirect("/?auth=err");
    const key = crypto.createPublicKey({ key: jwk, format: "jwk" });
    const okSig = crypto.verify("RSA-SHA256", Buffer.from(parts[0] + "." + parts[1]), key, Buffer.from(parts[2], "base64url"));
    if (!okSig) return res.redirect("/?auth=err");
    const claims = JSON.parse(Buffer.from(parts[1], "base64url").toString("utf8"));
    if (claims.iss !== "https://appleid.apple.com" || claims.aud !== cid || !claims.email || claims.exp * 1000 < Date.now())
      return res.redirect("/?auth=err");
    let name = "";
    try { const u = JSON.parse((req.body || {}).user || "{}"); name = (((u.name || {}).firstName || "") + " " + ((u.name || {}).lastName || "")).trim(); } catch (e) {}
    res.redirect("/?auth=apple&name=" + encodeURIComponent(name) + "&email=" + encodeURIComponent(claims.email));
  } catch (e) { res.redirect("/?auth=err"); }
});

app.get("/", (req, res) =>
  res.send("Party server is running. Connect with the game client.")
);
app.get("/health", (req, res) =>
  res.json({ ok: true, online: players.size })
);

io.on("connection", (socket) => {
  // Player enters the party
  socket.on("join", (data = {}) => {
    const room = cleanRoomName(data.room);
    const player = {
      id: socket.id,
      name: cleanName(data.name),
      avatar: cleanAvatar(data.avatar),
      room,
      x: 100 + Math.random() * 200,
      y: 100 + Math.random() * 200,
      dancing: false,
      photoUrl: null,
    };
    players.set(socket.id, player);
    socket.join(room);
    socket.emit("room-state", roomState(room)); // everyone already here
    socket.to(room).emit("player-joined", player); // tell the room
  });

  // Player moves around the room
  socket.on("move", (data = {}) => {
    const p = players.get(socket.id);
    if (!p) return;
    p.x = Math.max(0, Math.min(800, Number(data.x) || 0));
    p.y = Math.max(0, Math.min(600, Number(data.y) || 0));
    socket.to(p.room).emit("player-moved", { id: p.id, x: p.x, y: p.y });
  });

  // Player starts / stops dancing
  socket.on("dance", (data = {}) => {
    const p = players.get(socket.id);
    if (!p) return;
    p.dancing = !!data.dancing;
    socket.to(p.room).emit("player-danced", { id: p.id, dancing: p.dancing });
  });

  // Player sends a chat message
  socket.on("chat", (data = {}) => {
    const p = players.get(socket.id);
    if (!p) return;

    // Spam protection: max 8 messages per 10 seconds
    const now = Date.now();
    const times = (chatTimes.get(socket.id) || []).filter(
      (t) => now - t < 10000
    );
    if (times.length >= 8) {
      socket.emit("chat-blocked", {
        reason: "You're sending messages too fast. Slow down!",
      });
      return;
    }
    times.push(now);
    chatTimes.set(socket.id, times);

    let text = String(data.text || "").trim().slice(0, 200);
    if (!text) return;
    text = filterProfanity(text);
    io.to(p.room).emit("chat-message", {
      id: p.id,
      name: p.name,
      text,
      at: now,
    });
  });

  // Player walks into a different party room
  socket.on("switch-room", (data = {}) => {
    const p = players.get(socket.id);
    if (!p) return;
    const room = cleanRoomName(data.room);
    if (room === p.room) return;
    socket.leave(p.room);
    socket.to(p.room).emit("player-left", { id: p.id });
    p.room = room;
    p.dancing = false;
    socket.join(room);
    socket.emit("room-state", roomState(room));
    socket.to(room).emit("player-joined", p);
  });

  // Safety hook: a player reports another player.
  // This only logs for now — before launch, wire it to something you
  // actually check (email, Discord webhook, or an admin panel).
  socket.on("report", (data = {}) => {
    console.log("PLAYER REPORT:", {
      reporter: socket.id,
      reportedId: String(data.reportedId || ""),
      reason: String(data.reason || "").slice(0, 200),
      at: new Date().toISOString(),
    });
    socket.emit("report-received", { ok: true });
  });

  // Two players became a mutual match (client-verified). Session-scoped.
  socket.on("match-made", (data = {}) => {
    const other = players.get(String(data.withId || ""));
    if (!other || other.id === socket.id) return;
    matches.add(dmKey(socket.id, other.id));
  });

  // Live Battle (PK): thin relay between two live hosts + a live-host
  // registry so a host can find opponents. The server only routes messages
  // and stamps the battle end time — scoring lives on the clients, driven
  // by the same gift events their rooms already see.
  socket.on("battle", (data = {}) => {
    const p = players.get(socket.id);
    if (!p) return;
    const t = String(data.t || "");
    if (t === "reg") { p.live = data.on ? { name: p.name, at: Date.now() } : null; return; }
    if (t === "who") {
      const list = [];
      players.forEach((pl) => { if (pl.live && pl.id !== socket.id) list.push({ id: pl.id, name: pl.live.name }); });
      socket.emit("battle", { t: "who-list", list });
      return;
    }
    const other = players.get(String(data.to || ""));
    if (!other) { socket.emit("battle", { t: "gone" }); return; }
    const mins = Math.min(10, Math.max(1, parseInt(data.mins, 10) || 5));
    if (t === "invite") io.to(other.id).emit("battle", { t: "invite", from: socket.id, fromName: p.name, mins });
    else if (t === "decline") io.to(other.id).emit("battle", { t: "decline", from: socket.id, fromName: p.name });
    else if (t === "score") io.to(other.id).emit("battle", { t: "score", from: socket.id, pts: Math.max(0, parseInt(data.pts, 10) || 0) });
    else if (t === "end") io.to(other.id).emit("battle", { t: "end", from: socket.id });
    else if (t === "accept") {
      const endsAt = Date.now() + mins * 60000;
      io.to(other.id).emit("battle", { t: "accept", from: socket.id, fromName: p.name, endsAt });
      socket.emit("battle", { t: "start", from: other.id, fromName: other.name, endsAt });
    }
  });

  // Walkie-talkie floor: one talker per channel at a time.
  socket.on("voice-request-floor", (data = {}) => {
    const channel = String(data.channel || "").slice(0, 80);
    const members = channelMembers(channel);
    if (!members.includes(socket.id)) {
      return socket.emit("voice-floor-denied", { channel, reason: "not-a-member" });
    }
    if (channel.startsWith("dm:") && !matches.has(channel.slice(3))) {
      return socket.emit("voice-floor-denied", { channel, reason: "not-matched" });
    }
    const holder = voiceFloors.get(channel);
    if (holder && holder !== socket.id) {
      const hp = players.get(holder);
      return socket.emit("voice-floor-denied", {
        channel,
        reason: "busy",
        by: holder,
        byName: hp ? hp.name : "Someone",
      });
    }
    voiceFloors.set(channel, socket.id);
    const me = players.get(socket.id);
    const others = members.filter((id) => id !== socket.id);
    if (others.length)
      io.to(others).emit("voice-floor-granted", {
        channel,
        by: socket.id,
        byName: me ? me.name : "Someone",
      });
    socket.emit("voice-floor-granted", { channel, by: socket.id, self: true });
  });

  socket.on("voice-release-floor", (data = {}) => {
    const channel = String(data.channel || "").slice(0, 80);
    if (voiceFloors.get(channel) === socket.id) {
      voiceFloors.delete(channel);
      const others = channelMembers(channel).filter((id) => id !== socket.id);
      if (others.length)
        io.to(others).emit("voice-floor-released", { channel, by: socket.id });
    }
  });

  // WebRTC signaling relay. Allowed only within the same room or between
  // matched players.
  socket.on("voice-signal", (data = {}) => {
    const target = players.get(String(data.to || ""));
    const me = players.get(socket.id);
    if (!target || !me) return;
    const sameRoom = target.room === me.room;
    const matched = matches.has(dmKey(socket.id, target.id));
    if (!sameRoom && !matched) return;
    io.to(target.id).emit("voice-signal", {
      from: socket.id,
      fromName: me.name,
      type: String(data.type || ""),
      payload: data.payload || null,
    });
  });

  // -------------------------------------------------------------------------
  // Live auctions (Whatnot-style). One live auction per room. The host lists
  // an item with a starting bid and a timer; joined viewers bid in real time;
  // a bid in the last 5 seconds extends the timer by 5s (anti-sniping). The
  // server only runs the bidding — payment (Stripe) and shipping are handled
  // by the game client afterward; the winner is broadcast as "auction-ended".
  // -------------------------------------------------------------------------
  function endAuction(room, cancelled) {
    const a = auctions.get(room);
    if (!a) return;
    if (a.timer) clearTimeout(a.timer);
    auctions.delete(room);
    const winner = a.highBidderId
      ? { id: a.highBidderId, name: a.highBidderName, amount: a.currentBid }
      : null;
    io.to(room).emit(cancelled ? "auction-cancelled" : "auction-ended", {
      room,
      item: a.item,
      winner: cancelled ? null : winner,
    });
  }
  socket.on("auction-start", (data = {}) => {
    const me = players.get(socket.id);
    if (!me) return;
    const room = me.room;
    if (auctions.has(room)) return;
    const startBid = Math.max(1, Math.min(100000, Math.floor(Number(data.startBid) || 1)));
    const durationSec = Math.max(10, Math.min(600, Math.floor(Number(data.durationSec) || 60)));
    const item = {
      title: String(data.item?.title || "Item").replace(/[<>&"']/g, "").slice(0, 80),
      description: String(data.item?.description || "").replace(/[<>&"']/g, "").slice(0, 300),
      photoUrl: String(data.item?.photoUrl || "").slice(0, 500),
    };
    const a = {
      hostId: socket.id,
      hostName: me.name,
      item,
      startBid,
      currentBid: 0,
      highBidderId: null,
      highBidderName: null,
      endsAt: Date.now() + durationSec * 1000,
      timer: null,
    };
    a.timer = setTimeout(() => endAuction(room, false), durationSec * 1000);
    auctions.set(room, a);
    io.to(room).emit("auction-live", {
      room,
      hostId: a.hostId,
      hostName: a.hostName,
      item: a.item,
      startBid: a.startBid,
      currentBid: 0,
      highBidderName: null,
      endsAt: a.endsAt,
    });
  });
  socket.on("auction-bid", (data = {}) => {
    const me = players.get(socket.id);
    if (!me) return;
    const a = auctions.get(me.room);
    if (!a || a.hostId === socket.id) return;
    const amount = Math.floor(Number(data.amount) || 0);
    const minimum = a.highBidderId ? a.currentBid + 1 : a.startBid;
    if (amount < minimum) return;
    a.currentBid = amount;
    a.highBidderId = socket.id;
    a.highBidderName = me.name;
    let extended = false;
    const remaining = a.endsAt - Date.now();
    if (remaining < 5000) {
      a.endsAt = Date.now() + 5000;
      clearTimeout(a.timer);
      a.timer = setTimeout(() => endAuction(me.room, false), 5000);
      extended = true;
    }
    io.to(me.room).emit("auction-update", {
      room: me.room,
      currentBid: a.currentBid,
      highBidderId: a.highBidderId,
      highBidderName: a.highBidderName,
      endsAt: a.endsAt,
      extended,
    });
  });
  socket.on("auction-end", () => {
    const me = players.get(socket.id);
    if (!me) return;
    const a = auctions.get(me.room);
    if (a && a.hostId === socket.id) endAuction(me.room, false);
  });

  socket.on("disconnect", () => {
    const me = players.get(socket.id);
    if (me) {
      const a = auctions.get(me.room);
      if (a && a.hostId === socket.id) endAuction(me.room, true);
    }
    releaseFloorsHeldBy(socket.id);
    for (const m of [...matches]) {
      if (m.split(":").includes(socket.id)) matches.delete(m);
    }
    const p = players.get(socket.id);
    if (p) {
      socket.to(p.room).emit("player-left", { id: p.id });
      players.delete(socket.id);
      chatTimes.delete(socket.id);
    }
  });
});

server.listen(PORT, () =>
  console.log(`Party server listening on port ${PORT}`)
);
