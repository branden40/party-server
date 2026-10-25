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
const clientKeys = new Map(); // [RP-V7.24] socket.id -> stable per-device key from the client's join
// [RP-V7.28] Server-side LIVE REGISTRY: devKey -> { key, room, name, title,
// topic, photo, startedAt, lastBeat }. The old discovery model filed a host
// in a viewer's directory only when live-state messages were heard INSIDE
// the live room, so a client sitting on Home had no reliable way to learn
// about ongoing lives. Hosts now register + heartbeat here; the server
// broadcasts `lives-update` snapshots to every socket on any change and
// hands the current snapshot to each socket right after it joins a room.
// Lives are ephemeral — memory only, nothing persisted.
const liveRegistry = new Map();
const LIVE_SWEEP_MS = Math.max(1000, Number(process.env.LIVE_SWEEP_MS) || 30000);
const LIVE_BEAT_STALE_MS = Math.max(5000, Number(process.env.LIVE_BEAT_STALE_MS) || 75000);
function livesSnapshot() {
  const byKey = new Map(); // devKey -> current socket.id
  for (const [sid, k] of clientKeys) byKey.set(k, sid);
  const accountsDb = readAccounts();
  const potsDb = readPots(); // [RP-V7.41] Plaza Pot state rides the snapshot
  return [...liveRegistry.values()].map((e) => {
    const sid = byKey.get(e.key) || null;
    // [RP-V7.40] Resolve the host's ACCOUNT id: exact when the host's
    // own socket announced acct-presence; otherwise the unique-name
    // rule (same as follow-name). Null for guest hosts / shared names.
    let hostAccountId = null;
    if (sid) {
      const hs = io.sockets.sockets.get(sid);
      if (hs && hs.data && hs.data.accountId) hostAccountId = hs.data.accountId;
    }
    if (!hostAccountId) {
      const m = accountsDb.users.filter((u) => u.name === e.name);
      if (m.length === 1) hostAccountId = m[0].id;
    }
    let watchers = 0;
    for (const p of players.values()) if (p.room === e.room) watchers++;
    return {
      key: e.key,
      hostId: sid,
      hostAccountId,
      room: e.room,
      name: e.name,
      title: e.title,
      topic: e.topic,
      photo: e.photo,
      startedAt: e.startedAt,
      watchers,
      pot: potSnapshotFrom(potsDb, e.key), // [RP-V7.41] null unless a pot is open/drawn here
    };
  });
}
// [RP-V7.40] Per-recipient live ranking, from the SAME interest store
// as the Reels feed: decayed author affinity (x2.5) and followed hosts
// (+12) first, then current watchers (+1 each, capped +10), then
// just-started recency (<= +6, 45-min half-life). Exploration: after
// every 5 ranked entries the newest-started unplaced live is spliced
// in (deterministic), so a brand-new host lands in the first screenful
// for everyone. Defined here (used by livesPayloadFor below) — the
// interest-store helpers it needs are module-level function
// declarations further down, hoisted across the whole file.
function fyRankLives(user, snap) {
  const now = Date.now();
  const sig = readReelSignals();
  const urec = sig.users[user.id] || null;
  const aff = (urec && urec.authorAff) || {};
  const following = new Set(socialFollowingIds(readSocial(), user.id));
  const scored = snap.map((e) => {
    let s = 0;
    const hid = e.hostAccountId;
    if (hid && hid !== user.id) {
      s += 2.5 * fyDecayed(aff[hid], now);
      if (following.has(hid)) s += 12;
    }
    // [RP-V7.41] Pot discovery boost (personalized order only): an
    // OPEN pot on a host this member follows or has positive affinity
    // with earns +6 — enough to lift it above comparable non-pot
    // lives from strangers, never enough to bury a followed host
    // (+12) or real affinity. For everyone else the pot badge just
    // displays, order untouched. Discovery only: the DRAW never
    // reads affinity, follows, or gift history (potRunDraw's only
    // inputs are the pot's own entries).
    if (
      hid && hid !== user.id &&
      e.pot && e.pot.status === "open" &&
      (following.has(hid) || fyDecayed(aff[hid], now) > 0)
    )
      s += 6;
    s += Math.min(10, (e.watchers || 0) * 1);
    const ageMin = (now - (e.startedAt || now)) / 60000;
    if (isFinite(ageMin) && ageMin >= 0) s += 6 * Math.pow(0.5, ageMin / 45);
    return { e, s };
  });
  scored.sort(
    (a, b) =>
      b.s - a.s ||
      (b.e.startedAt || 0) - (a.e.startedAt || 0) ||
      String(a.e.key).localeCompare(String(b.e.key))
  );
  const fresh = snap
    .slice()
    .sort((a, b) => (b.startedAt || 0) - (a.startedAt || 0) || String(a.key).localeCompare(String(b.key)));
  const out = [];
  const used = new Set();
  let f = 0;
  scored.forEach((it, i) => {
    out.push(it.e);
    used.add(it.e.key);
    if ((i + 1) % 5 === 0) {
      while (f < fresh.length && used.has(fresh[f].key)) f++;
      if (f < fresh.length) {
        out.push(fresh[f]);
        used.add(fresh[f].key);
        f++;
      }
    }
  });
  return out;
}
// The lives-update payload FOR ONE SOCKET: signed-in sockets (identity
// from acct-presence) get their personal order + ranked:true; guests
// get the registry order exactly as it has always been. The registry
// and discovery mechanics are untouched — only the ORDER of the list
// inside the payload differs per recipient.
// [RP-V7.41] Discovery lift for the DEFAULT (guest / unranked) order
// only: lives with an OPEN Plaza Pot sort ahead of pot-less lives — a
// stable partition, so relative order inside each group is exactly
// the registry order it has always been. Ranked members keep their
// pure V7.40 affinity order (the pot just displays there).
function potLiftOrder(snap) {
  const withPot = [];
  const plain = [];
  for (const e of snap) {
    if (e.pot && e.pot.status === "open") withPot.push(e);
    else plain.push(e);
  }
  return withPot.concat(plain);
}
function livesPayloadFor(socket) {
  const snap = livesSnapshot();
  const acctId = socket && socket.data && socket.data.accountId;
  if (!acctId) return { lives: potLiftOrder(snap) };
  const user = readAccounts().users.find((u) => u.id === acctId);
  if (!user || user.deletionAt) return { lives: potLiftOrder(snap) };
  return { lives: fyRankLives(user, snap), ranked: true };
}
function broadcastLives() {
  // [RP-V7.40] personalized at emit time, per socket — no shared order.
  for (const s of io.sockets.sockets.values()) {
    try {
      s.emit("lives-update", livesPayloadFor(s));
    } catch (e) { /* a dying socket must not stop the broadcast */ }
  }
}
setInterval(() => {
  const now = Date.now();
  let changed = false;
  for (const [k, e] of [...liveRegistry]) {
    if (now - (e.lastBeat || 0) > LIVE_BEAT_STALE_MS) { liveRegistry.delete(k); changed = true; potLiveEnded(k); } // [RP-V7.41] a stale live is an ended live — settle its pot
  }
  if (changed) broadcastLives();
}, LIVE_SWEEP_MS);
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
// ---------------------------------------------------------------------------
// RP-V7.10: the Stripe webhook needs the RAW request body for signature
// verification, so its route is registered BEFORE the JSON body parser
// below would consume the stream. The handler (stripeWebhookHandler)
// and the rest of the money module live further down this file —
// top-level function declarations hoist, so registering here is safe.
// Until STRIPE_WEBHOOK_SECRET is set the handler ignores every event
// and credits nothing.
// ---------------------------------------------------------------------------
app.post(
  "/api/stripe/webhook",
  express.raw({ type: "*/*", limit: "1mb" }),
  stripeWebhookHandler
);
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
  return { id: u.id, name: u.name, username: u.username || "", email: u.email, phone: u.phone, profileType: profileTypeOf(u) };
}
// RP-V7.17: unique usernames. 3-20 chars, letters/numbers/underscore;
// uniqueness is compared case-insensitively, ignoring surrounding spaces.
const USERNAME_RE = /^[A-Za-z0-9_]{3,20}$/;
function usernameKey(v) {
  return String(v || "").trim().toLowerCase();
}
function usernameTaken(db, username, exceptId) {
  const k = usernameKey(username);
  if (!k) return false;
  return db.users.some((u) => u.id !== exceptId && usernameKey(u.username) === k);
}
// RP-V7.35: strong sign-up — one account per email and per phone number.
// Email uniqueness compares the normalized form (trim + lowercase) on BOTH
// sides, so a legacy row stored un-normalized still collides. Phone
// uniqueness compares a canonical digit form: strip non-digits; an
// 11-digit result starting with 1 drops the leading country code; a value
// that can't reduce to 10 digits compares as its full digit string. The
// same number typed as (555) 123-4567, +1 555-123-4567 or 5551234567
// therefore resolves to one key. Enforcement is write-time only — legacy
// accounts already sharing an email/phone are grandfathered, never locked.
// The checks scan LIVE records only: nothing is cached or tombstoned, so
// if a profile is ever deleted (record removed from the accounts store)
// its email and phone are freed for a new sign-up at that moment.
function normEmailKey(v) {
  return String(v || "").trim().toLowerCase();
}
function normPhoneKey(v) {
  const d = String(v || "").replace(/\D/g, "");
  if (d.length === 11 && d.charAt(0) === "1") return d.slice(1);
  return d;
}
function emailTaken(db, email, exceptId) {
  const k = normEmailKey(email);
  if (!k) return false;
  return db.users.some((u) => u.id !== exceptId && normEmailKey(u.email) === k);
}
function phoneTaken(db, phone, exceptId) {
  const k = normPhoneKey(phone);
  if (!k) return false;
  return db.users.some((u) => u.id !== exceptId && normPhoneKey(u.phone) === k);
}
// [RP-V7.37] Profile type: a self-chosen LABEL on the account —
// "member" (plain, the unbadged default) or one of the creator-family
// titles (creator, influencer, streamer, host, artist, musician,
// comedian, gamer, podcaster, entrepreneur, model, athlete, dancer,
// chef, author). It is chosen in the Profile setup (POST
// /api/account/profile-type) and shows as a badge by the member's
// name. A label ONLY: it changes no age gate, earnings split,
// cash-out, ranking or permission anywhere. Accounts created before
// this field existed have no profileType stored and read as "member".
// THE server map — kept in sync with the client map
// (window.RP_PROFILE_TYPES in index.html).
const PROFILE_TYPES = [
  "member", "creator", "influencer", "streamer", "host", "artist",
  "musician", "comedian", "gamer", "podcaster", "entrepreneur",
  "model", "athlete", "dancer", "chef", "author",
];
const PROFILE_TYPE_LABELS = {
  member: "Member",
  creator: "Content Creator",
  influencer: "Influencer",
  streamer: "Streamer",
  host: "Live Host",
  artist: "Artist",
  musician: "Musician",
  comedian: "Comedian",
  gamer: "Gamer",
  podcaster: "Podcaster",
  entrepreneur: "Entrepreneur",
  model: "Model",
  athlete: "Athlete",
  dancer: "Dancer",
  chef: "Chef",
  author: "Author",
};
function normProfileType(v) {
  const t = String(v || "").trim().toLowerCase();
  return PROFILE_TYPES.indexOf(t) >= 0 ? t : "member";
}
function profileTypeOf(u) {
  return normProfileType(u && u.profileType);
}
function profileTypeLabel(u) {
  return PROFILE_TYPE_LABELS[profileTypeOf(u)];
}
function deriveUsername(db, name, email) {
  let base = String(name || "")
    .toLowerCase()
    .replace(/[^a-z0-9_]+/g, "_")
    .replace(/^_+|_+$/g, "");
  if (base.length < 3)
    base = String(email || "")
      .split("@")[0]
      .toLowerCase()
      .replace(/[^a-z0-9_]+/g, "_")
      .replace(/^_+|_+$/g, "");
  if (base.length < 3) base = "player";
  base = base.slice(0, 20);
  let cand = base;
  for (let n = 2; usernameTaken(db, cand, null); n++) {
    const suf = "_" + n;
    cand = base.slice(0, 20 - suf.length) + suf;
  }
  return cand;
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
  const username = String(b.username || "").trim().slice(0, 20);
  const email = String(b.email || "").trim().toLowerCase().slice(0, 120);
  const phone = String(b.phone || "").replace(/[\s().-]/g, "").slice(0, 20);
  // [RP-V7.37] accepted for API callers; the app itself never sends
  // it at sign-up (the pick lives in the Profile setup), so new
  // accounts land on "member". Anything outside the allowed set is
  // stored as "member" too — a bad label never fails a sign-up.
  const profileType = normProfileType(b.profileType);
  const password = String(b.password || "");
  const dob = String(b.dob || "").trim().slice(0, 10);
  if (!/^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(email))
    return res.status(400).json({ ok: false, error: "Invalid email" });
  if (!USERNAME_RE.test(username))
    return res.status(400).json({
      ok: false,
      error: "Pick a username — 3–20 characters, letters, numbers and underscores only",
    });
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
  if (usernameTaken(db, username))
    return res.status(409).json({
      ok: false,
      error: "That username is taken — try another",
    });
  // [RP-V7.35] strong sign-up: the same email or phone number can only
  // ever belong to ONE account — a second sign-up is refused outright and
  // nothing is created (same 409 shape as the username refusal above).
  if (emailTaken(db, email, null))
    return res.status(409).json({
      ok: false,
      error: "That email is already registered",
    });
  if (phoneTaken(db, phone, null))
    return res.status(409).json({
      ok: false,
      error: "That phone number is already registered",
    });
  const now = new Date().toISOString();
  const salt = crypto.randomBytes(16).toString("hex");
  const user = {
    id: crypto.randomBytes(12).toString("hex"),
    name: name || email.split("@")[0],
    username,
    email,
    phone,
    profileType,
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
  // [RP-V7.37] Lazy finalization touch: any past-due pending deletion
  // is finalized before credentials are even looked at.
  try {
    sweepPendingDeletions();
  } catch (e) {}
  const b = req.body || {};
  const ident = String(b.id || b.username || b.email || "")
    .trim()
    .toLowerCase()
    .slice(0, 120);
  const password = String(b.password || "");
  const db = readAccounts();
  const user = db.users.find(
    (u) => u.email === ident || usernameKey(u.username) === ident
  );
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
      .json({ ok: false, error: "Wrong username/email or password" });
  }
  // [RP-V7.37] A successful login inside the 30-day window CANCELS the
  // scheduled deletion — nothing was ever removed, so the account is
  // restored whole (followers, DMs, content, balances). A past-due
  // account never reaches here: the sweep above finalized it, so the
  // lookup failed like any unknown account.
  let deletionCancelled = false;
  if (user.deletionAt && Date.parse(user.deletionAt) <= Date.now()) {
    // Window already closed but the sweep somehow missed it: finalize
    // now and refuse — a past-due deletion is never cancelled.
    try {
      finalizeAccountDeletion(user.id);
    } catch (e) {}
    noteLoginAttempt(ip);
    return res
      .status(401)
      .json({ ok: false, error: "Wrong username/email or password" });
  }
  if (user.deletionAt) {
    delete user.deletionAt;
    delete user.deletionRequestedAt;
    deletionCancelled = true;
  }
  user.lastLoginAt = new Date().toISOString();
  const token = newAccountToken(db, user.id);
  writeAccounts(db);
  console.log("[accounts] login", user.email);
  res.json({ ok: true, token, user: publicAccount(user), deletionCancelled });
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
// [RP-V7.37] Change my profile type. Session auth (requireAccount);
// the value must be one of PROFILE_TYPES — anything else is a 400
// and nothing changes (unlike sign-up, where a junk label defaults
// to "member" so a sign-up is never lost over a label).
app.post("/api/account/profile-type", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  const raw = String((req.body || {}).profileType || "").trim().toLowerCase();
  if (PROFILE_TYPES.indexOf(raw) < 0)
    return res.status(400).json({
      ok: false,
      error: "Pick a profile type from the list",
    });
  ctx.user.profileType = raw;
  writeAccounts(ctx.db);
  res.json({
    ok: true,
    profileType: raw,
    profileTypeLabel: PROFILE_TYPE_LABELS[raw],
    user: publicAccount(ctx.user),
  });
});

// ---------------------------------------------------------------------------
// RP-V7.37: member-facing DELETE PROFILE with a 30-day SAFETY WINDOW
// (Branden, Oct 24 — the TikTok model):
//   1) REQUEST (this route, password-confirmed): the account is marked
//      pending deletion (deletionRequestedAt + deletionAt = +30 days)
//      and deactivated IMMEDIATELY — every session is killed and the
//      profile goes invisible (directory, profile fetch, followers/
//      following lists and counts, faith discover, rankings, follow/DM
//      targets). Nothing is removed yet: the record still exists, so
//      the RP-V7.35 signup checks keep colliding — email, phone and
//      username stay TAKEN for the whole window.
//   2) REACTIVATION: a successful login during the window cancels the
//      deletion and restores everything untouched (followers, DMs,
//      content, balances — nothing was ever removed). See the login
//      route; it answers deletionCancelled:true for the client notice.
//   3) FINALIZATION (sweepPendingDeletions: on boot, every 10 minutes,
//      and at the top of the login route): accounts past deletionAt run
//      the FULL hard cascade in finalizeAccountDeletion — record +
//      sessions, social graph, faith presence, rankings, money ledger
//      (balances VOIDED — charms carry no cash value per Terms and no
//      payout is ever created by deleting), reels/workout content,
//      notify outbox. Only then are email/phone/username freed, and a
//      re-signup starts over as a brand-new account with zero
//      followers. The only trace kept is ONE line in
//      account-deletions.jsonl: timestamp + account id — never the
//      email, phone or name.
//   DM threads are keyed "<accountId>:<accountId>" and carry account
//   ids end to end, so a member's DMs belong to their profile on any
//   device. The moment an account is pending (and forever after final
//   deletion, via the ids-only tombstone set below), the OTHER side's
//   threads render as read-only "Deleted user" history — driven by
//   account status, so a reactivation revives the real name
//   automatically. Auth for the request: the caller's own session
//   token plus the account's CURRENT PASSWORD in the body; a wrong or
//   missing password schedules nothing.
// ---------------------------------------------------------------------------
const DELETIONS_FILE =
  process.env.DELETIONS_FILE ||
  path.join(path.dirname(PHOTO_DIR), "account-deletions.jsonl");
function verifyAccountPassword(user, password) {
  try {
    const calc = Buffer.from(hashPassword(password, user.salt), "hex");
    const stored = Buffer.from(user.passHash, "hex");
    return (
      calc.length === stored.length && crypto.timingSafeEqual(calc, stored)
    );
  } catch {
    return false;
  }
}
/* [RP-V7.37] DM tombstones ("make it like TikTok"): when a profile is
   deleted, the OTHER side keeps the conversation as read-only history
   under a generic "Deleted user". All that is remembered server-side
   is the set of deleted ACCOUNT IDS — no email, no phone, no username
   (the V7.35 release rule: those identifiers are freed, and a
   re-signup gets a brand-new id that inherits nothing). */
const DELETED_ACCOUNTS_FILE =
  process.env.DELETED_ACCOUNTS_FILE ||
  path.join(path.dirname(PHOTO_DIR), "deleted-accounts.json");
function emptyDeletedAccounts() {
  return { ids: [] };
}
function readDeletedAccounts() {
  try {
    const d = JSON.parse(fs.readFileSync(DELETED_ACCOUNTS_FILE, "utf8"));
    if (d && Array.isArray(d.ids)) return d;
    return emptyDeletedAccounts();
  } catch {
    return emptyDeletedAccounts();
  }
}
function writeDeletedAccounts(db) {
  const tmp = DELETED_ACCOUNTS_FILE + ".tmp";
  fs.writeFileSync(tmp, JSON.stringify(db, null, 2));
  fs.renameSync(tmp, DELETED_ACCOUNTS_FILE);
}
function isTombstonedAccount(id) {
  if (!id) return false;
  try {
    return readDeletedAccounts().ids.includes(String(id));
  } catch (e) {
    return false;
  }
}
function tombstoneAccount(id) {
  const db = readDeletedAccounts();
  if (!db.ids.includes(String(id))) {
    db.ids.push(String(id));
    writeDeletedAccounts(db);
  }
}
function deleteReelsByAuthor(name) {
  // Reels are keyed by author display NAME (that is how the store
  // records them) — remove this account's name's entries + their files.
  try {
    const list = listReels();
    const kept = list.filter((r) => !r || r.author !== name);
    const removed = list.length - kept.length;
    if (!removed) return 0;
    for (const r of list) {
      if (r && r.author === name && r.file) {
        try {
          fs.unlinkSync(path.join(REELS_DIR, r.file));
        } catch (e) {}
      }
    }
    const tmp = REELS_FILE + ".tmp";
    fs.writeFileSync(tmp, JSON.stringify(kept, null, 2));
    fs.renameSync(tmp, REELS_FILE);
    return removed;
  } catch (e) {
    return 0;
  }
}
function deleteWorkoutByUsername(username) {
  // Workout posts carry the account username — remove by that key.
  if (!username) return 0;
  try {
    const list = listWorkout();
    const kept = list.filter((e) => !e || e.username !== username);
    const removed = list.length - kept.length;
    if (!removed) return 0;
    for (const e of list) {
      if (e && e.username === username && e.file) {
        try {
          fs.unlinkSync(path.join(WORKOUT_DIR, e.file));
        } catch (e2) {}
      }
    }
    const tmp = WORKOUT_FILE + ".tmp";
    fs.writeFileSync(tmp, JSON.stringify(kept, null, 2));
    fs.renameSync(tmp, WORKOUT_FILE);
    return removed;
  } catch (e) {
    return 0;
  }
}
function isPendingDeletion(user) {
  return !!(user && user.deletionAt);
}
/* The FULL hard cascade — run ONLY once an account's 30-day window has
   closed, by the finalization sweep (or lazily from the login route).
   Returns the voided amounts, or null when the account is already
   gone. */
function finalizeAccountDeletion(uid) {
  const adb = readAccounts();
  const user = adb.users.find((u) => u.id === uid);
  if (!user) return null;
  const uname = user.name;
  const uuser = user.username || "";

  // What is being voided with the account (read before the cascade).
  let voidCharms = 0;
  let voidCents = 0;
  try {
    const mdb0 = readMoney();
    voidCharms = mdb0.balances[uid] || 0;
    const earn0 = mdb0.earnings[uid] || null;
    if (earn0) {
      voidCents += earn0.availableCents || 0;
      for (const h of earn0.held || []) voidCents += (h && h.cents) || 0;
    }
  } catch (e) {}

  // 1) Accounts store: the record + every session token it owns.
  adb.users = adb.users.filter((u) => u.id !== uid);
  for (const k of Object.keys(adb.tokens)) {
    if (adb.tokens[k] && adb.tokens[k].userId === uid)
      delete adb.tokens[k];
  }
  writeAccounts(adb);

  // 2) Social graph: my following list + me out of everyone else's.
  // Followers are computed live from this map, so the other members'
  // follower/following counts reflect the removal immediately.
  try {
    const sdb = readSocial();
    let changed = false;
    if (sdb.follows[uid]) {
      delete sdb.follows[uid];
      changed = true;
    }
    for (const fid of Object.keys(sdb.follows)) {
      const arr = socialFollowingIds(sdb, fid);
      if (arr.includes(uid)) {
        sdb.follows[fid] = arr.filter((x) => x !== uid);
        changed = true;
      }
    }
    if (changed) writeSocial(sdb);
  } catch (e) {}

  // 3) DMs — TikTok model: the threads themselves are NOT deleted.
  // The other party keeps the conversation + history as a read-only
  // "Deleted user" thread (the DM read/send routes resolve the
  // tombstone). What goes here: my block list, me out of everyone
  // else's block lists (so the kept history isn't hidden by a stale
  // block on a dead id), and my id joins the tombstone set.
  try {
    tombstoneAccount(uid);
  } catch (e) {}
  try {
    const ddb = readDms();
    let changed = false;
    if (ddb.blocks[uid]) {
      delete ddb.blocks[uid];
      changed = true;
    }
    for (const bid of Object.keys(ddb.blocks)) {
      const arr = dmBlockedSet(ddb, bid);
      if (arr.includes(uid)) {
        ddb.blocks[bid] = arr.filter((x) => x !== uid);
        changed = true;
      }
    }
    if (changed) writeDms(ddb);
  } catch (e) {}
  try {
    dmSendTimes.delete(uid);
  } catch (e) {}

  // 4) Faith dating: my profile + answers + like/pass lists, and me out
  // of everyone else's like/pass lists.
  try {
    const fdb = readFaith();
    let changed = false;
    for (const sect of ["profiles", "answers", "likes", "passes"]) {
      if (fdb[sect] && fdb[sect][uid]) {
        delete fdb[sect][uid];
        changed = true;
      }
    }
    for (const sect of ["likes", "passes"]) {
      for (const oid of Object.keys(fdb[sect] || {})) {
        const arr = fdb[sect][oid];
        if (Array.isArray(arr) && arr.includes(uid)) {
          fdb[sect][oid] = arr.filter((x) => x !== uid);
          changed = true;
        }
      }
    }
    if (changed) writeFaith(fdb);
  } catch (e) {}

  // 5) Daily rankings: my entry.
  try {
    const rdb = readRankings();
    if (rdb.hosts && rdb.hosts[uid]) {
      delete rdb.hosts[uid];
      writeRankings(rdb);
    }
  } catch (e) {}

  // 6) Money ledger: balance, earnings, premium, my cash-out records
  // and my transaction lines are removed. A positive charm balance or
  // earnings balance is VOIDED with the account — never paid out.
  try {
    const mdb = readMoney();
    let changed = false;
    if (mdb.balances[uid] !== undefined) {
      delete mdb.balances[uid];
      changed = true;
    }
    if (mdb.earnings[uid] !== undefined) {
      delete mdb.earnings[uid];
      changed = true;
    }
    if (mdb.premium[uid] !== undefined) {
      delete mdb.premium[uid];
      changed = true;
    }
    const nc = mdb.cashouts.filter((c) => !c || c.acctId !== uid);
    if (nc.length !== mdb.cashouts.length) {
      mdb.cashouts = nc;
      changed = true;
    }
    const nt = mdb.txlog.filter((t) => !t || (t.from !== uid && t.to !== uid));
    if (nt.length !== mdb.txlog.length) {
      mdb.txlog = nt;
      changed = true;
    }
    if (changed) writeMoney(mdb);
  } catch (e) {}

  // 7) Offline-alert outbox: queued alerts to or from me.
  try {
    const odb = readNotifyOutbox();
    const na = odb.alerts.filter(
      (a) => a && a.toAccountId !== uid && a.fromAccountId !== uid
    );
    if (na.length !== odb.alerts.length) {
      odb.alerts = na;
      writeNotifyOutbox(odb);
    }
  } catch (e) {}

  // 8) Posted content (reels by author name, workout posts by username).
  const reelsGone = deleteReelsByAuthor(uname);
  const workoutGone = deleteWorkoutByUsername(uuser);

  // 9) Live presence map (memory only).
  try {
    acctSockets.delete(uid);
  } catch (e) {}

  // 10) The only trace kept: timestamp + account id.
  try {
    fs.appendFileSync(
      DELETIONS_FILE,
      JSON.stringify({ at: new Date().toISOString(), accountId: uid }) + "\n"
    );
  } catch (e) {}
  console.log(
    "[accounts] delete-finalized",
    uid,
    "| voided charms:",
    voidCharms,
    "| voided earnings cents:",
    voidCents,
    "| reels removed:",
    reelsGone,
    "| workout removed:",
    workoutGone
  );
  return { voided: { charms: voidCharms, earningsCents: voidCents } };
}
/* The finalization sweep: every account whose 30-day window has closed
   gets the hard cascade. Runs on boot, on a 10-minute interval (both
   registered at the bottom of this file), and at the top of the login
   route — any of those "touches" finalizes a past-due account. */
function sweepPendingDeletions() {
  try {
    const db = readAccounts();
    const now = Date.now();
    const due = db.users.filter(
      (u) => u.deletionAt && Date.parse(u.deletionAt) <= now
    );
    for (const u of due) {
      try {
        finalizeAccountDeletion(u.id);
      } catch (e) {}
    }
    return due.length;
  } catch (e) {
    return 0;
  }
}
/* The delete REQUEST: password-confirmed deactivation + scheduling.
   Nothing is removed here — see the RP-V7.37 block comment above. */
app.post("/api/account/delete", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  const user = ctx.user;
  const password = String((req.body || {}).password || "");
  if (!password || !verifyAccountPassword(user, password)) {
    return res.status(403).json({
      ok: false,
      error: "That password doesn't match — your profile was not deleted",
    });
  }
  if (user.deletionAt) {
    // Already scheduled (barely reachable — the first request killed
    // every session). Answer with the existing date, change nothing.
    return res.json({
      ok: true,
      scheduled: true,
      deletionAt: user.deletionAt,
    });
  }
  // Deactivate NOW: mark pending + kill every session + drop presence.
  // The record stays, so email/phone/username stay TAKEN (RP-V7.35)
  // until the sweep finalizes at deletionAt.
  user.deletionRequestedAt = new Date().toISOString();
  user.deletionAt = new Date(
    Date.now() + 30 * 24 * 60 * 60 * 1000
  ).toISOString();
  for (const k of Object.keys(ctx.db.tokens)) {
    if (ctx.db.tokens[k] && ctx.db.tokens[k].userId === user.id)
      delete ctx.db.tokens[k];
  }
  writeAccounts(ctx.db);
  try {
    acctSockets.delete(user.id);
  } catch (e) {}
  console.log(
    "[accounts] delete-scheduled",
    user.id,
    "| finalizes:",
    user.deletionAt
  );
  res.json({ ok: true, scheduled: true, deletionAt: user.deletionAt });
});

// RP-V7.17: one-time username migration for accounts created before
// usernames existed — each keeps a username derived from its display name
// (or email), suffixed until free. Runs at boot; never locks anyone out.
(function migrateAccountUsernames() {
  try {
    const db = readAccounts();
    let changed = false;
    for (const u of db.users) {
      const cur = String(u.username || "").trim();
      if (!USERNAME_RE.test(cur) || usernameTaken(db, cur, u.id)) {
        u.username = deriveUsername(db, u.name, u.email);
        changed = true;
      }
    }
    if (changed) {
      writeAccounts(db);
      console.log("[accounts] assigned usernames to existing accounts");
    }
  } catch (e) {
    console.log("[accounts] username migration skipped:", e && e.message);
  }
})();

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
// Plaza Reels (RP-V7.3): user-posted short videos for the Moments feed.
// Video files live on the same volume as photos, under PHOTO_DIR/reels/,
// with a JSON index (reels.json) beside the other data files. All storage
// goes through saveReel()/listReels() below, so an R2/S3 backend can
// replace the disk later via env (R2_*) without touching the routes.
// ---------------------------------------------------------------------------
const REELS_DIR = path.join(PHOTO_DIR, "reels");
fs.mkdirSync(REELS_DIR, { recursive: true });
const REELS_FILE =
  process.env.REELS_FILE || path.join(path.dirname(PHOTO_DIR), "reels.json");
const REEL_VIDEO_TYPES = {
  "video/mp4": "mp4",
  "video/webm": "webm",
  "video/quicktime": "mov",
};
function listReels() {
  try {
    const arr = JSON.parse(fs.readFileSync(REELS_FILE, "utf8"));
    return Array.isArray(arr) ? arr : [];
  } catch {
    return [];
  }
}
function saveReel(entry) {
  const list = listReels();
  list.push(entry);
  while (list.length > 500) {
    const old = list.shift();
    if (old && old.file) fs.unlink(path.join(REELS_DIR, old.file), () => {});
  }
  const tmp = REELS_FILE + ".tmp";
  fs.writeFileSync(tmp, JSON.stringify(list, null, 2));
  fs.renameSync(tmp, REELS_FILE);
  return entry;
}
function reelCleanId(v) {
  const s = String(v || "").replace(/[^A-Za-z0-9_-]/g, "").slice(0, 80);
  return s || null;
}
function reelCleanName(v) {
  return String(v || "").replace(/[<>&"']/g, "").trim().slice(0, 40);
}
function reelNum(v, min, max) {
  const n = Number(v);
  if (!isFinite(n)) return null;
  return Math.min(max, Math.max(min, n));
}
function updateReelEntry(id, patch) {
  const list = listReels();
  const e = list.find((r) => r.id === id);
  if (!e) return null;
  Object.assign(e, patch);
  const tmp = REELS_FILE + ".tmp";
  fs.writeFileSync(tmp, JSON.stringify(list, null, 2));
  fs.renameSync(tmp, REELS_FILE);
  return e;
}
const reelUpload = multer({
  storage: multer.diskStorage({
    destination: (req, file, cb) => cb(null, REELS_DIR),
    filename: (req, file, cb) => {
      const ext = REEL_VIDEO_TYPES[file.mimetype] || "mp4";
      cb(null, `${Date.now()}-${crypto.randomBytes(6).toString("hex")}.${ext}`);
    },
  }),
  limits: { fileSize: 25 * 1024 * 1024 }, // 25 MB max per reel
  fileFilter: (req, file, cb) => {
    if (REEL_VIDEO_TYPES[file.mimetype]) cb(null, true);
    else cb(new Error("Only MP4, WebM or MOV videos are allowed"));
  },
});
// express.static answers Range requests with 206, which video playback
// (and seeking) needs.
app.use("/reel-files", express.static(REELS_DIR));
app.get("/api/reels", (req, res) => {
  const newest = listReels()
    .slice()
    .sort((a, b) => String(b.createdAt).localeCompare(String(a.createdAt)));
  // [RP-V7.40] For You: a request carrying a valid account token gets
  // the caller's personal ranked order (fyRankReels, below); everyone
  // else — guests, bad tokens — gets exactly the newest-first list this
  // route has always returned, byte for byte.
  let fyUser = null;
  try {
    fyUser = accountForToken(readAccounts(), req);
  } catch (e) {
    fyUser = null;
  }
  const all = fyUser ? fyRankReels(fyUser, newest) : newest;
  const list = all.slice(0, 100).map((r) => {
    // RP-V7.9: remix entries carry their provenance; resolve the source
    // reel's playback URL from the full index so a Duet/Stitch card can
    // play both halves even if the original fell off the feed page.
    const src = r.sourceId ? all.find((x) => x.id === r.sourceId) : null;
    return {
      id: r.id,
      author: r.author,
      caption: r.caption,
      createdAt: r.createdAt,
      url: "/reel-files/" + r.file,
      kind: r.kind || null,
      sourceId: r.sourceId || null,
      sourceAuthor: r.sourceAuthor || null,
      sourceUrl: src ? "/reel-files/" + src.file : null,
      stitchStart: typeof r.stitchStart === "number" ? r.stitchStart : null,
      stitchDur: typeof r.stitchDur === "number" ? r.stitchDur : null,
      allowRemix: r.allowRemix !== false,
    };
  });
  res.json({ ok: true, reels: list, ...(fyUser ? { ranked: true } : {}) });
});
app.post("/api/reel", (req, res) => {
  reelUpload.single("video")(req, res, (err) => {
    if (err) {
      const tooBig = err.code === "LIMIT_FILE_SIZE";
      return res.status(tooBig ? 413 : 400).json({
        ok: false,
        error: tooBig ? "That video is over the 25 MB reel limit" : err.message,
      });
    }
    if (!req.file)
      return res
        .status(400)
        .json({ ok: false, error: "No video file received" });
    // Author: the signed-in account's name when a valid v7.0 token rides
    // along; otherwise the name the client sent (guest) — same trust level
    // as the photo upload / support endpoints.
    let author = "";
    let authorUser = null; // [RP-V7.40] kept so the entry can carry authorId
    try {
      const user = accountForToken(readAccounts(), req);
      if (user) { author = user.name; authorUser = user; }
    } catch (e) {
      /* accounts unreadable — fall back to the guest name below */
    }
    if (!author)
      author =
        String((req.body || {}).author || "")
          .replace(/[<>&"']/g, "")
          .trim()
          .slice(0, 40) || "Guest";
    const caption = String((req.body || {}).caption || "")
      .replace(/[<>&"]/g, "")
      .trim()
      .slice(0, 140);
    // RP-V7.9 Duet & Stitch: optional remix metadata. A duet/stitch entry
    // stores a REFERENCE to its source reel (never a copy) — the feed
    // plays both halves from their own files. stitchDur is hard-clamped
    // to 5s: a stitch clip can never run longer than that.
    const rb = req.body || {};
    const kind = rb.kind === "duet" || rb.kind === "stitch" ? rb.kind : null;
    const sourceId = kind ? reelCleanId(rb.sourceId) : null;
    const sourceAuthor = kind ? reelCleanName(rb.sourceAuthor) : "";
    let stitchStart = null,
      stitchDur = null;
    if (kind === "stitch") {
      stitchStart = reelNum(rb.stitchStart, 0, 3600);
      stitchDur = reelNum(rb.stitchDur, 0, 5);
      if (stitchStart === null) stitchStart = 0;
      if (stitchDur === null) stitchDur = 5;
    }
    const allowRemix = !(
      rb.allowRemix === "false" ||
      rb.allowRemix === "0" ||
      rb.allowRemix === false
    );
    const entry = saveReel({
      id: path.basename(req.file.filename, path.extname(req.file.filename)),
      author,
      // [RP-V7.40] account id of the author when the upload carried a
      // valid token, so For You author affinity can key on the account
      // (older entries have no authorId — the ranker resolves by name).
      ...(authorUser ? { authorId: authorUser.id } : {}),
      caption,
      createdAt: new Date().toISOString(),
      file: req.file.filename,
      size: req.file.size,
      ...(kind ? { kind } : {}),
      ...(sourceId ? { sourceId } : {}),
      ...(sourceAuthor ? { sourceAuthor } : {}),
      ...(stitchStart !== null ? { stitchStart } : {}),
      ...(stitchDur !== null ? { stitchDur } : {}),
      allowRemix,
    });
    console.log("[reels] new reel", entry.id, "by", author, entry.size, "bytes");
    res.json({ ok: true, id: entry.id, url: "/reel-files/" + entry.file });
  });
});

// RP-V7.9: only a reel's own author may turn Duet & Stitch on or off for
// it. Same trust pattern as the upload route: a valid account token whose
// account name matches the entry's author. Guests who posted without an
// account get a 403 here — the client says so plainly.
app.post("/api/reel/remix", (req, res) => {
  const b = req.body || {};
  const id = reelCleanId(b.id);
  if (!id)
    return res.status(400).json({ ok: false, error: "Missing reel id" });
  const entry = listReels().find((r) => r.id === id);
  if (!entry)
    return res.status(404).json({ ok: false, error: "Reel not found" });
  let user = null;
  try {
    user = accountForToken(readAccounts(), req);
  } catch (e) {
    user = null;
  }
  if (!user || user.name !== entry.author)
    return res.status(403).json({
      ok: false,
      error: "Only the reel's author can change that setting",
    });
  const allow =
    b.allow === true || b.allow === "true" || b.allow === 1 || b.allow === "1";
  updateReelEntry(id, { allowRemix: allow });
  console.log("[reels] remix", allow ? "ON" : "OFF", "for", id, "by", user.name);
  res.json({ ok: true, id, allowRemix: allow });
});

// ---------------------------------------------------------------------------
// RP-V7.40: "For You" ranking — ONE interest profile per member, shared
// by the Reels feed AND live discovery: a favorite creator is a favorite
// creator. The feed learns from what each signed-in member actually
// watches, likes and skips:
//   reels: completed watch +3 · like +4 · long watch (>60%) +2 · fast skip −1
//   live:  stay ≥60s +2 · bounce <10s −1 (POST /api/live/signal, capped
//          to one counted event per member+host per 5 minutes)
//   gifts: +4 per gift event (POST /api/money/gift hook; the AMOUNT is
//          never a ranking input — only that a gift happened)
// Signals are first-party and private: the signal endpoints write ONLY
// the caller's own record (identity comes from the session token — the
// body cannot name another account), and nothing in any response exposes
// another member's signals. Store: reel-signals.json beside the other
// data files (the name predates the live expansion; it is THE interest
// store for both surfaces now):
//   { users: { [accountId]: { authorAff: { [authorKey]: { s, at } },
//                             liked: { [reelId]: true },
//                             seenFull: { [reelId]: ts },
//                             liveSigAt: { [hostAccountId]: ts } } },
//     reels: { [reelId]: { views, completes, likes, fastSkips } } }
// authorKey is the author's ACCOUNT id whenever the reel resolves to one
// (new reels store authorId; older ones resolve by exact display name,
// the same unique-match rule as /api/social/follow-name); guest-posted
// reels that match no account fall back to a "name:<name>" key so their
// creator still accrues affinity for the viewer.
// Affinity decays: half every 7 days, applied on read from the stored
// timestamp (and folded in on write), clamped to [-10, 60].
// ---------------------------------------------------------------------------
const REEL_SIGNALS_FILE =
  process.env.REEL_SIGNALS_FILE ||
  path.join(path.dirname(PHOTO_DIR), "reel-signals.json");
function readReelSignals() {
  try {
    const d = JSON.parse(fs.readFileSync(REEL_SIGNALS_FILE, "utf8"));
    if (d && d.users && typeof d.users === "object" && d.reels && typeof d.reels === "object")
      return d;
    return { users: {}, reels: {} };
  } catch {
    return { users: {}, reels: {} };
  }
}
function writeReelSignals(sig) {
  const tmp = REEL_SIGNALS_FILE + ".tmp";
  fs.writeFileSync(tmp, JSON.stringify(sig, null, 2));
  fs.renameSync(tmp, REEL_SIGNALS_FILE);
}
const FY_HALF_LIFE_MS = 7 * 24 * 3600 * 1000;
function fyDecayed(entry, now) {
  if (!entry || typeof entry.s !== "number" || !isFinite(entry.s)) return 0;
  const dt = Math.max(0, now - (typeof entry.at === "number" ? entry.at : now));
  return entry.s * Math.pow(0.5, dt / FY_HALF_LIFE_MS);
}
function fyBump(urec, key, delta, now) {
  if (!urec.authorAff) urec.authorAff = {};
  const v = Math.max(-10, Math.min(60, fyDecayed(urec.authorAff[key], now) + delta));
  urec.authorAff[key] = { s: Math.round(v * 1000) / 1000, at: now };
}
// Fetch (and optionally create) a member's interest record, normalized
// to the full shape — records may have been started by any of the three
// writers (reels signals, live signals, the gift hook).
function fyUserRec(sig, userId, create) {
  let rec = sig.users[userId];
  if (!rec) {
    if (!create) return null;
    rec = sig.users[userId] = { authorAff: {}, liked: {}, seenFull: {}, liveSigAt: {} };
  }
  if (!rec.authorAff) rec.authorAff = {};
  if (!rec.liked) rec.liked = {};
  if (!rec.seenFull) rec.seenFull = {};
  if (!rec.liveSigAt) rec.liveSigAt = {};
  return rec;
}
function reelAuthorKeyFor(accountsDb, reel) {
  if (!reel) return null;
  if (reel.authorId && accountsDb.users.some((u) => u.id === reel.authorId))
    return reel.authorId;
  const matches = accountsDb.users.filter((u) => u.name === reel.author);
  if (matches.length === 1) return matches[0].id;
  return "name:" + String(reel.author || "").trim().toLowerCase();
}
// Score one reel for one member. Weights, highest first: author affinity
// (×2.5), followed-author boost (+12), popularity from the aggregates
// (−4..+7), gentle recency (≤ +8, 48h half-life); −15 for a reel the
// member already watched fully in the last 24h. The caller's own reels
// get no affinity of their own (neutral), as before they simply appear.
function fyScoreReel(user, urec, sig, following, accountsDb, reel, now) {
  const key = reelAuthorKeyFor(accountsDb, reel);
  const isOwn = key === user.id;
  const aff = (urec && urec.authorAff) || {};
  const seenFull = (urec && urec.seenFull) || {};
  let score = 0;
  if (urec && key && !isOwn) score += 2.5 * fyDecayed(aff[key], now);
  if (!isOwn && key && key.indexOf("name:") !== 0 && following.has(key))
    score += 12;
  const agg = sig.reels[reel.id];
  if (agg && agg.views > 0) {
    const pop =
      5 * Math.min(1, (agg.completes + agg.likes) / agg.views) +
      2 * Math.min(1, agg.views / 20) -
      4 * (agg.fastSkips / agg.views);
    score += Math.max(-4, Math.min(7, pop));
  }
  const ageH = (now - Date.parse(reel.createdAt || "")) / 3600000;
  if (isFinite(ageH) && ageH >= 0) score += 8 * Math.pow(0.5, ageH / 48);
  if (seenFull[reel.id] && now - seenFull[reel.id] < 24 * 3600 * 1000)
    score -= 15;
  return score;
}
// Rank the full reel list for a member, then interleave exploration:
// after every 5 ranked picks, the newest not-yet-placed reel is spliced
// in (deterministic), so a brand-new creator always reaches the first
// page no matter how strong the member's habits are.
function fyRankReels(user, newestFirst) {
  const now = Date.now();
  const sig = readReelSignals();
  const urec = sig.users[user.id] || null;
  const following = new Set(socialFollowingIds(readSocial(), user.id));
  const accountsDb = readAccounts();
  const scored = newestFirst.map((r) => ({
    r,
    s: fyScoreReel(user, urec, sig, following, accountsDb, r, now),
  }));
  scored.sort(
    (a, b) =>
      b.s - a.s ||
      String(b.r.createdAt).localeCompare(String(a.r.createdAt)) ||
      String(b.r.id).localeCompare(String(a.r.id))
  );
  const out = [];
  const used = new Set();
  let f = 0;
  scored.forEach((it, i) => {
    out.push(it.r);
    used.add(it.r.id);
    if ((i + 1) % 5 === 0) {
      while (f < newestFirst.length && used.has(newestFirst[f].id)) f++;
      if (f < newestFirst.length) {
        out.push(newestFirst[f]);
        used.add(newestFirst[f].id);
        f++;
      }
    }
  });
  return out;
}
app.post("/api/reels/signal", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return; // 401 — guests write no signals
  const b = req.body || {};
  const reelId = reelCleanId(b.reelId);
  if (!reelId)
    return res.status(400).json({ ok: false, error: "Missing reel id" });
  const all = listReels();
  const reel = all.find((r) => r.id === reelId);
  if (!reel)
    return res.status(404).json({ ok: false, error: "Reel not found" });
  const now = Date.now();
  const sig = readReelSignals();
  const urec = fyUserRec(sig, ctx.user.id, true);
  const agg =
    sig.reels[reelId] ||
    (sig.reels[reelId] = { views: 0, completes: 0, likes: 0, fastSkips: 0 });
  const key = reelAuthorKeyFor(ctx.db, reel);
  const notSelf = key && key !== ctx.user.id;
  if (b.kind === "like") {
    // Idempotent per member: a second "like" for the same reel changes
    // nothing, an "unlike" only counts against a recorded like.
    const want = b.liked === true;
    const has = !!urec.liked[reelId];
    if (want && !has) {
      urec.liked[reelId] = true;
      agg.likes += 1;
      if (notSelf) fyBump(urec, key, 4, now);
    } else if (!want && has) {
      delete urec.liked[reelId];
      agg.likes = Math.max(0, agg.likes - 1);
      if (notSelf) fyBump(urec, key, -4, now);
    }
  } else {
    const watchedMs = reelNum(b.watchedMs, 0, 3600000) || 0;
    const durationMs = reelNum(b.durationMs, 0, 3600000) || 0;
    let frac = reelNum(b.frac, 0, 1);
    if (frac === null)
      frac = durationMs > 0 ? Math.min(1, watchedMs / durationMs) : 0;
    const completed = b.completed === true || frac >= 0.9;
    // Under ~2s AND under a quarter watched = a skip, judged server-side
    // from the numbers, not from a client flag.
    const skippedFast = watchedMs < 2000 && frac < 0.25;
    if (watchedMs <= 0 && !completed)
      return res.json({ ok: true, ignored: true });
    agg.views += 1;
    if (completed) {
      agg.completes += 1;
      urec.seenFull[reelId] = now;
    }
    if (skippedFast) agg.fastSkips += 1;
    if (notSelf) {
      if (completed) fyBump(urec, key, 3, now);
      else if (frac > 0.6) fyBump(urec, key, 2, now);
      if (skippedFast) fyBump(urec, key, -1, now);
    }
  }
  // Bound the store: drop aggregates for reels that fell out of the index.
  const live = new Set(all.map((r) => r.id));
  for (const id of Object.keys(sig.reels)) if (!live.has(id)) delete sig.reels[id];
  writeReelSignals(sig);
  res.json({ ok: true });
});

// [RP-V7.40] Live-stay signals: the client reports how long the caller
// stayed in someone's live. A real stay (>= 60s) is +2 affinity toward
// the host; a bounce (< 10s) is -1; anything between is neutral. Feeds
// the SAME authorAff map the Reels ranking reads. Spam-capped: at most
// one COUNTED event per member+host per 5 minutes. Host identity: the
// account id the client read from the lives snapshot; a unique display
// name is accepted as a fallback for older clients. Unresolvable or
// guest hosts simply don't count — the response stays { ok: true }.
app.post("/api/live/signal", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return; // 401 — guests write no signals
  const b = req.body || {};
  let hostId = String(b.hostAccountId || "").trim();
  if (!hostId && b.hostName) {
    const m = ctx.db.users.filter(
      (u) => u.name === String(b.hostName).trim().slice(0, 40)
    );
    if (m.length === 1) hostId = m[0].id;
  }
  const host = hostId ? ctx.db.users.find((u) => u.id === hostId) : null;
  if (!host || host.id === ctx.user.id)
    return res.json({ ok: true, counted: false });
  const watchedMs = reelNum(b.watchedMs, 0, 4 * 3600 * 1000) || 0;
  let delta = 0;
  if (watchedMs >= 60000) delta = 2;
  else if (watchedMs < 10000) delta = -1;
  if (!delta) return res.json({ ok: true, counted: false });
  const now = Date.now();
  const sig = readReelSignals();
  const urec = fyUserRec(sig, ctx.user.id, true);
  if (urec.liveSigAt[host.id] && now - urec.liveSigAt[host.id] < 5 * 60 * 1000)
    return res.json({ ok: true, counted: false });
  fyBump(urec, host.id, delta, now);
  urec.liveSigAt[host.id] = now;
  writeReelSignals(sig);
  res.json({ ok: true, counted: true });
});

// ---------------------------------------------------------------------------
// RP-V7.41: Plaza Pot — a host-seeded charm pot inside a live.
// LEGAL SHAPE (settled with the owner; do not soften): NO buy-ins,
// ever. Nobody stakes anything to enter — entry is a free tap by any
// signed-in 18+ member. The pot is promo charms only: the HOST seeds
// it from their own charm balance (escrowed through the money ledger),
// and the PLATFORM grows it while it is open with a match of 10% of
// each gift's charm value that lands on the host, capped at the seed
// amount (the match never exceeds the seed). The gift itself is
// untouched — the host still receives the full normal gift split; the
// match is platform-funded pot accounting, credited to winners only at
// the draw and evaporated (never paid out) on cancel/refund.
// At the draw, 5 lucky entrants split seed+match evenly (fewer when
// fewer entered — with <5 entrants everyone entered wins and the pot
// splits by the entrant count); each winner gets floor(total / count)
// and the split remainder returns to the host. Store: pots.json beside
// the other stores, one record per live keyed by the live-registry
// (device) key:
//   { pots: { [liveKey]: { key, room, hostAccountId, hostName, seed,
//       match, entries: [accountId], entryNames: { id: name },
//       status: "open"|"drawn"|"cancelled",
//       winners: [{ id, name, amount }], createdAt, drawnAt } } }
// A drawn/cancelled record is replaced when the host opens a new pot.
// Lifecycle: when a live ends with an open pot (unregister, walking out
// of the room, registry staleness, disconnect+timeout — all funnel to
// potLiveEnded), entries >= 1 auto-draws on the spot; with no entries
// the seed refunds to the host. A boot/60s orphan sweep settles any
// open pot whose live no longer exists (crash safety; at boot every
// live is gone by construction, so boot IS a live-end for old pots).
// BURST TARGET (optional, host-set at open): burstAt must be > seed
// and <= 2x escrow (the match can add at most the full escrow — seed +
// top-ups — again, so the max reachable pot is 2x escrow). After every
// pot-changing event (gift match, top-up, a join), if total >= burstAt
// the pot BURSTS: the draw fires immediately through the same single
// payout path. With zero entrants at the target it sits full/frozen
// (no further match accrues) and bursts on the first join. Draw
// reasons — one payout path, recorded on the record (drawReason) and
// broadcast: "burst" | "host" | "live-end". Advertising rides along:
// an open line + 50%/90% burst-progress shouts go out as system lines
// in the live's chat, list cards show the pot, and guest (unranked)
// Live Now order lifts open-pot lives ahead (ranked order untouched).
// ---------------------------------------------------------------------------
const POTS_FILE =
  process.env.POTS_FILE || path.join(path.dirname(PHOTO_DIR), "pots.json");
const POT_SEED_MIN = 100;
const POT_MATCH_PCT = 10; // platform growth match, % of gift charm value
const POT_WINNER_COUNT = 5;
function readPots() {
  try {
    const d = JSON.parse(fs.readFileSync(POTS_FILE, "utf8"));
    if (d && d.pots && typeof d.pots === "object" && !Array.isArray(d.pots))
      return d;
  } catch (e) {}
  return { pots: {} };
}
function writePots(db) {
  const tmp = POTS_FILE + ".tmp";
  fs.writeFileSync(tmp, JSON.stringify(db, null, 2));
  fs.renameSync(tmp, POTS_FILE);
}
function potTotal(pot) {
  return (pot.seed || 0) + (pot.match || 0);
}
function potPublic(pot, viewerId) {
  if (!pot) return null;
  return {
    key: pot.key,
    room: pot.room,
    status: pot.status,
    total: potTotal(pot),
    seed: pot.seed || 0,
    match: pot.match || 0,
    entries: Array.isArray(pot.entries) ? pot.entries.length : 0,
    burstAt: pot.burstAt || null, // [RP-V7.41] optional burst target
    winners: pot.status === "drawn" ? pot.winners || [] : [],
    reason: pot.status === "drawn" ? pot.drawReason || null : null,
    drawnAt: pot.drawnAt || null,
    createdAt: pot.createdAt || null,
    joined: viewerId ? (pot.entries || []).indexOf(viewerId) >= 0 : false,
    isHost: viewerId ? pot.hostAccountId === viewerId : false,
  };
}
function potSnapshotFrom(potsDb, key) {
  const pot = potsDb && potsDb.pots ? potsDb.pots[key] : null;
  if (!pot) return null;
  if (pot.status === "open")
    return {
      status: "open",
      total: potTotal(pot),
      seed: pot.seed || 0, // [RP-V7.41] the chip's swell mapping needs the seed
      match: pot.match || 0, // [RP-V7.41] the chip floats "+N 🪙" on match growth
      entries: (pot.entries || []).length,
      burstAt: pot.burstAt || null, // [RP-V7.41] cards + chip show burst progress
    };
  if (pot.status === "drawn")
    return {
      status: "drawn",
      total: potTotal(pot),
      entries: (pot.entries || []).length,
      winners: pot.winners || [],
      reason: pot.drawReason || null,
      drawnAt: pot.drawnAt || null,
    };
  return null;
}
function potOpenForHost(accountId) {
  const db = readPots();
  for (const k of Object.keys(db.pots)) {
    const p = db.pots[k];
    if (p && p.status === "open" && p.hostAccountId === accountId) return p;
  }
  return null;
}
// Resolve a live-registry entry's host ACCOUNT id exactly the way
// livesSnapshot does: the host socket's acct-presence announcement
// first, otherwise the unique display-name rule. Null when the host is
// a guest or the name is shared — pot hosting needs a proven account.
function liveHostAccountId(entry) {
  if (!entry) return null;
  const byKey = new Map();
  for (const [sid, k] of clientKeys) byKey.set(k, sid);
  const sid = byKey.get(entry.key) || null;
  if (sid) {
    const hs = io.sockets.sockets.get(sid);
    if (hs && hs.data && hs.data.accountId) return hs.data.accountId;
  }
  const m = readAccounts().users.filter((u) => u.name === entry.name);
  if (m.length === 1) return m[0].id;
  return null;
}
function potLiveForHost(user, liveKey) {
  const entry = liveRegistry.get(String(liveKey || ""));
  if (!entry) return null;
  return liveHostAccountId(entry) === user.id ? entry : null;
}
function potBroadcast(pot) {
  if (!pot) return;
  try {
    io.to(pot.room).emit("pot-update", {
      key: pot.key,
      room: pot.room,
      pot: potPublic(pot, null),
    });
  } catch (e) {}
  try {
    broadcastLives();
  } catch (e) {}
}
// [RP-V7.41] A server-relayed system line in the live's chat/comments
// (the client renders chat-message with sys:true through its system
// line path — the same stream viewers already watch).
function potShout(pot, text) {
  try {
    io.to(pot.room).emit("chat-message", {
      id: "",
      name: "",
      text,
      sys: true,
      at: Date.now(),
    });
  } catch (e) {}
}
// [RP-V7.41] Burst-progress shouts: at 50% and at 90% of a set burst
// target, once each (flags persist on the record). A jump straight past
// 90 announces only the 90 line — the 50 flag is consumed with it.
function potThresholdShouts(db, pot) {
  if (!pot || pot.status !== "open" || !pot.burstAt) return;
  const total = potTotal(pot);
  const pct = total / pot.burstAt;
  let text = null;
  if (pct >= 0.9 && !pot.shout90) {
    pot.shout90 = true;
    pot.shout50 = true;
    text =
      "💥💥 The Plaza Pot is about to BURST — " + total + " / " + pot.burstAt +
      " charms! Join free before it pops!";
  } else if (pct >= 0.5 && !pot.shout50) {
    pot.shout50 = true;
    text =
      "💥 The Plaza Pot is halfway to bursting — " + total + " / " + pot.burstAt +
      " charms! Free to join — tap the pot!";
  }
  if (text) {
    writePots(db);
    potShout(pot, text);
  }
}
// [RP-V7.41] Runs after EVERY pot-changing event (gift match accrual,
// top-up, a join landing in a full pot): progress shouts first, then
// the BURST check. At/over the target with at least one entrant, the
// draw fires immediately through the one payout path with reason
// "burst". With zero entrants nothing draws — the pot sits full and
// frozen (potOnGift refuses further match) and bursts the moment the
// first entry joins. Returns the draw output when a burst fired.
function potAfterChange(db, pot) {
  if (!pot || pot.status !== "open") return null;
  potThresholdShouts(db, pot);
  if (
    pot.burstAt &&
    potTotal(pot) >= pot.burstAt &&
    (pot.entries || []).length >= 1
  ) {
    return potFinishDraw(db, pot, "burst");
  }
  return null;
}
// The draw itself: pick distinct winners uniformly at random
// (crypto Fisher-Yates over the entrant list), credit each winner
// floor(total / winnerCount) charms through the money ledger, return
// the split remainder to the host, and stamp the record drawn.
// Money conservation: seed was debited from the host at open/topup;
// payouts + remainder == seed + match exactly (the match is the only
// platform-created part, and only ever leaves as winner payouts or
// the remainder share of it — never on cancel, where it evaporates).
function potRunDraw(pot) {
  const entrants = (pot.entries || []).slice();
  const total = potTotal(pot);
  const n = Math.min(POT_WINNER_COUNT, entrants.length);
  for (let i = entrants.length - 1; i > 0; i--) {
    const j = crypto.randomInt(i + 1);
    const t = entrants[i];
    entrants[i] = entrants[j];
    entrants[j] = t;
  }
  const picked = entrants.slice(0, n);
  const share = Math.floor(total / n);
  const remainder = total - share * n;
  const adb = readAccounts();
  const winners = picked.map((id) => {
    const u = adb.users.find((x) => x.id === id);
    return {
      id,
      name: (u && u.name) || (pot.entryNames && pot.entryNames[id]) || "Winner",
      amount: share,
    };
  });
  const mdb = readMoney();
  for (const w of winners) {
    mdb.balances[w.id] = (mdb.balances[w.id] || 0) + w.amount;
    moneyTx(mdb, {
      type: "pot-win", from: null, to: w.id, charms: w.amount,
      cents: 0, cut: 0, ref: pot.key,
    });
  }
  if (remainder > 0) {
    mdb.balances[pot.hostAccountId] =
      (mdb.balances[pot.hostAccountId] || 0) + remainder;
    moneyTx(mdb, {
      type: "pot-remainder", from: null, to: pot.hostAccountId,
      charms: remainder, cents: 0, cut: 0, ref: pot.key,
    });
  }
  writeMoney(mdb);
  pot.status = "drawn";
  pot.winners = winners;
  pot.drawnAt = new Date().toISOString();
  return { winners, share, remainder };
}
function potFinishDraw(potsDb, pot, reason) {
  const out = potRunDraw(pot);
  pot.drawReason = reason || "host"; // [RP-V7.41] recorded + broadcast: "burst" | "host" | "live-end"
  writePots(potsDb);
  try {
    io.to(pot.room).emit("pot-drawn", {
      key: pot.key,
      room: pot.room,
      reason: reason || "host",
      total: potTotal(pot),
      entries: (pot.entries || []).length,
      winners: out.winners,
      pot: potPublic(pot, null),
    });
  } catch (e) {}
  try {
    broadcastLives();
  } catch (e) {}
  console.log(
    "[pot] drawn", pot.key, "total", potTotal(pot),
    "winners", out.winners.map((w) => w.id).join(","),
    "share", out.share, "remainder", out.remainder, reason || ""
  );
  return out;
}
// Cancel/refund path: the SEED returns to the host in full through the
// ledger; the platform match was only ever pot accounting, so it
// evaporates here — it is never credited to anyone.
function potRefundSeed(potsDb, pot, status) {
  const mdb = readMoney();
  if ((pot.seed || 0) > 0) {
    mdb.balances[pot.hostAccountId] =
      (mdb.balances[pot.hostAccountId] || 0) + pot.seed;
    moneyTx(mdb, {
      type: "pot-refund", from: null, to: pot.hostAccountId,
      charms: pot.seed, cents: 0, cut: 0, ref: pot.key,
    });
    writeMoney(mdb);
  }
  pot.status = status || "cancelled";
  writePots(potsDb);
  try {
    io.to(pot.room).emit("pot-update", {
      key: pot.key,
      room: pot.room,
      pot: potPublic(pot, null),
    });
  } catch (e) {}
  try {
    broadcastLives();
  } catch (e) {}
  console.log("[pot] refunded seed", pot.key, pot.seed, "to host", pot.hostAccountId);
}
// A live ended (or vanished): settle its open pot by the lifecycle
// rule — entrants mean an immediate auto-draw, no entrants means the
// seed goes home. Called from every registry-removal path.
function potLiveEnded(key) {
  try {
    const db = readPots();
    const pot = db.pots[key];
    if (!pot || pot.status !== "open") return;
    if ((pot.entries || []).length >= 1) potFinishDraw(db, pot, "live-end");
    else potRefundSeed(db, pot, "cancelled");
  } catch (e) {
    console.log("[pot] live-end settle failed", key, e && e.message);
  }
}
function sweepOrphanPots() {
  try {
    const db = readPots();
    for (const k of Object.keys(db.pots)) {
      const pot = db.pots[k];
      if (pot && pot.status === "open" && !liveRegistry.has(k)) {
        if ((pot.entries || []).length >= 1) potFinishDraw(db, pot, "live-end"); // the live no longer exists — same settle rule, same reason set
        else potRefundSeed(db, pot, "cancelled");
      }
    }
  } catch (e) {}
}
// Gift growth hook (called from POST /api/money/gift after the money
// has moved): a gift landing on a host whose pot is open grows the pot
// by the platform match — 10% of the gift's charm value, floored,
// capped so the match never exceeds the seed. The gift itself and the
// host's gift split are untouched; this is pot accounting only.
function potOnGift(hostAccountId, giftCharms) {
  const pot = potOpenForHost(hostAccountId);
  if (!pot) return;
  // [RP-V7.41] A pot at/over its burst target is FROZEN — no further
  // match accrues while it waits for its first entrant.
  if (pot.burstAt && potTotal(pot) >= pot.burstAt) return;
  // Match cap = total host escrow (seed + every top-up lives in seed).
  const room = (pot.seed || 0) - (pot.match || 0);
  if (room <= 0) return;
  const add = Math.min(room, Math.floor((giftCharms * POT_MATCH_PCT) / 100));
  if (add <= 0) return;
  const db = readPots();
  const cur = db.pots[pot.key];
  if (!cur || cur.status !== "open") return;
  if (cur.burstAt && potTotal(cur) >= cur.burstAt) return; // frozen (fresh copy)
  cur.match = (cur.match || 0) + add;
  writePots(db);
  // [RP-V7.41] Progress shouts + the burst check ride every accrual.
  if (potAfterChange(db, cur)) return; // burst drew it — potFinishDraw broadcast everything
  try {
    io.to(cur.room).emit("pot-update", {
      key: cur.key,
      room: cur.room,
      pot: potPublic(cur, null),
    });
  } catch (e) {}
}
app.post("/api/pot/open", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  if (isPendingDeletion(ctx.user))
    return res
      .status(403)
      .json({ ok: false, error: "This account is scheduled for deletion" });
  const b = req.body || {};
  const entry = potLiveForHost(ctx.user, b.live);
  if (!entry)
    return res
      .status(403)
      .json({ ok: false, error: "Only the live's host can open a pot" });
  const seed = Math.floor(Number(b.seed) || 0);
  if (!(seed >= POT_SEED_MIN))
    return res.status(400).json({
      ok: false,
      error: "Seed the pot with at least " + POT_SEED_MIN + " charms",
    });
  // [RP-V7.41] Optional burst target: the pot pays out the moment
  // gifts grow it to the target. It must be MORE than the seed (the
  // seed alone can never burst it) and at most 2x the host's escrow —
  // escrow at open is the seed itself, and the platform match can add
  // at most the full escrow again, so max reachable pot is 2x escrow.
  let burstAt = null;
  if (b.burstAt !== undefined && b.burstAt !== null && b.burstAt !== "") {
    burstAt = Math.floor(Number(b.burstAt) || 0);
    if (!(burstAt > seed))
      return res.status(400).json({
        ok: false,
        error:
          "Burst target must be more than your seed (" + seed +
          ") — the pot bursts when gifts grow it there",
      });
    if (burstAt > 2 * seed)
      return res.status(400).json({
        ok: false,
        error:
          "Burst target can't exceed 2× the pot's escrow (seed + top-ups) — max " +
          2 * seed + " for a " + seed + " seed",
      });
  }
  const db = readPots();
  const existing = db.pots[entry.key];
  if (existing && existing.status === "open")
    return res
      .status(409)
      .json({ ok: false, error: "A pot is already open in this live" });
  const mdb = readMoney();
  const bal = mdb.balances[ctx.user.id] || 0;
  if (bal < seed)
    return res.status(400).json({
      ok: false,
      error: "insufficient-charms",
      balance: bal,
      needed: seed,
    });
  // Escrow: the seed leaves the host's spendable balance now and is
  // only ever paid out as winner shares (+ remainder back) or refunded.
  mdb.balances[ctx.user.id] = bal - seed;
  moneyTx(mdb, {
    type: "pot-seed", from: ctx.user.id, to: null, charms: seed,
    cents: 0, cut: 0, ref: entry.key,
  });
  writeMoney(mdb);
  const pot = {
    key: entry.key,
    room: entry.room,
    hostAccountId: ctx.user.id,
    hostName: ctx.user.name,
    seed,
    match: 0,
    burstAt, // [RP-V7.41] null = no burst target
    shout50: false,
    shout90: false,
    drawReason: null,
    entries: [],
    entryNames: {},
    status: "open",
    winners: [],
    createdAt: new Date().toISOString(),
    drawnAt: null,
  };
  db.pots[entry.key] = pot;
  writePots(db);
  potBroadcast(pot);
  // [RP-V7.41] Advertise the pot in the live's own chat stream.
  potShout(
    pot,
    "🪙 Plaza Pot is OPEN — " + seed + " charms, 5 winners split it. Free to join — tap the pot!"
  );
  console.log("[pot] opened", entry.key, "seed", seed, "burstAt", burstAt, "by", ctx.user.name);
  res.json({
    ok: true,
    pot: potPublic(pot, ctx.user.id),
    balance: mdb.balances[ctx.user.id],
  });
});
app.post("/api/pot/topup", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  if (isPendingDeletion(ctx.user))
    return res
      .status(403)
      .json({ ok: false, error: "This account is scheduled for deletion" });
  const b = req.body || {};
  const entry = potLiveForHost(ctx.user, b.live);
  if (!entry)
    return res
      .status(403)
      .json({ ok: false, error: "Only the live's host can top up the pot" });
  const amount = Math.floor(Number(b.amount) || 0);
  if (!(amount >= 1))
    return res.status(400).json({ ok: false, error: "Invalid amount" });
  const db = readPots();
  const pot = db.pots[entry.key];
  if (!pot || pot.status !== "open")
    return res.status(404).json({ ok: false, error: "No open pot in this live" });
  const mdb = readMoney();
  const bal = mdb.balances[ctx.user.id] || 0;
  if (bal < amount)
    return res.status(400).json({
      ok: false,
      error: "insufficient-charms",
      balance: bal,
      needed: amount,
    });
  mdb.balances[ctx.user.id] = bal - amount;
  moneyTx(mdb, {
    type: "pot-topup", from: ctx.user.id, to: null, charms: amount,
    cents: 0, cut: 0, ref: entry.key,
  });
  writeMoney(mdb);
  pot.seed = (pot.seed || 0) + amount;
  writePots(db);
  // [RP-V7.41] A top-up is a pot-changing event: shouts + burst check.
  const burstOut = potAfterChange(db, pot);
  potBroadcast(pot);
  console.log("[pot] topup", entry.key, "+", amount, "seed now", pot.seed);
  res.json({
    ok: true,
    pot: potPublic(pot, ctx.user.id),
    // a burst draw may have paid the host a remainder — re-read then
    balance: burstOut
      ? readMoney().balances[ctx.user.id] || 0
      : mdb.balances[ctx.user.id],
    ...(burstOut
      ? { winners: burstOut.winners, share: burstOut.share, remainder: burstOut.remainder }
      : {}),
  });
});
app.post("/api/pot/join", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return; // 401 "Not signed in" — guests must sign in to enter
  if (isPendingDeletion(ctx.user))
    return res
      .status(403)
      .json({ ok: false, error: "This account is scheduled for deletion" });
  if (ageFromDob(ctx.user.dob) < 18)
    return res.status(403).json({ ok: false, error: "The Plaza Pot is 18+" });
  const liveKey = String((req.body || {}).live || "");
  const db = readPots();
  const pot = db.pots[liveKey];
  if (!pot || pot.status !== "open")
    return res.status(404).json({ ok: false, error: "No open pot in this live" });
  if (pot.hostAccountId === ctx.user.id)
    return res
      .status(400)
      .json({ ok: false, error: "You can't enter your own pot" });
  if ((pot.entries || []).indexOf(ctx.user.id) >= 0)
    return res
      .status(409)
      .json({ ok: false, error: "You're already in the pot" });
  pot.entries.push(ctx.user.id);
  pot.entryNames[ctx.user.id] = ctx.user.name;
  writePots(db);
  // [RP-V7.41] Interest signal (V7.40 store): joining a host's pot is
  // a small affinity bump (+1) for that host. Exactly once per pot
  // per member falls out of the duplicate-join guard above — a second
  // join is a 409 and never reaches this line. (Gifting already feeds
  // affinity through the gift hook; nothing else about the pot does,
  // and NOTHING in the interest system ever feeds the draw.)
  try {
    const sig = readReelSignals();
    fyBump(fyUserRec(sig, ctx.user.id, true), pot.hostAccountId, 1, Date.now());
    writeReelSignals(sig);
  } catch (e) {}
  // [RP-V7.41] A full/frozen pot bursts the moment its first entry
  // joins — the join itself is the pot-changing event that arms it.
  const burstOut = potAfterChange(db, pot);
  potBroadcast(pot);
  res.json({
    ok: true,
    pot: potPublic(pot, ctx.user.id),
    ...(burstOut
      ? { winners: burstOut.winners, share: burstOut.share, remainder: burstOut.remainder }
      : {}),
  });
});
app.post("/api/pot/draw", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  const b = req.body || {};
  const entry = potLiveForHost(ctx.user, b.live);
  if (!entry)
    return res
      .status(403)
      .json({ ok: false, error: "Only the live's host can draw the pot" });
  const db = readPots();
  const pot = db.pots[entry.key];
  if (!pot || pot.status !== "open")
    return res.status(404).json({ ok: false, error: "No open pot in this live" });
  if ((pot.entries || []).length < 1)
    return res.status(400).json({
      ok: false,
      error: "No entries yet — the pot needs at least one entrant",
    });
  const out = potFinishDraw(db, pot, "host");
  res.json({
    ok: true,
    pot: potPublic(pot, ctx.user.id),
    winners: out.winners,
    share: out.share,
    remainder: out.remainder,
  });
});
app.post("/api/pot/cancel", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  const b = req.body || {};
  const entry = potLiveForHost(ctx.user, b.live);
  if (!entry)
    return res
      .status(403)
      .json({ ok: false, error: "Only the live's host can cancel the pot" });
  const db = readPots();
  const pot = db.pots[entry.key];
  if (!pot || pot.status !== "open")
    return res.status(404).json({ ok: false, error: "No open pot in this live" });
  potRefundSeed(db, pot, "cancelled");
  res.json({ ok: true, pot: potPublic(pot, ctx.user.id) });
});
app.get("/api/pot/state", (req, res) => {
  const liveKey = String(req.query.live || "");
  let viewerId = null;
  try {
    const u = accountForToken(readAccounts(), req);
    if (u) viewerId = u.id;
  } catch (e) {}
  const pot = readPots().pots[liveKey] || null;
  res.json({ ok: true, pot: potPublic(pot, viewerId) });
});

// ---------------------------------------------------------------------------
// [RP-V7.42] THE DAILY POT — one whole-Plaza pot, sibling of the
// per-live Plaza Pot (RP-V7.41 above, untouched). It gathers from ALL
// streamers' rooms and takes from NONE of them:
//   - the PLAZA seeds each day with DAILY_POT_SEED charms (platform
//     promo accounting, like the live-pot match — no member debited);
//   - every gift ANYWHERE on the Plaza grows it by a platform match
//     of 2% of the gift's charm value (floored, min 0), capped for
//     the day at DAILY_POT_MATCH_CAP. The gift itself, its 70/30
//     split and any live-pot match are untouched — a single gift can
//     feed a live pot (10%) and the Daily Pot (2%) at once.
// Entry is a FREE tap, once per account per day, signed-in 18+ only.
// Lifecycle (America/New_York, via Intl — never server-local time):
// the day opens at 00:00 ET seeded; at 21:00 ET the pot BURSTS — 5
// winners (fewer entrants = all win) split the total evenly through
// the money ledger (tx "dailypot-win"), picked uniformly at random
// over the ENTRY LIST ONLY — the same draw discipline as potRunDraw;
// nothing from the interest system ever feeds this draw. The split
// remainder is NOT paid out and does NOT vanish: it is stamped
// rolledOut and folds into TOMORROW's pot. With ZERO entries at
// 21:00 there is no burst at all and the ENTIRE total rolls into
// tomorrow (tomorrow = rollover + fresh seed + its own growth).
// After a burst, the evening shows the winners; at 00:00 ET the next
// day's pot opens. State lives in dailypot.json beside the other
// stores, so a restart mid-day loses nothing; a scheduler tick
// (boot + every 60s, plus a settle check inside dpEnsureToday)
// opens days and fires the 21:00 settlement.
// Record: { date, seed, rolledIn, match, entries: [accountId],
//   entryNames: { id: name }, status: "open"|"burst"|"noburst",
//   winners: [{ id, name, amount }], burstAt: <ms epoch, 21:00 ET>,
//   burstDoneAt, rolledOut }
// ---------------------------------------------------------------------------
const DAILYPOT_FILE =
  process.env.DAILYPOT_FILE || path.join(path.dirname(PHOTO_DIR), "dailypot.json");
const DAILY_POT_SEED = 1000;
const DAILY_POT_MATCH_PCT = 2; // platform growth match, % of ANY gift's charm value
const DAILY_POT_MATCH_CAP = 10000;
const DAILY_POT_WINNER_COUNT = 5;
const DAILY_POT_TZ = "America/New_York";
const DAILY_POT_BURST_HOUR = 21; // 9:00 PM ET
// [RP-V7.42] Launch tiers (Branden's call): launch at Tier 1 and
// AUTO-GROW as the Plaza grows. At each ET day rollover the new
// day's tier is read from the PREVIOUS ET day's total gift volume
// (charms, summed from the money ledger's gift-sent transactions):
//   < 25,000 gifted  -> Tier 1 (seed 1,000, match cap 10,000)
//   >= 25,000        -> Tier 2 (seed 2,500, match cap 25,000)
//   >= 100,000       -> Tier 3 (seed 5,000, match cap 50,000)
//   >= 250,000       -> Tier 4 (seed 10,000, match cap 100,000)
// DAILY_POT_SEED_OVERRIDE (env, default 0 = auto) forces that seed
// with a proportional cap (10x the seed) when set > 0.
const DAILY_POT_TIERS = [
  { tier: 4, minVolume: 250000, seed: 10000, cap: 100000 },
  { tier: 3, minVolume: 100000, seed: 5000, cap: 50000 },
  { tier: 2, minVolume: 25000, seed: 2500, cap: 25000 },
  { tier: 1, minVolume: 0, seed: 1000, cap: 10000 },
];
const DAILY_POT_SEED_OVERRIDE = (() => {
  const n = parseInt(process.env.DAILY_POT_SEED_OVERRIDE || "0", 10);
  return Number.isFinite(n) && n > 0 ? n : 0;
})();
function readDailyPot() {
  try {
    const d = JSON.parse(fs.readFileSync(DAILYPOT_FILE, "utf8"));
    if (d && d.rec && typeof d.rec === "object" && !Array.isArray(d.rec))
      return d;
  } catch (e) {}
  return { rec: null };
}
function writeDailyPot(db) {
  const tmp = DAILYPOT_FILE + ".tmp";
  fs.writeFileSync(tmp, JSON.stringify(db, null, 2));
  fs.renameSync(tmp, DAILYPOT_FILE);
}
// --- America/New_York wall-clock helpers (Intl only) ---
function dpEtParts(ms) {
  const parts = {};
  try {
    const fmt = new Intl.DateTimeFormat("en-US", {
      timeZone: DAILY_POT_TZ, year: "numeric", month: "2-digit", day: "2-digit",
      hour: "2-digit", minute: "2-digit", second: "2-digit", hour12: false,
    });
    for (const p of fmt.formatToParts(new Date(ms))) parts[p.type] = p.value;
  } catch (e) {
    return null;
  }
  return {
    y: +parts.year, mo: +parts.month, d: +parts.day,
    h: (+parts.hour) % 24, mi: +parts.minute, s: +parts.second,
  };
}
function dpDateStr(ms) {
  const p = dpEtParts(ms);
  if (!p) return new Date(ms).toISOString().slice(0, 10);
  return (
    p.y + "-" + String(p.mo).padStart(2, "0") + "-" + String(p.d).padStart(2, "0")
  );
}
function dpDatePlus(dateStr, days) {
  const [y, m, d] = dateStr.split("-").map(Number);
  return new Date(Date.UTC(y, m - 1, d + days)).toISOString().slice(0, 10);
}
// Epoch ms of an ET wall-clock moment (dateStr + hh:mi ET): iterate
// the zone offset until the guess reads back as the target wall time.
function dpEtEpoch(dateStr, hh, mi) {
  const [y, m, d] = dateStr.split("-").map(Number);
  const target = Date.UTC(y, m - 1, d, hh, mi || 0, 0);
  let guess = target;
  for (let i = 0; i < 3; i++) {
    const p = dpEtParts(guess);
    if (!p) break;
    const read = Date.UTC(p.y, p.mo - 1, p.d, p.h, p.mi, p.s);
    const drift = target - read;
    if (drift === 0) break;
    guess += drift;
  }
  return guess;
}
function dailyPotTotal(rec) {
  return (rec.seed || 0) + (rec.rolledIn || 0) + (rec.match || 0);
}
function dailyPotPublic(rec, viewerId) {
  if (!rec) return null;
  let nextBurstAt = rec.burstAt || null;
  if (rec.status !== "open")
    nextBurstAt = dpEtEpoch(dpDatePlus(rec.date, 1), DAILY_POT_BURST_HOUR, 0);
  return {
    date: rec.date,
    status: rec.status,
    tier: rec.tier != null ? rec.tier : 1, // [RP-V7.42] the day's launch tier (0 = manual override)
    matchCap: rec.matchCap != null ? rec.matchCap : DAILY_POT_MATCH_CAP,
    total: dailyPotTotal(rec),
    seedPart: rec.seed || 0,
    rolledIn: rec.rolledIn || 0,
    matchPart: rec.match || 0,
    entriesCount: Array.isArray(rec.entries) ? rec.entries.length : 0,
    joined: viewerId ? (rec.entries || []).indexOf(viewerId) >= 0 : false,
    winners: rec.status === "burst" ? rec.winners || [] : [],
    burstAt: rec.burstAt || null,
    nextBurstInSec: nextBurstAt
      ? Math.max(0, Math.round((nextBurstAt - Date.now()) / 1000))
      : null,
  };
}
let dpLastGrowthBcastAt = 0;
// Plaza-wide state push. Growth ticks are throttled to ~15s; joins,
// bursts and day opens force an immediate push.
function dpBroadcastUpdate(force) {
  const now = Date.now();
  if (!force && now - dpLastGrowthBcastAt < 15000) return;
  dpLastGrowthBcastAt = now;
  try {
    io.emit("dailypot-update", { pot: dailyPotPublic(readDailyPot().rec, null) });
  } catch (e) {}
}
// The Daily Pot draw — the same discipline as potRunDraw (RP-V7.41):
// distinct winners picked uniformly at random (crypto Fisher-Yates)
// over the ENTRY LIST ONLY; each winner is credited floor(total / n)
// through the money ledger; the split remainder is stamped rolledOut
// and folds into tomorrow's pot at the roll (never paid to a host).
function dpRunBurst(db, rec) {
  const total = dailyPotTotal(rec);
  const entrants = (rec.entries || []).slice();
  const n = Math.min(DAILY_POT_WINNER_COUNT, entrants.length);
  for (let i = entrants.length - 1; i > 0; i--) {
    const j = crypto.randomInt(i + 1);
    const t = entrants[i];
    entrants[i] = entrants[j];
    entrants[j] = t;
  }
  const picked = entrants.slice(0, n);
  const share = Math.floor(total / n);
  const remainder = total - share * n;
  const adb = readAccounts();
  const winners = picked.map((id) => {
    const u = adb.users.find((x) => x.id === id);
    return {
      id,
      name: (u && u.name) || (rec.entryNames && rec.entryNames[id]) || "Winner",
      amount: share,
    };
  });
  const mdb = readMoney();
  for (const w of winners) {
    mdb.balances[w.id] = (mdb.balances[w.id] || 0) + w.amount;
    moneyTx(mdb, {
      type: "dailypot-win", from: null, to: w.id, charms: w.amount,
      cents: 0, cut: 0, ref: rec.date,
    });
  }
  writeMoney(mdb);
  rec.status = "burst";
  rec.winners = winners;
  rec.burstDoneAt = new Date().toISOString();
  rec.rolledOut = remainder;
  writeDailyPot(db);
  try {
    io.emit("dailypot-burst", {
      date: rec.date, total, winners, share, remainder,
    });
  } catch (e) {}
  dpBroadcastUpdate(true);
  console.log(
    "[dailypot] BURST", rec.date, "total", total,
    "winners", winners.map((w) => w.id).join(","),
    "share", share, "rolledOut", remainder
  );
  return { winners, share, remainder };
}
// The 21:00 settlement for a day: entries -> burst; ZERO entries ->
// NO burst (status "noburst") — the whole total rolls into tomorrow.
function dpSettle(rec) {
  const db = readDailyPot();
  const cur = db.rec;
  if (!cur || cur.date !== rec.date || cur.status !== "open") return null;
  if ((cur.entries || []).length >= 1) return dpRunBurst(db, cur);
  cur.status = "noburst";
  writeDailyPot(db);
  dpBroadcastUpdate(true);
  console.log(
    "[dailypot] no burst (0 entries) — whole pot rolls forward:", cur.date,
    dailyPotTotal(cur)
  );
  return { noburst: true };
}
function dpGiftVolumeOn(dateStr) {
  // [RP-V7.42] Total charms gifted on one ET date, from the money
  // ledger's gift-sent transactions (one per gift, charms = the
  // gift's catalog cost). No ledger yet = zero volume = Tier 1.
  let total = 0;
  try {
    const db = readMoney();
    for (const tx of db.txlog || []) {
      if (!tx || tx.type !== "gift-sent") continue;
      const at = Date.parse(tx.at || "");
      if (!Number.isFinite(at)) continue;
      if (dpDateStr(at) === dateStr) total += tx.charms || 0;
    }
  } catch (e) { /* volume reads must never break the day roll */ }
  return total;
}
function dpTierForNewDay(dateStr) {
  // [RP-V7.42] The tier a NEW day (dateStr) opens at — from the
  // PREVIOUS ET day's gift volume; the manual override wins outright.
  if (DAILY_POT_SEED_OVERRIDE > 0)
    return {
      tier: 0, // 0 = manual override (state still exposes seed + cap)
      seed: DAILY_POT_SEED_OVERRIDE,
      cap: DAILY_POT_SEED_OVERRIDE * 10,
      prevVolume: null,
    };
  const prevVolume = dpGiftVolumeOn(dpDatePlus(dateStr, -1));
  for (const t of DAILY_POT_TIERS)
    if (prevVolume >= t.minVolume)
      return { tier: t.tier, seed: t.seed, cap: t.cap, prevVolume };
  return { tier: 1, seed: DAILY_POT_SEED, cap: DAILY_POT_MATCH_CAP, prevVolume };
}
function dpFreshRec(dateStr, rolledIn) {
  const t = dpTierForNewDay(dateStr); // [RP-V7.42] the day carries its tier
  return {
    date: dateStr,
    tier: t.tier,
    seed: t.seed,
    matchCap: t.cap,
    prevVolume: t.prevVolume,
    rolledIn: rolledIn || 0,
    match: 0,
    entries: [],
    entryNames: {},
    status: "open",
    winners: [],
    burstAt: dpEtEpoch(dateStr, DAILY_POT_BURST_HOUR, 0),
    burstDoneAt: null,
    rolledOut: 0,
  };
}
// Make sure the store holds TODAY's (ET) pot, settling/rolling any
// stale day first: an old day still "open" past its 21:00 settles by
// its own rules (missed bursts still fire), then the carry folds in —
// a burst day contributes only its split remainder; any other day
// (no-burst) contributes its ENTIRE total. Also settles today's pot
// the moment it comes due, so state reads never lag the tick.
function dpEnsureToday(now) {
  const today = dpDateStr(now);
  let db = readDailyPot();
  let rec = db.rec;
  if (rec && rec.date !== today) {
    if (rec.status === "open" && now >= (rec.burstAt || 0)) {
      dpSettle(rec);
      db = readDailyPot();
      rec = db.rec;
    }
    const carry = rec
      ? rec.status === "burst"
        ? rec.rolledOut || 0
        : dailyPotTotal(rec)
      : 0;
    rec = dpFreshRec(today, carry);
    db.rec = rec;
    writeDailyPot(db);
    console.log("[dailypot] opened", today, "seed", rec.seed, "rolledIn", carry);
    dpBroadcastUpdate(true);
  }
  if (!rec) {
    rec = dpFreshRec(today, 0);
    db.rec = rec;
    writeDailyPot(db);
    console.log("[dailypot] opened", today, "seed", rec.seed, "rolledIn", 0);
  }
  if (rec.status === "open" && now >= (rec.burstAt || 0)) {
    dpSettle(rec);
    rec = readDailyPot().rec;
  }
  return rec;
}
// The scheduler tick (boot + every 60s): open the ET day at midnight,
// fire the 21:00 ET burst settlement.
function dailyPotTick() {
  try {
    dpEnsureToday(Date.now());
  } catch (e) {
    console.log("[dailypot] tick failed", e && e.message);
  }
}
// Gift growth hook (called from POST /api/money/gift after the money
// has moved): EVERY gift on the Plaza grows today's Daily Pot by a
// platform match of 2% of its charm value (floored, min 0), capped
// for the day at the day's tier cap (rec.matchCap). Platform accounting only — the
// gift, its split and any live-pot match are untouched.
function dailyPotOnGift(giftCharms) {
  const rec = dpEnsureToday(Date.now());
  if (!rec || rec.status !== "open") return;
  const cap = rec.matchCap != null ? rec.matchCap : DAILY_POT_MATCH_CAP; // [RP-V7.42] the DAY's cap, from its tier
  const add = Math.min(
    cap - (rec.match || 0),
    Math.floor((giftCharms * DAILY_POT_MATCH_PCT) / 100)
  );
  if (!(add > 0)) return;
  const db = readDailyPot();
  const cur = db.rec;
  if (!cur || cur.date !== rec.date || cur.status !== "open") return;
  const cap2 = cur.matchCap != null ? cur.matchCap : DAILY_POT_MATCH_CAP;
  const add2 = Math.min(cap2 - (cur.match || 0), add);
  if (!(add2 > 0)) return;
  cur.match = (cur.match || 0) + add2;
  writeDailyPot(db);
  dpBroadcastUpdate(false); // throttled — joins/bursts force their own
}
app.post("/api/dailypot/join", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return; // 401 "Not signed in" — guests must sign in to enter
  if (isPendingDeletion(ctx.user))
    return res
      .status(403)
      .json({ ok: false, error: "This account is scheduled for deletion" });
  if (ageFromDob(ctx.user.dob) < 18)
    return res.status(403).json({ ok: false, error: "The Daily Pot is 18+" });
  dpEnsureToday(Date.now());
  const db = readDailyPot();
  const rec = db.rec;
  if (!rec || rec.status !== "open")
    return res.status(409).json({
      ok: false,
      error: "Today's pot already burst — tomorrow's opens at midnight ET",
    });
  if ((rec.entries || []).indexOf(ctx.user.id) >= 0)
    return res
      .status(409)
      .json({ ok: false, error: "You're already in today's pot" });
  rec.entries.push(ctx.user.id);
  rec.entryNames[ctx.user.id] = ctx.user.name;
  writeDailyPot(db);
  dpBroadcastUpdate(true);
  console.log("[dailypot] join", rec.date, ctx.user.name, "entries", rec.entries.length);
  res.json({ ok: true, pot: dailyPotPublic(rec, ctx.user.id) });
});
app.get("/api/dailypot/state", (req, res) => {
  let viewerId = null;
  try {
    const u = accountForToken(readAccounts(), req);
    if (u) viewerId = u.id;
  } catch (e) {}
  const rec = dpEnsureToday(Date.now());
  res.json({ ok: true, pot: dailyPotPublic(rec, viewerId) });
});

// ---------------------------------------------------------------------------
// RP-V7.18: Workout Room member videos. Posts live in workout.json beside
// accounts.json (same volume, same atomic-write pattern); the video files
// live in PHOTO_DIR/workout and are served at /workout-files/*. Posting
// requires a signed-in account (401 otherwise) -- guests watch only.
// Entry: { id, author, username, title, category, createdAt, file, size, clientId }
const WORKOUT_DIR = path.join(PHOTO_DIR, "workout");
const WORKOUT_FILE =
  process.env.WORKOUT_FILE || path.join(path.dirname(PHOTO_DIR), "workout.json");
try {
  fs.mkdirSync(WORKOUT_DIR, { recursive: true });
} catch (e) {}
function listWorkout() {
  try {
    const a = JSON.parse(fs.readFileSync(WORKOUT_FILE, "utf8"));
    return Array.isArray(a) ? a : [];
  } catch (e) {
    return [];
  }
}
function saveWorkout(entry) {
  const all = listWorkout();
  all.unshift(entry);
  while (all.length > 300) {
    const old = all.pop();
    if (old && old.file) {
      try {
        fs.unlinkSync(path.join(WORKOUT_DIR, old.file));
      } catch (e) {}
    }
  }
  const tmp = WORKOUT_FILE + ".tmp";
  fs.writeFileSync(tmp, JSON.stringify(all, null, 2));
  fs.renameSync(tmp, WORKOUT_FILE);
  return entry;
}
const WORKOUT_VIDEO_TYPES = {
  "video/mp4": "mp4",
  "video/webm": "webm",
  "video/quicktime": "mov",
};
const workoutUpload = multer({
  storage: multer.diskStorage({
    destination: WORKOUT_DIR,
    filename: (req, file, cb) => {
      const ext = WORKOUT_VIDEO_TYPES[file.mimetype] || "mp4";
      cb(null, "wo-" + Date.now() + "-" + crypto.randomBytes(4).toString("hex") + "." + ext);
    },
  }),
  limits: { fileSize: 25 * 1024 * 1024 },
  fileFilter: (req, file, cb) => cb(null, !!WORKOUT_VIDEO_TYPES[file.mimetype]),
});
app.use("/workout-files", express.static(WORKOUT_DIR));
app.get("/api/workout-videos", (req, res) => {
  const videos = listWorkout()
    .slice(0, 100)
    .map((w) => ({
      id: w.id,
      author: w.author,
      username: w.username || "",
      title: w.title,
      category: w.category,
      createdAt: w.createdAt,
      clientId: w.clientId || "",
      url: "/workout-files/" + w.file,
    }));
  res.json({ ok: true, videos });
});
app.post("/api/workout-video", workoutUpload.single("video"), (req, res) => {
  const accounts = readAccounts();
  const user = accountForToken(accounts, req);
  if (!user) {
    if (req.file) {
      try {
        fs.unlinkSync(req.file.path);
      } catch (e) {}
    }
    return res.status(401).json({ ok: false, error: "Sign in to post a video" });
  }
  if (!req.file) return res.status(400).json({ ok: false, error: "No video received" });
  const clean = (s, n) => String(s || "").replace(/[<>&"']/g, "").trim().slice(0, n);
  const category =
    ["workouts", "nutrition", "fitness"].indexOf(String(req.body.category || "")) >= 0
      ? String(req.body.category)
      : "workouts";
  const entry = saveWorkout({
    id: "wo" + Date.now().toString(36) + crypto.randomBytes(3).toString("hex"),
    author: user.name,
    username: user.username || "",
    title: clean(req.body.title, 80) || "Workout video",
    category,
    createdAt: Date.now(),
    file: req.file.filename,
    size: req.file.size,
    clientId: clean(req.body.clientId, 60),
  });
  console.log("[workout] post", entry.id, "by", user.name, "in", category);
  res.json({ ok: true, id: entry.id, url: "/workout-files/" + entry.file });
});

// ---------------------------------------------------------------------------
// RP-V7.4: server social graph. Follows between ACCOUNTS live in
// social.json beside accounts.json (same volume, same atomic-write
// pattern). Store shape: { follows: { <followerId>: [<followeeId>, ...] } }.
// Every route requires a valid v7.0 account token (401 otherwise) —
// guests keep the game client's device-local follows and never touch
// these routes. All mutations are idempotent.
// ---------------------------------------------------------------------------
const SOCIAL_FILE =
  process.env.SOCIAL_FILE ||
  path.join(path.dirname(PHOTO_DIR), "social.json");
function readSocial() {
  try {
    const d = JSON.parse(fs.readFileSync(SOCIAL_FILE, "utf8"));
    if (d && d.follows && typeof d.follows === "object" && !Array.isArray(d.follows))
      return d;
    return { follows: {} };
  } catch {
    return { follows: {} };
  }
}
function writeSocial(db) {
  const tmp = SOCIAL_FILE + ".tmp";
  fs.writeFileSync(tmp, JSON.stringify(db, null, 2));
  fs.renameSync(tmp, SOCIAL_FILE);
}
function socialFollowingIds(db, userId) {
  const arr = db.follows[userId];
  return Array.isArray(arr) ? arr.filter((x) => typeof x === "string") : [];
}
function socialFollowerIds(db, userId) {
  const out = [];
  for (const fid of Object.keys(db.follows)) {
    if (fid !== userId && socialFollowingIds(db, fid).includes(userId))
      out.push(fid);
  }
  return out;
}
function socialBrief(accountsDb, id) {
  const u = accountsDb.users.find((x) => x.id === id);
  // [RP-V7.37] A pending-deletion account is invisible everywhere a
  // brief is rendered (lists + the counts computed from them).
  if (!u || u.deletionAt) return null;
  // [RP-V7.37] the profile-type label rides along for cards/lists.
  return { id: u.id, name: u.name, profileType: profileTypeOf(u), profileTypeLabel: profileTypeLabel(u) };
}
function socialSetFollow(db, followerId, followeeId, on) {
  const cur = socialFollowingIds(db, followerId);
  const has = cur.includes(followeeId);
  if (on && !has) {
    cur.push(followeeId);
    db.follows[followerId] = cur;
    writeSocial(db);
    return true;
  }
  if (!on && has) {
    db.follows[followerId] = cur.filter((x) => x !== followeeId);
    writeSocial(db);
    return true;
  }
  return false;
}
app.post("/api/social/follow", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  const targetId = String((req.body || {}).accountId || "");
  if (!targetId || targetId === ctx.user.id)
    return res
      .status(400)
      .json({ ok: false, error: "You can't follow yourself" });
  const target = ctx.db.users.find((u) => u.id === targetId);
  if (!target || target.deletionAt)
    return res.status(404).json({
      ok: false,
      error: "Account not found",
    });
  const db = readSocial();
  socialSetFollow(db, ctx.user.id, targetId, true);
  res.json({
    ok: true,
    following: true,
    id: target.id,
    name: target.name,
    followersCount: socialFollowerIds(db, targetId).length,
  });
});
app.post("/api/social/unfollow", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  const targetId = String((req.body || {}).accountId || "");
  if (!targetId || targetId === ctx.user.id)
    return res
      .status(400)
      .json({ ok: false, error: "You can't unfollow yourself" });
  const target = ctx.db.users.find((u) => u.id === targetId);
  if (!target)
    return res.status(404).json({ ok: false, error: "Account not found" });
  const db = readSocial();
  socialSetFollow(db, ctx.user.id, targetId, false);
  res.json({
    ok: true,
    following: false,
    id: target.id,
    name: target.name,
    followersCount: socialFollowerIds(db, targetId).length,
  });
});
app.post("/api/social/follow-name", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  const name = String((req.body || {}).name || "").trim().slice(0, 40);
  if (!name) return res.json({ ok: false, resolved: false });
  const matches = ctx.db.users.filter(
    (u) => u.name === name && u.id !== ctx.user.id
  );
  if (matches.length !== 1) return res.json({ ok: false, resolved: false });
  const db = readSocial();
  socialSetFollow(db, ctx.user.id, matches[0].id, true);
  res.json({
    ok: true,
    resolved: true,
    id: matches[0].id,
    name: matches[0].name,
  });
});
app.get("/api/social/me", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  const db = readSocial();
  const following = socialFollowingIds(db, ctx.user.id)
    .map((id) => socialBrief(ctx.db, id))
    .filter(Boolean);
  const followers = socialFollowerIds(db, ctx.user.id)
    .map((id) => socialBrief(ctx.db, id))
    .filter(Boolean);
  res.json({
    ok: true,
    id: ctx.user.id,
    name: ctx.user.name,
    following,
    followers,
    followingCount: following.length,
    followersCount: followers.length,
  });
});
app.get("/api/social/user/:id", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  const target = ctx.db.users.find((u) => u.id === req.params.id);
  if (!target) {
    // [RP-V7.37] Deleted accounts say so plainly (no profile to open).
    if (isTombstonedAccount(req.params.id))
      return res.status(404).json({
        ok: false,
        error: "This account no longer exists",
        deleted: true,
      });
    return res.status(404).json({ ok: false, error: "Account not found" });
  }
  if (target.deletionAt)
    return res.status(404).json({
      ok: false,
      error: "This account no longer exists",
      deleted: true,
    });
  const db = readSocial();
  res.json({
    ok: true,
    id: target.id,
    name: target.name,
    profileType: profileTypeOf(target),
    profileTypeLabel: profileTypeLabel(target),
    followersCount: socialFollowerIds(db, target.id).length,
    followingCount: socialFollowingIds(db, target.id).length,
    iFollow: socialFollowingIds(db, ctx.user.id).includes(target.id),
  });
});
app.get("/api/social/directory", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  const users = ctx.db.users
    .slice(0, 500)
    .map((u) => ({ id: u.id, name: u.name }));
  res.json({ ok: true, users });
});
// [RP-V7.28] Full public profile for the person card + profile page.
// Read-only; every field is computed from stores the server already
// keeps — social graph counts, today's gift rankings, the money txlog
// (charms sent / received + distinct gifts received), the faith
// profile testimony, and the Reels store (matched by author name,
// which is how reels are recorded). Nothing is invented: a person
// with no account simply 404s and the client shows the guest card.
// Levels are OUR tiers over the real charm totals, and the totals
// ship alongside so the number under each level is the actual data.
const RP_LEVEL_STEPS = [100, 500, 2000, 7500, 20000, 50000];
function rpLevelFor(charms) {
  let lv = 1;
  for (const s of RP_LEVEL_STEPS) if (charms >= s) lv++;
  return lv;
}
app.get("/api/social/profile", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  let target = null;
  const wantId = String(req.query.id || "");
  const wantName = String(req.query.name || "").trim();
  if (wantId) target = ctx.db.users.find((u) => u.id === wantId) || null;
  if (!target && wantName) {
    const m = ctx.db.users.filter(
      (u) => u.name === wantName && !u.deletionAt
    );
    if (m.length === 1) target = m[0];
  }
  if (target && target.deletionAt)
    return res.status(404).json({
      ok: false,
      error: "This account no longer exists",
      deleted: true,
    });
  if (!target) {
    // [RP-V7.37] Deleted accounts say so plainly (no profile to open).
    if (wantId && isTombstonedAccount(wantId))
      return res.status(404).json({
        ok: false,
        error: "This account no longer exists",
        deleted: true,
      });
    return res.status(404).json({ ok: false, error: "Account not found" });
  }
  const sdb = readSocial();
  // Today's Daily Ranking position (same computation as
  // /api/rankings/daily: entries sorted by total charms desc).
  let dailyRank = null, dailyCharms = 0;
  try {
    // Same store shape + computation as /api/rankings/daily: the store
    // is { day, hosts: { <accountId>: { name, total, gifts } } } and
    // only counts when its day is today.
    const rdb = readRankings();
    if (rdb && rdb.day === rankDayKey() && rdb.hosts) {
      const rows = Object.keys(rdb.hosts)
        .map((id) => ({ hostId: id, total: rdb.hosts[id].total || 0 }))
        .sort((a, b) => b.total - a.total);
      const ix = rows.findIndex((r) => r.hostId === target.id);
      if (ix >= 0) { dailyRank = ix + 1; dailyCharms = rows[ix].total || 0; }
    }
  } catch (e) { }
  // Money txlog: lifetime charms sent / received + gift gallery.
  let sentCharms = 0, receivedCharms = 0;
  const galleryRefs = {};
  try {
    const mdb = readMoney();
    for (const t of mdb.txlog || []) {
      if (!t) continue;
      if (t.type === "gift-sent" && t.from === target.id) sentCharms += t.charms || 0;
      if (t.type === "gift-received" && t.to === target.id) {
        receivedCharms += t.charms || 0;
        if (t.ref) galleryRefs[t.ref] = true;
      }
    }
  } catch (e) { }
  // Their Reels (author is the display name in the reels store).
  let reels = [];
  try {
    reels = listReels()
      .filter((r) => r && r.author === target.name)
      .slice(0, 12)
      .map((r) => ({ id: r.id, url: r.url, kind: r.kind || "video", caption: r.caption || "", createdAt: r.createdAt || null }));
  } catch (e) { }
  let reelsCount = reels.length;
  try {
    reelsCount = listReels().filter((r) => r && r.author === target.name).length;
  } catch (e) { }
  // Faith testimony line, when they've set up a faith profile.
  let testimony = "";
  try {
    const fp = (readFaith().profiles || {})[target.id];
    if (fp && fp.testimony) testimony = String(fp.testimony).slice(0, 140);
  } catch (e) { }
  res.json({
    ok: true,
    id: target.id,
    name: target.name,
    username: target.username || null,
    profileType: profileTypeOf(target),
    profileTypeLabel: profileTypeLabel(target),
    followersCount: socialFollowerIds(sdb, target.id).length,
    followingCount: socialFollowingIds(sdb, target.id).length,
    iFollow: socialFollowingIds(sdb, ctx.user.id).includes(target.id),
    dailyRank, dailyCharms,
    gifter: { level: rpLevelFor(sentCharms), charms: sentCharms },
    host: { level: rpLevelFor(receivedCharms), charms: receivedCharms },
    gallery: { got: Object.keys(galleryRefs).length, total: Object.keys(MONEY_GIFT_TABLE).length },
    reelsCount, reels, testimony,
  });
});

// ---------------------------------------------------------------------------
// RP-V7.7: direct messages between ACCOUNTS. Threads live in dms.json
// beside accounts.json / social.json (same volume, same atomic-write
// pattern). Store: { threads: { "<idA>:<idB>": thread },
// blocks: { <userId>: [<userId>, ...] } } with the pair key sorted.
// Thread: { id, users: [a, b], startedBy, accepted, messages:
// [{ id, from, text, at }], createdAt, lastAt, lastReadAt: { uid: iso },
// declined: { uid: iso } }.
// A thread is a message REQUEST for the person who received first
// contact until they accept it or reply — UNLESS they already follow
// the sender (social graph), in which case it lands in the inbox from
// the start. Declining a request hides the thread for that person until
// the other side sends a newer message. Every route requires a valid
// v7.0 account token (guests never touch these routes and keep the
// room chat). Game sockets are anonymous players, so there is no
// realtime DM push — clients poll their open thread. [RP-V7.30] adds
// ONE account->socket presence map (acct-presence, below) used ONLY
// to decide whether an offline-alert needs queueing — never to push.
// ---------------------------------------------------------------------------
const DMS_FILE =
  process.env.DMS_FILE || path.join(path.dirname(PHOTO_DIR), "dms.json");
function emptyDms() {
  return { threads: {}, blocks: {} };
}
function readDms() {
  try {
    const d = JSON.parse(fs.readFileSync(DMS_FILE, "utf8"));
    if (
      d &&
      d.threads && typeof d.threads === "object" && !Array.isArray(d.threads) &&
      d.blocks && typeof d.blocks === "object" && !Array.isArray(d.blocks)
    )
      return d;
    return emptyDms();
  } catch {
    return emptyDms();
  }
}
function writeDms(db) {
  const tmp = DMS_FILE + ".tmp";
  fs.writeFileSync(tmp, JSON.stringify(db, null, 2));
  fs.renameSync(tmp, DMS_FILE);
}
function dmThreadKey(a, b) {
  return [String(a), String(b)].sort().join(":");
}
function dmBlockedSet(db, userId) {
  const arr = db.blocks[userId];
  return Array.isArray(arr) ? arr.filter((x) => typeof x === "string") : [];
}
function dmEitherBlocked(db, a, b) {
  return dmBlockedSet(db, a).includes(b) || dmBlockedSet(db, b).includes(a);
}
function dmUnreadCount(t, userId) {
  const since = (t.lastReadAt && t.lastReadAt[userId]) || "";
  let n = 0;
  for (const m of t.messages) if (m.from !== userId && m.at > since) n++;
  return n;
}
function dmIsRequestFor(socialDb, t, userId) {
  if (t.startedBy === userId || t.accepted) return false;
  const other = t.users.find((u) => u !== userId);
  // If I already follow them, their first message is welcome — inbox.
  return !socialFollowingIds(socialDb, userId).includes(other);
}
const dmSendTimes = new Map(); // userId -> [timestamps]; 30 sends / minute
function dmRateLimited(userId) {
  const now = Date.now();
  const arr = (dmSendTimes.get(userId) || []).filter(
    (t) => now - t < 60 * 1000
  );
  dmSendTimes.set(userId, arr);
  return arr.length >= 30;
}
function noteDmSend(userId) {
  const arr = dmSendTimes.get(userId) || [];
  arr.push(Date.now());
  dmSendTimes.set(userId, arr);
}
app.get("/api/dm/threads", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  const meId = ctx.user.id;
  const db = readDms();
  const socialDb = readSocial();
  const inbox = [];
  const requests = [];
  let unreadTotal = 0;
  for (const t of Object.values(db.threads)) {
    if (!t || !Array.isArray(t.users) || !t.users.includes(meId)) continue;
    const otherId = t.users.find((u) => u !== meId);
    if (dmEitherBlocked(db, meId, otherId)) continue;
    let other = socialBrief(ctx.db, otherId);
    if (!other) {
      // [RP-V7.37] Pending-deletion OR fully deleted account: the
      // conversation shows as read-only "Deleted user" history,
      // driven by account status — a reactivation revives the name.
      const ou = ctx.db.users.find((u) => u.id === otherId);
      if (!((ou && ou.deletionAt) || isTombstonedAccount(otherId)))
        continue;
      other = { id: otherId, name: "Deleted user", deleted: true };
    }
    // A declined request stays hidden until a newer message lands.
    if (t.declined && t.declined[meId] && String(t.lastAt) <= String(t.declined[meId]))
      continue;
    const last = t.messages[t.messages.length - 1] || null;
    const unread = dmUnreadCount(t, meId);
    unreadTotal += unread;
    const brief = {
      user: other,
      lastText: last ? last.text : "",
      lastAt: t.lastAt || t.createdAt,
      unread,
      startedByMe: t.startedBy === meId,
    };
    if (dmIsRequestFor(socialDb, t, meId)) requests.push(brief);
    else inbox.push(brief);
  }
  const byTime = (x, y) => String(y.lastAt).localeCompare(String(x.lastAt));
  inbox.sort(byTime);
  requests.sort(byTime);
  res.json({ ok: true, inbox, requests, unreadTotal });
});
app.get("/api/dm/thread/:userId", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  const otherId = String(req.params.userId);
  const other = ctx.db.users.find((u) => u.id === otherId);
  // [RP-V7.37] A pending-deletion or deleted (tombstoned) account's
  // thread stays readable by the other party as "Deleted user"
  // history — the label follows the account's live status.
  const gone =
    (!other && isTombstonedAccount(otherId)) ||
    !!(other && other.deletionAt);
  if (!other && !gone)
    return res.status(404).json({ ok: false, error: "Account not found" });
  const db = readDms();
  const t = db.threads[dmThreadKey(ctx.user.id, otherId)];
  const socialDb = readSocial();
  res.json({
    ok: true,
    user: gone
      ? { id: otherId, name: "Deleted user", deleted: true }
      : { id: other.id, name: other.name },
    messages: t ? t.messages : [],
    accepted: t ? !!t.accepted : false,
    isRequest: t ? dmIsRequestFor(socialDb, t, ctx.user.id) : false,
    blocked: dmEitherBlocked(db, ctx.user.id, otherId),
    deleted: !!gone,
  });
});
app.post("/api/dm/send", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  if (dmRateLimited(ctx.user.id))
    return res.status(429).json({
      ok: false,
      error: "You're sending messages too fast — slow down a moment",
    });
  const b = req.body || {};
  const text = String(b.text || "").trim();
  if (text.length < 1 || text.length > 1000)
    return res
      .status(400)
      .json({ ok: false, error: "Messages must be 1–1000 characters" });
  const other = ctx.db.users.find((u) => u.id === String(b.to || ""));
  if (!other) {
    // [RP-V7.37] Sending into a deleted account's thread is refused —
    // the conversation is read-only history now.
    if (isTombstonedAccount(String(b.to || "")))
      return res.status(410).json({
        ok: false,
        error:
          "This account no longer exists — this conversation is read-only now.",
      });
    return res.status(404).json({ ok: false, error: "Account not found" });
  }
  // [RP-V7.37] A pending-deletion account can't receive new DMs.
  if (other.deletionAt)
    return res.status(410).json({
      ok: false,
      error:
        "This account no longer exists — this conversation is read-only now.",
    });
  if (other.id === ctx.user.id)
    return res
      .status(400)
      .json({ ok: false, error: "You can't message yourself" });
  const db = readDms();
  if (dmEitherBlocked(db, ctx.user.id, other.id))
    return res.status(403).json({
      ok: false,
      error: "Messages are blocked between you and this person",
    });
  const key = dmThreadKey(ctx.user.id, other.id);
  let t = db.threads[key];
  const now = new Date().toISOString();
  if (!t) {
    t = {
      id: key,
      users: [ctx.user.id, other.id].sort(),
      startedBy: ctx.user.id,
      accepted: false,
      messages: [],
      createdAt: now,
      lastAt: now,
      lastReadAt: {},
      declined: {},
    };
    db.threads[key] = t;
  }
  const msg = {
    id: crypto.randomBytes(8).toString("hex"),
    from: ctx.user.id,
    text,
    at: now,
  };
  t.messages.push(msg);
  while (t.messages.length > 500) t.messages.shift();
  t.lastAt = now;
  // Replying to a first contact accepts the thread — same as Accept.
  if (t.startedBy !== ctx.user.id && !t.accepted) t.accepted = true;
  writeDms(db);
  noteDmSend(ctx.user.id);
  // [RP-V7.30] The message is stored and waits in the recipient's
  // inbox either way. If they have no live socket right now, also
  // queue an offline alert (deduped per sender per hour) for the
  // future email/SMS transport — see the RP-V7.30 block below.
  if (!acctIsOnline(other.id))
    queueOfflineDmAlert(other.id, ctx.user.id, ctx.user.name);
  res.json({ ok: true, message: msg });
});
app.post("/api/dm/read", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  const otherId = String((req.body || {}).userId || "");
  const db = readDms();
  const t = db.threads[dmThreadKey(ctx.user.id, otherId)];
  if (t) {
    t.lastReadAt = t.lastReadAt || {};
    t.lastReadAt[ctx.user.id] = new Date().toISOString();
    writeDms(db);
  }
  res.json({ ok: true });
});
app.post("/api/dm/accept", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  const otherId = String((req.body || {}).userId || "");
  const db = readDms();
  const t = db.threads[dmThreadKey(ctx.user.id, otherId)];
  if (t) {
    t.accepted = true;
    if (t.declined) delete t.declined[ctx.user.id];
    writeDms(db);
  }
  res.json({ ok: true });
});
app.post("/api/dm/decline", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  const otherId = String((req.body || {}).userId || "");
  const db = readDms();
  const t = db.threads[dmThreadKey(ctx.user.id, otherId)];
  if (t) {
    t.declined = t.declined || {};
    t.declined[ctx.user.id] = new Date().toISOString();
    writeDms(db);
  }
  res.json({ ok: true });
});
app.post("/api/dm/block", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  const other = ctx.db.users.find(
    (u) => u.id === String((req.body || {}).userId || "")
  );
  if (!other)
    return res.status(404).json({ ok: false, error: "Account not found" });
  if (other.id === ctx.user.id)
    return res
      .status(400)
      .json({ ok: false, error: "You can't block yourself" });
  const db = readDms();
  const set = dmBlockedSet(db, ctx.user.id);
  if (!set.includes(other.id)) {
    set.push(other.id);
    db.blocks[ctx.user.id] = set;
    writeDms(db);
  }
  res.json({ ok: true, blocked: true });
});
app.post("/api/dm/unblock", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  const otherId = String((req.body || {}).userId || "");
  const db = readDms();
  const set = dmBlockedSet(db, ctx.user.id).filter((x) => x !== otherId);
  if (set.length !== dmBlockedSet(db, ctx.user.id).length) {
    db.blocks[ctx.user.id] = set;
    writeDms(db);
  }
  res.json({ ok: true, blocked: false });
});

// ---------------------------------------------------------------------------
// RP-V7.30: offline DMs — member directory, account presence, and the
// offline-alert outbox.
//
// DIRECTORY: profiles used to "vanish" when a person went offline —
// you could only start a DM with someone you could see. GET
// /api/members makes every ACCOUNT findable 24/7 by username or
// display name. The payload is a strict whitelist (id, username, name,
// profileType + label [RP-V7.37], photo, followers, iFollow, isSelf):
// email, phone and DOB are NEVER included. Accounts don't store a photo (photos live on the live
// socket player), so `photo` is the photoUrl of a currently-connected
// player whose display name UNIQUELY matches the account name — the
// same name-matching the follow system already uses — else null.
//
// PRESENCE: game sockets are anonymous, so a signed-in client now
// announces its account over the socket with "acct-presence"
// { token } (verified server-side against the same token store as
// REST auth). acctSockets maps accountId -> Set of socket ids. It is
// used ONLY by the DM send route: a recipient with no live socket
// gets an offline alert queued. Guests never announce.
//
// OUTBOX: notify-outbox.json beside the other stores, entries:
// { toAccountId, kind: "dm", fromAccountId, fromName, at } — deduped
// so a burst from one sender queues ONE alert per sender per hour.
// ---------------------------------------------------------------------------
app.get("/api/members", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  const q = String(req.query.q || "").trim().toLowerCase().slice(0, 40);
  let limit = parseInt(req.query.limit, 10);
  if (!Number.isFinite(limit) || limit < 1) limit = 25;
  if (limit > 50) limit = 50;
  const sdb = readSocial();
  const myFollowing = socialFollowingIds(sdb, ctx.user.id);
  const photoByName = {};
  const nameCount = {};
  for (const p of players.values()) {
    if (!p || !p.name) continue;
    const k = String(p.name).toLowerCase();
    nameCount[k] = (nameCount[k] || 0) + 1;
    if (p.photoUrl) photoByName[k] = p.photoUrl;
  }
  const rows = [];
  const pendingIds = new Set(
    ctx.db.users.filter((u) => u.deletionAt).map((u) => u.id)
  );
  for (const u of ctx.db.users) {
    if (u.deletionAt) continue; // [RP-V7.37] pending deletion: invisible
    const uname = usernameKey(u.username);
    const lname = String(u.name || "").toLowerCase();
    let score = null;
    if (!q) score = 2;
    else if (uname.startsWith(q) || lname.startsWith(q)) score = 0;
    else if (uname.includes(q) || lname.includes(q)) score = 1;
    if (score === null) continue;
    rows.push({
      u,
      score,
      // [RP-V7.37] Pending-deletion followers don't count.
      followers: socialFollowerIds(sdb, u.id).filter(
        (fid) => !pendingIds.has(fid)
      ).length,
    });
  }
  rows.sort(
    (a, b) =>
      a.score - b.score ||
      b.followers - a.followers ||
      String(a.u.name).localeCompare(String(b.u.name))
  );
  const members = rows.slice(0, limit).map(({ u, followers }) => {
    const k = String(u.name || "").toLowerCase();
    return {
      id: u.id,
      accountId: u.id,
      username: u.username || "",
      name: u.name,
      profileType: profileTypeOf(u),
      profileTypeLabel: profileTypeLabel(u),
      photo: nameCount[k] === 1 ? photoByName[k] || null : null,
      followers,
      iFollow: myFollowing.includes(u.id),
      isSelf: u.id === ctx.user.id,
    };
  });
  res.json({ ok: true, members });
});

const NOTIFY_FILE =
  process.env.NOTIFY_FILE ||
  path.join(path.dirname(PHOTO_DIR), "notify-outbox.json");
function emptyNotifyOutbox() {
  return { alerts: [] };
}
function readNotifyOutbox() {
  try {
    const d = JSON.parse(fs.readFileSync(NOTIFY_FILE, "utf8"));
    if (d && Array.isArray(d.alerts)) return d;
    return emptyNotifyOutbox();
  } catch {
    return emptyNotifyOutbox();
  }
}
function writeNotifyOutbox(db) {
  const tmp = NOTIFY_FILE + ".tmp";
  fs.writeFileSync(tmp, JSON.stringify(db, null, 2));
  fs.renameSync(tmp, NOTIFY_FILE);
}
const acctSockets = new Map(); // accountId -> Set<socketId> [RP-V7.30]
function acctSocketAdd(accountId, socketId) {
  let set = acctSockets.get(accountId);
  if (!set) {
    set = new Set();
    acctSockets.set(accountId, set);
  }
  set.add(socketId);
}
function acctSocketRemove(accountId, socketId) {
  const set = acctSockets.get(accountId);
  if (!set) return;
  set.delete(socketId);
  if (!set.size) acctSockets.delete(accountId);
}
function acctIsOnline(accountId) {
  const set = acctSockets.get(accountId);
  return !!(set && set.size);
}
function queueOfflineDmAlert(toAccountId, fromAccountId, fromName) {
  const db = readNotifyOutbox();
  const now = Date.now();
  const dupe = db.alerts.some(
    (a) =>
      a &&
      a.kind === "dm" &&
      a.toAccountId === toAccountId &&
      a.fromAccountId === fromAccountId &&
      now - Date.parse(a.at || "") < 3600 * 1000
  );
  if (dupe) return false;
  db.alerts.push({
    toAccountId,
    kind: "dm",
    fromAccountId,
    fromName: String(fromName || "").slice(0, 40),
    at: new Date(now).toISOString(),
  });
  writeNotifyOutbox(db);
  return true;
}
// ---------------------------------------------------------------------------
// OFFLINE ALERT TRANSPORT — NOT WIRED (stub). sendOfflineAlerts() runs
// every minute and is a safe no-op until a provider is configured.
// To wire a real transport later, the owner sets ONE of these in the
// server environment (names follow the v7.0 mail-hook convention):
//   Email (Resend):  RESEND_API_KEY + ALERT_FROM_EMAIL
//   Email (SMTP):    SMTP_URL + ALERT_FROM_EMAIL
//   SMS (Twilio):    TWILIO_ACCOUNT_SID + TWILIO_AUTH_TOKEN +
//                    TWILIO_FROM_NUMBER
// A transport implementation should: read notify-outbox.json, group
// pending entries per recipient (one digest per person, e.g. "You have
// new Rizz Plaza messages from <fromName>"), look the recipient's
// email/phone up in accounts.json (server-side ONLY — contact details
// must never leave through an API), send, then remove the delivered
// entries from the outbox. Until then entries simply stay queued and
// nothing is ever sent.
// ---------------------------------------------------------------------------
function sendOfflineAlerts() {
  const emailReady = !!(
    (process.env.RESEND_API_KEY || process.env.SMTP_URL) &&
    process.env.ALERT_FROM_EMAIL
  );
  const smsReady = !!(
    process.env.TWILIO_ACCOUNT_SID &&
    process.env.TWILIO_AUTH_TOKEN &&
    process.env.TWILIO_FROM_NUMBER
  );
  if (!emailReady && !smsReady) return 0; // no provider configured
  // Provider keys exist but no transport is implemented yet — stay a
  // safe no-op rather than half-sending. See the block comment above.
  return 0;
}
const notifyAlertTimer = setInterval(() => {
  try {
    sendOfflineAlerts();
  } catch (e) {}
}, 60 * 1000);
if (notifyAlertTimer.unref) notifyAlertTimer.unref();

// ---------------------------------------------------------------------------
// RP-V7.8: Faith Dating — a full dating app INSIDE the Christian
// Fellowship room, for server ACCOUNTS only. Accounts are 18+ by
// construction (v7.0 signup refuses under-18), and every route here
// requires a valid account token (401 otherwise), so guests and the
// under-18 view can never reach this layer — the Fellowship room's
// all-ages features (chapel, prayer wall, Bible study, chat) are
// untouched and live entirely elsewhere.
// Data lives in faith.json beside accounts.json (same volume, same
// atomic-write pattern). Store shape:
//   { profiles: { uid: { testimony, denomination, attendance, intent,
//                        optedIn, updatedAt } },
//     answers:  { uid: { answers: { qid: value }, mustHaves: [ids],
//                        cantStands: [ids], updatedAt } },
//     likes:    { uid: [uid, ...] }, passes: { uid: [uid, ...] } }
// Compatibility is computed HERE from both answer sets — a client
// never sees another user's raw answers or can't-stand list, only
// the resulting percentage and flags.
// ---------------------------------------------------------------------------
const FAITH_FILE =
  process.env.FAITH_FILE || path.join(path.dirname(PHOTO_DIR), "faith.json");
function emptyFaith() {
  return { profiles: {}, answers: {}, likes: {}, passes: {} };
}
function readFaith() {
  try {
    const d = JSON.parse(fs.readFileSync(FAITH_FILE, "utf8"));
    if (
      d &&
      d.profiles && typeof d.profiles === "object" && !Array.isArray(d.profiles) &&
      d.answers && typeof d.answers === "object" && !Array.isArray(d.answers) &&
      d.likes && typeof d.likes === "object" && !Array.isArray(d.likes) &&
      d.passes && typeof d.passes === "object" && !Array.isArray(d.passes)
    )
      return d;
    return emptyFaith();
  } catch {
    return emptyFaith();
  }
}
function writeFaith(db) {
  const tmp = FAITH_FILE + ".tmp";
  fs.writeFileSync(tmp, JSON.stringify(db, null, 2));
  fs.renameSync(tmp, FAITH_FILE);
}
// The questionnaire catalog — ids, dimensions, option positions. The
// game client carries the SAME ids/values/positions with the question
// wording (original, written for Rizz Plaza). Positions sit on a
// 0..1 axis per question; compatibility is weighted agreement.
const FAITH_DIM_WEIGHTS = { faith: 3, church: 2, values: 2, family: 1.5, life: 1, intent: 2 };
const FAITH_CATALOG = {
  fq1: { dim: "faith", kind: "choice", pos: { "every-day": 1, "most-days": 0.66, "few-times": 0.33, "rarely": 0 } },
  fq2: { dim: "faith", kind: "choice", pos: { "daily": 1, "few-week": 0.66, "now-then": 0.33, "rarely": 0 } },
  fq3: { dim: "faith", kind: "scale" },
  fq4: { dim: "faith", kind: "scale" },
  cq1: { dim: "church", kind: "choice", pos: { "weekly": 1, "monthly": 0.66, "sometimes": 0.33, "not-yet": 0 } },
  cq2: { dim: "church", kind: "choice", pos: { "regularly": 1, "sometimes": 0.66, "a-little": 0.33, "not-yet": 0 } },
  cq3: { dim: "church", kind: "scale" },
  cq4: { dim: "church", kind: "scale" },
  vq1: { dim: "values", kind: "scale" },
  vq2: { dim: "values", kind: "choice", pos: { "regularly": 1, "sometimes": 0.66, "growing": 0.33, "not-yet": 0 } },
  vq3: { dim: "values", kind: "scale" },
  vq4: { dim: "values", kind: "scale" },
  kq1: { dim: "family", kind: "choice", pos: { "definitely": 1, "open": 0.66, "unsure": 0.33, "no-kids": 0 } },
  kq2: { dim: "family", kind: "scale" },
  kq3: { dim: "family", kind: "choice", pos: { "often": 1, "holidays": 0.66, "balanced": 0.33, "quiet": 0 } },
  kq4: { dim: "family", kind: "scale" },
  lq1: { dim: "life", kind: "choice", pos: { "never": 0, "rarely": 0.33, "socially": 0.66, "regularly": 1 } },
  lq2: { dim: "life", kind: "choice", pos: { "never": 0, "rarely": 0.33, "socially": 0.66, "regularly": 1 } },
  lq3: { dim: "life", kind: "choice", pos: { "outdoors": 0, "friends": 0.4, "family": 0.7, "home": 1 } },
  lq4: { dim: "life", kind: "scale" },
  iq1: { dim: "intent", kind: "choice", pos: { "friendship": 0, "purpose": 0.4, "courtship": 0.75, "marriage": 1 } },
  iq2: { dim: "intent", kind: "choice", pos: { "take-time": 0, "few-weeks": 0.5, "soon": 1 } },
  iq3: { dim: "intent", kind: "scale" },
  iq4: { dim: "intent", kind: "choice", pos: { "nearby": 0, "state": 0.5, "anywhere": 1 } },
};
const FAITH_QUESTION_COUNT = Object.keys(FAITH_CATALOG).length;
const FAITH_MIN_ANSWERED = 20; // of 24 — "completed questionnaire"
const FAITH_ATTENDANCE = ["weekly", "monthly", "occasionally", "seeking"];
const FAITH_INTENTS = ["friendship", "courtship", "marriage"];
const FAITH_MUST_HAVES = [
  "mh-faith", "mh-church", "mh-prayer", "mh-kids", "mh-nokids",
  "mh-nosmoke", "mh-family", "mh-honest", "mh-kind", "mh-serve",
];
const FAITH_CANT_STANDS = [
  "cs-smoking", "cs-drinking", "cs-faith", "cs-nochurch",
  "cs-nokids", "cs-kids", "cs-rush", "cs-cold",
];
function faithPos(qid, value) {
  const q = FAITH_CATALOG[qid];
  if (!q || value == null) return null;
  if (q.kind === "scale") {
    const n = Number(value);
    if (!Number.isInteger(n) || n < 1 || n > 5) return null;
    return (n - 1) / 4;
  }
  return Object.prototype.hasOwnProperty.call(q.pos, value) ? q.pos[value] : null;
}
function faithValidAnswer(qid, value) {
  return faithPos(qid, value) != null;
}
function faithAnsweredCount(rec) {
  if (!rec || !rec.answers || typeof rec.answers !== "object") return 0;
  let n = 0;
  for (const qid of Object.keys(rec.answers))
    if (FAITH_CATALOG[qid] && faithValidAnswer(qid, rec.answers[qid])) n++;
  return n;
}
function faithCompleted(rec) {
  return faithAnsweredCount(rec) >= FAITH_MIN_ANSWERED;
}
// Average answer POSITION per dimension for one user (their own lean),
// used for must-have checks and can't-stand detection.
function faithDimAvgPos(rec) {
  const sums = {}, counts = {};
  if (rec && rec.answers) {
    for (const qid of Object.keys(rec.answers)) {
      const q = FAITH_CATALOG[qid];
      if (!q) continue;
      const p = faithPos(qid, rec.answers[qid]);
      if (p == null) continue;
      sums[q.dim] = (sums[q.dim] || 0) + p;
      counts[q.dim] = (counts[q.dim] || 0) + 1;
    }
  }
  const out = {};
  for (const dim of Object.keys(sums)) out[dim] = sums[dim] / counts[dim];
  return out;
}
// Does viewer V's can't-stand list hit candidate C? Every rule reads
// only C's own answers/profile — V's list itself is never exposed.
function faithCantStandHit(cantStands, candRec, candProfile, candDimAvg) {
  const ans = (candRec && candRec.answers) || {};
  for (const cs of cantStands || []) {
    if (cs === "cs-smoking" && faithPos("lq1", ans.lq1) >= 1) return true;
    if (cs === "cs-drinking" && faithPos("lq2", ans.lq2) >= 1) return true;
    if (cs === "cs-faith" && candDimAvg.faith != null && candDimAvg.faith < 0.35) return true;
    if (cs === "cs-nochurch" && candProfile && candProfile.attendance === "occasionally") return true;
    if (cs === "cs-nokids" && faithPos("kq1", ans.kq1) === 0) return true;
    if (cs === "cs-kids" && faithPos("kq1", ans.kq1) === 1) return true;
    if (cs === "cs-rush" && faithPos("iq1", ans.iq1) >= 0.75) return true;
    if (cs === "cs-cold" && faithPos("fq1", ans.fq1) != null && faithPos("fq1", ans.fq1) <= 0.33) return true;
  }
  return false;
}
// Do all of viewer V's DETECTABLE must-haves pass for candidate C?
function faithMustHavesPass(mustHaves, candRec, candProfile, candDimAvg) {
  const ans = (candRec && candRec.answers) || {};
  for (const mh of mustHaves || []) {
    if (mh === "mh-faith" && !(candDimAvg.faith != null && candDimAvg.faith >= 0.6)) return false;
    if (mh === "mh-church" && !(candProfile && (candProfile.attendance === "weekly" || candProfile.attendance === "monthly"))) return false;
    if (mh === "mh-prayer" && !(faithPos("fq1", ans.fq1) >= 0.66)) return false;
    if (mh === "mh-kids" && !(faithPos("kq1", ans.kq1) >= 0.66)) return false;
    if (mh === "mh-nokids" && !(faithPos("kq1", ans.kq1) != null && faithPos("kq1", ans.kq1) <= 0.33)) return false;
    if (mh === "mh-nosmoke" && !(faithPos("lq1", ans.lq1) != null && faithPos("lq1", ans.lq1) <= 0.33)) return false;
    if (mh === "mh-family" && !(candDimAvg.family != null && candDimAvg.family >= 0.6)) return false;
    if (mh === "mh-honest" && !(candDimAvg.values != null && candDimAvg.values >= 0.6)) return false;
    if (mh === "mh-kind" && !(candDimAvg.values != null && candDimAvg.values >= 0.5)) return false;
    if (mh === "mh-serve" && !(faithPos("cq2", ans.cq2) >= 0.66)) return false;
  }
  return true;
}
// Compatibility % between two answer records: weighted agreement
// (1 - distance) per dimension, weighted by dimension importance.
function faithCompatibility(recA, recB) {
  const sims = {}, weights = {};
  const a = (recA && recA.answers) || {};
  const b = (recB && recB.answers) || {};
  for (const qid of Object.keys(FAITH_CATALOG)) {
    const pa = faithPos(qid, a[qid]);
    const pb = faithPos(qid, b[qid]);
    if (pa == null || pb == null) continue;
    const dim = FAITH_CATALOG[qid].dim;
    sims[dim] = (sims[dim] || 0) + (1 - Math.abs(pa - pb));
    weights[dim] = (weights[dim] || 0) + 1;
  }
  let num = 0, den = 0;
  for (const dim of Object.keys(sims)) {
    const w = FAITH_DIM_WEIGHTS[dim] || 1;
    num += w * (sims[dim] / weights[dim]);
    den += w;
  }
  if (!den) return 0;
  return Math.max(0, Math.min(100, Math.round((num / den) * 100)));
}
function faithIdList(db, key, userId) {
  const arr = db[key][userId];
  return Array.isArray(arr) ? arr.filter((x) => typeof x === "string") : [];
}
function faithPublicProfile(p) {
  if (!p) return null;
  return {
    testimony: p.testimony || "",
    denomination: p.denomination || "",
    attendance: p.attendance || "",
    intent: p.intent || "",
    optedIn: !!p.optedIn,
  };
}
app.put("/api/faith/profile", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  const b = req.body || {};
  const testimony = String(b.testimony || "").replace(/[<>]/g, "").trim().slice(0, 140);
  const denomination = String(b.denomination || "").replace(/[<>]/g, "").trim().slice(0, 40);
  const attendance = String(b.attendance || "");
  const intent = String(b.intent || "");
  if (!FAITH_ATTENDANCE.includes(attendance))
    return res.status(400).json({ ok: false, error: "Pick how often you attend church" });
  if (!FAITH_INTENTS.includes(intent))
    return res.status(400).json({ ok: false, error: "Pick what you're looking for" });
  if (b.optedIn !== undefined && typeof b.optedIn !== "boolean")
    return res.status(400).json({ ok: false, error: "optedIn must be true or false" });
  const db = readFaith();
  const prof = {
    testimony,
    denomination,
    attendance,
    intent,
    optedIn: b.optedIn === true,
    updatedAt: new Date().toISOString(),
  };
  db.profiles[ctx.user.id] = prof;
  writeFaith(db);
  res.json({ ok: true, profile: faithPublicProfile(prof) });
});
app.get("/api/faith/profile", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  const db = readFaith();
  res.json({ ok: true, profile: faithPublicProfile(db.profiles[ctx.user.id] || null) });
});
app.put("/api/faith/answers", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  const b = req.body || {};
  const answers = b.answers;
  if (!answers || typeof answers !== "object" || Array.isArray(answers))
    return res.status(400).json({ ok: false, error: "answers must be an object" });
  const clean = {};
  for (const qid of Object.keys(answers)) {
    if (!FAITH_CATALOG[qid])
      return res.status(400).json({ ok: false, error: "Unknown question: " + qid });
    const val = FAITH_CATALOG[qid].kind === "scale" ? String(answers[qid]) : String(answers[qid] || "");
    if (!faithValidAnswer(qid, val))
      return res.status(400).json({ ok: false, error: "Invalid answer for question: " + qid });
    clean[qid] = val;
  }
  function cleanIdList(list, allowed, label) {
    if (list === undefined) return [];
    if (!Array.isArray(list))
      return null;
    const out = [];
    for (const id of list) {
      const s = String(id || "");
      if (!allowed.includes(s)) return null;
      if (!out.includes(s)) out.push(s);
    }
    if (out.length > 5) return null;
    return out;
  }
  const mustHaves = cleanIdList(b.mustHaves, FAITH_MUST_HAVES, "mustHaves");
  if (mustHaves === null)
    return res.status(400).json({ ok: false, error: "mustHaves must be up to 5 known choices" });
  const cantStands = cleanIdList(b.cantStands, FAITH_CANT_STANDS, "cantStands");
  if (cantStands === null)
    return res.status(400).json({ ok: false, error: "cantStands must be up to 5 known choices" });
  const db = readFaith();
  db.answers[ctx.user.id] = {
    answers: clean,
    mustHaves,
    cantStands,
    updatedAt: new Date().toISOString(),
  };
  writeFaith(db);
  res.json({ ok: true, answered: faithAnsweredCount(db.answers[ctx.user.id]), total: FAITH_QUESTION_COUNT });
});
app.get("/api/faith/answers", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  const db = readFaith();
  const rec = db.answers[ctx.user.id] || null;
  res.json({
    ok: true,
    answers: rec ? rec.answers : {},
    mustHaves: rec ? rec.mustHaves : [],
    cantStands: rec ? rec.cantStands : [],
    answered: faithAnsweredCount(rec),
    total: FAITH_QUESTION_COUNT,
  });
});
app.get("/api/faith/discover", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  const meId = ctx.user.id;
  const db = readFaith();
  const myProf = db.profiles[meId] || null;
  const myRec = db.answers[meId] || null;
  if (!myProf || !myProf.optedIn)
    return res.json({ ok: true, ready: false, reason: "not-opted-in", results: [] });
  if (!faithCompleted(myRec))
    return res.json({ ok: true, ready: false, reason: "no-answers", results: [] });
  const myDimAvg = faithDimAvgPos(myRec);
  const myLikes = faithIdList(db, "likes", meId);
  const myPasses = faithIdList(db, "passes", meId);
  const dmDb = readDms();
  const results = [];
  for (const other of ctx.db.users) {
    if (!other || other.id === meId || other.deletionAt) continue;
    const prof = db.profiles[other.id];
    if (!prof || !prof.optedIn) continue;
    const rec = db.answers[other.id];
    if (!faithCompleted(rec)) continue;
    if (myPasses.includes(other.id)) continue;
    if (dmEitherBlocked(dmDb, meId, other.id)) continue;
    const dimAvg = faithDimAvgPos(rec);
    let pct = faithCompatibility(myRec, rec);
    // A can't-stand conflict in EITHER direction caps the score and
    // flags the pairing — neither side's list is ever revealed.
    const dealbreaker =
      faithCantStandHit(myRec.cantStands, rec, prof, dimAvg) ||
      faithCantStandHit(rec.cantStands, myRec, myProf, myDimAvg);
    if (dealbreaker) pct = Math.min(pct, 49);
    results.push({
      id: other.id,
      name: other.name,
      denomination: prof.denomination || "",
      attendance: prof.attendance,
      intent: prof.intent,
      testimony: prof.testimony || "",
      pct,
      dealbreaker: !!dealbreaker,
      mustHavePass: faithMustHavesPass(myRec.mustHaves, rec, prof, dimAvg),
      iLiked: myLikes.includes(other.id),
      matched: myLikes.includes(other.id) && faithIdList(db, "likes", other.id).includes(meId),
    });
  }
  results.sort((x, y) => y.pct - x.pct);
  res.json({ ok: true, ready: true, results: results.slice(0, 50) });
});
app.post("/api/faith/like", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  const targetId = String((req.body || {}).userId || "");
  if (!targetId || targetId === ctx.user.id)
    return res.status(400).json({ ok: false, error: "You can't like yourself" });
  const target = ctx.db.users.find((u) => u.id === targetId);
  if (!target || target.deletionAt)
    return res.status(404).json({ ok: false, error: "Account not found" });
  if (dmEitherBlocked(readDms(), ctx.user.id, targetId))
    return res.status(403).json({ ok: false, error: "Not available" });
  const db = readFaith();
  const likes = faithIdList(db, "likes", ctx.user.id);
  if (!likes.includes(targetId)) {
    likes.push(targetId);
    db.likes[ctx.user.id] = likes;
    writeFaith(db);
  }
  const matched = faithIdList(db, "likes", targetId).includes(ctx.user.id);
  res.json({ ok: true, matched });
});
app.post("/api/faith/pass", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  const targetId = String((req.body || {}).userId || "");
  if (!targetId || targetId === ctx.user.id)
    return res.status(400).json({ ok: false, error: "You can't pass yourself" });
  const target = ctx.db.users.find((u) => u.id === targetId);
  if (!target || target.deletionAt)
    return res.status(404).json({ ok: false, error: "Account not found" });
  const db = readFaith();
  const passes = faithIdList(db, "passes", ctx.user.id);
  if (!passes.includes(targetId)) passes.push(targetId);
  db.passes[ctx.user.id] = passes;
  // A pass overrides an earlier like.
  const likes = faithIdList(db, "likes", ctx.user.id).filter((x) => x !== targetId);
  db.likes[ctx.user.id] = likes;
  writeFaith(db);
  res.json({ ok: true });
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


// ---------------------------------------------------------------------------
// RP-V7.10: Money Live — the server ledger of record for signed-in
// accounts: charm balances, host earnings (with holds), premium,
// Stripe Connect cash-outs. Data lives in money.json beside
// accounts.json (same volume, same atomic-write pattern):
//   { balances: { acctId: charms },
//     earnings: { acctId: { availableCents,
//                           held: [{ cents, unlockAt, reason }],
//                           totalEarnedCents } },
//     premium:  { acctId: { active, until, subRef, customerRef, plan } },
//     cashouts: [ { id, acctId, cents, feeCents, status, at,
//                   unlockReviewAt, transferRef?, sentAt? } ],
//     txlog:    [ { id, at, type, from, to, charms, cents, cut, ref } ],
//     processed:{ <stripe session id>: iso } }   // webhook idempotency
//
// STRIPE IS INERT UNTIL THE OWNER SETS KEYS: with no STRIPE_SECRET_KEY
// every purchase/subscribe/connect route answers
// { ok:false, error:"payments-not-configured" } and nothing is charged
// or credited for money — the ledger math below still runs (gifts
// between accounts, holds, cash-out queueing) so it can be tested and
// so balances are real the moment keys land. No secrets live in code:
// keys come from Railway env (STRIPE_SECRET_KEY / STRIPE_WEBHOOK_SECRET).
// Checkout uses inline price_data — no pre-created Stripe products.
// The stripe npm package is NOT a dependency, so Stripe is reached via
// its REST API with fetch, and webhook signatures are verified manually
// (HMAC-SHA256 over "<timestamp>.<raw body>", 5-minute tolerance).
//
// Settled economics (owner-approved; do not change casually):
//   charm packs: $0.99/100, $4.99/550, $9.99/1200, $19.99/2500, $49.99/7000
//   gift earnings: host 70% / platform 30%
//   auction earnings: platform cut 10% (host 90%)
//   cash-out: minimum $20.00, max 1 per day, 25c payout fee deducted
//   premium: $9.99/mo or $59.99/yr
// Cash-out safeguards (from the approved Cash-Out Letter briefing):
//   a single gift worth $100+ is HELD for HOLD_DAYS before it can be
//   cashed out (chargeback cover), and a host's first-ever payout is
//   held FIRST_PAYOUT_HOLD_DAYS for review. Unlocking is lazy: holds
//   mature into "available" whenever the owner reads their balance.
//   "Unlock today" is NOT "paid today" — the client says so plainly.
// ---------------------------------------------------------------------------
const MONEY_FILE =
  process.env.MONEY_FILE || path.join(path.dirname(PHOTO_DIR), "money.json");
const CHARM_CENT_VALUE = 1; // 1 charm of gift value = 1 cent (the Plaza's
// charm packs price charms at roughly 1c each in the base pack, and the
// gift catalog is denominated in charms at 1 charm = 1c of gift value).
const GIFT_HOST_PCT = 70; // host share of gift value; platform keeps rest
const AUCTION_HOST_PCT = 90; // platform cut on auctions is 10%
const MONEY_CASHOUT_MIN_CENTS = 2000; // $20.00
const MONEY_CASHOUT_FEE_CENTS = 25; // 25c payout fee, deducted from payout
const LARGE_GIFT_HOLD_CENTS = 10000; // $100 — single gifts at/above hold
const HOLD_DAYS = 3; // large-gift hold length
const FIRST_PAYOUT_HOLD_DAYS = 3; // first-ever cash-out review hold
const CHARM_PACKS = {
  pack100: { priceCents: 99, charms: 100, label: "100 charms" },
  pack550: { priceCents: 499, charms: 550, label: "550 charms" },
  pack1200: { priceCents: 999, charms: 1200, label: "1,200 charms" },
  pack2500: { priceCents: 1999, charms: 2500, label: "2,500 charms" },
  pack7000: { priceCents: 4999, charms: 7000, label: "7,000 charms" },
};
const PREMIUM_PLANS = {
  monthly: { priceCents: 999, interval: "month", label: "Premium monthly" },
  yearly: { priceCents: 5999, interval: "year", label: "Premium yearly" },
};
// Mirror of the game client's GIFT_SHOP catalog (id -> charm cost). The
// server charges the CATALOG cost — a client-sent amount is never
// trusted for ledger math.
const MONEY_GIFT_TABLE = {
  heart: 1, rose: 5, coffee: 10, icecream: 25, donut: 30, clap: 50,
  fingerheart: 99, kiss: 100, fireworks: 200, motorcycle: 300,
  sportscar: 500, loveballoon: 600, airplane: 800, moneygun: 999,
  castle: 1000, volcano: 2000, lion: 2500, dragon: 3000, meteor: 4000,
  whale: 4500, galaxy: 5000, diamonds: 6000, rocket: 7500,
  ferriswheel: 9900, jet: 10000, yacht: 15000, phoenix: 25000,
  universe: 50000,
};
function emptyMoney() {
  return {
    balances: {},
    earnings: {},
    premium: {},
    cashouts: [],
    txlog: [],
    processed: {},
  };
}
function readMoney() {
  try {
    const d = JSON.parse(fs.readFileSync(MONEY_FILE, "utf8"));
    if (
      d &&
      d.balances && typeof d.balances === "object" && !Array.isArray(d.balances) &&
      d.earnings && typeof d.earnings === "object" && !Array.isArray(d.earnings) &&
      d.premium && typeof d.premium === "object" && !Array.isArray(d.premium) &&
      Array.isArray(d.cashouts) && Array.isArray(d.txlog)
    ) {
      if (!d.processed || typeof d.processed !== "object" || Array.isArray(d.processed))
        d.processed = {};
      return d;
    }
    return emptyMoney();
  } catch {
    return emptyMoney();
  }
}
function writeMoney(db) {
  const tmp = MONEY_FILE + ".tmp";
  fs.writeFileSync(tmp, JSON.stringify(db, null, 2));
  fs.renameSync(tmp, MONEY_FILE);
}
function moneyEarningsFor(db, acctId) {
  let e = db.earnings[acctId];
  if (!e || typeof e !== "object") {
    e = { availableCents: 0, held: [], totalEarnedCents: 0 };
    db.earnings[acctId] = e;
  }
  if (!Array.isArray(e.held)) e.held = [];
  if (typeof e.availableCents !== "number") e.availableCents = 0;
  if (typeof e.totalEarnedCents !== "number") e.totalEarnedCents = 0;
  return e;
}
function moneyHeldCents(e) {
  return (e.held || []).reduce((sum, h) => sum + (h.cents || 0), 0);
}
// Move matured holds into available. Returns true when anything moved.
function unlockMoneyHolds(db, acctId) {
  const e = moneyEarningsFor(db, acctId);
  const now = Date.now();
  let moved = 0;
  e.held = e.held.filter((h) => {
    if (h && Date.parse(h.unlockAt) <= now) {
      moved += h.cents || 0;
      return false;
    }
    return true;
  });
  if (moved > 0) {
    e.availableCents += moved;
    return true;
  }
  return false;
}
function moneyTx(db, entry) {
  db.txlog.push(
    Object.assign(
      { id: crypto.randomBytes(8).toString("hex"), at: new Date().toISOString() },
      entry
    )
  );
  while (db.txlog.length > 5000) db.txlog.shift();
}
function moneyPremiumState(db, acctId) {
  const p = db.premium[acctId];
  if (!p) return { active: false, until: null };
  const active =
    !!p.active && (!p.until || Date.parse(p.until) > Date.now());
  return { active, until: p.until || null };
}
function moneyCashedOutToday(db, acctId) {
  const today = new Date().toISOString().slice(0, 10);
  return db.cashouts.some(
    (c) =>
      c.acctId === acctId &&
      String(c.at).slice(0, 10) === today &&
      c.status !== "failed"
  );
}
function moneyPublicCashout(c) {
  return {
    id: c.id,
    cents: c.cents,
    feeCents: c.feeCents,
    netCents: c.cents - c.feeCents,
    status: c.status,
    at: c.at,
    unlockReviewAt: c.unlockReviewAt || null,
  };
}
function stripeConfigured() {
  return !!process.env.STRIPE_SECRET_KEY;
}
function stripeNotConfigured(res) {
  return res.json({ ok: false, error: "payments-not-configured" });
}
// Minimal Stripe REST client (form-encoded, like the API expects).
function stripeEncode(params, prefix, out) {
  out = out || new URLSearchParams();
  for (const k of Object.keys(params || {})) {
    const v = params[k];
    if (v === undefined || v === null) continue;
    const key = prefix ? prefix + "[" + k + "]" : k;
    if (Array.isArray(v)) {
      v.forEach((item, i) => {
        if (item && typeof item === "object")
          stripeEncode(item, key + "[" + i + "]", out);
        else out.append(key + "[" + i + "]", String(item));
      });
    } else if (typeof v === "object") {
      stripeEncode(v, key, out);
    } else {
      out.append(key, String(v));
    }
  }
  return out;
}
async function stripeApi(method, p, params) {
  const res = await fetch("https://api.stripe.com/v1" + p, {
    method,
    headers: {
      Authorization: "Bearer " + process.env.STRIPE_SECRET_KEY,
      "Content-Type": "application/x-www-form-urlencoded",
    },
    body: method === "GET" ? undefined : stripeEncode(params).toString(),
  });
  const data = await res.json().catch(() => ({}));
  if (!res.ok) {
    const msg =
      (data && data.error && data.error.message) || "Stripe HTTP " + res.status;
    throw new Error(msg);
  }
  return data;
}
// Lazily move queued cash-outs toward Stripe when everything is in
// place (hold matured + Stripe configured + host connected + payouts
// enabled). Returns true when the money store changed.
async function moneyProcessCashouts(db, accountsDb) {
  if (!stripeConfigured()) return false;
  let changed = false;
  for (const c of db.cashouts) {
    if (c.status !== "queued" && c.status !== "queued-needs-connect") continue;
    if (c.unlockReviewAt && Date.parse(c.unlockReviewAt) > Date.now()) continue;
    const user = accountsDb.users.find((u) => u.id === c.acctId);
    if (!user || !user.stripeAccountId) {
      if (c.status !== "queued-needs-connect") {
        c.status = "queued-needs-connect";
        changed = true;
      }
      continue;
    }
    try {
      const acct = await stripeApi("GET", "/accounts/" + user.stripeAccountId);
      if (!acct.payouts_enabled) {
        if (c.status !== "queued-needs-connect") {
          c.status = "queued-needs-connect";
          changed = true;
        }
        continue;
      }
      const tr = await stripeApi("POST", "/transfers", {
        amount: c.cents - c.feeCents,
        currency: "usd",
        destination: user.stripeAccountId,
        transfer_group: "cashout_" + c.id,
        metadata: { cashoutId: c.id, acctId: c.acctId },
      });
      c.status = "sent";
      c.transferRef = tr.id;
      c.sentAt = new Date().toISOString();
      changed = true;
      console.log("[money] cashout sent", c.id, c.cents - c.feeCents, "->", user.stripeAccountId);
    } catch (e) {
      console.error("[money] cashout transfer failed", c.id, e.message);
    }
  }
  return changed;
}
async function moneyConnectInfo(user) {
  const info = {
    configured: stripeConfigured(),
    connected: !!user.stripeAccountId,
    payoutsEnabled: false,
  };
  if (info.configured && user.stripeAccountId) {
    try {
      const a = await stripeApi("GET", "/accounts/" + user.stripeAccountId);
      info.payoutsEnabled = !!a.payouts_enabled;
      info.connected = !!(a.details_submitted || a.payouts_enabled);
    } catch (e) {
      /* leave defaults — status is best-effort */
    }
  }
  return info;
}
function moneyMePayload(db, user, connect) {
  const e = moneyEarningsFor(db, user.id);
  const heldCents = moneyHeldCents(e);
  let nextUnlockAt = null;
  for (const h of e.held) {
    if (h && h.unlockAt && (!nextUnlockAt || h.unlockAt < nextUnlockAt))
      nextUnlockAt = h.unlockAt;
  }
  const cashedToday = moneyCashedOutToday(db, user.id);
  const reasons = [];
  if (e.availableCents < MONEY_CASHOUT_MIN_CENTS) reasons.push("below-minimum");
  if (cashedToday) reasons.push("already-cashed-out-today");
  return {
    ok: true,
    charms: db.balances[user.id] || 0,
    earnings: {
      availableCents: e.availableCents,
      heldCents,
      held: e.held,
      nextUnlockAt,
      totalEarnedCents: e.totalEarnedCents,
    },
    premium: moneyPremiumState(db, user.id),
    cashoutEligibility: { canCashOut: reasons.length === 0, reasons },
    connect,
    paymentsConfigured: stripeConfigured(),
  };
}
app.get("/api/money/me", async (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  const db = readMoney();
  let changed = unlockMoneyHolds(db, ctx.user.id);
  if (await moneyProcessCashouts(db, ctx.db)) changed = true;
  if (changed) writeMoney(db);
  const connect = await moneyConnectInfo(ctx.user);
  res.json(moneyMePayload(db, ctx.user, connect));
});
app.post("/api/money/checkout", async (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  const pack = CHARM_PACKS[String((req.body || {}).packId || "")];
  if (!pack)
    return res.status(400).json({ ok: false, error: "Unknown charm pack" });
  if (!stripeConfigured()) return stripeNotConfigured(res);
  try {
    const origin = siteOrigin(req);
    const session = await stripeApi("POST", "/checkout/sessions", {
      mode: "payment",
      success_url: origin + "/?money=ok",
      cancel_url: origin + "/?money=cancel",
      line_items: [
        {
          quantity: 1,
          price_data: {
            currency: "usd",
            unit_amount: pack.priceCents,
            product_data: { name: "Rizz Plaza charms — " + pack.label },
          },
        },
      ],
      metadata: {
        kind: "charms",
        acctId: ctx.user.id,
        packId: String((req.body || {}).packId || ""),
        charms: String(pack.charms),
        priceCents: String(pack.priceCents),
      },
    });
    res.json({ ok: true, url: session.url });
  } catch (e) {
    console.error("[money] checkout failed", e.message);
    res.status(502).json({ ok: false, error: "stripe-error" });
  }
});
app.post("/api/money/subscribe", async (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  const planName = String((req.body || {}).plan || "");
  const plan = PREMIUM_PLANS[planName];
  if (!plan)
    return res.status(400).json({ ok: false, error: "Unknown premium plan" });
  if (!stripeConfigured()) return stripeNotConfigured(res);
  try {
    const origin = siteOrigin(req);
    const session = await stripeApi("POST", "/checkout/sessions", {
      mode: "subscription",
      success_url: origin + "/?money=ok",
      cancel_url: origin + "/?money=cancel",
      line_items: [
        {
          quantity: 1,
          price_data: {
            currency: "usd",
            unit_amount: plan.priceCents,
            recurring: { interval: plan.interval },
            product_data: { name: "Rizz Plaza " + plan.label },
          },
        },
      ],
      metadata: { kind: "premium", acctId: ctx.user.id, plan: planName },
      subscription_data: {
        metadata: { kind: "premium", acctId: ctx.user.id, plan: planName },
      },
    });
    res.json({ ok: true, url: session.url });
  } catch (e) {
    console.error("[money] subscribe failed", e.message);
    res.status(502).json({ ok: false, error: "stripe-error" });
  }
});
// Stripe webhook (route registered before the JSON parser, near the top
// of this file). No account auth — authenticity is the signature. With
// no STRIPE_WEBHOOK_SECRET set, events are acknowledged and IGNORED:
// nothing is ever credited on an unverified event.
function stripeWebhookHandler(req, res) {
  const secret = process.env.STRIPE_WEBHOOK_SECRET;
  if (!secret)
    return res.json({ received: true, ignored: "webhook-secret-not-configured" });
  const raw = Buffer.isBuffer(req.body) ? req.body : Buffer.from("");
  const header = String(req.headers["stripe-signature"] || "");
  let t = null;
  const v1s = [];
  for (const part of header.split(",")) {
    const eq = part.indexOf("=");
    if (eq < 0) continue;
    const k = part.slice(0, eq).trim();
    const v = part.slice(eq + 1).trim();
    if (k === "t") t = v;
    else if (k === "v1") v1s.push(v);
  }
  if (!t || !v1s.length)
    return res.status(400).json({ received: false, error: "bad-signature" });
  if (Math.abs(Date.now() / 1000 - Number(t)) > 300)
    return res.status(400).json({ received: false, error: "stale-timestamp" });
  const h = crypto.createHmac("sha256", secret);
  h.update(t + ".", "utf8");
  h.update(raw);
  const expected = h.digest("hex");
  const ok = v1s.some((v) => {
    try {
      const a = Buffer.from(v, "utf8");
      const b = Buffer.from(expected, "utf8");
      return a.length === b.length && crypto.timingSafeEqual(a, b);
    } catch (e) {
      return false;
    }
  });
  if (!ok)
    return res.status(400).json({ received: false, error: "bad-signature" });
  let event;
  try {
    event = JSON.parse(raw.toString("utf8"));
  } catch (e) {
    return res.status(400).json({ received: false, error: "bad-json" });
  }
  try {
    handleStripeEvent(event);
  } catch (e) {
    console.error("[money] webhook event handling failed", e.message);
  }
  res.json({ received: true });
}
function handleStripeEvent(event) {
  const type = String((event && event.type) || "");
  const obj = (event && event.data && event.data.object) || {};
  if (type === "checkout.session.completed") {
    const md = obj.metadata || {};
    const acctId = String(md.acctId || "");
    if (!acctId || !obj.id) return;
    const db = readMoney();
    if (db.processed[obj.id]) return; // idempotent on the session id
    const user = readAccounts().users.find((u) => u.id === acctId);
    if (!user) return;
    if (md.kind === "charms") {
      const charms = parseInt(md.charms, 10) || 0;
      if (charms > 0) {
        db.balances[acctId] = (db.balances[acctId] || 0) + charms;
        moneyTx(db, {
          type: "purchase", from: null, to: acctId,
          charms, cents: parseInt(md.priceCents, 10) || 0, cut: 0, ref: obj.id,
        });
        console.log("[money] charms credited", charms, "to", user.name);
      }
    } else if (md.kind === "premium") {
      const plan = md.plan === "yearly" ? "yearly" : "monthly";
      db.premium[acctId] = {
        active: true,
        until: new Date(
          Date.now() + (plan === "yearly" ? 366 : 32) * 24 * 3600 * 1000
        ).toISOString(),
        subRef: obj.subscription || null,
        customerRef: obj.customer || null,
        plan,
      };
      moneyTx(db, {
        type: "premium", from: null, to: acctId, charms: 0,
        cents: plan === "yearly" ? 5999 : 999, cut: 0, ref: obj.id,
      });
      console.log("[money] premium on for", user.name, plan);
    } else {
      return; // unknown kind — do not mark processed
    }
    db.processed[obj.id] = new Date().toISOString();
    writeMoney(db);
    return;
  }
  if (type === "invoice.paid") {
    const subId = obj.subscription;
    if (!subId) return;
    const db = readMoney();
    const acctId = Object.keys(db.premium).find(
      (id) => db.premium[id] && db.premium[id].subRef === subId
    );
    if (!acctId) return;
    const line =
      (obj.lines && Array.isArray(obj.lines.data) && obj.lines.data[0]) || null;
    const endSec =
      (line && line.period && line.period.end) || obj.period_end || null;
    if (endSec) db.premium[acctId].until = new Date(endSec * 1000).toISOString();
    db.premium[acctId].active = true;
    moneyTx(db, {
      type: "premium-renew", from: null, to: acctId, charms: 0,
      cents: obj.amount_paid || 0, cut: 0, ref: obj.id,
    });
    writeMoney(db);
    return;
  }
  if (type === "customer.subscription.deleted") {
    const db = readMoney();
    const acctId = Object.keys(db.premium).find(
      (id) => db.premium[id] && db.premium[id].subRef === obj.id
    );
    if (!acctId) return;
    // Premium ends at the period end Stripe reports — which is when
    // this event fires for an end-of-period cancellation.
    db.premium[acctId].active = false;
    if (obj.current_period_end)
      db.premium[acctId].until = new Date(obj.current_period_end * 1000).toISOString();
    moneyTx(db, {
      type: "premium-off", from: null, to: acctId, charms: 0,
      cents: 0, cut: 0, ref: obj.id,
    });
    writeMoney(db);
    return;
  }
}
// Send a gift, ledger-first: the sender's charms are debited and the
// recipient's earnings credited HERE — the room animation/proto the
// client plays afterwards is just the show; this is the money.
app.post("/api/money/gift", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  const b = req.body || {};
  const giftId = String(b.giftId || "");
  const cost = MONEY_GIFT_TABLE[giftId];
  if (!cost)
    return res.status(400).json({ ok: false, error: "Unknown gift" });
  const sentCharms = Math.floor(Number(b.charms) || 0);
  if (sentCharms <= 0)
    return res.status(400).json({ ok: false, error: "Invalid charm amount" });
  // Recipient: exact unique display-name match, the same resolution
  // rule as /api/social/follow-name. Unresolvable (no account, or the
  // name is not unique) → 404 and NOTHING moves.
  const toName = String(b.toName || "").trim().slice(0, 40);
  if (!toName)
    return res.status(400).json({ ok: false, error: "Missing recipient" });
  const matches = ctx.db.users.filter(
    (u) => u.name === toName && u.id !== ctx.user.id
  );
  if (matches.length !== 1) {
    if (toName === ctx.user.name && matches.length === 0)
      return res
        .status(400)
        .json({ ok: false, error: "You can't gift yourself" });
    return res
      .status(404)
      .json({ ok: false, resolved: false, error: "recipient-not-found" });
  }
  const recipient = matches[0];
  const db = readMoney();
  const balance = db.balances[ctx.user.id] || 0;
  if (balance < cost)
    return res.status(400).json({
      ok: false,
      error: "insufficient-charms",
      balance,
      needed: cost,
    });
  db.balances[ctx.user.id] = balance - cost;
  const giftValueCents = cost * CHARM_CENT_VALUE;
  const hostShare = Math.floor((giftValueCents * GIFT_HOST_PCT) / 100);
  const platformCut = giftValueCents - hostShare;
  const earn = moneyEarningsFor(db, recipient.id);
  let held = false;
  if (giftValueCents >= LARGE_GIFT_HOLD_CENTS) {
    earn.held.push({
      cents: hostShare,
      unlockAt: new Date(
        Date.now() + HOLD_DAYS * 24 * 3600 * 1000
      ).toISOString(),
      reason: "large-gift",
    });
    held = true;
  } else {
    earn.availableCents += hostShare;
  }
  earn.totalEarnedCents += hostShare;
  const txBase = {
    from: ctx.user.id,
    to: recipient.id,
    charms: cost,
    ref: giftId,
  };
  moneyTx(db, Object.assign({}, txBase, {
    type: "gift-sent", cents: giftValueCents, cut: platformCut,
  }));
  moneyTx(db, Object.assign({}, txBase, {
    type: "gift-received", cents: hostShare, cut: platformCut,
  }));
  writeMoney(db);
  rankCreditDaily(recipient.id, recipient.name, cost);
  // [RP-V7.40] Gifting is the strongest interest signal there is: +4
  // affinity from the gifter toward the host, into the SAME interest
  // store the Reels + live rankings read. Per gift EVENT only — the
  // charm amount is never a ranking input. Bonus bookkeeping: wrapped
  // so it can never fail a gift that already moved money.
  try {
    const gSig = readReelSignals();
    const gRec = fyUserRec(gSig, ctx.user.id, true);
    fyBump(gRec, recipient.id, 4, Date.now());
    writeReelSignals(gSig);
  } catch (e) { /* affinity bookkeeping must never break a gift */ }
  // [RP-V7.41] Plaza Pot growth match: a gift landing on a host with an
  // open pot grows the pot by the platform match (10% of the gift's
  // charm value, capped at the seed). Pot accounting only, in its own
  // try/catch for the same reason as the affinity hook above.
  try {
    potOnGift(recipient.id, cost);
  } catch (e) { /* pot bookkeeping must never break a gift */ }
  // [RP-V7.42] Daily Pot growth match: EVERY gift on the Plaza also
  // grows the whole-Plaza Daily Pot by 2% of its charm value (platform
  // match, capped per day) — a gift can feed a live pot AND the Daily
  // Pot; both matches are platform-side and the split above is final.
  try {
    dailyPotOnGift(cost);
  } catch (e) { /* daily pot bookkeeping must never break a gift */ }
  console.log(
    "[money] gift", giftId, cost, "charms:", ctx.user.name, "->", recipient.name,
    "| host", hostShare, "c", held ? "(held)" : "", "| cut", platformCut, "c"
  );
  res.json({
    ok: true,
    balance: db.balances[ctx.user.id],
    charged: cost,
    recipient: { id: recipient.id, name: recipient.name },
    hostShareCents: hostShare,
    held,
  });
});
// RP-V7.22: Daily host rankings. A lightweight tally of charms gifted
// per host per calendar day (America/New_York), credited from the
// /api/money/gift path below - the money ledger stays the source of
// truth for balances; this file only feeds the Daily Ranking sheet in
// the live view.
const RANKINGS_FILE =
  process.env.RANKINGS_FILE ||
  path.join(path.dirname(PHOTO_DIR), "rankings.json");
function rankDayKey() {
  try {
    return new Intl.DateTimeFormat("en-CA", {
      timeZone: "America/New_York",
      year: "numeric",
      month: "2-digit",
      day: "2-digit",
    }).format(new Date());
  } catch (e) {
    return new Date().toISOString().slice(0, 10);
  }
}
function readRankings() {
  try {
    const j = JSON.parse(fs.readFileSync(RANKINGS_FILE, "utf8"));
    if (j && typeof j === "object" && j.hosts) return j;
  } catch (e) {}
  return { day: rankDayKey(), hosts: {} };
}
function writeRankings(db) {
  const tmp = RANKINGS_FILE + ".tmp";
  fs.writeFileSync(tmp, JSON.stringify(db, null, 2));
  fs.renameSync(tmp, RANKINGS_FILE);
}
function rankCreditDaily(hostId, hostName, charms) {
  try {
    if (!hostId || !(charms > 0)) return;
    const day = rankDayKey();
    let db = readRankings();
    if (db.day !== day) db = { day, hosts: {} };
    const h =
      db.hosts[hostId] || (db.hosts[hostId] = { name: "", total: 0, gifts: 0 });
    if (hostName) h.name = hostName;
    h.total += charms;
    h.gifts += 1;
    writeRankings(db);
  } catch (e) {}
}
app.get("/api/rankings/daily", (req, res) => {
  const day = rankDayKey();
  const db = readRankings();
  // [RP-V7.37] Pending-deletion hosts are invisible on the board.
  let pendingHosts = new Set();
  try {
    pendingHosts = new Set(
      readAccounts()
        .users.filter((u) => u.deletionAt)
        .map((u) => u.id)
    );
  } catch (e) {}
  const rows =
    db.day === day
      ? Object.keys(db.hosts)
          .filter((id) => !pendingHosts.has(id))
          .map((id) => ({
            hostId: id,
            name: db.hosts[id].name || "",
            total: db.hosts[id].total || 0,
            gifts: db.hosts[id].gifts || 0,
          }))
      : [];
  rows.sort((a, b) => b.total - a.total);
  rows.forEach((r, i) => {
    r.rank = i + 1;
  });
  let me = null;
  try {
    const user = accountForToken(readAccounts(), req);
    if (user) {
      const mine = rows.find((r) => r.hostId === user.id);
      if (mine)
        me = {
          rank: mine.rank,
          total: mine.total,
          gap: mine.rank > 1 ? rows[mine.rank - 2].total - mine.total : 0,
        };
    }
  } catch (e) {}
  res.json({ ok: true, day, top: rows.slice(0, 50), me });
});
// Auction earnings recorder (10% platform cut). The auction engine can
// call this when a winner's payment clears; for now it is also how an
// auction earning can be recorded against a seller's account. Credits
// the CALLER's earnings — a seller only ever records their own sales.
function recordAuctionEarning(db, acctId, grossCents, ref) {
  const hostShare = Math.floor((grossCents * AUCTION_HOST_PCT) / 100);
  const cut = grossCents - hostShare;
  const earn = moneyEarningsFor(db, acctId);
  earn.availableCents += hostShare;
  earn.totalEarnedCents += hostShare;
  moneyTx(db, {
    type: "auction", from: null, to: acctId, charms: 0,
    cents: grossCents, cut, ref: String(ref || ""),
  });
  return { hostShare, cut };
}
app.post("/api/money/auction-earning", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  const gross = Math.floor(Number((req.body || {}).grossCents) || 0);
  if (gross <= 0 || gross > 10000000)
    return res.status(400).json({ ok: false, error: "Invalid amount" });
  const db = readMoney();
  unlockMoneyHolds(db, ctx.user.id);
  const out = recordAuctionEarning(
    db,
    ctx.user.id,
    gross,
    (req.body || {}).ref
  );
  writeMoney(db);
  res.json({ ok: true, hostShareCents: out.hostShare, cutCents: out.cut });
});
app.post("/api/money/connect/onboard", async (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  if (!stripeConfigured()) return stripeNotConfigured(res);
  try {
    let acctId = ctx.user.stripeAccountId || null;
    if (!acctId) {
      const acct = await stripeApi("POST", "/accounts", {
        type: "express",
        country: "US",
        email: ctx.user.email,
        business_type: "individual",
        capabilities: { transfers: { requested: true } },
      });
      acctId = acct.id;
      ctx.user.stripeAccountId = acctId;
      writeAccounts(ctx.db);
      console.log("[money] connect account created for", ctx.user.email);
    }
    const origin = siteOrigin(req);
    const link = await stripeApi("POST", "/account_links", {
      account: acctId,
      refresh_url: origin + "/?connect=refresh",
      return_url: origin + "/?connect=done",
      type: "account_onboarding",
    });
    res.json({ ok: true, url: link.url });
  } catch (e) {
    console.error("[money] connect onboard failed", e.message);
    res.status(502).json({ ok: false, error: "stripe-error" });
  }
});
app.get("/api/money/connect/status", async (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  if (!stripeConfigured()) return stripeNotConfigured(res);
  const info = await moneyConnectInfo(ctx.user);
  res.json({
    ok: true,
    connected: info.connected,
    payoutsEnabled: info.payoutsEnabled,
  });
});
app.post("/api/money/cashout", async (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  const db = readMoney();
  unlockMoneyHolds(db, ctx.user.id);
  const earn = moneyEarningsFor(db, ctx.user.id);
  if (moneyCashedOutToday(db, ctx.user.id)) {
    writeMoney(db);
    return res
      .status(400)
      .json({ ok: false, error: "already-cashed-out-today" });
  }
  if (earn.availableCents < MONEY_CASHOUT_MIN_CENTS) {
    writeMoney(db);
    return res.status(400).json({
      ok: false,
      error: "below-minimum",
      availableCents: earn.availableCents,
      minCents: MONEY_CASHOUT_MIN_CENTS,
    });
  }
  const firstEver = !db.cashouts.some((c) => c.acctId === ctx.user.id);
  const cents = earn.availableCents;
  // Reserve BEFORE anything else: the amount leaves "available" the
  // moment the cash-out exists, so it can never be double-spent.
  earn.availableCents = 0;
  const record = {
    id: crypto.randomBytes(8).toString("hex"),
    acctId: ctx.user.id,
    cents,
    feeCents: MONEY_CASHOUT_FEE_CENTS,
    status: "queued",
    at: new Date().toISOString(),
    unlockReviewAt: firstEver
      ? new Date(
          Date.now() + FIRST_PAYOUT_HOLD_DAYS * 24 * 3600 * 1000
        ).toISOString()
      : null,
  };
  db.cashouts.push(record);
  moneyTx(db, {
    type: "cashout", from: ctx.user.id, to: null, charms: 0,
    cents, cut: MONEY_CASHOUT_FEE_CENTS, ref: record.id,
  });
  // Try to move it immediately (first-payout holds and unconfigured /
  // unconnected states simply stay queued, honestly labelled — with no
  // Stripe keys at all the honest label is "queued-needs-connect"; the
  // first-payout review date rides along in unlockReviewAt either way).
  await moneyProcessCashouts(db, ctx.db);
  if (record.status === "queued" && !stripeConfigured())
    record.status = "queued-needs-connect";
  writeMoney(db);
  console.log(
    "[money] cashout", record.id, cents, "c by", ctx.user.name,
    "status", record.status, firstEver ? "(first payout, review hold)" : ""
  );
  res.json({
    ok: true,
    cashout: moneyPublicCashout(record),
    firstPayoutHold: firstEver,
    availableCents: earn.availableCents,
  });
});
app.get("/api/money/history", async (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  const db = readMoney();
  let changed = unlockMoneyHolds(db, ctx.user.id);
  if (await moneyProcessCashouts(db, ctx.db)) changed = true;
  if (changed) writeMoney(db);
  const mine = db.txlog
    .filter((t) => t.from === ctx.user.id || t.to === ctx.user.id)
    .slice(-50)
    .reverse();
  const cashouts = db.cashouts
    .filter((c) => c.acctId === ctx.user.id)
    .slice(-20)
    .reverse()
    .map(moneyPublicCashout);
  res.json({ ok: true, tx: mine, cashouts });
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
    // [RP-V7.24] A reconnecting client keeps its identity via a stable
    // per-device key: if an older socket still holds the same key, it
    // is a ghost (its connection died but the ping timeout hasn't
    // noticed) — evict it exactly as if it had disconnected, so the
    // same person is never counted / rendered twice.
    const devKey = String(data.key || "").toLowerCase().replace(/[^a-z0-9-]/g, "").slice(0, 40);
    if (devKey.length >= 8) {
      for (const [oldId, k] of [...clientKeys]) {
        if (k !== devKey || oldId === socket.id) continue;
        const old = players.get(oldId);
        if (old) {
          const oa = auctions.get(old.room);
          if (oa && oa.hostId === oldId) endAuction(old.room, true);
          io.to(old.room).emit("player-left", { id: oldId });
          players.delete(oldId);
        }
        chatTimes.delete(oldId);
        releaseFloorsHeldBy(oldId);
        for (const m of [...matches]) {
          if (m.split(":").includes(oldId)) matches.delete(m);
        }
        clientKeys.delete(oldId);
        const os = io.sockets.sockets.get(oldId);
        if (os) os.disconnect(true);
      }
      clientKeys.set(socket.id, devKey);
    }
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
    socket.emit("lives-update", livesPayloadFor(socket)); // [RP-V7.28] current live registry, so a fresh client sees ongoing lives immediately ([RP-V7.40] in the recipient's own order)
    socket.to(room).emit("player-joined", player); // tell the room
  });

  // [RP-V7.30] Account presence: a signed-in client announces which
  // account this socket belongs to so the DM routes know the person
  // is online (no offline alert needs queueing for them). The token
  // is verified against the same store as REST auth; a bad or missing
  // token simply never announces. Guests never send this.
  socket.on("acct-presence", (data = {}) => {
    const token = String(data.token || "");
    if (!token) return;
    const user = accountForToken(readAccounts(), {
      headers: { authorization: "Bearer " + token },
    });
    if (!user) return;
    if (socket.data.accountId && socket.data.accountId !== user.id)
      acctSocketRemove(socket.data.accountId, socket.id);
    socket.data.accountId = user.id;
    acctSocketAdd(user.id, socket.id);
    // [RP-V7.40] now that this socket's account is known, hand it the
    // lives list in its own For You order right away.
    try {
      socket.emit("lives-update", livesPayloadFor(socket));
    } catch (e) { /* the next broadcast will carry it */ }
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
    socket.emit("lives-update", livesPayloadFor(socket)); // [RP-V7.28] fresh snapshot on room change too ([RP-V7.40] personalized)
    // [RP-V7.28] a host who walks out of their own live room has ended the
    // live, even if their client never sent live-unregister
    const swKey = clientKeys.get(socket.id);
    if (swKey) {
      const reg = liveRegistry.get(swKey);
      if (reg && reg.room !== room) { liveRegistry.delete(swKey); broadcastLives(); potLiveEnded(swKey); } // [RP-V7.41] walking out ends the live — settle its pot
    }
    socket.to(room).emit("player-joined", p);
  });

  // [RP-V7.28] Live registry: hosts register on Go LIVE, heartbeat while
  // live, and unregister on end. The sender's device key + room come from
  // server-side socket state — the client only supplies title/topic.
  socket.on("live-register", (data = {}) => {
    const p = players.get(socket.id);
    const devKey = clientKeys.get(socket.id);
    if (!p || !devKey) return;
    const wantRoom = ("live-" + devKey).slice(0, 40);
    if (p.room !== wantRoom) return; // sanity: only from inside your own live room
    const now = Date.now();
    const prev = liveRegistry.get(devKey);
    liveRegistry.set(devKey, {
      key: devKey,
      room: p.room,
      name: p.name,
      title: String(data.title || "").replace(/[<>&"]/g, "").slice(0, 60),
      topic: String(data.topic || "").replace(/[<>&"]/g, "").slice(0, 24) || "Chatting",
      photo: p.photoUrl || null,
      startedAt: prev ? prev.startedAt : now,
      lastBeat: now,
    });
    broadcastLives();
  });

  socket.on("live-beat", (data = {}) => {
    const devKey = clientKeys.get(socket.id);
    if (!devKey) return;
    const p = players.get(socket.id);
    const e = liveRegistry.get(devKey);
    if (!e) {
      // [RP-V7.32] beat-heal: if a host's one live-register never landed
      // (missed emit, player record not ready, gate-deferred room switch),
      // their 20s beats still arrive — and a sender provably inside their
      // own live room is a host, so create the entry from the beat instead
      // of leaving the live invisible forever. Same sanity check and the
      // same title/topic sanitizing as live-register; nothing is weakened.
      if (!p) return;
      const wantRoom = ("live-" + devKey).slice(0, 40);
      if (p.room !== wantRoom) return; // sanity: only from inside your own live room
      const now = Date.now();
      liveRegistry.set(devKey, {
        key: devKey,
        room: p.room,
        name: p.name,
        title: String(data.title || "").replace(/[<>&"]/g, "").slice(0, 60),
        topic: String(data.topic || "").replace(/[<>&"]/g, "").slice(0, 24) || "Chatting",
        photo: p.photoUrl || null,
        startedAt: now,
        lastBeat: now,
      });
      broadcastLives();
      return;
    }
    e.lastBeat = Date.now();
    if (p) { e.name = p.name; if (p.photoUrl) e.photo = p.photoUrl; }
  });

  socket.on("live-unregister", () => {
    const devKey = clientKeys.get(socket.id);
    if (!devKey) return;
    if (liveRegistry.delete(devKey)) { broadcastLives(); potLiveEnded(devKey); } // [RP-V7.41] settle the pot of the ended live
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
    if (socket.data.accountId) acctSocketRemove(socket.data.accountId, socket.id); // [RP-V7.30]
    clientKeys.delete(socket.id); // [RP-V7.24]
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

// [RP-V7.37] Delete-profile finalization sweep: once on boot, then
// every 10 minutes (the login route also runs it lazily). Accounts
// past their 30-day deletionAt get the full hard cascade.
try {
  sweepPendingDeletions();
} catch (e) {}
const deletionSweepTimer = setInterval(() => {
  try {
    sweepPendingDeletions();
  } catch (e) {}
}, 10 * 60 * 1000);
if (deletionSweepTimer.unref) deletionSweepTimer.unref();

// [RP-V7.41] Plaza Pot orphan sweep: once on boot, then every 60s.
// Any open pot whose live is no longer in the registry is settled by
// the lifecycle rule (entries -> auto-draw, none -> seed refund), so a
// crashed or restarted server can never strand escrowed charms.
try {
  sweepOrphanPots();
} catch (e) {}
const potSweepTimer = setInterval(() => {
  try {
    sweepOrphanPots();
  } catch (e) {}
}, 60 * 1000);
if (potSweepTimer.unref) potSweepTimer.unref();

// [RP-V7.42] Daily Pot scheduler: once on boot, then every 60s —
// opens the America/New_York day at midnight and fires the 21:00 ET
// burst settlement (dpEnsureToday also settles on contact, so a state
// read right at 21:00 never lags; this timer is the guarantee for an
// idle server). All state persists in dailypot.json across restarts.
try {
  dailyPotTick();
} catch (e) {}
const dailyPotTimer = setInterval(() => {
  try {
    dailyPotTick();
  } catch (e) {}
}, 60 * 1000);
if (dailyPotTimer.unref) dailyPotTimer.unref();
