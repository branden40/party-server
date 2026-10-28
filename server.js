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

// [RP-V7.52] Store hardening (audit C5 + addendum, H11): the money,
// accounts, pots and dailypot stores NEVER boot empty over a corrupt
// file again. A read that cannot parse (or fails shape validation)
// restores the last-good .bak when one exists, quarantines the
// corrupt bytes to <file>.corrupt-<ts> for forensics, and logs
// loudly; every successful write refreshes .bak to the state just
// written, so .bak is always the last known-good state. A missing
// file is a fresh install — the fallback, silently.
function storeQuarantine(file) {
  try {
    if (fs.existsSync(file)) fs.renameSync(file, file + ".corrupt-" + Date.now());
  } catch (e) {}
}
function storeReadJson(file, validate, fallback, label) {
  if (!fs.existsSync(file)) return fallback;
  try {
    const d = JSON.parse(fs.readFileSync(file, "utf8"));
    if (validate(d)) return d;
    console.error("[store] " + label + ": unexpected shape in " + file + " — attempting .bak restore");
  } catch (e) {
    console.error("[store] " + label + ": cannot parse " + file + " (" + e.message + ") — attempting .bak restore");
  }
  try {
    const b = JSON.parse(fs.readFileSync(file + ".bak", "utf8"));
    if (validate(b)) {
      storeQuarantine(file);
      const tmp = file + ".tmp";
      fs.writeFileSync(tmp, JSON.stringify(b, null, 2));
      fs.renameSync(tmp, file);
      console.error("[store] " + label + ": restored last-good state from " + file + ".bak");
      return b;
    }
  } catch (e) {}
  storeQuarantine(file);
  console.error("[store] " + label + ": NO usable backup for " + file + " — starting from empty; corrupt bytes quarantined, nothing silently overwritten");
  return fallback;
}
function storeWriteJson(file, obj) {
  const tmp = file + ".tmp";
  fs.writeFileSync(tmp, JSON.stringify(obj, null, 2));
  fs.renameSync(tmp, file);
  try {
    fs.copyFileSync(file, file + ".bak");
  } catch (e) {}
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
  // [RP-V7.63] The readAccounts() that used to sit here was DEAD — the
  // host account id has come from the socket's token-verified binding
  // since V7.52 (audit C4) — yet it cost a full synchronous read+parse
  // of accounts.json on EVERY snapshot computation. Gone.
  const potsDb = readPots(); // [RP-V7.41] Plaza Pot state rides the snapshot
  return [...liveRegistry.values()].map((e) => {
    const sid = byKey.get(e.key) || null;
    // [RP-V7.52] Resolve the host's ACCOUNT id ONLY from the host
    // socket's token-verified acct-presence binding (audit C4). The
    // old unique-display-name fallback is gone: display names are
    // claimable by anyone, so an unverified socket could get its
    // live attributed to a victim's account. An unverified socket
    // is a guest host with NO account identity — null here.
    let hostAccountId = null;
    if (sid) {
      const hs = io.sockets.sockets.get(sid);
      if (hs && hs.data && hs.data.accountId) hostAccountId = hs.data.accountId;
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
      pot: potSnapshotFrom(potsDb, e.key, e.startedAt), // [RP-V7.41] null unless a pot is open/drawn here; [RP-V7.49] terminal pots from a previous live are scoped out
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
function fyRankLives(user, snap, pre) {
  const now = Date.now();
  const sig = (pre && pre.sig) || readReelSignals(); // [RP-V7.63] broadcast preloads shared stores (see broadcastLives)
  const urec = sig.users[user.id] || null;
  const aff = (urec && urec.authorAff) || {};
  const following = new Set(socialFollowingIds((pre && pre.social) || readSocial(), user.id));
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
function livesPayloadFor(socket, snap, pre) {
  // [RP-V7.63] snap/pre are optional preloads from broadcastLives: ONE
  // snapshot + ONE read of each shared store per broadcast, shared by
  // every recipient. Previously every socket in a broadcast paid for
  // its own full snapshot (a sync pots parse + an O(lives×players)
  // watcher count) AND its own accounts/signals/social re-reads — all
  // synchronous on the event loop, so a broadcast to S sockets did
  // S× the disk work and stalled every other request behind it.
  const shot = snap || livesSnapshot();
  const acctId = socket && socket.data && socket.data.accountId;
  if (!acctId) return { lives: potLiftOrder(shot) };
  const user = ((pre && pre.accounts) || readAccounts()).users.find((u) => u.id === acctId);
  if (!user || user.deletionAt) return { lives: potLiftOrder(shot) };
  return { lives: fyRankLives(user, shot, pre), ranked: true };
}
function broadcastLives() {
  // [RP-V7.40] personalized at emit time, per socket — no shared order.
  // [RP-V7.63] …but the snapshot + shared stores are computed ONCE here
  // and handed down (see livesPayloadFor): per-socket work is now just
  // the ranking sort. If a preload ever throws, snap/pre stay null and
  // each socket falls back to computing its own, exactly as before.
  let snap = null, pre = null;
  try {
    snap = livesSnapshot();
    pre = { accounts: readAccounts(), sig: readReelSignals(), social: readSocial() };
  } catch (e) { snap = null; pre = null; }
  for (const s of io.sockets.sockets.values()) {
    try {
      s.emit("lives-update", livesPayloadFor(s, snap, pre));
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
// [RP-V7.80] Full-scan F3: the server socket auction enforces the
// SAME tiered bid ladder as the shipping client (aucBidStep in
// index.html, RP-V6.15 — quoted there against a high bid in cents;
// the socket auction bids in whole dollars, so the steps mirror in
// dollars, thresholds identical):
//   high < $10 -> $1 · < $25 -> $2 · < $50 -> $4 · < $100 -> $5 ·
//   < $250 -> $10 · < $1000 -> $20 · >= $1000 -> $25
function auctionBidStepDollars(highDollars) {
  const d = Number(highDollars) || 0;
  if (d < 10) return 1;
  if (d < 25) return 2;
  if (d < 50) return 4;
  if (d < 100) return 5;
  if (d < 250) return 10;
  if (d < 1000) return 20;
  return 25;
}

// ---------------------------------------------------------------------------
// Voice (walkie-talkie) signaling + floor control.
// Channels: "room:<room>" for public voice rooms (Chaos Room),
// "dm:<idA>:<idB>" (ids sorted) for matched-player talk.
// Floor: one talker per channel at a time. Matches are session-scoped.
// ---------------------------------------------------------------------------
const voiceFloors = new Map(); // [RP-V7.48] channel -> floor-holder IDENTITY: "key:<deviceKey>" for keyed clients (stable across reconnects) or "sock:<socket.id>" as the keyless fallback
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
// [RP-V7.48] Floor-holder identity for a socket: its stable device key
// when it has one, else the socket id itself. Floors survive reconnects
// because the identity does — a same-device re-join TRANSFERS the floor
// instead of the old socket.id-keyed release killing the talk ~1s in.
function floorHolderId(socketId) {
  const k = clientKeys.get(socketId);
  return k && k.length >= 8 ? "key:" + k : "sock:" + socketId;
}
function floorHolderSocketId(hid) {
  if (!hid) return null;
  if (hid.startsWith("key:")) {
    const k = hid.slice(4);
    for (const [sid, ck] of clientKeys) if (ck === k) return sid;
    return null;
  }
  return hid.startsWith("sock:") ? hid.slice(5) : hid;
}
function releaseFloorsHeldBy(hid, fromSocketId) {
  // If another live socket still carries this identity (the same
  // device reconnected), the floor TRANSFERS — nothing is released
  // and no release is broadcast.
  if (hid && hid.startsWith("key:")) {
    const k = hid.slice(4);
    for (const ck of clientKeys.values()) if (ck === k) return;
  }
  for (const [ch, holder] of voiceFloors) {
    if (holder !== hid) continue;
    voiceFloors.delete(ch);
    const members = channelMembers(ch).filter((id) => id !== fromSocketId);
    if (members.length)
      io.to(members).emit("voice-floor-released", { channel: ch, by: fromSocketId });
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
  // [RP-V7.52] hardened read (audit C5 addendum): a corrupt
  // accounts.json restores from accounts.json.bak instead of
  // booting empty and letting the next write destroy the original.
  return storeReadJson(
    ACCOUNTS_FILE,
    (d) => !!(d && Array.isArray(d.users) && d.tokens && typeof d.tokens === "object"),
    emptyAccounts(),
    "accounts"
  );
}
function writeAccounts(db) {
  storeWriteJson(ACCOUNTS_FILE, db);
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
// [RP-V7.94] Extended profile fields — the account owns them (brain
// rule): gender, ageRange, lookingFor, relStatus, vibe. Only known
// values ever read back; anything else reads as null (unset). An
// unset gender is null — the server never invents one.
const EXT_GENDERS = ["male", "female"];
const EXT_AGE_RANGES = ["18-24", "25-34", "35-44", "45-54", "55+", "under18"];
const EXT_REL_STATUSES = ["single", "married", "divorced", "widowed"];
const EXT_VIBES = ["Charming", "Funny", "Sweet", "Bold", "Chill", "Romantic"];
function extProfileOf(u) {
  const e = (u && u.extProfile && typeof u.extProfile === "object" && !Array.isArray(u.extProfile)) ? u.extProfile : {};
  return {
    gender: EXT_GENDERS.indexOf(e.gender) >= 0 ? e.gender : null,
    ageRange: EXT_AGE_RANGES.indexOf(e.ageRange) >= 0 ? e.ageRange : null,
    lookingFor: EXT_AGE_RANGES.indexOf(e.lookingFor) >= 0 ? e.lookingFor : null,
    relStatus: EXT_REL_STATUSES.indexOf(e.relStatus) >= 0 ? e.relStatus : null,
    vibe: EXT_VIBES.indexOf(e.vibe) >= 0 ? e.vibe : null,
  };
}
function publicAccount(u) {
  // [RP-V7.50] photo: the account record is the source of truth for the
  // profile photo — login / signup / /me all carry it back.
  // [RP-V7.61] bio rides along too: the account record owns the whole
  // profile (name, username, bio, profileType, photo), so any login on
  // any device returns everything the client needs to restore it.
  // [RP-V7.62] photos rides along too: the whole photo gallery (ordered
  // URLs, first = main) lives on the account record, so login / signup
  // / /me return it and any device restores the same gallery.
  // [RP-V7.64] photoViews rides along too: the server-owned "👁 n"
  // count for each gallery photo, keyed by URL (parallel to photos).
  // [RP-V7.88] face rides along too: photo stays the EFFECTIVE face
  // (every surface already reads it); facePhoto is the member's own
  // uploaded photo, kept apart so switching back never loses it.
  return { id: u.id, name: u.name, username: u.username || "", email: u.email, phone: u.phone, profileType: profileTypeOf(u), photo: u.photo || null, bio: typeof u.bio === "string" ? u.bio : "", photos: accountPhotos(u), photoViews: photoViewsFor(u), link: typeof u.link === "string" ? u.link : "", likedPrivate: !!u.likedPrivate, faceMode: faceModeOf(u), faceRack: typeof u.faceRack === "string" ? u.faceRack : "", faceBuild: (u.faceBuild && typeof u.faceBuild === "object" && !Array.isArray(u.faceBuild)) ? u.faceBuild : null, facePhoto: facePhotoOrig(u), extProfile: extProfileOf(u) };
}
// [RP-V7.62] The gallery as the rest of the app sees it: the stored
// array when the record has one. A legacy account that only ever set
// a profile photo has no array — its photo IS the gallery (seed on
// read). The stored record is only rewritten on a real gallery write
// (upload / set), never on a read, so reads stay side-effect free.
const ACCOUNT_PHOTOS_MAX = 12;
function accountPhotos(u) {
  if (Array.isArray(u.photos))
    return u.photos.filter((x) => typeof x === "string" && x).slice(0, ACCOUNT_PHOTOS_MAX);
  return u.photo ? [u.photo] : [];
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
// ---------------------------------------------------------------------------
// [RP-V7.55] NOTIFICATION TRANSPORT — the real sender (Branden's pick,
// Oct 25: members hear from the Plaza by email AND phone). Providers
// are env-configured; with no keys set, every send is a safe no-op
// and alerts simply stay queued, exactly as before. Contact details
// are read from the account record server-side ONLY — they never
// leave through an API.
//   Email (Resend): RESEND_API_KEY + ALERT_FROM_EMAIL
//     (RESEND_API_BASE overrides the API root — used by tests)
//   SMS (Twilio):   TWILIO_ACCOUNT_SID + TWILIO_AUTH_TOKEN +
//                   TWILIO_FROM_NUMBER (TWILIO_API_BASE likewise)
// ---------------------------------------------------------------------------
function notifyEmailReady() {
  return !!(process.env.RESEND_API_KEY && process.env.ALERT_FROM_EMAIL);
}
function notifySmsReady() {
  return !!(
    process.env.TWILIO_ACCOUNT_SID &&
    process.env.TWILIO_AUTH_TOKEN &&
    process.env.TWILIO_FROM_NUMBER
  );
}
function notifyPhoneE164(phone) {
  const raw = String(phone || "").trim();
  const d = raw.replace(/\D/g, "");
  if (d.length === 10) return "+1" + d;
  if (d.length === 11 && d[0] === "1") return "+" + d;
  if (raw.startsWith("+") && d.length >= 10) return "+" + d;
  return null;
}
async function notifySendEmail(to, subject, text) {
  if (!notifyEmailReady() || !to) return false;
  try {
    const base = process.env.RESEND_API_BASE || "https://api.resend.com";
    const r = await fetch(base + "/emails", {
      method: "POST",
      headers: {
        Authorization: "Bearer " + process.env.RESEND_API_KEY,
        "Content-Type": "application/json",
      },
      body: JSON.stringify({ from: process.env.ALERT_FROM_EMAIL, to, subject, text }),
    });
    return r.ok;
  } catch (e) {
    return false;
  }
}
async function notifySendSms(toPhone, body) {
  if (!notifySmsReady()) return false;
  const to = notifyPhoneE164(toPhone);
  if (!to) return false;
  try {
    const sid = process.env.TWILIO_ACCOUNT_SID;
    const base = process.env.TWILIO_API_BASE || "https://api.twilio.com";
    const form = new URLSearchParams({
      From: process.env.TWILIO_FROM_NUMBER,
      To: to,
      Body: body,
    });
    const r = await fetch(base + "/2010-04-01/Accounts/" + sid + "/Messages.json", {
      method: "POST",
      headers: {
        Authorization:
          "Basic " + Buffer.from(sid + ":" + process.env.TWILIO_AUTH_TOKEN).toString("base64"),
        "Content-Type": "application/x-www-form-urlencoded",
      },
      body: form.toString(),
    });
    return r.ok;
  } catch (e) {
    return false;
  }
}
// Account email (welcome today): really sends when Resend is
// configured; otherwise the message lives in-app only, as before.
// Fire-and-forget — a mail failure must never break sign-up.
function sendAccountEmail(user, kind) {
  if (!user || !user.email) return;
  if (!notifyEmailReady()) {
    console.log(
      "[accounts] " + kind + " email queued (no email provider configured) for " + user.email
    );
    return;
  }
  const subjects = { welcome: "Welcome to Rizz Plaza 🎉" };
  const bodies = {
    welcome:
      "Hi " + (user.name || "there") + " — welcome to Rizz Plaza!\n\n" +
      "Your account is ready. Jump in: go live, meet people in the rooms, enter the Daily Pot (it bursts at a secret moment between 7 and 9 PM ET — be there!), and catch the holiday events all year.\n\n" +
      "Open the Plaza: https://rizzplaza.com\n\n— The Rizz Plaza team",
  };
  notifySendEmail(
    user.email,
    subjects[kind] || "Rizz Plaza",
    bodies[kind] || "Welcome to Rizz Plaza — open https://rizzplaza.com to get started."
  )
    .then((ok) =>
      console.log("[accounts] " + kind + " email " + (ok ? "sent" : "FAILED") + " to " + user.email)
    )
    .catch(() => {});
}
// [RP-V7.55] The welcome text — after sign-up, members hear from the
// Plaza by phone too (same rule as the email above).
function sendAccountSms(user, kind) {
  if (!user || !user.phone || !notifySmsReady()) return;
  if (kind !== "welcome") return;
  notifySendSms(
    user.phone,
    "Welcome to Rizz Plaza 🎉 Your account is ready — go live, meet people, and enter the Daily Pot (bursts at a secret moment between 7 and 9 PM ET — be there!): https://rizzplaza.com"
  )
    .then((ok) => console.log("[accounts] welcome sms " + (ok ? "sent" : "FAILED")))
    .catch(() => {});
}
// [RP-V7.52] In-flight sign-up identifier reservations (audit H2):
// normalized username/email/phone keys held from the uniqueness
// check until the insert lands, so the one-account-per-identifier
// rule is structural, not timing-dependent.
const signupReservations = new Set();
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
  // [RP-V7.48] Phone is REQUIRED at sign-up (the startup wall build
  // retired guest browsing): a missing/empty number is a 400, exactly
  // like a bad email. The V7.35 normalization + one-phone-per-account
  // uniqueness check below is untouched.
  if (!phone || !normPhoneKey(phone))
    return res
      .status(400)
      .json({ ok: false, error: "A mobile phone number is required" });
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
  // [RP-V7.80] TEEN SIGNUP IS OPEN (full-scan F1; Branden's decision,
  // Oct 26, 2026: "Open teen signup — the full teen model goes
  // live"). The floor is 13: an under-13 DOB is refused outright. A
  // 13–17 sign-up creates a normal account through this same
  // machinery — the stored DOB is what every existing gate reads
  // (ageFromDob < 18 → teen class: charms-only economy, money doors
  // server-locked, room/pot classes), so no downstream rule changes.
  if (age < 13)
    return res.status(403).json({
      ok: false,
      error: "You must be 13 or older to join Rizz Plaza",
    });
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
  // [RP-V7.52] Reserve all three identifiers synchronously BEFORE
  // the insert work, and re-check against a fresh read at insert
  // (audit H2): two sign-ups racing the same normalized email,
  // phone or username can no longer both pass — the second sees
  // either the reservation or the inserted record and gets the
  // same 409s as a sequential duplicate. Sequential behavior and
  // every message above are unchanged.
  const resKeys = [
    "u:" + usernameKey(username),
    "e:" + normEmailKey(email),
    "p:" + normPhoneKey(phone),
  ];
  if (signupReservations.has(resKeys[0]))
    return res.status(409).json({
      ok: false,
      error: "That username is taken — try another",
    });
  if (signupReservations.has(resKeys[1]))
    return res.status(409).json({
      ok: false,
      error: "That email is already registered",
    });
  if (signupReservations.has(resKeys[2]))
    return res.status(409).json({
      ok: false,
      error: "That phone number is already registered",
    });
  for (const k of resKeys) signupReservations.add(k);
  try {
    const fresh = readAccounts();
    if (usernameTaken(fresh, username))
      return res.status(409).json({
        ok: false,
        error: "That username is taken — try another",
      });
    if (emailTaken(fresh, email, null))
      return res.status(409).json({
        ok: false,
        error: "That email is already registered",
      });
    if (phoneTaken(fresh, phone, null))
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
    fresh.users.push(user);
    const token = newAccountToken(fresh, user.id);
    writeAccounts(fresh);
    sendAccountEmail(user, "welcome");
    sendAccountSms(user, "welcome"); // [RP-V7.55] email AND phone, per Branden's rule
    console.log("[accounts] signup", user.email);
    res.status(201).json({ ok: true, token, user: publicAccount(user) });
  } finally {
    for (const k of resKeys) signupReservations.delete(k);
  }
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
function accountMeHandler(req, res) {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  const unread = ctx.user.reminders.filter((r) => !r.read).length;
  res.json({ ok: true, user: publicAccount(ctx.user), unread });
}
app.get("/api/account/me", accountMeHandler);
// [RP-V7.52] Short alias (audit H5): the canonical account payload
// (publicAccount — id, name, username, email, phone, profileType,
// photo) at the path API callers reach for first.
app.get("/api/me", accountMeHandler);
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

// [RP-V7.61] Save my profile fields (display name + bio) on the ACCOUNT
// record. Session auth only (requireAccount) — no room join, no player
// record, no socket. This is the server half of "profile saved strong":
// Profile setup used to write name/bio only into this device's
// localStorage (datingGameProfile.v1), so a logout / fresh device lost
// them even though the member had an account. Sanitization matches the
// sign-up name rule (markup characters stripped); lengths are capped
// (name 40, bio 160). An empty/absent name is ignored (a save can never
// blank a member's name); a present bio string is saved as-is, so an
// emptied bio clears deliberately.
// [RP-V7.86] The profile LINK: one URL, set in Profile setup, shown
// tappable under the bio. Accepts a bare domain (gets https://) or a
// full http(s) URL; anything else (other schemes, spaces, junk) is
// rejected with null so the endpoint can 400 it. Empty string clears.
function normProfileLink(v) {
  let s = String(v == null ? "" : v).trim().slice(0, 300);
  if (!s) return "";
  if (!/^[a-z][a-z0-9+.-]*:/i.test(s)) s = "https://" + s;
  let u;
  try { u = new URL(s); } catch (e) { return null; }
  if (u.protocol !== "http:" && u.protocol !== "https:") return null;
  if (!u.hostname || u.hostname.indexOf(".") < 0) return null;
  return u.toString();
}

app.post("/api/account/profile", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  const b = req.body || {};
  let changed = false;
  if (typeof b.name === "string") {
    const name = b.name.replace(/[<>&"']/g, "").trim().slice(0, 40);
    if (name && name !== ctx.user.name) {
      ctx.user.name = name;
      changed = true;
    }
  }
  if (typeof b.bio === "string") {
    const bio = b.bio
      .replace(/[\u0000-\u0008\u000B\u000C\u000E-\u001F\u007F]/g, "")
      .trim()
      .slice(0, 160);
    if (bio !== (ctx.user.bio || "")) {
      ctx.user.bio = bio;
      changed = true;
    }
  }
  // [RP-V7.86] The one tappable link under the bio.
  if (typeof b.link === "string") {
    const link = normProfileLink(b.link);
    if (link === null)
      return res.status(400).json({ ok: false, error: "That link doesn't look right — use a full web address like yoursite.com" });
    if (link !== (ctx.user.link || "")) { ctx.user.link = link; changed = true; }
  }
  // [RP-V7.94] Extended profile fields ride this same save: only
  // known values are stored, null clears, an absent ext object
  // changes nothing, and no value is ever invented server-side.
  if (b.ext && typeof b.ext === "object" && !Array.isArray(b.ext)) {
    const cur94 = extProfileOf(ctx.user);
    const nx94 = { gender: cur94.gender, ageRange: cur94.ageRange, lookingFor: cur94.lookingFor, relStatus: cur94.relStatus, vibe: cur94.vibe };
    let extBad94 = false;
    const extSet94 = (key, allowed) => {
      if (!(key in b.ext)) return;
      if (b.ext[key] === null) nx94[key] = null;
      else if (allowed.indexOf(b.ext[key]) >= 0) nx94[key] = b.ext[key];
      else extBad94 = true;
    };
    extSet94("gender", EXT_GENDERS);
    extSet94("ageRange", EXT_AGE_RANGES);
    extSet94("lookingFor", EXT_AGE_RANGES);
    extSet94("relStatus", EXT_REL_STATUSES);
    extSet94("vibe", EXT_VIBES);
    if (extBad94)
      return res.status(400).json({ ok: false, error: "That profile value isn't one of the Plaza's choices" });
    if (JSON.stringify(nx94) !== JSON.stringify(cur94)) { ctx.user.extProfile = nx94; changed = true; }
  }
  // [RP-V7.86] Liked-tab privacy: private = only the owner sees it.
  if (typeof b.likedPrivate === "boolean" && b.likedPrivate !== !!ctx.user.likedPrivate) {
    ctx.user.likedPrivate = b.likedPrivate; changed = true;
  }
  if (changed) writeAccounts(ctx.db);
  res.json({ ok: true, user: publicAccount(ctx.user) });
});

/* ---------- [RP-V7.86] PROFILE PINS + COLLECTIONS ----------
   Pins: up to 3 of a member's OWN posts (reels / photo posts), stored
   on the account record (u.pins = [{kind, id}]) — pins ride the
   account, not the device. Collections (the @sswurve "playlists" row,
   in our own code): named groups of the member's own posts, stored in
   a small account-keyed store beside the other JSON stores. Only the
   owner can pin / collect; reads ride the public profile payload. */
const PROFILE_COLLECTIONS_FILE = process.env.PROFILE_COLLECTIONS_FILE || path.join(path.dirname(PHOTO_DIR), "profile-collections.json");
function readProfileCollections() {
  return storeReadJson(PROFILE_COLLECTIONS_FILE, (d) => !!(d && d.byUser && typeof d.byUser === "object" && !Array.isArray(d.byUser)), { byUser: {} }, "profile-collections");
}
function writeProfileCollections(db) { storeWriteJson(PROFILE_COLLECTIONS_FILE, db); }
function profileOwnsPost(db, user, kind, id) {
  if (kind === "reel") {
    const r = listReels().find((x) => x && x.id === id);
    if (!r) return false;
    return reelAuthorKeyFor(db, r) === user.id;
  }
  if (kind === "photopost") {
    const post = readPhotoPosts().posts.find((x) => x && x.id === id);
    return !!(post && post.owner === user.id);
  }
  return false;
}
function profileSanitizeItems(db, user, raw, cap) {
  const out = []; const seen = new Set();
  for (const it of Array.isArray(raw) ? raw : []) {
    if (!it || typeof it !== "object") continue;
    const kind = it.kind === "reel" || it.kind === "photopost" ? it.kind : null;
    const id = typeof it.id === "string" ? it.id.slice(0, 80) : "";
    if (!kind || !id) continue;
    const k = kind + ":" + id;
    if (seen.has(k)) continue;
    if (!profileOwnsPost(db, user, kind, id)) continue;
    seen.add(k); out.push({ kind, id });
    if (out.length >= cap) break;
  }
  return out;
}
app.post("/api/account/pins", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  const items = profileSanitizeItems(ctx.db, ctx.user, (req.body || {}).items, 3);
  ctx.user.pins = items;
  writeAccounts(ctx.db);
  res.json({ ok: true, pins: items });
});
app.post("/api/account/collections", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  const b = req.body || {};
  const name = String(b.name || "").trim().slice(0, 40);
  if (!name) return res.status(400).json({ ok: false, error: "Give the collection a name." });
  const db = readProfileCollections();
  const mine = Array.isArray(db.byUser[ctx.user.id]) ? db.byUser[ctx.user.id] : [];
  if (mine.length >= 20) return res.status(400).json({ ok: false, error: "That's the collection limit for now." });
  const coll = { id: crypto.randomBytes(8).toString("hex"), name, items: profileSanitizeItems(ctx.db, ctx.user, b.items, 60), createdAt: Date.now() };
  mine.push(coll);
  db.byUser[ctx.user.id] = mine;
  writeProfileCollections(db);
  res.json({ ok: true, collection: { id: coll.id, name: coll.name, count: coll.items.length } });
});
app.post("/api/account/collections/update", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  const b = req.body || {};
  const db = readProfileCollections();
  const mine = Array.isArray(db.byUser[ctx.user.id]) ? db.byUser[ctx.user.id] : [];
  const coll = mine.find((c) => c && c.id === b.id);
  if (!coll) return res.status(404).json({ ok: false, error: "Collection not found." });
  if (typeof b.name === "string" && b.name.trim()) coll.name = b.name.trim().slice(0, 40);
  if (Array.isArray(b.items)) coll.items = profileSanitizeItems(ctx.db, ctx.user, b.items, 60);
  writeProfileCollections(db);
  res.json({ ok: true, collection: { id: coll.id, name: coll.name, count: coll.items.length } });
});
app.post("/api/account/collections/delete", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  const b = req.body || {};
  const db = readProfileCollections();
  const mine = Array.isArray(db.byUser[ctx.user.id]) ? db.byUser[ctx.user.id] : [];
  db.byUser[ctx.user.id] = mine.filter((c) => !(c && c.id === b.id));
  writeProfileCollections(db);
  res.json({ ok: true });
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

// [RP-V7.89] FAIL-2 (V7.88 full scan): routes that ran the shared
// photo upload as bare middleware (`upload.single("photo")`) let a
// wrong-type or oversize file fall through to Express's default
// error page (HTTP 500 HTML). photoUpload runs the same upload
// through the error-callback discipline the wrapped routes
// (/api/reel, stories, feed, DMs) already use: the multer error is
// answered in place with clean JSON — 413 for LIMIT_FILE_SIZE, 400
// otherwise — and nothing is stored. A clean upload runs the
// route's original handler untouched.
function photoUpload(handler) {
  return (req, res) => {
    upload.single("photo")(req, res, (err) => {
      if (err) {
        const tooBig = err.code === "LIMIT_FILE_SIZE";
        return res.status(tooBig ? 413 : 400).json({
          ok: false,
          error: tooBig ? "That photo is over the 5 MB limit" : err.message,
        });
      }
      return handler(req, res);
    });
  };
}

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

// [RP-V7.62] Best-effort: if this account is live in a room right now,
// refresh its player record + room broadcast with a new main photo —
// the same extra /api/account/photo performs inline. Used by the
// gallery routes below, where the main photo can change too.
function refreshPlayerPhoto(userId, publicUrl) {
  try {
    const sids = acctSockets.get(userId);
    if (sids) {
      for (const sid of sids) {
        const p = players.get(sid);
        if (p) {
          p.photoUrl = publicUrl;
          io.to(p.room).emit("player-photo", { id: p.id, photoUrl: publicUrl });
        }
      }
    }
  } catch (e) { /* the account save already succeeded */ }
}

// [RP-V7.61] Upload a profile photo straight onto the ACCOUNT record.
// Session auth ONLY (requireAccount / Bearer token) — no joined player,
// no room, no socket required. This is the route Profile setup uses:
// before V7.61 the only upload path was the legacy /api/profile-photo
// below, which 400s ("Join the party before uploading a photo") unless
// the uploader already holds a live player record — so a member doing
// Profile setup from Home could end up with a photo that lived only in
// device-local state, and logout wiped it (Branden, Oct 25). Same
// multer storage, same 5 MB / image-only limits, same moderateImage
// flow as the legacy route. The photo is saved on the account record
// (user.photo) and returned in the account payload, so it restores on
// any login on any device. If the member happens to be in a room, their
// player record is updated + broadcast as a best-effort extra.
app.post("/api/account/photo", photoUpload(async (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) {
    if (req.file) fs.unlink(req.file.path, () => {});
    return;
  }
  try {
    if (!req.file) {
      return res.status(400).json({ ok: false, error: "No image file received." });
    }
    // Railway always serves public domains over HTTPS.
    const publicUrl = `https://${req.get("host")}/photos/${req.file.filename}`;
    const mod = await moderateImage(publicUrl);
    if (!mod.ok) {
      fs.unlink(req.file.path, () => {});
      console.log("ACCOUNT PHOTO REJECTED:", ctx.user.id, mod.reason);
      return res.status(422).json({
        ok: false,
        error: "That photo didn't pass our safety check. Please try a different one.",
      });
    }
    if (mod.unreviewed) {
      console.log("ACCOUNT PHOTO UNREVIEWED (no HIVE_API_KEY):", ctx.user.id, publicUrl);
    }
    ctx.user.photo = publicUrl;
    // [RP-V7.88] A fresh main photo is also the face record: it becomes
    // the stored original (photoOrig) and the photo route wins, so
    // switching face modes later can always bring THIS photo back.
    ctx.user.photoOrig = publicUrl;
    ctx.user.faceMode = "photo";
    // [RP-V7.62] Keep the gallery invariant: the profile photo IS the
    // first gallery photo. A fresh main photo moves to the front of
    // the stored gallery (seeding it for legacy accounts), so the
    // payload's photo and photos[0] can never disagree.
    const gal62 = accountPhotos(ctx.user).filter((x) => x !== publicUrl);
    gal62.unshift(publicUrl);
    ctx.user.photos = gal62.slice(0, ACCOUNT_PHOTOS_MAX);
    writeAccounts(ctx.db);
    // Best-effort: if this account is live in a room right now, refresh
    // its player record + room broadcast exactly like the legacy route.
    try {
      const sids = acctSockets.get(ctx.user.id);
      if (sids) {
        for (const sid of sids) {
          const p = players.get(sid);
          if (p) {
            p.photoUrl = publicUrl;
            io.to(p.room).emit("player-photo", { id: p.id, photoUrl: publicUrl });
          }
        }
      }
    } catch (e) { /* the account save already succeeded */ }
    return res.json({ ok: true, photoUrl: publicUrl, user: publicAccount(ctx.user) });
  } catch (e) {
    console.log("ACCOUNT UPLOAD ERROR:", e.message);
    return res.status(500).json({ ok: false, error: "Upload failed. Please try again." });
  }
}));

// [RP-V7.62] Upload ONE photo into the account gallery. Session auth
// ONLY (requireAccount) — no joined player, no room, no socket, same
// as /api/account/photo. Same multer storage, 5 MB / image-only limits
// and moderateImage flow. The URL is appended to the stored gallery
// (user.photos, max ACCOUNT_PHOTOS_MAX); a legacy account with only a
// profile photo seeds its gallery from that photo on this first
// gallery write (see accountPhotos). At the cap the upload is refused
// with a clear 400 BEFORE moderation runs, and the temp file is
// removed. user.photo re-syncs to photos[0] (appends can only change
// it when the gallery was empty).
app.post("/api/account/photos", photoUpload(async (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) {
    if (req.file) fs.unlink(req.file.path, () => {});
    return;
  }
  try {
    if (!req.file) {
      return res.status(400).json({ ok: false, error: "No image file received." });
    }
    const list = accountPhotos(ctx.user);
    if (list.length >= ACCOUNT_PHOTOS_MAX) {
      fs.unlink(req.file.path, () => {});
      return res.status(400).json({
        ok: false,
        error: "That's the full set — 12 photos max. Remove one to add another.",
      });
    }
    const publicUrl = `https://${req.get("host")}/photos/${req.file.filename}`;
    const mod = await moderateImage(publicUrl);
    if (!mod.ok) {
      fs.unlink(req.file.path, () => {});
      console.log("ACCOUNT GALLERY REJECTED:", ctx.user.id, mod.reason);
      return res.status(422).json({
        ok: false,
        error: "That photo didn't pass our safety check. Please try a different one.",
      });
    }
    if (mod.unreviewed) {
      console.log("ACCOUNT GALLERY UNREVIEWED (no HIVE_API_KEY):", ctx.user.id, publicUrl);
    }
    list.push(publicUrl);
    ctx.user.photos = list;
    // [RP-V7.88] The gallery main tracks into photoOrig (the member's
    // own photo); the EFFECTIVE face only follows the gallery while
    // the member is on the photo route — an avatar face is never
    // clobbered by adding a gallery photo.
    ctx.user.photoOrig = list[0];
    if (faceModeOf(ctx.user) === "photo") {
      ctx.user.photo = list[0];
    }
    writeAccounts(ctx.db);
    // The main photo only changed if the gallery was empty.
    if (list.length === 1 && faceModeOf(ctx.user) === "photo") refreshPlayerPhoto(ctx.user.id, publicUrl);
    return res.json({ ok: true, photoUrl: publicUrl, photos: list, user: publicAccount(ctx.user) });
  } catch (e) {
    console.log("ACCOUNT GALLERY UPLOAD ERROR:", e.message);
    return res.status(500).json({ ok: false, error: "Upload failed. Please try again." });
  }
}));

// [RP-V7.62] Replace the gallery wholesale — remove + reorder in ONE
// atomic write. Session auth ONLY. The body carries the FULL ordered
// list the member wants ({ photos: [url, ...] }); every entry must be
// a photo already in their stored gallery (the seeded view for legacy
// accounts), so nothing can be smuggled in; duplicates collapse and
// the result can never exceed the cap. user.photo re-syncs to the
// first entry, or null when the gallery is emptied. Removed photos'
// files stay on disk (same as every photo replacement in this app —
// only the gallery list changes).
app.post("/api/account/photos/set", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  const b = req.body || {};
  if (!Array.isArray(b.photos)) {
    return res.status(400).json({ ok: false, error: "Send the full ordered photo list." });
  }
  const owned = accountPhotos(ctx.user);
  const seen = new Set();
  const list = [];
  for (const raw of b.photos) {
    const url = typeof raw === "string" ? raw : "";
    if (!url || seen.has(url)) continue;
    if (!owned.includes(url)) {
      return res.status(400).json({
        ok: false,
        error: "That list includes a photo that isn't in your gallery.",
      });
    }
    seen.add(url);
    list.push(url);
  }
  if (list.length > ACCOUNT_PHOTOS_MAX) {
    return res.status(400).json({ ok: false, error: "That's the full set — 12 photos max." });
  }
  const galleryMain = list.length ? list[0] : null;
  // [RP-V7.88] Same split as the gallery upload: the stored original
  // follows the gallery order, the effective face follows only on the
  // photo route.
  const mainChanged = faceModeOf(ctx.user) === "photo" && galleryMain !== (ctx.user.photo || null);
  ctx.user.photos = list;
  ctx.user.photoOrig = galleryMain;
  if (faceModeOf(ctx.user) === "photo") {
    ctx.user.photo = galleryMain;
  }
  writeAccounts(ctx.db);
  if (mainChanged && ctx.user.photo) refreshPlayerPhoto(ctx.user.id, ctx.user.photo);
  return res.json({ ok: true, photos: list, user: publicAccount(ctx.user) });
});

/* ---------- [RP-V7.88] FACE CHOICE — photo OR avatar, all three routes ----------
   The member's face is chosen in Profile setup, FOUR ways: their real
   PHOTO (the original path), a ready-made Plaza AVATAR from the rack,
   a BUILD-YOUR-OWN avatar (original layered builder — the spec is
   stored, the render is a PNG through the photo pipeline), or an AI
   AVATAR FROM THEIR PHOTO (v1: on-device stylized renditions of the
   member's own photo; a generative provider plugs into the same
   face/upload route later). The brain rule holds: the choice lives on
   the ACCOUNT (u.faceMode / u.faceRack / u.faceBuild / u.faceImg).
   Whichever route wins, the produced image lands in u.photo — the one
   field every surface already reads (profile page, profile card,
   directory, live seats + host bar, comments, story tray) — so no
   surface needed rewiring. u.photoOrig keeps the member's uploaded
   photo apart from the effective face: switching back to Photo
   restores it exactly; nothing is ever destroyed by switching. */
const FACE_MODES = ["photo", "rack", "build", "ai"];
// [RP-V7.89] The rack grew 12 → 100 faces (Branden, Oct 27, 2026:
// "Can it be 100 faces") — ids run avatar-01 … avatar-100; the art
// for 13–100 ships as file drops beside the original twelve.
const FACE_RACK_IDS = [];
for (let _fr = 1; _fr <= 100; _fr++)
  FACE_RACK_IDS.push("avatar-" + (_fr < 10 ? "0" + _fr : String(_fr)));
function faceRackUrl(id) { return "/img/avatars/" + id + ".webp"; }
function faceModeOf(u) {
  const m = String((u && u.faceMode) || "photo").trim().toLowerCase();
  return FACE_MODES.indexOf(m) >= 0 ? m : "photo";
}
function facePhotoOrig(u) {
  if (!u) return null;
  if (typeof u.photoOrig === "string" && u.photoOrig) return u.photoOrig;
  const gal = accountPhotos(u);
  if (gal.length) return gal[0];
  return typeof u.photo === "string" && u.photo ? u.photo : null;
}
const FACE_BUILD_HAIRS = ["fade", "waves", "braids", "bun", "curly", "long", "buzz", "bob"];
const FACE_BUILD_EXPRS = ["smile", "bigsmile", "calm", "wink"];
const FACE_BUILD_ACCS = ["none", "glasses", "shades", "cap", "hoops", "star"];
function faceHex(v) {
  const t = String(v || "").trim().toLowerCase();
  return /^#[0-9a-f]{6}$/.test(t) ? t : null;
}
function normFaceBuild(v) {
  if (!v || typeof v !== "object" || Array.isArray(v)) return null;
  const skin = faceHex(v.skin), hairColor = faceHex(v.hairColor),
    top = faceHex(v.top), bg = faceHex(v.bg);
  const hair = FACE_BUILD_HAIRS.indexOf(String(v.hair || "")) >= 0 ? String(v.hair) : null;
  const expr = FACE_BUILD_EXPRS.indexOf(String(v.expr || "")) >= 0 ? String(v.expr) : null;
  const acc = FACE_BUILD_ACCS.indexOf(String(v.acc || "")) >= 0 ? String(v.acc) : null;
  if (!skin || !hairColor || !top || !bg || !hair || !expr || !acc) return null;
  return { skin, hair, hairColor, expr, top, acc, bg };
}

// Switch the face route. Photo + rack are pure account writes; build /
// ai restore the face image that route last produced (face/upload made
// it) — asking for one that was never made is a clear 400, not a
// silent blank face.
app.post("/api/account/face", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  const b = req.body || {};
  const mode = String(b.mode || "").trim().toLowerCase();
  if (FACE_MODES.indexOf(mode) < 0)
    return res.status(400).json({ ok: false, error: "Pick how your face shows: photo, avatar rack, build your own, or AI from your photo." });
  const u = ctx.user;
  if (mode === "photo") {
    const orig = facePhotoOrig(u);
    u.faceMode = "photo";
    // faceImg / faceImgMode are NOT touched here: they keep pointing
    // at the last avatar the member produced, so switching back to
    // that route restores it exactly.
    if (orig) u.photo = orig;
  } else if (mode === "rack") {
    const rack = String(b.rack || "").trim();
    if (FACE_RACK_IDS.indexOf(rack) < 0)
      return res.status(400).json({ ok: false, error: "Pick one of the Plaza avatars from the rack." });
    u.faceMode = "rack";
    u.faceRack = rack;
    u.faceImg = faceRackUrl(rack);
    u.photo = u.faceImg;
  } else {
    if (u.faceImgMode !== mode || !u.faceImg)
      return res.status(400).json({ ok: false, error: mode === "build" ? "Build your avatar first — then it is yours to switch back to anytime." : "Make your AI avatar from your photo first — then it is yours to switch back to anytime." });
    u.faceMode = mode;
    u.photo = u.faceImg;
  }
  writeAccounts(ctx.db);
  if (u.photo) refreshPlayerPhoto(u.id, u.photo);
  return res.json({ ok: true, user: publicAccount(u) });
});

// A produced face image arrives: the builder's PNG render, or the
// member's picked AI-from-photo rendition. Same multer storage, same
// 5 MB / image-only limits, same moderateImage gate as
// /api/account/photo — the produced image becomes the account's
// effective face and is remembered per route (faceImg + faceImgMode)
// so the member can switch away and back without remaking it.
app.post("/api/account/face/upload", photoUpload(async (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) {
    if (req.file) fs.unlink(req.file.path, () => {});
    return;
  }
  try {
    if (!req.file) {
      return res.status(400).json({ ok: false, error: "No image file received." });
    }
    const mode = String((req.body || {}).mode || "").trim().toLowerCase();
    if (mode !== "build" && mode !== "ai") {
      fs.unlink(req.file.path, () => {});
      return res.status(400).json({ ok: false, error: "That upload route only takes a built avatar or an AI avatar." });
    }
    let spec = null;
    if (mode === "build") {
      try { spec = normFaceBuild(JSON.parse(String((req.body || {}).spec || ""))); } catch (e) { spec = null; }
      if (!spec) {
        fs.unlink(req.file.path, () => {});
        return res.status(400).json({ ok: false, error: "That avatar build doesn't look right — reopen the builder and save again." });
      }
    }
    const publicUrl = `https://${req.get("host")}/photos/${req.file.filename}`;
    const mod = await moderateImage(publicUrl);
    if (!mod.ok) {
      fs.unlink(req.file.path, () => {});
      console.log("FACE IMAGE REJECTED:", ctx.user.id, mod.reason);
      return res.status(422).json({ ok: false, error: "That image didn't pass our safety check. Please try a different one." });
    }
    if (mod.unreviewed) {
      console.log("FACE IMAGE UNREVIEWED (no HIVE_API_KEY):", ctx.user.id, publicUrl);
    }
    const u = ctx.user;
    u.faceMode = mode;
    u.faceImg = publicUrl;
    u.faceImgMode = mode;
    if (mode === "build") u.faceBuild = spec;
    u.photo = publicUrl;
    writeAccounts(ctx.db);
    refreshPlayerPhoto(u.id, publicUrl);
    return res.json({ ok: true, photoUrl: publicUrl, user: publicAccount(u) });
  } catch (e) {
    console.log("FACE UPLOAD ERROR:", e.message);
    return res.status(500).json({ ok: false, error: "Upload failed. Please try again." });
  }
}));

// The AI route's source photo. The moderation gate runs on the SOURCE
// before any stylizing happens client-side (the picked rendition is
// moderated again by face/upload on its way in). The source is stored
// on the account (u.faceAiSource) so a future generative provider
// plugs into exactly this step; setting a source never changes the
// member's current face by itself.
app.post("/api/account/face/source", photoUpload(async (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) {
    if (req.file) fs.unlink(req.file.path, () => {});
    return;
  }
  try {
    if (!req.file) {
      return res.status(400).json({ ok: false, error: "No image file received." });
    }
    const publicUrl = `https://${req.get("host")}/photos/${req.file.filename}`;
    const mod = await moderateImage(publicUrl);
    if (!mod.ok) {
      fs.unlink(req.file.path, () => {});
      console.log("FACE SOURCE REJECTED:", ctx.user.id, mod.reason);
      return res.status(422).json({ ok: false, error: "That photo didn't pass our safety check. Please try a different one." });
    }
    if (mod.unreviewed) {
      console.log("FACE SOURCE UNREVIEWED (no HIVE_API_KEY):", ctx.user.id, publicUrl);
    }
    ctx.user.faceAiSource = publicUrl;
    writeAccounts(ctx.db);
    return res.json({ ok: true, photoUrl: publicUrl, user: publicAccount(ctx.user) });
  } catch (e) {
    console.log("FACE SOURCE ERROR:", e.message);
    return res.status(500).json({ ok: false, error: "Upload failed. Please try again." });
  }
}));

// Upload a profile photo. The uploader must be a joined player (playerId =
// their socket id). On success the photo URL is saved on the player and
// broadcast to everyone in their room. [RP-V7.50] It is ALSO bound to the
// uploader's account (resolved from the Bearer token, else the socket's
// acct-presence announcement) — the account is the source of truth, so
// the photo survives sign-out and follows the member to any device.
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
    // [RP-V7.50] Bind the photo to the account record. Best-effort: a
    // binding failure never fails the upload itself.
    try {
      const adb = readAccounts();
      let au = accountForToken(adb, req);
      if (!au) {
        const sk = io.sockets.sockets.get(player.id);
        const aid = sk && sk.data && sk.data.accountId;
        if (aid) au = adb.users.find((x) => x.id === aid) || null;
      }
      if (au && au.photo !== publicUrl) {
        au.photo = publicUrl;
        // [RP-V7.88] Same face bookkeeping as /api/account/photo.
        au.photoOrig = publicUrl;
        au.faceMode = "photo";
        // [RP-V7.62] Same gallery sync as /api/account/photo: the new
        // main photo moves to the front of the stored gallery.
        const lgal = accountPhotos(au).filter((x) => x !== publicUrl);
        lgal.unshift(publicUrl);
        au.photos = lgal.slice(0, ACCOUNT_PHOTOS_MAX);
        writeAccounts(adb);
      }
    } catch (e) { /* the upload already succeeded */ }
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
// ---------------------------------------------------------------------------
// [RP-V7.51] Emoji reactions on Photos + Reels (Branden: "Add emojis for
// photos and reels" → Both → "Give all the emojis"). Any emoji from the
// full picker can be a reaction; a member may hold several DIFFERENT
// emojis on one post (once each) and tapping theirs again removes it.
// Storage: reels carry reactions inside their reels.json entry
// (reactions: { emoji: [accountId, ...] }) — extending the existing
// store. Photo (Moments) posts have NO server store (they live in the
// client), so their reactions get one small store file of the same
// atomic tmp+rename shape, keyed by the client-side post id.
// Clients only ever receive counts + their own picks — never member
// lists. A reaction is NOT a like: nothing here touches reel-signals.
// ---------------------------------------------------------------------------
const REACTIONS_FILE =
  process.env.REACTIONS_FILE ||
  path.join(path.dirname(PHOTO_DIR), "reactions.json");
const RX_MAX_DISTINCT_PER_MEMBER = 25;
function readPhotoReactions() {
  try {
    const db = JSON.parse(fs.readFileSync(REACTIONS_FILE, "utf8"));
    if (db && typeof db === "object" && db.photos && typeof db.photos === "object")
      return db;
  } catch (e) {}
  return { photos: {} };
}
function writePhotoReactions(db) {
  const tmp = REACTIONS_FILE + ".tmp";
  fs.writeFileSync(tmp, JSON.stringify(db, null, 2));
  fs.renameSync(tmp, REACTIONS_FILE);
}
// One emoji = exactly one grapheme cluster (ZWJ families, keycaps and
// flag pairs count as one), a sane byte cap, and a lone ASCII letter,
// digit or punctuation mark is not an emoji — refuse it as junk.
function rxCleanEmoji(v) {
  const s = String(v == null ? "" : v).trim();
  if (!s) return null;
  if (Buffer.byteLength(s, "utf8") > 32) return null;
  let clusters = 0;
  try {
    const seg = new Intl.Segmenter("en", { granularity: "grapheme" });
    for (const _part of seg.segment(s)) {
      clusters++;
      if (clusters > 1) return null;
    }
  } catch (e) {
    if ([...s].length > 10) return null;
    clusters = 1;
  }
  if (clusters !== 1) return null;
  if (/^[\x20-\x7E]$/.test(s)) return null;
  return s;
}
// reactions map (emoji -> [accountId]) -> { counts, mine } for one user.
function rxSummarize(map, uid) {
  // [RP-V7.89] ONE reaction per member per post (owner: "This should
  // only show once not where I can pick multiple ones"). Stored maps
  // predate the rule and carry no timestamps, so a member holding
  // several emojis collapses to the FIRST emoji in the map's stored
  // key order — counts and "mine" both derive from the per-account
  // records with that dedupe, so reads are correct even before any
  // new write heals the record (rxToggle normalizes on write).
  const counts = {};
  const mine = [];
  if (map && typeof map === "object") {
    const counted = new Set();
    for (const emoji of Object.keys(map)) {
      const ids = Array.isArray(map[emoji]) ? map[emoji] : [];
      let n = 0;
      for (const id of ids) {
        if (counted.has(id)) continue;
        counted.add(id);
        n++;
        if (uid && id === uid) mine.push(emoji);
      }
      if (n) counts[emoji] = n;
    }
  }
  return { counts, mine };
}
// Toggle uid's hold on emoji inside a reactions map (mutates). Returns
// false when the member already holds the per-post distinct cap and
// tried to add one more.
function rxToggle(map, uid, emoji) {
  // [RP-V7.89] Single-choice (Facebook model): first collapse any
  // legacy multi-holds to the member's first-stored emoji, then —
  // tapping the held emoji removes it; tapping any other emoji
  // SWITCHES (old -1, new +1). Never refuses.
  const held = Object.keys(map).filter(
    (e) => Array.isArray(map[e]) && map[e].includes(uid)
  );
  for (const e of held.slice(1)) {
    map[e] = map[e].filter((x) => x !== uid);
    if (!map[e].length) delete map[e];
  }
  const cur = Array.isArray(map[emoji]) ? map[emoji] : null;
  if (cur && cur.includes(uid)) {
    map[emoji] = cur.filter((x) => x !== uid);
    if (!map[emoji].length) delete map[emoji];
    return true;
  }
  for (const e of Object.keys(map)) {
    if (e !== emoji && Array.isArray(map[e]) && map[e].includes(uid)) {
      map[e] = map[e].filter((x) => x !== uid);
      if (!map[e].length) delete map[e];
    }
  }
  if (!Array.isArray(map[emoji])) map[emoji] = [];
  map[emoji].push(uid);
  return true;
}
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
  const vdb64 = readViews(); // [RP-V7.64] public tile counts ride along
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
      // [RP-V7.90] the reel's attached sound (reference + mix), if any.
      musicTrackId: r.musicTrackId || null,
      musicStart: typeof r.musicStart === "number" ? r.musicStart : null,
      musicVol: typeof r.musicVol === "number" ? r.musicVol : null,
      origVol: typeof r.origVol === "number" ? r.origVol : null,
      // [RP-V7.64] Real server-owned view count (the tile number).
      views: mediaViewCount(vdb64, "reel:" + r.id),
      // [RP-V7.51] Compact reaction summary: counts for everyone, the
      // caller's own picks only when they sent a valid token.
      reactions: rxSummarize(r.reactions, null).counts,
      // [RP-V7.84] FIX-4/FIX-3: heart-likes and comments are account
      // state on the reel record. Counts are public; the caller's own
      // heart rides only with a valid token (same rule as myReactions).
      heartLikes: Array.isArray(r.heartLikes) ? r.heartLikes.length : 0,
      // [RP-V7.89] Reposts ride the payload like heart-likes do.
      reposts: Array.isArray(r.reposts) ? r.reposts.length : 0,
      comments: reelPublicComments(r),
      commentCount: Array.isArray(r.comments) ? r.comments.length : 0,
      ...(fyUser
        ? {
            myReactions: rxSummarize(r.reactions, fyUser.id).mine,
            myHeart:
              Array.isArray(r.heartLikes) && r.heartLikes.includes(fyUser.id),
            myReposted:
              Array.isArray(r.reposts) && r.reposts.some((x) => x && x.u === fyUser.id),
          }
        : {}),
    };
  });
  res.json({ ok: true, reels: list, ...(fyUser ? { ranked: true } : {}) });
});
// [RP-V7.89] Hashtag view (owner: "Hashtags help a lot to see what a
// person likes"): GET /api/tag/<tag> lists reels + photo posts whose
// captions carry that hashtag, newest first. Public counts; the
// caller's own like/repost state rides with a valid token, exactly
// like the surfaces these posts normally ride.
app.get("/api/tag/:tag", (req, res) => {
  const tag = String(req.params.tag || "").toLowerCase().replace(/[^a-z0-9_]/g, "").slice(0, 40);
  if (!tag) return res.status(400).json({ ok: false, error: "Bad tag" });
  let uid = null;
  try {
    const u = accountForToken(readAccounts(), req);
    if (u) uid = u.id;
  } catch (e) {}
  const hasTag = (text) => styleKeysForCaption(text).tags.includes(tag);
  const reels = listReels()
    .filter((r) => r && hasTag(r.caption))
    .sort((a, b) => String(b.createdAt).localeCompare(String(a.createdAt)))
    .slice(0, 60)
    .map((r) => ({
      id: r.id,
      author: r.author,
      caption: r.caption,
      createdAt: r.createdAt,
      url: "/reel-files/" + r.file,
      views: mediaViewCount(readViews(), "reel:" + r.id),
      heartLikes: Array.isArray(r.heartLikes) ? r.heartLikes.length : 0,
      reposts: Array.isArray(r.reposts) ? r.reposts.length : 0,
      myReposted: !!uid && Array.isArray(r.reposts) && r.reposts.some((x) => x && x.u === uid),
      commentCount: Array.isArray(r.comments) ? r.comments.length : 0,
    }));
  const likesDb = readPhotoLikes();
  const commentsDb = readPhotoComments();
  const repostsDb = readPhotoReposts();
  const photos = readPhotoPosts()
    .posts.filter((x) => x && hasTag(x.caption))
    .slice(0, 60)
    .map((x) => photoPublicPost(x, uid, likesDb, commentsDb, repostsDb));
  res.json({ ok: true, tag, reels, photos });
});

// ---------------------------------------------------------------------------
// [RP-V7.90] ADD SOUND — the camera's music layer. The catalog itself stays
// the client's TRACKS shelf (licensed Pixabay instrumentals, served at
// full source quality from /audio/); this block mirrors only the track
// IDS + their style families so the server can validate references and
// feed the For You style profile. Authorized scope, nothing wider:
//   - reel + photo-post records carry musicTrackId/musicStart/musicVol
//     (+ origVol on reels) — stored and returned verbatim;
//   - Favorites + Recents are ACCOUNT state (the brain rule) in
//     sounds.json, with Plaza-wide usage counts for cold-start ordering;
//   - using a track on a post bumps its style family +4 in the EXISTING
//     reel-signals machinery (the gift-hook convention: +4 per event);
//     favoriting bumps +4 / unfavoriting -4, transition-guarded exactly
//     like a reel like; completing a watch of a reel that carries a
//     track credits the track's family +3 alongside the completion.
const SOUND_TRACKS = {
  reggae: { family: "music" }, gospel: { family: "faith" },
  soft: { family: "music" }, party: { family: "music" },
  lofi: { family: "music" }, island: { family: "music" },
  worship: { family: "faith" }, dance: { family: "dance" },
};
function soundCleanId(v) {
  const s = String(v || "");
  return Object.prototype.hasOwnProperty.call(SOUND_TRACKS, s) ? s : null;
}
const SOUNDS_FILE =
  process.env.SOUNDS_FILE || path.join(path.dirname(PHOTO_DIR), "sounds.json");
function readSounds() {
  try {
    const d = JSON.parse(fs.readFileSync(SOUNDS_FILE, "utf8"));
    if (d && d.users && typeof d.users === "object" && d.usage && typeof d.usage === "object") {
      if (!d.trend || typeof d.trend !== "object") d.trend = {};
      return d;
    }
  } catch {}
  return { users: {}, usage: {}, trend: {} };
}
// [RP-V7.90] TRENDING — computed, never hand-picked: a per-track score
// bumped by REAL Plaza activity (post +10 · favorite add +4 ·
// "use this sound" tap +3 · completed watch of a tracked reel +2),
// decayed with the codebase's own convention (7-day half-life, the
// fyDecayed math from the reel-signals store) so this week's riser
// outranks an old evergreen.
function soundTrendBump(trackId, w) {
  const d = readSounds();
  const now = Date.now();
  const v = Math.min(9999, fyDecayed(d.trend[trackId], now) + w);
  d.trend[trackId] = { s: Math.round(v * 1000) / 1000, at: now };
  writeSounds(d);
}
function soundTrending(d) {
  const now = Date.now();
  const order = Object.keys(SOUND_TRACKS);
  const scores = {};
  for (const id of order) scores[id] = Math.round(fyDecayed(d.trend[id], now) * 1000) / 1000;
  const ids = order.slice().sort((a, b) => {
    if (scores[b] !== scores[a]) return scores[b] - scores[a];
    const ua = (d.usage && d.usage[a]) || 0, ub = (d.usage && d.usage[b]) || 0;
    if (ub !== ua) return ub - ua;
    return order.indexOf(a) - order.indexOf(b);
  });
  return { ids, scores };
}
function writeSounds(d) {
  const tmp = SOUNDS_FILE + ".tmp";
  fs.writeFileSync(tmp, JSON.stringify(d, null, 2));
  fs.renameSync(tmp, SOUNDS_FILE);
}
function soundBumpFamily(uid, trackId, delta) {
  const fam = SOUND_TRACKS[trackId] && SOUND_TRACKS[trackId].family;
  if (!uid || !fam || !delta) return;
  const sig = readReelSignals();
  const urec = fyUserRec(sig, uid, true);
  fyBumpStyleKeys(urec, { tags: [], families: [fam] }, delta, Date.now());
  writeReelSignals(sig);
}
function soundTouchUse(uid, trackId) {
  const d = readSounds();
  d.usage[trackId] = (d.usage[trackId] || 0) + 1;
  if (uid) {
    const u = d.users[uid] || (d.users[uid] = { favs: [], recents: [] });
    u.recents = [trackId].concat((u.recents || []).filter((x) => x !== trackId)).slice(0, 12);
  }
  writeSounds(d);
  soundBumpFamily(uid, trackId, 4); // a use is a like-tier (+4) style signal
  soundTrendBump(trackId, 10); // a post is the heaviest trending signal
}
app.get("/api/sounds/state", (req, res) => {
  const d = readSounds();
  let user = null;
  try { user = accountForToken(readAccounts(), req); } catch (e) { user = null; }
  const out = { ok: true, usage: d.usage || {} };
  const tr = soundTrending(d);
  out.trending = tr.ids;
  out.trendScores = tr.scores;
  // [RP-V7.90] No featured/hand-picked list exists — the owner
  // retracted handpicks: Trending is the algorithm's alone.
  if (user) {
    const u = d.users[user.id] || { favs: [], recents: [] };
    out.favorites = Array.isArray(u.favs) ? u.favs : [];
    out.recents = Array.isArray(u.recents) ? u.recents : [];
    // The caller's OWN decayed style weights (their picker ordering) —
    // own record only, the same privacy rule as every signal surface.
    const sig = readReelSignals();
    const urec = fyUserRec(sig, user.id, false);
    const now = Date.now();
    const style = {};
    if (urec && urec.styleAff) {
      for (const fam of Object.keys(STYLE_FAMILIES)) {
        const w = fyDecayed(urec.styleAff[fam], now);
        if (w) style[fam] = Math.round(w * 1000) / 1000;
      }
    }
    out.style = style;
  }
  res.json(out);
});
app.post("/api/sounds/favorite", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return; // guests keep a device-local list (client-side)
  const b = req.body || {};
  const tid = soundCleanId(b.trackId);
  if (!tid) return res.status(400).json({ ok: false, error: "Unknown track" });
  const want = b.fav === true;
  const d = readSounds();
  const u = d.users[ctx.user.id] || (d.users[ctx.user.id] = { favs: [], recents: [] });
  if (!Array.isArray(u.favs)) u.favs = [];
  const has = u.favs.includes(tid);
  if (want && !has) u.favs.push(tid);
  if (!want && has) u.favs = u.favs.filter((x) => x !== tid);
  writeSounds(d);
  if (want !== has) soundBumpFamily(ctx.user.id, tid, want ? 4 : -4);
  if (want && !has) soundTrendBump(tid, 4);
  res.json({ ok: true, favorites: u.favs });
});
app.post("/api/sounds/use-tap", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return; // guests write no signals — the standing rule
  const tid = soundCleanId((req.body || {}).trackId);
  if (!tid) return res.status(400).json({ ok: false, error: "Unknown track" });
  soundTrendBump(tid, 3); // "use this sound" tap from a watched reel
  res.json({ ok: true });
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
    // [RP-V7.90] Add Sound: an optional catalog track reference + the
    // poster's mix (start point, music volume, original volume). The
    // track FILE is never uploaded or re-encoded — the record carries
    // the reference and players stream the full-quality source.
    const musicTrackId = soundCleanId(rb.musicTrackId);
    const musicStart = musicTrackId ? (reelNum(rb.musicStart, 0, 3600) || 0) : null;
    const musicVol = musicTrackId ? (reelNum(rb.musicVol, 0, 1) ?? 0.8) : null;
    const origVol = musicTrackId ? (reelNum(rb.origVol, 0, 1) ?? 1) : null;
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
      ...(musicTrackId ? { musicTrackId, musicStart, musicVol, origVol } : {}),
    });
    if (musicTrackId) soundTouchUse(authorUser ? authorUser.id : null, musicTrackId);
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
// ---------------------------------------------------------------------------
// [RP-V7.89] STYLE affinity — the For You profile learns WHAT a member
// likes, not just WHO (owner: "make sure the algorithm feeds off of what
// you like to see... If I watch a lot of sports make the algorithm send
// me more sports videos and pictures" + "Hashtags help a lot to see what
// a person likes"). Style keys come from metadata the app already has:
//   - HASHTAGS in reel / photo-post captions are the PRIMARY signal —
//     every #tag is a style bucket of its own (open vocabulary).
//   - Caption WORDS never create buckets; they only roll up into the
//     curated FAMILIES below (a football post feeds "sports"), so plain
//     text can never override or dilute an explicit hashtag.
//   - A live's room/theme text rolls into families the same way.
// Style weights live in the SAME per-member record (urec.styleAff) with
// the SAME decay (7-day half-life) and clamp family ([-10, 60]) as
// author affinity. A post's style weight = its tag weights + its family
// weights, families counted ONCE per post (no multi-tag stuffing), the
// sum clamped to the same [-10, 60] so style is comparable to one
// author affinity in the combined score.
const STYLE_FAMILIES = {
  faith: ["faith","church","jesus","god","bible","scripture","prayer","praying","worship","gospel","sermon","pastor","ministry","christian","praise","hallelujah","blessing","blessed","testimony","devotion","psalm","verse","choir"],
  sports: ["sports","football","basketball","soccer","baseball","boxing","mma","ufc","nfl","nba","mlb","nhl","fifa","worldcup","highlights","touchdown","dunk","homerun","tennis","golf","racing","nascar","olympics","wrestling","volleyball","softball","hockey","athlete","superbowl","playoffs"],
  music: ["music","song","singing","singer","rap","hiphop","piano","guitar","drums","concert","album","beats","producer","dj","rnb","jazz","blues","rock","metal","country","violin","cello","trumpet","saxophone","freestyle"],
  comedy: ["comedy","funny","laugh","laughs","joke","jokes","humor","hilarious","skit","prank","standup","memes","meme"],
  fitness: ["fitness","gym","workout","workouts","exercise","training","cardio","weights","lifting","running","runner","marathon","yoga","pilates","health","healthy","muscle","strength","crossfit","bodybuilding"],
  food: ["food","cooking","cook","recipe","recipes","baking","chef","kitchen","delicious","yummy","breakfast","lunch","dinner","dessert","cake","pizza","tacos","bbq","grill","vegan","snacks","coffee","tea","restaurant","eats","foodie"],
  fashion: ["fashion","beauty","makeup","style","outfit","ootd","hair","nails","skincare","glam","model","boutique","shopping","dress","shoes","sneakers","aesthetic"],
  gaming: ["gaming","gamer","games","game","xbox","playstation","ps5","nintendo","stream","streaming","twitch","fortnite","minecraft","roblox","cod","gta","esports","gameplay"],
  cars: ["cars","car","truck","trucks","auto","automotive","engine","motorsport","drift","garage","mechanic","ford","chevy","dodge","tesla","bmw","lowrider","offroad","motorcycle","bike","biker","harley"],
  dance: ["dance","dancing","dancer","choreography","ballet","salsa","bachata","twerk","shuffle"],
  pets: ["pets","pet","dog","dogs","puppy","puppies","cat","cats","kitten","kittens","animals","animal","horse","horses","bird","fish","rescue","vet","bunny","rabbit"],
};
const STYLE_WORD2FAM = {};
for (const fam of Object.keys(STYLE_FAMILIES)) {
  for (const w of STYLE_FAMILIES[fam]) if (!STYLE_WORD2FAM[w]) STYLE_WORD2FAM[w] = fam;
  if (!STYLE_WORD2FAM[fam]) STYLE_WORD2FAM[fam] = fam;
}
function styleKeysForCaption(text) {
  const tags = new Set();
  const fams = new Set();
  const str = String(text || "").toLowerCase();
  for (const m of str.matchAll(/#([a-z0-9_]{2,40})/g)) tags.add(m[1]);
  const words = str.replace(/#([a-z0-9_]+)/g, " $1 ").split(/[^a-z0-9]+/);
  for (const w of words) { if (w.length >= 3 && STYLE_WORD2FAM[w]) fams.add(STYLE_WORD2FAM[w]); }
  for (const t of tags) { if (STYLE_WORD2FAM[t]) fams.add(STYLE_WORD2FAM[t]); }
  return { tags: [...tags].slice(0, 8), families: [...fams] };
}
function styleKeysForText(text) {
  // Lives: the room/theme text rolls into families; a single-token room
  // id also counts as its own bucket.
  const k = styleKeysForCaption(text);
  const tok = String(text || "").toLowerCase().replace(/[^a-z0-9]+/g, " ").trim();
  if (tok && !tok.includes(" ") && tok.length >= 2 && !k.tags.includes(tok)) k.tags.push(tok);
  return k;
}
function fyBumpStyleKeys(urec, keys, delta, now) {
  if (!urec || !keys || !delta) return;
  if (!urec.styleAff) urec.styleAff = {};
  const bump = (k) => {
    const v = Math.max(-10, Math.min(60, fyDecayed(urec.styleAff[k], now) + delta));
    urec.styleAff[k] = { s: Math.round(v * 1000) / 1000, at: now };
  };
  for (const t of keys.tags || []) bump(t);
  for (const f of keys.families || []) bump(f);
}
function fyStyleWeight(urec, keys, now) {
  if (!urec || !keys || !urec.styleAff) return 0;
  let sum = 0;
  for (const t of keys.tags || []) sum += fyDecayed(urec.styleAff[t], now);
  for (const f of keys.families || []) sum += fyDecayed(urec.styleAff[f], now);
  return Math.max(-10, Math.min(60, sum));
}
// Fetch (and optionally create) a member's interest record, normalized
// to the full shape — records may have been started by any of the three
// writers (reels signals, live signals, the gift hook).
function fyUserRec(sig, userId, create) {
  let rec = sig.users[userId];
  if (!rec) {
    if (!create) return null;
    rec = sig.users[userId] = { authorAff: {}, liked: {}, seenFull: {}, liveSigAt: {}, storySigDay: {}, pliked: {}, reposted: {}, styleAff: {} };
  }
  if (!rec.authorAff) rec.authorAff = {};
  if (!rec.liked) rec.liked = {};
  if (!rec.seenFull) rec.seenFull = {};
  if (!rec.liveSigAt) rec.liveSigAt = {};
  if (!rec.storySigDay) rec.storySigDay = {};
  if (!rec.pliked) rec.pliked = {};
  if (!rec.reposted) rec.reposted = {}; // [RP-V7.89] repost exactly-once guard (kind:id)
  if (!rec.styleAff) rec.styleAff = {}; // [RP-V7.89] style affinity (tags + families)
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
  // [RP-V7.89] STYLE affinity joins the score: a brand-new author in a
  // member's proven style can outrank an established author in a style
  // the member skips. Same 2.5 weight as one author affinity.
  if (urec && !isOwn) score += 2.5 * fyStyleWeight(urec, styleKeysForCaption(reel.caption), now);
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
// [RP-V7.51] Toggle the caller's reaction on a photo post or a reel.
// Session-only (requireAccount → 401 signed out); pending-deletion
// accounts are refused like everywhere else (403). The response is the
// post's fresh compact summary so the client can re-render its row.
app.post("/api/reactions/toggle", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  if (isPendingDeletion(ctx.user))
    return res
      .status(403)
      .json({ ok: false, error: "This account is scheduled for deletion" });
  const b = req.body || {};
  const kind = b.kind === "reel" ? "reel" : b.kind === "photo" ? "photo" : null;
  const id = reelCleanId(b.id);
  const emoji = rxCleanEmoji(b.emoji);
  if (!kind || !id)
    return res.status(400).json({ ok: false, error: "Bad post reference" });
  if (!emoji)
    return res.status(400).json({ ok: false, error: "Pick one emoji" });
  const uid = ctx.user.id;
  if (kind === "reel") {
    const entry = listReels().find((r) => r.id === id);
    if (!entry) return res.status(404).json({ ok: false, error: "No such reel" });
    if (!entry.reactions || typeof entry.reactions !== "object")
      entry.reactions = {};
    if (!rxToggle(entry.reactions, uid, emoji))
      return res
        .status(400)
        .json({ ok: false, error: "Too many different reactions on one post" });
    updateReelEntry(id, { reactions: entry.reactions });
    const s = rxSummarize(entry.reactions, uid);
    return res.json({ ok: true, kind, id, reactions: s.counts, mine: s.mine });
  }
  const db = readPhotoReactions();
  const map = db.photos[id] || (db.photos[id] = {});
  if (!rxToggle(map, uid, emoji))
    return res
      .status(400)
      .json({ ok: false, error: "Too many different reactions on one post" });
  if (!Object.keys(map).length) delete db.photos[id];
  writePhotoReactions(db);
  const s = rxSummarize(map, uid);
  return res.json({ ok: true, kind, id, reactions: s.counts, mine: s.mine });
});
// [RP-V7.51] Batch reaction summaries for client-side posts (Photos
// have no server feed to ride, so their cards ask for the ids on
// screen). Read is public — counts are public; "mine" appears only
// with a valid session token.
app.get("/api/reactions", (req, res) => {
  const kind = req.query.kind === "reel" ? "reel" : "photo";
  const ids = String(req.query.ids || "")
    .split(",")
    .map((x) => reelCleanId(x))
    .filter(Boolean)
    .slice(0, 50);
  let uid = null;
  try {
    const u = accountForToken(readAccounts(), req);
    if (u) uid = u.id;
  } catch (e) {}
  const posts = {};
  if (kind === "reel") {
    const all = listReels();
    for (const id of ids) {
      const entry = all.find((r) => r.id === id);
      const s = rxSummarize(entry ? entry.reactions : null, uid);
      posts[id] = { reactions: s.counts, mine: s.mine };
    }
  } else {
    const db = readPhotoReactions();
    for (const id of ids) {
      const s = rxSummarize(db.photos[id], uid);
      posts[id] = { reactions: s.counts, mine: s.mine };
    }
  }
  res.json({ ok: true, kind, posts });
});
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
      if (notSelf) { fyBump(urec, key, 4, now); fyBumpStyleKeys(urec, styleKeysForCaption(reel.caption), 4, now); }
    } else if (!want && has) {
      delete urec.liked[reelId];
      agg.likes = Math.max(0, agg.likes - 1);
      if (notSelf) { fyBump(urec, key, -4, now); fyBumpStyleKeys(urec, styleKeysForCaption(reel.caption), -4, now); }
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
      const sKeys = styleKeysForCaption(reel.caption);
      if (completed) { fyBump(urec, key, 3, now); fyBumpStyleKeys(urec, sKeys, 3, now); if (reel.musicTrackId && SOUND_TRACKS[reel.musicTrackId]) fyBumpStyleKeys(urec, { tags: [], families: [SOUND_TRACKS[reel.musicTrackId].family] }, 3, now); soundTrendBump(reel.musicTrackId, 2); }
      else if (frac > 0.6) { fyBump(urec, key, 2, now); fyBumpStyleKeys(urec, sKeys, 2, now); }
      if (skippedFast) { fyBump(urec, key, -1, now); fyBumpStyleKeys(urec, sKeys, -1, now); }
    }
  }
  // Bound the store: drop aggregates for reels that fell out of the index.
  const live = new Set(all.map((r) => r.id));
  for (const id of Object.keys(sig.reels)) if (!live.has(id)) delete sig.reels[id];
  writeReelSignals(sig);
  res.json({ ok: true });
});

// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// [RP-V7.84] FIX-3 + FIX-4 — reel comments and heart-likes become
// ACCOUNT state (brain-train batch 2, sweep G3/G4). Through V7.83 a
// comment lived only in the writing device's localStorage
// (rpReelComments.v1) and a heart-like only in rpReelLikes.v1 — no
// other member ever saw either. Now:
//   comments: stored on the reel record (comments: [{uid, name, text,
//     ts}]) and returned with GET /api/reels; POST /api/reel/comment
//     is token-authed and stamps the account's own display name.
//     Text is cleaned exactly like a reel caption (angle brackets and
//     quotes stripped, trimmed, capped) and the client renders with
//     escHtml as it always has. POST /api/reel/comment also accepts
//     kind:"photo" with the client-side Moments post id, storing into
//     photo-comments.json with the same shape — the endpoint is ready
//     for photo Moments the day those posts get a server store (their
//     posts are still device-local, so the Moments UI does not call
//     it yet and its on-post comments are untouched).
//   heart-likes: a per-account set on the reel record (heartLikes:
//     [accountId]) toggled by POST /api/reel/like; GET /api/reels
//     computes the count from the set and reports the caller's own
//     heart as myHeart. Emoji reactions (above) are a separate system
//     and are NOT touched.
//   the +4 signal: /api/reel/like performs the SAME bookkeeping as
//     the kind:"like" branch of /api/reels/signal, through the SAME
//     exactly-once guard (the caller's liked record in
//     reel-signals.json): whichever endpoint hears about a like first
//     moves the aggregate + affinity (+4 / −4), the other sees the
//     record already set and does nothing — a like can never count
//     twice, and an unlike only ever counts against a recorded like.
// ---------------------------------------------------------------------------
const REEL_COMMENT_MAX = 140; // matches the client input maxlength
const REEL_COMMENTS_KEEP = 300; // stored per post, oldest dropped
const REEL_COMMENTS_RETURN = 100; // newest ones riding GET /api/reels
const PHOTO_COMMENTS_FILE =
  process.env.PHOTO_COMMENTS_FILE ||
  path.join(path.dirname(PHOTO_DIR), "photo-comments.json");
function readPhotoComments() {
  try {
    const db = JSON.parse(fs.readFileSync(PHOTO_COMMENTS_FILE, "utf8"));
    if (db && typeof db === "object" && db.photos && typeof db.photos === "object")
      return db;
  } catch (e) {}
  return { photos: {} };
}
function writePhotoComments(db) {
  const tmp = PHOTO_COMMENTS_FILE + ".tmp";
  fs.writeFileSync(tmp, JSON.stringify(db, null, 2));
  fs.renameSync(tmp, PHOTO_COMMENTS_FILE);
}
// The public shape of a stored comment: display name + text + time.
// The author's account id stays server-side (moderation only) — the
// same "never member lists" rule the reaction summaries follow.
function reelPublicComments(r) {
  const list = r && Array.isArray(r.comments) ? r.comments : [];
  return list.slice(-REEL_COMMENTS_RETURN).map((c) => ({
    name: String((c && c.name) || "Someone").slice(0, 40),
    text: String((c && c.text) || "").slice(0, REEL_COMMENT_MAX),
    ts: (c && c.ts) || null,
  }));
}
function reelCleanCommentText(v) {
  return String(v == null ? "" : v)
    .replace(/[<>&"]/g, "")
    .trim()
    .slice(0, REEL_COMMENT_MAX);
}
app.post("/api/reel/comment", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  if (isPendingDeletion(ctx.user))
    return res
      .status(403)
      .json({ ok: false, error: "This account is scheduled for deletion" });
  const b = req.body || {};
  const kind = b.kind === "photo" ? "photo" : "reel";
  const id = reelCleanId(b.id || b.reelId);
  const text = reelCleanCommentText(b.text);
  if (!id) return res.status(400).json({ ok: false, error: "Bad post reference" });
  if (!text) return res.status(400).json({ ok: false, error: "Write a comment first" });
  const comment = {
    uid: ctx.user.id,
    name: reelCleanName(ctx.user.name) || "Someone",
    text,
    ts: new Date().toISOString(),
  };
  const pub = { name: comment.name, text: comment.text, ts: comment.ts };
  if (kind === "photo") {
    const db = readPhotoComments();
    const list = db.photos[id] || (db.photos[id] = []);
    list.push(comment);
    while (list.length > REEL_COMMENTS_KEEP) list.shift();
    writePhotoComments(db);
    return res.json({ ok: true, kind, id, comment: pub, count: list.length });
  }
  const entry = listReels().find((r) => r.id === id);
  if (!entry) return res.status(404).json({ ok: false, error: "Reel not found" });
  if (!Array.isArray(entry.comments)) entry.comments = [];
  entry.comments.push(comment);
  while (entry.comments.length > REEL_COMMENTS_KEEP) entry.comments.shift();
  updateReelEntry(id, { comments: entry.comments });
  res.json({ ok: true, kind, id, comment: pub, count: entry.comments.length });
});
app.post("/api/reel/like", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  if (isPendingDeletion(ctx.user))
    return res
      .status(403)
      .json({ ok: false, error: "This account is scheduled for deletion" });
  const b = req.body || {};
  const id = reelCleanId(b.id || b.reelId);
  if (!id) return res.status(400).json({ ok: false, error: "Missing reel id" });
  const entry = listReels().find((r) => r.id === id);
  if (!entry) return res.status(404).json({ ok: false, error: "Reel not found" });
  const want = b.liked === true;
  if (!Array.isArray(entry.heartLikes)) entry.heartLikes = [];
  const has = entry.heartLikes.includes(ctx.user.id);
  if (want && !has) {
    entry.heartLikes.push(ctx.user.id);
    updateReelEntry(id, { heartLikes: entry.heartLikes });
  } else if (!want && has) {
    entry.heartLikes = entry.heartLikes.filter((x) => x !== ctx.user.id);
    updateReelEntry(id, { heartLikes: entry.heartLikes });
  }
  // For You bookkeeping — identical semantics to the kind:"like"
  // branch of /api/reels/signal, sharing its exactly-once guard.
  try {
    const sig = readReelSignals();
    const urec = fyUserRec(sig, ctx.user.id, true);
    const agg =
      sig.reels[id] || (sig.reels[id] = { views: 0, completes: 0, likes: 0, fastSkips: 0 });
    const key = reelAuthorKeyFor(ctx.db, entry);
    const notSelf = key && key !== ctx.user.id;
    const sigHas = !!urec.liked[id];
    if (want && !sigHas) {
      urec.liked[id] = true;
      agg.likes += 1;
      if (notSelf) { fyBump(urec, key, 4, Date.now()); fyBumpStyleKeys(urec, styleKeysForCaption(entry.caption), 4, Date.now()); }
    } else if (!want && sigHas) {
      delete urec.liked[id];
      agg.likes = Math.max(0, agg.likes - 1);
      if (notSelf) { fyBump(urec, key, -4, Date.now()); fyBumpStyleKeys(urec, styleKeysForCaption(entry.caption), -4, Date.now()); }
    }
    writeReelSignals(sig);
  } catch (e) { /* affinity bookkeeping must never break a like */ }
  res.json({ ok: true, id, liked: want, heartLikes: entry.heartLikes.length });
});
// [RP-V7.89] REPOST (owner, from his phone on live V7.88: "I'm missing a
// repost button — along with the others for reels and photos"). The
// repost set lives ON the reel record as [{u, at}] so counts ride GET
// /api/reels like heart-likes, and the profile Reposts tab + the Feed
// resolve from the same records. Toggle is idempotent, token identity
// only. A member cannot repost their own reel (refused here AND the
// client hides the button). The For You +4 fires ONCE per (member,
// post) EVER via urec.reposted — unrepost never reverses it and a
// re-repost never re-fires it (deliberately unlike likes).
app.post("/api/reel/repost", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  if (isPendingDeletion(ctx.user))
    return res
      .status(403)
      .json({ ok: false, error: "This account is scheduled for deletion" });
  const b = req.body || {};
  const id = reelCleanId(b.id || b.reelId);
  if (!id) return res.status(400).json({ ok: false, error: "Missing reel id" });
  const entry = listReels().find((r) => r.id === id);
  if (!entry) return res.status(404).json({ ok: false, error: "Reel not found" });
  const key = reelAuthorKeyFor(ctx.db, entry);
  if (key && key === ctx.user.id)
    return res.status(400).json({ ok: false, error: "You can't repost your own post" });
  const want = b.reposted === true;
  if (!Array.isArray(entry.reposts)) entry.reposts = [];
  const has = entry.reposts.some((x) => x && x.u === ctx.user.id);
  if (want && !has) {
    entry.reposts.push({ u: ctx.user.id, at: new Date().toISOString() });
    updateReelEntry(id, { reposts: entry.reposts });
  } else if (!want && has) {
    entry.reposts = entry.reposts.filter((x) => !(x && x.u === ctx.user.id));
    updateReelEntry(id, { reposts: entry.reposts });
  }
  try {
    const sig = readReelSignals();
    const urec = fyUserRec(sig, ctx.user.id, true);
    const gk = "reel:" + id;
    if (want && !urec.reposted[gk]) {
      urec.reposted[gk] = true;
      if (key && key !== ctx.user.id) fyBump(urec, key, 4, Date.now());
      fyBumpStyleKeys(urec, styleKeysForCaption(entry.caption), 4, Date.now());
    }
    writeReelSignals(sig);
  } catch (e) { /* affinity bookkeeping must never break a repost */ }
  res.json({ ok: true, id, reposted: entry.reposts.some((x) => x && x.u === ctx.user.id), reposts: entry.reposts.length });
});

// ---------------------------------------------------------------------------
// [RP-V7.85] FIX-3b — photo Moments posts get a server home (Branden,
// Oct 27: "Add the photo comments"). Through V7.84 a Moments post
// lived ONLY in the posting device's memory: Moments.posts was never
// persisted anywhere, so a member's photo post, its comments and its
// heart-likes all vanished on reload and no other member ever saw
// the post at all. (Emoji reactions were already server state, keyed
// by the client post id — V7.51 — and V7.84's POST /api/reel/comment
// kind:"photo" already wrote comments into photo-comments.json, but
// nothing ever read them back.) Now:
//   posts: photo-posts.json — { posts: [ { id, owner, name, photo,
//     caption, clientKey, ts } ] } newest first, capped. Created by
//     POST /api/photo/post on the SAME pipeline as account photos:
//     the shared multer `upload` into PHOTO_DIR (5 MB, image-only),
//     the same moderateImage gate, the same /photos/ URL shape. The
//     composer may instead pass photoUrl to reuse one of the caller's
//     OWN gallery photos ("Use my online photo") — ownership is
//     checked by file name against the account's gallery. clientKey
//     (the on-device post id) dedupes per owner, so the one-time
//     client migration can never double-post.
//   feed: GET /api/photo/posts is a public read (counts are public);
//     with a token it also reports mine / myLiked. Each post's
//     comments ride the payload out of photo-comments.json in the
//     same public shape as reel comments (name + text + ts — the
//     author's account id never leaves the server).
//   seed/demo posts keep their client ids ("seed0"…); their shared
//     comments + like counts ride GET /api/photo/extras?ids=, the
//     same batch shape as GET /api/reactions.
//   likes: photo-likes.json — { photos: { "<postId>": [accountId] } },
//     a per-account set per post, toggled by POST /api/photo/like
//     (idempotent). Counts are computed from the set everywhere.
//   the +4 signal: liking a MEMBER's post bumps the author's
//     affinity in the liker's interest profile exactly once, guarded
//     by urec.pliked in reel-signals.json (normalized in fyUserRec
//     above) — the same economics as reel/story likes; an unlike
//     reverses it only against a recorded like. Likes on seed/demo
//     ids are recorded (shared counts) but emit no signal: those
//     posts have no account author. Self-likes never emit a signal.
// ---------------------------------------------------------------------------
const PHOTO_POSTS_FILE =
  process.env.PHOTO_POSTS_FILE ||
  path.join(path.dirname(PHOTO_DIR), "photo-posts.json");
const PHOTO_LIKES_FILE =
  process.env.PHOTO_LIKES_FILE ||
  path.join(path.dirname(PHOTO_DIR), "photo-likes.json");
const PHOTO_POSTS_KEEP = 500;
const PHOTO_POSTS_RETURN = 100;
function readPhotoPosts() {
  return storeReadJson(
    PHOTO_POSTS_FILE,
    (d) => !!(d && Array.isArray(d.posts)),
    { posts: [] },
    "photo-posts"
  );
}
function writePhotoPosts(db) {
  storeWriteJson(PHOTO_POSTS_FILE, db);
}
function readPhotoLikes() {
  try {
    const db = JSON.parse(fs.readFileSync(PHOTO_LIKES_FILE, "utf8"));
    if (db && typeof db === "object" && db.photos && typeof db.photos === "object")
      return db;
  } catch (e) {}
  return { photos: {} };
}
function writePhotoLikes(db) {
  const tmp = PHOTO_LIKES_FILE + ".tmp";
  fs.writeFileSync(tmp, JSON.stringify(db, null, 2));
  fs.renameSync(tmp, PHOTO_LIKES_FILE);
}
function photoLikeCount(likesDb, id) {
  const s = likesDb.photos[id];
  return Array.isArray(s) ? s.length : 0;
}
// [RP-V7.89] Reposts for photo posts: photo-reposts.json
// { photos: { <postId>: [{ u, at }] } } — same read/write discipline as
// photo-likes.json (plain read + tmp/rename write).
const PHOTO_REPOSTS_FILE =
  process.env.PHOTO_REPOSTS_FILE ||
  path.join(path.dirname(PHOTO_DIR), "photo-reposts.json");
function readPhotoReposts() {
  try {
    const db = JSON.parse(fs.readFileSync(PHOTO_REPOSTS_FILE, "utf8"));
    if (db && typeof db === "object" && db.photos && typeof db.photos === "object")
      return db;
  } catch (e) {}
  return { photos: {} };
}
function writePhotoReposts(db) {
  const tmp = PHOTO_REPOSTS_FILE + ".tmp";
  fs.writeFileSync(tmp, JSON.stringify(db, null, 2));
  fs.renameSync(tmp, PHOTO_REPOSTS_FILE);
}
function photoRepostSet(repostsDb, id) {
  const s2 = repostsDb && repostsDb.photos ? repostsDb.photos[id] : null;
  return Array.isArray(s2) ? s2 : [];
}
function photoPublicPost(p, uid, likesDb, commentsDb, repostsDb) {
  const list = (commentsDb.photos && commentsDb.photos[p.id]) || [];
  const set = Array.isArray(likesDb.photos[p.id]) ? likesDb.photos[p.id] : [];
  const rset = photoRepostSet(repostsDb, p.id);
  return {
    id: p.id,
    author: p.name,
    photo: p.photo,
    caption: p.caption || "",
    createdAt: p.ts || null,
    mine: !!uid && uid === p.owner,
    likes: set.length,
    myLiked: !!uid && set.includes(uid),
    // [RP-V7.89] repost count + the caller's own state, like likes.
    reposts: rset.length,
    myReposted: !!uid && rset.some((x) => x && x.u === uid),
    comments: reelPublicComments({ comments: list }),
    commentCount: list.length,
    // [RP-V7.90] attached sound reference on photo posts, same shape as reels.
    musicTrackId: p.musicTrackId || null,
    musicStart: typeof p.musicStart === "number" ? p.musicStart : null,
    musicVol: typeof p.musicVol === "number" ? p.musicVol : null,
  };
}
app.post("/api/photo/post", photoUpload(async (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) {
    if (req.file) fs.unlink(req.file.path, () => {});
    return;
  }
  if (isPendingDeletion(ctx.user)) {
    if (req.file) fs.unlink(req.file.path, () => {});
    return res
      .status(403)
      .json({ ok: false, error: "This account is scheduled for deletion" });
  }
  try {
    const b = req.body || {};
    const caption = reelCleanCommentText(b.caption);
    const clientKey = reelCleanId(b.clientKey);
    const db = readPhotoPosts();
    if (clientKey) {
      const ex = db.posts.find(
        (p) => p.owner === ctx.user.id && p.clientKey === clientKey
      );
      if (ex) {
        if (req.file) fs.unlink(req.file.path, () => {});
        return res.json({
          ok: true,
          deduped: true,
          post: photoPublicPost(ex, ctx.user.id, readPhotoLikes(), readPhotoComments(), readPhotoReposts()),
        });
      }
    }
    let photoUrl = null;
    if (req.file) {
      photoUrl = `https://${req.get("host")}/photos/${req.file.filename}`;
      const mod = await moderateImage(photoUrl);
      if (!mod.ok) {
        fs.unlink(req.file.path, () => {});
        console.log("PHOTO POST REJECTED:", ctx.user.id, mod.reason);
        return res.status(422).json({
          ok: false,
          error: "That photo didn't pass our safety check. Please try a different one.",
        });
      }
      if (mod.unreviewed) {
        console.log("PHOTO POST UNREVIEWED (no HIVE_API_KEY):", ctx.user.id, photoUrl);
      }
    } else if (b.photoUrl) {
      const url = String(b.photoUrl).slice(0, 600);
      const fileOf = (u) => {
        const i = String(u || "").indexOf("/photos/");
        return i >= 0 ? String(u).slice(i + "/photos/".length) : null;
      };
      const f = fileOf(url);
      const owned = !!f && accountPhotos(ctx.user).some((u) => fileOf(u) === f);
      if (!owned)
        return res.status(400).json({ ok: false, error: "That photo isn't one of yours" });
      photoUrl = url;
    }
    if (!photoUrl)
      return res.status(400).json({ ok: false, error: "Pick a photo first" });
    const musicTrackId = soundCleanId(b.musicTrackId);
    const post = {
      id: "ph" + Date.now().toString(36) + crypto.randomBytes(3).toString("hex"),
      owner: ctx.user.id,
      name: reelCleanName(ctx.user.name) || "Someone",
      photo: photoUrl,
      caption,
      clientKey: clientKey || null,
      ts: new Date().toISOString(),
      ...(musicTrackId ? { musicTrackId, musicStart: reelNum(b.musicStart, 0, 3600) || 0, musicVol: reelNum(b.musicVol, 0, 1) ?? 0.8 } : {}),
    };
    if (musicTrackId) soundTouchUse(ctx.user.id, musicTrackId);
    db.posts.unshift(post);
    db.posts = db.posts.slice(0, PHOTO_POSTS_KEEP);
    writePhotoPosts(db);
    return res.json({
      ok: true,
      post: photoPublicPost(post, ctx.user.id, readPhotoLikes(), readPhotoComments(), readPhotoReposts()),
    });
  } catch (e) {
    console.log("PHOTO POST ERROR:", e.message);
    if (req.file) fs.unlink(req.file.path, () => {});
    return res.status(500).json({ ok: false, error: "Posting failed. Please try again." });
  }
}));
app.get("/api/photo/posts", (req, res) => {
  let uid = null;
  try {
    const u = accountForToken(readAccounts(), req);
    if (u) uid = u.id;
  } catch (e) {}
  const likesDb = readPhotoLikes();
  const commentsDb = readPhotoComments();
  const repostsDb = readPhotoReposts();
  const posts = readPhotoPosts()
    .posts.slice(0, PHOTO_POSTS_RETURN)
    .map((p) => photoPublicPost(p, uid, likesDb, commentsDb, repostsDb));
  res.json({ ok: true, posts });
});
// [RP-V7.85] Batch social state for posts that have no server post
// record (the client-seeded demo posts): shared comments + like
// counts by id. Public read — counts are public; myLiked appears
// only with a valid session token. Mirrors GET /api/reactions.
app.get("/api/photo/extras", (req, res) => {
  const ids = String(req.query.ids || "")
    .split(",")
    .map((x) => reelCleanId(x))
    .filter(Boolean)
    .slice(0, 50);
  let uid = null;
  try {
    const u = accountForToken(readAccounts(), req);
    if (u) uid = u.id;
  } catch (e) {}
  const likesDb = readPhotoLikes();
  const commentsDb = readPhotoComments();
  const repostsDbE = readPhotoReposts();
  const posts = {};
  for (const id of ids) {
    const list = (commentsDb.photos && commentsDb.photos[id]) || [];
    const set = Array.isArray(likesDb.photos[id]) ? likesDb.photos[id] : [];
    const rset = photoRepostSet(repostsDbE, id);
    posts[id] = {
      comments: reelPublicComments({ comments: list }),
      commentCount: list.length,
      likes: set.length,
      myLiked: !!uid && set.includes(uid),
      reposts: rset.length,
      myReposted: !!uid && rset.some((x) => x && x.u === uid),
    };
  }
  res.json({ ok: true, posts });
});
app.post("/api/photo/like", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  if (isPendingDeletion(ctx.user))
    return res
      .status(403)
      .json({ ok: false, error: "This account is scheduled for deletion" });
  const b = req.body || {};
  const id = reelCleanId(b.id);
  if (!id) return res.status(400).json({ ok: false, error: "Bad post reference" });
  const want = b.liked === true;
  const db = readPhotoLikes();
  const set = Array.isArray(db.photos[id]) ? db.photos[id].slice() : [];
  const has = set.includes(ctx.user.id);
  if (want && !has) set.push(ctx.user.id);
  if (!want && has) set.splice(set.indexOf(ctx.user.id), 1);
  if (set.length) db.photos[id] = set;
  else delete db.photos[id];
  writePhotoLikes(db);
  // For You bookkeeping — the +4 like signal, exactly once, only for
  // a real member's post (seed/demo ids have no account author) and
  // never for a self-like; guarded by the caller's pliked record.
  try {
    const post = readPhotoPosts().posts.find((p) => p.id === id);
    if (post && post.owner && post.owner !== ctx.user.id) {
      const sig = readReelSignals();
      const urec = fyUserRec(sig, ctx.user.id, true);
      const sigHas = !!urec.pliked[id];
      if (want && !sigHas) {
        urec.pliked[id] = true;
        fyBump(urec, post.owner, 4, Date.now());
        fyBumpStyleKeys(urec, styleKeysForCaption(post.caption), 4, Date.now());
      } else if (!want && sigHas) {
        delete urec.pliked[id];
        fyBump(urec, post.owner, -4, Date.now());
        fyBumpStyleKeys(urec, styleKeysForCaption(post.caption), -4, Date.now());
      }
      writeReelSignals(sig);
    }
  } catch (e) { /* affinity bookkeeping must never break a like */ }
  res.json({ ok: true, id, liked: set.includes(ctx.user.id), likes: set.length });
});
// [RP-V7.89] REPOST for photo posts — mirrors /api/reel/repost. Only
// real server posts can be reposted (seed/demo ids have no record and
// answer 404; the client renders no repost button on them). Own-post
// refused. The +4 (author + style) fires once per (member, post) EVER
// via urec.reposted and never reverses.
app.post("/api/photo/repost", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  if (isPendingDeletion(ctx.user))
    return res
      .status(403)
      .json({ ok: false, error: "This account is scheduled for deletion" });
  const b = req.body || {};
  const id = reelCleanId(b.id);
  if (!id) return res.status(400).json({ ok: false, error: "Bad post reference" });
  const post = readPhotoPosts().posts.find((x) => x && x.id === id);
  if (!post) return res.status(404).json({ ok: false, error: "Post not found" });
  if (post.owner === ctx.user.id)
    return res.status(400).json({ ok: false, error: "You can't repost your own post" });
  const want = b.reposted === true;
  const db = readPhotoReposts();
  const set = photoRepostSet(db, id).slice();
  const has = set.some((x) => x && x.u === ctx.user.id);
  if (want && !has) set.push({ u: ctx.user.id, at: new Date().toISOString() });
  if (!want && has) {
    const ix = set.findIndex((x) => x && x.u === ctx.user.id);
    if (ix >= 0) set.splice(ix, 1);
  }
  if (set.length) db.photos[id] = set;
  else delete db.photos[id];
  writePhotoReposts(db);
  try {
    const sig = readReelSignals();
    const urec = fyUserRec(sig, ctx.user.id, true);
    const gk = "photo:" + id;
    if (want && !urec.reposted[gk]) {
      urec.reposted[gk] = true;
      if (post.owner && post.owner !== ctx.user.id) fyBump(urec, post.owner, 4, Date.now());
      fyBumpStyleKeys(urec, styleKeysForCaption(post.caption), 4, Date.now());
    }
    writeReelSignals(sig);
  } catch (e) { /* affinity bookkeeping must never break a repost */ }
  res.json({ ok: true, id, reposted: set.some((x) => x && x.u === ctx.user.id), reposts: set.length });
});

// [RP-V7.64] Media view counts — the Facebook-style "👁 332K" on every
// picture and video tile (Branden, Oct 25: "You see how these posted
// videos view you can see how many people views it" → "Make the
// pictures and videos just like this"). Counts are REAL and SERVER-
// OWNED (the brain rule: they live with the content, not on a device):
// one small store, views.json, shaped
//   { items: { "<itemKey>": { count, seen: { "<viewerKey>": "YYYY-MM-DD" } } } }
// Item keys: "reel:<reelId>" and "photo:<ownerAccountId>:<photoUrl>"
// (URL-keyed, so reordering a gallery never moves a photo's count).
// Dedupe: a viewer counts at most ONCE per item per America/New_York
// calendar day (same Intl day key as the Daily Ranking tally). Viewer
// identity: the account token when one rides along, else the client's
// per-device key (rpDeviceKey.v1, same shape the socket join carries).
// A client can only ever ASK to count a view — it can never set,
// decrement or delete a number. The store prunes on every write: seen
// stamps older than today are dropped (dedupe only ever needs today),
// so the seen maps cannot grow unboundedly; an item entry is dropped
// when its count is 0 and nobody is stamped today.
// Deliberately SEPARATE from reel-signals: a counted "view" here is
// the public tile number; the For You aggregate is untouched.
// ---------------------------------------------------------------------------
const VIEWS_FILE =
  process.env.VIEWS_FILE || path.join(path.dirname(PHOTO_DIR), "views.json");
function viewDayKey() {
  // America/New_York calendar day ("YYYY-MM-DD"), Intl only — the
  // same construction as rankDayKey() for the Daily Ranking tally.
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
function readViews() {
  return storeReadJson(
    VIEWS_FILE,
    (d) => !!(d && d.items && typeof d.items === "object" && !Array.isArray(d.items)),
    { items: {} },
    "views"
  );
}
function writeViews(db) {
  storeWriteJson(VIEWS_FILE, db);
}
function pruneViews(db, today) {
  for (const k of Object.keys(db.items)) {
    const it = db.items[k];
    if (!it || typeof it !== "object") { delete db.items[k]; continue; }
    if (it.seen && typeof it.seen === "object") {
      for (const vk of Object.keys(it.seen)) {
        if (it.seen[vk] !== today) delete it.seen[vk];
      }
    } else it.seen = {};
    if (!(it.count > 0) && !Object.keys(it.seen).length) delete db.items[k];
  }
  return db;
}
function mediaViewCount(db, itemKey) {
  const it = db.items[itemKey];
  return it && typeof it.count === "number" && it.count > 0 ? Math.floor(it.count) : 0;
}
// Record one view. Returns { views, counted } — counted is false when
// this viewer already counted for this item today (dedupe), in which
// case the store is not rewritten at all.
function recordMediaView(db, itemKey, viewerKey, today) {
  let it = db.items[itemKey];
  if (!it || typeof it !== "object") it = db.items[itemKey] = { count: 0, seen: {} };
  if (!it.seen || typeof it.seen !== "object") it.seen = {};
  if (it.seen[viewerKey] === today) return { views: mediaViewCount(db, itemKey), counted: false };
  it.seen[viewerKey] = today;
  it.count = (typeof it.count === "number" && it.count > 0 ? Math.floor(it.count) : 0) + 1;
  pruneViews(db, today);
  return { views: it.count, counted: true };
}
function photoViewsFor(owner) {
  const out = {};
  const vdb = readViews();
  for (const url of accountPhotos(owner)) out[url] = mediaViewCount(vdb, "photo:" + owner.id + ":" + url);
  return out;
}
function viewDeviceKey(v) {
  const s = String(v || "").trim();
  return /^[A-Za-z0-9_-]{8,80}$/.test(s) ? s : null;
}
app.post("/api/media/view", (req, res) => {
  const b = req.body || {};
  const kind = String(b.kind || "");
  if (kind !== "reel" && kind !== "photo")
    return res.status(400).json({ ok: false, error: "kind must be \"reel\" or \"photo\"" });
  // Viewer identity: account token wins; else the device key.
  const adb = readAccounts();
  const viewer = accountForToken(adb, req);
  let viewerKey = null;
  if (viewer) viewerKey = "acct:" + viewer.id;
  else {
    const dk = viewDeviceKey(b.deviceKey || req.headers["x-device-key"]);
    if (dk) viewerKey = "dev:" + dk;
  }
  if (!viewerKey)
    return res.status(400).json({ ok: false, error: "Missing viewer identity" });
  let itemKey = null;
  if (kind === "reel") {
    const reelId = reelCleanId(b.id);
    if (!reelId) return res.status(400).json({ ok: false, error: "Missing reel id" });
    const reel = listReels().find((r) => r.id === reelId);
    if (!reel) return res.status(404).json({ ok: false, error: "Reel not found" });
    itemKey = "reel:" + reelId;
  } else {
    const ownerId = String(b.owner || "").trim();
    const url = String(b.id || "").trim().slice(0, 600);
    if (!ownerId || !url)
      return res.status(400).json({ ok: false, error: "Missing photo owner or url" });
    const owner = adb.users.find((u) => u.id === ownerId);
    if (!owner) return res.status(404).json({ ok: false, error: "Account not found" });
    if (!accountPhotos(owner).includes(url))
      return res.status(404).json({ ok: false, error: "Photo not found" });
    itemKey = "photo:" + ownerId + ":" + url;
  }
  const db = readViews();
  const out = recordMediaView(db, itemKey, viewerKey, viewDayKey());
  if (out.counted) writeViews(db);
  res.json({ ok: true, views: out.views, counted: out.counted });
});

// ---------------------------------------------------------------------------
// [RP-V7.65] Media search — Branden (Oct 25): the Facebook screenshot
// he circled was the video SEARCH results grid ("This was for
// searching for videos"). GET /api/media/search?q=<text> searches
// VIDEOS (reels) and PICTURES (members' gallery photos) Plaza-wide:
//   - a reel matches when its caption, its author's display name, or
//     its author's username contains the query (case-insensitive);
//   - a photo matches when its OWNER's name or username contains the
//     query (photos carry no captions — the owner is the honest key).
//     Only photos of visible accounts ride along: pending-deletion
//     accounts (deletionAt set) are excluded, and fully deleted
//     accounts are gone from the store entirely — the same
//     visibility line the directory and /api/social/profile draw.
//   - a blank query returns the DISCOVERY set: the most-viewed reels
//     and photos (view count desc, newest first on ties), capped at
//     24 per kind — what the search screen shows before anyone types.
//   - query results are capped at 48 per kind, same order.
// Reel entries are the exact public shape GET /api/reels returns
// (guests included), counts read from the same views.json — and
// searching NEVER counts as a view: only opening/playing an item
// pings POST /api/media/view, exactly as RP-V7.64 built it. Like
// GET /api/reels, reading public media needs no token and applies
// no extra filtering (the 18+ gate lives at screen entry, the same
// place /api/reels relies on it).
// ---------------------------------------------------------------------------
function mediaSearchReelItem(r, all, vdb) {
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
    views: mediaViewCount(vdb, "reel:" + r.id),
    reactions: rxSummarize(r.reactions, null).counts,
  };
}
app.get("/api/media/search", (req, res) => {
  const q = String(req.query.q || "").trim().toLowerCase().slice(0, 80);
  const vdb = readViews();
  const adb = readAccounts();
  const byId = new Map();
  const byName = new Map();
  for (const u of adb.users) {
    if (!u) continue;
    byId.set(u.id, u);
    const nk = String(u.name || "").toLowerCase();
    if (nk && !byName.has(nk)) byName.set(nk, u);
  }
  const allReels = listReels().filter((r) => r && r.id);
  const reelHit = (r) => {
    if (!q) return true;
    if (String(r.caption || "").toLowerCase().includes(q)) return true;
    if (String(r.author || "").toLowerCase().includes(q)) return true;
    let acct = r.authorId ? byId.get(r.authorId) : null;
    if (!acct && r.author) acct = byName.get(String(r.author).toLowerCase()) || null;
    return !!(
      acct &&
      acct.username &&
      String(acct.username).toLowerCase().includes(q)
    );
  };
  const byViewsThenNew = (a, b) =>
    b.views - a.views ||
    String(b.createdAt || "").localeCompare(String(a.createdAt || ""));
  const reels = allReels
    .filter(reelHit)
    .map((r) => mediaSearchReelItem(r, allReels, vdb))
    .sort(byViewsThenNew)
    .slice(0, q ? 48 : 24);
  const photos = [];
  for (const u of adb.users) {
    if (!u || u.deletionAt) continue; // pending deletion = invisible
    if (
      q &&
      !String(u.name || "").toLowerCase().includes(q) &&
      !String(u.username || "").toLowerCase().includes(q)
    )
      continue;
    for (const url of accountPhotos(u)) {
      photos.push({
        ownerId: u.id,
        ownerName: u.name,
        ownerUsername: u.username || "",
        url,
        views: mediaViewCount(vdb, "photo:" + u.id + ":" + url),
      });
    }
  }
  photos.sort((a, b) => b.views - a.views);
  res.json({ ok: true, q, reels, photos: photos.slice(0, q ? 48 : 24) });
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
  // [RP-V7.89] the live's room/theme is a style too — the client sends
  // roomKey when it knows it; absent, no style learning from this event.
  if (typeof b.roomKey === "string" && b.roomKey)
    fyBumpStyleKeys(urec, styleKeysForText(b.roomKey.slice(0, 60)), delta, now);
  urec.liveSigAt[host.id] = now;
  writeReelSignals(sig);
  res.json({ ok: true, counted: true });
});

// ---------------------------------------------------------------------------
// RP-V7.41: Plaza Pot — a host-seeded charm pot inside a live.
// LEGAL SHAPE (settled with the owner; do not soften): NO buy-ins,
// ever. Nobody stakes anything to enter — entry is a free tap by any
// signed-in member. [RP-V7.75] Under-18 members included: the pot is
// charms end to end, and a teen's whole economy is charms-only, so
// teen hosts may seed/top up/draw/cancel and teen members may enter
// (Branden's teen model, Oct 26, 2026). The pot is promo charms only: the HOST seeds
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
// [RP-V7.75] THE TEEN BUILD constants (Branden, Oct 26, 2026 — he
// picked "Both — daily drop and boosted winnings" for how under-18
// members earn "thousands more" charms than adults): every under-18
// account claims TEEN_DAILY_DROP charms once per America/New_York
// day, and every Plaza Pot / Daily Pot win by an under-18 account
// gets TEEN_WIN_BOOST extra charms on top of the split — platform-
// funded, never taken from the pot or the other winners. Both land
// in the teen's main balance AND mirror into their gift balance
// (giftBalMirrorWin), because winning is what fuels teen gifting.
const TEEN_DAILY_DROP = 2500;
const TEEN_WIN_BOOST = 2500;
const POT_MATCH_PCT = 10; // platform growth match, % of gift charm value
const POT_WINNER_COUNT = 5;
// [RP-V7.54] Winner eligibility (Branden's rule, Oct 25): to RECEIVE
// pot winnings an entrant must (a) FOLLOW the host and (b) have been
// in the live at least 30 minutes. Entry itself stays free and open
// to every signed-in member — eligibility is judged at draw time,
// and the draw over the QUALIFIED pool stays uniform crypto-random.
// Watch time accrues server-side from socket presence (the verified
// acct-presence account binding) while a pot is open; in-memory only,
// like the lives themselves. Env-tunable for tests; production 30 min.
const POT_WIN_MIN_WATCH_MS = process.env.POT_WIN_MIN_WATCH_MS !== undefined && Number.isFinite(Number(process.env.POT_WIN_MIN_WATCH_MS)) ? Math.max(0, Number(process.env.POT_WIN_MIN_WATCH_MS)) : 30 * 60 * 1000;
const POT_WATCH_TICK_MS = Math.max(250, Number(process.env.POT_WATCH_TICK_MS) || 15000);
const potWatch = new Map(); // live key -> Map(accountId -> ms accrued in the live's room)
function accountAgeClass(user) {
  return user && ageFromDob(user.dob) < 18 ? "teen" : "adult";
}
function accountAgeClassById(accountId, adb) {
  try {
    const db = adb || readAccounts();
    return accountAgeClass(db.users.find((u) => u.id === accountId));
  } catch (e) {
    return "adult";
  }
}
function potClassForRecord(pot, adb) {
  if (pot && (pot.potClass === "teen" || pot.potClass === "adult"))
    return pot.potClass;
  // [RP-V7.77] Legacy live pots predate age classes. Branden's
  // migration rule is adult unless the host account's DOB proves the
  // host was in the teen class.
  return pot ? accountAgeClassById(pot.hostAccountId, adb) : "adult";
}
function potWrongClassError(potClass) {
  return potClass === "teen"
    ? "This is the teen pot — teens only"
    : "This is the adults' pot";
}
function readPots() {
  // [RP-V7.52] hardened read (audit H11): a corrupt pots.json
  // restores from .bak instead of forgetting escrowed pots.
  const db = storeReadJson(
    POTS_FILE,
    (d) => !!(d && d.pots && typeof d.pots === "object" && !Array.isArray(d.pots)),
    { pots: {} },
    "pots"
  );
  // [RP-V7.77] Normalize every record to its host's age class in
  // memory; boot migration persists the field, and every later write
  // carries it too. This makes a legacy record adult by default,
  // exactly as the migration rule requires.
  let adb = null;
  for (const pot of Object.values(db.pots || {})) {
    if (!pot || typeof pot !== "object") continue;
    if (pot.potClass !== "teen" && pot.potClass !== "adult") {
      if (!adb) {
        try { adb = readAccounts(); } catch (e) { adb = { users: [] }; }
      }
      pot.potClass = potClassForRecord(pot, adb);
    }
  }
  return db;
}
function writePots(db) {
  storeWriteJson(POTS_FILE, db);
}
function potTotal(pot) {
  return (pot.seed || 0) + (pot.match || 0);
}
function potPublic(pot, viewerId) {
  if (!pot) return null;
  return {
    key: pot.key,
    room: pot.room,
    potClass: potClassForRecord(pot),
    status: pot.status,
    total: potTotal(pot),
    seed: pot.seed || 0,
    match: pot.match || 0,
    entries: Array.isArray(pot.entries) ? pot.entries.length : 0,
    qualified: pot.status === "drawn" ? (pot.qualifiedCount != null ? pot.qualifiedCount : null) : null, // [RP-V7.54] entrants who met the win rules at the draw
    burstAt: pot.burstAt || null, // [RP-V7.41] optional burst target
    winners: pot.status === "drawn" ? pot.winners || [] : [],
    reason: pot.status === "drawn" ? pot.drawReason || null : null,
    drawnAt: pot.drawnAt || null,
    createdAt: pot.createdAt || null,
    joined: viewerId ? (pot.entries || []).indexOf(viewerId) >= 0 : false,
    isHost: viewerId ? pot.hostAccountId === viewerId : false,
  };
}
// [RP-V7.49] A terminal pot record belongs to the live that created
// it. The store is keyed by device key, so when the host's NEXT live
// registers later than the pot was created, the drawn/cancelled
// record is history — state and snapshot consumers must see "no pot"
// for the new live, or the dead record masks it and the host can
// never seed again (the sheet only offers the form when no pot comes
// back). Open pots are never stale: every registry-removal path
// settles them (potLiveEnded) before a new live can register.
function potStaleForLive(pot, liveStartedAt) {
  if (!pot || pot.status === "open") return false;
  if (!liveStartedAt) return false;
  const created = Date.parse(pot.createdAt || "");
  return isFinite(created) && created < liveStartedAt;
}
function potSnapshotFrom(potsDb, key, liveStartedAt) {
  const pot = potsDb && potsDb.pots ? potsDb.pots[key] : null;
  if (!pot) return null;
  if (pot.status !== "open" && potStaleForLive(pot, liveStartedAt))
    return null; // [RP-V7.49] a previous live's settled pot is not this live's pot
  if (pot.status === "open")
    return {
      status: "open",
      potClass: potClassForRecord(pot),
      total: potTotal(pot),
      seed: pot.seed || 0, // [RP-V7.41] the chip's swell mapping needs the seed
      match: pot.match || 0, // [RP-V7.41] the chip floats "+N 🪙" on match growth
      entries: (pot.entries || []).length,
      burstAt: pot.burstAt || null, // [RP-V7.41] cards + chip show burst progress
    };
  if (pot.status === "drawn")
    return {
      status: "drawn",
      potClass: potClassForRecord(pot),
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
// livesSnapshot does: ONLY from the host socket's token-verified
// acct-presence binding. [RP-V7.52] The unique-display-name fallback
// was removed (audit C4) — pot host authorization keys off this, and
// a claimable name must never authorize a pot. Null when the host
// socket has not verified: pot hosting needs a proven account.
function liveHostAccountId(entry) {
  if (!entry) return null;
  const byKey = new Map();
  for (const [sid, k] of clientKeys) byKey.set(k, sid);
  const sid = byKey.get(entry.key) || null;
  if (sid) {
    const hs = io.sockets.sockets.get(sid);
    if (hs && hs.data && hs.data.accountId) return hs.data.accountId;
  }
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
// [RP-V7.54] Watch-time accrual for winner eligibility: every tick,
// each OPEN pot credits the tick to every account-verified socket
// currently sitting in its live's room. A pot frozen at its burst
// target re-checks here too, so it bursts the moment the first
// entrant crosses 30 minutes — no new gift needed.
setInterval(() => {
  try {
    const db = readPots();
    const openKeys = new Set();
    for (const k of Object.keys(db.pots)) {
      const pot = db.pots[k];
      if (!pot || pot.status !== "open") continue;
      openKeys.add(k);
      let watch = potWatch.get(k);
      if (!watch) { watch = new Map(); potWatch.set(k, watch); }
      for (const [sid, p] of players) {
        if (!p || p.room !== pot.room) continue;
        const s = io.sockets.sockets.get(sid);
        const acctId = s && s.data && s.data.accountId;
        if (acctId) watch.set(acctId, (watch.get(acctId) || 0) + POT_WATCH_TICK_MS);
      }
      if (pot.burstAt && potTotal(pot) >= pot.burstAt && (pot.entries || []).length >= 1)
        potAfterChange(db, pot);
    }
    for (const k of Array.from(potWatch.keys()))
      if (!openKeys.has(k)) potWatch.delete(k);
  } catch (e) {}
}, POT_WATCH_TICK_MS);
// The draw itself: pick distinct winners uniformly at random
// (crypto Fisher-Yates over the entrant list), credit each winner
// floor(total / winnerCount) charms through the money ledger, return
// the split remainder to the host, and stamp the record drawn.
// Money conservation: seed was debited from the host at open/topup;
// payouts + remainder == seed + match exactly (the match is the only
// platform-created part, and only ever leaves as winner payouts or
// the remainder share of it — never on cancel, where it evaporates).
function potRunDraw(pot, pool) {
  // [RP-V7.54] The pool is the QUALIFIED entrants (follow + 30-min
  // watch — filtered in potFinishDraw); the pick over the pool is the
  // same uniform crypto shuffle as always.
  const entrants = (pool || pot.entries || []).slice();
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
    // [RP-V7.75] Boosted teen winnings: an under-18 winner gets
    // TEEN_WIN_BOOST on top of the split. The boost is platform-
    // funded — share/remainder math over the pot itself is exact
    // and untouched, so no other winner loses a charm to it.
    // [RP-V7.77] The boost belongs to the TEEN pot world only: a
    // legacy teen entrant in an adult-class pot does not receive it.
    const boost =
      potClassForRecord(pot) === "teen" && u && ageFromDob(u.dob) < 18
        ? TEEN_WIN_BOOST
        : 0;
    return {
      id,
      name: (u && u.name) || (pot.entryNames && pot.entryNames[id]) || "Winner",
      amount: share + boost,
      ...(boost ? { boost } : {}),
    };
  });
  const mdb = readMoney();
  for (const w of winners) {
    mdb.balances[w.id] = (mdb.balances[w.id] || 0) + w.amount;
    moneyTx(mdb, {
      type: "pot-win", from: null, to: w.id, charms: w.amount,
      cents: 0, cut: 0, ref: pot.key,
    });
    // [RP-V7.74] A teen winner's prize also fills their gift balance.
    // [RP-V7.75] w.amount already includes the teen win boost, so the
    // gift balance mirrors the FULL credited amount (split + boost).
    giftBalMirrorWin(mdb, adb.users.find((x) => x.id === w.id), w.amount);
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
  pot.qualifiedCount = entrants.length; // [RP-V7.54] the qualified pool size at this draw
  pot.status = "drawn";
  pot.winners = winners;
  pot.drawnAt = new Date().toISOString();
  return { winners, share, remainder };
}
// [RP-V7.54] The qualified pool for a draw: entrants who FOLLOW the
// host AND have at least POT_WIN_MIN_WATCH_MS of in-room presence
// accrued while the pot was open. Everyone else entered for free but
// cannot receive winnings — the rule the sheet states up front.
function potEligibleEntries(pot) {
  const entries = pot.entries || [];
  if (!entries.length) return [];
  const sdb = readSocial();
  const watch = potWatch.get(pot.key);
  return entries.filter((id) => {
    if (id === pot.hostAccountId) return false;
    const watched = watch ? watch.get(id) || 0 : 0;
    if (watched < POT_WIN_MIN_WATCH_MS) return false;
    return socialFollowingIds(sdb, id).indexOf(pot.hostAccountId) >= 0;
  });
}
function potFinishDraw(potsDb, pot, reason) {
  // [RP-V7.54] No qualified entrants -> NO draw and no side effects
  // (returns null): callers decide what that means — a burst/host
  // draw leaves the pot open; a live-end refunds the seed instead.
  const pool = potEligibleEntries(pot);
  if (!pool.length) return null;
  const out = potRunDraw(pot, pool);
  pot.drawReason = reason || "host"; // [RP-V7.41] recorded + broadcast: "burst" | "host" | "live-end"
  writePots(potsDb);
  try {
    io.to(pot.room).emit("pot-drawn", {
      key: pot.key,
      room: pot.room,
      reason: reason || "host",
      total: potTotal(pot),
      entries: (pot.entries || []).length,
      qualified: pool.length, // [RP-V7.54]
      winners: out.winners,
      pot: potPublic(pot, null),
    });
  } catch (e) {}
  potWatch.delete(pot.key); // [RP-V7.54] the pot is settled — its watch clocks are done
  // [RP-V7.54] Announce the winners in the live's chat (Branden:
  // "announce the winners on the screen") — rides the potShout
  // system-line path into the comments everyone is watching, on top
  // of the burst show's winners overlay.
  potShout(
    pot,
    "🏆 Plaza Pot winners: " +
      out.winners.map((w) => w.name + " — " + w.amount + " charms").join(" · ") +
      " 🎉"
  );
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
  potWatch.delete(pot.key); // [RP-V7.54] settled — drop its watch clocks
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
    if ((pot.entries || []).length >= 1) {
      // [RP-V7.54] Entrants who never qualified (follow + 30 min)
      // can't be paid — the draw returns null and the seed goes home
      // exactly like a no-entrant pot.
      if (!potFinishDraw(db, pot, "live-end")) potRefundSeed(db, pot, "cancelled");
    } else potRefundSeed(db, pot, "cancelled");
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
        if ((pot.entries || []).length >= 1) { if (!potFinishDraw(db, pot, "live-end")) potRefundSeed(db, pot, "cancelled"); } // the live no longer exists — same settle rule, same reason set; [RP-V7.54] unqualified entrants -> seed refunds
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
app.post("/api/pot/open", lockedHandler("pot-open", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  if (isPendingDeletion(ctx.user))
    return res
      .status(403)
      .json({ ok: false, error: "This account is scheduled for deletion" });
  // [RP-V7.75] No age gate here anymore: the pot escrows CHARMS
  // only, and under Branden's teen model a teen host seeds their own
  // live's pot with charms exactly like an adult (the V7.74 18+
  // block on this route is reversed — money doors stay locked, the
  // charms-only pot is not a money door).
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
    potClass: accountAgeClass(ctx.user), // [RP-V7.77] a live pot is classed by its HOST, permanently at open
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
}));
app.post("/api/pot/topup", lockedHandler("pot-topup", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  if (isPendingDeletion(ctx.user))
    return res
      .status(403)
      .json({ ok: false, error: "This account is scheduled for deletion" });
  // [RP-V7.75] Charms-only escrow — teen hosts top up too (see /api/pot/open).
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
}));
app.post("/api/pot/join", lockedHandler("pot-join", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return; // 401 "Not signed in" — guests must sign in to enter
  if (isPendingDeletion(ctx.user))
    return res
      .status(403)
      .json({ ok: false, error: "This account is scheduled for deletion" });
  // [RP-V7.75] Pot ENTRY is open to signed-in under-18 accounts —
  // free, charms-only, winner eligibility (follow + 30 min) unchanged.
  const liveKey = String((req.body || {}).live || "");
  const db = readPots();
  const pot = db.pots[liveKey];
  if (!pot || pot.status !== "open")
    return res.status(404).json({ ok: false, error: "No open pot in this live" });
  if (pot.hostAccountId === ctx.user.id)
    return res
      .status(400)
      .json({ ok: false, error: "You can't enter your own pot" });
  // [RP-V7.77] Live-pot entry is locked to the pot's HOST class.
  // The pot remains visible across classes; only entry is refused.
  const viewerPotClass = accountAgeClass(ctx.user);
  const thisPotClass = potClassForRecord(pot);
  if (viewerPotClass !== thisPotClass)
    return res.status(403).json({
      ok: false,
      error: potWrongClassError(thisPotClass),
      potClass: thisPotClass,
    });
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
}));
app.post("/api/pot/draw", lockedHandler("pot-draw", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  // [RP-V7.75] Drawing pays out escrowed CHARMS — a teen host draws
  // their own pot too (see /api/pot/open).
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
  if (!out)
    return res.status(409).json({
      ok: false,
      error: "Nobody qualifies yet — winners must follow you and be in your live at least 30 minutes",
    });
  res.json({
    ok: true,
    pot: potPublic(pot, ctx.user.id),
    winners: out.winners,
    share: out.share,
    remainder: out.remainder,
  });
}));
app.post("/api/pot/cancel", lockedHandler("pot-cancel", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  // [RP-V7.75] Cancelling refunds the escrowed seed in charms — teen
  // hosts cancel their own pots too (see /api/pot/open).
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
}));
app.get("/api/pot/state", (req, res) => {
  const liveKey = String(req.query.live || "");
  let viewerId = null;
  try {
    const u = accountForToken(readAccounts(), req);
    if (u) viewerId = u.id;
  } catch (e) {}
  let pot = readPots().pots[liveKey] || null;
  // [RP-V7.49] Scope the record to the CURRENT live: a terminal pot
  // left over from a previous live on this device key is history —
  // report no pot so the host's sheet offers the seed form again.
  if (pot && pot.status !== "open") {
    const entry = liveRegistry.get(liveKey);
    if (entry && potStaleForLive(pot, entry.startedAt)) pot = null;
  }
  res.json({ ok: true, pot: potPublic(pot, viewerId) });
});

// ---------------------------------------------------------------------------
// [RP-V7.42] THE DAILY POT — sibling of the per-live Plaza Pot.
// [RP-V7.77] POT SEPARATION (Branden, Oct 26, 2026: "Don't mix up
// the adult daily and live pot with teen daily and live pot they
// both have different pots"): there are now TWO Daily Pots — an
// ADULT Daily Pot and a TEEN Daily Pot — fully independent in
// state, entries, tier track, caps, streaks, recaps, milestones and
// remainder rolls. A member only ever sees or enters their own
// class's pot. Each pot gathers from its own class and takes from
// no member:
//   - the PLAZA seeds each class's day from THAT class's tier
//     (platform promo accounting — no member debited);
//   - every gift grows the SENDER's class Daily Pot by a platform
//     match of 2% of the gift's charm value (floored, min 0),
//     capped at that pool's own cap. The gift itself, its 70/30
//     split and any live-pot match are untouched — a single gift
//     can feed a live pot (10%) and its class Daily Pot (2%) at once.
// Entry is a FREE tap, once per account per day, signed-in members
// in their own class only. Teen winners in the TEEN pot get the
// TEEN_WIN_BOOST on top; adult winners never do.
// Lifecycle (America/New_York, via Intl — never server-local time):
// the day opens at 00:00 ET seeded; at its own SECRET drawn
// moment inside 19:00-21:00 ET the pot BURSTS —
// 1 to 5 winners (the count itself is drawn at random each night,
// RP-V7.66; fewer entrants = all win) split the total evenly through
// the money ledger (tx "dailypot-win"), picked uniformly at random
// over the ENTRY LIST ONLY — the same draw discipline as potRunDraw;
// nothing from the interest system ever feeds this draw. The split
// remainder is NOT paid out and does NOT vanish: it is stamped
// rolledOut and folds into TOMORROW's pot IN THE SAME CLASS. With
// ZERO entries at its drawn moment there is no burst at all and the ENTIRE
// total rolls into that class's tomorrow (rollover + fresh seed +
// its own growth).
// After a burst, the evening shows the winners; at 00:00 ET the next
// day's pot opens. State lives in dailypot.json beside the other
// stores, so a restart mid-day loses nothing; a scheduler tick
// (boot + every 60s, plus a settle check inside dpEnsureToday)
// opens days and fires each settlement at its drawn moment.
// Store: { pots: { adult: Record, teen: Record } }. Record:
// { potClass, date, seed, rolledIn, match, milestonesHit: [thresholds
//   already shouted — RP-V7.43], entries: [accountId],
//   entryNames: { id: name }, status: "open"|"burst"|"noburst",
//   winners: [{ id, name, amount }], burstAt: <ms epoch, SECRET drawn
//   moment in 19:00-21:00 ET — server record only, never public pre-burst>,
//   burstDoneAt, rolledOut }
// ---------------------------------------------------------------------------
const DAILYPOT_FILE =
  process.env.DAILYPOT_FILE || path.join(path.dirname(PHOTO_DIR), "dailypot.json");
// [RP-V7.43] Daily-return engine stores: entry streaks per account and
// the last-7-days recap history, beside dailypot.json.
const DAILYPOT_STREAKS_FILE =
  process.env.DAILYPOT_STREAKS_FILE ||
  path.join(path.dirname(PHOTO_DIR), "dailypot-streaks.json");
const DAILYPOT_HISTORY_FILE =
  process.env.DAILYPOT_HISTORY_FILE ||
  path.join(path.dirname(PHOTO_DIR), "dailypot-history.json");
// [RP-V7.43] Milestone shouts: the day's total crossing one of these
// (via gift growth, or rollover-in the moment the day opens) broadcasts
// dailypot-milestone exactly once per threshold per day.
const DAILY_POT_MILESTONES = [2500, 5000, 10000, 25000, 50000, 100000];
const DAILY_POT_SEED = 1000;
const DAILY_POT_MATCH_PCT = 2; // platform growth match, % of ANY gift's charm value
const DAILY_POT_MATCH_CAP = 10000;
const DAILY_POT_MAX_WINNERS = 5; // [RP-V7.66] the nightly winner COUNT is drawn at random, 1..this (Branden, Oct 26)
const DAILY_POT_TZ = "America/New_York";
const DAILY_POT_BURST_WINDOW_START_HOUR = 19; // 7:00 PM ET
const DAILY_POT_BURST_WINDOW_MS = 2 * 60 * 60 * 1000; // secret moment in [19:00, 21:00) ET
const DAILY_POT_BURST_COPY = "Bursts tonight between 7 and 9 PM ET — be here!";
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
// [RP-V7.77] BE-THERE RULE (Branden, Oct 26, 2026: "Add a be-there
// rule to the Daily Pots too" — mirroring the live Plaza Pot's
// winner rule, but Plaza-wide, in his words: winners must have
// "been in the plaza for at least 30 minutes" that ET day).
// In-Plaza presence accrues server-side per ACCOUNT per ET day
// (dp-presence.json — the brain rule: it survives device switches
// and reconnects, and time across sessions sums). It is a SEPARATE
// counter from the live pot's in-a-specific-live watch time
// (potWatch): being in a live also counts toward in-Plaza time
// (that socket is in the Plaza), never the other way around.
const DP_WIN_MIN_PRESENCE_MS = process.env.DP_WIN_MIN_PRESENCE_MS !== undefined && Number.isFinite(Number(process.env.DP_WIN_MIN_PRESENCE_MS)) ? Math.max(0, Number(process.env.DP_WIN_MIN_PRESENCE_MS)) : 30 * 60 * 1000;
const DP_PRESENCE_FILE =
  process.env.DP_PRESENCE_FILE || path.join(path.dirname(PHOTO_DIR), "dp-presence.json");
const DAILY_POT_SEED_OVERRIDE = (() => {
  const n = parseInt(process.env.DAILY_POT_SEED_OVERRIDE || "0", 10);
  return Number.isFinite(n) && n > 0 ? n : 0;
})();
function normalizeDailyPotDb(raw) {
  const pots = { adult: null, teen: null };
  const take = (value, potClass) => {
    if (!value || typeof value !== "object" || Array.isArray(value)) return null;
    const rec = { ...value, potClass };
    if (!Array.isArray(rec.entries)) rec.entries = [];
    if (!rec.entryNames || typeof rec.entryNames !== "object") rec.entryNames = {};
    return rec;
  };
  if (raw && raw.pots && typeof raw.pots === "object" && !Array.isArray(raw.pots)) {
    pots.adult = take(raw.pots.adult, "adult");
    pots.teen = take(raw.pots.teen, "teen");
  } else if (raw && "rec" in raw) {
    // [RP-V7.77] MIGRATION: the pre-split store held ONE pot and its
    // entry gate admitted adults only. The whole record — total,
    // entries and burst state — therefore belongs to the ADULT pot.
    // The teen pot starts unset here and dpEnsureClass seeds it
    // fresh from the teen class's own tier.
    pots.adult = take(raw.rec, "adult");
  }
  return { splitVersion: 1, pots };
}
function readDailyPot() {
  // [RP-V7.52] hardened read (audit C5 family): a corrupt
  // dailypot.json restores from .bak instead of resetting the day.
  const raw = storeReadJson(
    DAILYPOT_FILE,
    (d) =>
      !!(
        d &&
        (("rec" in d &&
          (d.rec === null ||
            (d.rec && typeof d.rec === "object" && !Array.isArray(d.rec)))) ||
          (d.pots &&
            typeof d.pots === "object" &&
            !Array.isArray(d.pots)))
      ),
    { pots: { adult: null, teen: null } },
    "dailypot"
  );
  return normalizeDailyPotDb(raw);
}
function writeDailyPot(db) {
  storeWriteJson(DAILYPOT_FILE, normalizeDailyPotDb(db));
}
// ---------------------------------------------------------------------------
// [RP-V7.43] DAILY-RETURN ENGINE — habit mechanics around the Daily
// Pot: entry streaks, a yesterday recap, and milestone shouts. These
// are READ-ONLY garnish around the draw: the burst in dpRunBurst reads
// the ENTRY LIST ONLY and never touches streaks, history or milestones,
// so a long streak (or a big recap) moves nobody's odds by a hair.
// ---------------------------------------------------------------------------
function normalizeDpStreaks(raw) {
  const out = { classes: { adult: { users: {} }, teen: { users: {} } } };
  const takeUsers = (value) =>
    value && typeof value === "object" && !Array.isArray(value) ? value : {};
  if (raw && raw.classes && typeof raw.classes === "object") {
    out.classes.adult.users = takeUsers(raw.classes.adult && raw.classes.adult.users);
    out.classes.teen.users = takeUsers(raw.classes.teen && raw.classes.teen.users);
  }
  // [RP-V7.77] Legacy streaks belonged to the adult-only Daily Pot,
  // so the whole legacy users map migrates into the adult class.
  if (raw && raw.users && typeof raw.users === "object" && !Array.isArray(raw.users))
    out.classes.adult.users = { ...raw.users, ...out.classes.adult.users };
  return out;
}
function readDpStreaks() {
  try {
    return normalizeDpStreaks(
      JSON.parse(fs.readFileSync(DAILYPOT_STREAKS_FILE, "utf8"))
    );
  } catch (e) {}
  return normalizeDpStreaks(null);
}
function writeDpStreaks(db) {
  const tmp = DAILYPOT_STREAKS_FILE + ".tmp";
  fs.writeFileSync(tmp, JSON.stringify(normalizeDpStreaks(db), null, 2));
  fs.renameSync(tmp, DAILYPOT_STREAKS_FILE);
}
function dpClassOrDerived(userId, potClass) {
  if (potClass === "adult" || potClass === "teen") return potClass;
  return accountAgeClassById(userId);
}
function dpStreakBucket(db, potClass) {
  const normalized = normalizeDpStreaks(db);
  return normalized.classes[potClass].users;
}
// After a successful join on dateStr: yesterday -> streak+1; anything
// older (or a first-ever entry) -> streak 1. best = the all-time max.
function dpBumpStreak(userId, dateStr, potClass) {
  const db = readDpStreaks();
  const bucket = dpStreakBucket(db, dpClassOrDerived(userId, potClass));
  const cur = bucket[userId] || { lastDate: null, streak: 0, best: 0 };
  if (cur.lastDate === dateStr) return cur; // already counted today (the join route's dup-guard keeps this unreachable)
  cur.streak = cur.lastDate === dpDatePlus(dateStr, -1) ? (cur.streak || 0) + 1 : 1;
  cur.lastDate = dateStr;
  cur.best = Math.max(cur.best || 0, cur.streak);
  bucket[userId] = cur;
  // dpStreakBucket returns a bucket inside a normalized copy; write
  // that exact normalized shape back through its class container.
  const cls = dpClassOrDerived(userId, potClass);
  db.classes[cls].users = bucket;
  writeDpStreaks(db);
  return cur;
}
// The streak as the member should see it TODAY: entered today -> the
// streak; last entry yesterday -> still alive (at risk until they
// enter); anything older -> 0 (broken).
function dpStreakFor(userId, todayStr, potClass) {
  const db = readDpStreaks();
  const s = dpStreakBucket(db, dpClassOrDerived(userId, potClass))[userId];
  if (!s || !s.lastDate) return 0;
  if (s.lastDate === todayStr) return s.streak || 0;
  if (s.lastDate === dpDatePlus(todayStr, -1)) return s.streak || 0;
  return 0;
}
function normalizeDpHistory(raw) {
  const out = { adult: [], teen: [] };
  const take = (value) => (Array.isArray(value) ? value : []);
  if (Array.isArray(raw)) out.adult = take(raw);
  else if (raw && Array.isArray(raw.days)) out.adult = take(raw.days);
  else if (raw && typeof raw === "object") {
    out.adult = take(raw.adult);
    out.teen = take(raw.teen);
  }
  return out;
}
function readDpHistoryMap() {
  try {
    return normalizeDpHistory(
      JSON.parse(fs.readFileSync(DAILYPOT_HISTORY_FILE, "utf8"))
    );
  } catch (e) {}
  return normalizeDpHistory(null);
}
function readDpHistory(potClass) {
  const cls = potClass === "teen" ? "teen" : "adult";
  return readDpHistoryMap()[cls];
}
function writeDpHistoryMap(map) {
  const tmp = DAILYPOT_HISTORY_FILE + ".tmp";
  fs.writeFileSync(tmp, JSON.stringify(normalizeDpHistory(map), null, 2));
  fs.renameSync(tmp, DAILYPOT_HISTORY_FILE);
}
// Snapshot a finished day for the recap, newest first, last 7 kept.
// Deduped by date so a restart mid-roll can never double-record a day.
function dpPushHistory(rec) {
  if (!rec || !rec.date) return;
  const snap = {
    date: rec.date,
    total: dailyPotTotal(rec),
    status: rec.status,
    statusNote: rec.statusNote || null,
    winners: (rec.winners || []).map((w) => ({ name: w.name, amount: w.amount })),
    entriesCount: Array.isArray(rec.entries) ? rec.entries.length : 0,
  };
  const cls = rec.potClass === "teen" ? "teen" : "adult";
  const map = readDpHistoryMap();
  let hist = map[cls].filter((s) => s && s.date !== snap.date);
  hist.unshift({ ...snap, potClass: cls });
  hist.sort((a, b) => (a.date < b.date ? 1 : a.date > b.date ? -1 : 0)); // newest day first
  map[cls] = hist.slice(0, 7);
  writeDpHistoryMap(map);
}
function dpYesterdayRecap(todayStr, potClass) {
  const y = dpDatePlus(todayStr, -1);
  const hist = readDpHistory(potClass);
  for (const s of hist) if (s && s.date === y) return s;
  return null;
}
// Fire dailypot-milestone for every threshold the day's total has
// crossed that hasn't been shouted yet. The crossed set persists on
// the day record (milestonesHit), so restarts never re-shout.
function dpCheckMilestones(dateStr, potClass) {
  const cls = potClass === "teen" ? "teen" : "adult";
  const db = readDailyPot();
  const rec = db.pots[cls];
  if (!rec || rec.date !== dateStr) return;
  const total = dailyPotTotal(rec);
  if (!Array.isArray(rec.milestonesHit)) rec.milestonesHit = [];
  const crossed = DAILY_POT_MILESTONES.filter(
    (t) => total >= t && rec.milestonesHit.indexOf(t) < 0
  );
  if (!crossed.length) return;
  crossed.sort((a, b) => a - b);
  for (const t of crossed) rec.milestonesHit.push(t);
  writeDailyPot(db);
  for (const t of crossed) {
    try {
      io.emit("dailypot-milestone", { threshold: t, total, date: rec.date, potClass: cls });
    } catch (e) {}
    console.log("[dailypot] MILESTONE", rec.date, "crossed", t, "total", total);
  }
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
// [RP-V7.77] Each Daily Pot draws its OWN secret burst moment for
// the day, crypto-random over [19:00, 21:00) ET, when the day opens.
// It is persisted on the server record as burstAt and is NEVER put
// in a public payload while the pot is open ("give everyone a
// reason to be there" — Branden, Oct 26, 2026).
function dpDrawDailyBurstAt(dateStr) {
  return dpEtEpoch(dateStr, DAILY_POT_BURST_WINDOW_START_HOUR, 0) + crypto.randomInt(DAILY_POT_BURST_WINDOW_MS);
}
function dailyPotTotal(rec) {
  return (rec.seed || 0) + (rec.rolledIn || 0) + (rec.match || 0);
}
// ---------------------------------------------------------------------------
// [RP-V7.81] EVENT-NOW — the server-anchored holiday calendar for the
// gift-film resolver (Branden, Oct 26, 2026: during a holiday/event
// window the HD gift films "dress up" event-matched, automatically,
// and flip back after). The client HOLIDAYS framework detects windows
// in DEVICE-local time; film selection must not depend on the viewer's
// timezone, so the active event is computed HERE, anchored to
// America/New_York calendar days (the same Intl-only discipline as the
// Daily Pot), from the same 18-event table and the same window rules
// (the event day plus `pre` days before and `post` days after).
// The film files use their own slug vocabulary (the rizz-event-films
// production list), so each framework id maps to a film slug; events
// with no commissioned films (mlk, stpatricks, cinco, memorial,
// summer, laborday, veterans) map to null — the standard film plays.
// ---------------------------------------------------------------------------
const RP_EVENT_FILM_SLUGS = {
  newyear: "newyears", valentines: "valentines", easter: "easter",
  mothers: "mothersday", fathers: "fathersday", juneteenth: "juneteenth",
  july4: "july4", birthday: "plazabirthday", halloween: "halloween",
  thanksgiving: "thanksgiving", christmas: "christmas",
  mlk: null, stpatricks: null, cinco: null, memorial: null,
  summer: null, laborday: null, veterans: null,
};
// Calendar rules mirrored from the client's HOLIDAYS table (RP-V7.54):
// { mo, da } fixed date · { nth: [mo, weekday, n] } nth weekday of the
// month · { last: [mo, weekday] } last weekday of the month ·
// { easter: true } Easter Sunday (Gregorian computus).
const RP_EVENT_CALENDAR = [
  { id: "newyear", name: "New Year's Day", mo: 0, da: 1, pre: 3, post: 1 },
  { id: "mlk", name: "Martin Luther King Jr. Day", nth: [0, 1, 3], pre: 3, post: 1 },
  { id: "valentines", name: "Valentine's Day", mo: 1, da: 14, pre: 3, post: 1 },
  { id: "stpatricks", name: "St. Patrick's Day", mo: 2, da: 17, pre: 3, post: 1 },
  { id: "easter", name: "Easter", easter: true, pre: 3, post: 1 },
  { id: "cinco", name: "Cinco de Mayo", mo: 4, da: 5, pre: 3, post: 1 },
  { id: "mothers", name: "Mother's Day", nth: [4, 0, 2], pre: 3, post: 1 },
  { id: "memorial", name: "Memorial Day", last: [4, 1], pre: 3, post: 1 },
  { id: "juneteenth", name: "Juneteenth", mo: 5, da: 19, pre: 3, post: 0 },
  { id: "fathers", name: "Father's Day", nth: [5, 0, 3], pre: 3, post: 1 },
  { id: "july4", name: "Independence Day", mo: 6, da: 4, pre: 3, post: 1 },
  { id: "summer", name: "Summer Splash", mo: 7, da: 15, pre: 3, post: 2 },
  { id: "laborday", name: "Labor Day", nth: [8, 1, 1], pre: 3, post: 1 },
  { id: "birthday", name: "Plaza Birthday Bash", mo: 9, da: 18, pre: 3, post: 3 },
  { id: "halloween", name: "Halloween", mo: 9, da: 31, pre: 3, post: 1 },
  { id: "veterans", name: "Veterans Day", mo: 10, da: 11, pre: 3, post: 1 },
  { id: "thanksgiving", name: "Thanksgiving", nth: [10, 4, 4], pre: 3, post: 3 },
  { id: "christmas", name: "Christmas", mo: 11, da: 25, pre: 3, post: 1 },
];
function rpEasterMonthDay(y) {
  const a = y % 19, b = Math.floor(y / 100), c = y % 100, d = Math.floor(b / 4), e = b % 4,
    f = Math.floor((b + 8) / 25), g = Math.floor((b - f + 1) / 3), h = (19 * a + b - d - g + 15) % 30,
    i = Math.floor(c / 4), k = c % 4, l = (32 + 2 * e + 2 * i - h - k) % 7, m = Math.floor((a + 11 * h + 22 * l) / 451),
    mo = Math.floor((h + l - 7 * m + 114) / 31), da = ((h + l - 7 * m + 114) % 31) + 1;
  return { mo: mo - 1, da };
}
function rpEventDayNum(y, mo, da) { return Math.floor(Date.UTC(y, mo, da) / 86400000); }
function rpEventDateDayNum(h, y) {
  if (h.easter) { const ed = rpEasterMonthDay(y); return rpEventDayNum(y, ed.mo, ed.da); }
  if (h.nth) {
    const first = new Date(Date.UTC(y, h.nth[0], 1)).getUTCDay();
    const da = 1 + ((h.nth[1] - first + 7) % 7) + 7 * (h.nth[2] - 1);
    return rpEventDayNum(y, h.nth[0], da);
  }
  if (h.last) {
    const lastDay = new Date(Date.UTC(y, h.last[0] + 1, 0));
    const da = lastDay.getUTCDate() - ((lastDay.getUTCDay() - h.last[1] + 7) % 7);
    return rpEventDayNum(y, h.last[0], da);
  }
  return rpEventDayNum(y, h.mo, h.da);
}
// The event (if any) whose window contains TODAY in America/New_York.
// Returns { id, slug, name } — slug is the film slug or null.
function rpActiveEvent(nowMs) {
  const p = dpEtParts(nowMs == null ? Date.now() : nowMs);
  if (!p) return { id: null, slug: null, name: null };
  const today = rpEventDayNum(p.y, p.mo - 1, p.d);
  for (const yy of [p.y - 1, p.y, p.y + 1]) {
    for (const h of RP_EVENT_CALENDAR) {
      const d = rpEventDateDayNum(h, yy);
      if (today >= d - h.pre && today <= d + h.post)
        return { id: h.id, slug: RP_EVENT_FILM_SLUGS[h.id] || null, name: h.name };
    }
  }
  return { id: null, slug: null, name: null };
}
app.get("/api/event-now", (req, res) => {
  const ev = rpActiveEvent(Date.now());
  res.json({ ok: true, id: ev.id, slug: ev.slug, name: ev.name });
});
// ---------------------------------------------------------------------------
// [RP-V7.76] UNIFIED SERVER DAILY CLAIM (brain train batch 1, FIX-2) —
// ONE claim gate for the whole Plaza. Up to V7.75 the Plaza had two
// parallel daily faucets: the adult Daily Rewards ladder was gated
// per-DEVICE in the client (rpDailyClaim.v1 — claimable once per
// device per day, streak = whichever device you were holding), while
// the teen daily drop (V7.75) was already server-side on the account
// record (teenDailyDropDate). Both now run through the single claim
// system below: the gate + streak live in claims.json on the ACCOUNT
// (an America/New_York day), so one claim per account per ET day
// across ALL devices, and every device renders the same streak from
// the claim/state payloads. The claim TYPE is set by the account's
// age class, never by the request: under-18 = the teen drop (2,500
// main + 2,500 giftBal mirror, the V7.75 terms verbatim); 18+ = the
// Daily Rewards ladder (DAILY_CLAIM_LADDER — the exact amounts the
// client ladder has always paid: 10/15/20/25/30/40/60 by streak day).
// The endpoint stays kind-extensible: { kind: "daily-claim" |
// "teen-drop" } is accepted, an adult explicitly asking for the teen
// drop is refused 403, and either kind from a teen pays teen terms —
// it is the same single gate. The superseded parallel gate (the
// /api/teen/daily-drop route + the teenDailyDropDate account field)
// is retired: claimRecordFor still READS a same-day teenDailyDropDate
// as an already-made teen claim so a deploy-day claim can never
// double-pay, and nothing writes the field anymore.
// ---------------------------------------------------------------------------
const CLAIMS_FILE =
  process.env.CLAIMS_FILE || path.join(path.dirname(PHOTO_DIR), "claims.json");
const DAILY_CLAIM_LADDER = [10, 15, 20, 25, 30, 40, 60];
function readClaims() {
  try {
    const d = JSON.parse(fs.readFileSync(CLAIMS_FILE, "utf8"));
    if (d && d.users && typeof d.users === "object" && !Array.isArray(d.users))
      return d;
  } catch (e) {}
  return { users: {} };
}
function writeClaims(db) {
  const tmp = CLAIMS_FILE + ".tmp";
  fs.writeFileSync(tmp, JSON.stringify(db, null, 2));
  fs.renameSync(tmp, CLAIMS_FILE);
}
// The account's claim record: { lastDate, streak, best, lastKind }.
// Merges the claims store with the retired V7.75 field for read
// compat (see the block comment above).
function claimRecordFor(user, cdb) {
  const db = cdb || readClaims();
  const rec = db.users[user.id];
  if (rec && rec.lastDate)
    return {
      lastDate: rec.lastDate,
      streak: rec.streak || 0,
      best: rec.best || 0,
      lastKind: rec.lastKind || null,
    };
  if (user.teenDailyDropDate)
    return {
      lastDate: user.teenDailyDropDate,
      streak: 1,
      best: 1,
      lastKind: "teen-drop",
    };
  return { lastDate: null, streak: 0, best: 0, lastKind: null };
}
// The streak as the member should see it TODAY (same display rule
// as dpStreakFor): claimed today or last claimed yesterday -> the
// streak is alive; anything older -> 0 (broken).
function claimStreakShown(rec, today) {
  if (!rec || !rec.lastDate) return 0;
  if (rec.lastDate === today || rec.lastDate === dpDatePlus(today, -1))
    return rec.streak || 0;
  return 0;
}
// The claim state every payload carries (claim responses +
// /api/money/me): one shape, rendered identically on every device.
function claimStatePayload(user, cdb) {
  const today = dpDateStr(Date.now());
  const rec = claimRecordFor(user, cdb);
  const teen = ageFromDob(user.dob) < 18;
  const streak = claimStreakShown(rec, today);
  return {
    date: today,
    kind: teen ? "teen-drop" : "daily-claim",
    claimedToday: rec.lastDate === today,
    lastDate: rec.lastDate || null,
    streak,
    best: rec.best || 0,
    nextAmount: teen
      ? TEEN_DAILY_DROP
      : DAILY_CLAIM_LADDER[Math.min(streak, DAILY_CLAIM_LADDER.length - 1)],
  };
}
// [RP-V7.75] The teen daily-drop status for one viewer: eligible
// only for under-18 accounts; claimed is read from the unified
// server claim store (RP-V7.76 — claims.json, see above); the brain
// rule stands: account-persistent, never device-local.
function teenDropStatusFor(viewerId) {
  const base = { eligible: false, amount: TEEN_DAILY_DROP, claimed: false };
  if (!viewerId) return base;
  try {
    const u = readAccounts().users.find((x) => x.id === viewerId);
    if (!u || ageFromDob(u.dob) >= 18) return base;
    return {
      eligible: true,
      amount: TEEN_DAILY_DROP,
      claimed: claimRecordFor(u).lastDate === dpDateStr(Date.now()),
    };
  } catch (e) {
    return base;
  }
}
function readDpPresence() {
  try {
    const d = JSON.parse(fs.readFileSync(DP_PRESENCE_FILE, "utf8"));
    if (d && d.days && typeof d.days === "object" && !Array.isArray(d.days)) return d;
  } catch (e) {}
  return { days: {} };
}
function writeDpPresence(db) {
  const tmp = DP_PRESENCE_FILE + ".tmp";
  fs.writeFileSync(tmp, JSON.stringify(db, null, 2));
  fs.renameSync(tmp, DP_PRESENCE_FILE);
}
function dpPresenceMs(userId, dateStr) {
  if (!userId) return 0;
  const day = readDpPresence().days[dateStr || dpDateStr(Date.now())] || {};
  return Number(day[userId]) || 0;
}
function dpAccountPresent(userId) {
  // [RP-V7.77] The third be-there condition: the account holds a
  // live acct-presence socket RIGHT NOW (any device — the server's
  // view of "here", not any one screen's).
  if (!userId) return false;
  try {
    for (const [, sock] of io.sockets.sockets)
      if (sock && sock.data && sock.data.accountId === userId) return true;
  } catch (e) {}
  return false;
}
function dpPresencePayload(userId, dateStr) {
  if (!userId) return null;
  const ms = dpPresenceMs(userId, dateStr);
  const minutesQualified = ms >= DP_WIN_MIN_PRESENCE_MS;
  const presentNow = dpAccountPresent(userId);
  return {
    ms,
    minutes: Math.floor(ms / 60000),
    requiredMs: DP_WIN_MIN_PRESENCE_MS,
    requiredMinutes: Math.round(DP_WIN_MIN_PRESENCE_MS / 60000),
    minutesQualified,
    presentNow,
    // Full be-there qualification: 30+ minutes banked today AND
    // present in the Plaza at the burst moment.
    qualified: minutesQualified && presentNow,
  };
}
// Presence accrual: the same 15s tick discipline as the live pot's
// watch accrual — every tick credits each account with at least one
// verified acct-presence socket connected. One credit per account
// per tick no matter how many devices (presence is presence);
// sequential sessions across the day sum into the same counter.
setInterval(() => {
  try {
    const present = new Set();
    for (const [, sock] of io.sockets.sockets) {
      const acctId = sock && sock.data && sock.data.accountId;
      if (acctId) present.add(acctId);
    }
    if (!present.size) return;
    const today = dpDateStr(Date.now());
    const db = readDpPresence();
    if (!db.days[today]) db.days[today] = {};
    for (const id of present)
      db.days[today][id] = (Number(db.days[today][id]) || 0) + POT_WATCH_TICK_MS;
    // keep today + the last two ET days; older days are history
    const keep = new Set([today, dpDatePlus(today, -1), dpDatePlus(today, -2)]);
    for (const d of Object.keys(db.days)) if (!keep.has(d)) delete db.days[d];
    writeDpPresence(db);
  } catch (e) {}
}, POT_WATCH_TICK_MS);
function dailyPotPublic(rec, viewerId) {
  if (!rec) return null;
  // [RP-V7.77] SURPRISE DISCIPLINE for BOTH Daily Pots: while a pot
  // is open, its exact drawn burst moment and any countdown to it
  // stay server-side only. The public payload carries the window
  // copy instead. After settlement the moment is history.
  const secret = rec.status === "open";
  return {
    date: rec.date,
    potClass: rec.potClass === "teen" ? "teen" : "adult",
    status: rec.status,
    tier: rec.tier != null ? rec.tier : 1, // [RP-V7.42] the day's launch tier (0 = manual override)
    matchCap: rec.matchCap != null ? rec.matchCap : DAILY_POT_MATCH_CAP,
    total: dailyPotTotal(rec),
    seedPart: rec.seed || 0,
    rolledIn: rec.rolledIn || 0,
    matchPart: rec.match || 0,
    entriesCount: Array.isArray(rec.entries) ? rec.entries.length : 0,
    joined: viewerId ? (rec.entries || []).indexOf(viewerId) >= 0 : false,
    streak: viewerId ? dpStreakFor(viewerId, rec.date, rec.potClass) : null, // [RP-V7.43] the caller's entry streak, in their class (null for guests)
    presence: viewerId ? dpPresencePayload(viewerId, rec.date) : null, // [RP-V7.77] the caller's in-Plaza minutes today + be-there qualification
    winRule: "Winners must have been in the Plaza at least 30 minutes today AND be in the Plaza when it bursts — leave before it pops and the win goes to someone who's here.",
    statusNote: rec.statusNote || null, // [RP-V7.77] why a pot rolled instead of bursting, when it did
    teenDrop: viewerId ? teenDropStatusFor(viewerId) : null, // [RP-V7.75] the caller's teen daily-drop status (null for guests)
    yesterday: dpYesterdayRecap(rec.date, rec.potClass), // [RP-V7.43 + V7.77] yesterday's recap for THIS class only
    winners: rec.status === "burst" ? rec.winners || [] : [],
    burstAt: secret ? null : rec.burstAt || null,
    burstAtMasked: secret,
    burstWindow: { startHour: 19, endHour: 21, tz: DAILY_POT_TZ, label: DAILY_POT_BURST_COPY },
    burstCopy: DAILY_POT_BURST_COPY,
    nextBurstInSec: null,
  };
}
// [RP-V7.77] The side-by-side Home payload (Branden approved the
// mock, Oct 26): a signed-in member gets BOTH Daily Pots — their
// own class's pot in the existing `pot` shape (full viewer state),
// plus the other class's pot marked watch-only (public state only:
// no joined/streak/teenDrop for this viewer). Guests keep the
// historical single adult-pot view in `pot`; the pair rides along
// in `pots`/`otherPot` and the guest client renders only its own.
function dailyPotPairPayload(viewer) {
  const db = readDailyPot();
  const ownClass = viewer ? accountAgeClass(viewer) : "adult";
  const otherClass = ownClass === "teen" ? "adult" : "teen";
  const own = dailyPotPublic(db.pots[ownClass], viewer ? viewer.id : null);
  const other = dailyPotPublic(db.pots[otherClass], null);
  if (own) { own.own = true; own.enterable = !!viewer; own.watchOnly = !viewer; }
  if (other) { other.own = false; other.enterable = false; other.watchOnly = true; }
  const pots = {};
  pots[ownClass] = own;
  pots[otherClass] = other;
  return { pot: own, ownPot: own, otherPot: other, pots, ownClass, otherClass };
}
let dpLastGrowthBcastAt = 0;
// Plaza-wide state push. Growth ticks are throttled to ~15s; joins,
// bursts and day opens force an immediate push.
function dpBroadcastUpdate(force) {
  const now = Date.now();
  if (!force && now - dpLastGrowthBcastAt < 15000) return;
  dpLastGrowthBcastAt = now;
  try {
    const db = readDailyPot();
    const adult = dailyPotPublic(db.pots.adult, null);
    const teen = dailyPotPublic(db.pots.teen, null);
    // `pot` remains the adult pot for older clients. V7.77 clients
    // select their own class from `pots` and never render the other.
    io.emit("dailypot-update", { pot: adult, pots: { adult, teen } });
  } catch (e) {}
}
// The Daily Pot draw — the same discipline as potRunDraw (RP-V7.41):
// distinct winners picked uniformly at random (crypto Fisher-Yates)
// over the ENTRY LIST ONLY; each winner is credited floor(total / n)
// through the money ledger; the split remainder is stamped rolledOut
// and folds into tomorrow's pot at the roll (never paid to a host).
// [RP-V7.66] HOW MANY winners is itself random (Branden, Oct 26):
// every night the count is drawn fresh, 1..DAILY_POT_MAX_WINNERS —
// some nights ONE lucky winner takes the whole pot.
function dpRunBurst(db, rec) {
  // [RP-V7.52] Settlement is idempotent per pot date (audit C1): a
  // record that is no longer "open" has already settled — a second
  // settle for the same date is a no-op and pays nobody twice.
  if (!rec || rec.status !== "open" || rec.burstDoneAt) return null;
  const total = dailyPotTotal(rec);
  // [RP-V7.77] BE-THERE RULE: the draw runs over QUALIFIED entrants
  // only — entered AND at least DP_WIN_MIN_PRESENCE_MS of in-Plaza
  // presence today AND present in the Plaza at the burst moment
  // (a live acct-presence socket when settlement runs; Branden:
  // "30 minutes and can't leave until the pot burst"). Unqualified
  // names are skipped, exactly like the live pot's qualified-pool
  // draw. If NOBODY qualifies, the pot does not burst at all: the
  // whole pot rolls into its class's tomorrow through the noburst
  // path, with the reason on the record.
  const entrants = (rec.entries || []).filter(
    (id) =>
      dpPresenceMs(id, rec.date) >= DP_WIN_MIN_PRESENCE_MS &&
      dpAccountPresent(id)
  );
  if (!entrants.length) {
    rec.status = "noburst";
    rec.statusNote = !(rec.entries || []).length
      ? "rolled — nobody entered"
      : (rec.entries || []).some((id) => dpPresenceMs(id, rec.date) >= DP_WIN_MIN_PRESENCE_MS)
        ? "rolled — nobody with 30 minutes in the Plaza was here when it burst"
        : "rolled — nobody had 30 minutes in the Plaza yet";
    rec.burstDoneAt = new Date().toISOString();
    writeDailyPot(db);
    dpBroadcastUpdate(true);
    console.log(
      "[dailypot:" + rec.potClass + "] no burst —", rec.statusNote + ":", rec.date, total
    );
    return { noburst: true, reason: "presence" };
  }
  const drawCount = 1 + crypto.randomInt(DAILY_POT_MAX_WINNERS); // [RP-V7.66] tonight's winner count: 1..5
  const n = Math.min(drawCount, entrants.length);
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
    // [RP-V7.75] Boosted teen winnings, same rule as the Plaza Pot:
    // +TEEN_WIN_BOOST platform-funded charms on top of the split for
    // an under-18 winner. The split remainder (rolledOut) is computed
    // from share alone, so it stays exact to the charm.
    // [RP-V7.77] Only the TEEN Daily Pot carries the boost; the adult
    // pool never boosts an anomalously classed legacy entrant.
    const boost =
      rec.potClass === "teen" && u && ageFromDob(u.dob) < 18
        ? TEEN_WIN_BOOST
        : 0;
    return {
      id,
      name: (u && u.name) || (rec.entryNames && rec.entryNames[id]) || "Winner",
      amount: share + boost,
      ...(boost ? { boost } : {}),
    };
  });
  // [RP-V7.52] The settlement stamp is persisted BEFORE any payout
  // lands: status flips to "burst" with its burstDoneAt, so any
  // concurrent or repeated settle attempt from here on reads a
  // settled record and stops (audit C1).
  rec.status = "burst";
  rec.winners = winners;
  rec.burstDoneAt = new Date().toISOString();
  rec.rolledOut = remainder;
  writeDailyPot(db);
  const mdb = readMoney();
  for (const w of winners) {
    mdb.balances[w.id] = (mdb.balances[w.id] || 0) + w.amount;
    moneyTx(mdb, {
      type: "dailypot-win", from: null, to: w.id, charms: w.amount,
      cents: 0, cut: 0, ref: rec.date,
    });
    // [RP-V7.74] A teen winner's prize also fills their gift balance.
    // [RP-V7.75] w.amount includes the teen win boost — the mirror
    // sees the full credited amount.
    giftBalMirrorWin(mdb, adb.users.find((x) => x.id === w.id), w.amount);
  }
  writeMoney(mdb);
  try {
    io.emit("dailypot-burst", {
      date: rec.date, potClass: rec.potClass, total, winners, share, remainder,
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
// The settlement for a day at its drawn moment: entries -> burst; ZERO entries ->
// NO burst (status "noburst") — the whole total rolls into tomorrow.
function dpSettleClass(potClass) {
  const cls = potClass === "teen" ? "teen" : "adult";
  const db = readDailyPot();
  const cur = db.pots[cls];
  if (!cur || cur.status !== "open") return null;
  if ((cur.entries || []).length >= 1) return dpRunBurst(db, cur);
  cur.status = "noburst";
  cur.statusNote = "rolled — nobody entered";
  writeDailyPot(db);
  dpBroadcastUpdate(true);
  console.log(
    "[dailypot:" + cls + "] no burst (0 entries) — whole pot rolls forward:", cur.date,
    dailyPotTotal(cur)
  );
  return { noburst: true };
}
function dpGiftVolumeOn(dateStr, potClass) {
  // [RP-V7.42] Total charms gifted on one ET date, from the money
  // ledger's gift-sent transactions (one per gift, charms = the
  // gift's catalog cost). No ledger yet = zero volume = Tier 1.
  // [RP-V7.77] Volume is measured PER AGE CLASS from the sender:
  // adult gifts grow the adult tier track, teen gifts the teen one.
  // The classes never lend each other volume.
  const cls = potClass === "teen" ? "teen" : "adult";
  let total = 0;
  try {
    const db = readMoney();
    const adb = readAccounts();
    const senderClass = new Map(
      adb.users.map((u) => [u.id, accountAgeClass(u)])
    );
    for (const tx of db.txlog || []) {
      if (!tx || tx.type !== "gift-sent") continue;
      if ((senderClass.get(tx.from) || "adult") !== cls) continue;
      const at = Date.parse(tx.at || "");
      if (!Number.isFinite(at)) continue;
      if (dpDateStr(at) === dateStr) total += tx.charms || 0;
    }
  } catch (e) { /* volume reads must never break the day roll */ }
  return total;
}
function dpTierForNewDay(dateStr, potClass) {
  // [RP-V7.42] The tier a NEW day (dateStr) opens at — from the
  // PREVIOUS ET day's gift volume; the manual override wins outright.
  if (DAILY_POT_SEED_OVERRIDE > 0)
    return {
      tier: 0, // 0 = manual override (state still exposes seed + cap)
      seed: DAILY_POT_SEED_OVERRIDE,
      cap: DAILY_POT_SEED_OVERRIDE * 10,
      prevVolume: null,
    };
  const prevVolume = dpGiftVolumeOn(dpDatePlus(dateStr, -1), potClass);
  for (const t of DAILY_POT_TIERS)
    if (prevVolume >= t.minVolume)
      return { tier: t.tier, seed: t.seed, cap: t.cap, prevVolume };
  return { tier: 1, seed: DAILY_POT_SEED, cap: DAILY_POT_MATCH_CAP, prevVolume };
}
function dpFreshRec(dateStr, rolledIn, potClass) {
  const cls = potClass === "teen" ? "teen" : "adult";
  const t = dpTierForNewDay(dateStr, cls); // [RP-V7.42] the day carries its own class tier
  return {
    potClass: cls,
    date: dateStr,
    tier: t.tier,
    seed: t.seed,
    matchCap: t.cap,
    prevVolume: t.prevVolume,
    rolledIn: rolledIn || 0,
    match: 0,
    milestonesHit: [], // [RP-V7.43] milestone thresholds already shouted today
    entries: [],
    entryNames: {},
    status: "open",
    winners: [],
    burstAt: dpDrawDailyBurstAt(dateStr), // [RP-V7.77] this class's own secret moment in [19:00, 21:00) ET
    burstDrawVersion: 1,
    burstDoneAt: null,
    rolledOut: 0,
  };
}
// Make sure the store holds TODAY's (ET) pot, settling/rolling any
// stale day first: an old day still "open" past its drawn moment settles by
// its own rules (missed bursts still fire), then the carry folds in —
// a burst day contributes only its split remainder; any other day
// (no-burst) contributes its ENTIRE total. Also settles today's pot
// the moment it comes due, so state reads never lag the tick.
function dpEnsureClass(potClass, now) {
  const cls = potClass === "teen" ? "teen" : "adult";
  const today = dpDateStr(now);
  let db = readDailyPot();
  let rec = db.pots[cls];
  if (rec && rec.date === today && rec.status === "open" && rec.burstDrawVersion !== 1) {
    // A record opened before the secret-window rule gets its drawn
    // moment now, persisted once — reboots never redraw it.
    rec.burstAt = dpDrawDailyBurstAt(today);
    rec.burstDrawVersion = 1;
    db.pots[cls] = rec;
    writeDailyPot(db);
    db = readDailyPot();
    rec = db.pots[cls];
  }
  if (rec && rec.date !== today) {
    if (rec.status === "open" && now >= (rec.burstAt || 0)) {
      dpSettleClass(cls);
      db = readDailyPot();
      rec = db.pots[cls];
    }
    if (rec) dpPushHistory(rec); // [RP-V7.43] snapshot this class's finished day only
    const carry = rec
      ? rec.status === "burst"
        ? rec.rolledOut || 0
        : dailyPotTotal(rec)
      : 0;
    rec = dpFreshRec(today, carry, cls);
    db = readDailyPot();
    db.pots[cls] = rec;
    writeDailyPot(db);
    console.log("[dailypot:" + cls + "] opened", today, "seed", rec.seed, "rolledIn", carry);
    dpBroadcastUpdate(true);
    dpCheckMilestones(today, cls); // [RP-V7.43] rollover-in may open the day already past a threshold
  }
  if (!rec) {
    rec = dpFreshRec(today, 0, cls);
    db = readDailyPot();
    db.pots[cls] = rec;
    writeDailyPot(db);
    console.log("[dailypot:" + cls + "] opened", today, "seed", rec.seed, "rolledIn", 0);
    dpCheckMilestones(today, cls); // a big manual seed override could open past a threshold too
  }
  if (rec.status === "open" && now >= (rec.burstAt || 0)) {
    dpSettleClass(cls);
    rec = readDailyPot().pots[cls];
  }
  return rec;
}
function dpEnsureToday(now) {
  // Both class worlds roll/settle independently. The adult record
  // is returned for the few legacy-shaped internal callers; routes
  // and gift routing always name their class explicitly.
  dpEnsureClass("teen", now);
  return dpEnsureClass("adult", now);
}
// The scheduler tick (boot + every 60s): open the ET day at midnight,
// fire each burst settlement at its drawn moment.
function dailyPotTick() {
  // [RP-V7.52] the tick settles through the same money lock as the
  // HTTP settle-on-contact paths (audit C1).
  withMoneyLock(() => {
    try {
      dpEnsureToday(Date.now());
    } catch (e) {
      console.log("[dailypot] tick failed", e && e.message);
    }
  }).catch(() => {});
}
// Gift growth hook (called from POST /api/money/gift after the money
// has moved): EVERY gift on the Plaza grows today's Daily Pot by a
// platform match of 2% of its charm value (floored, min 0), capped
// for the day at the day's tier cap (rec.matchCap). Platform accounting only — the
// gift, its split and any live-pot match are untouched.
function dailyPotOnGift(giftCharms, senderClass) {
  // [RP-V7.77] The 2% match follows the SENDER's age class and only
  // that class's Daily Pot, against that pool's own cap.
  const cls = senderClass === "teen" ? "teen" : "adult";
  const rec = dpEnsureClass(cls, Date.now());
  if (!rec || rec.status !== "open") return;
  const cap = rec.matchCap != null ? rec.matchCap : DAILY_POT_MATCH_CAP; // [RP-V7.42] the DAY's cap, from its tier
  const add = Math.min(
    cap - (rec.match || 0),
    Math.floor((giftCharms * DAILY_POT_MATCH_PCT) / 100)
  );
  if (!(add > 0)) return;
  const db = readDailyPot();
  const cur = db.pots[cls];
  if (!cur || cur.date !== rec.date || cur.status !== "open") return;
  const cap2 = cur.matchCap != null ? cur.matchCap : DAILY_POT_MATCH_CAP;
  const add2 = Math.min(cap2 - (cur.match || 0), add);
  if (!(add2 > 0)) return;
  cur.match = (cur.match || 0) + add2;
  writeDailyPot(db);
  dpCheckMilestones(cur.date, cls); // [RP-V7.43] growth may have crossed a milestone threshold
  dpBroadcastUpdate(false); // throttled — joins/bursts force their own
}
app.post("/api/dailypot/join", lockedHandler("dailypot-join", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return; // 401 "Not signed in" — guests must sign in to enter
  if (isPendingDeletion(ctx.user))
    return res
      .status(403)
      .json({ ok: false, error: "This account is scheduled for deletion" });
  // [RP-V7.77] Daily Pot entry is class-locked. With no explicit
  // target the member enters their own class's pot. A client may
  // name a potClass (the card normally doesn't), and naming the
  // other world is a clean refusal — the pools never mix.
  const ownClass = accountAgeClass(ctx.user);
  const requestedClass = String(
    (req.body || {}).potClass || (req.body || {}).class || ownClass
  );
  if (requestedClass !== ownClass)
    return res.status(403).json({
      ok: false,
      error:
        requestedClass === "teen"
          ? "This is the teen pot — teens only"
          : "This is the adults' pot",
      potClass: requestedClass,
    });
  dpEnsureClass(ownClass, Date.now());
  const db = readDailyPot();
  const rec = db.pots[ownClass];
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
  dpBumpStreak(ctx.user.id, rec.date, ownClass); // [RP-V7.43] a successful entry feeds this class's streak
  dpBroadcastUpdate(true);
  console.log("[dailypot:" + ownClass + "] join", rec.date, ctx.user.name, "entries", rec.entries.length);
  res.json({ ok: true, ...dailyPotPairPayload(ctx.user) });
}));
app.get("/api/dailypot/state", lockedHandler("dailypot-state", (req, res) => {
  let viewer = null;
  try {
    viewer = accountForToken(readAccounts(), req);
  } catch (e) {}
  // [RP-V7.52] settle-on-contact runs inside the money lock, so a
  // state read in the burst window can never race the scheduler
  // into a second settlement (audit C1).
  // [RP-V7.77] A signed-in member is served BOTH Daily Pots for
  // the side-by-side Home pair: their own class's pot in `pot`
  // (enterable) and the other class's pot watch-only in
  // `otherPot`/`pots`. Guests keep the adult pot in `pot`; they
  // cannot enter either pool without an account.
  dpEnsureToday(Date.now());
  const payload = dailyPotPairPayload(viewer);
  // [RP-V7.80] Full-scan F4: a guest (no/invalid token) gets NO
  // otherPot key at all — the side-by-side pair is a signed-in
  // surface. Signed-in adult/teen payloads are unchanged.
  if (!viewer) delete payload.otherPot;
  res.json({ ok: true, ...payload });
}));

// ---------------------------------------------------------------------------
// [RP-V7.76] THE UNIFIED DAILY CLAIM ENDPOINT (brain train batch 1,
// FIX-2) — the single claim gate described above claimRecordFor.
// History: RP-V7.75 shipped the teen half of this as
// POST /api/teen/daily-drop with the gate on the account record;
// that route and field are retired into this endpoint (read-compat
// for a same-day teenDailyDropDate lives in claimRecordFor), and the
// adult Daily Rewards ladder — device-gated in the client since
// RP-V7.26 — moves behind the same gate here. Externally visible
// teen behavior is IDENTICAL to V7.75: 2,500 main + 2,500 giftBal
// mirror, 409 on a same-day re-claim with the same copy, adults
// refused the teen claim, claimed-state UI driven by the same
// teenDrop status in the Daily Pot state. The adult claim pays the
// ladder rung for the NEW streak day — the exact amounts the client
// has always paid (DAILY_CLAIM_LADDER mirrors REWARD_LADDER).
// Runs through the money lock like every other charm mutation.
// ---------------------------------------------------------------------------
app.post("/api/money/daily-claim", lockedHandler("daily-claim", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return; // 401 "Not signed in"
  if (isPendingDeletion(ctx.user))
    return res
      .status(403)
      .json({ ok: false, error: "This account is scheduled for deletion" });
  const user =
    ctx.db.users.find((u) => u.id === ctx.user.id) || ctx.user;
  const teen = ageFromDob(user.dob) < 18;
  const wantKind = String((req.body || {}).kind || "");
  // The teen claim stays teen-only in BOTH directions: an adult
  // explicitly asking for the teen drop is refused (the V7.75 rule).
  if (!teen && (wantKind === "teen-drop" || wantKind === "teen"))
    return res
      .status(403)
      .json({ ok: false, error: "The daily charm drop is for under-18 members" });
  const today = dpDateStr(Date.now());
  const cdb = readClaims();
  const rec = claimRecordFor(user, cdb);
  const kind = teen ? "teen-drop" : "daily-claim";
  if (rec.lastDate === today) {
    // ONE gate: any claim kind already made today refuses every
    // other kind today too — nothing moves, the payload carries the
    // shared state so any client surface renders the claimed day.
    return res.status(409).json({
      ok: false,
      error: teen
        ? "You've already claimed today's drop — the next one lands tomorrow"
        : "You've already claimed today's reward — the next one lands tomorrow",
      claimed: true,
      kind,
      amount: teen
        ? TEEN_DAILY_DROP
        : DAILY_CLAIM_LADDER[Math.min(rec.streak || 1, DAILY_CLAIM_LADDER.length) - 1],
      streak: rec.streak || 0,
      dailyClaim: claimStatePayload(user, cdb),
      teenDrop: teen
        ? { eligible: true, amount: TEEN_DAILY_DROP, claimed: true }
        : { eligible: false, amount: TEEN_DAILY_DROP, claimed: false },
    });
  }
  // Streak advance in the claim store (ET days): yesterday -> +1,
  // anything older (or a first-ever claim) -> 1.
  const streak = rec.lastDate === dpDatePlus(today, -1) ? (rec.streak || 0) + 1 : 1;
  cdb.users[user.id] = {
    lastDate: today,
    streak,
    best: Math.max(rec.best || 0, streak),
    lastKind: kind,
  };
  writeClaims(cdb);
  const amount = teen
    ? TEEN_DAILY_DROP
    : DAILY_CLAIM_LADDER[Math.min(streak, DAILY_CLAIM_LADDER.length) - 1];
  const mdb = readMoney();
  mdb.balances[user.id] = (mdb.balances[user.id] || 0) + amount;
  moneyTx(mdb, {
    // Ledger continuity: the teen claim keeps its V7.75 tx type.
    type: teen ? "teen-daily-drop" : "daily-claim", from: null, to: user.id,
    charms: amount, cents: 0, cut: 0, ref: today,
  });
  // The teen claim keeps its V7.75 fill rule: the drop is gifting
  // fuel, so the full amount mirrors into the gift balance. The
  // mirror helper itself no-ops for adults.
  if (teen) giftBalMirrorWin(mdb, user, amount);
  writeMoney(mdb);
  // [RP-V7.75, kept] BRAIN + ALGORITHM: the claim also registers in
  // the server-side daily-return engine (RP-V7.43, dailypot-streaks)
  // — a claim day counts as a daily return exactly like a Daily Pot
  // entry day. dpBumpStreak is same-day idempotent, so claim-then-
  // enter (or enter-then-claim) counts the day once and never
  // resets a running streak. (V7.75 did this for teen claims; the
  // unified claim does it for every claim — same engine, same rule.)
  try { dpBumpStreak(user.id, today, teen ? "teen" : "adult"); } catch (e) {}
  console.log("[claim]", kind, today, user.name, "+", amount, "streak", streak);
  res.json({
    ok: true,
    kind,
    amount,
    streak,
    date: today,
    balance: mdb.balances[user.id],
    giftBal: (mdb.giftBals && mdb.giftBals[user.id]) || 0,
    dailyClaim: claimStatePayload(user),
    teenDrop: teen
      ? { eligible: true, amount: TEEN_DAILY_DROP, claimed: true }
      : { eligible: false, amount: TEEN_DAILY_DROP, claimed: false },
  });
}));

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
// [RP-V7.50] Fallback photo for an account with none stored: the
// photoUrl of a currently-connected player whose display name uniquely
// matches the account name (the pre-V7.50 source), else null.
function livePhotoForAccount(u) {
  const k = String((u && u.name) || "").toLowerCase();
  if (!k) return null;
  let found = null, n = 0;
  for (const p of players.values()) {
    if (!p || !p.name || String(p.name).toLowerCase() !== k) continue;
    n++;
    if (p.photoUrl) found = p.photoUrl;
  }
  return n === 1 ? found : null;
}
// [RP-V7.86] Resolve one post reference ({kind, id}) to a profile tile,
// or null when the post is gone. Shared by pins, collections and the
// Liked tab so every profile surface renders the same tile shape.
function profileTileForPost(kind, id, vdb, likesDb, commentsDb) {
  if (kind === "reel") {
    const r = listReels().find((x) => x && x.id === id);
    if (!r || !r.file) return null;
    return { kind: "reel", id: r.id, src: "/reel-files/" + r.file, views: mediaViewCount(vdb, "reel:" + r.id), caption: r.caption || "", likes: Array.isArray(r.heartLikes) ? r.heartLikes.length : 0 };
  }
  if (kind === "photopost") {
    const p = readPhotoPosts().posts.find((x) => x && x.id === id);
    if (!p || !p.photo) return null;
    const pub = photoPublicPost(p, "", likesDb, commentsDb);
    return { kind: "photopost", id: p.id, src: p.photo, views: 0, caption: p.caption || "", likes: pub.likes || 0 };
  }
  return null;
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
  // [RP-V7.64] each reel carries its real view count; the playback URL
  // is resolved from the stored file when the entry has no url field
  // (the same construction GET /api/reels uses).
  let reels = [];
  try {
    const vdb = readViews();
    reels = listReels()
      .filter((r) => r && r.author === target.name)
      .slice(0, 12)
      .map((r) => ({ id: r.id, url: r.url || (r.file ? "/reel-files/" + r.file : null), kind: r.kind || "video", caption: r.caption || "", createdAt: r.createdAt || null, views: mediaViewCount(vdb, "reel:" + r.id) }));
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
  // [RP-V7.86] Likes RECEIVED across every post kind (reels + photo
  // posts + stories + feed posts), the profile's own photo posts, the
  // live badge, pinned posts, collections and the Liked tab — all from
  // the server stores, never faked client-side.
  const vdb86 = readViews();
  const likesDb86 = readPhotoLikes();
  const commentsDb86 = readPhotoComments();
  const repostsDb86 = readPhotoReposts(); // [RP-V7.89]
  let likesTotal = 0;
  let photoPosts = [];
  try {
    for (const r of listReels())
      if (r && Array.isArray(r.heartLikes) && r.heartLikes.length && reelAuthorKeyFor(ctx.db, r) === target.id)
        likesTotal += r.heartLikes.length;
  } catch (e) { }
  try {
    photoPosts = readPhotoPosts().posts.filter((p) => p && p.owner === target.id).slice(0, 30)
      .map((p) => photoPublicPost(p, ctx.user.id, likesDb86, commentsDb86, repostsDb86));
    for (const p of photoPosts) likesTotal += p.likes || 0;
  } catch (e) { }
  try {
    const nowMs = Date.now();
    const sdb86 = readStories();
    for (const s of Object.values(sdb86.stories || {}))
      if (s && s.authorId === target.id && Date.parse(s.expiresAt) > nowMs && Array.isArray(s.likes))
        likesTotal += s.likes.length;
  } catch (e) { }
  try {
    const fdb86 = readFeed();
    for (const fp of Object.values(fdb86.posts || {}))
      if (fp && fp.authorId === target.id && Array.isArray(fp.likes))
        likesTotal += fp.likes.length;
  } catch (e) { }
  const liveNow = [...liveRegistry.values()].some((e) => e && e.name === target.name);
  const pinRefs = (Array.isArray(target.pins) ? target.pins : [])
    .filter((x) => x && (x.kind === "reel" || x.kind === "photopost") && typeof x.id === "string").slice(0, 3);
  const pinnedItems = [];
  for (const pn of pinRefs) {
    const it = profileTileForPost(pn.kind, pn.id, vdb86, likesDb86, commentsDb86);
    if (it) pinnedItems.push(it);
  }
  let collections = [];
  try {
    const cdb86 = readProfileCollections();
    const mine86 = Array.isArray(cdb86.byUser[target.id]) ? cdb86.byUser[target.id] : [];
    collections = mine86.map((c) => ({
      id: c.id, name: c.name,
      count: Array.isArray(c.items) ? c.items.length : 0,
      items: (Array.isArray(c.items) ? c.items : []).map((it) => profileTileForPost(it.kind, it.id, vdb86, likesDb86, commentsDb86)).filter(Boolean),
    }));
  } catch (e) { }
  const likedPrivate = !!target.likedPrivate;
  let liked = null;
  if (ctx.user.id === target.id || !likedPrivate) {
    liked = [];
    try {
      for (const r of listReels())
        if (r && Array.isArray(r.heartLikes) && r.heartLikes.includes(target.id)) {
          const it = profileTileForPost("reel", r.id, vdb86, likesDb86, commentsDb86);
          if (it) liked.push(it);
        }
    } catch (e) { }
    try {
      for (const pid of Object.keys(likesDb86.photos || {}))
        if (Array.isArray(likesDb86.photos[pid]) && likesDb86.photos[pid].includes(target.id)) {
          const it = profileTileForPost("photopost", pid, vdb86, likesDb86, commentsDb86);
          if (it) liked.push(it);
        }
    } catch (e) { }
    try {
      const fdb87 = readFeed();
      for (const fp of Object.values(fdb87.posts || {}))
        if (fp && fp.file && Array.isArray(fp.likes) && fp.likes.includes(target.id))
          liked.push({ kind: fp.kind === "video" ? "reel" : "photo", id: fp.id, src: "/photos/feed/" + fp.file, views: 0, caption: fp.text || "", likes: fp.likes.length });
    } catch (e) { }
    liked = liked.slice(0, 36);
  }
  // [RP-V7.89] Reposts tab: the member's reposted reels + photo posts,
  // newest repost first, resolved at read time (a deleted post drops
  // out via profileTileForPost, like pins/collections). Public — the
  // Liked-privacy toggle governs Liked only.
  let reposts86 = [];
  try {
    const mine86 = [];
    for (const r of listReels())
      if (r && Array.isArray(r.reposts))
        for (const rp of r.reposts)
          if (rp && rp.u === target.id) {
            const it = profileTileForPost("reel", r.id, vdb86, likesDb86, commentsDb86);
            if (it) { it.repostedAt = rp.at || null; mine86.push(it); }
          }
    for (const pid of Object.keys(repostsDb86.photos || {})) {
      const hit = photoRepostSet(repostsDb86, pid).find((x) => x && x.u === target.id);
      if (hit) {
        const it = profileTileForPost("photopost", pid, vdb86, likesDb86, commentsDb86);
        if (it) { it.repostedAt = hit.at || null; mine86.push(it); }
      }
    }
    mine86.sort((a, b) => String(b.repostedAt || "").localeCompare(String(a.repostedAt || "")));
    reposts86 = mine86.slice(0, 36);
  } catch (e) { }
  res.json({
    ok: true,
    id: target.id,
    name: target.name,
    username: target.username || null,
    profileType: profileTypeOf(target),
    profileTypeLabel: profileTypeLabel(target),
    // [RP-V7.50] the account's stored photo, live-player fallback
    photo: target.photo || livePhotoForAccount(target),
    followersCount: socialFollowerIds(sdb, target.id).length,
    followingCount: socialFollowingIds(sdb, target.id).length,
    iFollow: socialFollowingIds(sdb, ctx.user.id).includes(target.id),
    dailyRank, dailyCharms,
    gifter: { level: rpLevelFor(sentCharms), charms: sentCharms },
    host: { level: rpLevelFor(receivedCharms), charms: receivedCharms },
    gallery: { got: Object.keys(galleryRefs).length, total: Object.keys(MONEY_GIFT_TABLE).length },
    // [RP-V7.64] the member's gallery photos + their server-owned
    // view counts, so profile pages can render the tile grid.
    photos: accountPhotos(target),
    photoViews: photoViewsFor(target),
    reelsCount, reels, testimony,
    // [RP-V7.86] The profile build: bio + link, live badge, Likes
    // received, photo posts, pins, collections, Liked tab + privacy.
    bio: typeof target.bio === "string" ? target.bio : "",
    link: typeof target.link === "string" ? target.link : "",
    liveNow,
    likesTotal, photoPosts,
    pins: pinRefs, pinnedItems, collections,
    likedPrivate, liked,
    reposts: reposts86, // [RP-V7.89]
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
// ---------------------------------------------------------------------------
// [RP-V7.70] Plaza Stories (Branden, Oct 26: "Every profile should have
// this where people post to their story and algorithm will post your
// friends story so you can see it... When you touch anyone's story the
// video will play. And you can gift it or like it or share it or follow
// that person just like it is in TikTok" — TikTok's story FLOW, rebuilt
// in original code with Plaza branding; no TikTok assets or copy).
//
// Stories are ACCOUNT state ("the brain in everything"): the store is
// stories.json beside the other data files, media files live under
// PHOTO_DIR/stories and ride the existing /photos static mount, so a
// story answers at /photos/stories/<file> on any device the member
// signs in on — never device-only.
//
//   { stories: { [storyId]: { id, authorId, authorName, file,
//        createdAt, expiresAt, likes: [accountId], viewedBy: [accountId] } } }
//
// Lifetime: a story dies 24h after posting (expiresAt). sweepStories()
// runs on boot, on a 10-minute timer (same pattern as the deletion
// sweep) and lazily inside read paths; expiring a story also unlinks
// its media file.
//
// Tray ranking REUSES the one shared For You interest profile
// (reel-signals.json): people the member follows come first, ordered
// by decayed author affinity (fyDecayed, the same read the Reels and
// Live rankers use), then everyone else by affinity, newest first on
// ties. No second ranker exists.
//
// Views ride the EXISTING views system (views.json): POST
// /api/story/view records through recordMediaView with item key
// "story:<id>" — deduped per viewer per America/New_York day, exactly
// the semantics reels and photos use. The public count on a story is
// mediaViewCount of that key. (viewedBy in this store is only the
// ring state — colored vs gray — which must live for the story's
// whole 24h, not just today.)
//
// Likes live here (a set of account ids per story); a fresh like also
// bumps the shared author affinity by +4 — the settled For You weight
// for a like — so liking stories feeds the same interest profile that
// ranks Reels, Live and this tray.
//
// AGE SPLIT — FINAL, Branden, Oct 26, 2026. His clarifications, in
// order: "Stories: all ages can view, gifting stays 18+" (options
// tap) → "Likes to" → "Let's get this straight under 18 is allowed
// to post anything get likes can share to" + "No gifting for
// under 18". Net rule: EVERYTHING SOCIAL = ALL AGES; MONEY = 18+.
//   VIEWING (tray + view recording): ALL AGES.
//   LIKES: ALL AGES (RP-V7.74; follows viewing).
//   POSTING: ALL AGES (RP-V7.74 — the /api/story/post gate below
//     is now view-level; V7.72–V7.73 held posting at 18+, that is
//     superseded).
//   SHARING: ALL AGES (share never carried an age gate).
//   GIFTING from a story: OPEN to every signed-in account since
//     RP-V7.79 — the V7.72 door gate on the viewer's 🎁 tap is
//     superseded (Branden tapped "Open teen story-gifting too
//     (charms only)"); a teen's story gift settles charms-only.
//     On the server,
//     POST /api/money/gift itself no longer 403s teens (RP-V7.74,
//     superseding RP-V7.73): a gift with a teen on either side runs
//     CHARMS-ONLY — charms move, no earnings are created. Real money
//     stays 18+ server-locked: checkout / subscribe / cashout
//     (RP-V7.74).
// The constants below (and their client mirrors) are the ONE
// flip point for this split. Teen Hangout and Fellowship all-ages
// functions are untouched either way.
// ---------------------------------------------------------------------------
const STORY_VIEW_ALL_AGES = true;    // [RP-V7.72] viewing/tray/views: every signed-in account
const STORY_LIKE_ALL_AGES = true;    // [RP-V7.74] likes: ALL AGES, like viewing (Branden: "Likes to")
const STORY_POST_ALL_AGES = true;    // [RP-V7.74] posting: ALL AGES (Branden: "allowed to post anything") — replaces STORY_POST_ADULT_ONLY (V7.72, superseded)
const STORY_GIFT_ADULT_ONLY = false; // [RP-V7.79] story gifting OPEN to every signed-in account (Branden tapped "Open teen story-gifting too (charms only)") — supersedes the V7.72 hold: the tray payload's canGift follows storyCanGift below, the 🎁 tap opens the standard gift sheet, and /api/money/gift's teen branch settles the send charms-only (giftBal debit, author credited charms, zero earnings, RP-V7.74). Guests still can't gift: the tray requires an account.
const STORY_TTL_MS = 24 * 3600 * 1000;
const STORY_VIDEO_MAX = 50 * 1024 * 1024; // same cap as DM/reel video
const STORY_MAX_ACTIVE_PER_AUTHOR = 10;
const STORY_TRAY_MAX_AUTHORS = 50;
const STORIES_FILE =
  process.env.STORIES_FILE || path.join(path.dirname(PHOTO_DIR), "stories.json");
const STORY_DIR = path.join(PHOTO_DIR, "stories");
fs.mkdirSync(STORY_DIR, { recursive: true });
function readStories() {
  return storeReadJson(
    STORIES_FILE,
    (d) => !!(d && d.stories && typeof d.stories === "object" && !Array.isArray(d.stories)),
    { stories: {} },
    "stories"
  );
}
function writeStories(db) {
  storeWriteJson(STORIES_FILE, db);
}
function sweepStories() {
  const db = readStories();
  const now = Date.now();
  let changed = false;
  for (const id of Object.keys(db.stories)) {
    const s = db.stories[id];
    if (!s || !(Date.parse(s.expiresAt) > now)) {
      if (s && s.file) fs.unlink(path.join(STORY_DIR, String(s.file)), () => {});
      delete db.stories[id];
      changed = true;
    }
  }
  if (changed) writeStories(db);
  return db;
}
function storyIsAdult(user) {
  return ageFromDob(user.dob) >= 18;
}
function storyCanView(user) {
  return STORY_VIEW_ALL_AGES || storyIsAdult(user);
}
function storyCanLike(user) {
  // [RP-V7.74] Likes are view-level: any signed-in account, any DOB.
  return STORY_LIKE_ALL_AGES || storyIsAdult(user);
}
function storyCanPost(user) {
  // [RP-V7.74] Posting is view-level now: any signed-in account.
  return STORY_POST_ALL_AGES || storyIsAdult(user);
}
function storyCanGift(user) {
  return !STORY_GIFT_ADULT_ONLY || storyIsAdult(user);
}
function storyPublic(s, vdb, meId) {
  const likes = Array.isArray(s.likes) ? s.likes : [];
  const viewedBy = Array.isArray(s.viewedBy) ? s.viewedBy : [];
  return {
    id: s.id,
    url: "/photos/stories/" + s.file,
    createdAt: s.createdAt,
    expiresAt: s.expiresAt,
    views: mediaViewCount(vdb, "story:" + s.id),
    likes: likes.length,
    likedByMe: meId ? likes.includes(meId) : false,
    viewedByMe: meId ? viewedBy.includes(meId) : false,
  };
}
const storyUpload = multer({
  storage: multer.diskStorage({
    destination: (req, file, cb) => cb(null, STORY_DIR),
    filename: (req, file, cb) => {
      const ext = REEL_VIDEO_TYPES[file.mimetype] || "mp4";
      cb(null, `${Date.now()}-${crypto.randomBytes(6).toString("hex")}.${ext}`);
    },
  }),
  limits: { fileSize: STORY_VIDEO_MAX },
  fileFilter: (req, file, cb) => {
    if (REEL_VIDEO_TYPES[file.mimetype]) cb(null, true);
    else cb(new Error("Stories are video only — MP4, WebM or MOV"));
  },
});
// Post a story. Auth (and the age gate) run BEFORE multer, exactly
// like POST /api/dm/media, so a refused request never writes a file;
// every later failure unlinks the stored file.
app.post("/api/story/post",
  (req, res, next) => {
    const ctx = requireAccount(req, res);
    if (!ctx) return;
    if (!storyCanPost(ctx.user))
      return res.status(403).json({ ok: false, error: "Posting stories is 18+" });
    req._storyCtx = ctx;
    next();
  },
  (req, res, next) => {
    storyUpload.single("media")(req, res, (err) => {
      if (err) {
        const tooBig = err && err.code === "LIMIT_FILE_SIZE";
        return res.status(tooBig ? 413 : 400).json({
          ok: false,
          error: tooBig ? "That video is too big — 50 MB max" : (err.message || "That file can't be posted"),
        });
      }
      next();
    });
  },
  (req, res) => {
    const ctx = req._storyCtx;
    const fail = (status, error) => {
      if (req.file) fs.unlink(req.file.path, () => {});
      return res.status(status).json({ ok: false, error });
    };
    if (!req.file) return fail(400, "No video received");
    const db = sweepStories();
    const mine = Object.values(db.stories).filter((s) => s && s.authorId === ctx.user.id);
    if (mine.length >= STORY_MAX_ACTIVE_PER_AUTHOR)
      return fail(429, "You already have " + STORY_MAX_ACTIVE_PER_AUTHOR + " stories up — let one expire first");
    const now = Date.now();
    const story = {
      id: crypto.randomBytes(8).toString("hex"),
      authorId: ctx.user.id,
      authorName: ctx.user.name,
      file: path.basename(req.file.path),
      createdAt: new Date(now).toISOString(),
      expiresAt: new Date(now + STORY_TTL_MS).toISOString(),
      likes: [],
      viewedBy: [],
    };
    db.stories[story.id] = story;
    writeStories(db);
    res.json({ ok: true, story: storyPublic(story, readViews(), ctx.user.id) });
  }
);
// The story tray: active stories grouped by author, ranked by the
// shared For You profile (follows first, then decayed author
// affinity, newest first on ties).
app.get("/api/story/tray", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  if (!storyCanView(ctx.user))
    return res.json({ ok: true, adultOnly: true, authors: [] });
  const db = sweepStories();
  const vdb = readViews();
  const sdb = readSocial();
  const following = new Set(socialFollowingIds(sdb, ctx.user.id));
  const sig = readReelSignals();
  const urec = fyUserRec(sig, ctx.user.id, false);
  const aff = (urec && urec.authorAff) || {};
  const now = Date.now();
  const byAuthor = new Map();
  for (const s of Object.values(db.stories)) {
    if (!s || !s.authorId) continue;
    if (!byAuthor.has(s.authorId)) byAuthor.set(s.authorId, []);
    byAuthor.get(s.authorId).push(s);
  }
  const authors = [];
  for (const [authorId, list] of byAuthor) {
    const brief = socialBrief(ctx.db, authorId);
    if (!brief) continue; // pending-deletion / gone accounts don't show
    const acct = ctx.db.users.find((u) => u.id === authorId);
    const photos = acct ? accountPhotos(acct) : [];
    list.sort((a, b) => String(a.createdAt).localeCompare(String(b.createdAt)));
    const stories = list.map((s) => storyPublic(s, vdb, ctx.user.id));
    authors.push({
      author: { id: authorId, name: brief.name, photo: (acct && acct.photo) || photos[0] || null }, // [RP-V7.89] the FACE is user.photo — gallery[0] showed the old photo after an avatar pick
      iFollow: following.has(authorId),
      isSelf: authorId === ctx.user.id,
      allViewed: stories.every((s) => s.viewedByMe),
      latestAt: list[list.length - 1].createdAt,
      stories,
      _score:
        (following.has(authorId) ? 1000 : 0) +
        2.5 * fyDecayed(aff[authorId], now),
    });
  }
  authors.sort(
    (a, b) =>
      b._score - a._score || String(b.latestAt).localeCompare(String(a.latestAt))
  );
  for (const a of authors.slice(0, STORY_TRAY_MAX_AUTHORS)) delete a._score;
  const mePhotos = accountPhotos(ctx.user);
  res.json({
    ok: true,
    adultOnly: false,
    // [RP-V7.72] Capability flags from the account's adult status —
    // the client shows Post controls only when canPost, and routes
    // the viewer's Gift tap through the adult door gate when !canGift.
    // [RP-V7.74] canLike rides along: true for every account while
    // likes are all-ages.
    canPost: storyCanPost(ctx.user),
    canLike: storyCanLike(ctx.user),
    canGift: storyCanGift(ctx.user),
    me: { id: ctx.user.id, name: ctx.user.name, photo: ctx.user.photo || mePhotos[0] || null }, // [RP-V7.89] face, not gallery[0]
    authors: authors.slice(0, STORY_TRAY_MAX_AUTHORS),
  });
});
// Record a story view: the count rides the shared views system
// (deduped per viewer per ET day); viewedBy marks the ring seen.
app.post("/api/story/view", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  if (!storyCanView(ctx.user))
    return res.status(403).json({ ok: false, error: "Stories aren't available on this account" });
  const storyId = String((req.body || {}).storyId || "");
  const db = sweepStories();
  const s = db.stories[storyId];
  if (!s) return res.status(404).json({ ok: false, error: "Story not found" });
  const vdb = readViews();
  const out = recordMediaView(vdb, "story:" + s.id, "acct:" + ctx.user.id, viewDayKey());
  if (out.counted) writeViews(vdb);
  if (!Array.isArray(s.viewedBy)) s.viewedBy = [];
  if (!s.viewedBy.includes(ctx.user.id)) {
    s.viewedBy.push(ctx.user.id);
    if (s.viewedBy.length > 500) s.viewedBy = s.viewedBy.slice(-500);
    writeStories(db);
  }
  // [RP-V7.84] N3 (sweep G14): a FULL view (the client reports
  // full:true when the story plays to the end) also teaches the
  // shared For You profile — +3 to the author's affinity in the
  // VIEWER's record, the reel "complete" weight, at most once per
  // story per viewer per America/New_York day. The day stamp lives in
  // the viewer's own signal record (storySigDay, pruned to today on
  // write), so replays and tray-sitting can't farm it. Story LIKES
  // keep their own +4 in /api/story/like — this path never fires it.
  let storySig = false;
  if ((req.body || {}).full === true && s.authorId && s.authorId !== ctx.user.id) {
    try {
      const sig = readReelSignals();
      const rec = fyUserRec(sig, ctx.user.id, true);
      const today = viewDayKey();
      if (!rec.storySigDay) rec.storySigDay = {};
      if (rec.storySigDay[s.id] !== today) {
        rec.storySigDay[s.id] = today;
        for (const k of Object.keys(rec.storySigDay))
          if (rec.storySigDay[k] !== today) delete rec.storySigDay[k];
        fyBump(rec, s.authorId, 3, Date.now());
        writeReelSignals(sig);
        storySig = true;
      }
    } catch (e) { /* affinity bookkeeping must never break a view */ }
  }
  res.json({ ok: true, views: out.views, counted: out.counted, ...(storySig ? { sig: true } : {}) });
});
// Like / unlike a story (toggle). A fresh like bumps the shared
// author affinity by +4 — the settled For You like weight.
app.post("/api/story/like", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  // [RP-V7.74] Likes are ALL AGES (Branden, Oct 26, 2026: "Likes
  // to") — this gate was storyCanPost through V7.73; it now checks
  // storyCanLike, which follows viewing. Posting stays 18+.
  if (!storyCanLike(ctx.user))
    return res.status(403).json({ ok: false, error: "Liking stories is 18+" });
  const storyId = String((req.body || {}).storyId || "");
  const db = sweepStories();
  const s = db.stories[storyId];
  if (!s) return res.status(404).json({ ok: false, error: "Story not found" });
  if (!Array.isArray(s.likes)) s.likes = [];
  const ix = s.likes.indexOf(ctx.user.id);
  let liked;
  if (ix >= 0) {
    s.likes.splice(ix, 1);
    liked = false;
  } else {
    s.likes.push(ctx.user.id);
    liked = true;
    if (s.authorId !== ctx.user.id) {
      try {
        const sig = readReelSignals();
        const rec = fyUserRec(sig, ctx.user.id, true);
        fyBump(rec, s.authorId, 4, Date.now());
        writeReelSignals(sig);
      } catch (e) { /* affinity bookkeeping must never break a like */ }
    }
  }
  writeStories(db);
  res.json({ ok: true, likes: s.likes.length, likedByMe: liked });
});
// Delete one of my own stories (and its file).
app.delete("/api/story/:id", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  const db = readStories();
  const s = db.stories[String(req.params.id)];
  if (!s) return res.status(404).json({ ok: false, error: "Story not found" });
  if (s.authorId !== ctx.user.id)
    return res.status(403).json({ ok: false, error: "That's not your story" });
  if (s.file) fs.unlink(path.join(STORY_DIR, String(s.file)), () => {});
  delete db.stories[s.id];
  writeStories(db);
  res.json({ ok: true });
});

// ---------------------------------------------------------------------------
// [RP-V7.71] Open Plaza Feed (Branden, Oct 26: "make a feed available
// for random people to post anything and gifting likes follow and
// sharing available for that as well").
//
// The Feed is ACCOUNT state ("the brain in everything"): the store is
// feed.json beside the other data files, media files live under
// PHOTO_DIR/feed and ride the existing /photos static mount, so a post
// answers at /photos/feed/<file> on any device the member signs in
// on — never device-only.
//
//   { posts: { [postId]: { id, authorId, authorName, text, kind,
//        file, createdAt, likes: [accountId] } } }
//
// kind: "text" | "photo" | "video". Media rules match DM media
// exactly: photos JPG/PNG/WebP/GIF at most 10 MB (and through the same
// moderateImage safety check as profile photos and DM photos), videos
// MP4/WebM/MOV via REEL_VIDEO_TYPES at most 50 MB. Auth (and the age
// gate) run BEFORE multer, so a refused request never writes a file;
// every later failure unlinks the stored file.
//
// Ranking REUSES the one shared For You interest profile
// (reel-signals.json) — no second ranker: the base order is newest
// first, and each post's timestamp is lifted by the same affinity read
// Reels and Stories use (2.5 x decayed author affinity, fyDecayed)
// plus a follow bonus, the total lift capped at 24 hours so fresh
// posts still lead while authors a member engages with surface sooner.
//
// Likes live here (a set of account ids per post); a fresh like also
// bumps the shared author affinity by +4 — the settled For You weight
// for a like — exactly like story and reel likes.
//
// Gifting a post's author is NOT new money code: the client calls the
// existing openGiftSheet(authorId, authorName), which runs the money
// layer's ledger-first /api/money/gift path. Follow likewise calls
// the existing /api/social/follow, and share rides the existing share
// machinery (navigator.share with a clipboard fallback).
//
// AGE RULE — FINAL, Branden, Oct 26, 2026 ("under 18 is allowed to
// post anything get likes can share to" / "No gifting for under
// 18"): the Feed is SOCIAL, so viewing, posting and liking are ALL
// AGES behind the ONE constant below, which RP-V7.74 flips to
// all-ages semantics (FEED_ADULT_ONLY=false; V7.71 shipped it 18+,
// superseded). Gifting a post's author still rides
// POST /api/money/gift — since RP-V7.74 a gift with a teen on either
// side is CHARMS-ONLY there (charms move, no earnings), and buying /
// subscribing / cashing out stay 18+ server-locked — no money door
// opens here. Which screens a teen-LOCKED account may
// enter (the TEEN_ONLY_18 surface list) is a separate rule and is
// NOT changed by this build. Teen Hangout and Fellowship all-ages
// functions are untouched either way.
// ---------------------------------------------------------------------------
const FEED_ADULT_ONLY = false; // [RP-V7.74] THE Feed age flip point (server) — false = all ages (Branden, Oct 26, 2026)
const FEED_PHOTO_MAX = 10 * 1024 * 1024; // same cap as DM photos
const FEED_VIDEO_MAX = 50 * 1024 * 1024; // same cap as DM/reel/story video
const FEED_TEXT_MAX = 500;
const FEED_PAGE_MAX = 50;
const FEED_FILE =
  process.env.FEED_FILE || path.join(path.dirname(PHOTO_DIR), "feed.json");
const FEED_DIR = path.join(PHOTO_DIR, "feed");
fs.mkdirSync(FEED_DIR, { recursive: true });
function readFeed() {
  return storeReadJson(
    FEED_FILE,
    (d) => !!(d && d.posts && typeof d.posts === "object" && !Array.isArray(d.posts)),
    { posts: {} },
    "feed"
  );
}
function writeFeed(db) {
  storeWriteJson(FEED_FILE, db);
}
function feedAdultOk(user) {
  return !FEED_ADULT_ONLY || ageFromDob(user.dob) >= 18;
}
function feedPublic(ctx, p, following) {
  const brief = socialBrief(ctx.db, p.authorId);
  if (!brief) return null; // pending-deletion / gone authors don't show
  const acct = ctx.db.users.find((u) => u.id === p.authorId);
  const photos = acct ? accountPhotos(acct) : [];
  const likes = Array.isArray(p.likes) ? p.likes : [];
  return {
    id: p.id,
    author: { id: p.authorId, name: brief.name, photo: (acct && acct.photo) || photos[0] || null }, // [RP-V7.89] face, not gallery[0]
    text: p.text || "",
    kind: p.kind || (p.file ? "photo" : "text"),
    url: p.file ? "/photos/feed/" + p.file : null,
    createdAt: p.createdAt,
    likes: likes.length,
    likedByMe: likes.includes(ctx.user.id),
    iFollow: following ? following.has(p.authorId) : false,
    isSelf: p.authorId === ctx.user.id,
  };
}
const FEED_IMAGE_TYPES = ["image/jpeg", "image/png", "image/webp", "image/gif"];
const feedUpload = multer({
  storage: multer.diskStorage({
    destination: (req, file, cb) => cb(null, FEED_DIR),
    filename: (req, file, cb) => {
      const ext = (file.mimetype || "").startsWith("video/")
        ? (REEL_VIDEO_TYPES[file.mimetype] || "mp4")
        : extFor(file.mimetype);
      cb(null, `${Date.now()}-${crypto.randomBytes(6).toString("hex")}.${ext}`);
    },
  }),
  limits: { fileSize: FEED_VIDEO_MAX },
  fileFilter: (req, file, cb) => {
    const m = file.mimetype || "";
    if (FEED_IMAGE_TYPES.includes(m) || REEL_VIDEO_TYPES[m]) cb(null, true);
    else cb(new Error("Only photos (JPG, PNG, WebP, GIF) and videos (MP4, WebM, MOV) can be posted"));
  },
});
// Post to the Feed: text only (JSON), or text + one photo/video
// (multipart). Auth (and the age gate) run BEFORE multer, exactly
// like POST /api/dm/media; every later failure unlinks the file.
app.post("/api/feed/post",
  (req, res, next) => {
    const ctx = requireAccount(req, res);
    if (!ctx) return;
    if (!feedAdultOk(ctx.user))
      return res.status(403).json({ ok: false, error: "The Feed is 18+ right now" });
    req._feedCtx = ctx;
    next();
  },
  (req, res, next) => {
    if (!/^multipart\/form-data/i.test(String(req.get("content-type") || ""))) return next();
    feedUpload.single("media")(req, res, (err) => {
      if (err) {
        const tooBig = err && err.code === "LIMIT_FILE_SIZE";
        return res.status(tooBig ? 413 : 400).json({
          ok: false,
          error: tooBig ? "That file is too big — 50 MB max" : (err.message || "That file can't be posted"),
        });
      }
      next();
    });
  },
  async (req, res) => {
    const ctx = req._feedCtx;
    const fail = (status, error) => {
      if (req.file) fs.unlink(req.file.path, () => {});
      return res.status(status).json({ ok: false, error });
    };
    try {
      const text = String((req.body || {}).text || "").trim();
      if (text.length > FEED_TEXT_MAX)
        return fail(400, "Posts are " + FEED_TEXT_MAX + " characters max");
      if (!req.file && !text)
        return fail(400, "Write something, or add a photo or video");
      let kind = "text";
      if (req.file) {
        const isVideo = (req.file.mimetype || "").startsWith("video/");
        if (!isVideo && req.file.size > FEED_PHOTO_MAX)
          return fail(413, "That photo is too big — 10 MB max");
        if (!isVideo) {
          const publicUrl = `https://${req.get("host")}/photos/feed/${req.file.filename}`;
          const mod = await moderateImage(publicUrl);
          if (!mod.ok) {
            console.log("FEED PHOTO REJECTED:", ctx.user.id, mod.reason);
            return fail(422, "That photo didn't pass our safety check. Please try a different one.");
          }
        }
        kind = isVideo ? "video" : "photo";
      }
      const db = readFeed();
      const post = {
        id: crypto.randomBytes(8).toString("hex"),
        authorId: ctx.user.id,
        authorName: ctx.user.name,
        text,
        kind,
        file: req.file ? path.basename(req.file.path) : null,
        createdAt: new Date().toISOString(),
        likes: [],
      };
      db.posts[post.id] = post;
      writeFeed(db);
      const sdb = readSocial();
      const following = new Set(socialFollowingIds(sdb, ctx.user.id));
      res.json({ ok: true, post: feedPublic(ctx, post, following) });
    } catch (e) {
      console.log("FEED POST ERROR:", e.message);
      if (req.file) fs.unlink(req.file.path, () => {});
      return res.status(500).json({ ok: false, error: "That post didn't go up. Please try again." });
    }
  }
);
// The Feed itself: newest first, lifted by the shared For You author
// affinity (2.5 x decayed affinity + a follow bonus, lift capped at
// 24h) — the same philosophy as Reels and the Stories tray.
app.get("/api/feed", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  if (!feedAdultOk(ctx.user))
    return res.json({ ok: true, adultOnly: true, posts: [] });
  const limit = Math.max(1, Math.min(FEED_PAGE_MAX, parseInt(req.query.limit, 10) || 30));
  const db = readFeed();
  const sdb = readSocial();
  const following = new Set(socialFollowingIds(sdb, ctx.user.id));
  const sig = readReelSignals();
  const urec = fyUserRec(sig, ctx.user.id, false);
  const aff = (urec && urec.authorAff) || {};
  const now = Date.now();
  const scored = [];
  for (const p of Object.values(db.posts)) {
    if (!p || !p.authorId) continue;
    const pub = feedPublic(ctx, p, following);
    if (!pub) continue;
    // [RP-V7.89] the lift is now author affinity + STYLE affinity (from
    // the post's caption text), still capped at 24h total.
    const styleLift = urec ? 2.5 * fyStyleWeight(urec, styleKeysForCaption(p.text), now) : 0;
    const liftH = Math.max(0, Math.min(24,
      2.5 * fyDecayed(aff[p.authorId], now) + (following.has(p.authorId) ? 6 : 0) + styleLift));
    scored.push({ pub, _t: Date.parse(p.createdAt) + liftH * 3600000 });
  }
  // [RP-V7.89] Reposts surface to the reposter's FOLLOWERS in the Feed,
  // in reverse-chronological position by repost time (no ranking change),
  // carrying a "reposted" attribution the client renders.
  try {
    const rpDbF = readPhotoReposts();
    const byId = (uid) => ctx.db.users.find((u) => u.id === uid && !u.deletionAt);
    for (const r of listReels()) {
      if (!r || !Array.isArray(r.reposts)) continue;
      for (const rp of r.reposts) {
        if (!rp || rp.u === ctx.user.id || !following.has(rp.u)) continue;
        const by = byId(rp.u); if (!by) continue;
        const aKey = reelAuthorKeyFor(ctx.db, r);
        const aUser = aKey ? ctx.db.users.find((u) => u.id === aKey) : null;
        scored.push({ pub: { kind: "repost", id: "rp:reel:" + r.id + ":" + rp.u, repostBy: { id: rp.u, name: by.name }, repostedAt: rp.at || null, createdAt: rp.at || null, post: { kind: "reel", id: r.id, author: { id: aKey || null, name: (aUser && aUser.name) || r.author || "" }, url: "/reel-files/" + r.file, caption: r.caption || "" } }, _t: Date.parse(rp.at || "") || 0 });
      }
    }
    for (const pp of readPhotoPosts().posts) {
      const set = photoRepostSet(rpDbF, pp.id);
      for (const rp of set) {
        if (!rp || rp.u === ctx.user.id || !following.has(rp.u)) continue;
        const by = byId(rp.u); if (!by) continue;
        scored.push({ pub: { kind: "repost", id: "rp:photopost:" + pp.id + ":" + rp.u, repostBy: { id: rp.u, name: by.name }, repostedAt: rp.at || null, createdAt: rp.at || null, post: { kind: "photopost", id: pp.id, author: { id: pp.owner, name: pp.name || "" }, url: pp.photo, caption: pp.caption || "" } }, _t: Date.parse(rp.at || "") || 0 });
      }
    }
  } catch (e) { /* repost surfacing must never break the feed */ }
  scored.sort((a, b) => b._t - a._t);
  res.json({
    ok: true,
    adultOnly: false,
    me: { id: ctx.user.id, name: ctx.user.name },
    posts: scored.slice(0, limit).map((s) => s.pub),
  });
});
// Like / unlike a Feed post (toggle). A fresh like bumps the shared
// author affinity by +4 — the settled For You like weight.
app.post("/api/feed/like", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  if (!feedAdultOk(ctx.user))
    return res.status(403).json({ ok: false, error: "The Feed is 18+ right now" });
  const postId = String((req.body || {}).postId || "");
  const db = readFeed();
  const p = db.posts[postId];
  if (!p) return res.status(404).json({ ok: false, error: "Post not found" });
  if (!Array.isArray(p.likes)) p.likes = [];
  const ix = p.likes.indexOf(ctx.user.id);
  let liked;
  if (ix >= 0) {
    p.likes.splice(ix, 1);
    liked = false;
  } else {
    p.likes.push(ctx.user.id);
    liked = true;
    if (p.authorId !== ctx.user.id) {
      try {
        const sig = readReelSignals();
        const rec = fyUserRec(sig, ctx.user.id, true);
        fyBump(rec, p.authorId, 4, Date.now());
        fyBumpStyleKeys(rec, styleKeysForCaption(p.text), 4, Date.now()); // [RP-V7.89]
        writeReelSignals(sig);
      } catch (e) { /* affinity bookkeeping must never break a like */ }
    }
  }
  writeFeed(db);
  res.json({ ok: true, likes: p.likes.length, likedByMe: liked });
});
// Delete one of my own Feed posts (and its media file).
app.delete("/api/feed/:id", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  const db = readFeed();
  const p = db.posts[String(req.params.id)];
  if (!p) return res.status(404).json({ ok: false, error: "Post not found" });
  if (p.authorId !== ctx.user.id)
    return res.status(403).json({ ok: false, error: "That's not your post" });
  if (p.file) fs.unlink(path.join(FEED_DIR, String(p.file)), () => {});
  delete db.posts[p.id];
  writeFeed(db);
  res.json({ ok: true });
});

// [RP-V7.68] DM media (Branden, Oct 26: "when you click the message
// button have a way you can send pictures to them and videos").
// Files live under PHOTO_DIR/dm and ride the existing /photos static
// mount, so a stored file answers at /photos/dm/<file> — the same
// volume and serving path as profile photos and reels.
const DM_DIR = path.join(PHOTO_DIR, "dm");
fs.mkdirSync(DM_DIR, { recursive: true });
const DM_PHOTO_MAX = 10 * 1024 * 1024; // 10 MB per photo
const DM_VIDEO_MAX = 50 * 1024 * 1024; // 50 MB per video
const DM_IMAGE_TYPES = ["image/jpeg", "image/png", "image/webp", "image/gif"];
const dmUpload = multer({
  storage: multer.diskStorage({
    destination: (req, file, cb) => cb(null, DM_DIR),
    filename: (req, file, cb) => {
      const ext = (file.mimetype || "").startsWith("video/")
        ? (REEL_VIDEO_TYPES[file.mimetype] || "mp4")
        : extFor(file.mimetype);
      cb(null, `${Date.now()}-${crypto.randomBytes(6).toString("hex")}.${ext}`);
    },
  }),
  limits: { fileSize: DM_VIDEO_MAX },
  fileFilter: (req, file, cb) => {
    const m = file.mimetype || "";
    if (DM_IMAGE_TYPES.includes(m) || REEL_VIDEO_TYPES[m]) cb(null, true);
    else cb(new Error("Only photos (JPG, PNG, WebP, GIF) and videos (MP4, WebM, MOV) can be sent"));
  },
});
// Shared delivery for text AND media messages: get-or-create the
// thread, append, cap history, accept-on-reply, persist, count the
// send against the rate limit, and queue the offline alert.
function dmDeliver(ctx, other, msg) {
  const db = readDms();
  const key = dmThreadKey(ctx.user.id, other.id);
  let t = db.threads[key];
  const now = msg.at || new Date().toISOString();
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
  t.messages.push(msg);
  while (t.messages.length > 500) t.messages.shift();
  t.lastAt = now;
  // Replying to a first contact accepts the thread — same as Accept.
  if (t.startedBy !== ctx.user.id && !t.accepted) t.accepted = true;
  writeDms(db);
  noteDmSend(ctx.user.id);
  // [RP-V7.30] The message is stored and waits in the recipient's
  // inbox either way. If they have no live socket right now, also
  // queue an offline alert (deduped per sender per hour).
  if (!acctIsOnline(other.id))
    queueOfflineDmAlert(other.id, ctx.user.id, ctx.user.name);
  return msg;
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
  const msg = {
    id: crypto.randomBytes(8).toString("hex"),
    from: ctx.user.id,
    text,
    at: new Date().toISOString(),
  };
  dmDeliver(ctx, other, msg);
  res.json({ ok: true, message: msg });
});
// [RP-V7.68] Send a photo or video in a DM. Auth runs BEFORE multer
// so an unauthenticated request never writes a file; every later
// validation failure unlinks the stored file. Photos go through the
// same moderateImage safety check as profile photos.
app.post("/api/dm/media",
  (req, res, next) => {
    const ctx = requireAccount(req, res);
    if (!ctx) return;
    req._dmCtx = ctx;
    next();
  },
  (req, res, next) => {
    dmUpload.single("media")(req, res, (err) => {
      if (err) {
        const tooBig = err && err.code === "LIMIT_FILE_SIZE";
        return res.status(tooBig ? 413 : 400).json({
          ok: false,
          error: tooBig ? "That video is too big — 50 MB max" : (err.message || "That file can't be sent"),
        });
      }
      next();
    });
  },
  async (req, res) => {
    const ctx = req._dmCtx;
    const fail = (status, error) => {
      if (req.file) fs.unlink(req.file.path, () => {});
      return res.status(status).json({ ok: false, error });
    };
    try {
      if (!req.file)
        return res.status(400).json({ ok: false, error: "No photo or video received" });
      if (dmRateLimited(ctx.user.id))
        return fail(429, "You're sending messages too fast — slow down a moment");
      const toId = String((req.body || {}).to || "");
      const other = ctx.db.users.find((u) => u.id === toId);
      if (!other) {
        if (isTombstonedAccount(toId))
          return fail(410, "This account no longer exists — this conversation is read-only now.");
        return fail(404, "Account not found");
      }
      if (other.deletionAt)
        return fail(410, "This account no longer exists — this conversation is read-only now.");
      if (other.id === ctx.user.id)
        return fail(400, "You can't message yourself");
      const db = readDms();
      if (dmEitherBlocked(db, ctx.user.id, other.id))
        return fail(403, "Messages are blocked between you and this person");
      const isVideo = (req.file.mimetype || "").startsWith("video/");
      if (!isVideo && req.file.size > DM_PHOTO_MAX)
        return fail(413, "That photo is too big — 10 MB max");
      const publicUrl = `https://${req.get("host")}/photos/dm/${req.file.filename}`;
      if (!isVideo) {
        const mod = await moderateImage(publicUrl);
        if (!mod.ok) {
          console.log("DM PHOTO REJECTED:", ctx.user.id, mod.reason);
          return fail(422, "That photo didn't pass our safety check. Please try a different one.");
        }
      }
      const msg = {
        id: crypto.randomBytes(8).toString("hex"),
        from: ctx.user.id,
        text: isVideo ? "🎥 Video" : "📷 Photo",
        media: { kind: isVideo ? "video" : "photo", url: publicUrl },
        at: new Date().toISOString(),
      };
      dmDeliver(ctx, other, msg);
      res.json({ ok: true, message: msg });
    } catch (e) {
      console.log("DM MEDIA ERROR:", e.message);
      if (req.file) fs.unlink(req.file.path, () => {});
      return res.status(500).json({ ok: false, error: "That file didn't send. Please try again." });
    }
  }
);
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
// email, phone and DOB are NEVER included. [RP-V7.50] `photo` is the
// account's stored photo (bound at upload); when the account has none,
// it falls back to the photoUrl of a currently-connected player whose
// display name UNIQUELY matches the account name — the same
// name-matching the follow system already uses — else null.
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
      // [RP-V7.50] the account's stored photo wins; the live-player
      // name match remains as the fallback for accounts without one.
      photo: u.photo || (nameCount[k] === 1 ? photoByName[k] || null : null),
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
  // [RP-V7.55] The one-alert-per-sender-per-hour rule also honors the
  // DELIVERED log: without it, an alert that drained instantly would
  // let the next DM re-alert a minute later (a text per message).
  const recent = (a) =>
    a &&
    a.kind === "dm" &&
    a.toAccountId === toAccountId &&
    a.fromAccountId === fromAccountId &&
    now - Date.parse(a.at || "") < 3600 * 1000;
  const dupe =
    db.alerts.some(recent) || (db.sentLog || []).some(recent);
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
// [RP-V7.55] OFFLINE ALERT TRANSPORT — WIRED (was a no-op stub through
// V7.54). sendOfflineAlerts() drains notify-outbox.json: entries are
// grouped per recipient into ONE digest per drain ("You have new
// Rizz Plaza messages from X"), the recipient's email/phone are
// looked up in accounts.json (server-side ONLY), and the digest goes
// out on every configured channel (Resend email + Twilio SMS —
// Branden's pick: both). Entries are removed only when the recipient
// was reached on at least one configured channel; failures stay
// queued for the next drain. Entries for accounts that no longer
// exist (or are pending deletion) are dropped as undeliverable.
// NOTIFY_DRAIN_MS overrides the cadence for tests; production 60 s.
// ---------------------------------------------------------------------------
let notifyDrainRunning = false;
async function sendOfflineAlerts() {
  if (notifyDrainRunning) return 0;
  const emailReady = notifyEmailReady();
  const smsReady = notifySmsReady();
  if (!emailReady && !smsReady) return 0; // no provider configured
  const db = readNotifyOutbox();
  if (!db.alerts.length) return 0;
  notifyDrainRunning = true;
  try {
    const keyOf = (a) => a.toAccountId + "|" + a.fromAccountId + "|" + a.at;
    const byRecipient = new Map();
    for (const a of db.alerts) {
      if (!a || !a.toAccountId) continue;
      if (!byRecipient.has(a.toAccountId)) byRecipient.set(a.toAccountId, []);
      byRecipient.get(a.toAccountId).push(a);
    }
    const adb = readAccounts();
    const deliveredKeys = new Set();
    let sentCount = 0;
    for (const [toId, entries] of byRecipient) {
      const u = adb.users.find((x) => x.id === toId);
      if (!u || u.deletionAt) {
        for (const e of entries) deliveredKeys.add(keyOf(e)); // undeliverable — drop
        continue;
      }
      const names = [...new Set(entries.map((e) => e.fromName || "Someone"))];
      const who =
        names.length === 1
          ? names[0]
          : names.length === 2
            ? names[0] + " and " + names[1]
            : names[0] + " and " + (names.length - 1) + " others";
      let reached = false;
      if (emailReady && u.email) {
        const ok = await notifySendEmail(
          u.email,
          "You have new Rizz Plaza messages 💬",
          "Hi " + (u.name || "there") + " — you have new Rizz Plaza messages from " + who + ".\n\nOpen the Plaza to read and reply: https://rizzplaza.com\n\n— The Rizz Plaza team"
        );
        if (ok) reached = true;
      }
      if (smsReady && u.phone) {
        const ok = await notifySendSms(
          u.phone,
          "Rizz Plaza 💬 You have new messages from " + who + " — open https://rizzplaza.com to reply."
        );
        if (ok) reached = true;
      }
      if (reached) {
        for (const e of entries) deliveredKeys.add(keyOf(e));
        sentCount++;
      }
    }
    if (deliveredKeys.size) {
      const fresh = readNotifyOutbox();
      const deliveredEntries = fresh.alerts.filter((a) => deliveredKeys.has(keyOf(a)));
      fresh.alerts = fresh.alerts.filter((a) => !deliveredKeys.has(keyOf(a)));
      // [RP-V7.55] Delivered DM alerts leave a 1-hour tombstone so the
      // per-sender cooldown survives delivery (see queueOfflineDmAlert).
      const cutoff = Date.now() - 2 * 3600 * 1000;
      fresh.sentLog = (fresh.sentLog || [])
        .concat(deliveredEntries.filter((a) => a.kind === "dm"))
        .filter((a) => Date.parse(a.at || "") > cutoff)
        .slice(-500);
      writeNotifyOutbox(fresh);
    }
    if (sentCount)
      console.log("[notify] offline alerts delivered to " + sentCount + " member(s)");
    return sentCount;
  } catch (e) {
    return 0;
  } finally {
    notifyDrainRunning = false;
  }
}
const NOTIFY_DRAIN_MS = Math.max(1000, Number(process.env.NOTIFY_DRAIN_MS) || 60 * 1000);
const notifyAlertTimer = setInterval(() => {
  try {
    sendOfflineAlerts();
  } catch (e) {}
}, NOTIFY_DRAIN_MS);
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
  heartburst: 60, thunderbolt: 75, fingerheart: 99, kiss: 100,
  fireworks: 200, motorcycle: 300, goldgloves: 450, sportscar: 500,
  loveballoon: 600, guardianpalm: 700, airplane: 800, moneygun: 999,
  castle: 1000, volcano: 2000, lion: 2500, dragon: 3000, meteor: 4000,
  whale: 4500, galaxy: 5000, starsurge: 5500, diamonds: 6000,
  rocket: 7500, ferriswheel: 9900, jet: 10000, yacht: 15000,
  phoenix: 25000, universe: 50000,
  // [RP-V7.82] +5 gifts (heartburst/thunderbolt small, goldgloves/
  // guardianpalm medium, starsurge big) — ids + prices mirror the
  // client's GIFT_SHOP exactly; the catalog is now 33 gifts.
};
function emptyMoney() {
  return {
    balances: {},
    earnings: {},
    premium: {},
    cashouts: [],
    txlog: [],
    processed: {},
    giftIdem: {}, // [RP-V7.52] gift idempotency keys -> original responses
    giftBals: {}, // [RP-V7.74] under-18 earned/won gift balance (charms) — see giftBalMirrorWin
    auctionSettlements: {}, // [RP-V7.80] auction settlement records by auctionId (full-scan F2) — recorded outcomes are final; [RP-V7.89] insufficient-charms failures are never recorded (FAIL-1)
  };
}
function readMoney() {
  // [RP-V7.52] hardened read (audit C5): a corrupt money.json
  // restores from money.json.bak instead of silently wiping every
  // balance and letting the next write destroy the original.
  const d = storeReadJson(
    MONEY_FILE,
    (x) =>
      !!(
        x &&
        x.balances && typeof x.balances === "object" && !Array.isArray(x.balances) &&
        x.earnings && typeof x.earnings === "object" && !Array.isArray(x.earnings) &&
        x.premium && typeof x.premium === "object" && !Array.isArray(x.premium) &&
        Array.isArray(x.cashouts) && Array.isArray(x.txlog)
      ),
    emptyMoney(),
    "money"
  );
  if (!d.processed || typeof d.processed !== "object" || Array.isArray(d.processed))
    d.processed = {};
  if (!d.giftIdem || typeof d.giftIdem !== "object" || Array.isArray(d.giftIdem))
    d.giftIdem = {};
  if (!d.giftBals || typeof d.giftBals !== "object" || Array.isArray(d.giftBals))
    d.giftBals = {};
  if (!d.auctionSettlements || typeof d.auctionSettlements !== "object" || Array.isArray(d.auctionSettlements))
    d.auctionSettlements = {};
  // [RP-V7.81] owner sales board: the pushed Magniphiscents store total
  // ({ storeCents, at } from POST /api/owner/store-sales) or null until
  // the first push lands — never a fabricated number.
  if (d.ownerStore !== null && (typeof d.ownerStore !== "object" || Array.isArray(d.ownerStore))) d.ownerStore = null;
  return d;
}
function writeMoney(db) {
  storeWriteJson(MONEY_FILE, db);
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
// [RP-V7.74] TEEN GIFT BALANCE (giftBals, charms — Branden, Oct 26,
// 2026: "It's teen gifting free but they have to earn and win it").
// An under-18 account gifts for FREE: a teen's gift never spends
// their main charm balance and never costs money — it spends ONLY
// this earned/won balance. giftBals fills EXCLUSIVELY by mirroring
// WIN/PRIZE charm credits to an under-18 account (pot-win and
// dailypot-win today; any future giveaway charm credit should call
// this same helper). Charm-pack purchases (a teen can't check out
// anyway), received gifts, pot seed refunds/remainders and every
// other credit do NOT fill it. Adults never use it: the mirror is a
// no-op for 18+ accounts, and the gift handler only spends from it
// for under-18 senders.
function giftBalMirrorWin(mdb, user, amount) {
  if (!user || !(amount > 0)) return;
  if (ageFromDob(user.dob) >= 18) return;
  if (!mdb.giftBals || typeof mdb.giftBals !== "object") mdb.giftBals = {};
  mdb.giftBals[user.id] = (mdb.giftBals[user.id] || 0) + amount;
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
// [RP-V7.52] One shared serialization for every money mutation
// (audit C1/C6/C7/H7): the gift POST, pot open/topup/draw/cancel/
// join, cash-out and the Daily Pot settlement all run strictly
// one-at-a-time through this queue, so a check-and-debit can never
// interleave with another mutation across an await, and a retried
// request is evaluated against the state the first attempt left
// behind. Handlers wrapped here MUST NOT call withMoneyLock again
// (the Daily Pot settle helpers below deliberately never do).
let moneyQueue = Promise.resolve();
function withMoneyLock(fn) {
  const run = moneyQueue.then(() => fn());
  moneyQueue = run.then(
    () => undefined,
    () => undefined
  );
  return run;
}
function lockedHandler(label, fn) {
  return (req, res) => {
    withMoneyLock(() => fn(req, res)).catch((e) => {
      console.error("[money-lock] " + label + " failed:", e && e.message);
      if (!res.headersSent)
        res.status(500).json({ ok: false, error: "server-error" });
    });
  };
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
    // [RP-V7.63] Explicit timeout: without it a hung Stripe call waits
    // out undici's ~300s default while the client gives up at 9–12s and
    // the member stares at a stuck "Opening Stripe…" — a timeout makes
    // the failure surface as the 502 "stripe-error" the routes already
    // return and the client already handles.
    signal: AbortSignal.timeout(15000),
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
    giftBal: (db.giftBals && db.giftBals[user.id]) || 0, // [RP-V7.74] teen earned/won gift balance (0 for adults)
    earnings: {
      availableCents: e.availableCents,
      heldCents,
      held: e.held,
      nextUnlockAt,
      totalEarnedCents: e.totalEarnedCents,
    },
    premium: moneyPremiumState(db, user.id),
    dailyClaim: claimStatePayload(user), // [RP-V7.76] the unified claim gate + streak (FIX-2): every device renders the same claimed state and streak from this
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
  // [RP-V7.74] Buying charms is 18+ on the SERVER (Branden, Oct 26,
  // 2026: "No gifting for under 18" — no money door stays open to
  // under-18 accounts). Same ageFromDob determination first used in
  // V7.73's gift gate, placed BEFORE the pack lookup, the Stripe-config
  // check and any session creation, so an under-18 attempt creates
  // nothing and reaches no Stripe call.
  if (ageFromDob(ctx.user.dob) < 18)
    return res.status(403).json({ ok: false, error: "Buying charms is 18+" });
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
  // [RP-V7.74] Subscribing is 18+ on the SERVER — its own handler
  // (it does NOT share the /api/money/checkout handler), so it gets
  // the same ageFromDob gate, before the plan lookup, the Stripe-
  // config check and any session creation.
  if (ageFromDob(ctx.user.dob) < 18)
    return res.status(403).json({ ok: false, error: "Subscribing is 18+" });
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
// Send a gift, ledger-first: the sender's charms are debited HERE —
// the room animation/proto the client plays afterwards is just the
// show; this is the money. Adult→adult: the recipient's EARNINGS are
// credited (70% split). If EITHER side is under 18 the gift is
// CHARMS-ONLY (RP-V7.74, see the branch below): the recipient's charm
// balance is credited instead and no earnings exist.
app.post("/api/money/gift", lockedHandler("gift", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  // [RP-V7.74] No blanket age 403 here anymore. RP-V7.73 locked this
  // endpoint to 18+ outright; Branden's later rulings the same day
  // (Oct 26, 2026: "They can go live and gift to but they gifting is
  // free no money in it only charms" + "It's teen gifting free but
  // they have to earn and win it") supersede it: an under-18 account
  // MAY gift — the gift runs CHARMS-ONLY and a teen sender pays from
  // their earned/won gift balance, never their main balance (branch
  // after the recipient is resolved). What stays 18+ server-locked
  // is real money: checkout / subscribe / cashout (below) — no money
  // enters or leaves a teen account in either direction.
  const b = req.body || {};
  // [RP-V7.52] Idempotency (audit C6): the client stamps each gift
  // ATTEMPT with a key; a retry of the same attempt (double-tap,
  // network retry) returns the original result and never re-charges.
  const idemKey = String(b.idem || "").slice(0, 64);
  const idemStoreKey = idemKey ? ctx.user.id + ":" + idemKey : null;
  if (idemStoreKey) {
    const seen = readMoney().giftIdem[idemStoreKey];
    if (seen && seen.response)
      return res.json(Object.assign({}, seen.response, { deduped: true }));
  }
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
  // [RP-V7.74] TEEN ECONOMY — CHARMS ONLY, SPENT FROM EARNINGS/WINS.
  // If the sender OR the recipient is under 18, the gift moves
  // charms and ONLY charms: the recipient's spendable CHARM balance
  // is credited the gift's cost and NO earnings are created (no
  // availableCents, no held entry, no totalEarnedCents; the tx pair
  // records cents: 0 / cut: 0, so no money figure anywhere moves).
  // The 70% money split applies ONLY when both sides are adults —
  // that path is byte-for-byte the RP-V7.73 behavior.
  // SPEND SOURCE (Branden's final refinement, Oct 26, 2026: "It's
  // teen gifting free but they have to earn and win it"): an
  // under-18 SENDER never spends their main charm balance — the
  // gift is FREE to them and is paid out of their earned/won gift
  // balance (giftBals, filled only by win/prize credits — see
  // giftBalMirrorWin). An adult sender pays from the main balance
  // exactly as before, even when the recipient is a teen.
  const senderTeen = ageFromDob(ctx.user.dob) < 18;
  const charmsOnly = senderTeen || ageFromDob(recipient.dob) < 18;
  let giftBal = (db.giftBals && db.giftBals[ctx.user.id]) || 0;
  if (senderTeen) {
    if (giftBal < cost)
      return res.status(400).json({
        ok: false,
        error: "insufficient-charms",
        message: "Earn or win charms to gift",
        balance,
        giftBal,
        needed: cost,
      });
  } else if (balance < cost) {
    return res.status(400).json({
      ok: false,
      error: "insufficient-charms",
      balance,
      needed: cost,
    });
  }
  if (senderTeen) {
    giftBal -= cost;
    db.giftBals[ctx.user.id] = giftBal;
  } else {
    db.balances[ctx.user.id] = balance - cost;
  }
  let giftValueCents = 0;
  let hostShare = 0;
  let platformCut = 0;
  let held = false;
  if (charmsOnly) {
    db.balances[recipient.id] = (db.balances[recipient.id] || 0) + cost;
  } else {
    giftValueCents = cost * CHARM_CENT_VALUE;
    hostShare = Math.floor((giftValueCents * GIFT_HOST_PCT) / 100);
    platformCut = giftValueCents - hostShare;
    const earn = moneyEarningsFor(db, recipient.id);
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
  }
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
  const giftResponse = {
    ok: true,
    balance: db.balances[ctx.user.id],
    charged: cost,
    recipient: { id: recipient.id, name: recipient.name },
    hostShareCents: hostShare,
    held,
    // [RP-V7.74] Additive fields (older clients ignore them): a
    // charms-only gift reports hostShareCents 0 and the charm amount
    // the recipient's balance was credited; giftBal is the sender's
    // post-gift earned/won gift balance (teen spend source — for an
    // adult sender it simply reports their stored value, unused).
    charmsOnly,
    recipientCharms: charmsOnly ? cost : 0,
    giftBal,
  };
  // [RP-V7.52] The idempotency record lands in the SAME write as
  // the debit itself, so a retry can never slip between the charge
  // and its record (audit C6).
  if (idemStoreKey) {
    db.giftIdem[idemStoreKey] = {
      at: new Date().toISOString(),
      response: giftResponse,
    };
    const idemKeys = Object.keys(db.giftIdem);
    if (idemKeys.length > 400) {
      idemKeys.sort((a, b2) =>
        String(db.giftIdem[a].at).localeCompare(String(db.giftIdem[b2].at))
      );
      for (let i = 0; i < idemKeys.length - 400; i++)
        delete db.giftIdem[idemKeys[i]];
    }
  }
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
  // grows the SENDER's class Daily Pot by 2% of its charm value
  // (platform match, capped per pool) — a gift can feed a live pot
  // AND its own class's Daily Pot; both matches are platform-side
  // and the split above is final. [RP-V7.77]
  try {
    dailyPotOnGift(cost, senderTeen ? "teen" : "adult");
  } catch (e) { /* daily pot bookkeeping must never break a gift */ }
  console.log(
    "[money] gift", giftId, cost, "charms:", ctx.user.name, "->", recipient.name,
    "| host", hostShare, "c", held ? "(held)" : "", "| cut", platformCut, "c",
    charmsOnly ? "| CHARMS-ONLY (teen involved)" : ""
  );
  res.json(giftResponse);
}));
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
// [RP-V7.52] REMOVED: POST /api/money/auction-earning (audit C2
// family). The route let any signed-in caller credit their own
// earnings from a CLIENT-CHOSEN grossCents — an unbounded self-mint
// feeding the (server-computed) cash-out. No client build calls it
// (verified against the V7.49/V7.51 clients); auction settlement
// stays client-local until the Stripe wiring lands, at which point
// recordAuctionEarning is called from a server-verified settle path
// with a server-known amount — never from a request body.
// [RP-V7.80] That settle path now exists (full-scan F2):
// settleAuctionMoney below. It honors the C2 lesson in both
// directions — earnings are credited ONLY against an equal charm
// debit taken in the same locked mutation, and on the HTTP path
// the debit can only ever come out of the authenticated caller's
// own balance.
// ---------------------------------------------------------------------------
// Settle ONE finished auction as a TRANSFER, never a mint:
//   - Client auctions bid in dollars; settlement is in CHARMS at
//     100 charms = $1 of bid (bidCharms = round(winningBid * 100)).
//   - The winner's charm balance is debited the full bidCharms.
//   - The host is credited via recordAuctionEarning (grossCents =
//     bidCharms numerically — 100 charms = $1 = 100 cents at
//     CHARM_CENT_VALUE 1): floor(90%) of the bid value lands as
//     host EARNINGS, so the credit is backed by the debit and can
//     never exceed 90% of it; the platform's 10% is the difference.
//   - Both parties must be existing ADULT accounts, winner ≠ host,
//     amount > 0. A teen on either side, a self-win, an unknown
//     account or a bad amount refuses with NOTHING moved.
//   - Insufficient winner balance fails cleanly: no debit, no
//     credit — and [RP-V7.89] the failure is NOT recorded, so it
//     never blocks a later retry once the winner tops up (FAIL-1).
//   - IDEMPOTENT by auctionId: every RECORDED outcome (settled, or
//     a deterministic refusal) is final; later calls return that
//     record with deduped:true and move nothing.
// Runs inside the money lock (callers wrap it); mutates mdb — the
// caller writes it. adb is an accounts-db snapshot for the
// existence/class checks.
function settleAuctionMoney(adb, mdb, opts) {
  const auctionId = String((opts && opts.auctionId) || "").slice(0, 80);
  if (!mdb.auctionSettlements || typeof mdb.auctionSettlements !== "object")
    mdb.auctionSettlements = {};
  const prior = mdb.auctionSettlements[auctionId];
  // [RP-V7.89] FAIL-1: a prior insufficient-charms record (only
  // writable by older builds — V7.89 never persists one) does NOT
  // dedupe: the retry re-runs against the winner's current balance
  // and supersedes it. Any other recorded outcome stays final.
  if (prior && !(prior.ok === false && prior.error === "insufficient-charms"))
    return Object.assign({}, prior, { deduped: true });
  const winnerId = String((opts && opts.winnerId) || "");
  const hostId = String((opts && opts.hostId) || "");
  const bidDollars = Number(opts && opts.winningBid);
  const bidCharms = Math.round(bidDollars * 100);
  const record = (fields) => {
    const rec = Object.assign(
      {
        ok: false,
        auctionId,
        winnerId,
        hostId,
        bidDollars: isFinite(bidDollars) ? bidDollars : 0,
        bidCharms: isFinite(bidCharms) ? bidCharms : 0,
        at: new Date().toISOString(),
      },
      fields
    );
    // [RP-V7.89] FAIL-1: insufficient-charms failures are returned
    // to the caller but never persisted — persisting one cached the
    // failure forever and that auctionId could never settle.
    if (!(rec.ok === false && rec.error === "insufficient-charms")) {
      mdb.auctionSettlements[auctionId] = rec;
      // Same 400-record cap discipline as giftIdem.
      const keys = Object.keys(mdb.auctionSettlements);
      if (keys.length > 400) {
        keys.sort((a, b2) =>
          String(mdb.auctionSettlements[a].at).localeCompare(
            String(mdb.auctionSettlements[b2].at)
          )
        );
        for (let i = 0; i < keys.length - 400; i++)
          delete mdb.auctionSettlements[keys[i]];
      }
    }
    return Object.assign({}, rec);
  };
  const winner = adb.users.find((u) => u.id === winnerId);
  const host = adb.users.find((u) => u.id === hostId);
  if (!winner || !host) return record({ ok: false, error: "account-not-found" });
  if (winnerId === hostId) return record({ ok: false, error: "self-win" });
  if (ageFromDob(winner.dob) < 18 || ageFromDob(host.dob) < 18)
    return record({ ok: false, error: "teen-party" });
  if (!(bidCharms > 0)) return record({ ok: false, error: "bad-amount" });
  const balance = mdb.balances[winnerId] || 0;
  if (balance < bidCharms)
    return record({
      ok: false,
      error: "insufficient-charms",
      balance,
      needed: bidCharms,
    });
  mdb.balances[winnerId] = balance - bidCharms;
  const { hostShare, cut } = recordAuctionEarning(mdb, hostId, bidCharms, auctionId);
  moneyTx(mdb, {
    type: "auction-paid",
    from: winnerId,
    to: hostId,
    charms: bidCharms,
    cents: bidCharms,
    cut,
    ref: auctionId,
  });
  return record({
    ok: true,
    hostShareCents: hostShare,
    cutCents: cut,
    winnerBalance: mdb.balances[winnerId],
  });
}
// [RP-V7.80] The client (rpWn) settle path — account auth only, and
// the winner is ALWAYS the authenticated caller: a settle request
// can spend the caller's own charms to pay a host, but it can never
// name a third-party winner and drain them. The socket auction
// path settles inside endAuction with server-known identities and
// never comes through here.
app.post("/api/money/auction-settle", lockedHandler("auction-settle", (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  if (isPendingDeletion(ctx.user))
    return res
      .status(403)
      .json({ ok: false, error: "This account is scheduled for deletion" });
  const b = req.body || {};
  const auctionId = String(b.auctionId || "").trim().slice(0, 80);
  const hostId = String(b.hostId || "").trim().slice(0, 64);
  const winningBid = Number(b.winningBid);
  if (!auctionId || !hostId || !isFinite(winningBid))
    return res.status(400).json({
      ok: false,
      error: "auctionId, hostId and winningBid are required",
    });
  const mdb = readMoney();
  const result = settleAuctionMoney(ctx.db, mdb, {
    auctionId,
    winnerId: ctx.user.id,
    hostId,
    winningBid,
  });
  writeMoney(mdb);
  if (result.ok) return res.json(result);
  const status =
    result.error === "teen-party"
      ? 403
      : result.error === "account-not-found"
        ? 404
        : 400;
  return res.status(status).json(result);
}));
// ---------------------------------------------------------------------------
// [RP-V7.81] OWNER-ONLY SALES BOARD (Branden, Oct 26, 2026: "a sales
// mark list on my page but I can only see it" + "show sales from
// everything broken down" + the milestone watch's $10K → $3M ladder).
// GET /api/owner/sales answers ONLY for the owner: the account whose
// id equals env OWNER_ACCOUNT_ID when set, otherwise the
// earliest-created account in the accounts store (the platform's
// first member). Every other caller — other accounts AND guests —
// gets a flat 404: for them this endpoint does not exist. The totals
// are computed on the fly from the money ledger's transaction log
// (moneyTx appends one entry per money event):
//   charmPacksCents   — "purchase" tx (cents = the pack price paid)
//   premiumSubsCents  — "premium" + "premium-renew" tx (cents paid)
//   giftsVolumeCents  — "gift-sent" tx (cents = the gift's dollar
//                       value; volume across ALL age classes — it is
//                       volume, not earnings, so charms-only teen
//                       gifts count at face value like adult gifts)
//   auctionsVolumeCents — "auction-paid" tx (cents = the settled
//                       winning bid in charms at 100 = $1, matched by
//                       the "auction-earned" settlement record)
//   storeCents        — the Magniphiscents store total, which this
//                       server cannot read: it is PUSHED in via
//                       POST /api/owner/store-sales and stays null
//                       until the first push lands. Never invented.
// LIMITATION (documented in BUILD-NOTES): the tx log is capped at
// 5,000 entries (moneyTx shifts the oldest off), so on a very busy
// Plaza these "all-time" stream totals are exact only back to the
// oldest retained entry.
// ---------------------------------------------------------------------------
function rpOwnerUserId(adb) {
  const want = String(process.env.OWNER_ACCOUNT_ID || "").trim();
  if (want) {
    const u = (adb.users || []).find((x) => x && x.id === want);
    if (u) return u.id;
  }
  let best = null, bestT = Infinity;
  for (const u of adb.users || []) {
    if (!u || !u.id) continue;
    const t = Date.parse(u.createdAt);
    const tt = isFinite(t) ? t : Infinity;
    if (tt < bestT) { bestT = tt; best = u; }
  }
  return best ? best.id : null;
}
function rpSalesStreams(mdb) {
  let charmPacksCents = 0, premiumSubsCents = 0, giftsVolumeCents = 0, auctionsVolumeCents = 0;
  for (const tx of mdb.txlog || []) {
    if (!tx || typeof tx !== "object") continue;
    const c = Math.round(Number(tx.cents) || 0);
    if (tx.type === "purchase") charmPacksCents += c;
    else if (tx.type === "premium" || tx.type === "premium-renew") premiumSubsCents += c;
    else if (tx.type === "gift-sent") giftsVolumeCents += c;
    else if (tx.type === "auction-paid") auctionsVolumeCents += c;
  }
  return { charmPacksCents, premiumSubsCents, giftsVolumeCents, auctionsVolumeCents };
}
app.get("/api/owner/sales", (req, res) => {
  const adb = readAccounts();
  const user = accountForToken(adb, req);
  const ownerId = rpOwnerUserId(adb);
  if (!user || !ownerId || user.id !== ownerId) return res.status(404).json({ ok: false, error: "not-found" });
  const mdb = readMoney();
  const s = rpSalesStreams(mdb);
  const storeCents = mdb.ownerStore && isFinite(Number(mdb.ownerStore.storeCents)) ? Math.round(Number(mdb.ownerStore.storeCents)) : null;
  const storeAsOf = storeCents === null ? null : (mdb.ownerStore.at || null);
  const totalCents = s.charmPacksCents + s.premiumSubsCents + s.giftsVolumeCents + s.auctionsVolumeCents + (storeCents || 0);
  const stepDollars = 10000, capDollars = 3000000;
  const totalDollars = totalCents / 100;
  const crossed = totalDollars >= stepDollars ? Math.min(capDollars, Math.floor(totalDollars / stepDollars) * stepDollars) : 0;
  const next = crossed >= capDollars ? null : crossed + stepDollars;
  res.json({
    ok: true,
    totalCents,
    streams: {
      charmPacksCents: s.charmPacksCents,
      premiumSubsCents: s.premiumSubsCents,
      giftsVolumeCents: s.giftsVolumeCents,
      auctionsVolumeCents: s.auctionsVolumeCents,
      storeCents,
      storeAsOf,
    },
    marks: { step: stepDollars, cap: capDollars, crossed, next },
  });
});
app.post("/api/owner/store-sales", lockedHandler("owner-store-sales", (req, res) => {
  const want = String(process.env.OWNER_PUSH_SECRET || "");
  // Disabled entirely (404) until the push secret is configured.
  if (!want) return res.status(404).json({ ok: false, error: "not-found" });
  const body = req.body || {};
  if (String(body.secret || "") !== want) return res.status(404).json({ ok: false, error: "not-found" });
  const totalCents = Number(body.totalCents);
  if (!isFinite(totalCents) || totalCents < 0) return res.status(400).json({ ok: false, error: "bad-total" });
  const mdb = readMoney();
  mdb.ownerStore = { storeCents: Math.round(totalCents), at: new Date().toISOString() };
  writeMoney(mdb);
  res.json({ ok: true, storeCents: mdb.ownerStore.storeCents, at: mdb.ownerStore.at });
}));
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
app.post("/api/money/cashout", lockedHandler("cashout", async (req, res) => {
  const ctx = requireAccount(req, res);
  if (!ctx) return;
  // [RP-V7.74] Cashing out is 18+ on the SERVER — the same ageFromDob
  // gate first used in V7.73's gift gate, placed BEFORE the ledger is
  // read, so an under-18 attempt reserves nothing and changes no state.
  if (ageFromDob(ctx.user.dob) < 18)
    return res.status(403).json({ ok: false, error: "Cashing out is 18+" });
  // [RP-V7.52] Server-computed cash-out, serialized (audit C2/H6):
  // the request carries NO amounts — the server reads a FRESH ledger
  // inside the money lock, matures holds, enforces the $20 minimum,
  // the 25c fee and one cash-out per day, and reserves the full
  // available balance. Nothing the client sends can change the sum.
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
}));
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

// [RP-V7.52] Server-side adult class (audit H1): Christian
// Fellowship ("faith") and Teen Hangout ("teen") are the ONLY
// all-ages socket rooms — every other room (themed rooms, state
// rooms, Chaos) is an 18+ area. [RP-V7.75] ONE carve-out was added
// later under Branden's teen model: the Live Stage and personal
// live rooms admit verified TEEN-class sockets too (see
// socketMayEnterRoom below). A socket is adult-class only when its acct-presence was
// verified against a session token AND that account's DOB is 18+
// (accounts are 18+ by the sign-up rule; the class is computed
// from the verified record, never from anything a client claims).
const ALL_AGES_ROOMS = new Set(["faith", "teen"]);
function roomNeedsAdult(room) {
  return !ALL_AGES_ROOMS.has(room);
}
function socketIsAdult(socket) {
  return !!(
    socket &&
    socket.data &&
    socket.data.accountId &&
    socket.data.adultClass
  );
}
// [RP-V7.75] THE TEEN BUILD — live rooms are the carve-out
// (Branden's teen model, Oct 26, 2026: "They can go live"): the Live
// Stage ("live-stage") and personal live rooms ("live-<key>") are
// open to SIGNED-IN under-18 accounts as viewers and as hosts. A
// socket is teen-class when its acct-presence was verified against a
// session token AND that account's DOB is under 18 — computed from
// the verified record, never from anything a client claims. Every
// other 18+ room class (dating rooms, state rooms, auction rooms,
// themed rooms, Chaos) keeps the audit-H1 adult gate exactly as it
// was, and a socket with NO account still enters none of them —
// lives included.
function isLiveRoom(room) {
  return (
    room === "live-stage" ||
    (typeof room === "string" && room.indexOf("live-") === 0)
  );
}
function socketIsTeen(socket) {
  return !!(
    socket &&
    socket.data &&
    socket.data.accountId &&
    socket.data.teenClass
  );
}
function socketMayEnterRoom(socket, room) {
  if (!roomNeedsAdult(room)) return true; // faith / teen: all ages
  if (isLiveRoom(room)) return socketIsAdult(socket) || socketIsTeen(socket);
  return socketIsAdult(socket);
}
function roomGatePayload(room) {
  // [RP-V7.75] a live room refuses only the account-less; its copy
  // says so instead of calling the room 18+.
  if (isLiveRoom(room))
    return {
      room,
      reason: "account-required",
      error: "Sign in with a Plaza account to enter a live.",
    };
  return {
    room,
    reason: "adults-only",
    error: "This room is 18+ — sign in with an 18+ account to enter.",
  };
}
function socketIdForKey(devKey) {
  let found = null;
  for (const [sid, k] of clientKeys) if (k === devKey) found = sid;
  return found;
}
// [RP-V7.52] Pending stage requests (audit H3): hostSocketId ->
// Map(requesterSocketId -> at). The server tracks them so a host's
// answer is relayed only for a request it actually received.
const stageRequests = new Map();

io.on("connection", (socket) => {
  // Player enters the party
  socket.on("join", (data = {}) => {
    const room = cleanRoomName(data.room);
    // [RP-V7.52] 18+ rooms require a verified adult-class socket
    // (audit H1). A refused join creates NO player record — the
    // client receives a clean room-gate refusal, never a hang.
    // Fellowship and Teen Hangout stay open to everyone, as always.
    if (!socketMayEnterRoom(socket, room)) {
      socket.emit("room-gate", roomGatePayload(room));
      return;
    }
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
        // [RP-V7.48] NO floor release here: this eviction only fires
        // for a same-device-key ghost, and floors are keyed to that
        // device key — the joining socket simply takes them over.
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
      // [RP-V7.50] the account's photo, when acct-presence landed first
      photoUrl: socket.data.acctPhoto || null,
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
    // [RP-V7.52] The verified adult class rides the binding (audit
    // H1): computed here, from the token-verified account record.
    socket.data.adultClass = ageFromDob(user.dob) >= 18;
    // [RP-V7.75] The verified teen class rides the same binding: a
    // signed-in under-18 account, computed from the token-verified
    // record — it opens LIVE rooms only (see socketMayEnterRoom).
    socket.data.teenClass = ageFromDob(user.dob) < 18;
    acctSocketAdd(user.id, socket.id);
    // [RP-V7.50] The account's photo rides the socket: stashed for the
    // join handler (announce-before-join), and seeded onto an
    // already-joined player that has none (announce-after-join), so a
    // fresh sign-in shows the photo everywhere with no re-upload.
    socket.data.acctPhoto = user.photo || null;
    try {
      const p = players.get(socket.id);
      if (p && !p.photoUrl && user.photo) {
        p.photoUrl = user.photo;
        io.to(p.room).emit("player-photo", { id: p.id, photoUrl: user.photo });
      }
    } catch (e) { }
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

    // [RP-V7.47] An account with a pending (30-day) deletion is
    // read-only — and its live socket may predate the delete request
    // (which kills its tokens), so check the account record itself.
    // Guests (no accountId) are untouched; this relay is room-scoped
    // (io.to(p.room)) exactly as before.
    if (socket.data && socket.data.accountId) {
      const acctDb = readAccounts();
      const acctUser = acctDb.users.find((u) => u.id === socket.data.accountId);
      if (!acctUser || acctUser.deletionRequestedAt) {
        socket.emit("chat-blocked", {
          reason:
            "This account is scheduled for deletion, so it can't send chat.",
        });
        return;
      }
    }

    // [RP-V7.52] Chat in an 18+ room is adults-only on the server
    // too (audit H1) — the join gate keeps non-adults out, and this
    // keeps the relay honest even for a socket that slipped rooms.
    if (!socketMayEnterRoom(socket, p.room)) {
      socket.emit("chat-blocked", {
        reason: isLiveRoom(p.room)
          ? "Live chat needs a signed-in Plaza account."
          : "This room is 18+ — verified adults only.",
      });
      return;
    }

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
    // [RP-V7.52] Same adult-class gate as join (audit H1): a
    // refused switch leaves the player exactly where they were.
    if (!socketMayEnterRoom(socket, room)) {
      socket.emit("room-gate", roomGatePayload(room));
      return;
    }
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

  // [RP-V7.52] Stage requests ride a DEDICATED relay (audit H3).
  // The legacy path folds the request into the rate-limited chat
  // proto stream, where a busy room can silently eat it — the
  // request is now also a first-class socket event: the server
  // resolves the live's host socket from the registry, records the
  // pending request, and delivers it to the host; the host's
  // answer (stage-respond, sent by the existing Invite / new
  // Decline controls) is relayed only for a request that exists.
  socket.on("stage-request", () => {
    const p = players.get(socket.id);
    if (!p) return;
    if (!socketMayEnterRoom(socket, p.room)) return; // [RP-V7.75] lives are open to signed-in teens too — the same may-enter rule as join
    let hostSid = null;
    if (p.room.indexOf("live-") === 0)
      hostSid = socketIdForKey(p.room.slice(5));
    if (!hostSid) {
      for (const e of liveRegistry.values()) {
        if (e.room === p.room) {
          hostSid = socketIdForKey(e.key);
          break;
        }
      }
    }
    if (!hostSid || hostSid === socket.id) return;
    let pend = stageRequests.get(hostSid);
    if (!pend) {
      pend = new Map();
      stageRequests.set(hostSid, pend);
    }
    if (pend.has(socket.id)) return; // already asked — no duplicates
    pend.set(socket.id, Date.now());
    io.to(hostSid).emit("stage-request", {
      fromId: socket.id,
      fromName: p.name,
    });
    socket.emit("stage-request-ack", { ok: true });
  });
  socket.on("stage-respond", (data = {}) => {
    const pend = stageRequests.get(socket.id);
    const to = String(data.to || "");
    if (!pend || !pend.has(to)) return;
    pend.delete(to);
    if (!pend.size) stageRequests.delete(socket.id);
    const me = players.get(socket.id);
    io.to(to).emit(data.accept ? "stage-accepted" : "stage-denied", {
      fromId: socket.id,
      fromName: me ? me.name : "",
    });
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
    const myHid = floorHolderId(socket.id); // [RP-V7.48]
    if (holder && holder !== myHid) {
      const holderSid = floorHolderSocketId(holder);
      const hp = holderSid ? players.get(holderSid) : null;
      return socket.emit("voice-floor-denied", {
        channel,
        reason: "busy",
        by: holderSid || holder,
        byName: hp ? hp.name : "Someone",
      });
    }
    voiceFloors.set(channel, myHid);
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
    if (voiceFloors.get(channel) === floorHolderId(socket.id)) { // [RP-V7.48]
      voiceFloors.delete(channel);
      const others = channelMembers(channel).filter((id) => id !== socket.id);
      if (others.length)
        io.to(others).emit("voice-floor-released", { channel, by: socket.id });
    }
  });

  // WebRTC signaling relay. Allowed only within the same room or between
  // matched players.
  socket.on("voice-signal", (data = {}) => {
    // [RP-V7.52] 1:1 video (vc-*) stays 18+ even inside all-ages
    // Fellowship (audit H4 + the settled rule): BOTH ends must be
    // verified adult-class sockets or the signal is dropped here.
    if (String(data.type || "").indexOf("vc-") === 0) {
      const targetSocket = io.sockets.sockets.get(String(data.to || ""));
      if (!socketIsAdult(socket) || !targetSocket || !socketIsAdult(targetSocket))
        return;
    }
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
  // winner is broadcast as "auction-ended". [RP-V7.80] Settlement is
  // server-side now (full-scan F2/F3/F5): endAuction settles through
  // settleAuctionMoney when both parties are account-identified, bids
  // follow the client's tiered ladder, and a suddenDeath auction
  // never extends. Shipping stays a client/host matter.
  // -------------------------------------------------------------------------
  function endAuction(room, cancelled) {
    const a = auctions.get(room);
    if (!a) return;
    if (a.timer) clearTimeout(a.timer);
    auctions.delete(room);
    const winner = a.highBidderId
      ? { id: a.highBidderId, name: a.highBidderName, amount: a.currentBid }
      : null;
    const payload = {
      room,
      item: a.item,
      winner: cancelled ? null : winner,
    };
    const emitEnd = () =>
      io.to(room).emit(cancelled ? "auction-cancelled" : "auction-ended", payload);
    // [RP-V7.80] Full-scan F2: a real (not cancelled) win with BOTH
    // parties account-identified settles server-side through
    // settleAuctionMoney BEFORE the end broadcast, so the money has
    // already moved exactly once when clients hear the result. A
    // win involving a guest socket (no account identity) cannot
    // settle — the announcement still goes out, marked skipped.
    if (!cancelled && winner && a.hostAccountId && a.highBidderAccountId) {
      withMoneyLock(() => {
        const adb = readAccounts();
        const mdb = readMoney();
        const r = settleAuctionMoney(adb, mdb, {
          auctionId: a.id,
          winnerId: a.highBidderAccountId,
          hostId: a.hostAccountId,
          winningBid: a.currentBid,
        });
        writeMoney(mdb);
        return r;
      })
        .then((r) => {
          payload.settlement = r;
          emitEnd();
        })
        .catch(() => emitEnd());
    } else {
      if (!cancelled && winner)
        payload.settlement = {
          ok: false,
          error: "settlement-skipped-unverified-party",
        };
      emitEnd();
    }
  }
  socket.on("auction-start", (data = {}) => {
    const me = players.get(socket.id);
    if (!me) return;
    if (socketIsTeen(socket)) return; // [RP-V7.75] auctions stay 18+ — a teen in a live room can't run one
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
      // [RP-V7.80] Full-scan F5: Sudden Death — when the seller
      // starts with suddenDeath:true, a late bid never extends the
      // clock (the client rpWn module's aucSd rule, now server-side).
      suddenDeath: !!data.suddenDeath,
      // [RP-V7.80] Full-scan F2: settlement identity — a stable
      // per-auction id (the settlement idempotency key) and the
      // host's ACCOUNT id, captured from acct-presence.
      id: "auc-" + crypto.randomBytes(8).toString("hex"),
      hostAccountId: socket.data.accountId || null,
      highBidderAccountId: null,
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
      suddenDeath: a.suddenDeath,
      auctionId: a.id,
    });
  });
  socket.on("auction-bid", (data = {}) => {
    const me = players.get(socket.id);
    if (!me) return;
    if (socketIsTeen(socket)) return; // [RP-V7.75] auctions stay 18+ — a teen in a live room can't bid in the host's pinned auction
    const a = auctions.get(me.room);
    if (!a || a.hostId === socket.id) return;
    const amount = Math.floor(Number(data.amount) || 0);
    // [RP-V7.80] Full-scan F3: the minimum next bid follows the
    // client's tiered ladder (auctionBidStepDollars) — a first bid
    // may land exactly on startBid; every later bid must clear the
    // current high by the tier step. A below-ladder bid is refused
    // silently with NO state change, exactly like a below-minimum
    // bid before.
    const minimum = a.highBidderId
      ? a.currentBid + auctionBidStepDollars(a.currentBid)
      : a.startBid;
    if (amount < minimum) return;
    a.currentBid = amount;
    a.highBidderId = socket.id;
    a.highBidderName = me.name;
    a.highBidderAccountId = socket.data.accountId || null; // [RP-V7.80] settlement identity (F2)
    let extended = false;
    const remaining = a.endsAt - Date.now();
    // [RP-V7.80] Full-scan F5: Sudden Death auctions never extend.
    if (!a.suddenDeath && remaining < 5000) {
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
      suddenDeath: !!a.suddenDeath,
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
    const discKey = clientKeys.get(socket.id); // [RP-V7.52] capture the device key BEFORE the mapping goes away (host teardown below)
    const floorHid = floorHolderId(socket.id); // [RP-V7.48] capture the floor identity BEFORE the key mapping goes away
    clientKeys.delete(socket.id); // [RP-V7.24]
    const me = players.get(socket.id);
    if (me) {
      const a = auctions.get(me.room);
      if (a && a.hostId === socket.id) endAuction(me.room, true);
    }
    releaseFloorsHeldBy(floorHid, socket.id); // [RP-V7.48] releases only when no live socket still carries this device identity
    for (const m of [...matches]) {
      if (m.split(":").includes(socket.id)) matches.delete(m);
    }
    const p = players.get(socket.id);
    if (p) {
      socket.to(p.room).emit("player-left", { id: p.id });
      players.delete(socket.id);
      chatTimes.delete(socket.id);
    }
    // [RP-V7.52] Host disconnect teardown (audit H13): a host whose
    // socket dies (tab close, crash, deploy) deregisters their live
    // NOW — settle its pot by the lifecycle rule and broadcast the
    // removal — instead of leaving a ghost live (with a joinable
    // pot) advertised until the 75s staleness sweep. Guarded by the
    // device key: if another live socket still carries this key
    // (the same device reconnected), the live is theirs now and
    // nothing is torn down. Mirrors live-unregister exactly.
    if (discKey && liveRegistry.has(discKey)) {
      let otherHoldsKey = false;
      for (const k of clientKeys.values())
        if (k === discKey) {
          otherHoldsKey = true;
          break;
        }
      if (!otherHoldsKey) {
        liveRegistry.delete(discKey);
        broadcastLives();
        potLiveEnded(discKey);
      }
    }
    // [RP-V7.52] Stage-request bookkeeping dies with either side.
    stageRequests.delete(socket.id);
    for (const [hid, pend] of [...stageRequests]) {
      pend.delete(socket.id);
      if (!pend.size) stageRequests.delete(hid);
    }
  });
});

server.listen(PORT, () =>
  console.log(`Party server listening on port ${PORT}`)
);

/* ---------- [RP-V7.94] Seed/demo content sweep (boot, idempotent) ----------
   The Plaza no longer ships fake content (Branden, Oct 28, 2026:
   "Erase these fake photos"). The client seed routines are gone;
   this sweep removes the server-side traces the seeds could leave:
   shared likes / comments / reposts / reactions recorded under the
   client seed post ids "seed0".."seed5" (the six Moments demo
   posts), plus — defensively — any photo post or reel whose id IS
   one of those seed ids. Those ids were only ever minted by the
   client seed routine (real posts/reels carry server-generated
   ids), so nothing a real member made can match. No account is
   touched: accounts were never seeded server-side (sign-up is the
   only account creator). Runs once per boot; a second boot finds
   nothing and writes nothing. */
const SEED_DEMO_IDS_94 = ["seed0", "seed1", "seed2", "seed3", "seed4", "seed5"];
function sweepSeedDemo94() {
  let removed = 0;
  const dropKeys = (map) => {
    if (!map || typeof map !== "object") return false;
    let hit = false;
    for (const id of SEED_DEMO_IDS_94) if (id in map) { delete map[id]; hit = true; removed++; }
    return hit;
  };
  try {
    const pp = readPhotoPosts();
    const before = pp.posts.length;
    pp.posts = pp.posts.filter((p) => !(p && SEED_DEMO_IDS_94.indexOf(p.id) >= 0));
    if (pp.posts.length !== before) { removed += before - pp.posts.length; writePhotoPosts(pp); }
  } catch (e) {}
  try { const lk = readPhotoLikes(); if (dropKeys(lk.photos)) writePhotoLikes(lk); } catch (e) {}
  try { const cm = readPhotoComments(); if (dropKeys(cm.photos)) writePhotoComments(cm); } catch (e) {}
  try { const rp = readPhotoReposts(); if (dropKeys(rp.photos)) writePhotoReposts(rp); } catch (e) {}
  try { const rx = readPhotoReactions(); if (dropKeys(rx.photos)) writePhotoReactions(rx); } catch (e) {}
  try {
    const reels = listReels();
    const keep = reels.filter((r) => !(r && SEED_DEMO_IDS_94.indexOf(r.id) >= 0));
    if (keep.length !== reels.length) { removed += reels.length - keep.length; fs.writeFileSync(REELS_FILE, JSON.stringify(keep, null, 2)); }
  } catch (e) {}
  if (removed) console.log("[seed-sweep] removed " + removed + " seeded demo record(s)");
  return removed;
}
try { sweepSeedDemo94(); } catch (e) { console.log("[seed-sweep] failed", e && e.message); }

// [RP-V7.77] POT SEPARATION boot migration: persist the normalized
// classed shapes once. readPots/readDailyPot/readDpStreaks and the
// history reader all migrate legacy data in memory (live pots and
// the Daily Pot to ADULT unless a live host's DOB says teen; streaks
// and history to ADULT wholesale); writing them back here makes the
// migration durable and idempotent — a second boot reads classed
// stores and changes nothing. dpEnsureToday then creates the fresh
// teen Daily Pot from the teen class's own tier if it does not yet
// exist, without touching the migrated adult record.
try {
  writePots(readPots());
  writeDailyPot(readDailyPot());
  dpEnsureToday(Date.now());
  writeDpStreaks(readDpStreaks());
  writeDpHistoryMap(readDpHistoryMap());
} catch (e) {
  console.log("[pot-separation] boot migration failed", e && e.message);
}

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
// opens the America/New_York day at midnight and fires each Daily
// Pot settlement at its secret drawn moment in 19:00-21:00 ET; a state
// burst settlement (dpEnsureToday also settles on contact, so a state
// read right at a drawn moment never lags; this timer is the guarantee for an
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

// [RP-V7.70] Stories expiry sweep: once on boot, then every 10
// minutes (the deletion-sweep pattern) — a story dies at 24h and its
// media file is unlinked with it. Reads also sweep lazily.
try {
  sweepStories();
} catch (e) {}
const storySweepTimer = setInterval(() => {
  try {
    sweepStories();
  } catch (e) {}
}, 10 * 60 * 1000);
if (storySweepTimer.unref) storySweepTimer.unref();

