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
