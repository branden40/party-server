# Party Server — deploy guide

This is the real-time server for the dating party game. It keeps track of
who is in each room, relays chat messages, and syncs avatars moving and
dancing. Deploy it once, then every player connects to it.

## What you need

- A free Railway account (railway.app)
- These files (server.js, package.json)

## Deploy in 5 steps

1. **Push to GitHub.** Create a new repository on github.com and upload
   these files (drag-and-drop works fine on the GitHub website).

2. **Create a Railway project.** At railway.app: New Project → Deploy from
   GitHub → pick your repository. Railway auto-detects Node.js and runs
   `npm start`. No settings to change.

   (Alternative without GitHub: install the Railway CLI, then in this
   folder run `railway login`, `railway init`, `railway up`.)

3. **Get your public URL.** In Railway: click the service → Settings →
   Networking → Generate Domain. Copy the URL — it looks like
   `https://party-server-abc123.up.railway.app`.

4. **Check it's alive.** Open `https://YOUR-URL/health` in a browser.
   You should see `{"ok":true,"online":0}`.

5. **Send me the URL.** I'll add an "Online" mode to the game wired to
   your server, so players actually meet each other in the rooms.

## Profile photos (for the online version)

Players can upload a profile picture from their device. The server stores
it in cloud storage and runs it through an auto-moderation safety check
before it goes live. Both have free tiers.

**Storage — Cloudflare R2 (free tier: 10 GB, no egress fees):**
1. At dash.cloudflare.com, go to R2 → Create bucket (e.g. `profile-photos`).
2. Under R2 → Manage R2 API tokens, create a token with Object Read &
   Write permission.
3. Back on the bucket: Settings → Public access → Allow public access,
   and copy the public bucket URL (`https://pub-<hash>.r2.dev`).

**Safety check — Hive (free tier at thehive.ai):**
1. Create an account, copy your API key.
2. Photos flagged as explicit are deleted automatically and never go live.

**Railway variables** (service → Variables → add all of these):
- `S3_ENDPOINT` = `https://<accountid>.r2.cloudflarestorage.com`
- `S3_BUCKET` = your bucket name
- `S3_ACCESS_KEY` / `S3_SECRET_KEY` = your R2 token credentials
- `S3_PUBLIC_URL` = your public bucket URL (no trailing slash)
- `HIVE_API_KEY` = your Hive key (optional but strongly recommended —
  without it, uploads are accepted and logged as UNREVIEWED, so check
  your logs and the in-game report system instead)

Without the S3 variables, the upload endpoint answers "not configured"
and everything else keeps working — photos simply stay device-only
until you set this up.

## Cost

Railway's free tier covers getting started and a handful of players.
Expect roughly $5–20/month as it grows — you'll see usage in the
Railway dashboard before you're ever charged.

## Before you invite real people

- **Age gate:** add an 18+ confirmation to the game's entry screen.
- **Reports:** the server logs player reports to its console. Before
  launch, point those somewhere you actually check — Railway lets you
  forward logs, or wire the `report` event to an email/Discord webhook.
- **Block button:** the game client should let players block/mute
  individuals (the server already supports per-player messaging hooks).

## Test it locally (optional)

Need Node.js 18+ installed, then:

```
npm install
node server.js
```

Open http://localhost:3000/health — you should see `{"ok":true,"online":0}`.


