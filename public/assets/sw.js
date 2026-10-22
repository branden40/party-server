/* Rizz Plaza service worker v2 — offline app shell + fast repeat opens.
   - Navigations: network-first, so a fresh build always wins when online.
   - Everything else (icons, audio, photos): stale-while-revalidate —
     instant from cache, refreshed quietly in the background.
   - Live traffic is NEVER cached: Socket.io and /api/ always hit network. */
var CACHE = "dating-game-v2";
var CORE = [
  "../",
  "../index.html",
  "manifest.webmanifest",
  "icon-192.png",
  "icon-512.png",
  "icon-maskable-512.png",
  "apple-touch-icon.png"
];

self.addEventListener("install", function (event) {
  event.waitUntil(
    caches.open(CACHE).then(function (cache) {
      return cache.addAll(CORE);
    }).then(function () {
      return self.skipWaiting();
    })
  );
});

self.addEventListener("activate", function (event) {
  event.waitUntil(
    caches.keys().then(function (keys) {
      return Promise.all(keys.map(function (key) {
        return key === CACHE ? null : caches.delete(key);
      }));
    }).then(function () {
      return self.clients.claim();
    })
  );
});

self.addEventListener("fetch", function (event) {
  var req = event.request;
  if (req.method !== "GET") return;
  var url = new URL(req.url);
  if (url.origin !== self.location.origin) return;

  // Live traffic: never intercept (realtime must stay realtime).
  if (url.pathname.indexOf("/socket.io/") === 0 || url.pathname.indexOf("/api/") === 0) return;

  if (req.mode === "navigate") {
    event.respondWith(
      fetch(req).then(function (res) {
        var copy = res.clone();
        caches.open(CACHE).then(function (cache) { cache.put("../index.html", copy); });
        return res;
      }).catch(function () {
        return caches.match("../index.html", { ignoreSearch: true })
          .then(function (hit) { return hit || caches.match("../", { ignoreSearch: true }); });
      })
    );
    return;
  }

  // Stale-while-revalidate for static assets, audio and photos.
  event.respondWith(
    caches.match(req, { ignoreSearch: true }).then(function (hit) {
      var network = fetch(req).then(function (res) {
        if (res && res.ok) {
          var copy = res.clone();
          caches.open(CACHE).then(function (cache) { cache.put(req, copy); });
        }
        return res;
      }).catch(function () { return hit; });
      return hit || network;
    })
  );
});
