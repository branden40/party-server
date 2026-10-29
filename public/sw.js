/* Rizz Plaza service worker — offline app shell.
   Cache-first for the app shell and icons, network-first for page
   navigations so a fresh build always wins when online.
   [RP-V7.120] The v1 worker cached EVERY same-origin GET — including
   the /socket.io/ polling handshake — and matched the cache with
   ignoreSearch, so every later connect replayed the first session's
   dead handshake and the app could never get online. v2: realtime
   (/socket.io/) and /api/ traffic is never intercepted, the cache
   name is bumped (activation deletes the poisoned v1 cache), static
   matches no longer ignore the query string, and only clean 200
   responses are stored. */
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

  // [RP-V7.120] Realtime and API traffic goes straight to the network:
  // never cached, never replayed.
  if (url.pathname.indexOf("/socket.io/") === 0 || url.pathname.indexOf("/api/") === 0) return;

  if (req.mode === "navigate") {
    event.respondWith(
      fetch(req).then(function (res) {
        if (res && res.ok) {
          var copy = res.clone();
          caches.open(CACHE).then(function (cache) { cache.put("../index.html", copy); });
        }
        return res;
      }).catch(function () {
        return caches.match("../index.html", { ignoreSearch: true })
          .then(function (hit) { return hit || caches.match("../", { ignoreSearch: true }); });
      })
    );
    return;
  }

  event.respondWith(
    caches.match(req).then(function (hit) {
      if (hit) return hit;
      return fetch(req).then(function (res) {
        if (res && res.status === 200) {
          var copy = res.clone();
          caches.open(CACHE).then(function (cache) { cache.put(req, copy); });
        }
        return res;
      });
    })
  );
});
