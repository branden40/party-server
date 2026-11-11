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
   responses are stored.
   [RP-V7.328] Web Push added BELOW the fetch handler: `push` shows
   the notification the server sent (with a focus check — if the
   member is actively viewing that same DM thread in a focused
   window, the banner is suppressed), and `notificationclick`
   focuses/opens the app at the notification's deep link. The fetch
   handler above is byte-for-byte the V7.120 behaviour: navigations
   stay network-first, so a fresh build still always wins online and
   push can never serve a stale index. The cache name is unchanged —
   the shell contents did not change, only this file did, and a
   changed worker script is itself what makes browsers update. */
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

/* ================= [RP-V7.328] WEB PUSH =================
   The server sends { title, body, url, tag, dmWith }. A DM push
   first asks any FOCUSED window whether it is actively viewing that
   same thread (the page answers via MessageChannel — see the client
   push module); if so the banner is suppressed, because the member
   is already looking at the conversation and the in-app UI has it.
   Every other case shows the notification. */
function rp328ViewingDm(dmWith) {
  return self.clients
    .matchAll({ type: "window", includeUncontrolled: true })
    .then(function (wins) {
      var focused = wins.filter(function (w) {
        return w.focused;
      });
      if (!focused.length) return false;
      var asks = focused.map(function (w) {
        return new Promise(function (resolve) {
          var done = false;
          var finish = function (v) {
            if (!done) {
              done = true;
              resolve(v);
            }
          };
          try {
            var ch = new MessageChannel();
            ch.port1.onmessage = function (ev) {
              finish(!!(ev.data && ev.data.viewingDm));
            };
            w.postMessage({ type: "rp328-focus-query", dmWith: dmWith }, [ch.port2]);
          } catch (e) {
            finish(false);
          }
          setTimeout(function () {
            finish(false);
          }, 350);
        });
      });
      return Promise.race([
        Promise.all(asks).then(function (rs) {
          return rs.some(function (x) {
            return x;
          });
        }),
        new Promise(function (resolve) {
          setTimeout(function () {
            resolve(false);
          }, 700);
        }),
      ]);
    })
    .catch(function () {
      return false;
    });
}

self.addEventListener("push", function (event) {
  var data = {};
  if (event.data) {
    try {
      data = event.data.json() || {};
    } catch (e) {
      try {
        data = { body: event.data.text() };
      } catch (e2) {
        data = {};
      }
    }
  }
  var title = data.title || "Rizz Plaza";
  var opts = {
    body: data.body || "",
    icon: "/icon-192.png",
    badge: "/icon-192.png",
    tag: data.tag || undefined,
    renotify: !!data.tag,
    data: { url: data.url || "/", dmWith: data.dmWith || null },
  };
  var gate = data.dmWith ? rp328ViewingDm(String(data.dmWith)) : Promise.resolve(false);
  event.waitUntil(
    gate.then(function (viewing) {
      if (viewing) return null; // already looking at this thread — no double noise
      return self.registration.showNotification(title, opts);
    })
  );
});

self.addEventListener("notificationclick", function (event) {
  event.notification.close();
  var url = (event.notification.data && event.notification.data.url) || "/";
  event.waitUntil(
    self.clients
      .matchAll({ type: "window", includeUncontrolled: true })
      .then(function (wins) {
        var target = null;
        for (var i = 0; i < wins.length; i++) {
          try {
            if (new URL(wins[i].url).origin === self.location.origin) {
              target = wins[i];
              break;
            }
          } catch (e) {}
        }
        if (target) {
          var nav = typeof target.navigate === "function"
            ? target.navigate(url).catch(function () {
                return target;
              })
            : Promise.resolve(target);
          return Promise.resolve(nav).then(function (c) {
            var w = c || target;
            return w && typeof w.focus === "function" ? w.focus() : null;
          });
        }
        return self.clients.openWindow(url);
      })
  );
});
