// 音盒 PWA：极简 Service Worker
// 仅用于满足"可安装"条件，不缓存任何内容——所有请求走网络，保证歌单/歌词永远最新
self.addEventListener('install', e => self.skipWaiting());
self.addEventListener('activate', e => e.waitUntil(self.clients.claim()));
self.addEventListener('fetch', () => { /* 不拦截，默认网络直通 */ });
