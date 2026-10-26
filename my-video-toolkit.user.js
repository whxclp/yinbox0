// ==UserScript==
// @name         我的视频工具箱 v2
// @namespace    whxclp
// @version      2.0.26
// @description  自研轻量视频增强：自动跳广告（播放时识别片头/插播广告，静音+16倍速+跳尾，工具菜单可关；⑤边播边录时也会把广告直接跳过、录出来不含广告）、倍速调速、画面旋转/镜像/缩放/位移、亮度对比度饱和度滤镜、截图、画中画、循环播放。下载推荐用本机 yt-dlp 脚本（① 当前页 / ② 任意链接 / ⑥ 整段下完再剪 / ⑦ 去片头广告），兜底为分片合并与边播边录。菜单固定向左展开，绝不超出屏幕右侧。
// @author       whxclp
// @match        *://*/*
// @run-at       document-start
// @grant        none
// @updateURL    https://whxclp.github.io/yinbox/my-video-toolkit.user.js
// @downloadURL  https://whxclp.github.io/yinbox/my-video-toolkit.user.js
// ==/UserScript==

(function () {
  'use strict';

  /* ============================================================
   * 分片捕获：必须在页面脚本执行前挂钩，所以 @run-at 是 document-start
   * 思路：拦下 fetch / XHR，把视频音频分片的二进制先攒起来，
   *      用户点「分片合并下载」时按序号排序拼接 —— 即「先下载完，再合并」。
   * ============================================================ */
  var CAP = {
    on: true,
    seq: 0,
    items: [],            // {seq, url, ct, kind, idx, buf}
    bytes: 0,
    maxBytes: 1200 * 1024 * 1024,   // 缓存上限 1.2GB，超了只记 URL 不再占内存
    overflow: false
  };

  /* B站 dash：文件名里的 5 位 30xxx 是轨 ID（<30200 视频、>=30200 音频）；
     其余站点看 content-type；实在判不出来归 'unk'，绝不乱猜成 video */
  function mediaKind(u, ct) {
    var s = String(u || '');
    var m = s.match(/(\d{5})\.m4s(\?|$)/i);
    if (m) { return parseInt(m[1], 10) >= 30200 ? 'audio' : 'video'; }
    var c = String(ct || '').toLowerCase();
    if (/^audio\//.test(c)) return 'audio';
    if (/^video\//.test(c)) return 'video';
    if (/\.(m4s|ts)(\?|$)/i.test(s)) return 'unk';
    return null;
  }

  /* 分片序号：range 参数 > 文件名数字；5 位 30xxx 是轨 ID 不是序号，要排除 */
  function segIndex(u) {
    var s = String(u || '');
    if (/(\d{5})\.m4s(\?|$)/i.test(s)) return -1;
    var m = s.match(/(\d+)\.(?:m4s|ts)(\?|$)/i);
    if (m) return parseInt(m[1], 10);
    m = s.match(/[?&](?:range|start|byte)[=_](\d+)/i);
    if (m) return parseInt(m[1], 10);
    return -1;
  }

  /* 从 Content-Range 取起始字节；B站 dash 是按 range 分段加载同一个大 m4s，
     所以去重键必须是 url + 起始偏移，只按 url 去重会把后到的片段全丢掉 */
  function rangeStart(r) {
    try {
      var cr = (r && r.headers && r.headers.get) ? r.headers.get('content-range') : '';
      var m = String(cr || '').match(/bytes\s+(\d+)-/i);
      if (m) return parseInt(m[1], 10);
    } catch (e) {}
    return -1;
  }

  function addSeg(u, ct, buf, start) {
    var k = mediaKind(u, ct);
    if (!k) return;
    var st = (typeof start === 'number') ? start : -1;
    for (var i = 0; i < CAP.items.length; i++) {
      var it = CAP.items[i];
      if (it.url === u && it.start === st) return;      // 去重：同 URL 同偏移
    }
    CAP.items.push({
      seq: CAP.seq++, url: u, ct: ct || '', kind: k,
      idx: segIndex(u), buf: buf || null, start: st
    });
    if (buf) CAP.bytes += buf.byteLength || 0;
  }

  /* ============================================================
   * 抖音：页面上下文内提取视频直链（零 cookie）
   * 背景：Edge 156 的 ABE（App-Bound Encryption）把 cookie 值加密成
   * v20 格式，SQLite 里 value 列全空，DPAPI 解不开；而带
   * --remote-debugging-port 启动 Edge 会让 ABE 校验失败、Edge 直接把
   * 「解不开」的 cookie 从库里物理删掉（2026-10-25 实测 1853→25，
   * 不可恢复）。所以任何「自动读浏览器 cookie」的方案都既不可行
   * 也不安全。
   * 可行思路（参考 WhiteSevs「抖音优化」greasyfork #494643）：
   * 页面自己登录着，页面自己的 /aweme/ 接口响应里就带
   * video.play_addr.url_list —— 自带签名查询参数的 CDN 直链，
   * yt-dlp 带上 Referer 直接下，完全不需要 cookie。
   * 数据来源（按可靠性排序）：
   *   1) 网络钩子抓到的 /aweme/ 接口响应（document-start 就装好钩子）
   *   2) 页面 SSR 数据 window._ROUTER_DATA
   *   3) <script id="RENDER_DATA">（URL 编码或纯 JSON）
   *   4) React fiber 上挂的 awemeInfo（当前播放视频）
   * ============================================================ */
  var DY = { map: {}, last: null };   // aweme_id -> aweme 详情对象

  function dyIsAwemeApi(u) {
    var s = String(u || '');
    if (!/\/aweme\/v\d+\/web\//.test(s)) return false;
    /* 绝对 URL 时校验主机必须含 douyin，避免误伤其它站点同路径接口 */
    var m = s.match(/^https?:\/\/([^\/]+)/i);
    if (m) return /douyin/i.test(m[1]);
    return true;   /* 相对路径：页面内只可能请求自家接口 */
  }

  /* aweme ID：网络/SSR 源是 aweme_id（snake），DOM/fiber 源是 awemeId（camel） */
  function dyAwemeId(a) {
    if (!a || typeof a !== 'object') return '';
    if (a.aweme_id) return String(a.aweme_id);
    if (a.awemeId) return String(a.awemeId);
    return '';
  }

  /* 从 aweme 详情对象里挑最优直链：bit_rate 数组按码率降序，取第一个。
     双 schema 兼容：
       网络/SSR 源：aweme_id / video.bit_rate[].play_addr.url_list / video.play_addr
       DOM/fiber 源：awemeId / video.bitRateList[].playApi / playAddr[].src */
  function dyPickVideo(aweme) {
    if (!aweme || typeof aweme !== 'object') return null;
    var v = aweme.video;
    if (!v) return null;
    var cands = [];
    if (Array.isArray(v.bit_rate)) {
      for (var i = 0; i < v.bit_rate.length; i++) {
        var b = v.bit_rate[i];
        var pa = b && b.play_addr;
        if (pa && Array.isArray(pa.url_list) && pa.url_list.length && typeof pa.url_list[0] === 'string') {
          cands.push({ url: pa.url_list[0], back: pa.url_list.slice(1, 3),
                       w: pa.width || 0, h: pa.height || 0, br: b.bit_rate || 0,
                       size: pa.data_size || 0 });
        }
      }
    }
    if (Array.isArray(v.bitRateList)) {
      for (var j = 0; j < v.bitRateList.length; j++) {
        var d = v.bitRateList[j];
        if (!d) continue;
        var du = (typeof d.playApi === 'string') ? d.playApi : '';
        var dback = [];
        if (Array.isArray(d.playAddr)) {
          for (var q = 0; q < d.playAddr.length; q++) {
            var it2 = d.playAddr[q];
            if (it2 && typeof it2.src === 'string' && it2.src !== du) {
              if (!du) du = it2.src; else dback.push(it2.src);
            }
          }
        }
        if (du) {
          cands.push({ url: du, back: dback, w: d.width || 0, h: d.height || 0,
                       br: d.bitRate || 0, size: d.dataSize || 0 });
        }
      }
    }
    var pv = v.play_addr;
    if (pv && Array.isArray(pv.url_list) && pv.url_list.length && typeof pv.url_list[0] === 'string') {
      cands.push({ url: pv.url_list[0], back: pv.url_list.slice(1, 3),
                   w: pv.width || v.width || 0, h: pv.height || v.height || 0,
                   br: 0, size: pv.data_size || 0 });
    }
    if (!cands.length) return null;
    cands.sort(function (a, b2) { return (b2.br - a.br) || (b2.h - a.h); });
    var best = cands[0];
    return {
      url: best.url,
      backUrls: best.back || [],
      id: dyAwemeId(aweme),
      desc: String(aweme.desc || '').slice(0, 80),
      duration: v.duration || 0,
      width: best.w, height: best.h, size: best.size
    };
  }

  function dyStoreAweme(a) {
    if (!a || typeof a !== 'object') return;
    var id = dyAwemeId(a);
    if (id) {
      DY.map[id] = a;
      var n = 0, k;
      for (k in DY.map) n++;
      if (n > 200) DY.map = {};      // 防滚屏无限增长，超过 200 个清空重来
    }
    DY.last = a;
  }

  /* 深搜任意 JSON 里所有「像 aweme」的对象（有 ID + 播放地址字段） */
  function dyDeepFindAll(node, depth, out, budget) {
    if (!node || typeof node !== 'object' || depth > 7) return budget;
    if (budget.n-- <= 0) return budget;
    if (Array.isArray(node)) {
      for (var i = 0; i < node.length && budget.n > 0; i++) dyDeepFindAll(node[i], depth + 1, out, budget);
      return budget;
    }
    var v = node.video;
    var hasApi = v && v.play_addr && Array.isArray(v.play_addr.url_list) && v.play_addr.url_list.length;
    var hasDom = v && (Array.isArray(v.bitRateList) || typeof v.playApi === 'string');
    if (dyAwemeId(node) && (hasApi || hasDom)) {
      out.push(node);
      return budget;
    }
    for (var k in node) {
      if (budget.n-- <= 0) break;
      try { dyDeepFindAll(node[k], depth + 1, out, budget); } catch (e) {}
    }
    return budget;
  }

  /* 处理一个 /aweme/ 接口响应 */
  function dyIngestJson(json) {
    try {
      if (!json || typeof json !== 'object') return;
      if (json.aweme_detail && typeof json.aweme_detail === 'object') {
        dyStoreAweme(json.aweme_detail);
        return;
      }
      if (Array.isArray(json.aweme_list) && json.aweme_list.length) {
        for (var i = 0; i < json.aweme_list.length; i++) {
          var it = json.aweme_list[i];
          if (it && it.aweme_info) dyStoreAweme(it.aweme_info);
        }
        return;
      }
      var out = [];
      dyDeepFindAll(json, 0, out, { n: 200000 });
      for (var j = 0; j < out.length; j++) dyStoreAweme(out[j]);
    } catch (e) {}
  }

  function dyParseRenderData(txt) {
    try { return JSON.parse(decodeURIComponent(txt)); } catch (e) {}
    try { return JSON.parse(txt); } catch (e) {}
    return null;
  }

  /* 扫页面 SSR 数据：_ROUTER_DATA / RENDER_DATA */
  function dyScanPageData() {
    var out = [];
    try {
      if (window._ROUTER_DATA) dyDeepFindAll(window._ROUTER_DATA, 0, out, { n: 300000 });
    } catch (e) {}
    if (!out.length) {
      try {
        var sd = document.getElementById('RENDER_DATA');
        if (sd && sd.textContent) {
          var j = dyParseRenderData(sd.textContent);
          if (j) dyDeepFindAll(j, 0, out, { n: 300000 });
        }
      } catch (e) {}
    }
    for (var i = 0; i < out.length; i++) dyStoreAweme(out[i]);
    return out;
  }

  /* 从当前播放器的 React fiber 上找 awemeInfo（抖音优化同款思路） */
  function dyFiberAweme(el) {
    var node = el;
    for (var up = 0; node && up < 8; up++, node = node.parentElement) {
      var key = '';
      try {
        var ks = Object.keys(node);
        for (var i = 0; i < ks.length; i++) {
          if (ks[i].indexOf('__reactFiber$') === 0 || ks[i].indexOf('__reactInternalInstance$') === 0) {
            key = ks[i]; break;
          }
        }
      } catch (e) {}
      if (!key) continue;
      var fiber = node[key];
      for (var d = 0; fiber && d < 10; d++, fiber = fiber.return) {
        try {
          var mp = fiber.memoizedProps;
          if (mp && mp.awemeInfo && typeof mp.awemeInfo === 'object') return mp.awemeInfo;
        } catch (e) {}
      }
    }
    return null;
  }

  function dyFromFiber() {
    var sels = ['.basePlayerContainer', '[data-e2e="feed-active-video"]',
                '.swiper-slide-active xg-player', 'xg-player', '.xg-video-player'];
    for (var s = 0; s < sels.length; s++) {
      var els;
      try { els = document.querySelectorAll(sels[s]); } catch (e) { continue; }
      for (var i = 0; i < els.length && i < 3; i++) {
        var a = dyFiberAweme(els[i]);
        if (a) return a;
      }
    }
    return null;
  }

  /* 对外入口：拿当前视频的直链信息。awemeId 可空（feed 页场景）。
     返回 {url, backUrls, id, desc, duration, width, height, size} 或 null */
  function dyGetVideo(awemeId) {
    var id = awemeId ? String(awemeId) : '';
    /* 1) 网络钩子已抓到的（最可靠，清晰度列表最全） */
    if (id && DY.map[id]) return dyPickVideo(DY.map[id]);
    /* 2) 页面 SSR 数据 */
    var cands = dyScanPageData();
    if (id) {
      for (var i = 0; i < cands.length; i++) {
        if (dyAwemeId(cands[i]) === id) return dyPickVideo(cands[i]);
      }
      /* 3) fiber：详情页上 fiber 里挂的就是当前视频 */
      var f = dyFromFiber();
      if (f && (!dyAwemeId(f) || dyAwemeId(f) === id)) return dyPickVideo(f);
      return null;
    }
    /* 无 id（feed 页）：优先 fiber 当前播放，其次最近抓到的 */
    var f2 = dyFromFiber();
    if (f2) { var p2 = dyPickVideo(f2); if (p2) return p2; }
    if (DY.last) { var p3 = dyPickVideo(DY.last); if (p3) return p3; }
    return cands.length ? dyPickVideo(cands[0]) : null;
  }

  function capFetch(url, p) {
    if (!p || typeof p.then !== 'function') return p;
    return p.then(function (r) {
      try {
        var ct = (r.headers && r.headers.get) ? (r.headers.get('content-type') || '') : '';
        if (!mediaKind(url, ct)) {
          /* 抖音接口响应：clone 出来读 JSON，不影响页面自己拿到的 response */
          if (CAP.on && dyIsAwemeApi(url)) {
            var dj = r.clone();
            if (dj.json) {
              dj.json().then(dyIngestJson).catch(function () {});
            }
          }
          return r;
        }
        var st = rangeStart(r);
        if (CAP.bytes >= CAP.maxBytes) { CAP.overflow = true; addSeg(url, ct, null, st); return r; }
        var c = r.clone();
        c.arrayBuffer().then(function (b) { addSeg(url, ct, b, st); })
                        .catch(function () { addSeg(url, ct, null, st); });
      } catch (e) {}
      return r;
    }, function (e) { throw e; });
  }

  function hookNetwork() {
    /* --- fetch --- */
    var of = window.fetch;
    if (typeof of === 'function') {
      window.fetch = function (input, init) {
        var url = (typeof input === 'string') ? input
               : (input && input.url) ? input.url : '';
        var p;
        try { p = of.apply(this, arguments); } catch (e) { throw e; }
        return CAP.on ? capFetch(url, p) : p;
      };
    }
    /* --- XHR：response 多为 arraybuffer，直接取；否则只记 URL --- */
    var X = window.XMLHttpRequest;
    if (X && X.prototype && X.prototype.open) {
      var P = X.prototype;
      var oo = P.open, os = P.send;
      P.open = function (m, u) { this.__mvtU = u; return oo.apply(this, arguments); };
      P.send = function () {
        var self = this;
        if (CAP.on) {
          this.addEventListener('load', function () {
            try {
              var ct = (self.getResponseHeader && self.getResponseHeader('content-type')) || '';
              var u = self.__mvtU || '';
              /* 抖音 /aweme/ 接口：解析 JSON 存直链（零 cookie 方案的数据源） */
              if (CAP.on && dyIsAwemeApi(u)) {
                try {
                  var dr = self.response;
                  if (typeof dr === 'string') dyIngestJson(JSON.parse(dr));
                  else if (dr && typeof dr === 'object') dyIngestJson(dr);
                  else if (self.responseText) dyIngestJson(JSON.parse(self.responseText));
                } catch (e) {}
                return;
              }
              if (!mediaKind(u, ct)) return;
              var buf = null;
              try {
                if (self.responseType === 'arraybuffer' && self.response &&
                    self.response.byteLength) buf = self.response;
              } catch (e) {}
              var cr = '';
              try { cr = self.getResponseHeader('content-range') || ''; } catch (e) {}
              var mm = String(cr).match(/bytes\s+(\d+)-/i);
              addSeg(u, ct, buf, mm ? parseInt(mm[1], 10) : -1);
            } catch (e) {}
          });
        }
        return os.apply(this, arguments);
      };
    }
  }
  hookNetwork();
  window.__mvtCap = CAP;   /* 控制台可查看分片情况 */

  /* ================= 样式 ================= */
  var css = [
    '.mvt-bar{position:fixed;top:0;left:40px;z-index:2147483000;display:flex;align-items:center;gap:2px;',
    '  background:linear-gradient(90deg,#d91e43,#ff6a3d);border:1px solid rgba(255,255,255,.4);border-top:none;border-radius:0 0 8px 8px;',
    '  padding:4px 6px;box-shadow:0 4px 16px rgba(0,0,0,.4);font-size:13px;user-select:none;',
    '  transform:translateY(calc(-100% + 3px));transition:transform .22s ease;}',
    '.mvt-bar.mvt-on{transform:translateY(0);}',
    '.mvt-btn{position:relative;color:#fff;font-weight:600;text-shadow:0 1px 2px rgba(0,0,0,.4);background:transparent;border:none;border-radius:6px;',
    '  padding:5px 9px;cursor:pointer;font-size:13px;line-height:1;white-space:nowrap;font-family:inherit;}',
    '.mvt-btn:hover{background:rgba(255,255,255,.22);}',
    '.mvt-btn.rate-btn{color:#ffd166;}',
    '.mvt-btn.pic-btn{color:#7dffb2;}',
    '.mvt-btn.flt-btn{color:#c4a6ff;}',
    '.mvt-btn.dl-btn{color:#7fd8ff;}',
    '.mvt-btn.tool-btn{color:#7ff5e8;}',
    '.mvt-btn.mvt-has-menu::after{content:" ▾";opacity:.6;font-size:10px;}',
    '.mvt-menu{position:absolute;top:calc(100% + 6px);right:0;min-width:150px;',
    '  background:rgba(28,28,32,.97);border:1px solid rgba(255,255,255,.16);border-radius:8px;',
    '  padding:5px;display:none;flex-direction:column;gap:1px;box-shadow:0 6px 20px rgba(0,0,0,.5);}',
    '.mvt-btn.mvt-open .mvt-menu{display:flex;}',
    '.mvt-menu button{color:#eee;background:transparent;border:none;border-radius:6px;text-align:right;',
    '  padding:7px 10px;cursor:pointer;font-size:13px;white-space:nowrap;font-family:inherit;}',
    '.mvt-menu button:hover{background:rgba(255,255,255,.14);}',
    '.mvt-menu .mvt-sep{height:1px;background:rgba(255,255,255,.14);margin:4px 2px;}',
    '.mvt-menu .mvt-cur{color:#8fd3ff;font-weight:600;}',
    '.mvt-toast{position:fixed;top:16px;left:50%;transform:translateX(-50%);z-index:2147483001;',
    '  background:rgba(20,20,24,.95);color:#fff;padding:9px 18px;border-radius:8px;font-size:14px;',
    '  display:none;box-shadow:0 4px 16px rgba(0,0,0,.5);max-width:86vw;line-height:1.5;}',
    '.mvt-logo{color:#9fb4c8;font-size:11px;padding:0 4px;cursor:default;letter-spacing:.5px;}',
    '.mvt-ver{color:#4ec98a;font-size:10px;padding:0 4px 0 0;cursor:default;letter-spacing:.3px;opacity:.95;}',
    '.mvt-stop{color:#fff;background:#d9483b;border-radius:6px;padding:5px 9px;font-size:12px;line-height:1;}',
    '.mvt-stop:hover{background:#c33a2e;}'
  ].join('');

  /* ================= 状态 ================= */
  var cur = null;
  var hideTimer = null;
  var bar, toastEl, toastTimer = null;

  function newState() {
    return { rate: 1, rotate: 0, flipH: false, flipV: false, zoom: 1, dx: 0, dy: 0,
             bright: 100, contrast: 100, sat: 100 };
  }

  /* ================= 工具函数 ================= */
  function toast(msg, ms) {
    toastEl.textContent = msg;
    toastEl.style.display = 'block';
    clearTimeout(toastTimer);
    toastTimer = setTimeout(function () { toastEl.style.display = 'none'; }, ms || 2600);
  }

  function safeName() {
    var t = (document.title || '').replace(/[\\/:*?"<>|]/g, '_').trim().slice(0, 50);
    return t || ('视频_' + Date.now());
  }

  function stamp() {
    var d = new Date(), p = function (n) { return n < 10 ? '0' + n : '' + n; };
    return d.getFullYear() + p(d.getMonth() + 1) + p(d.getDate()) + '_' +
           p(d.getHours()) + p(d.getMinutes()) + p(d.getSeconds());
  }

  function apply(v) {
    var s = v.__mvt;
    v.style.filter = 'brightness(' + s.bright + '%) contrast(' + s.contrast + '%) saturate(' + s.sat + '%)';
    v.style.transformOrigin = 'center center';
    v.style.transform =
      'translate(' + s.dx + 'px,' + s.dy + 'px) rotate(' + s.rotate + 'deg)' +
      ' scale(' + s.zoom + ')' + (s.flipH ? ' scaleX(-1)' : '') + (s.flipV ? ' scaleY(-1)' : '');
  }

  /* ================= 下载：入口 ================= */
  function downloadVideo() {
    var v = cur;
    if (!v) return;
    var src = v.currentSrc || v.src;
    if (src && src.indexOf('http') === 0) {
      toast('开始下载原文件…');
      fetch(src, { credentials: 'include' }).then(function (r) {
        if (!r.ok) throw new Error('HTTP ' + r.status);
        var type = r.headers.get('content-type') || '';
        return r.blob().then(function (b) { saveBlob(b, guessName(src, type)); });
      }).catch(function (e) {
        if (CAP.items.length) {
          toast('直链下载失败（多为跨域拦截），已捕获 ' + CAP.items.length + ' 个分片，可用「分片合并下载」', 4000);
        } else {
          toast('直链下载失败：' + e.message + '，可试「边播边录合成」', 4000);
        }
      });
    } else if (src && (src.indexOf('blob:') === 0 || src.indexOf('data:') === 0)) {
      if (CAP.items.length >= 2) {
        toast('检测到 MSE 流，已捕获 ' + CAP.items.length + ' 个分片，建议用「分片合并下载」', 4000);
      } else {
        mergeRecord(v);
      }
    } else {
      toast('找不到视频地址');
    }
  }

  /* ================= 下载模式二：分片合并（先下完再拼） ================= */
  function fetchOne(it) {
    if (it.buf) return Promise.resolve(it.buf);
    return fetch(it.url, { credentials: 'include' }).then(function (r) {
      if (!r.ok) throw new Error(r.status);
      return r.arrayBuffer();
    });
  }

  /* 同一个 URL 被 range 切成多段时：
     片段齐全且字节连续 -> 直接用缓存；否则整段重新 fetch 一次（不带 range），
     免得拼出一个带空洞、播放到一半就断的文件 */
  function normalize(list) {
    var gmap = {}, order = [];
    list.forEach(function (it) {
      if (!gmap[it.url]) { gmap[it.url] = []; order.push(it.url); }
      gmap[it.url].push(it);
    });
    var out = [];
    order.forEach(function (u) {
      var g = gmap[u].slice().sort(function (a, b) {
        return (a.start < 0 ? 0 : a.start) - (b.start < 0 ? 0 : b.start);
      });
      if (g.length === 1) { out.push(g[0]); return; }
      var ok = true, expect = 0;
      for (var i = 0; i < g.length; i++) {
        if (!g[i].buf || g[i].start < 0 || g[i].start !== expect) { ok = false; break; }
        expect += g[i].buf.byteLength;
      }
      if (ok) {
        g.forEach(function (x) { out.push(x); });
      } else {
        out.push({ seq: g[0].seq, url: u, ct: g[0].ct, kind: g[0].kind,
                   idx: g[0].idx, buf: null, start: -1, whole: true });
      }
    });
    out.sort(function (a, b) {
      if (a.idx >= 0 && b.idx >= 0 && a.idx !== b.idx) return a.idx - b.idx;
      return a.seq - b.seq;
    });
    return out;
  }

  function buildTrack(kind, raw, done) {
    var list = normalize(raw);
    var out = [], i = 0, miss = 0;
    function step() {
      if (segAbort) {   /* 用户点了「停止」：把已下到的部分先存下来 */
        done(new Blob(out, { type: kind === 'audio' ? 'audio/mp4' : 'video/mp4' }), miss);
        return;
      }
      if (i >= list.length) {
        done(new Blob(out, { type: kind === 'audio' ? 'audio/mp4' : 'video/mp4' }), miss);
        return;
      }
      var it = list[i++];
      if (i % 10 === 0 || i === list.length) toast('正在取分片 ' + i + '/' + list.length);
      fetchOne(it).then(function (b) {
        if (segAbort) { step(); return; }
        out.push(b); step();
      }).catch(function () { if (segAbort) { step(); return; } miss++; step(); });
    }
    step();
  }

  function segDownload() {
    if (!CAP.items.length) {
      toast('还没捕获到分片。请刷新页面、让视频正常播放一段时间后再试', 4000);
      return;
    }
    var kinds = {};
    CAP.items.forEach(function (it) { (kinds[it.kind] = kinds[it.kind] || []).push(it); });
    var keys = Object.keys(kinds);
    var base = safeName() + '_' + stamp();
    var doneCount = 0;
    segRunning = true; segAbort = false; showStop(true);

    keys.forEach(function (k) {
      var list = kinds[k];
      buildTrack(k, list, function (blob, miss) {
        doneCount++;
        var ext = (k === 'audio') ? 'm4a' : (k === 'unk') ? 'bin' : 'mp4';
        saveBlob(blob, base + '_' + k + '.' + ext);
        if (miss) toast('警告：' + k + ' 轨有 ' + miss + ' 个分片没取到，文件可能不完整', 5000);

        if (doneCount === keys.length) {
          segRunning = false; segAbort = false; showStop(false);
          if (keys.length === 2) {
            setTimeout(function () {
              toast('已分别存下视频轨和音频轨。用 ffmpeg 合成完整文件：\n' +
                    'ffmpeg -i ' + base + '_video.mp4 -i ' + base + '_audio.m4a -c copy out.mp4', 9000);
            }, 1200);
          }
        }
      });
    });

    if (CAP.overflow) {
      toast('注意：分片体积超过缓存上限，部分需重新联网拉取', 4000);
    }
  }

  function reportSeg() {
    var n = CAP.items.length, v = 0, a = 0, cached = 0;
    CAP.items.forEach(function (it) {
      if (it.kind === 'video') v++; else a++;
      if (it.buf) cached++;
    });
    toast('已捕获分片 ' + n + ' 个（视频 ' + v + ' / 音频 ' + a + '），已缓存 ' + cached +
          ' 个，占用 ' + Math.round(CAP.bytes / 1048576) + ' MB' + (CAP.overflow ? '（已超限）' : ''), 5000);
  }

  /* 生成「自举」下载脚本：首次运行自动把 yt-dlp.exe 与 ffmpeg 下载到
   * %LOCALAPPDATA%\mvt\bin，不依赖本机 Python / WinGet，重装系统后双击即用。
   * bakedUrl 非空 => 把链接烤进脚本；为空 => 运行时粘贴/拖放链接。
   * dyVid 非空（抖音页面内提取到的直链）=> 走零 cookie 直链分支。 */
  function buildYtDlpBat(bakedUrl, isDouyin, dyId, dyVid) {
    /* 防盗链：B站 CDN 直链必须同时带浏览器 UA + B站 Referer（实测缺一即 403） */
    var isCdn = /bilivideo\.com|bilivod\.com|bilicdn/i.test(bakedUrl || '');
    /* 抖音直链分支：从页面提取的 CDN 直链自带签名查询参数，只需抖音页面 Referer */
    var direct = (dyVid && dyVid.url) ? String(dyVid.url) : '';
    var ref = direct ? 'https://www.douyin.com/'
      : (isCdn ? 'https://www.bilibili.com/'
      : ((bakedUrl && /^https?:/i.test(bakedUrl)) ? String(bakedUrl).split('#')[0] : 'https://www.bilibili.com/'));
    var UA = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/138.0.0.0 Safari/537.36';
    /* 抖音输出名：固定 douyin_<视频ID>.%(ext)s。
       必须固定名字——抖音 CDN 直链的查询串曾被 yt-dlp 当成标题/ID 用，
       400+ 字符含 ? & = 的文件名 Windows 直接拒绝创建（Errno 22）。
       注意 bat 里 %% 会被 cmd 折成 %，所以模板写 %%(ext)s。
       注：dyId 为空时退回 %(id)s 模板；feed 页场景用 dyVid.id 兜底。 */
    var dyKey = dyId || (dyVid && dyVid.id) || '';
    /* 乱名修复：dyKey 拿不到时不再用 %(id)s（yt-dlp 会把直链 URL 的
       路径段+查询串拼成文件名，Windows 直接拒绝创建/乱名）。
       改用页面标题清洗后做文件名，最差兜底 douyin_video。 */
    var dyDesc = (dyVid && dyVid.desc) || '';
    var dyOut = dyKey
      ? ('douyin_' + dyKey + '.%%(ext)s')
      : ('douyin_' + (dyDesc.replace(/[\\/:*?"<>|%&^!]/g, '_').trim().slice(0, 60) || 'video') + '.%%(ext)s');
    var L = [
      '@echo off',
      'rem This .bat is intentionally ASCII-only (English prompts). cmd.exe has a 4KB read-buffer',
      'rem bug with chcp 65001 + UTF-8: a multi-byte char straddling the boundary splits a Chinese',
      'rem echo line and runs the tail as a command. ASCII avoids the bug entirely.',
      '',
      'set "TOOLS=%LOCALAPPDATA%\\mvt\\bin"',
      'if not exist "%TOOLS%" mkdir "%TOOLS%" >nul 2>nul',
      'set "YTDLP=%TOOLS%\\yt-dlp.exe"',
      'if not exist "%YTDLP%" (',
      '  echo [mvt] First run: downloading yt-dlp ...',
      '  curl.exe -L --ssl-no-revoke -o "%YTDLP%" "https://github.com/yt-dlp/yt-dlp/releases/latest/download/yt-dlp.exe"',
      '  for %%F in ("%YTDLP%") do if %%~zF LSS 1000000 del /f /q "%YTDLP%" >nul 2>nul',
      "  if not exist \"%YTDLP%\" powershell -NoProfile -Command \"Invoke-WebRequest -Uri 'https://github.com/yt-dlp/yt-dlp/releases/latest/download/yt-dlp.exe' -OutFile '%YTDLP%' -UseBasicParsing\"",
      '  del /f /q "%YTDLP%:Zone.Identifier" 2>nul',
      ')',
      'if not exist "%YTDLP%" (',
      '  echo [mvt] yt-dlp download failed, check your network and retry.',
      '  pause & exit /b 1',
      ')',
      '',
      'set "FFDIR=%TOOLS%\\ffmpeg\\bin"',
      'set "FFZIP=%TOOLS%\\ffmpeg.zip"',
      'if not exist "%FFDIR%\\ffmpeg.exe" (',
      '  echo [mvt] First run: downloading ffmpeg ^(~190MB, please wait^) ...',
      '  curl.exe -L --ssl-no-revoke -o "%FFZIP%" "https://github.com/BtbN/FFmpeg-Builds/releases/latest/download/ffmpeg-master-latest-win64-gpl.zip"',
      '  for %%F in ("%FFZIP%") do if %%~zF LSS 1000000 del /f /q "%FFZIP%" >nul 2>nul',
      "  if not exist \"%FFZIP%\" powershell -NoProfile -Command \"Invoke-WebRequest -Uri 'https://github.com/BtbN/FFmpeg-Builds/releases/latest/download/ffmpeg-master-latest-win64-gpl.zip' -OutFile '%FFZIP%' -UseBasicParsing\"",
      '  if exist "%FFZIP%" (',
      '    echo [mvt] Extracting ffmpeg ...',
      '    if not exist "%TOOLS%\\ffmpeg_extract" mkdir "%TOOLS%\\ffmpeg_extract"',
      '    tar -xf "%FFZIP%" -C "%TOOLS%\\ffmpeg_extract"',
      '    for /d %%D in ("%TOOLS%\\ffmpeg_extract\\ffmpeg-*") do (',
      '      if exist "%%D\\bin\\ffmpeg.exe" xcopy /E /Y "%%D\\*" "%TOOLS%\\ffmpeg\\" >nul',
      '    )',
      '    rd /s /q "%TOOLS%\\ffmpeg_extract" >nul 2>nul',
      '    del /f /q "%FFZIP%" >nul 2>nul',
      '  )',
      ')',
      'if not exist "%FFDIR%\\ffmpeg.exe" (',
      '  echo [mvt] ffmpeg download/extract failed, check your network and retry.',
      '  del /f /q "%FFZIP%" >nul 2>nul',
      '  pause & exit /b 1',
      ')',
      '',
      'set "OUTDIR=%USERPROFILE%\\Desktop\\VideoDownloads"',
      'if not exist "%OUTDIR%" mkdir "%OUTDIR%" >nul 2>nul',
      ''
    ];
    if (direct) {
      /* 直链模式：烤进从页面提取到的 CDN 直链（自带签名，无需 cookie） */
      L.push('set "URL=' + direct + '"');
      L.push('if "%URL%"=="" (');
      L.push('  echo  [mvt] URL is empty.');
      L.push('  pause & exit /b 1');
      L.push(')');
    } else if (bakedUrl) {
      L.push('set "URL=' + bakedUrl + '"');
      L.push('if "%URL%"=="" (');
      L.push('  echo  [mvt] URL is empty.');
      L.push('  pause & exit /b 1');
      L.push(')');
    } else {
      L.push('set "URL=%~1"');
      L.push('if "%URL%"=="" (');
      L.push('  echo.');
      L.push('  echo  [mvt] Paste video URL ^(Bilibili/YouTube/etc via yt-dlp^) then Enter:');
      L.push('  set /p "URL=> "');
      L.push(')');
      L.push('if "%URL%"=="" (');
      L.push('  echo  [mvt] No URL entered.');
      L.push('  pause & exit /b 1');
      L.push(')');
    }
    L.push('');
    L.push('set "UA=' + UA + '"');
    L.push('set "REFERER=' + ref + '"');
    L.push('echo.');
    if (isDouyin && direct) {
      /* 零 cookie 直链分支：直链从页面自身数据提取（play_addr.url_list），
         自带签名查询参数，yt-dlp 只需带抖音页面的 Referer。
         Edge 156 的 ABE 加密让所有「读浏览器 cookie」的方案都不可行也不安全
         （2026-10-25 实测：带调试端口启动 Edge 会导致它物理删除解不开的
         cookie，1853→25 不可恢复），所以这条路是首选。 */
      L.push('echo  [mvt] Douyin: direct CDN link extracted from the page.');
      L.push('echo  [mvt] No cookies needed. The link is signed and expires within hours,');
      L.push('echo  [mvt] so run this bat soon after generating it.');
      L.push('"%YTDLP%" --no-playlist -f "bv*+ba/b" --merge-output-format mp4 --ffmpeg-location "%FFDIR%" --user-agent "%UA%" --referer "%REFERER%" -o "%OUTDIR%\\' + dyOut + '" -P "%OUTDIR%" --no-mtime "%URL%"');
      L.push('if errorlevel 1 (');
      L.push('  echo.');
      L.push('  echo  [mvt] ================ Direct link failed ================');
      L.push('  echo  [mvt] Most likely the signed link expired ^(valid for a few hours^).');
      L.push('  echo  [mvt]   1. Reopen the douyin video page');
      L.push('  echo  [mvt]   2. Click "download this video" again to regenerate this bat');
      L.push('  echo  [mvt] Alternative: use the toolbox "record while playing" button');
      L.push('  echo  [mvt] ^(works without any cookies^).');
      L.push('  echo  [mvt] ===================================================');
      L.push(')');
    } else if (isDouyin) {
      /* Edge 156 (ABE v20 cookies) makes ALL automatic cookie reading unsafe:
         launching Edge with --remote-debugging-port fails ABE validation and
         Edge then DELETES the undecryptable cookies from the profile DB
         (verified: 1853 cookies -> 25 on 2026-10-25). So we NEVER launch a
         debug browser here. Instead: use a pre-exported Netscape cookie file
         (Cookie-Editor extension, exported from a normal browser session). */
      L.push('echo  [mvt] Douyin detected.');
      L.push('echo  [mvt] Could not extract a direct link from the page; falling back to');
      L.push('echo  [mvt] a pre-exported cookie file. New Edge encrypts cookies ^(ABE^),');
      L.push('echo  [mvt] so auto-reading them from the browser is unsafe.');
      L.push('set "COOKIES=%OUTDIR%\\__dy_cookies.txt"');
      L.push('if not exist "%COOKIES%" set "COOKIES=%USERPROFILE%\\Desktop\\__dy_cookies.txt"');
      L.push('if exist "%COOKIES%" (');
      L.push('  echo  [mvt] Using exported cookies: %COOKIES%');
      L.push('  "%YTDLP%" --no-playlist -f "best[height<=1080]/best" --merge-output-format mp4 --ffmpeg-location "%FFDIR%" --user-agent "%UA%" --cookies "%COOKIES%" -o "%OUTDIR%\\' + dyOut + '" -P "%OUTDIR%" --no-mtime "%URL%"');
      L.push(') else (');
      L.push('  echo  [mvt] No cookie file found, trying browser cookies directly ^(fails on new Edge^) ...');
      L.push('  "%YTDLP%" --no-playlist -f "best[height<=1080]/best" --merge-output-format mp4 --ffmpeg-location "%FFDIR%" --user-agent "%UA%" --cookies-from-browser edge -o "%OUTDIR%\\' + dyOut + '" -P "%OUTDIR%" --no-mtime "%URL%"');
      L.push(')');
      L.push('if errorlevel 1 (');
      L.push('  echo.');
      L.push('  echo  [mvt] ================ Douyin cookie setup ================');
      L.push('  echo  [mvt] Douyin needs login cookies. One-time setup ^(~5 min^):');
      L.push('  echo  [mvt]   1. Install the "Cookie-Editor" extension in Edge');
      L.push('  echo  [mvt]   2. Open douyin.com and make sure you are logged in');
      L.push('  echo  [mvt]   3. Cookie-Editor icon - Export - Netscape format');
      L.push('  echo  [mvt]   4. Save the file as: %OUTDIR%\\__dy_cookies.txt');
      L.push('  echo  [mvt]   5. Run this bat again');
      L.push('  echo  [mvt] Alternative: use the toolbox "record while playing" button');
      L.push('  echo  [mvt] ^(works without any cookies^).');
      L.push('  echo  [mvt] =====================================================');
      L.push(')');
    } else {
      L.push('echo  [mvt] Downloading ... output dir: %OUTDIR%');
      L.push('echo.');
      L.push('"%YTDLP%" --no-playlist -f "bv*+ba/b" --merge-output-format mp4 --ffmpeg-location "%FFDIR%" --user-agent "%UA%" --referer "%REFERER%" --trim-filenames 120 -P "%OUTDIR%" --no-mtime "%URL%"');
    }
    L.push('');
    L.push('echo.');
    L.push('if errorlevel 1 ( echo  [mvt] Download failed, see info above. ) else ( echo  [mvt] Done, file in: %OUTDIR% )');
    if (isDouyin) {
      L.push('if errorlevel 1 (set "OK=") else (set "OK=1")');
      L.push('if defined OK set "LATEST="');
      L.push('if defined OK for /f "delims=" %%F in (\'dir /b /o-d "%OUTDIR%\\douyin_*.mp4" 2^>nul\') do if not defined LATEST set "LATEST=%OUTDIR%\\%%F"');
      /* 时长自检：ffprobe 输出重定向到临时文件再读（for /f 命令串会吞掉
         `=` 导致 -of csv=p=0 参数错乱，所以不能直接在 for /f 里跑 ffprobe）。 */
      L.push('if defined OK if defined LATEST set "TMPDUR=%TEMP%\\mvt_dur.tmp"');
      L.push('if defined OK if defined LATEST del /f /q "%TMPDUR%" 2>nul');
      L.push('if defined OK if defined LATEST "%FFDIR%\\ffprobe.exe" -v error -show_entries format=duration -of csv=p=0 "%LATEST%" > "%TMPDUR%" 2>nul');
      L.push('if defined OK if defined LATEST set /p DUR=<"%TMPDUR%"');
      L.push('if defined OK if defined LATEST del /f /q "%TMPDUR%" 2>nul');
      L.push('if defined OK if defined DUR for /f "tokens=1 delims=." %%N in ("%DUR%") do if %%N LSS 15 (');
      L.push('  echo.');
      L.push('  echo  [mvt] WARNING: only ~%%Ns downloaded - looks like the 5s preview.');
      L.push('  echo  [mvt] Log in to douyin.com in your browser, reopen this page, then');
      L.push('  echo  [mvt] regenerate this bat to get the full video.');
      L.push(')');
    }
    L.push('pause');
    L.push('rem Self-delete this bat after the window is closed.');
    L.push('(goto) 2>nul & del "%~f0"');
    return L.join('\r\n') + '\r\n';
  }

  function fmtTime(sec) {
    sec = Math.max(0, Math.floor(sec || 0));
    var h = Math.floor(sec / 3600), m = Math.floor((sec % 3600) / 60), s = sec % 60;
    var p = function (n) { return n < 10 ? '0' + n : '' + n; };
    return p(h) + ':' + p(m) + ':' + p(s);
  }

  /* ================= 片段下载：暂停→记录当前播放点→前后各留 N 秒 =================
   * 先下完整视频到临时目录，再用 ffmpeg 按时间精确裁剪出片段（全站通用、边界精确）。
   * 自举补齐 yt-dlp/ffmpeg，重装系统后也能用。 */
  function buildYtDlpSegBat(startSec, endSec, bakedUrl, pageUrl) {
    var S = fmtTime(startSec), E = fmtTime(endSec);
    /* 防盗链：直接拿到的 bilivideo CDN 直链必须同时带浏览器 UA + B站 Referer，
     * 只带 Referer 也是 403（已实测）。所以烤两个 Referer，第一个失败自动换第二个重试。 */
    var isCdn = /bilivideo\.com|bilivod\.com|bilicdn/i.test(bakedUrl);
    var pg = (pageUrl && /^https?:/i.test(pageUrl)) ? String(pageUrl).split('#')[0] : 'https://www.bilibili.com/';
    var REF1 = isCdn ? 'https://www.bilibili.com/' : pg;
    var REF2 = isCdn ? pg : 'https://www.bilibili.com/';
    var UA = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/138.0.0.0 Safari/537.36';
    function pad(n) { return n < 10 ? '0' + n : '' + n; }
    function fn(sec) {
      sec = Math.max(0, Math.floor(sec || 0));
      return pad(Math.floor(sec / 3600)) + pad(Math.floor((sec % 3600) / 60)) + pad(sec % 60);
    }
    var outName = 'clip_' + fn(startSec) + '-' + fn(endSec) + '.mp4';
    var L = [
      '@echo off',
      'rem This .bat is intentionally ASCII-only (English prompts). cmd.exe has a 4KB read-buffer',
      'rem bug with chcp 65001 + UTF-8: a multi-byte char straddling the boundary splits a Chinese',
      'rem echo line and runs the tail as a command. ASCII avoids the bug entirely.',
      '',
      'set "TOOLS=%LOCALAPPDATA%\\mvt\\bin"',
      'if not exist "%TOOLS%" mkdir "%TOOLS%" >nul 2>nul',
      'set "YTDLP=%TOOLS%\\yt-dlp.exe"',
      'if not exist "%YTDLP%" (',
      '  echo [mvt] First run: downloading yt-dlp ...',
      '  curl.exe -L --ssl-no-revoke -o "%YTDLP%" "https://github.com/yt-dlp/yt-dlp/releases/latest/download/yt-dlp.exe"',
      '  for %%F in ("%YTDLP%") do if %%~zF LSS 1000000 del /f /q "%YTDLP%" >nul 2>nul',
      "  if not exist \"%YTDLP%\" powershell -NoProfile -Command \"Invoke-WebRequest -Uri 'https://github.com/yt-dlp/yt-dlp/releases/latest/download/yt-dlp.exe' -OutFile '%YTDLP%' -UseBasicParsing\"",
      '  del /f /q "%YTDLP%:Zone.Identifier" 2>nul',
      ')',
      'if not exist "%YTDLP%" (',
      '  echo [mvt] yt-dlp download failed, check your network and retry.',
      '  pause & exit /b 1',
      ')',
      '',
      'set "FFDIR=%TOOLS%\\ffmpeg\\bin"',
      'set "FFZIP=%TOOLS%\\ffmpeg.zip"',
      'if not exist "%FFDIR%\\ffmpeg.exe" (',
      '  echo [mvt] First run: downloading ffmpeg ^(~190MB, please wait^) ...',
      '  curl.exe -L --ssl-no-revoke -o "%FFZIP%" "https://github.com/BtbN/FFmpeg-Builds/releases/latest/download/ffmpeg-master-latest-win64-gpl.zip"',
      '  for %%F in ("%FFZIP%") do if %%~zF LSS 1000000 del /f /q "%FFZIP%" >nul 2>nul',
      "  if not exist \"%FFZIP%\" powershell -NoProfile -Command \"Invoke-WebRequest -Uri 'https://github.com/BtbN/FFmpeg-Builds/releases/latest/download/ffmpeg-master-latest-win64-gpl.zip' -OutFile '%FFZIP%' -UseBasicParsing\"",
      '  if exist "%FFZIP%" (',
      '    echo [mvt] Extracting ffmpeg ...',
      '    if not exist "%TOOLS%\\ffmpeg_extract" mkdir "%TOOLS%\\ffmpeg_extract"',
      '    tar -xf "%FFZIP%" -C "%TOOLS%\\ffmpeg_extract"',
      '    for /d %%D in ("%TOOLS%\\ffmpeg_extract\\ffmpeg-*") do (',
      '      if exist "%%D\\bin\\ffmpeg.exe" xcopy /E /Y "%%D\\*" "%TOOLS%\\ffmpeg\\" >nul',
      '    )',
      '    rd /s /q "%TOOLS%\\ffmpeg_extract" >nul 2>nul',
      '    del /f /q "%FFZIP%" >nul 2>nul',
      '  )',
      ')',
      'if not exist "%FFDIR%\\ffmpeg.exe" (',
      '  echo [mvt] ffmpeg download/extract failed, check your network and retry.',
      '  del /f /q "%FFZIP%" >nul 2>nul',
      '  pause & exit /b 1',
      ')',
      '',
      'set "OUTDIR=%USERPROFILE%\\Desktop\\VideoDownloads"',
      'if not exist "%OUTDIR%" mkdir "%OUTDIR%" >nul 2>nul',
      'set "URL=' + bakedUrl + '"',
      'if "%URL%"=="" (',
      '  echo  [mvt] URL is empty.',
      '  pause & exit /b 1',
      ')',
      '',
      'set "TMPD=%OUTDIR%\\__seg_tmp"',
      'if not exist "%TMPD%" mkdir "%TMPD%"',
      'set "UA=' + UA + '"',
      'set "REF1=' + REF1 + '"',
      'set "REF2=' + REF2 + '"',
      'echo.',
      'echo  [mvt] Step 1/2: downloading full video to temp dir...',
      '"%YTDLP%" --no-playlist -f "bv*+ba/b" --merge-output-format mp4 --ffmpeg-location "%FFDIR%" --retries 10 --fragment-retries 10 --user-agent "%UA%" --referer "%REF1%" -o "%TMPD%\\full.%%(ext)s" --no-mtime "%URL%"',
      'set "FULL="',
      'for %%F in ("%TMPD%\\full.*") do if /i not "%%~xF"==".part" set "FULL=%%~fF"',
      'if not defined FULL (',
      '  echo  [mvt] First attempt failed ^(maybe hotlink-protected^); retrying with Referer=' + REF2 + ' ...',
      '  "%YTDLP%" --no-playlist -f "bv*+ba/b" --merge-output-format mp4 --ffmpeg-location "%FFDIR%" --retries 10 --fragment-retries 10 --user-agent "%UA%" --referer "%REF2%" -o "%TMPD%\\full.%%(ext)s" --no-mtime "%URL%"',
      '  for %%F in ("%TMPD%\\full.*") do if /i not "%%~xF"==".part" set "FULL=%%~fF"',
      ')',
      /* 第三招：奇艺/腾讯/优酷这类必须登录才给视频，用浏览器已登录的 cookie 再试一次 */
      'if not defined FULL (',
      '  echo  [mvt] Still failing; retrying with browser login state ^(Edge cookies^) ...',
      '  echo  [mvt] Force-closing Edge to unlock its cookie DB ^(your open tabs will close; Edge offers to restore them on next launch^) ...',
      '  taskkill /F /IM msedge.exe >nul 2>nul',
      '  ping -n 2 127.0.0.1 >nul',
      '  taskkill /F /IM msedge.exe >nul 2>nul',
      '  "%YTDLP%" --no-playlist -f "bv*+ba/b" --merge-output-format mp4 --ffmpeg-location "%FFDIR%" --retries 10 --fragment-retries 10 --cookies-from-browser edge -o "%TMPD%\\full.%%(ext)s" --no-mtime "%URL%"',
      '  for %%F in ("%TMPD%\\full.*") do if /i not "%%~xF"==".part" set "FULL=%%~fF"',
      ')',
      'if not defined FULL (',
      '  echo  [mvt] Full video download failed, see info above.',
      '  echo  [mvt] If link has signed params ^(deadline/e=^), it may have expired: replay it on the page then regenerate the script.',
      '  pause & exit /b 1',
      ')',
      'echo.',
      'echo  [mvt] Step 2/2: ffmpeg precise cut ' + S + ' to ' + E + ', saving as ' + outName,
      '"%FFDIR%\\ffmpeg.exe" -ss ' + S + ' -to ' + E + ' -i "%FULL%" -c:v libx264 -c:a aac -preset veryfast "%OUTDIR%\\' + outName + '"',
      'echo.',
      'if errorlevel 1 ( echo  [mvt] Cut failed, full video kept in %TMPD% ) else ( echo  [mvt] Done: %OUTDIR%\\' + outName + ' )',
      'del /f /q "%TMPD%\\full.*" 2>nul',
      'rd /s /q "%TMPD%" 2>nul',
      'pause'
    ];
    return L.join('\r\n') + '\r\n';
  }

  function genSegBat() {
    var v = cur;
    if (!v || !v.currentTime) { toast('没有正在播放的视频，无法定位播放点', 3000); return; }
    var ct = v.currentTime;
    var page = String(location.href || '').split('#')[0];
    var url = page;
    if (!/bilibili\.com/i.test(url) && cur) {
      var s = cur.currentSrc || cur.src || '';
      if (s && s.indexOf('http') === 0) url = s;
    }
    if (!url) { toast('拿不到视频地址', 3000); return; }
    showSegPanel(ct, url, page);
  }

  function showSegPanel(ct, url, page) {
    var mask = document.createElement('div');
    mask.style.cssText = 'position:fixed;inset:0;background:rgba(0,0,0,.35);z-index:2147483646;';
    var card = document.createElement('div');
    card.style.cssText = 'position:fixed;left:50%;top:50%;transform:translate(-50%,-50%);background:#fff;color:#222;'
      + 'border:1px solid #ccc;border-radius:10px;padding:18px 20px;z-index:2147483647;'
      + 'font:14px/1.6 system-ui,sans-serif;box-shadow:0 8px 30px rgba(0,0,0,.25);min-width:300px;';
    card.innerHTML =
      '<div style="font-weight:700;margin-bottom:10px;">片段下载 · 当前播放点 <span style="color:#c33a2e;">'
      + fmtTime(ct) + '</span></div>'
      + '<div style="margin:6px 0;">前留 <input id="mvtSegB" type="number" value="30" min="0" style="width:64px;"> 秒</div>'
      + '<div style="margin:6px 0;">后留 <input id="mvtSegA" type="number" value="30" min="0" style="width:64px;"> 秒</div>'
      + '<div style="margin-top:10px;color:#888;font-size:12px;">将下载：<span id="mvtSegPrev"></span>（整段下完再用 ffmpeg 精确裁剪）</div>'
      + '<div style="margin-top:14px;text-align:right;">'
      + '<button id="mvtSegCancel" style="background:#eee;color:#333;border:0;border-radius:6px;padding:6px 14px;cursor:pointer;">取消</button>'
      + '<button id="mvtSegOk" style="background:#4ec98a;color:#fff;border:0;border-radius:6px;padding:6px 14px;cursor:pointer;margin-left:8px;">生成下载脚本</button>'
      + '</div>';
    function close() { if (mask.parentNode) mask.parentNode.removeChild(mask); }
    mask.appendChild(card);
    document.body.appendChild(mask);
    function upd() {
      var b = parseFloat(document.getElementById('mvtSegB').value) || 0;
      var a = parseFloat(document.getElementById('mvtSegA').value) || 0;
      document.getElementById('mvtSegPrev').textContent =
        fmtTime(Math.max(0, ct - b)) + ' ~ ' + fmtTime(ct + a);
    }
    document.getElementById('mvtSegB').addEventListener('input', upd);
    document.getElementById('mvtSegA').addEventListener('input', upd);
    document.getElementById('mvtSegCancel').addEventListener('click', close);
    document.getElementById('mvtSegOk').addEventListener('click', function () {
      var b = parseFloat(document.getElementById('mvtSegB').value) || 0;
      var a = parseFloat(document.getElementById('mvtSegA').value) || 0;
      var start = Math.max(0, Math.floor(ct - b));
      var end = Math.floor(ct + a);
      var bat = buildYtDlpSegBat(start, end, url, page);
      saveBlob(new Blob([bat], { type: 'application/octet-stream' }), '片段下载.bat');
      if (navigator.clipboard && navigator.clipboard.writeText) {
        navigator.clipboard.writeText(bat).then(
          function () { close(); toast('已生成「片段下载.bat」并复制，双击即下 ' + fmtTime(start) + '~' + fmtTime(end) + '（首次自动拉依赖）', 6000); },
          function () { close(); toast('已生成「片段下载.bat」，双击即下 ' + fmtTime(start) + '~' + fmtTime(end), 4000); }
        );
      } else {
        close(); toast('已生成「片段下载.bat」，双击即下 ' + fmtTime(start) + '~' + fmtTime(end), 4000);
      }
    });
    mask.addEventListener('click', function (e) { if (e.target === mask) close(); });
    upd();
  }

  /* ================= 去片头广告：跳过前 N 秒 =================
   * 两种用法：① 双击后粘贴链接（先下载再裁）；② 把本地视频文件拖到生成的 bat 上直接裁。
   *
   * 【裁剪写法实测结论】（源 60s / GOP 10s / -ss 7，本机 ffmpeg N-128013 实测）
   *   A: -ss 前置 + -c copy + avoid_negative_ts → 输出 60s，根本没裁（退到上一个关键帧后全部保留）✗
   *   B: -ss 前置 + -c copy（不带 avoid_negative_ts）→ 时长对但首帧非关键帧，开头花屏 ✗
   *   C: -ss 前置 + 全重编码 + avoid_negative_ts → 53.03s，首帧关键帧，音视频同步 ✓（默认采用）
   *   D: -ss 前置 + 视频重编 + 音频 copy → 音频 pts 从 0 起、视频从 7 起，音画错位 7 秒 ✗
   *   E: -ss 后置 + -c copy + avoid_negative_ts → 52.98s，首帧是关键帧，但开头静止 0~GOP 秒 ⭕（极速档）
   * 结论：想要精确+干净必须重编码；音频绝不能用 -c copy（会不跟着裁）。 */
  function buildYtDlpAdBat(skipSec, bakedUrl, pageUrl, mode) {
    var fast = (mode === 'fast');
    var skip = fmtTime(skipSec);
    function pad(n) { return n < 10 ? '0' + n : '' + n; }
    function fn(sec) {
      sec = Math.max(0, Math.floor(sec || 0));
      return pad(Math.floor(sec / 3600)) + pad(Math.floor((sec % 3600) / 60)) + pad(sec % 60);
    }
    var outName = 'no_ad_' + fn(skipSec) + (fast ? '_fast' : '') + '.mp4';
    var isCdn = /bilivideo\.com|bilivod\.com|bilicdn/i.test(bakedUrl || '');
    var pg = (pageUrl && /^https?:/i.test(pageUrl)) ? String(pageUrl).split('#')[0] : 'https://www.bilibili.com/';
    var REF1 = isCdn ? 'https://www.bilibili.com/' : pg;
    var REF2 = isCdn ? pg : 'https://www.bilibili.com/';
    var UA = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/138.0.0.0 Safari/537.36';
    var L = [
      '@echo off',
      'rem This .bat is intentionally ASCII-only (English prompts). cmd.exe has a 4KB read-buffer',
      'rem bug with chcp 65001 + UTF-8: a multi-byte char straddling the boundary splits a Chinese',
      'rem echo line and runs the tail as a command. ASCII avoids the bug entirely.',
      '',
      'set "TOOLS=%LOCALAPPDATA%\\mvt\\bin"',
      'if not exist "%TOOLS%" mkdir "%TOOLS%" >nul 2>nul',
      'set "YTDLP=%TOOLS%\\yt-dlp.exe"',
      'if not exist "%YTDLP%" (',
      '  echo [mvt] First run: downloading yt-dlp ...',
      '  curl.exe -L --ssl-no-revoke -o "%YTDLP%" "https://github.com/yt-dlp/yt-dlp/releases/latest/download/yt-dlp.exe"',
      '  for %%F in ("%YTDLP%") do if %%~zF LSS 1000000 del /f /q "%YTDLP%" >nul 2>nul',
      "  if not exist \"%YTDLP%\" powershell -NoProfile -Command \"Invoke-WebRequest -Uri 'https://github.com/yt-dlp/yt-dlp/releases/latest/download/yt-dlp.exe' -OutFile '%YTDLP%' -UseBasicParsing\"",
      '  del /f /q "%YTDLP%:Zone.Identifier" 2>nul',
      ')',
      'if not exist "%YTDLP%" (',
      '  echo [mvt] yt-dlp download failed, check your network and retry.',
      '  pause & exit /b 1',
      ')',
      '',
      'set "FFDIR=%TOOLS%\\ffmpeg\\bin"',
      'set "FFZIP=%TOOLS%\\ffmpeg.zip"',
      'if not exist "%FFDIR%\\ffmpeg.exe" (',
      '  echo [mvt] First run: downloading ffmpeg ^(~190MB, please wait^) ...',
      '  curl.exe -L --ssl-no-revoke -o "%FFZIP%" "https://github.com/BtbN/FFmpeg-Builds/releases/latest/download/ffmpeg-master-latest-win64-gpl.zip"',
      '  for %%F in ("%FFZIP%") do if %%~zF LSS 1000000 del /f /q "%FFZIP%" >nul 2>nul',
      "  if not exist \"%FFZIP%\" powershell -NoProfile -Command \"Invoke-WebRequest -Uri 'https://github.com/BtbN/FFmpeg-Builds/releases/latest/download/ffmpeg-master-latest-win64-gpl.zip' -OutFile '%FFZIP%' -UseBasicParsing\"",
      '  if exist "%FFZIP%" (',
      '    echo [mvt] Extracting ffmpeg ...',
      '    if not exist "%TOOLS%\\ffmpeg_extract" mkdir "%TOOLS%\\ffmpeg_extract"',
      '    tar -xf "%FFZIP%" -C "%TOOLS%\\ffmpeg_extract"',
      '    for /d %%D in ("%TOOLS%\\ffmpeg_extract\\ffmpeg-*") do (',
      '      if exist "%%D\\bin\\ffmpeg.exe" xcopy /E /Y "%%D\\*" "%TOOLS%\\ffmpeg\\" >nul',
      '    )',
      '    rd /s /q "%TOOLS%\\ffmpeg_extract" >nul 2>nul',
      '    del /f /q "%FFZIP%" >nul 2>nul',
      '  )',
      ')',
      'if not exist "%FFDIR%\\ffmpeg.exe" (',
      '  echo [mvt] ffmpeg download/extract failed, check your network and retry.',
      '  del /f /q "%FFZIP%" >nul 2>nul',
      '  pause & exit /b 1',
      ')',
      '',
      'set "OUTDIR=%USERPROFILE%\\Desktop\\VideoDownloads"',
      'if not exist "%OUTDIR%" mkdir "%OUTDIR%" >nul 2>nul',
      'set "SKIP=' + skip + '"',
      'set "UA=' + UA + '"',
      'set "REF1=' + REF1 + '"',
      'set "REF2=' + REF2 + '"',
      'set "INPUT=%~1"',
      'set "TMPD=%OUTDIR%\\__ad_tmp"',
      ''
    ];
    if (bakedUrl) {
      L.push('set "URL=' + bakedUrl + '"');
    } else {
      L.push('set "URL="');
    }
    L.push('set "SRC="');
    L.push('if exist "%INPUT%" set "SRC=%INPUT%"');
    L.push('if defined SRC (');
    L.push('  echo.');
    L.push('  echo  [mvt] Processing local file directly: %SRC%');
    L.push(') else (');
    L.push('  if "%URL%"=="" (');
    L.push('    echo.');
    L.push('    echo  [mvt] Paste video URL ^(or drag a local video file onto this .bat^) then Enter:');
    L.push('    set /p "URL=> "');
    L.push('  )');
    L.push('  if "%URL%"=="" (');
    L.push('    echo  [mvt] Neither local file nor URL given, exiting.');
    L.push('    pause & exit /b 1');
    L.push('  )');
    L.push('  if not exist "%TMPD%" mkdir "%TMPD%"');
    L.push('  echo.');
    L.push('  echo  [mvt] Step 1/2: downloading full video to temp dir...');
    L.push('  "%YTDLP%" --no-playlist -f "bv*+ba/b" --merge-output-format mp4 --ffmpeg-location "%FFDIR%" --retries 10 --fragment-retries 10 --user-agent "%UA%" --referer "%REF1%" -o "%TMPD%\\full.%%(ext)s" --no-mtime "%URL%"');
    L.push('  for %%F in ("%TMPD%\\full.*") do if /i not "%%~xF"==".part" set "SRC=%%~fF"');
    L.push('  if not defined SRC (');
    L.push('    echo  [mvt] First attempt failed ^(maybe hotlink-protected^); retrying with Referer=' + REF2 + ' ...');
    L.push('    "%YTDLP%" --no-playlist -f "bv*+ba/b" --merge-output-format mp4 --ffmpeg-location "%FFDIR%" --retries 10 --fragment-retries 10 --user-agent "%UA%" --referer "%REF2%" -o "%TMPD%\\full.%%(ext)s" --no-mtime "%URL%"');
    L.push('    for %%F in ("%TMPD%\\full.*") do if /i not "%%~xF"==".part" set "SRC=%%~fF"');
    L.push('  )');
    /* 第三招：奇艺/腾讯/优酷这类必须登录才给视频，用浏览器已登录的 cookie 再试一次 */
    L.push('  if not defined SRC (');
    L.push('    echo  [mvt] Still failing; retrying with browser login state ^(Edge cookies^) ...');
    L.push('    echo  [mvt] Force-closing Edge to unlock its cookie DB ^(your open tabs will close; Edge offers to restore them on next launch^) ...');
    L.push('    taskkill /F /IM msedge.exe >nul 2>nul');
    L.push('    ping -n 2 127.0.0.1 >nul');
    L.push('    taskkill /F /IM msedge.exe >nul 2>nul');
    L.push('    "%YTDLP%" --no-playlist -f "bv*+ba/b" --merge-output-format mp4 --ffmpeg-location "%FFDIR%" --retries 10 --fragment-retries 10 --cookies-from-browser edge -o "%TMPD%\\full.%%(ext)s" --no-mtime "%URL%"');
    L.push('    for %%F in ("%TMPD%\\full.*") do if /i not "%%~xF"==".part" set "SRC=%%~fF"');
    L.push('  )');
    L.push(')');
    L.push('if not defined SRC (');
    L.push('  echo  [mvt] Could not get video source, see info above.');
    L.push('  echo  [mvt] iQiyi/Tencent/Youku need Edge login; the script retries with login state.');
    L.push('  echo  [mvt] If still failing, use 5^) live-record ^(it auto-skips ads while recording^).');
    L.push('  pause & exit /b 1');
    L.push(')');
    L.push('echo.');
    if (fast) {
      L.push('echo  [mvt] Step 2/2: skip intro ' + skip + '^(no re-encode, instant^)...');
      L.push('"%FFDIR%\\ffmpeg.exe" -i "%SRC%" -ss ' + skip + ' -c copy -avoid_negative_ts make_zero -movflags +faststart "%OUTDIR%\\' + outName + '"');
    } else {
      L.push('echo  [mvt] Step 2/2: skip intro ' + skip + '^(re-encode, frame-accurate, please wait for long videos^)...');
      L.push('"%FFDIR%\\ffmpeg.exe" -ss ' + skip + ' -i "%SRC%" -c:v libx264 -preset veryfast -crf 20 -c:a aac -b:a 192k -avoid_negative_ts make_zero -movflags +faststart "%OUTDIR%\\' + outName + '"');
    }
    L.push('echo.');
    L.push('if errorlevel 1 ( echo  [mvt] Failed, see info above. ) else ( echo  [mvt] Done: %OUTDIR%\\' + outName + ' )');
    L.push('if defined TMPD rd /s /q "%TMPD%" 2>nul');
    L.push('pause');
    return L.join('\r\n') + '\r\n';
  }

  function genAdBat() {
    var url = '';
    var page = String(location.href || '').split('#')[0];
    var v = cur;
    if (v) {
      var s = v.currentSrc || v.src || '';
      if (/bilibili\.com/i.test(page)) url = page;
      else if (s && s.indexOf('http') === 0) url = s;
    }
    showAdPanel(url, page);
  }

  function showAdPanel(url, page) {
    var mask = document.createElement('div');
    mask.style.cssText = 'position:fixed;inset:0;background:rgba(0,0,0,.35);z-index:2147483646;';
    var card = document.createElement('div');
    card.style.cssText = 'position:fixed;left:50%;top:50%;transform:translate(-50%,-50%);background:#fff;color:#222;'
      + 'border:1px solid #ccc;border-radius:10px;padding:18px 20px;z-index:2147483647;'
      + 'font:14px/1.6 system-ui,sans-serif;box-shadow:0 8px 30px rgba(0,0,0,.25);min-width:320px;';
    card.innerHTML =
      '<div style="font-weight:700;margin-bottom:10px;">去片头广告</div>'
      + '<div style="margin:6px 0;">跳过前 <input id="mvtAdS" type="number" value="90" min="0" step="1" style="width:70px;"> 秒</div>'
      + '<div style="margin:10px 0 4px;font-size:13px;">裁剪方式</div>'
      + '<label style="display:block;font-size:12px;margin:3px 0;cursor:pointer;">'
      + '<input type="radio" name="mvtAdMode" value="accurate" checked> 精确（重编码，分秒不差；1 小时片约几分钟）</label>'
      + '<label style="display:block;font-size:12px;margin:3px 0;cursor:pointer;">'
      + '<input type="radio" name="mvtAdMode" value="fast"> 极速（不重编码，秒级完成；开头可能静止几秒）</label>'
      + '<div style="margin-top:10px;color:#888;font-size:12px;">生成后：双击 bat 粘贴链接下载，或把本地视频文件拖到 bat 上直接裁。</div>'
      + '<div style="margin-top:6px;color:#888;font-size:12px;">不重编码无法精确落点（要对齐关键帧），所以默认走重编码。</div>'
      + '<div style="margin-top:14px;text-align:right;">'
      + '<button id="mvtAdCancel" style="background:#eee;color:#333;border:0;border-radius:6px;padding:6px 14px;cursor:pointer;">取消</button>'
      + '<button id="mvtAdOk" style="background:#4ec98a;color:#fff;border:0;border-radius:6px;padding:6px 14px;cursor:pointer;margin-left:8px;">生成脚本</button>'
      + '</div>';
    function close() { if (mask.parentNode) mask.parentNode.removeChild(mask); }
    mask.appendChild(card);
    document.body.appendChild(mask);
    document.getElementById('mvtAdCancel').addEventListener('click', close);
    document.getElementById('mvtAdOk').addEventListener('click', function () {
      var sk = Math.max(0, Math.floor(parseFloat(document.getElementById('mvtAdS').value) || 0));
      var md = 'accurate';
      var rs = document.getElementsByName('mvtAdMode');
      for (var i = 0; i < rs.length; i++) if (rs[i].checked) md = rs[i].value;
      var bat = buildYtDlpAdBat(sk, url, page, md);
      saveBlob(new Blob([bat], { type: 'application/octet-stream' }), '去片头广告.bat');
      var tip = '已生成「去片头广告.bat」：跳过前 ' + sk + ' 秒（' + (md === 'fast' ? '极速' : '精确') + '）';
      if (navigator.clipboard && navigator.clipboard.writeText) {
        navigator.clipboard.writeText(bat).then(
          function () { close(); toast(tip + '，已复制；可拖本地文件进去', 6000); },
          function () { close(); toast(tip, 4000); }
        );
      } else {
        close(); toast(tip, 4000);
      }
    });
    mask.addEventListener('click', function (e) { if (e.target === mask) close(); });
  }

  /* ================= 下载模式四：生成本地下载脚本（yt-dlp，最稳） =================
   * 把「当前视频 URL」烤进一个自举 .bat：双击即用，首次运行自动补齐 yt-dlp/ffmpeg，
   * 不依赖本机 Python / WinGet，重装系统后也能用。等价桌面那个 视频下载合并.bat。 */
  function genDownBat() {
    var url = String(location.href || '').split('#')[0];
    if (!/bilibili\.com/i.test(url) && cur) {
      var s = cur.currentSrc || cur.src || '';
      if (s && s.indexOf('http') === 0) url = s;
    }
    if (!url) { toast('拿不到当前视频地址', 3000); return; }

    /* 抖音：modal_id 转单视频页；再从页面数据提取直链（零 cookie 首选方案） */
    var isDouyin = /douyin\.com/i.test(url);
    var dyId = '', dyVid = null;
    if (isDouyin) {
      var m = url.match(/[?&]modal_id=(\d+)/i);
      if (m) {
        url = 'https://www.douyin.com/video/' + m[1];
        toast('已转为单视频页: ' + url, 3000);
      }
      /* 从 /video/<id> 提取数字 ID，用于固定输出文件名 */
      /* （CDN URL 的查询串曾被 yt-dlp 当标题/ID，400+ 字符导致 Errno 22） */
      var idm = url.match(/\/video\/(\d+)/);
      if (idm) dyId = idm[1];
      /* 页面内提取直链：网络钩子 / _ROUTER_DATA / RENDER_DATA / React fiber。
         详情页按 ID 精确匹配；feed 页（URL 无 /video/）用当前播放的 fiber 数据。 */
      dyVid = dyGetVideo(dyId);
      if (!dyVid && !dyId) {
        toast('抖音链接不是视频页，请打开具体视频后再试', 4000);
        return;
      }
    }

    var bat = buildYtDlpBat(url, isDouyin, dyId, dyVid);
    saveBlob(new Blob([bat], { type: 'application/octet-stream' }), '下载本视频.bat');
    if (navigator.clipboard && navigator.clipboard.writeText) {
      navigator.clipboard.writeText(bat).then(
        function () {
          toast(dyVid
            ? '已生成「下载本视频.bat」并复制：走页面直链、无需 cookie；直链有效期只有几小时，尽快双击运行'
            : '已生成「下载本视频.bat」并复制命令，双击即自动下载合并（首次会先拉取依赖）', 6000);
        },
        function () { toast('已生成「下载本视频.bat」，双击即自动下载合并', 4000); }
      );
    } else {
      toast('已生成「下载本视频.bat」，双击即自动下载合并', 4000);
    }
  }

  /* ================= 下载模式五：生成「通用」下载脚本（运行后粘贴任意链接） =================
   * 等价桌面那个 视频下载合并.bat，但更稳：自举补齐 yt-dlp/ffmpeg，不限 B站、不限是否在视频页。 */
  function genDownBatGeneric() {
    var bat = buildYtDlpBat('', false);
    saveBlob(new Blob([bat], { type: 'application/octet-stream' }), '视频下载合并.bat');
    if (navigator.clipboard && navigator.clipboard.writeText) {
      navigator.clipboard.writeText(bat).then(
        function () { toast('已生成「视频下载合并.bat」（通用版，运行后粘贴任意链接，首次自动拉依赖），命令已复制', 6000); },
        function () { toast('已生成「视频下载合并.bat」（通用版，运行后粘贴任意链接）', 4000); }
      );
    } else {
      toast('已生成「视频下载合并.bat」（通用版，运行后粘贴任意链接）', 4000);
    }
  }

  /* ================= 下载模式三：边播边录（兜底，已修多个坑） ================= */
  var mvtRecording = false;
  var segRunning = false, segAbort = false;   /* 分片下载进行中 / 用户取消 */
  var mvtStopFn = null;                       /* 录制进行时的停止回调 */
  var stopBtn = null;                         /* 工具栏上的「停止」按钮 */

  function showStop(show) {
    if (stopBtn) stopBtn.style.display = show ? '' : 'none';
  }
  function mergeRecord(v) {
    if (!v) return;
    if (mvtRecording) { toast('正在合成中，请稍候'); return; }
    if (!window.MediaRecorder) { toast('浏览器不支持录制合成'); return; }

    var stream;
    try {
      stream = v.captureStream ? v.captureStream()
             : (v.mozCaptureStream ? v.mozCaptureStream() : null);
    } catch (e) { toast('该视频受保护，无法捕获合成'); return; }
    if (!stream || !stream.getVideoTracks().length) { toast('无法捕获视频流，无法合成'); return; }

    var mime = '';
    ['video/webm;codecs=vp9,opus', 'video/webm;codecs=vp8,opus', 'video/webm'].forEach(function (t) {
      if (!mime && window.MediaRecorder.isTypeSupported(t)) mime = t;
    });
    var rec;
    try { rec = new MediaRecorder(stream, mime ? { mimeType: mime } : undefined); }
    catch (e) { toast('录制器启动失败'); return; }

    mvtRecording = true;
    var chunks = [];
    var wasRate = v.playbackRate, wasMuted = v.muted, wasVol = v.volume, wasLoop = v.loop;
    var stopped = false, iv = null, hardStop = null, visFn = null;

    function cleanup() {
      mvtRecording = false;
      mvtStopFn = null;
      showStop(false);
      clearInterval(iv); clearTimeout(hardStop);
      v.playbackRate = wasRate; v.muted = wasMuted; v.volume = wasVol; v.loop = wasLoop;
      if (visFn) document.removeEventListener('visibilitychange', visFn);
      /* 释放捕获流，否则元素声音可能被劫持变哑 */
      try { stream.getTracks().forEach(function (t) { t.stop(); }); } catch (e) {}
    }

    rec.ondataavailable = function (e) { if (e.data && e.data.size) chunks.push(e.data); };
    rec.onerror = function (e) {
      toast('录制出错：' + ((e.error && e.error.name) || '未知'), 4000);
      finish();
    };

    function finish() {
      if (stopped) return;
      stopped = true;
      try { if (rec.state !== 'inactive') rec.stop(); } catch (e) {}
      try { v.pause(); } catch (e) {}   /* 停止即停播，不再让视频空转 */
    }

    rec.onstop = function () {
      cleanup();
      var b = new Blob(chunks, { type: 'video/webm' });
      if (b.size < 1000) { toast('合成失败：没录到内容'); return; }
      saveBlob(b, safeName() + '_合成_' + stamp() + '.webm');
      toast('合成完成（' + Math.round(b.size / 1048576) + ' MB）', 4000);
    };

    var dur = (isFinite(v.duration) && v.duration > 0) ? v.duration : 0;

    v.addEventListener('ended', function () { finish(); }, { once: true });

    /* 切后台会被浏览器降频，直接导致丢帧 —— 明确警告 */
    visFn = function () {
      if (document.hidden) toast('⚠ 页面切到后台会导致录制丢帧！请保持本页面在前台', 5000);
    };
    document.addEventListener('visibilitychange', visFn);

    function begin() {
      try { if (v.currentTime > 0.5) v.currentTime = 0; } catch (e) {}
      /* 关键修复：必须强制原速。倍速播放会让流"快进"，录出来就缺内容 */
      v.playbackRate = 1;
      v.loop = false;
      v.muted = false;
      if (v.volume < 0.05) v.volume = 1;
      var pr = v.play();
      if (pr && pr.catch) pr.catch(function () { toast('自动播放被拦截，请手动点播放'); });
      try { rec.start(1000); } catch (e) { toast('录制启动失败'); cleanup(); return; }
      mvtStopFn = finish; showStop(true);

      var lastT = -1, stall = 0, pausedFor = 0;
      iv = setInterval(function () {
        if (!mvtRecording) { clearInterval(iv); return; }
        var t = v.currentTime;
        /* 录制时同步跳广告：检测到广告就 seek 过去，被录的流里就不会有广告画面/声音 */
        try { adSkipForRecord(v); } catch (e) {}
        if (dur > 0) {
          toast('合成中 ' + Math.min(100, Math.round(t / dur * 100)) + '%（原速录制，请勿切后台/关页面）');
        } else {
          toast('合成中 ' + Math.floor(t / 60) + '分' + Math.floor(t % 60) + '秒（请勿切后台）');
        }
        if (v.paused && !v.ended) {
          pausedFor++;
          if (pausedFor === 5) toast('视频处于暂停，录制仍在继续 —— 请恢复播放', 5000);
          if (pausedFor >= 120) { toast('暂停过久，已停止录制'); finish(); return; }
        } else { pausedFor = 0; }

        if (Math.abs(t - lastT) < 0.05) {
          stall++;
          if (stall === 30) toast('画面已 30 秒无进展，检查是否卡在缓冲', 5000);
          if (stall >= 90) { toast('长时间无进展，已停止'); finish(); }
        } else { stall = 0; }
        lastT = t;
      }, 1000);

      /* 安全上限：按片长留 40% 余量，绝对不超过 3 小时 */
      var limitMs = dur > 0 ? Math.ceil(dur * 1000 * 1.4) + 120000 : 40 * 60 * 1000;
      limitMs = Math.min(limitMs, 3 * 60 * 60 * 1000);
      hardStop = setTimeout(function () {
        if (mvtRecording) { toast('已到安全上限，停止录制', 4000); finish(); }
      }, limitMs);

      toast(dur > 0 ? '开始合成，需约 ' + Math.ceil(dur / 60) + ' 分钟（原速录制，请勿切后台/关页面）'
                    : '开始合成…（请勿切后台/关页面）', 4000);
    }

    if (v.readyState >= 2) begin();
    else v.addEventListener('canplay', begin, { once: true });
  }
  window.__mvtMerge = mergeRecord;

  function guessName(src, type) {
    try {
      var u = new URL(src, location.href);
      var p = decodeURIComponent(u.pathname).split('/').pop();
      if (p && /\.[a-z0-9]{2,5}$/i.test(p)) return p;
    } catch (e) {}
    return safeName() + '_' + stamp() + '.mp4';
  }

  function saveBlob(blob, name) {
    var a = document.createElement('a');
    a.href = URL.createObjectURL(blob);
    a.download = name;
    document.body.appendChild(a);
    a.click();
    setTimeout(function () { URL.revokeObjectURL(a.href); a.remove(); }, 8000);
    toast('已保存：' + name);
  }

  /* ================= UI 构建 ================= */
  function mBtn(text, hasMenu, cls) {
    var b = document.createElement('button');
    b.className = 'mvt-btn' + (hasMenu ? ' mvt-has-menu' : '') + (cls ? ' ' + cls : '');
    var sp = document.createElement('span');
    sp.className = 'mvt-label';
    sp.textContent = text;
    b.appendChild(sp);
    return b;
  }

  function mItem(text, fn) {
    var b = document.createElement('button');
    b.textContent = text;
    b.addEventListener('click', function (e) { e.stopPropagation(); closeMenus(); fn(); });
    return b;
  }

  function mSep() {
    var d = document.createElement('div');
    d.className = 'mvt-sep';
    return d;
  }

  function closeMenus() {
    bar.querySelectorAll('.mvt-btn.mvt-open').forEach(function (b) { b.classList.remove('mvt-open'); });
  }

  var rateBtn;

  function buildBar() {
    bar = document.createElement('div');
    bar.className = 'mvt-bar';
    bar.setAttribute('data-mvt-ver', '2.0.26');

    var logo = document.createElement('span');
    logo.className = 'mvt-logo';
    logo.textContent = '工具箱';
    bar.appendChild(logo);

    /* 版本角标：页面上看到 v1.5.1 才说明新版真的生效了 */
    var ver = document.createElement('span');
    ver.className = 'mvt-ver';
    ver.textContent = 'v2.0.26';
    ver.title = '脚本版本号';
    bar.appendChild(ver);

    /* --- 倍速 --- */
    rateBtn = mBtn('倍速 1x', true, 'rate-btn');
    var mRate = document.createElement('div');
    mRate.className = 'mvt-menu';
    [0.5, 0.75, 1, 1.25, 1.5, 2, 2.5, 3].forEach(function (r) {
      mRate.appendChild(mItem(r + 'x', function () { setRate(cur, r); }));
    });
    rateBtn.appendChild(mRate);
    bar.appendChild(rateBtn);

    /* --- 画面 --- */
    var picBtn = mBtn('画面', true, 'pic-btn');
    var mPic = document.createElement('div');
    mPic.className = 'mvt-menu';
    mPic.appendChild(mItem('左转 90°', function () { cur.__mvt.rotate -= 90; apply(cur); }));
    mPic.appendChild(mItem('右转 90°', function () { cur.__mvt.rotate += 90; apply(cur); }));
    mPic.appendChild(mItem('水平镜像', function () { cur.__mvt.flipH = !cur.__mvt.flipH; apply(cur); }));
    mPic.appendChild(mItem('垂直镜像', function () { cur.__mvt.flipV = !cur.__mvt.flipV; apply(cur); }));
    mPic.appendChild(mSep());
    mPic.appendChild(mItem('放大 10%', function () { cur.__mvt.zoom = Math.round(cur.__mvt.zoom * 110) / 100; apply(cur); }));
    mPic.appendChild(mItem('缩小 10%', function () { cur.__mvt.zoom = Math.round(cur.__mvt.zoom * 90) / 100; apply(cur); }));
    mPic.appendChild(mSep());
    mPic.appendChild(mItem('上移', function () { cur.__mvt.dy -= 20; apply(cur); }));
    mPic.appendChild(mItem('下移', function () { cur.__mvt.dy += 20; apply(cur); }));
    mPic.appendChild(mItem('左移', function () { cur.__mvt.dx -= 20; apply(cur); }));
    mPic.appendChild(mItem('右移', function () { cur.__mvt.dx += 20; apply(cur); }));
    mPic.appendChild(mSep());
    mPic.appendChild(mItem('重置画面', function () {
      var s = cur.__mvt;
      s.rotate = 0; s.flipH = false; s.flipV = false; s.zoom = 1; s.dx = 0; s.dy = 0;
      apply(cur); toast('画面已重置');
    }));
    picBtn.appendChild(mPic);
    bar.appendChild(picBtn);

    /* --- 滤镜 --- */
    var fltBtn = mBtn('滤镜', true, 'flt-btn');
    var mFlt = document.createElement('div');
    mFlt.className = 'mvt-menu';
    function step(key, delta, name) {
      return function () {
        cur.__mvt[key] = Math.min(300, Math.max(20, cur.__mvt[key] + delta));
        apply(cur); toast(name + '：' + cur.__mvt[key] + '%');
      };
    }
    mFlt.appendChild(mItem('亮度 +10%', step('bright', 10, '亮度')));
    mFlt.appendChild(mItem('亮度 −10%', step('bright', -10, '亮度')));
    mFlt.appendChild(mItem('对比度 +10%', step('contrast', 10, '对比度')));
    mFlt.appendChild(mItem('对比度 −10%', step('contrast', -10, '对比度')));
    mFlt.appendChild(mItem('饱和度 +10%', step('sat', 10, '饱和度')));
    mFlt.appendChild(mItem('饱和度 −10%', step('sat', -10, '饱和度')));
    mFlt.appendChild(mSep());
    mFlt.appendChild(mItem('重置滤镜', function () {
      cur.__mvt.bright = 100; cur.__mvt.contrast = 100; cur.__mvt.sat = 100;
      apply(cur); toast('滤镜已重置');
    }));
    fltBtn.appendChild(mFlt);
    bar.appendChild(fltBtn);

    /* --- 下载（三种模式） --- */
    var dlBtn = mBtn('下载', true, 'dl-btn');
    var mDl = document.createElement('div');
    mDl.className = 'mvt-menu';
    /* 优化：把真正能用的 yt-dlp 路径放到最前并标推荐，B站会出垃圾的①降级标注 */
    mDl.appendChild(mItem('① 本地下载脚本（推荐·yt-dlp）', function () { genDownBat(); }));
    mDl.appendChild(mItem('② 通用下载脚本（粘链接）', function () { genDownBatGeneric(); }));
    mDl.appendChild(mItem('③ 智能下载（部分站点）', function () { downloadVideo(); }));
    mDl.appendChild(mItem('④ 分片合并（仅部分站点）', function () { segDownload(); }));
    mDl.appendChild(mItem('⑤ 边播边录（兜底·自动去广告）', function () { mergeRecord(cur); }));
    mDl.appendChild(mItem('⑥ 片段下载（整段下完再剪）', function () { genSegBat(); }));
    mDl.appendChild(mItem('⑦ 去片头广告（跳过前 N 秒）', function () { genAdBat(); }));
    mDl.appendChild(mSep());
    mDl.appendChild(mItem('分片状态', function () { reportSeg(); }));
    mDl.appendChild(mItem('清空分片缓存', function () {
      CAP.items = []; CAP.bytes = 0; CAP.seq = 0; CAP.overflow = false;
      toast('分片缓存已清空');
    }));
    dlBtn.appendChild(mDl);
    bar.appendChild(dlBtn);

    /* --- 工具 --- */
    var toolBtn = mBtn('工具', true, 'tool-btn');
    var mTool = document.createElement('div');
    mTool.className = 'mvt-menu';
    var adItem = mItem('自动跳广告：' + (AD.on ? '开' : '关'), function () {
      AD.on = !AD.on;
      adSave();
      adItem.textContent = '自动跳广告：' + (AD.on ? '开' : '关');
      if (!AD.on && AD.active) adOff(AD.active);
      toast(AD.on ? '自动跳广告：开（识别到广告会静音+加速跳过）' : '自动跳广告：关', 3000);
    });
    mTool.appendChild(adItem);
    mTool.appendChild(mSep());
    mTool.appendChild(mItem('屏幕截图', function () {
      try {
        var c = document.createElement('canvas');
        c.width = cur.videoWidth; c.height = cur.videoHeight;
        c.getContext('2d').drawImage(cur, 0, 0);
        c.toBlob(function (b) {
          if (!b) { toast('截图失败'); return; }
          var a = document.createElement('a');
          a.href = URL.createObjectURL(b);
          a.download = '截图_' + stamp() + '.png';
          document.body.appendChild(a); a.click(); a.remove();
          toast('截图已保存');
        }, 'image/png');
      } catch (e) {
        toast('截图失败：该视频受跨域保护');
      }
    }));
    mTool.appendChild(mItem('画中画', function () {
      if (document.pictureInPictureElement) {
        document.exitPictureInPicture().catch(function () {});
      } else if (cur.requestPictureInPicture) {
        cur.requestPictureInPicture().catch(function () { toast('当前视频不支持画中画'); });
      } else {
        toast('浏览器不支持画中画');
      }
    }));
    mTool.appendChild(mItem('循环 开/关', function () {
      cur.loop = !cur.loop;
      toast(cur.loop ? '循环播放：开' : '循环播放：关');
    }));
    mTool.appendChild(mSep());
    mTool.appendChild(mItem('全部重置', function () {
      cur.__mvt = newState();
      cur.playbackRate = 1;
      apply(cur);
      toast('已全部重置');
      updateRateBtn();
    }));
    toolBtn.appendChild(mTool);
    bar.appendChild(toolBtn);

    /* --- 停止（仅在下载/录制进行中显示） --- */
    stopBtn = document.createElement('button');
    stopBtn.className = 'mvt-btn mvt-stop';
    stopBtn.textContent = '■ 停止';
    stopBtn.style.display = 'none';
    stopBtn.title = '立即停止当前下载/录制';
    stopBtn.addEventListener('click', function (e) {
      e.stopPropagation();
      if (mvtRecording && mvtStopFn) { mvtStopFn(); }
      if (segRunning) { segAbort = true; toast('已取消分片下载', 3000); }
    });
    bar.appendChild(stopBtn);

    /* 下拉开合 */
    bar.addEventListener('click', function (e) {
      var btn = e.target.closest('.mvt-btn.mvt-has-menu');
      if (!btn) return;
      var was = btn.classList.contains('mvt-open');
      closeMenus();
      if (!was) btn.classList.add('mvt-open');
      e.stopPropagation();
    });
    document.addEventListener('click', closeMenus);

    bar.addEventListener('mouseenter', function () { clearTimeout(hideTimer); bar.classList.add('mvt-on'); });
    bar.addEventListener('mouseleave', slideUpSoon);

    // 确保在 body 根部，避免被父容器 transform/overflow 影响
    if (bar.parentElement !== document.body) {
      document.body.appendChild(bar);
    }
    // 用 !important 强制覆盖页面 CSS（保留 transform 给 CSS 类控制，默认隐藏）
    bar.style.cssText = 'position:fixed!important;top:0!important;left:40px!important;right:auto!important;z-index:2147483000!important;display:flex!important;align-items:center!important;gap:2px!important;background:linear-gradient(90deg,#d91e43,#ff6a3d)!important;border:1px solid rgba(255,255,255,.4)!important;border-top:none!important;border-radius:0 0 8px 8px!important;padding:4px 6px!important;box-shadow:0 4px 16px rgba(0,0,0,.4)!important;font-size:13px!important;user-select:none!important;';
  }

  function setRate(v, r) {
    v.__mvt.rate = r;
    v.playbackRate = r;
    toast('倍速：' + r + 'x');
    updateRateBtn();
  }

  function updateRateBtn() {
    if (!cur || !rateBtn) return;
    var label = rateBtn.querySelector('.mvt-label');
    if (label) label.textContent = '倍速 ' + cur.playbackRate + 'x';
  }

  /* ================= 显隐与定位 ================= */
  function showFor(video) {
    cur = video;
    if (!video.__mvt) { video.__mvt = newState(); }
    updateRateBtn();
  }

  function isMenuOpen() {
    return !!bar.querySelector('.mvt-btn.mvt-open');
  }

  function slideDown() {
    clearTimeout(hideTimer);
    bar.classList.add('mvt-on');
    positionBar();
  }

  function slideUpSoon() {
    if (isMenuOpen()) return;
    clearTimeout(hideTimer);
    hideTimer = setTimeout(function () {
      if (isMenuOpen()) return;
      closeMenus();
      bar.classList.remove('mvt-on');
    }, 450);
  }

  function positionBar() {
    var left;
    if (cur && cur.getBoundingClientRect().width > 0) {
      var r = cur.getBoundingClientRect();
      left = r.right - bar.offsetWidth - 8;
    } else {
      left = 40;
    }
    left = Math.max(8, Math.min(left, window.innerWidth - bar.offsetWidth - 8));
    // 强制定位，只改 left/right，不要动 transform（transform 由 mvt-on 类控制显隐）
    bar.style.left = left + 'px';
    bar.style.right = '';
    // 确保在顶层
    bar.style.zIndex = '2147483000';
  }

  /* ================= 绑定视频 ================= */
  var bound = new WeakSet();

  function bind(video) {
    if (bound.has(video)) return;
    if (!(video instanceof HTMLVideoElement)) return;
    var r = video.getBoundingClientRect();
    if (r.width > 0 && (r.width < 260 || r.height < 140)) return;
    bound.add(video);
    video.addEventListener('mouseenter', function () { showFor(video); });
  }

  function scan() {
    document.querySelectorAll('video').forEach(bind);

    /* 若旧版 1.4.2 也在启用，它会在之后建出第二条工具栏；
       这里把不带 data-mvt-ver 的那条清掉，避免双工具栏/双录制 */
    var bars = document.querySelectorAll('.mvt-bar');
    if (bars.length > 1) {
      for (var i = 0; i < bars.length; i++) {
        if (bars[i] !== bar && !bars[i].hasAttribute('data-mvt-ver')) bars[i].remove();
      }
    }
  }

  /* ================= 鼠标/全屏 ================= */
  var lastHitCheck = 0;
  function onDocMove(e) {
    var now = Date.now();
    if (now - lastHitCheck < 100) return;
    lastHitCheck = now;
    var x = e.clientX, y = e.clientY;

    var br = bar.getBoundingClientRect();
    if (x >= br.left - 4 && x <= br.right + 4 && y <= br.bottom + 8) {
      clearTimeout(hideTimer);
      if (!bar.classList.contains('mvt-on')) slideDown();
      return;
    }
    if (bar.classList.contains('mvt-on')) {
      if (y <= 60) { clearTimeout(hideTimer); return; }
      slideUpSoon();
    }

    var hit = null;
    document.querySelectorAll('video').forEach(function (v) {
      if (hit) return;
      var r = v.getBoundingClientRect();
      if (r.width < 260 || r.height < 140) return;
      if (x >= r.left && x <= r.right && y >= r.top && y <= r.bottom) hit = v;
    });
    if (hit) {
      if (cur !== hit) { showFor(hit); }
      clearTimeout(hideTimer);
      if (!bar.classList.contains('mvt-on')) { slideDown(); }
      positionBar();
    }
  }

  function onFsChange() {
    var fs = document.fullscreenElement || document.webkitFullscreenElement;
    if (fs && bar.parentElement !== fs) {
      fs.appendChild(bar);
    } else if (!fs && bar.parentElement !== document.body) {
      document.body.appendChild(bar);
    }
  }

  /* ================= 播放时自动跳广告（片头/插播） =================
   * 和「⑦ 去片头广告」不是一回事：⑦ 是下载后剪掉片头，这里是在线播放时当场跳过。
   *
   * 判定：只在「视频所在容器」里找广告文案（不扫全页，避免误伤），
   *       命中 关闭此广告 / 跳过广告 / 广告剩余 / 广告时长 之类才算广告。
   *       普通视频页不会命中这些词，所以正片不会被误判。
   *
   * 三重手段，从轻到重：
   *   ① 点真正的跳过按钮（只认「跳过广告 / 跳过此广告 / Skip Ad」这几个词）
   *      —— 故意不点「关闭此广告」：奇艺那句「黄金会员关闭此广告」是 VIP 购买入口，点了会弹充值页
   *   ② 广告片通常很短（duration ≤ 180s）→ 直接跳到末尾，广告立刻结束
   *   ③ 跳不掉也点不掉 → 静音 + 16 倍速冲过去，广告结束自动还原原来的倍速和音量
   *
   * 实测要点：奇艺片头广告的文案是「黄金关此广告」（黄金会员关闭此广告被截断），
   * 所以正则里要同时含「关闭此广告」和「关此广告」。
   */
  var AD_SKIP_BTN = /^(跳过广告|跳过此广告|跳过片头广告|跳过$|稍后跳过|skip\s*ads?|关闭广告|暂不观看)$/i;
  var AD_HINT = /关(闭)?此广告|跳过广告|跳过此广告|跳过$|稍后跳过|广告剩余|广告时长|广告倒计时|正在播放广告|广告中|即将播放|skip\s*ads?|观看完整视频|关闭广告|暂不观看|黄金会员/gi;
  var AD = { on: true, rate0: null, mute0: null, lastJump: '', active: null };

  try { if (localStorage.getItem('mvt:adskip') === '0') AD.on = false; } catch (e) {}
  function adSave() { try { localStorage.setItem('mvt:adskip', AD.on ? '1' : '0'); } catch (e) {} }

  /* 取正在播的那个 video（广告可能是另一个 video 元素，不能只认 cur） */
  function adPickVideo() {
    if (cur && !cur.paused && cur.readyState > 2) return cur;
    var vs = document.querySelectorAll('video');
    for (var i = 0; i < vs.length; i++) {
      if (!vs[i].paused && vs[i].readyState > 2) return vs[i];
    }
    return cur || vs[0] || null;
  }

  /* 视频往上 6 层当作「播放器容器」，广告文案基本都在这里面 */
  function adBox(v) {
    if (!v) return null;
    var p = v;
    for (var i = 0; i < 6 && p.parentElement && p.parentElement !== document.body; i++) p = p.parentElement;
    return p;
  }

  function adLook(v) {
    /* ① 首选：在画面范围内采样，看压在画面上的文字里有没有广告文案。
          elementFromPoint 是 O(1) 且不触发全页布局，可以每个 tick 放心跑；
          而且「文字确实盖在视频画面上」本身就是很强的广告证据。 */
    if (adProbe(v)) return true;
    /* ② 兜底：广告标识可能挂在播放器容器里但不在画面正中，读一次容器文字，1.5s 缓存 */
    if (adBoxText(v)) return true;
    /* ③ 腾讯/QQ 专属增强：广告 overlay 有时在外层容器里但不在 video 的 6 层祖先里，
       所以额外扫一下 body 中所有可见的「广告」字样（限制在视频附近 400px） */
    if (/qq\.com|tencent\.com/i.test(window.location.hostname)) {
      try {
        var rr = v.getBoundingClientRect();
        var els = document.querySelectorAll('[class*="ad"],[class*="Ad"],[class*="adv"],[class*="AD"],.mvt-ad-overlay');
        for (var k = 0; k < els.length; k++) {
          var er = els[k].getBoundingClientRect();
          if (er.width < 20 || er.height < 10) continue;
          if (Math.abs(er.left - rr.left) > 400 && Math.abs(er.top - rr.top) > 400) continue;
          var et = els[k].innerText || '';
          if (et && et.length < 300 && AD_HINT.test(et)) return true;
        }
      } catch (e) {}
    }
    return false;
  }

  /* 采样点按比例撒在画面中下部（跳过广告/广告剩余这类文案基本都在这一带），
     最右下角那两点是照奇艺「黄金关此广告」的实际位置加的 */
  var AD_PTS = [
    [0.50, 0.50],
    [0.12, 0.88], [0.30, 0.90], [0.50, 0.93],
    [0.68, 0.90], [0.85, 0.88], [0.94, 0.92],
    [0.90, 0.10]
  ];

  function adProbe(v) {
    var r;
    try { r = v.getBoundingClientRect(); } catch (e) { return false; }
    if (!r || r.width < 200 || r.height < 120) return false;
    var W = window.innerWidth, H = window.innerHeight;
    for (var i = 0; i < AD_PTS.length; i++) {
      var x = r.left + r.width * AD_PTS[i][0];
      var y = r.top + r.height * AD_PTS[i][1];
      if (x < 0 || y < 0 || x > W - 1 || y > H - 1) continue;
      var el;
      try { el = document.elementFromPoint(x, y); } catch (e) { continue; }
      for (var d = 0; d < 3 && el && el !== document.body; d++) {
        /* 必须严格用 innerText（只含「看得见」的文字）。
           绝不能 `innerText || textContent` 回退：播放器常把「关闭此广告」这类
           DOM 预埋成 display:none，textContent 会把隐藏文字也算进来，
           结果广告早就播完了还一直判成广告（实测踩过）。 */
        var tx = (typeof el.innerText === 'string') ? el.innerText : (el.textContent || '');
        if (tx && tx.length < 300 && AD_HINT.test(tx)) return true;
        el = el.parentElement;
      }
    }
    return false;
  }

  var adBoxCache = { t: 0, v: false };
  function adBoxText(v) {
    var now = Date.now();
    if (now - adBoxCache.t < 1500) return adBoxCache.v;
    adBoxCache.t = now;
    adBoxCache.v = false;
    var box = adBox(v);
    if (box) {
      var t = box.innerText || '';
      if (t && t.length < 6000 && AD_HINT.test(t)) adBoxCache.v = true;
    }
    return adBoxCache.v;
  }

  /* ① 点跳过按钮：只在广告期间、只在容器内、只点短文案叶子节点 */
  function adHit(v) {
    var box = adBox(v);
    if (!box) return false;
    var all = box.querySelectorAll('*');
    if (all.length > 4000) return false;   /* 容器太杂就不动，免得卡 */
    for (var i = 0; i < all.length; i++) {
      var el = all[i];
      if (el.__mvtAdDone) continue;
      if (el.children && el.children.length) continue;
      var tx = (el.textContent || '').trim();
      if (!tx || tx.length > 12) continue;
      if (!AD_SKIP_BTN.test(tx)) continue;
      var r = el.getBoundingClientRect();
      if (r.width < 6 || r.height < 6) continue;
      el.__mvtAdDone = 1;
      try { el.click(); } catch (e) {}
      toast('已点击「' + tx + '」跳过广告', 2400);
      return true;
    }
    /* 腾讯/QQ 专属：有时跳过按钮是 SVG 图标，没有 textContent，得找整个可点击区域 */
    if (/qq\.com|tencent\.com/i.test(window.location.hostname)) {
      var hints = box.querySelectorAll('[class*="skip"],[class*="Skip"],[class*="close"],[class*="Close"],button,a');
      for (var j = 0; j < hints.length; j++) {
        var h = hints[j];
        if (h.__mvtAdDone) continue;
        var ht = (h.innerText || h.value || '').trim();
        if (ht && AD_SKIP_BTN.test(ht)) {
          h.__mvtAdDone = 1;
          try { h.click(); } catch (e) {}
          toast('已点击「' + ht + '」跳过广告', 2400);
          return true;
        }
      }
    }
    return false;
  }

  function adOn(v) {
    if (AD.active === v) {
      /* 播放器会自己把 rate 改回去，每个 tick 补一刀 */
      if (v.playbackRate < 16) { try { v.playbackRate = 16; } catch (e) {} }
      return;
    }
    if (AD.active && AD.active !== v) adOff(AD.active);
    AD.active = v;
    AD.rate0 = v.playbackRate;
    AD.mute0 = v.muted;

    /* ② 广告片很短 → 直接跳尾，一次就行。
       只在「刚开头」时才跳：万一是误判（比如正片本身就是 3 分钟短片），
       也不会把已经看到一半的人直接拽到结尾。 */
    var src = v.currentSrc || v.src || '';
    if (v.duration && v.duration <= 180 && v.currentTime < 5 && AD.lastJump !== src) {
      AD.lastJump = src;
      try { v.currentTime = Math.max(0, v.duration - 0.2); } catch (e) {}
    }
    /* ③ 静音 + 16 倍速 */
    try { v.muted = true; } catch (e) {}
    try { v.playbackRate = 16; } catch (e) {}
    toast('检测到广告，正在跳过…', 2600);
  }

  function adOff(v) {
    if (!v || AD.active !== v) return;
    AD.active = null;
    if (AD.rate0 != null) {
      try { v.playbackRate = AD.rate0; } catch (e) {}
      if (v.__mvt) v.__mvt.rate = AD.rate0;
      updateRateBtn();
    }
    if (AD.mute0 != null) { try { v.muted = AD.mute0; } catch (e) {} }
    AD.rate0 = null; AD.mute0 = null;
    toast('广告已跳过', 2200);
  }

  function adTick() {
    /* 兜一层：定时器里抛异常会每 800ms 刷一次控制台，还拖慢页面 */
    try {
      if (!AD.on) { if (AD.active) adOff(AD.active); return; }
      if (mvtRecording) return;   /* 录制中绝不动倍速，否则录制会错乱（录制时跳广告见 adSkipForRecord） */
      var v = adPickVideo();
      if (!v) return;
      if (adLook(v)) { adHit(v); adOn(v); }
      else { adOff(v); }
    } catch (e) { /* 静默：广告模块绝不能影响主功能 */ }
  }

  /* 录制中跳过广告：被录的是 captureStream 实时画面，所以不能用 16 倍速（只会录成快进残影），
     也不能改倍速。唯一干净的做法是 seek 到广告末尾 —— 被录的流里直接不含广告帧和声音。
     点不到也跳不动时退而求其次：静音，至少别让广告声音进录制（广告结束后恢复）。 */
  function adSkipForRecord(v) {
    if (!AD.on) return false;
    if (!adLook(v)) {
      if (AD.recMuted) { AD.recMuted = false; try { v.muted = false; } catch (e) {} }
      return false;
    }
    var clicked = adHit(v);
    var src = v.currentSrc || v.src || '';
    if (v.duration && v.duration <= 180 && v.currentTime < 5 && AD.lastJump !== src) {
      AD.lastJump = src;
      try { v.currentTime = Math.max(0, v.duration - 0.2); } catch (e) {}
      toast('录制中：已跳过广告', 2600);
      return true;
    }
    if (!v.muted) { AD.recMuted = true; try { v.muted = true; } catch (e) {} }
    return clicked;
  }

  /* ================= 启动 ================= */
  function start() {
    var st = document.createElement('style');
    st.textContent = css;
    (document.head || document.documentElement).appendChild(st);

    toastEl = document.createElement('div');
    toastEl.className = 'mvt-toast';
    toastEl.style.whiteSpace = 'pre-line';
    document.body.appendChild(toastEl);

    buildBar();
    scan();

    var mo = new MutationObserver(scan);
    mo.observe(document.documentElement, { childList: true, subtree: true });
    setInterval(scan, 2000);
    setInterval(adTick, 800);
    setInterval(positionBar, 250);
    window.addEventListener('scroll', positionBar, true);
    window.addEventListener('resize', positionBar);
    document.addEventListener('mousemove', onDocMove, true);
    document.addEventListener('fullscreenchange', onFsChange);
    document.addEventListener('webkitfullscreenchange', onFsChange);
  }

  if (document.body) {
    start();
  } else {
    document.addEventListener('DOMContentLoaded', start);
  }
})();
