// ==UserScript==
// @name         我的视频工具箱 v2
// @namespace    whxclp
// @version      2.0.52
// @description  自研轻量视频增强：自动跳广告（播放时识别片头/插播广告，静音+16倍速+跳尾，工具菜单可关）、倍速调速、画面旋转/镜像/缩放/位移、亮度对比度饱和度滤镜、截图、画中画、循环播放。下载：一个「⬇ 下载」按钮智能判断—— 当前页有视频下视频、只有音乐自动下 MP3（抖音走本机新视野后台直提，其他站生成 yt-dlp 脚本）；工具菜单另有「通用下载脚本（粘链接）」和「音频下载（MP3）」。菜单固定向左展开，绝不超出屏幕右侧。
// @author       whxclp
// @match        *://*/*
// @run-at       document-start
// @grant        none
// @updateURL    https://whxclp.github.io/yinbox0/my-video-toolkit.user.js
// @downloadURL  https://whxclp.github.io/yinbox0/my-video-toolkit.user.js
// ==/UserScript==

(function () {
  'use strict';

  /* v2.0.44：精细 iframe 注入。
     - iframe 里装网络钩子（播放器媒体请求在 CDN iframe 内，如 note 完整音频），
       不建工具栏、不跑轮询（无 PNA 噪音），钩子抓到的直链 postMessage 回传顶层；
       本插件 @match 是全站，B站/腾讯等其它站的 iframe 播放器同样适用。
     - 修复 v2.0.43 回归：iframe 钩子生效后视频页 DY.media 也攒了杂音频，
       点「①视频下载」被误判成音频 —— 现按页面 URL 类型判定（/video/ 一定是视频）。
     v2.0.46：工具栏「完成 文件名」行可点击 —— 点击即打开所在文件夹并选中文件。
     v2.0.47：去掉下载完成自动弹的完成提示与自动打开文件夹（刷新页面不再打扰）；
     需要时手动点击「完成 文件名」打开，打开失败会给出明确提示。
     v2.0.48：轮询只允许顶层窗口运行 —— 修复 iframe（lf-zt.douyin.com 等）里
     每 3 秒 fetch 127.0.0.1 被 Chrome 的 loopback 限制拦截刷屏（ERR_FAILED/CORS）。
     v2.0.49：下载视频命名带标题（综合抖音优化插件优点）—— douyin_<id>_<标题>.mp4，
     不再只有一串数字 ID；配合服务端 H.264 优先 + --fixup force，下载即能播且音画同步。
     v2.0.50：下载按钮合一（借鉴抖音优化下载箭头）—— 一个「⬇ 下载」按钮点击即智能下载：
     当前页有视频下视频、只有音乐（mp3）自动改下音频并提示；「通用下载脚本（粘链接）」
     和「音频下载（MP3）」移入工具菜单备用。
     v2.0.51：修复「完成行点击打不开文件夹/文件」—— 根因是抖音每次刷新/导航自动弹
     「登录后免费畅享高清视频」诱导弹窗，全屏遮罩拦截了完成行的点击。工具箱现在每 3 秒
     自动关闭该弹窗，点击完成行时也会先关弹窗再打开文件夹（服务端 /api/open 已实测正常）。 */
  var IS_TOP = (window.top === window);

  /* ============================================================
   * 抖音数据钩子（保留）：页面内提取视频/音频直链（零 cookie）
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
  var DY = { map: {}, last: null, media: [] };   // aweme_id -> aweme 详情对象；media: 播放器音频直链

  /* 媒体直链判定/记录（通用：mp3/m4a/aac/flac/wav/ogg，不限于抖音）。
     v2.0.28 引入 audio hook 时这两个函数从未定义、钩子一直静默失败，
     v2.0.43 补齐定义。 */
  function dyIsMediaUrl(u) {
    var s = String(u || '');
    if (!/^https?:/i.test(s)) return false;
    return /\.(mp3|m4a|aac|flac|wav|ogg|opus)(\?|$)/i.test(s);
  }

  function dyRecordMedia(u) {
    try {
      var s = String(u || '').split('#')[0];
      if (!s || DY.media.indexOf(s) >= 0) return;
      DY.media.push(s);
      /* iframe 内钩子抓到：同步上报顶层合并（顶层按域名白名单校验来源） */
      if (!IS_TOP) { try { window.top.postMessage({ __mvt: 'media', url: s }, '*'); } catch (e) {} }
    } catch (e) {}
  }

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
    /* note 图文/音乐作品：完整声音在 music.play_url（视频只有试看），一并提取 */
    var musicUrl = '';
    var mu = aweme.music;
    if (mu && mu.play_url && Array.isArray(mu.play_url.url_list) && mu.play_url.url_list.length
        && typeof mu.play_url.url_list[0] === 'string') {
      musicUrl = mu.play_url.url_list[0];
    }
    /* 封面图：视频封面优先，图文作品取第一张图（合成音乐视频用） */
    var coverUrl = '';
    var cv = v && (v.cover || v.origin_cover || v.dynamic_cover);
    if (cv && Array.isArray(cv.url_list) && cv.url_list.length
        && typeof cv.url_list[0] === 'string') {
      coverUrl = cv.url_list[0];
    }
    if (!coverUrl && Array.isArray(aweme.images) && aweme.images.length) {
      var im0 = aweme.images[0];
      if (im0 && Array.isArray(im0.url_list) && im0.url_list.length
          && typeof im0.url_list[0] === 'string') {
        coverUrl = im0.url_list[0];
      }
    }
    if (!cands.length && !musicUrl && !(DY.media && DY.media.length)) return null;
    cands.sort(function (a, b2) { return (b2.br - a.br) || (b2.h - a.h); });
    var best = cands[0] || {};
    return {
      url: best.url || '',   /* v2.0.45: video link only - never silently fall back to audio */
      backUrls: best.back || [],
      id: dyAwemeId(aweme),
      desc: String(aweme.desc || '').slice(0, 80),
      duration: v.duration || 0,
      width: best.w, height: best.h, size: best.size,
      musicUrl: musicUrl,   /* v2.0.44: no DY.media fallback (keeps video pages clean) */
      coverUrl: coverUrl
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
                '.swiper-slide-active xg-player', 'xg-player', '.xg-video-player',
                '.douyin-player-video-container video', '.note-video-container video'];
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
    /* DOM 音频兜底：播放器已加载的 audio 元素（钩子没抓到也能拿直链） */
    try {
      var _as = document.querySelectorAll('audio');
      for (var _ai = 0; _ai < _as.length; _ai++) {
        var _au = String(_as[_ai].currentSrc || _as[_ai].src || '').split('#')[0];
        if (_au && /^https?:/i.test(_au) && /\.(mp3|m4a|aac)(\?|$)/i.test(_au)
            && DY.media.indexOf(_au) < 0) DY.media.push(_au);
      }
    } catch (e) {}
    /* HTML 音频扫描：页面数据里的 ies-music 直链（无需播放即可提取） */
    try {
      var _h = document.documentElement.outerHTML.replace(/\\u0026/g, '&');
      var _hm = _h.match(/https?:\/\/[^"'\s\\]*ies-music\/\d+\.mp3[^"'\s\\]*/g) || [];
      for (var _hi = 0; _hi < _hm.length; _hi++) {
        var _hu = _hm[_hi];
        if (DY.media.indexOf(_hu) < 0) DY.media.push(_hu);
      }
      /* 同一音频的 CDN/query 变体按 music_id 去重，只留第一个 */
      var _seen = {};
      var _dd = [];
      for (var _di = 0; _di < DY.media.length; _di++) {
        var _mu2 = DY.media[_di];
        var _mid = (_mu2.match(/ies-music\/(\d+)/) || [])[1] || _mu2;
        if (!_seen[_mid]) { _seen[_mid] = 1; _dd.push(_mu2); }
      }
      DY.media = _dd;
    } catch (e) {}
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
        /* 音频钩子：播放器请求的完整 MP3 直链（note 作品的声音在这里） */
        if (dyIsMediaUrl(url)) {
          var cc = r.clone();
          if (cc.blob) cc.blob().then(function (b) {
            if (b && b.type && /audio/i.test(b.type)) dyRecordMedia(url);
          }).catch(function () {});
        }
        /* 抖音接口响应：clone 出来读 JSON，不影响页面自己拿到的 response */
        if (dyIsAwemeApi(url)) {
          var dj = r.clone();
          if (dj.json) {
            dj.json().then(dyIngestJson).catch(function () {});
          }
        }
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
        return capFetch(url, p);
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
        this.addEventListener('load', function () {
          try {
            var u = self.__mvtU || '';
            /* 抖音 /aweme/ 接口：解析 JSON 存直链（零 cookie 方案的数据源） */
            if (dyIsAwemeApi(u)) {
              try {
                var dr = self.response;
                if (typeof dr === 'string') dyIngestJson(JSON.parse(dr));
                else if (dr && typeof dr === 'object') dyIngestJson(dr);
                else if (self.responseText) dyIngestJson(JSON.parse(self.responseText));
              } catch (e) {}
              return;
            }
            /* 音频钩子：播放器请求的完整 MP3 直链（note 作品的声音在这里） */
            if (dyIsMediaUrl(u)) {
              try {
                var _xct = (self.getResponseHeader && self.getResponseHeader('content-type')) || '';
                if (/audio/i.test(_xct)) dyRecordMedia(u);
              } catch (e) {}
            }
          } catch (e) {}
        });
        return os.apply(this, arguments);
      };
    }
  }
  hookNetwork();

  /* 顶层：接收 iframe 钩子上报的媒体直链（只信媒体 CDN 域） */
  if (IS_TOP) {
    window.addEventListener('message', function (ev) {
      try {
        var d = ev.data;
        if (!d || d.__mvt !== 'media') return;
        var h = '';
        try { h = new URL(ev.origin).hostname; } catch (e) {}
        if (!/\.douyin\.com$|^douyin\.com$|\.yhgb-tn-static\.com$|\.pstatp\.com$|\.byteimg\.com$|\.ibytedtos\.com$/i.test(h)) return;
        dyRecordMedia(d.url);
      } catch (e) {}
    });
  }

  /* iframe：网络钩子已装好，其余（UI/轮询/下载/播放控制）顶层专属 */
  if (!IS_TOP) return;

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
    '.mvt-logo{color:#fff;font-size:11px;padding:0 4px;cursor:default;letter-spacing:.5px;}',
    '.mvt-ver{color:#ffd166;font-size:10px;padding:0 4px 0 0;cursor:default;letter-spacing:.3px;opacity:.95;}'
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

  /* ================= 生成「自举」下载脚本：首次运行自动把 yt-dlp.exe 与 ffmpeg 下载到
   * %LOCALAPPDATA%\mvt\bin，不依赖本机 Python / WinGet，重装系统后双击即用。
   * bakedUrl 非空 => 把链接烤进脚本；为空 => 运行时粘贴/拖放链接。
   * dyVid 非空（抖音页面内提取到的直链）=> 走零 cookie 直链分支。 */
  function buildYtDlpBat(bakedUrl, isDouyin, dyId, dyVid) {
    /* 防盗链：B站 CDN 直链必须同时带浏览器 UA + B站 Referer（实测缺一即 403） */
    var isCdn = /bilivideo\.com|bilivod\.com|bilicdn/i.test(bakedUrl || '');
    /* 抖音直链分支：从页面提取的 CDN 直链自带签名查询参数，只需抖音页面 Referer */
    /* note 图文/音乐作品：视频只有 5 秒试看，完整声音在 music 直链（MP3）——
       优先 aweme.music，其次播放器音频钩子（DY.media），最后视频直链 */
    var isNote = /\/note\//i.test(bakedUrl || '');
    var _mSrc = (dyVid && dyVid.musicUrl) || (DY.media && DY.media.length ? DY.media[0] : '');
    var coverSrc = (dyVid && dyVid.coverUrl) || '';
    var _directSrc = dyVid && (isNote ? (_mSrc || dyVid.url) : (dyVid.url || _mSrc));
    var direct = _directSrc ? String(_directSrc) : '';
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
    var dyOut = (isNote && _mSrc)
      ? ('douyin_music_' + (dyKey || 'note') + '.%%(ext)s')
      : (dyKey
        ? ('douyin_' + dyKey + '_' + (dyDesc.replace(/[\\/:*?"<>|%&^!]/g, '_').replace(/\s+/g, '').trim().slice(0, 40) || 'video') + '.%%(ext)s')
        : ('douyin_' + (dyDesc.replace(/[\\/:*?"<>|%&^!]/g, '_').trim().slice(0, 60) || 'video') + '.%%(ext)s'));
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
      if (isNote && _mSrc && coverSrc) {
        var _mk2 = (dyKey || 'note');
        var _mp3n = 'douyin_music_' + _mk2 + '.mp3';
        var _mp4n = 'douyin_music_' + _mk2 + '.mp4';
        L.push('echo.');
        L.push('echo  [mvt] Note music: merging cover + mp3 into a music video ...');
        L.push('set "COVER=' + coverSrc + '"');
        L.push('curl.exe -L --ssl-no-revoke -A "%UA%" -o "%OUTDIR%\\__mvt_cover.jpg" "%COVER%" >nul 2>nul');
        L.push('if exist "%OUTDIR%\\__mvt_cover.jpg" (');
        L.push('  "%FFDIR%\\ffmpeg.exe" -y -loop 1 -i "%OUTDIR%\\__mvt_cover.jpg" -i "%OUTDIR%\\' + _mp3n + '" -shortest -c:v libx264 -pix_fmt yuv420p -c:a aac -b:a 128k "%OUTDIR%\\' + _mp4n + '"');
        L.push('  if not errorlevel 1 (');
        L.push('    del /f /q "%OUTDIR%\\' + _mp3n + '" "%OUTDIR%\\__mvt_cover.jpg" >nul 2>nul');
        L.push('    echo  [mvt] Music video created: ' + _mp4n);
        L.push('  ) else (');
        L.push('    echo  [mvt] ffmpeg merge failed, MP3 kept: ' + _mp3n);
        L.push('  )');
        L.push(') else (');
        L.push('  echo  [mvt] Cover download failed, MP3 kept: ' + _mp3n);
        L.push(')');
      }
      if (isNote && DY.media && DY.media.length > 1) {
        var _mn = Math.min(DY.media.length, 6);
        for (var _mi = 1; _mi < _mn; _mi++) {
          L.push('echo.');
          L.push('echo  [mvt] Note audio segment ' + (_mi + 1) + '/' + _mn + ' ...');
          L.push('"%YTDLP%" --no-playlist -f "ba/b" --ffmpeg-location "%FFDIR%" --user-agent "%UA%" --referer "%REFERER%" -o "%OUTDIR%\\douyin_music_' + (_mi + 1) + '.%%(ext)s" -P "%OUTDIR%" --no-mtime "' + DY.media[_mi] + '"');
        }
        L.push('echo.');
        L.push('echo  [mvt] All note audio segments downloaded: douyin_music_1.mp3 ... douyin_music_' + _mn + '.mp3');
        L.push('echo  [mvt] If they are one song split into segments, merge with:');
        L.push('echo  [mvt]   ffmpeg -f concat -safe 0 -i list.txt -c copy merged.mp3');
      }
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
    L.push('echo.');
    L.push('echo  [mvt] Opening output folder ...');
    L.push('start "" explorer "%OUTDIR%"');
    L.push('pause');
    L.push('rem Self-delete this bat after the window is closed.');
    L.push('(goto) 2>nul & del "%~f0"');
    return L.join('\r\n') + '\r\n';
  }


  /* ================= 下载模式四：生成本地下载脚本（yt-dlp，最稳） =================
   * 把「当前视频 URL」烤进一个自举 .bat：双击即用，首次运行自动补齐 yt-dlp/ffmpeg，
   * 不依赖本机 Python / WinGet，重装系统后也能用。等价桌面那个 视频下载合并.bat。 */
  /* v2.0.34 抖音后台下载：直链提交给新视野本地服务（127.0.0.1:18322），不生成 bat。
     v2.0.42 新增 audio 参数：true = 仅音频（服务端 yt-dlp 转 MP3） */
  function mvtServerSubmit(url, title, referer, out, audio) {
    return fetch('http://127.0.0.1:18322/api/download', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json', 'X-XinVision-Token': 'xinvision-2026' },
      body: JSON.stringify({ url: url, title: title, referer: referer, out_template: out, audio: !!audio })
    }).then(function (r) { return r.json(); })
      .catch(function () { return { ok: false, error: 'service-unreachable' }; });
  }

  /* audioOnly=true（③ 音频下载）：video 页从视频直链提取音轨转 MP3；
     note 页本来就是音频直链（保持原格式，行为不变） */
  function mvtDouyinBackground(url, dyId, dyVid, audioOnly) {
    var ref = String(location.href || url);
    var desc0 = (dyVid && dyVid.desc) || document.title || 'douyin';
    var id0 = dyId || '';
    /* 自动触发播放：note 完整音频由播放器请求发出，钩子才能抓到（无需用户先手动播放）。
       仅当视频/音频处于暂停状态时才点播放按钮；正在播放时绝不点击，避免误触暂停键导致播放停止。 */
    try {
      var _v = document.querySelector('video,audio');
      if (_v && typeof _v.play === 'function' && _v.paused) { try { _v.play().catch(function () {}); } catch (e0) {} }
      if (_v && _v.paused) {
        var _pb = document.querySelector('[data-e2e="player-play"],.xgplayer-play,.xgplayer-start,.xgplayer-play-btn');
        if (_pb) { try { _pb.click(); } catch (e1) {} }
      }
    } catch (e2) {}
    setTimeout(function () {
      var dv = id0 ? dyGetVideo(id0) : dyGetVideo();
      var desc = (dv && dv.desc) || desc0;
      var subs = [];
      /* v2.0.44: decide by page URL - /video/ is always video; only note pages (or feed
         with no video link) are audio. Fixes v2.0.43 regression where video pages
         downloaded audio because DY.media picked up background/preview audio. */
      var isNote = /\/note\//i.test(ref) || (!/\/video\//i.test(ref) && !(dv && dv.url) && (DY.media && DY.media.length));
      /* v2.0.45: real video direct link only - an audio URL must never satisfy the video branch */
      var vUrl = (dv && dv.url && !/\.(mp3|m4a|aac|flac|wav|ogg|opus)(\?|$)/i.test(String(dv.url))) ? String(dv.url) : '';
      if (isNote) {
        var segs = [];
        if (DY.media && DY.media.length) segs = segs.concat(DY.media);
        if (dv && dv.musicUrl && segs.indexOf(dv.musicUrl) < 0) segs.unshift(dv.musicUrl);
        if (!segs.length) { toast('仍未提取到音频直链：请点一下播放键（等进度条走动）后再点下载', 6000); return; }
        for (var si = 0; si < segs.length; si++) {
          subs.push({ url: segs[si], out: 'douyin_music_' + (segs.length > 1 ? (si + 1) : (id0 || 'note')) + '.%(ext)s' });
        }
      } else if (vUrl) {
        var key = id0 || 'video';
        subs.push({
          url: vUrl,
          out: audioOnly ? ('douyin_music_' + key + '.%(ext)s') : ('douyin_' + key + '.%(ext)s'),
          audio: !!audioOnly
        });
      } else if (audioOnly) {
        /* ③ audio download but no video link: use the audio direct link instead */
        var segsA = [];
        if (DY.media && DY.media.length) segsA = segsA.concat(DY.media);
        if (dv && dv.musicUrl && segsA.indexOf(dv.musicUrl) < 0) segsA.unshift(dv.musicUrl);
        if (!segsA.length) { toast('拿不到音频直链：请点一下播放键（等进度条走动）后再点下载', 6000); return; }
        var keyA = id0 || 'video';
        segsA.forEach(function (su, si) {
          subs.push({ url: su, out: 'douyin_music_' + (segsA.length > 1 ? (si + 1) : keyA) + '.%(ext)s', audio: true });
        });
      } else {
        /* ① video download but no video direct link: tell the user clearly - audio only */
        var segs0 = [];
        if (DY.media && DY.media.length) segs0 = segs0.concat(DY.media);
        if (dv && dv.musicUrl && segs0.indexOf(dv.musicUrl) < 0) segs0.unshift(dv.musicUrl);
        if (segs0.length) {
          toast('⚠ 拿不到视频直链，此页面只能下载音频，已改为音频下载（登录抖音后刷新可下载完整视频）', 6000);
          var key0 = id0 || 'video';
          segs0.forEach(function (su, si) {
            subs.push({ url: su, out: 'douyin_music_' + (segs0.length > 1 ? (si + 1) : key0) + '.%(ext)s', audio: true });
          });
        } else {
          toast('拿不到任何直链（视频/音频都没有）：请刷新页面或重新打开视频后再试', 5000);
          return;
        }
      }
      var done = 0, total = subs.length;
      subs.forEach(function (sb) {
        mvtServerSubmit(sb.url, desc, ref, sb.out, sb.audio).then(function (res) {
          done++;
          if (res && res.ok) toast('后台下载已提交：' + sb.out + '（' + done + '/' + total + '）', 4500);
          else toast('提交失败：' + ((res && res.error) || '新视野服务未启动？') + '：' + sb.out, 5000);
        });
      });
    }, 2500);
  }

  function genDownBat() {
    var url = String(location.href || '').split('#')[0];
    if (!/bilibili\.com/i.test(url) && !/douyin\.com/i.test(url) && cur) {
      var s = cur.currentSrc || cur.src || '';
      if (s && s.indexOf('http') === 0) url = s;
    }
    if (!url) { toast('拿不到当前视频地址', 3000); return; }

    /* 抖音：modal_id 转单视频页；再从页面数据提取直链（零 cookie 首选方案） */
    var isDouyin = /douyin\.com/i.test(location.href) || /douyin\.com/i.test(url);
    var dyId = '', dyVid = null;
    if (isDouyin) {
      var m = url.match(/[?&]modal_id=(\d+)/i);
      if (m) {
        url = 'https://www.douyin.com/video/' + m[1];
        toast('已转为单视频页: ' + url, 3000);
      }
      /* 从 /video/<id> 提取数字 ID，用于固定输出文件名 */
      /* （CDN URL 的查询串曾被 yt-dlp 当标题/ID，400+ 字符导致 Errno 22） */
      var idm = url.match(/\/(?:video|note)\/(\d+)/);
      if (idm) dyId = idm[1];
      /* 页面内提取直链：网络钩子 / _ROUTER_DATA / RENDER_DATA / React fiber。
         详情页按 ID 精确匹配；feed 页（URL 无 /video/）用当前播放的 fiber 数据。 */
      dyVid = dyGetVideo(dyId);
      if (!dyVid && !dyId) {
        toast('抖音链接不是视频页，请打开具体视频后再试', 4000);
        return;
      }
      /* v2.0.34：后台下载（新视野本地服务），不再生成 bat */
      mvtDouyinBackground(url, dyId, dyVid);
      return;
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

  /* ================= 下载模式六：音频下载（MP3） =================
   * 抖音：提取直链提交新视野后台（audio 模式，服务端 yt-dlp 转 MP3）；
   * 其他站：生成「音频下载.bat」（yt-dlp -f ba/b -x --audio-format mp3）。 */
  function genAudioBat() {
    var url = String(location.href || '').split('#')[0];
    var isDouyin = /douyin\.com/i.test(location.href) || /douyin\.com/i.test(url);
    var dyId = '', dyVid = null;
    if (isDouyin) {
      var m = url.match(/[?&]modal_id=(\d+)/i);
      if (m) { url = 'https://www.douyin.com/video/' + m[1]; }
      var idm = url.match(/\/(?:video|note)\/(\d+)/);
      if (idm) dyId = idm[1];
      dyVid = dyGetVideo(dyId);
      if (!dyVid && !dyId) { toast('抖音链接不是视频页，请打开具体视频后再试', 4000); return; }
      /* 音频模式：video 页从视频直链提取音轨转 MP3；note 页本就是音频直链 */
      mvtDouyinBackground(url, dyId, dyVid, true);
      return;
    }
    /* 通用站：生成音频 bat（yt-dlp 转 MP3） */
    var bat = buildAudioBat(url || '');
    saveBlob(new Blob([bat], { type: 'application/octet-stream' }), '音频下载.bat');
    if (navigator.clipboard && navigator.clipboard.writeText) {
      navigator.clipboard.writeText(bat).then(
        function () { toast('已生成「音频下载.bat」并复制：yt-dlp 转 MP3，首次自动拉依赖', 6000); },
        function () { toast('已生成「音频下载.bat」，双击即下载转 MP3', 4000); }
      );
    } else {
      toast('已生成「音频下载.bat」，双击即下载转 MP3', 4000);
    }
  }

  /* 生成「音频下载」自举脚本：yt-dlp 转 MP3（首次自动拉 yt-dlp/ffmpeg）。
   * bakedUrl 非空 => 烤进链接；为空 => 运行时粘贴/拖放。 */
  function buildAudioBat(bakedUrl) {
    var UA = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/138.0.0.0 Safari/537.36';
    var ref = (bakedUrl && /^https?:/i.test(bakedUrl)) ? String(bakedUrl).split('#')[0] : 'https://www.bilibili.com/';
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
    if (bakedUrl) {
      L.push('set "URL=' + bakedUrl + '"');
    } else {
      L.push('set "URL=%~1"');
      L.push('if "%URL%"=="" (');
      L.push('  echo.');
      L.push('  echo  [mvt] Paste video URL to extract audio ^(Bilibili/YouTube/etc via yt-dlp^) then Enter:');
      L.push('  set /p "URL=> "');
      L.push(')');
    }
    L.push('if "%URL%"=="" (');
    L.push('  echo  [mvt] No URL entered.');
    L.push('  pause & exit /b 1');
    L.push(')');
    L.push('');
    L.push('set "UA=' + UA + '"');
    L.push('set "REFERER=' + ref + '"');
    L.push('echo.');
    L.push('echo  [mvt] Extracting audio as MP3 ...');
    L.push('"%YTDLP%" --no-playlist -f "ba/b" -x --audio-format mp3 --audio-quality 0 --ffmpeg-location "%FFDIR%" --user-agent "%UA%" --referer "%REFERER%" --trim-filenames 120 -P "%OUTDIR%" --no-mtime "%URL%"');
    L.push('');
    L.push('echo.');
    L.push('if errorlevel 1 ( echo  [mvt] Download failed, see info above. ) else ( echo  [mvt] Done, MP3 in: %OUTDIR% )');
    L.push('echo.');
    L.push('echo  [mvt] Opening output folder ...');
    L.push('start "" explorer "%OUTDIR%"');
    L.push('pause');
    L.push('rem Self-delete this bat after the window is closed.');
    L.push('(goto) 2>nul & del "%~f0"');
    return L.join('\r\n') + '\r\n';
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

  /* 下载进度：轮询新视野本地服务（127.0.0.1:18322），最新任务状态显示在工具栏 */
  /* v2.0.44: download done -> toast + open output folder (via local XinVision /api/open) */
  var mvtDoneNotified = null;
  function mvtOpenFolder(file) {
    try {
      fetch('http://127.0.0.1:18322/api/open', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json', 'X-XinVision-Token': 'xinvision-2026' },
        body: JSON.stringify({ file: String(file) })
      }).then(function (r) { return r.json(); }).then(function (j) {
        if (!(j && j.ok)) toast('打开文件夹失败：' + ((j && j.error) || '服务返回异常'), 4500);
      }).catch(function () {
        toast('打开文件夹失败：无法连接本地服务（新视野未启动？）', 4500);
      });
    } catch (e) {}
  }

  /* v2.0.51: 自动关闭抖音「登录后免费畅享高清视频」诱导弹窗 —— 其全屏遮罩会拦截完成行点击，
     导致「打不开文件夹和文件」。找到弹窗后点关闭按钮，找不到就移除弹窗容器。 */
  function mvtCloseLoginPop() {
    try {
      var nodes = document.querySelectorAll('div');
      for (var i = 0; i < nodes.length; i++) {
        var el = nodes[i];
        if (!el || el.children.length > 8) continue;
        var t = (el.textContent || '').trim();
        if (t.indexOf('登录后免费畅享') >= 0 && t.indexOf('验证码登录') >= 0 && t.length < 200) {
          var root = el, guard = 0;
          while (root && root.parentElement && guard < 8 && root.parentElement.children.length <= 6) {
            root = root.parentElement; guard++;
          }
          var closeBtn = root.querySelector('[class*="close"], [class*="Close"], svg, [aria-label*="关闭"]');
          if (closeBtn) { closeBtn.click(); return true; }
          root.remove(); return true;
        }
      }
    } catch (e) {}
    return false;
  }

  function mvtPollProgress() {
    if (!window.mvtProg) return;
    fetch('http://127.0.0.1:18322/api/tasks', { headers: { 'X-XinVision-Token': 'xinvision-2026' } })
      .then(function (r) { return r.json(); })
      .then(function (j) {
        if (!j || !j.ok || !j.tasks || !j.tasks.length) return;
        var c0 = j.tasks[0];
        var st = String(c0.state || '');
        var pct = (typeof c0.percent === 'number') ? Math.round(c0.percent) : -1;
        var nm = String(c0.out_template || c0.title || '');
        var txt = st;
        if (st === 'queued') txt = '排队';
        else if (st === 'running') txt = (pct >= 0 ? pct + '%' : '下载中');
        else if (st === 'done') {
          txt = '完成 ' + (c0.file ? String(c0.file).split(/[\\/]/).pop() : nm);
          /* v2.0.46: click the done row to open the containing folder & select the file */
          if (c0.file) {
            window.mvtProg.dataset.file = String(c0.file);
            window.mvtProg.style.cursor = 'pointer';
            window.mvtProg.title = '点击打开所在文件夹：' + String(c0.file).replace(/[\\/][^\\/]*$/, '');
            window.mvtProg.onclick = function () { mvtCloseLoginPop(); mvtOpenFolder(String(c0.file)); };
          }
          /* v2.0.47: no auto completion toast / no auto explorer - manual click only */
        }
        else if (st === 'failed') txt = '失败 ' + String(c0.error || '').slice(0, 24);
        if (window.mvtProg) {
          window.mvtProg.textContent = txt;
          window.mvtProg.style.color = (st === 'failed') ? '#f88' : (st === 'done' ? '#8f8' : '#8df');
          /* v2.0.46: non-done states - clear the click-to-open handler */
          if (st !== 'done') {
            window.mvtProg.onclick = null;
            window.mvtProg.style.cursor = '';
            window.mvtProg.title = '新视野后台下载状态';
            delete window.mvtProg.dataset.file;
          }
        }
      })
      .catch(function () {
        if (window.mvtProg) { window.mvtProg.textContent = '服务未启动'; window.mvtProg.style.color = '#fa0'; }
      });
  }
  if (IS_TOP && !window.__mvtPollStarted) {
    window.__mvtPollStarted = true;
    setInterval(mvtPollProgress, 2000);
    setInterval(mvtCloseLoginPop, 3000);  /* v2.0.51: 自动关登录诱导弹窗 */
  }

  function buildBar() {
    bar = document.createElement('div');
    bar.className = 'mvt-bar';
    bar.setAttribute('data-mvt-ver', '2.0.51');

    var logo = document.createElement('span');
    logo.className = 'mvt-logo';
    logo.textContent = '工具箱';
    bar.appendChild(logo);

    /* 版本角标：页面上看到 v1.5.1 才说明新版真的生效了 */
    var ver = document.createElement('span');
    ver.className = 'mvt-ver';
    ver.textContent = 'v2.0.52';
    ver.title = '脚本版本号';
    bar.appendChild(ver);

    /* 下载进度显示（轮询新视野服务）：数字/状态文字 */
    var prog = document.createElement('span');
    prog.className = 'mvt-prog';
    prog.textContent = '';
    prog.style.cssText = 'margin-left:8px;padding:2px 8px;border-radius:4px;font:12px/1.5 system-ui;'
      + 'background:rgba(255,255,255,.12);color:#8df;white-space:nowrap;max-width:280px;overflow:hidden;text-overflow:ellipsis;';
    prog.title = '新视野后台下载状态';
    bar.appendChild(prog);
    window.mvtProg = prog;

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

    /* --- 下载（智能：一个「下载」按钮，视频/音乐自动判断，借鉴抖音优化的下载箭头） --- */
    var dlBtn = mBtn('⬇ 下载', false, 'dl-btn');
    dlBtn.addEventListener('click', function (e) { e.stopPropagation(); closeMenus(); genDownBat(); });
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
    mTool.appendChild(mItem('通用下载脚本（粘链接）', function () { genDownBatGeneric(); }));
    mTool.appendChild(mItem('音频下载（MP3）', function () { genAudioBat(); }));
    mTool.appendChild(mItem('全部重置', function () {
      cur.__mvt = newState();
      cur.playbackRate = 1;
      apply(cur);
      toast('已全部重置');
      updateRateBtn();
    }));
    toolBtn.appendChild(mTool);
    bar.appendChild(toolBtn);

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
      var v = adPickVideo();
      if (!v) return;
      if (adLook(v)) { adHit(v); adOn(v); }
      else { adOff(v); }
    } catch (e) { /* 静默：广告模块绝不能影响主功能 */ }
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
