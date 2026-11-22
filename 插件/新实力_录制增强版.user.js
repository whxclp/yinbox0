// ==UserScript==
// @name         新实力·录制增强版
// @namespace    local.qnyh.qidian
// @version      1.0.0
// @description  新实力视频下载+录制正式版：①-⑤下载功能原样保留；⑥录制重大升级——标签页录屏、区域框选不压暗、录制条自动吸附播放器控制条、👁隐藏/Alt+H恢复/Alt+R停止、整段总时长倒计时到0自动停、固定存浏览器默认下载目录(桌面)、录完音量恢复原样。下载侧：新页面只先分类不动作等用户选择；换页/换集清空旧页捕获保障内容纯正；开开关才抓；必须真实听完到片尾才允许合并；抖音页只亮③直链解析其余全灰，分段嗅探/缓存/面板重计算全部豁免。
// @license      GPL-3.0-only
// 有意省略说明（非漏写，勿补）：@match/@include 省略＝全站注入，本脚本靠内部 HOST 判断在爱奇艺/腾讯/抖音等多站亮功能，写了会锁死站点；@run-at 省略＝内部已用 DOMContentLoaded+readyState 自己处理注入时机，start/end 都兼容；@connect 省略＝视频直链来自海量 CDN 节点无法枚举，不写 GM_xmlhttpRequest 才能访问任意 CDN，写了 CDN 一换下载即废。通用脚本检查器报"缺这四项"属误报。
// 本地加固版口径：不设 @updateURL / @downloadURL，版本更新一律以手动粘贴到暴力猴编辑器为准，避免旧更新源回滚
// @grant        GM_xmlhttpRequest
// @grant        GM_download
// @grant        GM_getValue
// @grant        GM_setValue
// @grant        GM_info
// @grant        unsafeWindow
// ==/UserScript==

(function () {
  "use strict";

  const BRAND = "新实力";

  // ===== GM 适配（缺一个就退化成原生能力，不让脚本崩） =====
  const _unsafe = (typeof unsafeWindow !== "undefined" ? unsafeWindow : window);
  const _GMxhr = (typeof GM_xmlhttpRequest === "function" ? GM_xmlhttpRequest : null);
  const _GM_download = (typeof GM_download === "function" ? GM_download : null);
  const _GMinfo = (typeof GM_info !== "undefined" ? GM_info : null);
  const VERSION = (_GMinfo && _GMinfo.script && _GMinfo.script.version) || "1.0.0";

  // 页面加载第一时间：下载开关默认关，清掉旧版持久化状态
  try { localStorage.setItem("qidian_auto", "0"); } catch (e) {}

  const HOST = location.hostname;
  const isQy = /(^|\.)iqiyi\.com$/i.test(HOST);
  const isTencent = /(^|\.)qq\.com$/i.test(HOST) || /tencentvideo/i.test(HOST);

  // ===== 内存状态（刷新后全部重建，不跨页面继承） =====
  const state = {
    videoUrlMap: new Map(),   // url -> 记录 {url, mediaType, type, source, rangeStart, rangeEnd, qyTvid, title, ts, savedAt, plSeq, capSeq}
    segBytesCache: new Map(), // segKey -> Uint8Array（已成功且校验通过的分段字节）
    segBytesCacheBytes: 0,
    segPreCount: 0,
    segPreFail: {},
    segInc: null,             // 增量合并缓冲 {sig, entries, keys}
    pageSig: "",
    __endedAt: 0,
    __endedSig: "",
    __playCov: { sig: "", iv: [], last: 0 },
    pausedKeys: {},
    __lockSnap: null,
    segDownloading: false,
    merging: false,
    navBlock: false,
    segAutoLast: 0,
    capSeq: 0,
    // 分组固化归档（用户敲定的分组合并体系）：每 10 段一组，组满自动归档防签名过期/内存淘汰；
    // 组可单独下载（精彩片段）；换页清空
    groupBytes: new Map(),   // segKey → bytes
    groups: [],              // [{ keys:[{k, mediaType}], n:段数, posMin, posMax }]
    groupArchived: 0,
    groupAutoLast: 0,
    groupInit: { video: null, audio: null },  // fMP4 init 段字节（按轨，组间共享）
    groupFiles: [],          // 本会话已落盘的分组 mp4 文件名（完整版合并成功后提示用户可删除）
    // 钩子是否已装（防止重复包装 fetch/XHR/MSE）
    fetchHooked: false,
    xhrHooked: false,
    mseHooked: false,
    mseTracks: [],          // [{mime, kind, buffers:[Uint8Array], seq}]
    mseSeq: 0,
    // 面板
    panel: null,
    panelBtn: null,
  };

  // 爱奇艺当前集身份（tvid）：页面 URL 自带的优先锁定，外来 tvid 不顶替
  const qyStore = { map: {}, cur: "", curAt: 0, fetching: {} };
  _unsafe.__qidianQy = qyStore;

  const CACHE_MAX = 1536 * 1024 * 1024;
  const MIN_KEEP_RATIO = 0.5;
  const LEDGER_KEY = "qidian_ep_ledger_v1";
  const LEDGER_TTL = 30 * 864e5;

  // ===== 下载台账：同一集重复下载前先问一次（本地 30 天、最多 30 条） =====
  function ledgerAll() {
    try { const arr = JSON.parse(localStorage.getItem(LEDGER_KEY) || "[]"); return Array.isArray(arr) ? arr : []; }
    catch (e) { return []; }
  }
  function ledgerHit(epKey, fp) {
    try { return ledgerAll().find((x) => x && x.k === epKey && x.f === fp) || null; }
    catch (e) { return null; }
  }
  function ledgerPut(epKey, fp, name, n) {
    try {
      let list = ledgerAll().filter((x) => x && Date.now() - (x.t || 0) < LEDGER_TTL && !(x.k === epKey && x.f === fp));
      list.push({ k: epKey, f: fp, n, name: String(name || "").slice(0, 40), t: Date.now() });
      if (list.length > 30) list = list.slice(-30);
      localStorage.setItem(LEDGER_KEY, JSON.stringify(list));
    } catch (e) {}
  }
  // 版本台账：记录上次运行版本，跨版本首次加载可提示；不做自动更新覆盖（本地加固版口径）
  const VER_KEY = "qidian_last_version";
  function versionBoot() {
    try {
      const last = localStorage.getItem(VER_KEY) || "";
      localStorage.setItem(VER_KEY, VERSION);
      if (last && last !== VERSION) log.info("版本 " + last + " → " + VERSION);
    } catch (e) {}
  }

  // ===== 小工具 =====
  const log = {
    info: (...a) => console.log("[新实力]", ...a),
    warn: (...a) => console.warn("[新实力]", ...a),
    error: (...a) => console.error("[新实力]", ...a),
  };
  const escapeHtml = (v) => String(v ?? "")
    .replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;")
    .replace(/"/g, "&quot;").replace(/'/g, "&#039;");
  const fmtTime = (s) => {
    s = Math.max(0, Math.round(s || 0));
    return Math.floor(s / 60) + ":" + String(s % 60).padStart(2, "0");
  };
  const fmtBytes = (n) => {
    if (!n || n < 0) return "未知大小";
    if (n < 1024) return n + " B";
    if (n < 1024 * 1024) return (n / 1024).toFixed(1) + " KB";
    return (n / 1024 / 1024).toFixed(2) + " MB";
  };
  const clamp = (v, a, b) => Math.max(a, Math.min(b, v));

  // ===== 身份识别 =====
  // 页面/内容标识：路径 + 稳定 id 参数；爱奇艺并入接口抓到的 tvid，识别同路径内部切集
  function pageSig() {
    try {
      const u = new URL(location.href);
      const IDP = /^(modal_id|aweme_id|item_id|item_ids|vid|bvid|aid|cid|id|mid|pos|p|page|track_id|trackid|song_id|album_id|tvid|tvId)$/i;
      const ids = [];
      u.searchParams.forEach((v, k) => { if (IDP.test(k)) ids.push(k + "=" + v); });
      ids.sort();
      let sig = u.origin + u.pathname + (ids.length ? "?" + ids.join("&") : "");
      if (isQy) {
        const tv = qyStore.cur || pageTvid();
        if (tv) sig += "#tvid=" + tv;
      }
      return sig;
    } catch (e) { return location.origin + location.pathname; }
  }
  // 页面 URL 自带 tvid（正片身份兜底）
  function pageTvid() {
    if (!isQy) return "";
    const m = /[?&]tvid=(\d+)/i.exec(location.href);
    return m ? m[1] : "";
  }
  // 记录一条流属于哪个 tvid；页面正片 tvid 锁定，外来 tvid 只登记不顶替
  function registerQyTvid(tvid) {
    tvid = String(tvid || "").trim();
    if (!/^\d{6,}$/.test(tvid)) return;
    const pageTv = pageTvid();
    if (pageTv) { if (tvid !== pageTv) return; }
    else if (qyStore.cur && qyStore.cur !== tvid) return;
    qyStore.cur = tvid;
    qyStore.curAt = Date.now();
  }

  // 当前视频标题：优先播放器/页面可读标题，兜底 document.title
  function trackTitle() {
    try {
      // 爱奇艺：接口登记的当前 tvid 片名最可靠
      if (isQy && qyStore.cur && qyStore.map[qyStore.cur]) {
        const t = qyStore.map[qyStore.cur].t;
        if (t) return t.slice(0, 120);
      }
      const v = mainVideo();
      if (v && v.title) return String(v.title).slice(0, 120);
      // 常见标题节点
      const sel = ["h1", ".video-title", ".videoName", ".title", "[class*=videoName]"];
      for (const s of sel) {
        const el = document.querySelector(s);
        if (el && el.textContent && el.textContent.trim().length > 1) {
          return el.textContent.trim().slice(0, 120);
        }
      }
    } catch (e) {}
    return String(document.title || "").replace(/\s+/g, " ").trim().slice(0, 120);
  }

  // 挑主 <video>：遍历普通 DOM 与 Shadow DOM，在播 > 大尺寸 > 有进度 优先
  function mainVideo() {
    try {
      const all = [];
      const walk = (root) => {
        root.querySelectorAll("video").forEach((v) => all.push(v));
        root.querySelectorAll("*").forEach((el) => { if (el.shadowRoot) walk(el.shadowRoot); });
      };
      walk(document);
      if (!all.length) return null;
      const score = (v) => {
        let s = 0;
        try { if (!v.paused) s += 100; if (isFinite(v.duration) && v.duration > 1) s += 10; } catch (e) {}
        try { const r = v.getBoundingClientRect(); s += Math.min(50, r.width * r.height / 50000); } catch (e) {}
        return s;
      };
      all.sort((a, b) => score(b) - score(a));
      return all[0] || null;
    } catch (e) { return null; }
  }

  // 真实播放覆盖：只统计连续向前播放的区间，跳进度条（一次 >5 秒）不计入
  function playCoverage() {
    try {
      const v = mainVideo();
      if (!v) return 0;
      const dur = isFinite(v.duration) ? v.duration : 0;
      const cur = isFinite(v.currentTime) ? v.currentTime : 0;
      const sig = pageSig();
      const st = state.__playCov;
      if (st.sig !== sig) { st.sig = sig; st.iv = []; st.last = cur; return 0; }
      const last = typeof st.last === "number" ? st.last : cur;
      if (cur > last && cur - last <= 5) {
        st.iv.push([last, cur]);
        st.iv.sort((a, b) => a[0] - b[0]);
        const merged = [];
        for (const sg of st.iv) {
          const top = merged[merged.length - 1];
          if (top && sg[0] <= top[1] + 1) top[1] = Math.max(top[1], sg[1]);
          else merged.push([sg[0], sg[1]]);
        }
        st.iv = merged;
      }
      st.last = cur;
      let total = 0;
      for (const sg of st.iv) total += Math.max(0, sg[1] - sg[0]);
      return dur > 0 ? Math.min(dur, total) : total;
    } catch (e) { return 0; }
  }

  // 开关：纯观看默认关；开=抓到分段后台固化、抓全后出合并按钮
  function autoOn() {
    try { return localStorage.getItem("qidian_auto") === "1"; } catch (e) { return false; }
  }
  function setAutoOn(on) {
    try { localStorage.setItem("qidian_auto", on ? "1" : "0"); } catch (e) {}
  }

  // ===== 分段判定 / 键 / 校验 / 缓存 =====
  const RE_SEG = /\.(ts|265ts|m4s)(\?|#|$)/i;
  function isSegUrl(u) { return RE_SEG.test(u); }
  // 记录级分段判定（沿用旧双响炮口径 + 显式标记强化）：
  // 1) MSE 喂流分片一律分段；2) 嗅探时按 type/mp2t 打的 seg 显式标记；
  // 3) Range 分段请求（带 rangeStart）必是分段；4) ts/m4s/265ts 后缀兜底。
  // m3u8/mpd 是播放列表地址，归⑤分段体系；无后缀 DASH 分片由 MSE 通道单独收集。
  function isSegRecord(it) {
    if (!it) return false;
    if (it.mseKey || it.seg) return true;
    if (it.rangeStart != null) return true;
    return isSegUrl(it.url);
  }
  // ===== fMP4 init 段字节级识别（合并引擎用：媒体段必须由 init 段的 moov 提供轨道元数据） =====
  function boxTypeAt(u8, off) {
    return (u8 && u8.length > off + 8) ? String.fromCharCode(u8[off + 4], u8[off + 5], u8[off + 6], u8[off + 7]) : "";
  }
  function isInitSegBytes(u8) {
    if (!u8 || u8.length < 16 || boxTypeAt(u8, 0) !== "ftyp") return false;
    for (let o = 8; o < Math.min(u8.length - 8, 128); o++) { if (boxTypeAt(u8, o) === "moov") return true; }
    return false;
  }
  // 从 MSE 轨道字节块（init + 媒体段 混合流）里截取 init 前缀：box 按 size 逐个遍历，遇到第一个 moof 即止——
  // moof 之前的字节（ftyp+moov）就是 init 段。不依赖 URL 特征，爱奇艺等 init 命名不规范的站点通吃。
  function extractInitPrefix(u8) {
    try {
      if (!u8 || u8.length < 16) return null;
      let o = 0;
      let sawMoov = false;
      while (o + 8 <= u8.length) {
        const box = boxTypeAt(u8, o);
        if (box === "moof") return sawMoov ? u8.subarray(0, o) : null;   // 到第一个媒体分片为止
        const size = ((u8[o] << 24) | (u8[o + 1] << 16) | (u8[o + 2] << 8) | u8[o + 3]) >>> 0;
        if (box === "moov") sawMoov = true;
        if (size < 8) return sawMoov ? u8.subarray(0, o) : null;         // 异常 size 兜底
        o += size;
      }
      return sawMoov ? u8.subarray(0, o) : null;   // 整块就是 init（无媒体分片）
    } catch (e) { return null; }
  }
  function concatU8List(arr) {
    const tot = arr.reduce((s, b) => s + b.length, 0);
    const raw = new Uint8Array(tot);
    let o = 0;
    for (const b of arr) { raw.set(b, o); o += b.length; }
    return raw;
  }

  function segKey(rawUrl, item) {    let base;
    try {
      const u = new URL(rawUrl);
      const keep = [];
      const SIG = /^(sign|signature|sig|token|auth|authorization|auth_key|akey|expire|expires|exp|nonce|hdnts|wssecret|wstime|txsecret|txtime|mkey|vkey|deadline)$/i;
      u.searchParams.forEach((v, k) => { if (!SIG.test(k)) keep.push(k + "=" + v); });
      keep.sort();
      base = u.pathname + (keep.length ? "?" + keep.join("&") : "");
    } catch (e) { base = String(rawUrl || "").split("#")[0]; }
    let r = "";
    if (item && item.rangeStart != null) r = item.rangeStart + "-" + (item.rangeEnd != null ? item.rangeEnd : "");
    if (!r) {
      const sm = /[?&]start=(\d+)/.exec(rawUrl || "");
      if (sm) { const em = /[?&]end=(\d+)/.exec(rawUrl || ""); r = sm[1] + "-" + (em ? em[1] : ""); }
    }
    return base + "|" + r;
  }
  // 判断一段字节像不像媒体分片：TS 看 0x47 同步字节，fMP4 看 box 头
  function segBytesValid(u8) {
    if (!u8 || !u8.byteLength || u8.byteLength < 12) return false;
    if (u8[0] === 0x47) return true;
    const box = String.fromCharCode(u8[4], u8[5], u8[6], u8[7]);
    if (/^(ftyp|styp|moof|mdat|free|skip|wide|sidx)$/.test(box)) return true;
    const scanLen = Math.min(u8.byteLength - 188, 188 * 4);
    for (let k = 0; k < scanLen; k++) {
      if (u8[k] === 0x47 && u8[k + 188] === 0x47) return true;
    }
    return false;
  }
  function cacheSeg(key, data) {    if (!key || !data || !data.byteLength) return;
    if (!segBytesValid(data)) return;
    const c = state.segBytesCache;
    if (c.has(key)) return;
    c.set(key, data);
    state.segBytesCacheBytes += data.byteLength;
    while (state.segBytesCacheBytes > CACHE_MAX && c.size > 1) {
      const k0 = c.keys().next().value;
      const v0 = c.get(k0);
      c.delete(k0);
      state.segBytesCacheBytes -= (v0 && v0.byteLength) || 0;
    }
  }
  function clearSegCache() {
    try { state.segBytesCache.clear(); } catch (e) {}
    state.segBytesCacheBytes = 0;
    state.segPreCount = 0;
    state.segPreFail = {};
    state.segInc = null;
    clearMse();
  }
  // MSE 缓冲清空（换集/收尾）
  function clearMse() {
    state.mseTracks.forEach((t) => { t.buffers.length = 0; });
    state.mseTracks.length = 0;
    state.mseSeq = 0;
  }

  // ===== 归属过滤：只保留“当前这一集/这一首”的记录 =====
  function currentFilter() {
    const sig = pageSig();
    const junkRe = /^(当前视频|爱奇艺|在线视频|腾讯视频|优酷|芒果TV|哔哩哔哩|西瓜视频|搜狐视频|乐视|抖音)$/;
    const rawTitle = String(trackTitle() || document.title || "").slice(0, 120);
    const title = rawTitle && !junkRe.test(rawTitle) ? rawTitle : "";
    let curTv = "";
    if (isQy) curTv = qyStore.cur || "";

    return (it) => {
      if (!it) return false;
      // MSE 喂流分片：直接来自当前播放器，归属当前集，不参与 tvid/标题兜底剔除
      if (it.mseKey) return true;
      // 爱奇艺：优先按 tvid 归属；无 tvid 记录时按标题兜底
      if (isQy) {
        if (curTv) {
          if (it.qyTvid) return String(it.qyTvid) === curTv;
          // 无 tvid 的直链/音频：标题能对上才放行
          return !!title && !!it.title && it.title === title;
        }
      }
      // 标题兜底：同路径切歌时，记录标题与当前一致
      if (title && it.title) return it.title === title;
      // 标识兜底：contentKey 以当前 sig 开头
      if (it.contentKey && String(it.contentKey).indexOf(sig) === 0) return true;
      return true; // 身份都取不到时不轻易剔除
    };
  }

  // 当前集抓到的分段（仅显示与合并用）
  function segItems() {
    const f = currentFilter();
    return Array.from(state.videoUrlMap.values()).filter((it) => isSegRecord(it) && f(it));
  }

  // ===== 地址登记 =====
  function addSource(url, info) {
    if (!url) return;
    info = info || {};
    try {
      if (state.videoUrlMap.has(url)) {
        const ex = state.videoUrlMap.get(url);
        for (const k in info) if (info[k] != null || ex[k] == null) ex[k] = info[k];
        return;
      }
      const MAX = 500;
      if (state.videoUrlMap.size >= MAX) {
        const oldest = state.videoUrlMap.keys().next().value;
        state.videoUrlMap.delete(oldest);
      }
      const rec = Object.assign({ url: url }, info);
      if (typeof rec.ts !== "number") rec.ts = Date.now();
      // 播放位置：段被请求时播放器所处的视频内时间（双响炮口径，分组起止时间显示用）
      if (typeof rec.pos !== "number") {
        try { const vv = mainVideo(); rec.pos = (vv && isFinite(vv.currentTime)) ? Math.max(0, vv.currentTime) : -1; }
        catch (e) { rec.pos = -1; }
      }
      // 爱奇艺 tvid 归属
      if (isQy && typeof rec.qyTvid !== "string") {
        const m = /[?&]tvid=(\d+)/i.exec(url);
        if (m) rec.qyTvid = m[1];
        else rec.qyTvid = qyStore.cur ? String(qyStore.cur) : "";
      }
      if (typeof rec.title !== "string") {
        try { rec.title = String(trackTitle() || document.title || "").slice(0, 120); }
        catch (e) { rec.title = String(document.title || "").slice(0, 120); }
      }
      state.videoUrlMap.set(url, rec);
      log.info("捕获:", rec.type || rec.mediaType || "seg", url.slice(-70));
    } catch (e) { log.warn("登记异常:", e && e.message); }
  }

  // ===== 消息提示（不依赖外部库，自造极简浮层） =====
  let msgTimer = null;
  function toast(text, kind) {
    // 录制期间不弹任何浮层提示，否则会被录进画面；只写控制台
    try {
      if (state && state.__recording) { log.info("toast(录制中静默): " + text); return; }
    } catch (e) {}
    try {
      let box = document.getElementById("qidian-toast");
      if (!box) {
        box = document.createElement("div");
        box.id = "qidian-toast";
        box.style.cssText = "position:fixed;left:50%;bottom:120px;transform:translateX(-50%);z-index:2147483647;max-width:80%;padding:8px 14px;border-radius:8px;font-size:13px;color:#fff;background:rgba(20,24,32,.88);box-shadow:0 4px 16px rgba(0,0,0,.3);pointer-events:none;line-height:1.5;";
        document.body.appendChild(box);
      }
      box.textContent = text;
      box.style.background = kind === "error" ? "rgba(180,40,40,.92)" : kind === "warn" ? "rgba(180,120,20,.92)" : "rgba(20,24,32,.88)";
      clearTimeout(msgTimer);
      msgTimer = setTimeout(() => { try { box.remove(); } catch (e) {} }, 4000);
    } catch (e) {}
  }

  // 暴露调试探针（挂到页面 window，控制台可直接读）
  try {
    const __probe = {
      version: VERSION,
      on: () => autoOn(),
      segN: () => segItems().length,
      segAll: () => Array.from(state.videoUrlMap.values()).length,
      status: () => captureStatus(segItems().length),
      sig: () => pageSig(),
      data: state,
    };
    Object.defineProperty(_unsafe, "__qidian", { value: __probe, configurable: true, writable: true });
  } catch (e) {}

  // ===== 抓取挂钩：包装 fetch / XHR，识别分段与直链 =====
  // 按 URL 后缀 + content-type + initiatorType 三重判定（照搬旧脚本口径）
  function sniffUrl(responseUrl, rangeInfo, contentType, initiatorType) {
    try {
      const u = String(responseUrl || "");
      if (!u || u.indexOf("http") !== 0) return;
      const ul = u.toLowerCase();
      let ct = String(contentType || "").toLowerCase();
      // 伪媒体响应直接拦截：页面脚本/接口数据/文档样式（爱奇艺首页的 qysdk.js、data.video JSON 等）不进台账；
      // dash+xml（mpd 播放列表）保留登记，归⑤/DASH 体系判定
      if (/javascript|\/json|text\/html|text\/css|application\/xml|text\/xml/i.test(ct)) return;
      // 排除统计/日志/图片/广告等伪媒体地址（沿用旧双响炮口径）
      if (/ztbox|zpblog|\/log[?/]|\.gif(\?|#|$)/i.test(ul)) return;
      if (/\.qpic\.cn\/|gdtqqvod|gdt\.qq\.com|adsmind/i.test(ul)) return;
      if (initiatorType === "img" || initiatorType === "image") return;

      const videoByType = ct.startsWith("video/") || ct.includes("mpegurl") || ct.includes("dash+xml");
      const audioByType = ct.startsWith("audio/");
      // 腾讯式字节范围分片：URL 同时带 start=数字 和 end=数字 参数——无论后缀/CT 长什么样，强制按分段登记
      const tencRange = /[?&]start=\d+/i.test(u) && /[?&]end=\d+/i.test(u);
      // 是否视频/音频只由 content-type 与 URL 后缀决定；
      // initiatorType 在 fetch/XHR 场景拿不到真实值（曾硬编码 "video" 导致一切请求恒真登记），不再参与判定
      const isVideo =
        videoByType ||
        tencRange ||
        ul.includes(".m3u8") || ul.includes(".mp4") || ul.includes(".webm") ||
        ul.includes(".flv") || ul.includes(".m4v") || ul.includes(".mpd") ||
        ul.includes(".m4s") || ul.includes(".ts?");
      // 音频：ct / DASH 纯音频命名 / URL 含音频后缀
      const isAudio =
        audioByType ||
        /[-_./]audio[-_.\d]/i.test(ul) ||
        ul.includes(".mp3") || ul.includes(".aac") || ul.includes(".ogg") ||
        ul.includes(".oga") || ul.includes(".m4a") || ul.includes(".flac") ||
        ul.includes(".wav") || ul.includes(".opus") || ul.includes(".wma");
      if (!isVideo && !isAudio) return;

      // m4s 分段按 content-type 分流：audio/* 的 m4s 是音频分片（B 站 DASH 音轨不走 MSE，靠网络嗅探捕获），
      // 不分流的话音频会被标成 video，合并时音频轨整个丢失（产物无声只有画面）
      const audio = (isAudio && !isVideo) || (audioByType && isVideo && ul.includes(".m4s"));
      let type = "";
      // fMP4 init 段（ftyp+moov，含轨道元数据）：媒体段（moof 开头）必须依赖它才能解析，
      // 不识别的话 init 会误入①直链列表、合并时缺 init 报 "moof with no moov"
      if (/(^|[\/._-])init([._-](mp4|m4s|ts))?([?#]|$)/i.test(u) && (videoByType || audioByType || /mp4|mp2t/i.test(ul))) type = "fmp4-init";
      else if (/\.m3u8(\?|#|$)/i.test(ul)) type = "m3u8";
      else if (/\.mp4(\?|#|$)/i.test(ul)) type = "mp4";
      else if (/\.webm(\?|#|$)/i.test(ul)) type = "webm";
      else if (/\.flv(\?|#|$)/i.test(ul)) type = "flv";
      else if (/\.m4v(\?|#|$)/i.test(ul)) type = "m4v";
      else if (/\.mpd(\?|#|$)/i.test(ul)) type = "mpd";
      else if (/\.265ts(\?|#|$)/i.test(ul)) type = "265ts";
      else if (/\.ts(\?|#|$)/i.test(ul)) type = "ts";
      else if (/\.m4s(\?|#|$)/i.test(ul)) type = "m4s";
      else if (/\.mp3(\?|#|$)/i.test(ul)) type = "mp3";
      else if (/\.aac(\?|#|$)/i.test(ul)) type = "aac";
      else if (/\.ogg(\?|#|$)/i.test(ul)) type = "ogg";
      else if (/\.m4a(\?|#|$)/i.test(ul)) type = "m4a";
      else if (/\.opus(\?|#|$)/i.test(ul)) type = "opus";
      else if (ct.includes("mpegurl")) type = "m3u8";
      else if (ct.includes("dash+xml")) type = "mpd";
      else if (ct.includes("mp2t")) type = "ts";   // 无后缀的 MPEG-TS 分段也显式识别
      else if (ct.includes("mp4")) type = audio ? "m4a" : "mp4";
      else if (ct.includes("aac")) type = "aac";
      else if (ct.includes("mpeg") || ct.includes("mp3")) type = "mp3";
      else type = audio ? "audio" : "video";

      // 抖音走直链解析路线：分段与播放列表地址不登记，防止台账膨胀、干扰抖音下载；直链/音频照常保留供解析兜底
      if (isDouyin() && (isSegUrl(u) || type === "m3u8" || type === "mpd")) return;

      const range = parseRange(rangeInfo, u);
      // 分段显式打标（ts/265ts/m4s/fmp4-init/腾讯式 start-end 范围）：
      // 直链判定时凭此标记隔离，不再依赖 URL 后缀推断
      const segMark = (type === "ts" || type === "265ts" || type === "m4s" || type === "fmp4-init" || tencRange);
      addSource(u, {
        mediaType: audio ? "audio" : "video",
        type: type,
        source: ct ? "network / " + ct : initiatorType ? "resource / " + initiatorType : "network",
        initiatorType: initiatorType || "",
        rangeStart: range.start, rangeEnd: range.end,
        seg: segMark || undefined,
      });
    } catch (e) {}
  }
  function parseRange(rangeHeader, url) {
    let start = null, end = null;
    try {
      const m = /bytes=(\d*)-(\d*)/.exec(String(rangeHeader || ""));
      if (m) { if (m[1]) start = parseInt(m[1], 10); if (m[2]) end = parseInt(m[2], 10); }
      if (start == null) { const s = /[?&]start=(\d+)/.exec(url || ""); if (s) start = parseInt(s[1], 10); }
      if (end == null) { const e = /[?&]end=(\d+)/.exec(url || ""); if (e) end = parseInt(e[1], 10); }
    } catch (e) {}
    return { start, end };
  }

  function hookFetch() {
    if (state.fetchHooked || typeof _unsafe.fetch !== "function") return;
    state.fetchHooked = true;
    const originFetch = _unsafe.fetch;
    const that = this;
    _unsafe.fetch = function (...args) {
      const request = args[0];
      let requestUrl = "";
      if (typeof request === "string") requestUrl = request;
      else if (request && typeof request.url === "string") requestUrl = request.url;
      let range = "";
      try {
        if (request && request.headers && typeof request.headers.get === "function") range = request.headers.get("range") || "";
        if (!range && args[1] && args[1].headers) {
          const h = args[1].headers;
          range = typeof h.get === "function" ? h.get("range") || "" : (h.range || h.Range || "");
        }
      } catch (e) {}
      const promise = Reflect.apply(originFetch, this, args);
      if (promise && typeof promise.then === "function") {
        promise.then((response) => {
          try {
            const responseUrl = response.url || requestUrl;
            let ctF = "";
            try { ctF = String((response.headers && response.headers.get && response.headers.get("content-type")) || ""); } catch (e) {}
            sniffUrl(responseUrl, range, ctF, "video");
            // 爱奇艺片名：JSON 响应异步解析；抖音 aweme 数据捕获
            if (isQy && !/\.(ts|m4s|mp4|m3u8|mpd|m4a|mp3)(\?|#|$)/i.test(responseUrl)) {
              let ct = "";
              try { ct = String((response.headers && response.headers.get && response.headers.get("content-type")) || ""); } catch (e) {}
              if (/json/i.test(ct)) response.clone().text().then((t) => { captureQyTitle(t); if (isDouyin()) captureDyAweme(t); }).catch(() => {});
            } else if (isDouyin() && /aweme|feed|detail|video/i.test(responseUrl)) {
              response.clone().text().then(captureDyAweme).catch(() => {});
            }
          } catch (e) {}
          return response;
        }).catch(() => {});
      }
      return promise;
    };
  }

  function hookXHR() {
    if (state.xhrHooked || typeof _unsafe.XMLHttpRequest !== "function") return;
    state.xhrHooked = true;
    const XHR = _unsafe.XMLHttpRequest;
    const originOpen = XHR.prototype.open;
    XHR.prototype.open = function (method, url, ...args) {
      this.__sxpo_url = url; this.__sxpo_range = "";
      return Reflect.apply(originOpen, this, [method, url, ...args]);
    };
    const originSetHeader = XHR.prototype.setRequestHeader;
    XHR.prototype.setRequestHeader = function (name, value) {
      try { if (/^range$/i.test(String(name))) this.__sxpo_range = String(value); } catch (e) {}
      return Reflect.apply(originSetHeader, this, [name, value]);
    };
    const originSend = XHR.prototype.send;
    XHR.prototype.send = function (...args) {
      const xhr = this;
      this.addEventListener("load", function () {
        try {
          const responseUrl = xhr.responseURL || xhr.__sxpo_url;
          let range = xhr.__sxpo_range || "";
          if (!range && typeof xhr.getResponseHeader === "function") range = xhr.getResponseHeader("Content-Range") || "";
          let ctX = "";
          try { ctX = typeof xhr.getResponseHeader === "function" ? String(xhr.getResponseHeader("content-type") || "") : ""; } catch (e) {}
          sniffUrl(responseUrl, range, ctX, "video");
          if (isQy && !/\.(ts|m4s|mp4|m3u8|mpd|m4a|mp3)(\?|#|$)/i.test(responseUrl)) {
            let t = "";
            try { t = !xhr.responseType || xhr.responseType === "text" ? xhr.responseText : ""; } catch (e) {}
            if (!t && xhr.response && typeof xhr.response === "object") { try { t = JSON.stringify(xhr.response); } catch (e) {} }
            if (t && /albumName|album_name|videoName|video_name|albumTitle|videoTitle/.test(t)) captureQyTitle(t);
          }
          if (isDouyin() && /aweme|feed|detail|video/i.test(responseUrl)) {
            let t2 = "";
            try { t2 = !xhr.responseType || xhr.responseType === "text" ? xhr.responseText : ""; } catch (e) {}
            if (!t2 && xhr.response && typeof xhr.response === "object") { try { t2 = JSON.stringify(xhr.response); } catch (e) {} }
            if (t2) captureDyAweme(t2);
          }
        } catch (e) {}
      });
      return Reflect.apply(originSend, this, args);
    };
  }

  // ===== MSE 拦截：覆写 addSourceBuffer / appendBuffer，按 mime 分轨收集喂给播放器的分片字节 =====
  // 适用 fetch/XHR 嗅探不到的无后缀 DASH/HLS 分片（浏览器内最后一道防线）。
  function mseKindOf(mime) {
    const m = String(mime || "").toLowerCase();
    if (m.indexOf("audio/") === 0 || /codecs=.*(mp4a|aac|mp3|opus|vorbis|flac)/.test(m)) return "audio";
    return "video";
  }
  function hookMSE() {
    if (state.mseHooked) return;
    const MS = _unsafe.MediaSource;
    if (!MS || typeof MS.prototype !== "object" || typeof MS.prototype.addSourceBuffer !== "function") return;
    state.mseHooked = true;
    const originAdd = MS.prototype.addSourceBuffer;
    MS.prototype.addSourceBuffer = function (mime) {
      const sb = originAdd.call(this, mime);
      const kind = mseKindOf(mime);
      const track = { mime: String(mime || ""), kind, buffers: [], seq: 0 };
      state.mseTracks.push(track);
      const originAppend = sb.appendBuffer;
      sb.appendBuffer = function (buffer) {
        try {
          // 抖音/直播走直链解析路线：MSE 喂流不做捕获缓存，避免分片字节堆积内存、干扰抖音下载
          if (isDouyin()) return originAppend.apply(this, arguments);
          // 未开下载开关：只做探测计数供分类判定（⑤点亮），不取字节、不缓存、不登记——先分类，等待用户选择后再抓
          if (!autoOn()) {
            state.mseProbeCount = (state.mseProbeCount || 0) + 1;
            return originAppend.apply(this, arguments);
          }
          let u8 = null;
          if (buffer instanceof ArrayBuffer) u8 = new Uint8Array(buffer);
          else if (ArrayBuffer.isView(buffer)) u8 = new Uint8Array(buffer.buffer, buffer.byteOffset, buffer.byteLength);
          if (u8 && u8.byteLength) {
            const segNo = ++state.mseSeq;
            track.seq = segNo;
            const copy = new Uint8Array(u8);
            track.buffers.push(copy);
            // init 段提取：MSE 轨道的第一块字节天然以 init（ftyp+moov）开头——按轨存入 groupInit，
            // 供嗅探/归档的纯媒体段（moof）合并时通过 initInput 注入（爱奇艺 init 命名不规范，URL 正则识别不到，字节级提取通吃）
            try {
              if (!state.groupInit[kind]) {
                const init = extractInitPrefix(copy);
                if (init && init.length > 16) {
                  state.groupInit[kind] = new Uint8Array(init);
                  log.info("已从 MSE 首块提取 " + kind + " init 段（" + init.length + " 字节），合并时自动注入");
                }
              }
            } catch (eInit) {}
            // 进字节缓存：稳定键用 MSE 轨道 + 序号；直入台账记录（分段、字节已在手）
            const k = "mse|" + kind + "|" + segNo;
            cacheSeg(k, copy);
            const fakeUrl = "mse://" + kind + "/seg-" + segNo + (track.mime ? "?" + encodeURIComponent(track.mime) : "");
            addSource(fakeUrl, {
              mediaType: kind,
              type: kind === "audio" ? "audio" : "fmp4",
              source: "MSE / " + track.mime,
              mseKey: k,
              mseBytes: copy,
              qyTvid: qyStore.cur ? String(qyStore.cur) : "",
              plSeq: segNo,
              capSeq: segNo,
            });
          }
        } catch (e) { log.warn("MSE 捕获异常:", e && e.message); }
        return originAppend.apply(this, arguments);
      };
      return sb;
    };
    log.info("MSE 拦截已挂载");
  }

  // 爱奇艺片名解析：从 JSON 树里按 tvid 收集标题
  function captureQyTitle(text) {
    if (!text || typeof text !== "string" || text.length > 6000000) return;
    let j;
    try { j = JSON.parse(text); } catch (e) { return; }
    const consider = (tvid, title) => {
      tvid = String(tvid || "").trim();
      title = String(title || "").replace(/\s+/g, " ").trim();
      if (!/^\d{6,}$/.test(tvid)) return;
      if (title.length < 2 || title.length > 100) return;
      if (/^(爱奇艺|在线视频|爱奇艺-在线视频网站.*)$/.test(title)) return;
      const old = qyStore.map[tvid];
      if (old && old.t.length >= title.length) return;
      qyStore.map[tvid] = { t: title.slice(0, 80), at: Date.now() };
    };
    const scan = (o, d) => {
      if (!o || typeof o !== "object" || d > 7) return;
      if (Array.isArray(o)) { o.forEach((x) => scan(x, d + 1)); return; }
      const tvid = o.tvid != null ? o.tvid : (o.tvId != null ? o.tvId : null);
      if (tvid != null) {
        const vn = String(o.vn || o.videoName || o.video_name || o.videoTitle || "").trim();
        const an = String(o.an || o.an || o.albumName || o.album_name || o.albumTitle || "").trim();
        let t = vn || an;
        if (vn && an && !vn.includes(an) && !an.includes(vn)) t = an + " · " + vn;
        if (t) consider(tvid, t);
        else if (o.name || o.title) consider(tvid, o.name || o.title);
      }
      for (const k in o) if (o[k] && typeof o[k] === "object") scan(o[k], d + 1);
    };
    try { scan(j, 0); } catch (e) {}
  }

  // ===== ended / 换源监听：真实听完才标记抓全并锁播放器 =====
  function armVideoEnded() {
    const v = mainVideo();
    if (!v || v.__sxpoEndArmed) return;
    v.__sxpoEndArmed = 1;
    // 下载场景必须自然 ended：循环播放（loop）会吞掉 ended 事件、播完自动重播导致锁定/分组全部落空
    try { if (v.loop) { v.loop = false; log.info("已关闭播放器循环（保证播完停住、合并可触发）"); } } catch (e0) {}
    let lastCur = -1, accumInc = 0;

    const markEnded = (src, force) => {
      try {
        if (state.__endedAt) return;
        // 抖音短视频为整段直链，不走分段抓取/合并，不锁播放器、不拦换页
        if (isDouyin() || isLiveDouyin()) { log.info(src + " 抖音直链页，跳过分段抓全锁定"); return; }
        const dur0 = isFinite(v.duration) ? v.duration : 0;
        const minInc = Math.max(60, dur0 * 0.6);
        // 只认"真正播到底"：必须 currentTime 到达片尾（零差值，仅留浮点最小容差），不提前抢任何一秒；
        // force：loop 回跳兜底（时间已倒退=本轮已播完），跳过 nearEnd 但仍要求真实听满
        const nearEnd = dur0 > 5 && v.currentTime >= dur0 - 0.01;
        if (accumInc < minInc || (!nearEnd && !force)) {
          log.info(src + " 未验证听完（递增 " + Math.round(accumInc) + "s，需 " + Math.round(minInc) + "s），跳过");
          return;
        }
        state.__endedAt = Date.now();
        state.__endedSig = pageSig();
        state.__endedSegCount = 0;
        // ended 后失败分段允许再重试一轮（12 并发+带宽空闲，签名未过期的段能补固化）；持续失败的段视为不可固化
        state.segPreFail = {};
        // 播放完停住（用户敲定）：关循环 + 暂停，防止播放器自动重播/跳下一集清空抓取数据
        try { v.loop = false; v.pause(); } catch (e2) {}
        log.info("已标记抓全 src=" + src);
        lockPlayer();
        navBlockLink();
      } catch (e) {}
    };

    v.addEventListener("ended", () => markEnded("ended", true), true);
    v.addEventListener("timeupdate", () => {
      try {
        if (state.__endedAt) return;
        const dur = isFinite(v.duration) ? v.duration : 0;
        const cur = isFinite(v.currentTime) ? v.currentTime : 0;
        // loop 回跳兜底：上一采样还在片尾附近、这一采样突然倒退 = 播放器自动重播了
        // （ended 被 loop 吞掉的铁证）——真实听满全程即兜底标记抓全，抢在播放器跳转清数据之前
        if (lastCur >= 0 && cur < lastCur - 1 && dur > 5 && lastCur >= dur - 2 && accumInc >= Math.max(60, dur * 0.6)) {
          markEnded("loop-回跳兜底", true);
        }
        if (lastCur >= 0 && cur > lastCur && cur - lastCur < 30) accumInc += (cur - lastCur);
        lastCur = cur;
        // 0.3 秒内进入验证，零差值在 markEnded 内部把关
        if (dur > 5 && cur >= dur - 0.3) markEnded("timeupdate");
      } catch (e) {}
    }, true);
    v.addEventListener("pause", () => {
      try {
        if (state.__endedAt) return;
        const dur = isFinite(v.duration) ? v.duration : 0;
        const cur = isFinite(v.currentTime) ? v.currentTime : 0;
        if (dur > 5 && cur >= dur - 0.3) markEnded("pause");
      } catch (e) {}
    }, true);
    // 换源：重置递增追踪；若锁定后流已变成另一首，强制清旧锁
    v.addEventListener("loadedmetadata", () => {
      try {
        lastCur = -1; accumInc = 0;
        // 已标记抓全：换源（片尾重播/换清晰度/广告插播）一律不再复位——
        // 抓全数据是最终成果，之前换源检测会把它全清（预下归零、分组消失），已按用户实测修正
        if (state.__endedAt) { log.info("换源发生但已抓全，保留抓取/分组数据"); return; }
        if (v.__sxpoLocked && v.__sxpoLockSnap) {
          const snap = v.__sxpoLockSnap;
          const nowTitle = trackTitle();
          const nowSrc = String(v.currentSrc || v.src || "").slice(0, 120);
          const durCh = snap.dur > 5 && isFinite(v.duration) && Math.abs(v.duration - snap.dur) > 5;
          const titleCh = snap.title && nowTitle && snap.title !== nowTitle;
          const srcCh = snap.src && nowSrc && snap.src !== nowSrc;
          if (durCh || titleCh || srcCh) {
            log.warn("换源检测到锁定残留 → 强制解锁");
            unlockPlayer();
            navBlockRelease();
            resetCaptureState();
          }
        }
        const ns = pageSig();
        if (state.__endedSig !== ns) state.__endedSig = "";
      } catch (e) {}
    }, true);
  }

  // 复位抓取相关内存状态（换歌/换集/收尾统一调用）：
  // 分组固化数据一并清理（用户敲定：合并完成后直接清理，不保留，垃圾太多）
  function resetCaptureState() {
    state.__endedAt = 0;
    state.__endedSig = "";
    state.__endedSegCount = 0;
    state.__playCov = { sig: "", iv: [], last: 0 };
    state.pausedKeys = {};
    state.mseProbeCount = 0;
    state.groupBytes = new Map();
    state.groups = [];
    state.groupArchived = 0;
    state.groupInit = { video: null, audio: null };
    state.groupFiles = [];
    state.groupAutoLast = 0;
    delete state.__lockSnap;
    state.segInc = null;
    clearSegCache();
  }

  // ===== 锁定 / 解锁：抓全未合并期间锁住播放器，换流/收尾全量强制复位 =====
  function lockPlayer() {
    try {
      // 抖音/直播为整段直链，不参与分段锁定，直接拒绝
      if (isDouyin() || isLiveDouyin()) { log.info("抖音页跳过锁播放器"); return; }
      const vids = Array.from(document.querySelectorAll("video") || []);
      const v = vids.find((x) => x && !x.paused && isFinite(x.duration)) || vids.find((x) => x && isFinite(x.duration) && x.duration > 0) || vids[0];
      if (!v || v.__sxpoLocked) return;
      v.__sxpoLocked = 1;
      v.__sxpoLockBackup = { loop: v.loop, play: v.play.bind(v) };
      v.__sxpoLockSnap = {
        dur: isFinite(v.duration) ? v.duration : 0,
        title: trackTitle().slice(0, 120),
        src: String(v.currentSrc || v.src || "").slice(0, 120),
      };
      v.loop = false;
      try { v.pause(); } catch (e) {}
      // 劫持 play：锁定期间任何 play() 都不执行
      try {
        v.play = function () { log.warn("🔒 播放器已锁定，忽略 play()"); return Promise.resolve(); };
      } catch (e) {}
      // 劫持 currentTime：禁止拖进度条
      try {
        let _ct = v.currentTime;
        Object.defineProperty(v, "currentTime", {
          configurable: true, get() { return _ct; },
          set(x) { log.warn("🔒 忽略 seek → " + x); },
        });
      } catch (e) {}
      v.__sxpoEndPauser = () => { try { v.pause(); } catch (e) {} };
      v.addEventListener("ended", v.__sxpoEndPauser, true);
      v.__sxpoLockTimer = setInterval(() => { try { if (!v.paused) v.pause(); } catch (e) {} }, 500);
      try { v.muted = true; } catch (e) {}
      log.info("🔒 播放器已锁定（抓全，等合并）");
      toast("🔒 分段已抓全！点「合并已抓分段」开始合并", "warn");
    } catch (e) { log.warn("锁播放器异常:", e && e.message); }
  }

  // 全量强制复位：遍历所有 video，清掉计时器/监听/play 劫持/currentTime 劫持/静音/标记
  function unlockPlayer() {
    try {
      const vids = Array.from(document.querySelectorAll("video") || []);
      vids.forEach((v) => {
        try {
          if (!v) return;
          if (v.__sxpoLockTimer) { clearInterval(v.__sxpoLockTimer); v.__sxpoLockTimer = null; }
          if (v.__sxpoEndPauser) { v.removeEventListener("ended", v.__sxpoEndPauser, true); v.__sxpoEndPauser = null; }
          if (v.__sxpoLockBackup && v.__sxpoLockBackup.play) v.play = v.__sxpoLockBackup.play;
          else if (v.__sxpoLocked) { try { delete v.play; } catch (eP) {} }
          try { v.loop = v.__sxpoLockBackup ? !!v.__sxpoLockBackup.loop : false; } catch (eL) {}
          try { v.muted = false; } catch (eM) {}
          try { delete v.currentTime; } catch (eC) {}
          try { delete v.__sxpoLocked; } catch (eD) {}
          try { delete v.__sxpoLockBackup; } catch (eD2) {}
          try { delete v.__sxpoLockSnap; } catch (eD3) {}
        } catch (eOne) { log.warn("单个 video 解锁残留:", eOne && eOne.message); }
      });
      delete state.__lockSnap;
      state.pausedKeys = {};
      log.info("🔓 播放器已强制复位（" + vids.length + " 个 video）");
    } catch (e) { log.warn("解锁异常:", e && e.message); }
  }

  // 换页拦截：抓全未合并期间防内部自动连播/跳转；解锁时一并撤掉
  function navBlock(on) {
    state.navBlock = !!on;
    navBlockApply();
  }
  function navBlockLink() { if (isDouyin() || isLiveDouyin()) return; if (!state.navBlock) navBlock(true); }
  function navBlockRelease() { if (state.navBlock) navBlock(false); }

  function navBlockApply() {
    const on = state.navBlock;
    if (on) {
      if (!state.__navUnload) {
        state.__navUnload = (e) => {
          const msg = "已开启「换页禁止」：合并还没完成，离开会丢掉已抓取的分段。确定离开吗？";
          e.preventDefault(); e.returnValue = msg; return msg;
        };
        window.addEventListener("beforeunload", state.__navUnload, true);
      }
      if (!state.__navClick) {
        state.__navClick = (e) => {
          const t = e.target;
          if (!t || !t.closest) return;
          const a = t.closest("a[href]");
          if (!a) return;
          if (a.target === "_blank" || a.hasAttribute("download")) return;
          const href = a.getAttribute("href");
          if (!href || href === "#" || href.indexOf("javascript:") === 0) return;
          let u; try { u = new URL(href, location.href); } catch (er) { return; }
          if (u.origin !== location.origin) return;
          if (u.pathname === location.pathname && u.search === location.search) return;
          e.preventDefault(); e.stopPropagation();
          toast("🚫 合并完成前不能换视频/换页", "warn");
        };
        document.addEventListener("click", state.__navClick, true);
      }
      if (!state.__navPatched) {
        state.__navPatched = true;
        state.__navOrigPush = history.pushState;
        state.__navOrigReplace = history.replaceState;
        const blocked = (url) => {
          try {
            const u = new URL(url || location.href, location.href);
            if (u.origin !== location.origin) return false;
            if (u.pathname === location.pathname && u.search === location.search) return false;
            return true;
          } catch (er) { return false; }
        };
        history.pushState = function (...args) { if (blocked(args[2])) { toast("🚫 合并完成前不能换页", "warn"); return; } return state.__navOrigPush.apply(this, args); };
        history.replaceState = function (...args) { if (blocked(args[2])) { toast("🚫 合并完成前不能换页", "warn"); return; } return state.__navOrigReplace.apply(this, args); };
      }
    } else {
      if (state.__navUnload) { window.removeEventListener("beforeunload", state.__navUnload, true); state.__navUnload = null; }
      if (state.__navClick) { document.removeEventListener("click", state.__navClick, true); state.__navClick = null; }
      if (state.__navPatched) {
        if (state.__navOrigPush) history.pushState = state.__navOrigPush;
        if (state.__navOrigReplace) history.replaceState = state.__navOrigReplace;
        state.__navPatched = false; state.__navOrigPush = null; state.__navOrigReplace = null;
      }
    }
  }

  // 巡检：身份变化 → 强制复位旧集锁定/拦截/状态；同一集 → 周期兜底检测锁定后换流
  function startIdentityWatch() {
    const tick = () => {
      try {
        armVideoEnded();
        // 抖音/直播：整段直链，不允许任何分段锁定/拦页残留，每帧兜底复位
        if (isDouyin()) {
          const locked = Array.from(document.querySelectorAll("video") || []).some((v) => v && v.__sxpoLocked);
          if (state.navBlock || locked) { unlockPlayer(); navBlockRelease(); resetCaptureState(); }
          // 防御：抖音为直链路线，无分段概念，残留分段字节缓存直接清掉，不给内存留负担
          if (state.segBytesCacheBytes > 0) clearSegCache();
        }
        const sig = pageSig();
        if (sig === state.pageSig) {
          // 周期兜底：锁定态 video 身份已变 → 清旧锁
          try {
            const v = mainVideo();
            if (v && v.__sxpoLocked && v.__sxpoLockSnap) {
              const snap = v.__sxpoLockSnap;
              const nowTitle = trackTitle();
              const nowSrc = String(v.currentSrc || v.src || "").slice(0, 120);
              const durCh = snap.dur > 5 && isFinite(v.duration) && Math.abs(v.duration - snap.dur) > 5;
              const titleCh = snap.title && nowTitle && snap.title !== nowTitle;
              const srcCh = snap.src && nowSrc && snap.src !== nowSrc;
              if (durCh || titleCh || srcCh) {
                log.warn("巡检发现锁定后换流 → 强制解锁");
                unlockPlayer(); navBlockRelease(); resetCaptureState();
              }
            }
          } catch (eL) {}
          // 同一集：周期跑分段固化/增量缓冲/分组归档（抖音/直播为整段直链，跳过分段链路）
          // 固化轮询 1.5 秒（原 3 秒）：保证预下吞吐大于播放消耗，抓取完成时预下也完成
          // 合并不再自动触发：抓全后面板出现蓝色合并按钮，由用户手动点击（用户敲定的交互）
          // 爱奇艺同样跳过固化链路（用户敲定放弃爱奇艺分段合并：①④等简单方式照常可用）
          if (!isDouyin() && !isQy) {
            const now = Date.now();
            if (now - (state.segAutoLast || 0) > 1500) {
              state.segAutoLast = now;
              const segItemsNow = sortedSegs(segItems());
              preloadGroup(segItemsNow);
              incrementalTick(segItemsNow);
              const stNow = captureStatus(segItemsNow.length, segItemsNow);
              autoGroupArchiveTick(stNow.complete);
            }
          }
          return;
        }
        // 身份变了：强制复位上一集的锁定、拦截、全部旧集状态
        state.pageSig = sig;
        state.segAutoTried = {};
        unlockPlayer();
        navBlockRelease();
        resetCaptureState();
        // 进入新页面/新集：旧页捕获记录全清空，保障下载内容纯正（新页数据由新页播放重新捕获）
        state.videoUrlMap.clear();
        log.info("页面/内容切换:", sig.slice(-70), "→ 旧页捕获记录已清空");
      } catch (e) {}
    };
    tick();
    setInterval(tick, 1000);
  }

  // 清掉不属于当前集的旧地址记录
  function purgeStaleSongs() {
    try {
      const f = currentFilter();
      Array.from(state.videoUrlMap.entries()).forEach(([u, it]) => { if (!f(it)) state.videoUrlMap.delete(u); });
    } catch (e) {}
  }

  // ===== 分段下载：预下固化 / 增量缓冲 / 抓全合并 =====
  // 拉取一段字节（带凭证；GM_XHR 优先，否则页面 fetch）
  function fetchBytes(url, rangeStart, rangeEnd) {
    return new Promise((resolve) => {
      const done = (u8) => resolve(u8 || null);
      try {
        if (_GMxhr) {
          // 带 Referer（双响炮同款口径）：爱奇艺/B站 CDN 校验来源头，缺 Referer 时预下通道全被 403 拒收，
          // 分片字节无法在播放期间固化，合并时旧段签名已过期 → 整次合并失败
          const headers = { Referer: window.location.href };
          if (rangeStart != null) headers["Range"] = "bytes=" + rangeStart + "-" + (rangeEnd != null ? rangeEnd : "");
          _GMxhr({
            method: "GET", url: url, headers: headers,
            responseType: "arraybuffer",
            onload: (r) => {
              try {
                const u8 = new Uint8Array(r.response);
                // 诊断日志：CDN 拒收（403=签名/Referer 问题，416=Range 越界）直接可见
                if (r.status >= 400) log.warn("取段请求 HTTP " + r.status + ":", String(url).slice(-70), "headers:", JSON.stringify(headers));
                done(u8);
              } catch (e) { done(null); }
            },
            onerror: () => { log.warn("取段请求网络错误:", String(url).slice(-70)); done(null); },
            ontimeout: () => { log.warn("取段请求超时:", String(url).slice(-70)); done(null); },
          });
          return;
        }
        const ctrl = new AbortController();
        const to = setTimeout(() => ctrl.abort(), 30000);
        fetch(url, { credentials: "include", signal: ctrl.signal })
          .then((resp) => resp.arrayBuffer())
          .then((ab) => { clearTimeout(to); done(new Uint8Array(ab)); })
          .catch(() => { clearTimeout(to); done(null); });
      } catch (e) { done(null); }
    });
  }

  // 按播放顺序给当前集分段排序：目录分组，组内 Range 偏移 > 文件名尾数字 > 抓取顺序
  // 播放顺序排序（用户实测修正）：优先按段播放位置 pos 升序（段被请求时播放器所处时间，双响炮口径），
  // 无 pos 的按抓取时间 ts——分组切块、归档、合并顺序全部以此为准。
  // 原目录分组 + 文件名数字排序会把 MSE 记录/不同时间抓到的段顺序打乱（组号、起止时间区间错乱的根源）
  function sortedSegs(items) {
    return items.slice().sort((a, b) => {
      const pa = (typeof a.pos === "number" && a.pos >= 0) ? a.pos : null;
      const pb = (typeof b.pos === "number" && b.pos >= 0) ? b.pos : null;
      if (pa != null && pb != null && pa !== pb) return pa - pb;
      if (pa != null) return -1;
      if (pb != null) return 1;
      return (a.ts || 0) - (b.ts || 0);
    });
  }

  // 预下：把当前已抓到、还没固化的分段拉下来缓存（开关开着才跑）
  // 借鉴边播边缓存的预取原理：固化吞吐必须大于播放消耗——轮询 1.5 秒、播放中 6 并发、播完 12 并发，
  // 确保抓取完成时预下也已完成（用户敲定）
  // 失败退避（用户敲定，不再 3 次放弃）：失败后 10 秒内不重试（缓解 CDN 风控/限流），之后持续重试直到固化成功；
  // segPreFail[k] 存的是"最近一次失败的时间戳"
  function preloadGroup(items) {
    if (!autoOn() || state.merging) return;
    const list = items || sortedSegs(segItems());
    let pending = 0;
    const cap = state.__endedAt ? 12 : 6;
    list.forEach((it) => {
      const k = segKey(it.url, it);
      // 已固化的段：字节确实在手（缓存/MSE/分组归档）才跳过；
      // savedAt 还在但字节被复位清掉的场景（换源误清后）→ 重新预下补回
      if (it.mseBytes && it.mseBytes.byteLength) return;
      if (state.groupBytes.has(k)) return;
      if (state.segBytesCache.has(k)) return;
      // 失败退避：失败后 10 秒内不重试
      if (state.segPreFail[k] && Date.now() - state.segPreFail[k] < 10000) return;
      if (pending >= cap) return;
      pending++;
      fetchBytes(it.url, it.rangeStart, it.rangeEnd).then((u8) => {
        if (u8 && u8.byteLength && segBytesValid(u8)) {
          cacheSeg(k, u8);
          it.savedAt = Date.now();
          delete state.segPreFail[k];
          state.segPreCount = (state.segPreCount || 0) + 1;
        } else {
          state.segPreFail[k] = Date.now();
          log.warn("预下失败（10 秒后自动重试）:", String(it.url).slice(-60), u8 ? "内容非媒体" : "请求失败");
        }
      });
    });
  }

  // 增量缓冲：抓全判定前持续把新分段并入内存缓冲，避免签名过期丢段
  function incrementalTick(items) {
    if (!autoOn() || state.merging) return;
    const sig = pageSig();
    const list = items || sortedSegs(segItems());
    if (!list.length) { state.segInc = null; return; }
    const inc = (state.segInc && state.segInc.sig === sig) ? state.segInc : { sig: sig, entries: [], keys: new Set() };
    let added = 0;
    list.forEach((it) => {
      const k = segKey(it.url, it);
      if (inc.keys.has(k)) return;
      const u8 = state.segBytesCache.get(k);
      if (u8 && u8.byteLength) { inc.entries.push({ k, url: it.url, bytes: u8 }); inc.keys.add(k); added++; }
    });
    state.segInc = inc;
    // 缓冲过大（>256MB）时淘汰最旧条目
    let total = 0; inc.entries.forEach((e) => total += e.bytes.byteLength);
    while (total > 256 * 1024 * 1024 && inc.entries.length > 1) {
      const old = inc.entries.shift(); inc.keys.delete(old.k); total -= old.bytes.byteLength;
    }
  }

  // ===== 分组自动固化归档（借鉴双响炮分组 + 用户敲定的组级自动合并） =====
  // 每 10 段一组（用户敲定：预下即真下载——组变小，落盘节奏约 2.5 秒/个，预下的字节尽快变成桌面文件）；
  // 组可单独下载（精彩片段）；换页清空。
  const GROUP_SIZE = 10;

  function archiveGroup(chunk) {
    let moved = 0;
    chunk.forEach(({ it, k }) => {
      const isMse = it.mseBytes && it.mseBytes.byteLength;
      const b = isMse ? it.mseBytes : state.segBytesCache.get(k);
      if (b && b.length) {
        state.groupBytes.set(k, b);
        // init 段全局记录（组间共享：组2+ 的纯媒体段合并时需要 init 注入；按轨存，音频缺失时借视频 init）
        if (isInitSegBytes(b)) state.groupInit[it.mediaType === "audio" ? "audio" : "video"] = b;
        if (!isMse) {
          state.segBytesCache.delete(k);
          state.segBytesCacheBytes = Math.max(0, state.segBytesCacheBytes - b.byteLength);
        }
        moved++;
      }
    });
    // 组起止播放时间：组内各段的 pos（段被请求时播放器所处的视频内时间）取最小/最大，双响炮口径
    const poss = chunk.map((c) => Number(c.it.pos)).filter((p) => isFinite(p) && p >= 0);
    const posMin = poss.length ? Math.min(...poss) : -1;
    const posMax = poss.length ? Math.max(...poss) : -1;
    state.groups.push({ keys: chunk.map((c) => ({ k: c.k, mediaType: c.it.mediaType === "audio" ? "audio" : "video" })).filter((x) => state.groupBytes.has(x.k)), n: moved, posMin: posMin, posMax: posMax });
    state.groupArchived += moved;
    const gi = state.groups.length - 1;
    log.info("分组固化归档：组" + (gi + 1) + "（" + moved + " 段，" + (posMin >= 0 ? fmtPos(posMin) + "–" + fmtPos(posMax) : "时间未知") + "），累计 " + state.groupArchived + " 段");
    return gi;
  }

  function autoGroupArchiveTick(stComplete) {
    if (!autoOn() || state.merging) return;
    try {
      const items = sortedSegs(segItems());
      const cand = [];
      for (const it of items) {
        const k = segKey(it.url, it);
        if (state.groupBytes.has(k)) continue;
        if (!(it.savedAt || (it.mseBytes && it.mseBytes.byteLength))) continue;
        cand.push({ it, k });
      }
      // 满组归档（顺序切块：播放顺序前 30 个未归档固化段为一组）
      // 组固化即自动下载该组 mp4（用户敲定：字节已固化在手，组级合并必成功，无需手动点击）
      while (cand.length >= GROUP_SIZE) {
        const gi = archiveGroup(cand.splice(0, GROUP_SIZE));
        downloadGroup(gi);
      }
      // 尾组归档：真正播完 + 段数稳定 + 预下固化完成（st.complete）后，剩余固化段全部归档并自动下载
      if (stComplete && cand.length) {
        const gi = archiveGroup(cand.splice(0, cand.length));
        downloadGroup(gi);
      }
    } catch (e) { log.warn("分组归档异常:", e && e.message); }
  }

  // 抓全状态判定
  // 合并按钮出现 = 真正播完 + 分段数稳定 + 预下固化 100%（用户敲定：预下完成才合并，点合并必成功）
  function captureStatus(segN, items) {
    const segText = "已抓 " + (segN || 0) + " 段";
    // 抖音短视频为整段直链，无分段抓取概念，不参与抓全判定
    if (isDouyin()) return { complete: false, pct: 0, text: "抖音直链，无需分段抓取" };
    let played = 0, dur = 0, pct = 0;
    try {
      const v = mainVideo();
      if (v) {
        dur = isFinite(v.duration) ? v.duration : 0;
        played = playCoverage();
        pct = dur > 0 ? clamp(Math.round((played / dur) * 100), 0, 100) : 0;
      }
    } catch (e) {}
    // 抓全只认"真正播放结束（ended）"：不按 96% 进度/接近片尾提前判定；
    // 且 ended 后分段数需连续两轮不再增长（播放器拉尾段有滞后）
    try {
      if (state.__endedAt && state.__endedSig === pageSig() && Date.now() - state.__endedAt < 30 * 60 * 1000) {
        const n = segN || 0;
        if (state.__endedSegCount === n && Date.now() - state.__endedAt > 6000) {
          // 预下固化判定：非 MSE 条目全部固化为完成；反复失败 3 次的段视为不可固化放行（合并时网络重拉+MSE 兜底），不死等
          let undone = 0, doneCnt = 0;
          try {
            (items || []).forEach((it) => {
              if (it.savedAt || (it.mseBytes && it.mseBytes.byteLength)) doneCnt++;
              else if (!(state.segPreFail[segKey(it.url, it)] > 0 && Date.now() - state.segPreFail[segKey(it.url, it)] > 15000)) undone++;
            });
          } catch (e2) {}
          if (undone === 0) {
            return { complete: true, pct: 100, text: segText + " · 已播完，预下固化完成（" + doneCnt + " 段）" };
          }
          return { complete: false, pct: pct, text: segText + " · 已播完，预下固化中（剩 " + undone + " 段）…" };
        }
        state.__endedSegCount = n;
        return { complete: false, pct: pct, text: segText + " · 已播完，等待尾部分段抓取完成…" };
      }
    } catch (eEnded) {}
    if (dur > 0) {
      return { complete: false, pct: pct, text: segText + " · 未抓全，需听完再合并，拖进度条无效" };
    }
    return { complete: false, pct: 0, text: segText + " · 读不到播放进度" };
  }

  function preloadText(items) {
    if (!items || !items.length) return "";
    const saved = items.filter((it) => it && it.savedAt).length;
    if (saved >= items.length) return "已预下 " + saved + " 段";
    const rest = items.length - saved;
    const n = clamp(Math.max(0, Math.min(rest, state.segPreCount || 0)), 0, rest);
    return "已预下 " + n + "/" + rest + " 段";
  }
  function durationText() {
    let dur = 0, played = 0;
    try { const v = mainVideo(); if (v) { dur = isFinite(v.duration) ? v.duration : 0; played = playCoverage(); } } catch (e) {}
    if (dur <= 0) return "时长：读不到播放进度";
    const left = Math.max(0, dur - played);
    return "时长 " + fmtTime(dur) + "，已播 " + fmtTime(played) + "，还剩 " + fmtTime(left);
  }

  function isDouyin() { return /douyin|iesdouyin/.test(HOST); }
  function isLiveDouyin() {
    if (!isDouyin()) return false;
    if (/live\.douyin\.com/.test(HOST)) return true;
    return /^\/(follow|root)\/live\//.test(location.pathname) ||
      !!document.querySelector('[data-e2e="feed-live"], [data-e2e="living-container"]');
  }

  // ===== React fiber 通用探测（不依赖外部 utils 库） =====
  const FIBER_KEYS = ["__reactFiber$", "__reactInternalInstance$"];
  const PROPS_KEYS = ["__reactProps$"];
  function reactFiberOf(el) {
    if (!el) return null;
    for (const k of FIBER_KEYS) {
      for (const key in el) {
        if (key.indexOf(k) === 0) return el[key];
      }
    }
    return null;
  }
  function reactPropsOf(el) {
    if (!el) return null;
    for (const k of PROPS_KEYS) {
      for (const key in el) {
        if (key.indexOf(k) === 0) return el[key];
      }
    }
    return null;
  }
  // 沿 fiber 向上找含目标属性的节点（限深 12），callback 返回 { isFind, data }
  function queryFiber(fiber, cb, maxDepth) {
    let node = fiber, depth = 0;
    while (node && depth < (maxDepth || 12)) {
      const r = cb(node);
      if (r && r.isFind) return r.data;
      node = node.return || (node.alternate && node.alternate.return) || null;
      depth++;
    }
    return null;
  }

  // ===== 抖音：解析当前视频的无水印直链 + 音频 =====
  const dyRaw = new Map(); // awemeId -> { at, aw }

  function captureDyAweme(text) {
    if (!text || typeof text !== "string" || text.length > 12000000) return;
    let j;
    try { j = JSON.parse(text); } catch (e) { return; }
    const put = (aw) => {
      if (!aw || typeof aw !== "object") return;
      const id = aw.aweme_id || aw.awemeId;
      if (!id) return;
      dyRaw.set(String(id), { at: Date.now(), aw });
    };
    try {
      put(j.aweme_detail);
      if (Array.isArray(j.aweme_list)) j.aweme_list.forEach(put);
      if (Array.isArray(j.data)) j.data.forEach((it) => { if (it && typeof it === "object") put(it.aweme_info || it.aweme_detail || it.aweme || it); });
      if (Array.isArray(j.cards)) j.cards.forEach((c) => { if (c && typeof c === "object") put(c.aweme_info || c.aweme_detail || c.aweme || c); });
    } catch (e2) {}
    while (dyRaw.size > 30) dyRaw.delete(dyRaw.keys().next().value);
  }

  function dyActiveAweme() {
    try {
      let v = document.querySelector('[data-e2e="feed-active-video"] video') || document.querySelector('[data-e2e="video-detail"] video');
      if (!v) {
        const list = Array.from(document.querySelectorAll("video")).filter((x) => { const r = x.getBoundingClientRect(); return r.width > 120 && r.height > 80; });
        v = list.find((x) => !x.paused) || list[0];
      }
      const fibers = [];
      try {
        const pcs = Array.from(document.querySelectorAll(".basePlayerContainer"));
        const pc = pcs.find((c) => { const x = c.querySelector("video"); return x && !x.paused; }) ||
          pcs.find((c) => { const r = c.getBoundingClientRect(); return r.width > 200 && r.height > 150; }) || pcs[pcs.length - 1];
        fibers.push(reactFiberOf(pc));
      } catch (e2) {}
      fibers.push(reactFiberOf(v));
      for (const f of fibers) {
        if (!f) continue;
        const info = queryFiber(f, (target) => {
          const mp = target && target.memoizedProps;
          if (mp && typeof mp === "object") {
            if (mp.awemeInfo && typeof mp.awemeInfo === "object") return { isFind: true, data: mp.awemeInfo };
            if (mp.originData && typeof mp.originData === "object") return { isFind: true, data: mp.originData };
            return { isFind: false, data: target.return || null };
          }
          return { isFind: false, data: null };
        });
        if (info) return info;
      }
    } catch (e) {}
    return null;
  }

  function dyRawAweme() {
    try {
      if (!dyRaw.size) return null;
      const sp = new URL(location.href).searchParams;
      let id = sp.get("modal_id") || sp.get("aweme_id") || sp.get("vid") || "";
      if (!id) { const m = /\/video\/(\d{8,})/.exec(location.pathname); if (m) id = m[1]; }
      if (id && dyRaw.has(id)) return dyRaw.get(id).aw;
      const dom = dyActiveAweme();
      const want = String((dom && (dom.desc || (dom.music && dom.music.title))) || "").trim();
      if (want) {
        for (const rec of dyRaw.values()) {
          const aw = (rec && rec.aw) || {};
          const t = String(aw.desc || (aw.music && aw.music.title) || "");
          if (t && (t.indexOf(want) >= 0 || want.indexOf(t.slice(0, 20)) >= 0)) return aw;
        }
      }
      if (dyRaw.size === 1) return dyRaw.values().next().value.aw;
    } catch (e) {}
    return null;
  }

  // 清晰度标签：竖屏视频按短边判档（2160×3840 → 4K，与拼音优化界面口径一致）；仅用于列表显示
  function qualityLabel(shortSide) {
    const h = shortSide | 0;
    if (!h) return "";
    if (h >= 2160) return "4K";
    if (h >= 1440) return "2K";
    if (h >= 1080) return "1080P";
    if (h >= 720) return "720P";
    if (h >= 576) return "576P";
    return h + "P";
  }

  function dySources(sig) {
    if (!isDouyin()) return [];
    const domAweme = dyActiveAweme();
    const rawAweme = dyRawAweme();
    const srcList = [];
    if (rawAweme) srcList.push(rawAweme);
    if (domAweme && domAweme !== rawAweme) srcList.push(domAweme);
    if (!srcList.length) return [];

    const pickUrl = (node) => {
      if (!node || typeof node !== "object") return "";
      const list = node.urlList || node.url_list;
      if (Array.isArray(list)) { const hit = list.find((u) => typeof u === "string" && u); if (hit) return hit; }
      if (typeof node.url === "string" && node.url) return node.url;
      return "";
    };
    // 双响炮原版口径：视频地址判定（mp4 / video/tos / aweme/v1/play 接口），剔图片
    const isVideoUrl = (u) => typeof u === "string" && /^https?:/i.test(u) &&
      !/\.(?:webp|jpe?g|png|gif|avif|heic)(?:\?|#|$)/i.test(u) &&
      (/\.mp4(?:\?|#|$)/i.test(u) || /\/video\/tos\//i.test(u) || /\/aweme\/v1\/play\//i.test(u));
    const normBitRate = (it) => {
      if (!it || typeof it !== "object") return null;
      const addr = it.playAddr || it.play_addr || it.playApi || it.play_api || it;
      const url = pickUrl(addr) || pickUrl(it.downloadAddr || it.download_addr);
      if (!url) return null;
      return {
        url,
        size: (addr && (addr.dataSize ?? addr.data_size)) || it.dataSize || it.data_size || 0,
        gear: it.gearName || it.gear_name || "",
        h265: !!(it.isH265 || it.is_h265),
        width: addr && addr.width,
        height: addr && addr.height,
        fps: it.fps ?? it.frame_rate ?? "",
      };
    };
    const cands = [];
    const pushCand = (c) => { if (c && c.url) cands.push(c); };
    srcList.forEach((aw) => {
      try {
        const rawV = (aw && aw.video) || {};
        [Array.isArray(rawV.bitRateList) ? rawV.bitRateList : [], Array.isArray(rawV.bit_rate) ? rawV.bit_rate : []]
          .forEach((list) => list.forEach((it) => pushCand(normBitRate(it))));
        pushCand(normBitRate(rawV.playAddr || rawV.play_addr));
        pushCand(normBitRate(rawV.downloadAddr || rawV.download_addr));
      } catch (e2) {}
    });
    // 兜底深度扫描：仅当 bitRate/play_addr 主路径未取到真实媒体时启用；双响炮口径（mp4 / video/tos / aweme/v1/play）
    try {
      const seenNodes = new WeakSet();
      let budget = 6000;
      const walk = (obj, depth, gearHint, keyName) => {
        if (budget <= 0) return;
        if (typeof obj === "string") {
          if (isVideoUrl(obj) && (/url|src|play|download|addr|api/i.test(String(keyName || "")) || /\/aweme\/v1\/play\//i.test(obj))) {
            pushCand({ url: obj, size: 0, gear: gearHint || "", watermark: /download/i.test(String(keyName || "")) });
          }
          return;
        }
        if (!obj || typeof obj !== "object" || depth > 7 || seenNodes.has(obj)) return;
        seenNodes.add(obj); budget--;
        const gear = obj.gearName || obj.gear_name || gearHint || "";
        const size = obj.dataSize ?? obj.data_size ?? 0;
        const list = obj.urlList || obj.url_list;
        if (Array.isArray(list)) list.forEach((u) => { if (isVideoUrl(u)) pushCand({ url: u, size, gear, h265: /h265|hevc/i.test(String(obj.format || obj.codec || "")), width: obj.width, height: obj.height, fps: obj.fps ?? obj.frame_rate ?? "", watermark: /download/i.test(String(keyName || "")) }); });
        for (const k in obj) { if (k === "urlList" || k === "url_list") continue; walk(obj[k], depth + 1, gear, k); }
      };
      srcList.forEach((aw) => walk(aw, 0, "", ""));
    } catch (e3) {}
    // 一条视频地址都没有时，退回抓包到的视频地址
    if (!cands.length) {
      const f = currentFilter();
      Array.from(state.videoUrlMap.values()).filter(f).forEach((it) => {
        if (!it || it.mediaType !== "video") return;
        if (!/^https?:/i.test(it.url || "")) return;
        if (/\.(ts|265ts|m4s)(\?|#|$)/i.test(it.url)) return;
        pushCand({ url: it.url, size: it.size || 0, gear: "", h265: /h265|265/i.test(it.type || "") });
      });
    }
    const seen = new Set();
    // 双响炮口径基础上按用户要求微调：无水印在前 → H264 整体优先于 H265（第 1 条保证兼容可播）→ 分辨率降序 → 体积降序；
    // aweme/v1/play 接口候选无分辨率信息，自然垫底作兜底
    const videos = cands.filter((c) => {
      const key = c.url.split("?")[0];
      if (seen.has(key)) return false;
      seen.add(key);
      return true;
    }).sort((a, b) => {
      const w = (a.watermark ? 1 : 0) - (b.watermark ? 1 : 0);
      if (w !== 0) return w;
      const h = (a.h265 ? 1 : 0) - (b.h265 ? 1 : 0);
      if (h !== 0) return h;
      const ah = (a.width && a.height) ? Math.min(a.width, a.height) : 0;
      const bh = (b.width && b.height) ? Math.min(b.width, b.height) : 0;
      if (ah !== bh) return bh - ah;
      return (b.size || 0) - (a.size || 0);
    });
    if (!videos.length) return [];
    const primary = srcList[0] || {};
    const musicTitle = (primary.music && typeof primary.music.title === "string" ? primary.music.title : "") || (primary.desc || "") || "douyin";
    const baseName = String(musicTitle).replace(/[\\/:*?"<>|]/g, "_").trim().slice(0, 50) || "douyin";
    const out = [];
    videos.forEach((v) => {
      const res = (v.gear && String(v.gear).replace(/\s+/g, "")) || (v.height ? v.height + "p" : "原画");
      const shortSide = (v.width && v.height) ? Math.min(v.width, v.height) : 0;
      const dims = (v.width && v.height) ? v.width + "×" + v.height : "";
      const fps = v.fps ? Math.round(Number(v.fps) || 0) : 0;
      out.push({
        url: v.url, mediaType: "video", type: "抖音直链" + (v.h265 ? " H265" : ""), source: "抖音解析",
        contentKey: sig, size: v.size || null,
        quality: qualityLabel(shortSide), dims: dims, fps: fps,
        fileName: baseName + "_" + res.replace(/[\\/:*?"<>|]/g, "_") + ".mp4", parsed: true,
      });
    });
    let musicUrl = "";
    const mp = primary.music && (primary.music.playUrl || primary.music.play_url);
    musicUrl = pickUrl(mp) || "";
    if (musicUrl) {
      const ext = (/\.(m4a|mp3|aac)(?:\?|#|$)/i.exec(musicUrl) || [, "m4a"])[1];
      out.push({ url: musicUrl, mediaType: "audio", type: "抖音音频", source: "抖音解析", contentKey: sig, size: null, fileName: baseName + "_音频." + ext, parsed: true });
    }
    return out;
  }

  // ===== 转封装（Mediabunny，库在文件尾部内联） =====
  function MB() { return globalThis.Mediabunny; }

  async function mergeMediaBuffers(videoData, audioData) {
    const m = MB();
    if (!m || typeof m.Input !== "function") throw new Error("合并组件缺失");
    const vInput = new m.Input({ source: new m.BufferSource(videoData), formats: m.ALL_FORMATS });
    const vTrack = await vInput.getPrimaryVideoTrack();
    if (!vTrack) throw new Error("视频数据中未找到视频轨");
    const vDecCfg = await vTrack.getDecoderConfig();
    const aInput = new m.Input({ source: new m.BufferSource(audioData), formats: m.ALL_FORMATS });
    const aTrack = await aInput.getPrimaryAudioTrack();
    if (!aTrack) throw new Error("音频数据中未找到音频轨");
    const aDecCfg = await aTrack.getDecoderConfig();
    const out = new m.Output({ format: new m.Mp4OutputFormat({ fastStart: "in-memory" }), target: new m.BufferTarget() });
    const vSource = new m.EncodedVideoPacketSource(vTrack.codec);
    out.addVideoTrack(vSource);
    const aSource = new m.EncodedAudioPacketSource(aTrack.codec);
    out.addAudioTrack(aSource);
    await out.start();
    let pi = 0;
    for await (const p of new m.EncodedPacketSink(vTrack).packets()) { await vSource.add(p, pi === 0 ? { decoderConfig: vDecCfg } : undefined); pi++; }
    pi = 0;
    for await (const p of new m.EncodedPacketSink(aTrack).packets()) { await aSource.add(p, pi === 0 ? { decoderConfig: aDecCfg } : undefined); pi++; }
    await out.finalize();
    return out.target.buffer;
  }

  // 多个 TS 分段顺序转封装：逐段解复用，时间戳整体平移接上一段结尾
  async function muxTsToMp4(m, segList) {
    const WRAP = 95443.71776;
    let out = null, vSource = null, aSource = null, vDecCfg = null, aDecCfg = null;
    let vNext = 0, aNext = 0, vAdded = 0, aAdded = 0;
    for (let s = 0; s < segList.length; s++) {
      const segData = segList[s];
      if (!segData || !segData.length) continue;
      const tsInput = new m.Input({ source: new m.BufferSource(segData), formats: m.ALL_FORMATS });
      const vTrack = await tsInput.getPrimaryVideoTrack();
      const aTrack = await tsInput.getPrimaryAudioTrack();
      if (!out) {
        if (!vTrack && !aTrack) throw new Error("分段数据中未找到音视频轨");
        vDecCfg = vTrack ? await vTrack.getDecoderConfig() : null;
        aDecCfg = aTrack ? await aTrack.getDecoderConfig() : null;
        out = new m.Output({ format: new m.Mp4OutputFormat({ fastStart: "in-memory" }), target: new m.BufferTarget() });
        if (vTrack) { vSource = new m.EncodedVideoPacketSource(vTrack.codec); out.addVideoTrack(vSource); }
        if (aTrack) { aSource = new m.EncodedAudioPacketSource(aTrack.codec); out.addAudioTrack(aSource); }
        await out.start();
      }
      const pump = async (track, source, isVideo) => {
        if (!track || !source) return;
        const pkts = [];
        for await (const p of new m.EncodedPacketSink(track).packets()) pkts.push(p);
        if (!pkts.length) return;
        const times = new Float64Array(pkts.length);
        let wrapOff = 0, segMax = -Infinity, base = Infinity;
        for (let k = 0; k < pkts.length; k++) {
          let t = pkts[k].timestamp + wrapOff;
          if (t < segMax - WRAP / 2) { wrapOff += WRAP; t = pkts[k].timestamp + wrapOff; }
          if (t > segMax) segMax = t;
          times[k] = t;
          if (t < base) base = t;
        }
        let next = isVideo ? vNext : aNext;
        const shift = next - base;
        for (let k = 0; k < pkts.length; k++) {
          const p = pkts[k];
          p.timestamp = times[k] + shift;
          const added = isVideo ? vAdded++ : aAdded++;
          await source.add(p, added === 0 ? { decoderConfig: isVideo ? vDecCfg : aDecCfg } : undefined);
          const end = p.timestamp + (p.duration || 0);
          if (end > next) next = end;
        }
        if (isVideo) vNext = next; else aNext = next;
      };
      await pump(vTrack, vSource, true);
      await pump(aTrack, aSource, false);
      if (typeof tsInput.dispose === "function") tsInput.dispose();
    }
    if (!out) throw new Error("分段数据中未找到音视频轨");
    if (!vAdded && !aAdded) throw new Error("分段中未解出任何音视频包");
    await out.finalize();
    return out.target.buffer;
  }

  // 多个 fMP4 分段顺序重封装
  async function muxSegmentsToMp4(m, segItems) {
    // v0.8.0 合并引擎重构：按轨处理 fMP4 分段（视频轨 = 视频 init + 视频媒体段；音频轨同理）
    // 纯媒体段（moof 开头）必须由 init 段的 moov 提供轨道元数据——通过 InputOptions.initInput 传入（Mediabunny 原生支持），
    // 解决爱奇艺/B站 "moof with no moov" 报错；双轨（B 站 DASH）各自独立 Input，音频 init 缺失时借视频 init（双轨同 moov 的站点）
    const tracks = { video: { init: [], media: [] }, audio: { init: [], media: [] } };
    (segItems || []).forEach((it) => {
      if (!it || !it.bytes || !it.bytes.length) return;
      const bucket = tracks[it.mediaType === "audio" ? "audio" : "video"];
      (isInitSegBytes(it.bytes) ? bucket.init : bucket.media).push(it.bytes);
    });
    // init 缺失兜底：音频轨借视频轨的 init（爱奇艺单 init 含双轨）；视频轨缺 init 无法兜底（真缺失）
    if (!tracks.video.init.length && tracks.video.media.length) {
      const init = await findMissingInit("video");
      if (init) tracks.video.init.push(init);
    }
    if (!tracks.audio.init.length && tracks.audio.media.length) {
      const init = await findMissingInit("audio") || (tracks.video.init.length ? tracks.video.init[0] : null);
      if (init) tracks.audio.init.push(init);
    }
    if (!tracks.video.init.length && tracks.video.media.length && tracks.audio.init.length) {
      tracks.video.init.push(tracks.audio.init[0]);   // 音频先找到时反向借用
    }

    // init 缺失兜底：嗅探/预下/MSE 都没拿到 init（爱奇艺 init 命名不规范且不走 MSE）时，
    // 扫描台账里的 mp4/mp2t 候选（播放器请求过的独立请求，URL 就在①直链列表里），
    // 逐个拉字节做 ftyp+moov 字节级验证——init 段通常很小，逐个探测开销可控
    const findMissingInit = async (kind) => {
      try {
        if (state.groupInit[kind]) return state.groupInit[kind];
        const cands = Array.from(state.videoUrlMap.values()).filter((it) =>
          it && !it.mseKey && !isSegRecord(it) && !state.groupBytes.has(segKey(it.url, it)) &&
          (String(it.type) === "mp4" || /mp4|mp2t/i.test(String(it.source) || ""))
        );
        log.info("缺失 " + kind + " init，扫描台账候选 " + cands.length + " 个…");
        for (const it of cands) {
          try {
            const u8 = await fetchBytes(it.url, it.rangeStart, it.rangeEnd);
            if (u8 && u8.byteLength > 16 && isInitSegBytes(u8)) {
              state.groupInit[kind] = u8;
              log.info("✓ 已捕获 " + kind + " init 段（" + u8.byteLength + " 字节）:", String(it.url).slice(-60));
              return u8;
            }
          } catch (eF) {}
        }
        log.warn("台账候选中未找到 " + kind + " init 段");
      } catch (e) {}
      return null;
    };

    const buildInput = (kind) => {
      const t = tracks[kind];
      if (!t.media.length) return null;
      const opts = { source: new m.BufferSource(concatU8List(t.media)), formats: m.ALL_FORMATS };
      if (t.init.length) opts.initInput = new m.Input({ source: new m.BufferSource(t.init[0]), formats: m.ALL_FORMATS });
      return new m.Input(opts);
    };
    const vInput = buildInput("video");
    const aInput = buildInput("audio");
    if (!vInput && !aInput) throw new Error("没有可解析的媒体分段（缺 init 或数据异常）");

    const out = new m.Output({ format: new m.Mp4OutputFormat({ fastStart: "in-memory" }), target: new m.BufferTarget() });
    let vSource = null, aSource = null, vDec = null, aDec = null;
    let vTrack = null, aTrack = null;
    if (vInput) {
      vTrack = await vInput.getPrimaryVideoTrack();
      if (vTrack) {
        vDec = await vTrack.getDecoderConfig();
        vSource = new m.EncodedVideoPacketSource(vTrack.codec);
        out.addVideoTrack(vSource);
      }
    }
    if (aInput) {
      aTrack = await aInput.getPrimaryAudioTrack();
      if (aTrack) {
        aDec = await aTrack.getDecoderConfig();
        aSource = new m.EncodedAudioPacketSource(aTrack.codec);
        out.addAudioTrack(aSource);
      }
    }
    if (!vSource && !aSource) throw new Error("分段流中未解析出音视频轨（init 或数据异常）");
    await out.start();
    // 每轨写入三步法（用户实测修正）：收集 → 按 timestamp 排序（MSE append/嗅探抓取的字节顺序可能乱于时间轴，
    // 直接按字节顺序写会触发 muxer 的 GOP 时间戳倒退报错）→ 平移归零后顺序写入
    const pullTrack = async (input, track, src) => {
      const decCfg = await track.getDecoderConfig();
      const pkts = [];
      for await (const pkt of new m.EncodedPacketSink(track).packets()) pkts.push(pkt);
      pkts.sort((x, y) => x.timestamp - y.timestamp);
      const base = pkts.length ? pkts[0].timestamp : 0;
      let pi = 0;
      for (const pkt of pkts) {
        pkt.timestamp = pkt.timestamp - base;
        await src.add(pkt, pi === 0 ? { decoderConfig: decCfg } : undefined);
        pi++;
      }
    };
    if (vTrack && vSource) await pullTrack(vInput, vTrack, vSource);
    if (aTrack && aSource) await pullTrack(aInput, aTrack, aSource);
    await out.finalize();
    return out.target.buffer;
  }

  // MSE 分轨合成：视频轨 / 音频轨各自拼接成一块 Buffer，再交给 fMP4 逐轨 mux；
  // 若只有单一轨（纯视频或纯音频），直接复用常规 mux。
  async function muxMseTracks(m, mseV, mseA, netKept) {
    const concat = (list) => {
      const tot = list.reduce((s, b) => s + b.length, 0);
      const raw = new Uint8Array(tot); let o = 0;
      for (const b of list) { raw.set(b, o); o += b.length; }
      return raw;
    };
    const vBuf = mseV.length ? concat(mseV) : null;
    const aBuf = mseA.length ? concat(mseA) : null;
    // 网络段（非 MSE）并入对应轨：这里保守并入视频轨，交给常规 mux 再判轨
    const fallback = (vBuf ? [vBuf] : []).concat(netKept || []);
    if (vBuf && aBuf) {
      // 双轨：分别解包取轨，再合成
      const parseOne = async (buf) => {
        const input = new m.Input({ source: new m.BufferSource(buf), formats: m.ALL_FORMATS });
        return { input, vTrack: await input.getPrimaryVideoTrack(), aTrack: await input.getPrimaryAudioTrack() };
      };
      const pv = await parseOne(vBuf);
      const pa = await parseOne(aBuf);
      const vTrack = pv.vTrack, aTrack = pa.aTrack || pv.aTrack;
      const vDecCfg = vTrack ? await vTrack.getDecoderConfig() : null;
      const aDecCfg = aTrack ? await aTrack.getDecoderConfig() : null;
      const out = new m.Output({ format: new m.Mp4OutputFormat({ fastStart: "in-memory" }), target: new m.BufferTarget() });
      let vSource = null, aSource = null;
      if (vTrack) { vSource = new m.EncodedVideoPacketSource(vTrack.codec); out.addVideoTrack(vSource); }
      if (aTrack) { aSource = new m.EncodedAudioPacketSource(aTrack.codec); out.addAudioTrack(aSource); }
      await out.start();
      let pi = 0;
      if (vTrack) for await (const p of new m.EncodedPacketSink(vTrack).packets()) { await vSource.add(p, pi === 0 ? { decoderConfig: vDecCfg } : undefined); pi++; }
      pi = 0;
      if (aTrack) for await (const p of new m.EncodedPacketSink(aTrack).packets()) { await aSource.add(p, pi === 0 ? { decoderConfig: aDecCfg } : undefined); pi++; }
      await out.finalize();
      try { pv.input.dispose(); } catch (e) {}
      try { pa.input.dispose(); } catch (e) {}
      return out.target.buffer;
    }
    // 单轨或无 MSE 音频轨：退回常规 fMP4 mux
    return muxSegmentsToMp4(m, fallback);
  }

  // ===== 分段合并主流程 =====
  async function mergeSegments(items, $progress) {
    if (state.merging) { toast("已有任务进行中", "warn"); return; }
    const setProgress = (pct, text) => {
      if (!$progress) return;
      const $bar = $progress.querySelector("span"); const $t = $progress.querySelector("em");
      if ($bar && typeof pct === "number") $bar.style.width = clamp(pct, 0, 100) + "%";
      if ($t && text) $t.textContent = text;
    };
    if (!MB() || typeof MB().Input !== "function") { toast("合并组件缺失，请更新脚本", "error"); finishMerge(); return; }
    state.merging = true;
    const baseName = ((state.mergeNameOverride || trackTitle() || "video").replace(/[\\/:*?"<>|]/g, "_").trim().slice(0, 50)) || "video";
    try {
      // --- 混入剔除 + 字节排序去重 ---
      const fileKey = (u) => {
        try { const p = new URL(u); const fn = (p.pathname.match(/[^/]*$/) || [""])[0]; return p.pathname.replace(/[^/]*$/, "") + fn.replace(/\d+(\.(ts|265ts|m4s))?$/i, "$1"); }
        catch (e) { return String(u).split("?")[0]; }
      };
      const parsed = items.map((it) => {
        let rs = it.rangeStart, re = it.rangeEnd;
        if (rs == null) { const sm = /[?&](start|pos|offset)=(\d+)/.exec(it.url); if (sm) { rs = parseInt(sm[2], 10); const em = /[?&](end|to|stop)=(\d+)/.exec(it.url); re = em ? parseInt(em[2], 10) : null; } }
        return { u: it.url, it, start: rs, end: re != null ? re : null, fk: fileKey(it.url) };
      });
      const withRange = parsed.filter((x) => x.start != null);
      const noRangeCnt = parsed.length - withRange.length;
      let urls = items.map((x) => x.url);
      if (withRange.length >= 2) {
        let pool = withRange; let foundOverlap = false;
        try {
          const fg = new Map();
          withRange.forEach((x) => { if (!fg.has(x.fk)) fg.set(x.fk, []); fg.get(x.fk).push(x); });
          if (fg.size > 1) {
            const stats = [...fg.entries()].map(([k, arr]) => {
              const lo = Math.min(...arr.map((z) => z.start));
              const hi = Math.max(...arr.map((z) => (z.end != null ? z.end : z.start + 1)));
              const cov = arr.reduce((n, z) => n + Math.max(0, (z.end != null ? z.end : z.start + 1) - z.start), 0);
              return { k, arr, lo, hi, cov, n: arr.length };
            }).sort((a, b) => b.cov - a.cov || b.n - a.n);
            const top = stats[0];
            const overlaps = stats.slice(1).filter((s) => s.lo < top.hi && s.hi > top.lo);
            if (overlaps.length) {
              foundOverlap = true;
              const keepSet = new Set(top.arr.map((z) => z.u));
              for (const s of overlaps) for (const seg of s.arr) {
                const lo = seg.start, hi = seg.end != null ? seg.end : seg.start + 1;
                if (!(lo < top.hi && hi > top.lo)) keepSet.add(seg.u);
              }
              log.warn("剔除混入重叠分段，保留 " + keepSet.size + " 段");
              pool = withRange.filter((z) => keepSet.has(z.u));
            }
          }
        } catch (eM) { log.warn("混入检测异常:", eM && eM.message); }
        pool.sort((a, b) => a.start - b.start || b.it.ts - a.it.ts);
        const kept = []; let lastEnd = -1;
        for (const s of pool) { if (s.start < lastEnd) continue; kept.push(s); lastEnd = s.end != null ? s.end : s.start + 1; }
        if (noRangeCnt > 0 && !foundOverlap) {
          const keepFks = new Set(pool.map((z) => z.fk));
          const noRange = parsed.filter((x) => x.start == null && keepFks.has(x.fk));
          kept.push(...noRange.map((y) => ({ ...y, start: Infinity, end: null, noRange: true })));
        }
        urls = kept.map((x) => x.u);
      } else if (noRangeCnt === 0) {
        urls = parsed.map((x) => x.u);
      } else {
        const fg = new Map();
        parsed.forEach((x) => { if (!fg.has(x.fk)) fg.set(x.fk, []); fg.get(x.fk).push(x); });
        if (fg.size > 1) {
          const stats = [...fg.entries()].map(([k, arr]) => ({ k, arr, n: arr.length })).sort((a, b) => b.n - a.n);
          urls = stats[0].arr.map((x) => x.u);
        }
      }
      // 下载前去重（稳定键）
      const byUrl = new Map(); items.forEach((it) => { if (!byUrl.has(it.url)) byUrl.set(it.url, it); });
      const seenSeg = new Set(); const segKeys = [];
      urls = urls.filter((u) => {
        const k = segKey(u, byUrl.get(u));
        if (seenSeg.has(k)) return false;
        seenSeg.add(k); segKeys.push(k); return true;
      });
      if (!urls.length) { toast("本集分段已保存过，没有新分段", "warn"); finishMerge(); return; }

      // MSE 已捕获条目：字节已在手，直接复用，不走网络二次请求
      const mseEntries = [];
      const netUrls = []; const netKeys = []; const netMeta = [];
      for (let i = 0; i < urls.length; i++) {
        const it = byUrl.get(urls[i]);
        if (it && it.mseBytes && it.mseBytes.byteLength) {
          mseEntries.push({ it, bytes: it.mseBytes });
        } else { netUrls.push(urls[i]); netKeys.push(segKeys[i]); netMeta.push(it && it.mediaType === "audio" ? "audio" : "video"); }
        }
      // 指纹：MSE + 网络条目一起算
      const fp = (() => {
        let h = 2166136261; const s = segKeys.join("~");
        for (let i = 0; i < s.length; i++) { h ^= s.charCodeAt(i); h = Math.imul(h, 16777619); }
        return (h >>> 0).toString(36) + "-" + segKeys.length;
      })();
      const epKey = pageSig();
      const hit = ledgerHit(epKey, fp);
      if ($progress && hit && !confirm("这一集已在 " + new Date(hit.t).toLocaleString() + " 下载并保存过（" + (hit.n || 0) + " 段）。\n是否仍要重新下载？点“取消”避免重复下载。")) {
        toast("本集已下载过，已跳过（要重下请再点一次并确定）", "warn");
        finishMerge(); return;
      }

      // --- 分段下载 ---
      const gmFetch = (url, responseType, headers) => new Promise((resolve, reject) => {
        if (!_GMxhr) { reject(new Error("无 GM_xhr")); return; }
        _GMxhr({ method: "GET", url, responseType, timeout: 30000, headers: headers === undefined ? { Referer: location.href } : headers,
          onload(r) { if (r.status >= 200 && r.status < 300 && r.response) resolve(new Uint8Array(r.response)); else reject(new Error("HTTP " + r.status)); },
          onerror: () => reject(new Error("网络错误")), ontimeout: () => reject(new Error("超时")) });
      });
      const fetchSeg = async (url, cacheKey) => {
        if (cacheKey && state.segBytesCache.has(cacheKey)) {
          const hit = state.segBytesCache.get(cacheKey);
          if (hit && hit.byteLength && segBytesValid(hit)) return hit;
          if (hit) { state.segBytesCache.delete(cacheKey); state.segBytesCacheBytes = Math.max(0, state.segBytesCacheBytes - hit.byteLength); }
        }
        // 分组固化归档的字节优先（已转存 groupBytes 的段不再受 segBytesCache LRU 淘汰影响）
        if (cacheKey && state.groupBytes.has(cacheKey)) {
          const gh = state.groupBytes.get(cacheKey);
          if (gh && gh.byteLength && segBytesValid(gh)) return gh;
        }
        const pageFetch = async (cred) => { const r = await fetch(url, { credentials: cred }); if (!r.ok) throw new Error("HTTP " + r.status); const b = await r.arrayBuffer(); if (!b || !b.byteLength) throw new Error("空数据"); return new Uint8Array(b); };
        const variants = [
          ["GM+Referer", () => gmFetch(url, "arraybuffer")],
          ["GM+iq来源", () => gmFetch(url, "arraybuffer", { Referer: "https://www.iq.com/", Origin: "https://www.iq.com" })],
          ["GM+无来源", () => gmFetch(url, "arraybuffer", {})],
          ["fetch+凭证", () => pageFetch("include")],
          ["fetch", () => pageFetch("omit")],
        ];
        let lastErr = null;
        for (const [name, fn] of variants) {
          try { const data = await fn(); if (cacheKey) cacheSeg(cacheKey, data); return data; }
          catch (e) { lastErr = e; log.warn("通道失败:", name, e && e.message); }
        }
        throw lastErr;
      };
      // 网络段下载；MSE 段字节已在手，直接放入结果
      const netResults = new Array(netUrls.length);
      let nextIdx = 0, doneCount = 0, skippedCount = 0; const failedIdx = [];
      // 增量缓冲复用
      const inc = state.segInc;
      if (inc && inc.sig === pageSig() && inc.entries && inc.entries.length) {
        const byUrlInc = new Map(); inc.entries.forEach((e) => byUrlInc.set(e.url, e.bytes));
        for (let i = 0; i < netUrls.length; i++) { const b = byUrlInc.get(netUrls[i]); if (b && b.byteLength) { netResults[i] = b; doneCount++; } }
      }
      const worker = async () => {
        while (nextIdx < netUrls.length) {
          const i = nextIdx++;
          if (netResults[i] && netResults[i].byteLength) continue;
          let data = null, lastErr = null;
          for (let attempt = 0; attempt < 4 && !data; attempt++) {
            try { data = await fetchSeg(netUrls[i], netKeys[i]); }
            catch (err) { lastErr = err; if (attempt < 3) await new Promise((r) => setTimeout(r, 1500 * (attempt + 1))); }
          }
          if (!data) { skippedCount++; netResults[i] = null; failedIdx.push(i + 1); }
          else netResults[i] = data;
          doneCount++;
          setProgress(5 + (doneCount / netUrls.length) * 80, "下载分段 " + doneCount + "/" + netUrls.length);
        }
      };
      await worker();
      // 合并 MSE 字节 + 网络字节（按原顺序）
      const results = [];
      let ni = 0;
      for (const it of items) {
        if (it && it.mseBytes && it.mseBytes.byteLength) results.push(it.mseBytes);
        else results.push(netResults[ni++]);
      }
      const mseN = mseEntries.length;
      if (netUrls.length && doneCount === skippedCount) throw new Error("所有分段均下载失败，请刷新页面重新播放后再试");
      const keepN = results.filter((x) => x && x.byteLength).length;
      const keepRatio = results.length ? keepN / results.length : 0;
      if (keepRatio < MIN_KEEP_RATIO) throw new Error("只拿到 " + keepN + "/" + results.length + " 个有效分段（" + Math.round(keepRatio * 100) + "%），多半是签名过期。请刷新从头完整播放，播到片尾尽快合并。");

      // fMP4 检测
      let fm4s = false;
      for (const u8 of results) { if (!u8 || u8.length < 12) continue; const box = String.fromCharCode(u8[4], u8[5], u8[6], u8[7]); if (box === "ftyp" || box === "styp" || box === "moof") fm4s = true; break; }
      // TS 校验：裁掉头部残缺，剔坏段
      if (!fm4s) for (let i = 0; i < results.length; i++) {
        const u8 = results[i]; if (!u8 || !u8.length) continue;
        let syncAt = -1; const scanLen = Math.min(u8.length - 188, 188 * 4);
        for (let k = 0; k < scanLen; k++) { if (u8[k] === 0x47 && u8[k + 188] === 0x47) { syncAt = k; break; } }
        if (syncAt < 0) { results[i] = null; skippedCount++; }
        else if (syncAt > 0) results[i] = u8.subarray(syncAt);
      }
      // 内容去重（SHA-1）
      const seenHash = new Set();
      for (let i = 0; i < results.length; i++) {
        const u8 = results[i]; if (!u8) continue;
        const hb = await crypto.subtle.digest("SHA-1", u8);
        const hex = [...new Uint8Array(hb)].map((b) => b.toString(16).padStart(2, "0")).join("");
        if (seenHash.has(hex)) { results[i] = null; skippedCount++; } else seenHash.add(hex);
      }
      const keepN2 = results.filter((x) => x && x.byteLength).length;
      if (results.length && keepN2 / results.length < MIN_KEEP_RATIO) throw new Error("校验后只剩 " + keepN2 + "/" + results.length + " 个有效分段，成片会残缺；请刷新重新完整播放后合并。");

      // MSE 分轨：视频轨 / 音频轨各自按捕获顺序拼接；fMP4 逐轨合成；
      // 网络分段按登记的 mediaType 分轨补位（B 站 DASH 音轨不走 MSE，音频整段在网络嗅探里，必须补进音频轨）
      const mseV = [], mseA = [];
      mseEntries.forEach((e) => { if (e.it.mediaType === "audio") mseA.push(e.bytes); else mseV.push(e.bytes); });
      const netAudioKept = [], netVideoKept = [];
      for (let i = 0; i < netResults.length; i++) {
        const b = netResults[i];
        if (!b || !b.length) continue;
        ((netMeta[i] === "audio") ? netAudioKept : netVideoKept).push(b);
      }
      // 每轨单一来源（MSE 优先，网络嗅探补位），避免同一段重复拼接
      const vTrackBytes = mseV.length ? mseV : netVideoKept;
      const aTrackBytes = mseA.length ? mseA : netAudioKept;

      let outBuffer = null, outExt = ".mp4";
      if (fm4s || vTrackBytes.length || aTrackBytes.length) {
        setProgress(90, "封装 mp4 中...");
        const kept = vTrackBytes.concat(aTrackBytes);
        if (!kept.length) throw new Error("没有有效分段");
        try {
          // 组装 {mediaType, bytes} 交给分轨合并引擎（v0.8.0：init 段识别注入 + 按轨 Input+initInput + 时间戳平移）
          const segItems2 = [];
          vTrackBytes.forEach((b) => segItems2.push({ mediaType: "video", bytes: b }));
          aTrackBytes.forEach((b) => segItems2.push({ mediaType: "audio", bytes: b }));
          outBuffer = await muxSegmentsToMp4(MB(), segItems2);
        }
        catch (muxF) { log.warn("fMP4 合成失败，改存原始分段:", muxF && muxF.message); const tot = kept.reduce((s, b) => s + b.length, 0); const raw = new Uint8Array(tot); let o2 = 0; for (const b of kept) { raw.set(b, o2); o2 += b.length; } outBuffer = raw.buffer; outExt = ".m4s"; toast("mp4 合成失败，已改存 .m4s", "warn"); }
      } else {
        setProgress(87, "拼接分段...");
        const totalLen = results.reduce((sum, u8) => sum + (u8 ? u8.length : 0), 0);
        const tsData = new Uint8Array(totalLen); let offset = 0;
        for (const u8 of results) { if (!u8) continue; tsData.set(u8, offset); offset += u8.length; }
        setProgress(90, "封装 mp4 中...");
        try { outBuffer = await muxTsToMp4(MB(), results.filter((x) => x && x.length)); }
        catch (muxErr) { log.warn("mp4 合成失败，改存 TS:", muxErr && muxErr.message); outBuffer = tsData.buffer; outExt = ".ts"; toast("mp4 合成失败，已改存 .ts", "warn"); }
      }
      saveBlob(outBuffer, baseName + outExt, outExt === ".ts" ? "video/mp2t" : "video/mp4");
      ledgerPut(epKey, fp, baseName, results.length);
      setProgress(100, "下载完成");
      toast("已保存 " + baseName + outExt, "success");
      // 完整版已保存：本会话落盘的分组片段完成使命——页面脚本无法删磁盘文件，但把清理清单列给用户（用户敲定）
      try {
        if (state.groupFiles && state.groupFiles.length) {
          log.info("以下分组片段已可删除（完整版 " + baseName + outExt + " 已包含其全部内容）:\n  " + state.groupFiles.join("\n  "));
          toast("完整版已保存；桌面上的分组片段（组1~组" + state.groupFiles.length + "）已完成使命，可删除", "");
          state.groupFiles = [];
        }
      } catch (eGF) {}
      // 清缓存但保留记录与已保存标记
      clearSegCache();
      urls.forEach((u) => { const it = state.videoUrlMap.get(u); if (it && !it.savedAt) it.savedAt = Date.now(); });
    } catch (error) {
      log.error("分段下载失败", error);
      setProgress(0, "下载失败");
      toast("分段下载失败：" + ((error && error.message) || error), "error");
    } finally {
      // 合并完成后直接清理分组固化数据（用户敲定：不清理垃圾太多）
      finishMerge();
    }
  }

  function finishMerge() {
    state.merging = false;
    unlockPlayer();
    navBlockRelease();
    setAutoOn(false);
    resetCaptureState();
  }

  function saveBlob(buf, name, type) {
    const blob = new Blob([buf], { type: type || "video/mp4" });
    const url = URL.createObjectURL(blob);
    const a = document.createElement("a");
    a.href = url; a.download = name;
    document.body.appendChild(a); a.click(); a.remove();
    setTimeout(() => URL.revokeObjectURL(url), 10000);
  }

  // ===== 自动保存到桌面：首次授权一次桌面目录，句柄存 IndexedDB，之后静默写盘，不再弹窗 =====
  function idbOpen() {
    return new Promise((resolve) => {
      try {
        const idb = _unsafe.indexedDB || window.indexedDB;
        const req = idb.open("qd_rec_dirs", 1);
        req.onupgradeneeded = () => { try { req.result.createObjectStore("dirs"); } catch (e) {} };
        req.onsuccess = () => resolve(req.result);
        req.onerror = () => resolve(null);
      } catch (e) { resolve(null); }
    });
  }
  async function idbGetDesktopDir() {
    const db = await idbOpen(); if (!db) return null;
    return await new Promise((resolve) => {
      try {
        const g = db.transaction("dirs", "readonly").objectStore("dirs").get("desktop");
        g.onsuccess = () => resolve(g.result || null);
        g.onerror = () => resolve(null);
      } catch (e) { resolve(null); }
    });
  }
  async function idbSetDesktopDir(handle) {
    const db = await idbOpen(); if (!db) return;
    try { db.transaction("dirs", "readwrite").objectStore("dirs").put(handle, "desktop"); } catch (e) {}
  }
  // 在「点开始录制」的用户手势里调用：取已授权目录，或首次弹一次目录选择（选桌面）
  async function ensureDesktopDir() {
    if (state.__desktopDir) return state.__desktopDir;
    if (typeof window.showDirectoryPicker !== "function") return null;
    let h = await idbGetDesktopDir();
    if (h) {
      try {
        const p = await h.queryPermission({ mode: "readwrite" });
        if (p === "granted") { state.__desktopDir = h; return h; }
        if (p === "prompt") { const q = await h.requestPermission({ mode: "readwrite" }); if (q === "granted") { state.__desktopDir = h; return h; } }
      } catch (e) {}
    }
    try {
      h = await window.showDirectoryPicker({ startIn: "desktop", mode: "readwrite" });
      await idbSetDesktopDir(h);
      state.__desktopDir = h;
      toast("已记住该目录，以后录制完自动存进去", "success");
      return h;
    } catch (e) { return null; }
  }

  // 录制文件保存：固定走浏览器默认下载目录（本机 Edge = 桌面）。零弹窗、不认任何"记住的目录"，所见即所得。
  // 不再用 showDirectoryPicker/showSaveFilePicker 那套——它会记住用户某次误选的隐藏目录，导致文件找不到。
  function saveRecordingToDesktop(blob, name, mimeType) {
    const mt = (mimeType || "video/webm").split(";")[0];
    saveBlob(blob, name, mt);
    log.info("⑥录制：已保存到浏览器默认下载目录（桌面） " + name);
    return "desktop";
  }

  // ===== 直链下载 / 直链对合并 =====
  // 双响炮原版口径：GM_download 由浏览器原生下载管理器落盘（自动跟随 CDN 302 跳转、带 Referer），
  // 拿到的必然是 CDN 最终文件；伪媒体地址（js/css/html/json）拦截；无 GM_download 时退回 window.open
  function downloadDirect(it, $progress) {
    setAutoOn(false);
    try {
      const url = it && it.url;
      if (!url) throw new Error("无下载地址");
      const fileName = it.fileName || ((trackTitle() || "video").replace(/[\\/:*?"<>|]/g, "_").slice(0, 50) + (it.mediaType === "audio" ? ".m4a" : ".mp4"));
      if (!_GM_download) {
        // 不再 window.open 打开地址：爱奇艺等站点直链可能 302/指向伪媒体，打开会变成一页代码
        log.error("当前脚本管理器不支持 GM_download，无法下载");
        toast("当前脚本管理器不支持 GM_download，请在暴力猴/TamperMonkey 中使用本脚本", "error");
        return;
      }
      if (/\.(m?js|css|html?|json)([?#].*)?$/i.test(url)) {
        log.error("疑似网页资源地址，已拦截下载: " + url);
        toast("已拦截：该地址不是视频", "error");
        return;
      }
      _GM_download({
        url: url,
        name: fileName,
        headers: { Referer: window.location.href },
        onload: () => { toast("下载 " + fileName + " 已完成", "success"); log.info("下载完成:", fileName); },
        onerror: (error) => { log.error("下载失败", error); toast("下载 " + fileName + " 失败或已取消", "error"); },
        ontimeout: () => { toast("下载 " + fileName + " 请求超时", "error"); },
      });
    } catch (e) { toast("下载失败：" + (e && e.message), "error"); }
  }

  async function mergeDirectPair(videoItem, audioItem) {
    try {
      if (!videoItem || !audioItem) { toast("需要同时抓到视频流和音频流", "warn"); return; }
      toast("下载视频流...", "");
      const vData = await fetchBytes(videoItem.url);
      if (!vData || !vData.byteLength) throw new Error("视频流下载失败");
      toast("下载音频流...", "");
      const aData = await fetchBytes(audioItem.url);
      if (!aData || !aData.byteLength) throw new Error("音频流下载失败");
      toast("合并封装中...", "");
      const merged = await mergeMediaBuffers(vData, aData);
      const baseName = ((trackTitle() || "video").replace(/[\\/:*?"<>|]/g, "_").trim().slice(0, 50)) || "video";
      saveBlob(merged, baseName + "_merged.mp4", "video/mp4");
      toast("已合成并保存 " + baseName + "_merged.mp4", "success");
    } catch (e) { toast("合并失败：" + (e && e.message), "error"); }
  }

  // ===== 面板：悬浮按钮 + 下载面板 =====
  const CHIP_COLOR = { "①": "#1677ff", "②": "#8e44ad", "③": "#ff2d55", "④": "#e6a23c", "⑤": "#67c23a", "⑥": "#d63031" };
  const CHIP_NAME = { "①": "① 普通直链下载", "②": "② 音频下载", "③": "③ 抖音下载", "④": "④ 普通合并下载", "⑤": "⑤ 分段合并下载", "⑥": "⑥ 视频录制兜底" };

  // ===== 悬浮元素拖拽：按钮与面板均可移动，位置持久化 =====
  const POS_KEY = "qidian_panel_pos";
  function loadPos() {
    try { return JSON.parse(localStorage.getItem(POS_KEY) || "{}") || {}; }
    catch (e) { return {}; }
  }
  function savePos(key, x, y) {
    try {
      const all = loadPos();
      all[key] = { x: Math.round(x), y: Math.round(y) };
      localStorage.setItem(POS_KEY, JSON.stringify(all));
    } catch (e) {}
  }
  // 把元素按保存的左上角坐标定位；越界回收到可视区内
  function applyPos(el, key) {
    const all = loadPos()[key];
    if (!all || typeof all.x !== "number" || typeof all.y !== "number") return;
    const maxX = Math.max(0, window.innerWidth - el.offsetWidth - 4);
    const maxY = Math.max(0, window.innerHeight - el.offsetHeight - 4);
    const x = clamp(all.x, 4, maxX), y = clamp(all.y, 4, maxY);
    el.style.left = x + "px";
    el.style.top = y + "px";
    el.style.right = "auto";
    el.style.bottom = "auto";
  }
  // 为可拖拽元素绑定：按下拖动改坐标，短按不触发点击；拖动超过阈值记为拖拽，阻止后续 click
  // dragHandle 可选：只在该子元素上按下才拖拽（面板内部区域留给滚动/点击）
  function makeDraggable(el, key, dragHandle) {
    let sx = 0, sy = 0, ox = 0, oy = 0, dragging = false, moved = false;
    const start = (e) => {
      if (e.button !== 0) return;
      // 点到链接/按钮/输入框时不拦截，保证下载等点击正常触发
      const t = e.target;
      if (t && t.closest && t.closest("a,button,input,textarea,select,#qidian-panel-close,[data-qd-dl],[data-qd-merge],[data-qd-sw],[data-qd-seg-merge]")) return;
      dragging = true; moved = false;
      sx = e.clientX; sy = e.clientY;
      const rect = el.getBoundingClientRect();
      ox = rect.left; oy = rect.top;
      el.style.left = ox + "px"; el.style.top = oy + "px";
      el.style.right = "auto"; el.style.bottom = "auto";
      el.style.cursor = "move";
      e.preventDefault();
    };
    if (dragHandle) {
      dragHandle.addEventListener("mousedown", start);
    } else {
      el.addEventListener("mousedown", start);
    }
    document.addEventListener("mousemove", (e) => {
      if (!dragging) return;
      const dx = e.clientX - sx, dy = e.clientY - sy;
      if (Math.abs(dx) + Math.abs(dy) > 4) moved = true;
      if (!moved) return;
      const maxX = Math.max(0, window.innerWidth - el.offsetWidth - 4);
      const maxY = Math.max(0, window.innerHeight - el.offsetHeight - 4);
      el.style.left = clamp(ox + dx, 4, maxX) + "px";
      el.style.top = clamp(oy + dy, 4, maxY) + "px";
    });
    document.addEventListener("mouseup", () => {
      if (!dragging) return;
      dragging = false;
      el.style.cursor = "";
      if (moved) {
        const rect = el.getBoundingClientRect();
        savePos(key, rect.left, rect.top);
        el.addEventListener("click", function stopOnce(ev) { ev.stopPropagation(); ev.preventDefault(); el.removeEventListener("click", stopOnce); }, true);
      }
    });
  }

  function buildPanelButton() {
    if (state.panelBtn) return;
    const btn = document.createElement("div");
    btn.id = "qidian-btn";
    btn.title = BRAND + " v" + VERSION + "（Ctrl+Alt+D 开关面板）";
    btn.style.cssText = "position:fixed;right:16px;bottom:120px;z-index:2147483646;width:44px;height:44px;border-radius:50%;background:rgba(22,119,255,.9);color:#fff;display:flex;align-items:center;justify-content:center;font-size:20px;cursor:pointer;box-shadow:0 4px 14px rgba(0,0,0,.3);user-select:none;";
    btn.textContent = "⤓";
    btn.addEventListener("click", () => togglePanel());
    document.body.appendChild(btn);
    applyPos(btn, "btn");
    makeDraggable(btn, "btn");
    state.panelBtn = btn;
    // 快捷键 Ctrl+Alt+D
    document.addEventListener("keydown", (e) => {
      if (e.ctrlKey && e.altKey && (e.key === "d" || e.key === "D")) {
        const tag = (e.target && e.target.tagName) || "";
        if (/input|textarea|select/i.test(tag) || (e.target && e.target.isContentEditable)) return;
        e.preventDefault();
        togglePanel();
      }
    }, true);
  }

  function togglePanel() {
    if (!state.panel) { renderPanel(); return; }
    const el = state.panel.el;
    el.style.display = el.style.display === "none" ? "block" : "none";
  }

  // 当前展示用源：抖音解析优先；抖音页解析为空则不给嗅探兜底，避免页面请求误点亮分类
  function currentSources() {
    const f = currentFilter();
    const sniffed = Array.from(state.videoUrlMap.values()).filter(f);
    if (isDouyin()) {
      const parsed = dySources(pageSig());
      return parsed.length ? parsed : [];
    }
    return sniffed;
  }

  // 真直链判定（沿用旧双响炮口径）：整文件媒体后缀 / 媒体 content-type / 媒体元素发起；
  // js/json/图片/配置等伪媒体不算直链，避免列出来下载后播放器无法识别；
  // m3u8/mpd 是播放列表不是可播直链（属⑤分段/DASH 体系），剔除后爱奇艺才能正确点亮⑤分段合并
  const RE_DIRECT_EXT = /\.(mp4|m4a|mp3|aac|webm|ogg|oga|opus|flac|wav|wma|m4v|flv)(\?|#|$)/i;
  const RE_MEDIA_CT = /^(video\/|audio\/)|mp4|aac|mpeg|mp3|webm|ogg|opus|flac|wav/i;
  function isDirectMedia(it) {
    if (!it || isSegRecord(it)) return false;
    if (it.parsed) return true; // 本面板解析出的抖音直链/音频，直接可下载
    if (RE_DIRECT_EXT.test(it.url)) return true;
    const ct = String(it.source || "").toLowerCase();
    if (ct && RE_MEDIA_CT.test(ct)) return true;
    return false;
  }

  function classify(sources) {
    const v = sources.filter((x) => x.mediaType === "video");
    const a = sources.filter((x) => x.mediaType === "audio");
    const segs = sources.filter((x) => isSegRecord(x));
    const dash = sources.filter((x) => /\.(mpd|m3u8)(\?|#|$)/i.test(x.url));
    // 真直链：剔除分段与伪媒体（js/json/图片/配置等）
    const vDirect = v.filter(isDirectMedia);
    const aDirect = a.filter(isDirectMedia);
    // segMode：网络嗅探分段 ≥2，或 MSE 探测计数 ≥2（未开开关时 MSE 只计数不登记，同样代表分段流）
    const segMode = (segs.length >= 2 || (state.mseProbeCount || 0) >= 2) && !vDirect.length;
    return { v, a, segs, dash, hasV: vDirect.length > 0, hasA: aDirect.length > 0, vDirect, aDirect, segMode };
  }

  function renderPanel() {
    buildPanelButton();
    let el = state.panel && state.panel.el;
    if (!el) {
      el = document.createElement("div");
      el.id = "qidian-panel";
      el.style.cssText = "position:fixed;right:16px;bottom:172px;z-index:2147483647;width:380px;max-height:70vh;overflow-y:auto;background:#fff;color:#222;border-radius:12px;box-shadow:0 8px 30px rgba(0,0,0,.35);font-size:13px;line-height:1.6;pointer-events:auto;";
      const dragHandle = document.createElement("div");
      dragHandle.id = "qidian-panel-handle";
      dragHandle.style.cssText = "height:28px;cursor:move;display:flex;align-items:center;justify-content:center;color:#c0c6d0;font-size:12px;user-select:none;border-bottom:1px solid #f0f2f5;flex:none;position:relative;";
      dragHandle.textContent = "⋮⋮ 拖动移动面板";
      const closeBtn = document.createElement("button");
      closeBtn.id = "qidian-panel-close";
      closeBtn.type = "button";
      closeBtn.title = "关闭面板";
      closeBtn.style.cssText = "position:absolute;right:10px;top:50%;transform:translateY(-50%);width:22px;height:22px;padding:0;line-height:20px;text-align:center;border:none;border-radius:50%;background:transparent;color:#888;font-size:15px;cursor:pointer;user-select:none;";
      closeBtn.textContent = "✕";
      closeBtn.addEventListener("mouseenter", () => { closeBtn.style.background = "#f0f2f5"; closeBtn.style.color = "#333"; });
      closeBtn.addEventListener("mouseleave", () => { closeBtn.style.background = "transparent"; closeBtn.style.color = "#888"; });
      const closePanel = (ev) => { if (ev) { ev.stopPropagation(); ev.preventDefault(); } el.style.display = "none"; };
      closeBtn.addEventListener("mousedown", closePanel);
      closeBtn.addEventListener("click", closePanel);
      dragHandle.appendChild(closeBtn);
      const body = document.createElement("div");
      body.id = "qidian-panel-body";
      el.appendChild(dragHandle);
      el.appendChild(body);
      document.body.appendChild(el);
      applyPos(el, "panel");
      makeDraggable(el, "panel", dragHandle);
      state.panel = { el, body, refreshTimer: null };
    }
    paintPanel(el);
    // 定时刷新状态（标题/段数/覆盖/开关态）；抖音页隔次跳过，实际约 3 秒一刷，降低重 DOM 页面开销
    if (state.panel.refreshTimer) clearInterval(state.panel.refreshTimer);
    state.panel.refreshTimer = setInterval(() => {
      if (state.panel && !state.panel.el.style.display || state.panel.el.style.display !== "none") {
        if (isDouyin()) { state.__dyPaintSkip = !state.__dyPaintSkip; if (state.__dyPaintSkip) return; }
        paintPanel(state.panel.el);
      }
    }, 1500);
  }

  // 视频内时间格式化（双响炮口径：分组起止以播放进度为准）
  function fmtPos(s) {
    const n = Math.max(0, Math.round(Number(s) || 0));
    const p = (x) => String(x).padStart(2, "0");
    const h = Math.floor(n / 3600), m = Math.floor((n % 3600) / 60), ss = n % 60;
    return h ? h + ":" + p(m) + ":" + p(ss) : m + ":" + p(ss);
  }

  // 单组下载：把某组的固化字节按顺序封装成 mp4 保存（精彩片段只要某组时用；双响炮"点组即合并"交互）
  async function downloadGroup(gi) {
    try {
      const g = state.groups && state.groups[gi];
      if (!g || !g.keys.length) { toast("该组还没有固化字节", "warn"); return; }
      const segItems2 = [];
      g.keys.forEach((x) => { const b = state.groupBytes.get(x.k); if (b && b.length) segItems2.push({ mediaType: x.mediaType, bytes: b }); });
      if (!segItems2.length) { toast("该组没有固化字节", "error"); return; }
      toast("组" + (gi + 1) + " 合并封装中…", "");
      let fm4s = false;
      for (const x of segItems2) {
        if (x.bytes.length < 12) continue;
        const box = String.fromCharCode(x.bytes[4], x.bytes[5], x.bytes[6], x.bytes[7]);
        if (box === "ftyp" || box === "styp" || box === "moof") { fm4s = true; break; }
      }
      const buffer = fm4s ? await muxSegmentsToMp4(MB(), segItems2) : await muxTsToMp4(MB(), segItems2.map((x) => x.bytes));
      const baseName = ((trackTitle() || "video").replace(/[\\/:*?"<>|]/g, "_").trim().slice(0, 50)) || "video";
      // 组文件名用内容时间段命名（不再用会话性的组序号）：跨会话/跨轮绝不冲突，看到文件名即知是哪段内容
      const tr = (g.posMin >= 0 && g.posMax >= 0)
        ? fmtPos(g.posMin).replace(/:/g, "m") + "s-" + fmtPos(g.posMax).replace(/:/g, "m") + "s"
        : "组" + (gi + 1);
      const fileName = baseName + "_" + tr + ".mp4";
      saveBlob(buffer, fileName, "video/mp4");
      if (!state.groupFiles) state.groupFiles = [];
      state.groupFiles.push(fileName);
      toast("已保存 " + fileName, "success");
    } catch (e) {
      log.error("分组合并失败", e);
      toast("分组合并失败：" + (e && e.message), "error");
    }
  }

  // ===== ⑥ 视频录制兜底（用户敲定的新路线）：难下载的站点（分段复杂/init 缺失）直接录制播放内容 =====
  // video.captureStream() 元素捕获（非录屏）：画质无损、音视频一起录、不受窗口遮挡影响；
  // MediaRecorder 输出格式自适配（新版浏览器优先 mp4，回退 webm）；播完（ended）自动停止保存。
  // 录制是独立下载通道：不读嗅探/分段/分组数据，与①-⑤零干扰。
  function pickRecorderMime() {
    const cands = [
      "video/mp4;codecs=avc1.42E01E,mp4a.40.2",
      "video/mp4",
      "video/webm;codecs=vp9,opus",
      "video/webm;codecs=vp8,opus",
      "video/webm",
    ];
    try { return cands.find((mm) => window.MediaRecorder && MediaRecorder.isTypeSupported(mm)) || ""; } catch (e) { return ""; }
  }

  // 录制增强版：抖音等站点元素捕获（captureStream）拿不到视频轨，改走浏览器录屏 getDisplayMedia。
  // 面板⑥按钮不变、①-⑤下载功能零改动。点按钮 → 弹共享窗选【标签页】勾选音频 → 录制 → 面板点停止/浏览器停止共享 自动保存。
  async function startVideoRecording() {
    // 防抖：getDisplayMedia 异步，从点击到弹窗确认之间有空窗期，重复点击会开出多条共享 → 同步上锁
    if (state.__recStarting) { log.warn("⑥录制：启动中，忽略重复点击（防多条共享）"); return; }
    state.__recStarting = true;
    let stream = null, gotStream = null, rec = null, stopTimer = null;
    // 统一释放：原始屏幕流 + 裁剪流全停，避免"停止共享"后指示条悬挂
    const releaseAll = () => {
      try { stream && stream.getTracks().forEach((t) => t.stop()); } catch (e) {}
      try { gotStream && gotStream.getTracks().forEach((t) => t.stop()); } catch (e) {}
    };
    try {
      log.info("⑥录制：启动流程开始（录屏版）");
      if (!window.MediaRecorder) { log.warn("⑥录制：MediaRecorder 不支持"); toast("当前浏览器不支持 MediaRecorder", "error"); return; }
      if (state.recorder && state.recorder.rec && state.recorder.rec.state === "recording") { log.warn("⑥录制：已有录制进行中"); toast("已有录制进行中", "warn"); return; }

      // 注意：getDisplayMedia 必须在点击的用户手势里第一个调用，绝不能先 await 别的（如目录授权），
      // 否则手势被消耗 → getDisplayMedia 被浏览器拒绝 → 表现为"点开始没反应"。目录授权挪到录制结束后做。

      // getDisplayMedia 必须由用户手势直接触发；本函数由面板点击直接调用，符合条件
      if (!navigator.mediaDevices || !navigator.mediaDevices.getDisplayMedia) {
        log.warn("⑥录制：getDisplayMedia 不支持（需 https 或 localhost）");
        toast("当前环境不支持录屏 API（需 https 页面）", "error");
        return;
      }
      let got;
      try {
        got = await navigator.mediaDevices.getDisplayMedia({ video: { frameRate: 30 }, audio: true, preferCurrentTab: true });
      } catch (e) {
        log.warn("⑥录制：用户取消或拒绝共享", e && e.name);
        toast("已取消共享，未开始录制", "warn");
        state.__recStarting = false;
        return;
      }
      stream = got;
      gotStream = got;
      const kinds = stream.getTracks().map((t) => t.kind).join(",") || "无";
      log.info("⑥录制：取得屏幕流 轨=" + kinds);
      const vt = stream.getVideoTracks()[0];
      // 拿到流就立刻绑定"停止共享"：无论后面卡在框选还是录制中，用户点浏览器停止共享都能释放流
      if (vt) vt.onended = () => {
        log.info("⑥录制：检测到共享已被浏览器停止，释放所有流");
        try { releaseAll(); } catch (e) {}
        if (rec && rec.state !== "inactive") { try { rec.stop(); } catch (e) {} }
      };
      if (!vt) { log.warn("⑥录制：未取得画面轨"); toast("没拿到画面，请重选标签页", "error"); releaseAll(); state.__recStarting = false; return; }

      // 区域选择：弹遮罩让用户框选要录的画面（默认给个视频位预设框），只录这块，画面小、无导航/推荐
      let crop = null;
      try {
        const area = await pickRecordArea();
        if (area) {
          crop = makeCroppedStream(stream, area);
          stream = crop.stream;
          log.info("⑥录制：已选区域，只录这一块");
        } else {
          log.info("⑥录制：已取消框选，将录制整个标签页");
        }
      } catch (e) { log.warn("区域选择失败，回退整页", e); }

      const mime = pickRecorderMime();
      log.info("⑥录制：使用编码 " + (mime || "浏览器默认"));
      try { rec = mime ? new MediaRecorder(stream, { mimeType: mime }) : new MediaRecorder(stream); }
      catch (e) {
        log.warn("⑥录制：指定编码失败，回退默认", e);
        try { rec = new MediaRecorder(stream); } catch (e2) { log.error("⑥录制：默认编码也失败", e2); toast("录制启动失败：编码不支持", "error"); releaseAll(); state.__recStarting = false; return; }
      }
      const usedMime = () => (rec.mimeType || mime || "video/webm");
      const chunks = [];
      rec.ondataavailable = (e) => { if (e.data && e.data.size) chunks.push(e.data); };
      rec.onerror = (e) => { log.error("录制错误", e); toast("录制出错，请查看控制台", "error"); };
      rec.onstop = () => {
        try { clearInterval(stopTimer); } catch (e) {}
        try { stopRecHud(); } catch (e) {}
        try { restorePluginUIAfterRecord(); } catch (e) {}
        try { restoreVideoVolumeAfterRecord(); } catch (e) {}
        try {
          const um = usedMime();
          const blob = new Blob(chunks, { type: um.split(";")[0] });
          const ext = um.indexOf("mp4") >= 0 ? ".mp4" : ".webm";
          const baseName = ((trackTitle() || "video").replace(/[\\/:*?"<>|]/g, "_").trim().slice(0, 50)) || "video";
          const stamp = fmtPos(Math.round((Date.now() - (state.recorder ? state.recorder.startAt : Date.now())) / 1000)).replace(/:/g, "m") + "s";
          const fileName = baseName + "_录制_" + stamp + ext;
          try { saveRecordingToDesktop(blob, fileName, um); } catch (e) { saveBlob(blob, fileName, um.split(";")[0]); }
          toast("🎥 已保存到桌面 " + fileName, "success");
        } catch (e) { log.error("录制保存失败", e); toast("录制保存失败", "error"); }
        try { crop && crop.dispose(); } catch (e) {}
        try { stream && stream.getTracks().forEach((t) => t.stop()); } catch (e) {}
        state.recorder = null;
        state.__recording = false;
        log.info("⑥录制：录制结束，提示浮层恢复");
        renderPanel();
      };
      // 「停止共享」监听已在拿到流时提前绑定，此处不再重复绑定

      // 记下录制前的音量状态，结束时原样恢复（防录完声音突然变大）
      try { snapshotVideoVolumeBeforeRecord(); } catch (e) {}
      // 录制开始：立刻封掉所有浮层提示并清掉框选阶段残留的 toast，绝不让提示进画面
      state.__recording = true;
      try { clearTimeout(msgTimer); const tb = document.getElementById("qidian-toast"); if (tb) tb.remove(); } catch (e) {}
      try { rec.start(1000); }
      catch (eStart) {
        state.__recording = false;
        log.error("⑥录制：rec.start 失败", eStart);
        toast("录制启动失败：" + (eStart && eStart.message), "error");
        try { releaseAll(); } catch (e2) {}
        state.__recStarting = false;
        return;
      }
      state.recorder = { rec, chunks, startAt: Date.now(), mime: usedMime() };
      // 隐藏下载面板与面板按钮，避免录进画面；控制改由底部录制条承担
      try { hidePluginUIForRecord(); } catch (e) { log.warn("隐藏插件界面失败", e); }
      // 录制中提示只写控制台，不弹浮层（会被录进画面）
      log.info("⑥录制：录制中（state=" + rec.state + "，界面已隐藏）。快捷键：👁隐藏 / Alt+H恢复 / Alt+R停止");
      try { startRecHud(); } catch (e) { log.warn("悬浮录制条启动失败", e); }

      // 尽力自动停止：页面视频播完就停（检测不到就手动停止）
      stopTimer = setInterval(() => {
        try {
          let any = false, allDone = true;
          const walk = (root) => {
            root.querySelectorAll && root.querySelectorAll("video").forEach((x) => {
              try { const d = x.duration, tt = x.currentTime; if (isFinite(d) && d > 3 && tt > 0.5) { any = true; if (!x.ended && d - tt > 1) allDone = false; } } catch (e) {}
            });
          };
          walk(document);
          if (any && allDone && rec.state !== "inactive") { log.info("⑥录制：视频播完，自动保存"); rec.stop(); }
        } catch (e) {}
      }, 1000);

      // 【从头播放】点录制后把页面上所有能触及的 video 拖回 0 并重播，保证从片头开始录。
      // 注意：抖音真播放器在跨域 iframe 内，脚本够不着——那种情况脚本无法强拖，靠用户录制前手动回到片头。
      let rewound = 0;
      try {
        const all = [];
        const walk = (root) => {
          root.querySelectorAll && root.querySelectorAll("video").forEach((v) => all.push(v));
          root.querySelectorAll && root.querySelectorAll("*").forEach((el) => { if (el.shadowRoot) walk(el.shadowRoot); });
        };
        walk(document);
        all.forEach((v) => {
          try { v.currentTime = 0; rewound++; const p = v.play(); if (p && p.catch) p.catch(() => {}); } catch (e) {}
        });
      } catch (e) {}
      log.info("⑥录制：从头播放，已重置 video 数=" + rewound);
      if (rewound === 0) toast("未触及播放器，请录制前手动把视频拖到片头", "warn");
    } catch (e) {
      log.error("录制启动失败", e);
      toast("录制启动失败：" + (e && e.message), "error");
      try { releaseAll(); } catch (e2) {}
      state.__recStarting = false;
    }
    // 正常走到这里说明录制已成功启动，解锁以便下次能点；真正"进行中"由 state.recorder 拦
    state.__recStarting = false;
  }

  // ===== 独立悬浮录制条：DOM 只建一次，不随面板重绘，停止按钮永远点得到 =====
  // 显示「整段视频总时长的倒计时」——从总长往下数到 0（不是已录多久）。到 0 自动停止保存。
  // 总长优先自动读 video.duration；读不到（如抖音跨域）由用户填分钟数。
  // 找到页面上真正可见的播放器区域（含 Shadow DOM；抖音 video 本身可能 0 高，向上找可见容器）
  function findVisiblePlayerRect() {
    const all = [];
    const walk = (root) => {
      if (!root || !root.querySelectorAll) return;
      root.querySelectorAll("video").forEach((v) => all.push(v));
      root.querySelectorAll("*").forEach((el) => { if (el.shadowRoot) walk(el.shadowRoot); });
    };
    walk(document);
    let best = null, bestArea = 0;
    for (const v of all) {
      let r = v.getBoundingClientRect();
      if (!(r.width > 200 && r.height > 100)) {
        let p = v.parentElement;
        for (let i = 0; i < 6 && p; i++, p = p.parentElement) {
          const pr = p.getBoundingClientRect();
          if (pr.width > 200 && pr.height > 100 && pr.width <= innerWidth * 0.96 && pr.height <= innerHeight * 0.9) { r = pr; break; }
        }
      }
      const area = r.width * r.height;
      if (area > bestArea && r.width > 200 && r.height > 100) { bestArea = area; best = r; }
    }
    return best;
  }

  // 把录制条吸附到播放器控制条（视频底部居中；太宽则等比缩小）；滚动/resize/全屏自动跟随
  function dockRecHudToPlayer() {
    const hud = document.getElementById("qd-rec-hud");
    if (!hud || state.__recHudManual) return;
    try {
      const fs = document.fullscreenElement;
      if (fs && hud.parentElement !== fs) fs.appendChild(hud);
      else if (!fs && hud.parentElement !== document.body) document.body.appendChild(hud);
      const r = findVisiblePlayerRect();
      if (!r) return;
      const hw = hud.offsetWidth, hh = hud.offsetHeight;
      if (!hw || !hh) return;
      const scale = hw > r.width - 16 ? Math.max(0.5, (r.width - 16) / hw) : 1;
      hud.style.transformOrigin = "bottom center";
      hud.style.transform = scale < 1 ? "scale(" + scale.toFixed(3) + ")" : "none";
      const ew = hw * scale, eh = hh * scale;
      let left = r.left + (r.width - ew) / 2;
      // 下移到播放器控制条那一行：条的顶部落在播放器底边往上约 1/3 自身高，主体压在控制条上
      let top = r.bottom - Math.round(eh * 0.35);
      left = Math.max(4, Math.min(left, innerWidth - ew - 4));
      top = Math.max(4, Math.min(top, innerHeight - eh - 4));
      hud.style.left = Math.round(left) + "px";
      hud.style.top = Math.round(top) + "px";
    } catch (e) {}
  }

  // 隐藏录制条：缩成一个小红点，点红点或按 Alt+H 恢复；Alt+R 随时停止并保存
  function ensureRecMini() {
    let m = document.getElementById("qd-rec-mini");
    if (m) return m;
    m = document.createElement("div");
    m.id = "qd-rec-mini";
    m.style.cssText = "position:fixed;right:12px;bottom:12px;z-index:2147483647;width:22px;height:22px;border-radius:50%;background:rgba(255,45,85,.92);color:#fff;display:none;align-items:center;justify-content:center;font:12px/1 sans-serif;cursor:pointer;box-shadow:0 2px 10px rgba(0,0,0,.45);user-select:none;";
    m.textContent = "●";
    m.title = "点击显示录制条（Alt+H）";
    m.addEventListener("click", (e) => { e.stopPropagation(); setRecHudHidden(false); });
    document.body.appendChild(m);
    return m;
  }

  function setRecHudHidden(hidden) {
    const hud = document.getElementById("qd-rec-hud");
    if (!hud) return;
    const mini = ensureRecMini();
    if (hidden) {
      const r = hud.getBoundingClientRect();
      mini.style.left = Math.round(Math.max(4, Math.min(r.left, innerWidth - 26))) + "px";
      mini.style.top = Math.round(Math.max(4, Math.min(r.top, innerHeight - 26))) + "px";
      mini.style.right = "auto"; mini.style.bottom = "auto";
      mini.style.display = "flex";
      hud.style.display = "none";
    } else {
      mini.style.display = "none";
      hud.style.display = "flex";
      dockRecHudToPlayer();
    }
    state.__recHudHidden = !!hidden;
  }

  function ensureRecHud() {
    let hud = document.getElementById("qd-rec-hud");
    if (hud) return hud;
    hud = document.createElement("div");
    hud.id = "qd-rec-hud";
    hud.style.cssText = "position:fixed;top:12px;left:12px;z-index:2147483647;display:flex;align-items:center;gap:8px;padding:8px 12px;border-radius:12px;background:rgba(20,24,32,.94);color:#fff;box-shadow:0 4px 20px rgba(0,0,0,.35);font:13px/1.4 -apple-system,'Microsoft YaHei',sans-serif;white-space:nowrap;";
    hud.innerHTML =
      '<span id="qd-rec-grip" title="拖动移动录制条" style="color:#9aa4b2;cursor:move;font-size:15px;letter-spacing:-2px;padding:0 2px;user-select:none;">⠿</span>' +
      '<button id="qd-rec-hide" title="隐藏录制条（Alt+H 恢复）" style="padding:4px 9px;border:0;border-radius:8px;background:#3a4252;color:#d7dee9;font-weight:700;font-size:12px;cursor:pointer;">👁 隐藏</button>' +
      '<span style="color:#ff4d6a;font-weight:800;">● 录制中</span>' +
      '<span id="qd-rec-left" style="color:#ffd166;font-variant-numeric:tabular-nums;font-weight:800;font-size:15px;">剩余 --:--</span>' +
      '<span id="qd-rec-total" style="color:#9aa4b2;font-variant-numeric:tabular-nums;font-size:11px;">总长 --:--</span>' +
      '<button id="qd-rec-stop" style="padding:5px 14px;border:0;border-radius:8px;background:#ff2d55;color:#fff;font-weight:800;font-size:13px;cursor:pointer;">■ 停止并保存</button>' +
      '<span style="width:1px;height:18px;background:rgba(255,255,255,.25);"></span>' +
      '<input id="qd-rec-min" type="number" min="1" max="600" placeholder="总长分钟" style="width:70px;padding:4px 6px;border:1px solid #555;border-radius:6px;background:#2b303b;color:#fff;font-size:12px;">' +
      '<button id="qd-rec-set" style="padding:5px 10px;border:0;border-radius:8px;background:#1677ff;color:#fff;font-weight:700;font-size:12px;cursor:pointer;">设总长</button>';
    document.body.appendChild(hud);

    // 恢复记住的位置；首次默认顶部居中
    const POS_KEY = "qd_rec_hud_pos";
    try {
      const p = JSON.parse(localStorage.getItem(POS_KEY) || "null");
      if (p && isFinite(p.x) && isFinite(p.y)) {
        hud.style.left = Math.max(0, Math.min(p.x, innerWidth - 60)) + "px";
        hud.style.top = Math.max(0, Math.min(p.y, innerHeight - 40)) + "px";
      } else {
        hud.style.left = Math.max(0, Math.round((innerWidth - hud.offsetWidth) / 2)) + "px";
      }
    } catch (e) {}

    // 拖拽手柄移动（按钮/输入框不触发拖动）；拖动后进入自由模式，双击 ⠿ 回到播放器控制条
    const grip = hud.querySelector("#qd-rec-grip");
    if (grip) {
      let drag = null, moved = false, sx = 0, sy = 0;
      grip.title = "拖动移动，双击回到播放器控制条";
      grip.addEventListener("mousedown", (e) => {
        e.preventDefault(); e.stopPropagation();
        const r = hud.getBoundingClientRect();
        drag = { dx: e.clientX - r.left, dy: e.clientY - r.top };
        moved = false; sx = e.clientX; sy = e.clientY;
      });
      document.addEventListener("mousemove", (e) => {
        if (!drag) return;
        if (!moved && Math.abs(e.clientX - sx) + Math.abs(e.clientY - sy) > 3) moved = true;
        if (!moved) return;
        const x = Math.max(0, Math.min(e.clientX - drag.dx, innerWidth - hud.offsetWidth));
        const y = Math.max(0, Math.min(e.clientY - drag.dy, innerHeight - hud.offsetHeight));
        hud.style.left = x + "px"; hud.style.top = y + "px";
      });
      document.addEventListener("mouseup", () => {
        if (!drag) return;
        drag = null;
        if (moved) {
          state.__recHudManual = true;
          hud.style.transform = "none";
          try { localStorage.setItem(POS_KEY, JSON.stringify({ x: Math.round(hud.getBoundingClientRect().left), y: Math.round(hud.getBoundingClientRect().top) })); } catch (e) {}
        }
      });
      grip.addEventListener("dblclick", (e) => {
        e.preventDefault(); e.stopPropagation();
        state.__recHudManual = false;
        dockRecHudToPlayer();
        toast("录制条已回到播放器控制条", "success");
      });
    }

    hud.querySelector("#qd-rec-stop").addEventListener("click", (e) => { e.stopPropagation(); stopVideoRecording(); });
    hud.querySelector("#qd-rec-hide").addEventListener("click", (e) => { e.stopPropagation(); setRecHudHidden(true); toast("录制条已隐藏，点小红点或按 Alt+H 恢复", "success"); });
    hud.querySelector("#qd-rec-set").addEventListener("click", (e) => {
      e.stopPropagation();
      const v = parseInt(hud.querySelector("#qd-rec-min").value, 10);
      if (!v || v < 1) { toast("请输入整段视频的总长分钟数", "warn"); return; }
      if (!state.recorder) { toast("当前没有录制", "warn"); return; }
      state.recorder.deadline = Date.now() + v * 60000;
      toast("总长设为 " + v + " 分钟，倒数到 0 自动保存", "success");
      tickRecHud();
    });
    return hud;
  }

  function tickRecHud() {
    const hud = document.getElementById("qd-rec-hud");
    const rec = state.recorder;
    if (!hud || !rec) return;
    const leftEl = hud.querySelector("#qd-rec-left");
    const totalEl = hud.querySelector("#qd-rec-total");
    if (rec.deadline) {
      const totalSec = Math.max(0, Math.round((rec.deadline - rec.startAt) / 1000));
      const ms = rec.deadline - Date.now();
      if (totalEl) totalEl.textContent = "总长 " + fmtPos(totalSec);
      if (ms <= 0) {
        if (leftEl) leftEl.textContent = "00:00 已录完";
        rec.deadline = 0;
        stopVideoRecording();
      } else if (leftEl) leftEl.textContent = "剩余 " + fmtPos(Math.round(ms / 1000));
    } else {
      if (leftEl) leftEl.textContent = "剩余 --:--";
      if (totalEl) totalEl.textContent = "填总长分钟 → 自动倒数";
    }
  }

  function startRecHud() {
    const hud = ensureRecHud();
    hud.style.display = "flex";
    state.__recHudManual = false;
    dockRecHudToPlayer();
    // 自动识别视频总长：遍历可达 video 取合理 duration，填入输入框并启动倒数
    let dur = 0;
    try {
      const all = [];
      const walk = (root) => {
        root.querySelectorAll && root.querySelectorAll("video").forEach((v) => all.push(v));
        root.querySelectorAll && root.querySelectorAll("*").forEach((el) => { if (el.shadowRoot) walk(el.shadowRoot); });
      };
      walk(document);
      all.forEach((v) => { try { const d = v.duration; if (isFinite(d) && d > dur && d < 6 * 3600) dur = d; } catch (e) {} });
    } catch (e) {}
    if (state.recorder && dur > 0) {
      state.recorder.deadline = Date.now() + dur * 1000;
      const inp = hud.querySelector("#qd-rec-min");
      if (inp) inp.value = String(Math.max(1, Math.round(dur / 60)));
      log.info("⑥录制：自动识别视频总长 " + fmtPos(Math.round(dur)) + "，已启动倒数");
    }
    if (state.recorder && !(state.recorder.deadline > 0)) {
      toast("读不到视频总长，请在悬浮条填总长分钟数", "warn");
    }
    if (state.recHudTimer) clearInterval(state.recHudTimer);
    state.recHudTimer = setInterval(() => { tickRecHud(); dockRecHudToPlayer(); }, 250);
    if (!state.__recHudEventsBound) {
      state.__recHudEventsBound = true;
      addEventListener("scroll", () => dockRecHudToPlayer(), true);
      addEventListener("resize", () => dockRecHudToPlayer());
      document.addEventListener("fullscreenchange", () => dockRecHudToPlayer());
      document.addEventListener("keydown", (e) => {
        if (!state.recorder || !e.altKey) return;
        const k = (e.key || "").toLowerCase();
        if (k === "h") { e.preventDefault(); setRecHudHidden(!state.__recHudHidden); }
        if (k === "r") { e.preventDefault(); stopVideoRecording(); }
      });
    }
    tickRecHud();
  }

  function stopRecHud() {
    if (state.recHudTimer) { clearInterval(state.recHudTimer); state.recHudTimer = null; }
    const hud = document.getElementById("qd-rec-hud");
    if (hud) { try { hud.remove(); } catch (e) { hud.style.display = "none"; } }
    const mini = document.getElementById("qd-rec-mini");
    if (mini) { try { mini.remove(); } catch (e) { mini.style.display = "none"; } }
    state.__recHudHidden = false;
  }

  // ===== 区域录制：先框选屏幕上一块区域，只把这块录进视频，画面小、无导航/推荐 =====
  // getDisplayMedia 只能录整标签页，这里用 隐藏video → canvas 裁剪选区 → canvas.captureStream 交给 MediaRecorder
  function pickRecordArea() {
    return new Promise((resolve) => {
      const mask = document.createElement("div");
      // 遮罩全透明：不压暗页面，视频轮廓清晰可见，方便快速框定；只靠红框+提示标示选区
      mask.style.cssText = "position:fixed;inset:0;z-index:2147483647;background:transparent;cursor:crosshair;";
      const box = document.createElement("div");
      const tip = document.createElement("div");
      tip.style.cssText = "position:absolute;top:16px;left:50%;transform:translateX(-50%);color:#fff;background:rgba(20,24,32,.9);padding:8px 14px;border-radius:10px;font:13px/1.6 -apple-system,'Microsoft YaHei',sans-serif;text-align:center;pointer-events:none;transition:opacity .15s;";
      tip.innerHTML = "拖动鼠标框选视频区域（页面不变暗，看清轮廓直接框）· 或用红框预设<br><span style='color:#9aa4b2;font-size:12px;'>拖动画框可调整，松开后点「就用这块」</span>";
      const okBtn = document.createElement("button");
      okBtn.textContent = "就用这块";
      okBtn.style.cssText = "position:absolute;left:50%;transform:translateX(-50%);bottom:24px;padding:10px 24px;border:0;border-radius:10px;background:#ff2d55;color:#fff;font-size:14px;font-weight:700;cursor:pointer;";
      const cancelBtn = document.createElement("button");
      cancelBtn.textContent = "取消框选（录整页）";
      cancelBtn.style.cssText = "position:absolute;right:24px;bottom:24px;padding:10px 16px;border:0;border-radius:10px;background:#555;color:#fff;font-size:13px;cursor:pointer;";
      mask.appendChild(tip); mask.appendChild(box); mask.appendChild(okBtn); mask.appendChild(cancelBtn);
      document.body.appendChild(mask);

      let area = null, dragging = false, ax = 0, ay = 0;
      const apply = (a) => {
        area = a;
        box.style.cssText = "position:absolute;left:" + a.x + "px;top:" + a.y + "px;width:" + a.w + "px;height:" + a.h + "px;border:3px solid #ff2d55;background:rgba(255,45,85,.12);box-sizing:border-box;pointer-events:none;outline:1px solid rgba(255,255,255,.9);";
      };
      apply({ x: Math.round(innerWidth * 0.12), y: Math.round(innerHeight * 0.15), w: Math.round(innerWidth * 0.64), h: Math.round(innerHeight * 0.77) });
      const onDown = (e) => {
        if (e.target === okBtn || e.target === cancelBtn) return;
        tip.style.opacity = "0"; // 一开始拖框就淡出提示，不挡视频画面
        dragging = true; ax = e.clientX; ay = e.clientY;
        apply({ x: ax, y: ay, w: 1, h: 1 });
      };
      const onMove = (e) => {
        if (!dragging) return;
        apply({ x: Math.min(ax, e.clientX), y: Math.min(ay, e.clientY), w: Math.abs(e.clientX - ax), h: Math.abs(e.clientY - ay) });
      };
      const onUp = () => { dragging = false; };
      mask.addEventListener("mousedown", onDown);
      document.addEventListener("mousemove", onMove);
      document.addEventListener("mouseup", onUp);
      const done = (result) => {
        document.removeEventListener("mousemove", onMove);
        document.removeEventListener("mouseup", onUp);
        try { mask.remove(); } catch (e) {}
        resolve(result);
      };
      okBtn.addEventListener("click", (e) => { e.stopPropagation(); done(area && area.w > 80 && area.h > 80 ? area : null); });
      cancelBtn.addEventListener("click", (e) => { e.stopPropagation(); done(null); });
    });
  }

  // 把整页屏幕流裁剪成选区流；音频轨直接沿用原流
  function makeCroppedStream(src, area) {
    const v = document.createElement("video");
    v.srcObject = src; v.muted = true; v.playsInline = true; v.autoplay = true;
    const c = document.createElement("canvas");
    const ctx = c.getContext("2d");
    let sx = 0, sy = 0, sw = 1, sh = 1, raf = 0;
    const loop = () => {
      try { if (v.readyState >= 2) ctx.drawImage(v, sx, sy, sw, sh, 0, 0, c.width, c.height); } catch (e) {}
      raf = requestAnimationFrame(loop);
    };
    v.onloadedmetadata = () => {
      try {
        const st = (src.getVideoTracks()[0] && src.getVideoTracks()[0].getSettings()) || {};
        const scaleX = (st.width || v.videoWidth || innerWidth) / innerWidth;
        const scaleY = (st.height || v.videoHeight || innerHeight) / innerHeight;
        sx = Math.round(area.x * scaleX); sy = Math.round(area.y * scaleY);
        sw = Math.max(1, Math.round(area.w * scaleX)); sh = Math.max(1, Math.round(area.h * scaleY));
        c.width = sw; c.height = sh;
        ctx.fillStyle = "#000"; ctx.fillRect(0, 0, c.width, c.height);
        log.info("⑥录制：裁剪区域 " + area.w + "x" + area.h + " → 输出 " + sw + "x" + sh);
      } catch (e) { log.warn("裁剪初始化失败", e); }
      loop();
    };
    try { v.play(); } catch (e) {}
    const cs = c.captureStream(30);
    try { src.getAudioTracks().forEach((t) => cs.addTrack(t)); } catch (e) {}
    return { stream: cs, dispose: () => { try { cancelAnimationFrame(raf); v.pause(); v.srcObject = null; } catch (e) {} } };
  }

  // 录制时隐藏插件下载面板与面板按钮（它们是"插件界面"，否则会被录进画面）；停止后按记录恢复
  function hidePluginUIForRecord() {
    state.__recHiddenUI = { panel: null, btn: null };
    try {
      const p = state.panel && state.panel.el;
      if (p && p.style.display !== "none") { state.__recHiddenUI.panel = p.style.display || ""; p.style.display = "none"; }
    } catch (e) {}
    try {
      const b = state.panelBtn;
      if (b && b.style.display !== "none") { state.__recHiddenUI.btn = b.style.display || ""; b.style.display = "none"; }
    } catch (e) {}
  }

  function restorePluginUIAfterRecord() {
    try {
      const h = state.__recHiddenUI;
      if (h) {
        const p = state.panel && state.panel.el; if (p && h.panel !== null) p.style.display = h.panel;
        const b = state.panelBtn; if (b && h.btn !== null) b.style.display = h.btn;
      }
    } catch (e) {}
    state.__recHiddenUI = null;
  }

  // 录制开始时记下每个 video 的音量/静音状态，结束后原样恢复，避免声音突然变大
  function snapshotVideoVolumeBeforeRecord() {
    state.__volSnap = [];
    try {
      const all = [];
      const walk = (root) => {
        root.querySelectorAll && root.querySelectorAll("video").forEach((v) => all.push(v));
        root.querySelectorAll && root.querySelectorAll("*").forEach((el) => { if (el.shadowRoot) walk(el.shadowRoot); });
      };
      walk(document);
      all.forEach((v) => { try { state.__volSnap.push({ el: v, muted: v.muted, volume: v.volume }); } catch (e) {} });
    } catch (e) {}
    log.info("⑥录制：音量快照 video 数=" + (state.__volSnap ? state.__volSnap.length : 0));
  }

  function restoreVideoVolumeAfterRecord() {
    let n = 0;
    try {
      (state.__volSnap || []).forEach((s) => {
        try { s.el.muted = s.muted; s.el.volume = s.volume; n++; } catch (e) {}
      });
    } catch (e) {}
    state.__volSnap = null;
    log.info("⑥录制：音量已恢复原样，video 数=" + n);
  }

  function stopVideoRecording() {
    try {
      const r = state.recorder && state.recorder.rec;
      if (!r || r.state === "inactive") { toast("当前没有进行中的录制", "warn"); return; }
      stopRecHud();
      r.stop();
    } catch (e) { toast("停止录制失败", "error"); }
  }

  function paintPanel(el) {
    const sources = currentSources();
    const cls = classify(sources);
    const dy = isDouyin();
    // 抖音页只渲染 ③ 直链解析，跳过分段排序与抓全状态计算，避免重 DOM 页面反复全量扫描
    const segItemsNow = dy ? [] : sortedSegs(segItems());
    const st = dy ? { complete: false, pct: 0, text: "" } : captureStatus(segItemsNow.length, segItemsNow);

    // 分类胶囊两行：上排 ①②③，下排 ④⑤⑥；抖音页③标记，①②仅按本面板解析出的直链点亮，④⑤强制灰显
    // 分类胶囊：判定抖音 → 只亮③，其它分类（①②④⑤）全灰；普通站点按分类结果点亮
    // ⑥ 视频录制兜底（用户敲定的第六分类，全站通用）：页面上抓取不到任何地址（①②⑤全空，抖音页③无结果也算）
    // 或录制进行中时点亮——"不能正常下载、抓取不到地址的一律走录制通道"
    const recActive = !!(state.recorder && state.recorder.rec && state.recorder.rec.state === "recording");
    const activeChips = {
      "①": !dy && cls.hasV,
      "②": !dy && cls.hasA,
      "③": dy && cls.hasV,
      "④": !dy && cls.vDirect.length > 0 && cls.aDirect.length > 0,
      "⑤": !dy && cls.segMode,
      "⑥": recActive || (!cls.hasV && !cls.hasA && !cls.segMode),
    };
    const chipRow = (keys) => '<div style="text-align:center;margin:4px 0;">' + keys.map((k) => {
      const act = activeChips[k];
      return '<span title="' + CHIP_NAME[k] + '" style="display:inline-block;margin:0 6px;padding:1px 9px;border-radius:10px;font-size:12px;line-height:1.8;border:1px solid ' +
        (act ? CHIP_COLOR[k] : "#d0d7e2") + ";background:" + (act ? CHIP_COLOR[k] : "#f5f7fa") + ";color:" + (act ? "#fff" : "#9aa4b2") + ";font-weight:700;\">" + CHIP_NAME[k] + "</span>";
    }).join("") + "</div>";

    let html = "";
    html += '<div style="padding:12px 14px 8px;border-bottom:1px solid #eee;">' +
      '<div style="font-weight:800;font-size:14px;color:#1677ff;">' + BRAND + ' <span style="font-weight:400;color:#9aa4b2;font-size:11px;">v' + VERSION + '</span></div>' +
      '<div style="margin-top:4px;color:#333;">当前：' + escapeHtml(trackTitle() || "未识别") + '</div>' +
      '<div>' + chipRow(["①", "②", "③"]) + chipRow(["④", "⑤", "⑥"]) + '</div>' +
      '</div>';

    // 直链列表（①②）：抖音解析结果一并列入；只列真媒体；抖音页仅列本面板解析出的条目
      // 直链列表双保险：isDirectMedia 判定 + 已归档进 groupBytes 的分段一律排除（防止分组/分段数据污染直链下载）
      const direct = sources.filter((it) => isDirectMedia(it) && !state.groupBytes.has(segKey(it.url, it)) && (!dy || it.parsed));
    if (direct.length) {
      html += '<div style="padding:10px 14px;border-bottom:1px solid #eee;"><div style="font-weight:700;margin-bottom:6px;">地址列表（点下载 / 复制地址）</div>';
      direct.forEach((it, i) => {
        const icon = it.mediaType === "audio" ? "🎵" : "🎬";
        const label = it.mediaType === "audio" ? "音频" : "视频";
        // 画质明细行：清晰度 · 分辨率@帧率 · 大小（参考拼音优化界面；无画质数据的嗅探/音频条目不显示）
        const qParts = [];
        if (it.quality) qParts.push('<b style="color:#ff2d55;">' + escapeHtml(it.quality) + '</b>');
        if (it.dims) qParts.push(escapeHtml(it.dims) + (it.fps ? " @" + it.fps : ""));
        if (it.size) qParts.push(fmtBytes(it.size));
        const qLine = qParts.length ? '<div style="color:#555;font-size:12px;margin-top:2px;">' + qParts.join(" · ") + '</div>' : "";
        html += '<div style="margin:6px 0;padding:6px 8px;border:1px solid #eee;border-radius:8px;background:#fafbfc;">' +
          '<div><span>' + icon + '</span><span style="font-weight:700;">' + escapeHtml(it.type || label) + '</span>' +
          '<span style="color:#999;margin-left:6px;">' + escapeHtml(it.source || "") + '</span></div>' +
          qLine +
          '<div style="color:#888;font-size:11px;word-break:break-all;">' + escapeHtml(it.url.slice(0, 120)) + '</div>' +
          '<div style="margin-top:4px;"><a href="javascript:;" data-qd-dl="' + i + '" style="color:#1677ff;margin-right:12px;">下载</a>' +
          '<a href="javascript:;" data-qd-copy="' + i + '" style="color:#8e44ad;">复制地址</a></div>' +
          '</div>';
      });
      html += '</div>';
    }

    // ③ 抖音：直播页不解析；短视频/作品由本面板直接解析直链（见上方地址列表）
    if (dy && isLiveDouyin()) {
      html += '<div style="padding:10px 14px;border-bottom:1px solid #eee;">' +
        '<div style="font-weight:700;color:#ff2d55;">③ 抖音下载</div>' +
        '<div style="color:#8a93a2;font-size:12px;line-height:1.7;margin-top:4px;">当前为直播页面：直播流不做下载。录播/短视频请切到作品页再解析下载。</div>' +
        '</div>';
    }

    // ④ 普通合并（视频+音频直链对）；抖音场景框位灰显
    if (!dy && cls.vDirect.length && cls.aDirect.length) {
      const v = cls.vDirect[0]; const a = cls.aDirect[0];
      html += '<div style="padding:10px 14px;border-bottom:1px solid #eee;">' +
        '<div style="font-weight:700;color:#e6a23c;">④ 普通合并下载</div>' +
        '<div style="color:#666;font-size:12px;margin:4px 0;">视频流 + 音频流，浏览器内直接合成有声 mp4（无需开关）</div>' +
        '<a href="javascript:;" data-qd-merge style="display:inline-block;margin-top:4px;padding:4px 12px;border-radius:10px;font-weight:700;font-size:12px;color:#fff;background:#e6a23c;text-decoration:none;">合并并下载</a>' +
        '</div>';
    } else if (!dy && cls.vDirect.length && !cls.aDirect.length) {
      html += '<div style="padding:10px 14px;border-bottom:1px solid #eee;color:#8a93a2;font-size:12px;">未发现独立音频流，此类 mp4 多数自带声音；若下载后无声，刷新页面重播几秒再开面板重试。</div>';
    } else if (dy) {
      html += '<div style="padding:10px 14px;border-bottom:1px solid #eee;color:#9aa4b2;font-size:12px;">④ 普通合并：抖音视频多为单文件直链，直接在上方地址列表下载即可。</div>';
    }

    // ⑤ 分段合并；抖音场景框位灰显
    if (!dy && cls.segMode) {
      const auto = autoOn();
      const swBg = auto ? "#67c23a" : "#ff2d55";   // 关闭态红色醒目（用户敲定），开启态绿色
      const swLabel = auto ? "● 分段下载中" : "○ 点击开始下载";
      // 分组固化进度（每 30 段一组；组起止时间用段播放位置，双响炮口径）；
      // 已归档组带"下载"按钮——精彩片段只要某组时点它单独合成
      let groupHtml = "";
      try {
        if (state.groups && state.groups.length) {
          const gBtns = state.groups.map((g, gi) => {
            const range = (g.posMin >= 0 && g.posMax >= 0) ? fmtPos(g.posMin) + "–" + fmtPos(g.posMax) + " · " : "";
            return '<a href="javascript:;" data-qd-group-dl="' + gi + '" title="把该组固化分片合成一个 mp4 下载" style="display:inline-block;margin:2px 6px 2px 0;padding:2px 10px;border-radius:10px;font-size:12px;color:#fff;background:#b8860b;text-decoration:none;">组' + (gi + 1) + "：" + range + g.n + "段 · 下载</a>";
          }).join("");
          groupHtml = '<div style="margin-top:6px;color:#555;font-size:12px;">📦 分组固化（每 ' + GROUP_SIZE + ' 段一组，点组名可单独下载该段精彩部分）：</div>' +
            '<div style="margin-top:2px;line-height:1.9;">' + gBtns + '</div>';
        }
      } catch (eG) {}
      html += '<div style="padding:10px 14px;">' +
        '<div style="font-weight:700;color:#67c23a;">⑤ 分段合并下载</div>' +
        '<div style="margin:6px 0;">' +
        '<a href="javascript:;" data-qd-sw style="padding:2px 10px;border-radius:10px;font-weight:700;font-size:12px;color:#fff;text-decoration:none;background:' + swBg + ';">' + swLabel + '</a>' +
        '<a href="javascript:;" data-qd-seg-merge style="margin-left:8px;padding:2px 10px;border-radius:10px;font-weight:700;font-size:12px;color:#fff;text-decoration:none;background:#1677ff;' + (st.complete ? "" : "display:none;") + ';">分段已抓全，点击开始合并</a>' +
        '</div>' +
        '<div style="color:#555;font-size:12px;">' + escapeHtml(durationText()) + '</div>' +
        (st.complete
          ? '<div>共 <b>' + segItemsNow.length + '</b> 段，已经抓全，请点击蓝色按钮进行合并下载</div>'
          : '<div>已抓 <b>' + segItemsNow.length + '</b> 段，' + escapeHtml(preloadText(segItemsNow)) + '，未抓全</div><div>需听完才能抓全合并，拖进度条无效</div>') +
        groupHtml +
        '<div data-qd-seg-progress style="margin-top:6px;"><span style="display:inline-block;width:0%;"></span><em style="font-style:normal;color:#999;"></em></div>' +
        '</div>';
    } else if (dy) {
      html += '<div style="padding:10px 14px;color:#9aa4b2;font-size:12px;">⑤ 分段合并：抖音短视频为整段直链，无需分段抓取。</div>';
    }

    if (!sources.length && !cls.segMode) {
      html += '<div style="padding:14px;color:#999;">🔍 正在判断下载类型，请先播放几秒…</div>';
    }

    // ⑥ 视频录制兜底（用户敲定全站通用，抖音也包括）：某视频解析抓不到地址时（③无结果），
    // 直接录制播放内容——元素捕获画质无损、音视频一起录、播完自动保存——与①-⑤严格隔离零干扰
    {
      const rec = state.recorder;
      const recActive = !!(rec && rec.rec && rec.rec.state === "recording");
      const recSec = recActive ? Math.round((Date.now() - rec.startAt) / 1000) : 0;
      const kindTip = "录屏：自动从头播放 → 选【标签页】+ 勾选音频 → 停止后保存到桌面";
      html += '<div style="padding:10px 14px;">' +
        '<div style="font-weight:700;color:#d63031;">⑥ 视频录制兜底</div>' +
        '<div style="color:#555;font-size:12px;margin-top:4px;">' + kindTip +
        (recActive ? '（<b style="color:#ff2d55;">🔴 录制中 ' + fmtPos(recSec) + '</b>）' : '') +
        '</div>' +
        '<div style="margin-top:6px;">' +
        (recActive
          ? '<a href="javascript:;" data-qd-rec-stop style="padding:2px 10px;border-radius:10px;font-weight:700;font-size:12px;color:#fff;background:#ff2d55;text-decoration:none;">■ 停止录制并保存</a>'
          : '<a href="javascript:;" data-qd-rec-start style="padding:2px 10px;border-radius:10px;font-weight:700;font-size:12px;color:#fff;background:#ff2d55;text-decoration:none;">● 开始录制（选标签页）</a>') +
        '</div></div>';
    }

    const body = state.panel.body || el;
    body.innerHTML = html;
    // 存当前渲染上下文：委托 handler 从这里取数据（每次重绘自动更新，无闭包过期问题）
    state.__panelCtx = { direct, cls };
    // 事件委托挂 body：面板每 1.5s 重绘 innerHTML 也不会丢点击（根治⑤开关"点了没反应"的重绘竞态）
    if (!state.__qdDelegated) {
      state.__qdDelegated = true;
      body.addEventListener("click", (e) => {
        const t = e.target;
        if (!t || !t.closest) return;
        const dl = t.closest("[data-qd-dl]");
        if (dl) { const arr = (state.__panelCtx && state.__panelCtx.direct) || []; const it = arr[Number(dl.getAttribute("data-qd-dl"))]; if (it) downloadDirect(it, null); return; }
        const cp = t.closest("[data-qd-copy]");
        if (cp) { const arr2 = (state.__panelCtx && state.__panelCtx.direct) || []; const it2 = arr2[Number(cp.getAttribute("data-qd-copy"))]; if (it2) { copyText(it2.url); toast("地址已复制", ""); } return; }
        if (t.closest("[data-qd-merge]")) { const c3 = (state.__panelCtx && state.__panelCtx.cls) || {}; mergeDirectPair(c3.vDirect && c3.vDirect[0], c3.aDirect && c3.aDirect[0]); return; }
        if (t.closest("[data-qd-sw]")) { toggleAuto(); return; }
        if (t.closest("[data-qd-rec-start]")) { log.info("⑥录制：收到开始请求，启动流程…"); startVideoRecording(); return; }
        if (t.closest("[data-qd-rec-stop]")) { log.info("⑥录制：收到停止请求"); stopVideoRecording(); return; }
        const gdl = t.closest("[data-qd-group-dl]");
        if (gdl) { downloadGroup(Number(gdl.getAttribute("data-qd-group-dl"))); return; }
        const segM = t.closest("[data-qd-seg-merge]");
        if (segM) mergeSegments(sortedSegs(segItems()), body.querySelector("[data-qd-seg-progress]"));
      });
    }
  }

  function toggleAuto() {
    const on = !autoOn();
    setAutoOn(on);
    if (on) {
      // 开开关：从头重播以完整覆盖
      const v = mainVideo();
      if (v) { try { v.currentTime = 0; v.play(); } catch (e) {} }
      toast(on ? "已开启分段下载，请完整听完到片尾" : "已关闭", "");
    } else {
      unlockPlayer(); navBlockRelease(); resetCaptureState();
      toast("已关闭分段下载", "");
    }
    renderPanel();
  }

  function copyText(text) {
    try {
      if (navigator.clipboard && navigator.clipboard.writeText) { navigator.clipboard.writeText(text); return; }
    } catch (e) {}
    const ta = document.createElement("textarea");
    ta.value = text; document.body.appendChild(ta); ta.select();
    try { document.execCommand("copy"); } catch (e) {}
    ta.remove();
  }

  // #MODULES#

  // 启动
  try {
    document.addEventListener("DOMContentLoaded", init, true);
    // 某些场景 DOMContentLoaded 已过
    if (document.readyState !== "loading") init();
  } catch (e) { log.error("boot error", e && e.message); }

  function init() {
    try {
      versionBoot();
      hookFetch();
      hookXHR();
      hookMSE();
      armVideoEnded();
      startIdentityWatch();
      buildPanelButton();
      log.info("booted v" + VERSION);
    } catch (e) { log.error("init error", e); }
  }


  // ===== 内联转封装库 Mediabunny（MIT，浏览器内音视频合成） =====
/* mediabunny (MIT) https://github.com/Vanilagy/mediabunny - 浏览器内音视频合并封装库 */
var Mediabunny=(()=>{var Bs=Object.defineProperty;var Al=Object.getOwnPropertyDescriptor;var xl=Object.getOwnPropertyNames;var Cl=Object.prototype.hasOwnProperty;var Pl=(r,e)=>{for(var t in e)Bs(r,t,{get:e[t],enumerable:!0})},El=(r,e,t,i)=>{if(e&&typeof e=="object"||typeof e=="function")for(let n of xl(e))!Cl.call(r,n)&&n!==t&&Bs(r,n,{get:()=>e[n],enumerable:!(i=Al(e,n))||i.enumerable});return r};var _l=r=>El(Bs({},"__esModule",{value:!0}),r);var Yd={};Pl(Yd,{ALL_FORMATS:()=>Da,BufferSource:()=>Oi,BufferTarget:()=>It,EncodedAudioPacketSource:()=>Wi,EncodedPacketSink:()=>jt,EncodedVideoPacketSource:()=>Hi,Input:()=>hr,Mp4OutputFormat:()=>ii,Output:()=>ji});function g(r){if(!r)throw new Error("Assertion failed.")}var Qi=Math.PI/180,Il=180/Math.PI,ai=r=>{let e=(r%360+360)%360;if(e===0||e===90||e===180||e===270)return e;throw new Error(`Invalid rotation ${r}.`)},Bt=[1,0,0,0,1,0,0,0,1],Xi=(r,e,t)=>{let[i,n,,a,s]=r,o=Math.abs(i)*e+Math.abs(a)*t,c=Math.abs(n)*e+Math.abs(s)*t;return Rt(Rt(Za(-e/2,-t/2),r),Za(o/2,c/2))},oi=r=>{let[e,t]=r,i=Math.atan2(t,Ms(r)?-e:e);return ai(Rl(i*Il,90))},Ms=r=>{let[e,t,,i,n]=r;return e*n-t*i<0},$i=r=>{let e=r*Qi,t=Math.round(Math.cos(e)),i=Math.round(Math.sin(e));return[t,i,0,-i,t,0,0,0,1]},Za=(r,e)=>[1,0,0,0,1,0,r,e,1],Yi=(r,e)=>[r,0,0,0,e,0,0,0,1],Rt=(r,e)=>{let t=new Array(9);for(let i=0;i<3;i++)for(let n=0;n<3;n++)t[3*i+n]=r[3*i]*e[n]+r[3*i+1]*e[3+n]+r[3*i+2]*e[6+n];return t};var $=r=>r&&r[r.length-1],it=r=>r>=0&&r<2**32,Ja=r=>r>=-(2**31)&&r<2**31,F=r=>{let e=0;for(;r.readBits(1)===0&&e<32;)e++;if(e>=32)throw new Error("Invalid exponential-Golomb code.");return 2**e-1+r.readBits(e)};var nt=r=>{let e=F(r);return e%2===0?-(e/2):(e+1)/2};var ke=r=>r.constructor===Uint8Array?r:ArrayBuffer.isView(r)?new Uint8Array(r.buffer,r.byteOffset,r.byteLength):new Uint8Array(r),W=r=>r.constructor===DataView?r:ArrayBuffer.isView(r)?new DataView(r.buffer,r.byteOffset,r.byteLength):new DataView(r),vl=typeof globalThis.TextEncoder<"u"?globalThis.TextEncoder:class{constructor(){this.encoding="utf-8"}encode(e=""){let t=new Uint8Array(3*e.length),i=0;for(let n=0;n<e.length;n++){let a=e.charCodeAt(n);if(a<128)t[i++]=a;else if(a<2048)t[i++]=192|a>>6,t[i++]=128|a&63;else if(a<55296||a>57343)t[i++]=224|a>>12,t[i++]=128|a>>6&63,t[i++]=128|a&63;else{let s=n+1<e.length?e.charCodeAt(n+1):0;a<56320&&s>=56320&&s<=57343?(a=65536+(a-55296<<10)+(s-56320),n++,t[i++]=240|a>>18,t[i++]=128|a>>12&63,t[i++]=128|a>>6&63,t[i++]=128|a&63):(t[i++]=239,t[i++]=191,t[i++]=189)}}return t.slice(0,i)}},$t=typeof globalThis.TextDecoder<"u"?globalThis.TextDecoder:class{constructor(e="utf-8"){let t=e.trim().toLowerCase();if(t==="utf-8"||t==="utf8"||t==="unicode-1-1-utf-8")this.encoding="utf-8";else if(t==="utf-16le"||t==="utf-16")this.encoding="utf-16le";else if(t==="utf-16be")this.encoding="utf-16be";else throw new RangeError(`The encoding label provided ('${e}') is invalid.`)}decode(e){let t=e?ke(e):new Uint8Array(0),i=[];if(this.encoding==="utf-8"){let a=t.length>=3&&t[0]===239&&t[1]===187&&t[2]===191?3:0;for(;a<t.length;){let s=t[a];if(s<128){i.push(s),a++;continue}let o,c;if(s>=194&&s<224)o=1,c=s&31;else if(s>=224&&s<240)o=2,c=s&15;else if(s>=240&&s<245)o=3,c=s&7;else{i.push(65533),a++;continue}let l=s===224?160:s===240?144:128,u=s===237?159:s===244?143:191,d=1;for(;d<=o;d++){let f=a+d<t.length?t[a+d]:0;if(f<l||f>u)break;c=c<<6|f&63,l=128,u=191}a+=d,d<=o?i.push(65533):c>=65536?(c-=65536,i.push(55296|c>>10,56320|c&1023)):i.push(c)}}else{let a=this.encoding==="utf-16le",s=a?255:254,o=a?254:255,c=t.length>=2&&t[0]===s&&t[1]===o?2:0;for(;c+1<t.length;){let l=a?t[c]|t[c+1]<<8:t[c]<<8|t[c+1];if(c+=2,l>=55296&&l<=56319){let u=c+1<t.length?a?t[c]|t[c+1]<<8:t[c]<<8|t[c+1]:-1;u>=56320&&u<=57343?(i.push(l,u),c+=2):i.push(65533)}else l>=56320&&l<=57343?i.push(65533):i.push(l)}c<t.length&&i.push(65533)}let n="";for(let a=0;a<i.length;a+=8192)n+=String.fromCharCode(...i.slice(a,a+8192));return n}},ie=new $t,Ee=new vl;var Ds=r=>Object.fromEntries(Object.entries(r).map(([e,t])=>[t,e])),Yt={bt709:1,bt470bg:5,smpte170m:6,bt2020:9,smpte432:12},De=Ds(Yt),Zt={bt709:1,smpte170m:6,linear:8,"iec61966-2-1":13,pq:16,hlg:18},Oe=Ds(Zt),Jt={rgb:0,bt709:1,bt470bg:5,smpte170m:6,"bt2020-ncl":9},Ue=Ds(Jt),ci=r=>!!r&&!!r.primaries&&!!r.transfer&&!!r.matrix&&r.fullRange!==void 0,eo=r=>!r||r.primaries==null&&r.transfer==null&&r.matrix==null&&r.fullRange==null,Zi={primaries:void 0,transfer:void 0,matrix:void 0,fullRange:void 0},Os=r=>r instanceof ArrayBuffer||typeof SharedArrayBuffer<"u"&&r instanceof SharedArrayBuffer||ArrayBuffer.isView(r),Pe=class{constructor(){this.currentPromise=Promise.resolve(),this.pending=0}async acquire(){let e,t=new Promise(n=>{let a=!1;e=()=>{a||(n(),this.pending--,a=!0)}}),i=this.currentPromise;return this.currentPromise=t,this.pending++,await i,e}},to=/^[0-9a-fA-F]+$/,Ft=r=>[...r].map(e=>e.toString(16).padStart(2,"0")).join(""),ro=r=>{g(r.length%2===0);let e=new Uint8Array(r.length/2);for(let t=0;t<r.length;t+=2)e[t/2]=parseInt(r.slice(t,t+2),16);return e},Us=r=>(r=r>>1&1431655765|(r&1431655765)<<1,r=r>>2&858993459|(r&858993459)<<2,r=r>>4&252645135|(r&252645135)<<4,r=r>>8&16711935|(r&16711935)<<8,r=r>>16&65535|(r&65535)<<16,r>>>0),pt=(r,e,t)=>{let i=0,n=r.length-1,a=-1;for(;i<=n;){let s=i+n>>1,o=t(r[s]);o===e?(a=s,n=s-1):o<e?i=s+1:n=s-1}return a},Q=(r,e,t)=>{let i=0,n=r.length-1,a=-1;for(;i<=n;){let s=i+(n-i+1)/2|0;t(r[s])<=e?(a=s,i=s+1):n=s-1}return a};var gt=()=>{let r,e;return{promise:new Promise((i,n)=>{r=i,e=n}),resolve:r,reject:e}},zs=(r,e)=>{let t=r.indexOf(e);t!==-1&&r.splice(t,1)},Ns=(r,e)=>{for(let t=r.length-1;t>=0;t--)if(e(r[t]))return r[t]},br=(r,e)=>{for(let t=r.length-1;t>=0;t--)if(e(r[t]))return t;return-1};var _e=r=>{throw new Error(`Unexpected value: ${r}`)},li=(r,e,t)=>{let i=r.getUint8(e),n=r.getUint8(e+1),a=r.getUint8(e+2);return t?i|n<<8|a<<16:i<<16|n<<8|a};var io=(r,e,t,i)=>{t=t>>>0,t=t&16777215,i?(r.setUint8(e,t&255),r.setUint8(e+1,t>>>8&255),r.setUint8(e+2,t>>>16&255)):(r.setUint8(e,t>>>16&255),r.setUint8(e+1,t>>>8&255),r.setUint8(e+2,t&255))};var st=(r,e,t)=>Math.max(e,Math.min(t,r));var ne="und",kt=r=>{let e=Math.round(r);return Math.abs(r/e-1)<10*Number.EPSILON?e:r},Rl=(r,e)=>Math.round(r/e)*e,Ji=(r,e)=>Math.round(r*e)/e,en=(r,e)=>Math.floor(r/e)*e;var no=r=>{let e=0;for(;r;)e++,r>>=1;return e},tn=r=>{let e=0;for(;r!==0;)r&=r-1,e++;return e},Bl=/^[a-z]{3}$/,Tr=r=>Bl.test(r),Vs=1e6*(1+Number.EPSILON);var so=(r,e)=>{let t=r<0?-1:1;r=Math.abs(r);let i=0,n=1,a=1,s=0,o=r;for(;;){let c=Math.floor(o),l=c*a+i,u=c*s+n;if(u>e)return{num:t*a,den:s};if(i=a,n=s,a=l,s=u,o=1/(o-c),!isFinite(o))break}return{num:t*a,den:s}};var Fs=null,Ls=()=>Fs!==null?Fs:Fs=!!(typeof navigator<"u"&&(navigator.vendor?.includes("Google Inc")||/Chrome/.test(navigator.userAgent)));var Fl=(async()=>{})().constructor,P=r=>r instanceof Fl||r instanceof Promise?!0:typeof r?.then=="function",er=(r,e)=>r!==-1?r:e;var ui=function*(r){for(let e in r){let t=r[e];t!==void 0&&(yield{key:e,value:t})}};var di=r=>{let e;try{e=atob(r)}catch{throw new Error("Invalid base64 string.")}let t=new Uint8Array(e.length);for(let i=0;i<e.length;i++)t[i]=e.charCodeAt(i);return t};var ao=(r,e)=>{if(r.length!==e.length)return!1;for(let t=0;t<r.length;t++)if(r[t]!==e[t])return!1;return!0},rn=()=>{Symbol.dispose??=Symbol("Symbol.dispose")},Mt=r=>typeof r=="number"&&!Number.isNaN(r),at=(r,e)=>{if(e.includes("://"))return e;if(r.includes("://")){let o=r.indexOf("?");o!==-1&&(r=r.slice(0,o))}let t;if(e.startsWith("/")){let o=r.indexOf("://");if(o===-1)t=e;else{let c=r.indexOf("/",o+3);c===-1?t=r+e:t=r.slice(0,c)+e}}else{let o=r.lastIndexOf("/");o===-1?t=e:t=r.slice(0,o+1)+e}let i="",n=t.indexOf("://");if(n!==-1){let o=t.indexOf("/",n+3);o!==-1&&(i=t.slice(0,o),t=t.slice(o))}let a=t.split("/"),s=[];for(let o of a)o===".."?s.pop():o!=="."&&s.push(o);return i+s.join("/")},oo=(r,e)=>{let t=r.indexOf("?");if(t===-1)return null;let i=r.indexOf("#",t),n=r.slice(t+1,i===-1?void 0:i);for(let a of n.split("&")){let s=a.indexOf("="),o=s===-1?a:a.slice(0,s),c=s===-1?"":a.slice(s+1);try{if(decodeURIComponent(o)===e)return decodeURIComponent(c)}catch{}}return null},tr=(r,e)=>{let t=0;for(let i=0;i<r.length;i++)e(r[i])&&t++;return t},Sr=(r,e)=>{let t=-1,i=1/0;for(let n=0;n<r.length;n++){let a=e(r[n]);(t===-1||a<i)&&(i=a,t=n)}return t};var fi=r=>{g(Number.isInteger(r.num)),g(Number.isInteger(r.den)),g(r.den!==0);let e=Math.abs(r.num),t=Math.abs(r.den);for(;t!==0;){let n=e%t;e=t,t=n}let i=e||1;return{num:r.num/i,den:r.den/i}};var Hs=r=>new Promise(e=>setTimeout(e,r));var Ar=r=>Array.isArray(r)?r:[r],Ne=class{constructor(){this._listeners=new Map}on(e,t,i){this._listeners.has(e)||this._listeners.set(e,new Set);let n={fn:t,once:i?.once??!1};return this._listeners.get(e).add(n),()=>{this._listeners.get(e)?.delete(n)}}_emit(...e){let[t,i]=e,n=this._listeners.get(t);if(n)for(let a of n){try{a.fn(i)}catch(s){console.error(s)}a.once&&n.delete(a)}}};var Ws=r=>r!==null&&typeof r=="object"&&Object.getPrototypeOf(r)===Object.prototype&&Object.values(r).every(e=>typeof e=="string");var ot;(function(r){r[r.Silent=0]="Silent",r[r.Errors=1]="Errors",r[r.Warnings=2]="Warnings",r[r.Info=3]="Info"})(ot||(ot={}));var H=class r{constructor(){}static get level(){return r._level}static set level(e){if(e!==ot.Silent&&e!==ot.Errors&&e!==ot.Warnings&&e!==ot.Info)throw new TypeError("Invalid log level. Use one of the values of the LogLevel enum.");r._level=e}static get _emitter(){return r._emitterInstance??=new Ne}static on(e,t,i){return r._emitter.on(e,t,i)}static _error(...e){r._emitter._emit("error",e),r._level>=ot.Errors&&console.error(...e)}static _warn(...e){r._emitter._emit("warn",e),r._level>=ot.Warnings&&console.warn(...e)}static _info(...e){r._emitter._emit("info",e),r._level>=ot.Info&&console.info(...e)}};H._level=ot.Info;H._emitterInstance=null;var je=class{constructor(e,t){if(this.data=e,this.mimeType=t,!(e instanceof Uint8Array))throw new TypeError("data must be a Uint8Array.");if(typeof t!="string")throw new TypeError("mimeType must be a string.")}},hi=class{constructor(e,t,i,n){if(this.data=e,this.mimeType=t,this.name=i,this.description=n,!(e instanceof Uint8Array))throw new TypeError("data must be a Uint8Array.");if(t!==void 0&&typeof t!="string")throw new TypeError("mimeType, when provided, must be a string.");if(i!==void 0&&typeof i!="string")throw new TypeError("name, when provided, must be a string.");if(n!==void 0&&typeof n!="string")throw new TypeError("description, when provided, must be a string.")}},co=r=>{if(!r||typeof r!="object")throw new TypeError("tags must be an object.");if(r.title!==void 0&&typeof r.title!="string")throw new TypeError("tags.title, when provided, must be a string.");if(r.description!==void 0&&typeof r.description!="string")throw new TypeError("tags.description, when provided, must be a string.");if(r.artist!==void 0&&typeof r.artist!="string")throw new TypeError("tags.artist, when provided, must be a string.");if(r.album!==void 0&&typeof r.album!="string")throw new TypeError("tags.album, when provided, must be a string.");if(r.albumArtist!==void 0&&typeof r.albumArtist!="string")throw new TypeError("tags.albumArtist, when provided, must be a string.");if(r.trackNumber!==void 0&&(!Number.isInteger(r.trackNumber)||r.trackNumber<=0))throw new TypeError("tags.trackNumber, when provided, must be a positive integer.");if(r.tracksTotal!==void 0&&(!Number.isInteger(r.tracksTotal)||r.tracksTotal<=0))throw new TypeError("tags.tracksTotal, when provided, must be a positive integer.");if(r.discNumber!==void 0&&(!Number.isInteger(r.discNumber)||r.discNumber<=0))throw new TypeError("tags.discNumber, when provided, must be a positive integer.");if(r.discsTotal!==void 0&&(!Number.isInteger(r.discsTotal)||r.discsTotal<=0))throw new TypeError("tags.discsTotal, when provided, must be a positive integer.");if(r.genre!==void 0&&typeof r.genre!="string")throw new TypeError("tags.genre, when provided, must be a string.");if(r.date!==void 0&&(!(r.date instanceof Date)||Number.isNaN(r.date.getTime())))throw new TypeError("tags.date, when provided, must be a valid Date.");if(r.creationTime!==void 0&&r.creationTime!==null&&(!(r.creationTime instanceof Date)||Number.isNaN(r.creationTime.getTime())))throw new TypeError("tags.creationTime, when provided, must be a valid Date or null.");if(r.beatsPerMinute!==void 0&&(!Number.isInteger(r.beatsPerMinute)||r.beatsPerMinute<=0))throw new TypeError("tags.beatsPerMinute, when provided, must be a positive integer.");if(r.lyrics!==void 0&&typeof r.lyrics!="string")throw new TypeError("tags.lyrics, when provided, must be a string.");if(r.images!==void 0){if(!Array.isArray(r.images))throw new TypeError("tags.images, when provided, must be an array.");for(let e of r.images){if(!e||typeof e!="object")throw new TypeError("Each image in tags.images must be an object.");if(!(e.data instanceof Uint8Array))throw new TypeError("Each image.data must be a Uint8Array.");if(typeof e.mimeType!="string")throw new TypeError("Each image.mimeType must be a string.");if(!["coverFront","coverBack","unknown"].includes(e.kind))throw new TypeError("Each image.kind must be 'coverFront', 'coverBack', or 'unknown'.")}}if(r.comment!==void 0&&typeof r.comment!="string")throw new TypeError("tags.comment, when provided, must be a string.");if(r.raw!==void 0){if(!r.raw||typeof r.raw!="object")throw new TypeError("tags.raw, when provided, must be an object.");for(let e of Object.values(r.raw))if(e!==null&&typeof e!="string"&&!(Array.isArray(e)&&e.every(t=>typeof t=="string"))&&!(e instanceof Uint8Array)&&!(Array.isArray(e)&&e.every(t=>t instanceof Uint8Array))&&!(e instanceof je)&&!(e instanceof hi)&&!Ws(e))throw new TypeError("Each value in tags.raw must be a string, string array, Uint8Array, Uint8Array array, RichImageData, AttachedFile, Record<string, string>, or null.")}};var fe={default:!0,primary:!0,forced:!1,original:!1,commentary:!1,hearingImpaired:!1,visuallyImpaired:!1},lo=r=>{if(!r||typeof r!="object")throw new TypeError("disposition must be an object.");if(r.default!==void 0&&typeof r.default!="boolean")throw new TypeError("disposition.default must be a boolean.");if(r.primary!==void 0&&typeof r.primary!="boolean")throw new TypeError("disposition.primary must be a boolean.");if(r.forced!==void 0&&typeof r.forced!="boolean")throw new TypeError("disposition.forced must be a boolean.");if(r.original!==void 0&&typeof r.original!="boolean")throw new TypeError("disposition.original must be a boolean.");if(r.commentary!==void 0&&typeof r.commentary!="boolean")throw new TypeError("disposition.commentary must be a boolean.");if(r.hearingImpaired!==void 0&&typeof r.hearingImpaired!="boolean")throw new TypeError("disposition.hearingImpaired must be a boolean.");if(r.visuallyImpaired!==void 0&&typeof r.visuallyImpaired!="boolean")throw new TypeError("disposition.visuallyImpaired must be a boolean.")};var q=class r{constructor(e){this.bytes=e,this.pos=0}seekToByte(e){this.pos=8*e}readBit(){let e=Math.floor(this.pos/8),t=this.bytes[e]??0,i=7-(this.pos&7),n=(t&1<<i)>>i;return this.pos++,n}readBits(e){if(e===1)return this.readBit();let t=0;for(let i=0;i<e;i++)t<<=1,t|=this.readBit();return t}writeBits(e,t){let i=this.pos+e;for(let n=this.pos;n<i;n++){let a=Math.floor(n/8),s=this.bytes[a],o=7-(n&7);s&=~(1<<o),s|=(t&1<<i-n-1)>>i-n-1<<o,this.bytes[a]=s}this.pos=i}copyBits(e,t){let i=0;for(i;i<e-7;i+=8)this.writeBits(8,t.readBits(8));let n=e-i;n>0&&this.writeBits(n,t.readBits(n))}readAlignedByte(){if(this.pos%8!==0)throw new Error("Bitstream is not byte-aligned.");let e=this.pos/8,t=this.bytes[e]??0;return this.pos+=8,t}skipBits(e){this.pos+=e}getBitsLeft(){return this.bytes.length*8-this.pos}clone(){let e=new r(this.bytes);return e.pos=this.pos,e}};var Ve=[96e3,88200,64e3,48e3,44100,32e3,24e3,22050,16e3,12e3,11025,8e3,7350],Dt=[-1,1,2,3,4,5,6,8],Ml=[1,2,3,4,6,7,17,19,20,21,22],mi=r=>{if(!r||r.byteLength<2)throw new TypeError("AAC description must be at least 2 bytes long.");let e=new q(r),t=qs(e),{frequencyIndex:i,sampleRate:n}=Ks(e),a=e.readBits(4),s=null;a>=1&&a<=7&&(s=Dt[a]);let o=t,c=!1,l=n;(t===5||t===29)&&(c=t===29,l=Ks(e).sampleRate,o=qs(e),o===22&&e.skipBits(4));let u=1024;if(Ml.includes(o)&&(u=e.readBits(1)?960:1024),t!==5&&t!==29)for(;e.getBitsLeft()>15;){let d=e.pos;if(e.readBits(11)!==695){e.pos=d+1;continue}qs(e)===5&&e.readBits(1)&&(l=Ks(e).sampleRate,e.getBitsLeft()>11&&e.readBits(11)===1352&&(c=!!e.readBits(1)));break}return s!==null&&s>1&&(c=!1),{objectType:t,coreObjectType:o,frequencyIndex:i,channelConfiguration:a,coreSampleRate:n,outputSampleRate:l,outputNumberOfChannels:c&&s===1?2:s,frameLength:u}},qs=r=>{let e=r.readBits(5);return e===31?32+r.readBits(6):e},Ks=r=>{let e=r.readBits(4);return e===15?{frequencyIndex:e,sampleRate:r.readBits(24)}:{frequencyIndex:e,sampleRate:e<Ve.length?Ve[e]:null}},ho=r=>{let e=r.objectType===5||r.objectType===29,t=r.objectType===29,i=e?r.outputSampleRate/2:r.outputSampleRate,n=t?1:r.outputNumberOfChannels,a=Dt.indexOf(n);if(a===-1)throw new TypeError(`Unsupported number of channels: ${r.outputNumberOfChannels}`);let s=16;r.objectType>=32&&(s+=6),js(i)===15&&(s+=24),e&&(s+=9,js(r.outputSampleRate)===15&&(s+=24));let o=Math.ceil(s/8),c=new Uint8Array(o),l=new q(c);return uo(l,r.objectType),fo(l,i),l.writeBits(4,a),e&&(fo(l,r.outputSampleRate),uo(l,2)),l.writeBits(3,0),c},uo=(r,e)=>{e<32?r.writeBits(5,e):(r.writeBits(5,31),r.writeBits(6,e-32))},fo=(r,e)=>{let t=js(e);r.writeBits(4,t),t===15&&r.writeBits(24,e)},js=r=>{let e=Ve.indexOf(r);return e===-1?15:e};var Dl=[44100,48e3,32e3],Ol=[-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,32,40,48,56,64,80,96,112,128,160,192,224,256,320,-1,-1,32,48,56,64,80,96,112,128,160,192,224,256,320,384,-1,-1,32,64,96,128,160,192,224,256,288,320,352,384,416,448,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,8,16,24,32,40,48,56,64,80,96,112,128,144,160,-1,-1,8,16,24,32,40,48,56,64,80,96,112,128,144,160,-1,-1,32,48,56,64,80,96,112,128,144,160,176,192,224,256,-1],pi=1483304551,nn=1231971951,Ul=(r,e,t,i,n)=>e===0?0:e===1?Math.floor(144*t/(i<<r))+n:e===2?Math.floor(144*t/i)+n:(Math.floor(12*t/i)+n)*4,mo=(r,e,t,i)=>e===0?0:e===1?144*t/(i<<r):e===2?144*t/i:12*t/i*4,sn=(r,e)=>r===3?e===3?21:36:e===3?13:21,gi=(r,e)=>{let t=r>>>24,i=r>>>16&255,n=r>>>8&255,a=r&255;if(t!==255&&i!==255&&n!==255&&a!==255)return{header:null,bytesAdvanced:4};if(t!==255)return{header:null,bytesAdvanced:1};if((i&224)!==224)return{header:null,bytesAdvanced:1};let s=0,o=0;i&16?s=i&8?0:1:(s=1,o=1);let c=i>>3&3,l=i>>1&3,u=n>>4&15,d=(n>>2&3)%3,f=n>>1&1,m=a>>6&3,p=a>>4&3,h=a>>3&1,k=a>>2&1,w=a&3,S=Ol[s*16*4+l*16+u];if(S===-1)return{header:null,bytesAdvanced:1};let b=S*1e3,T=Dl[d]>>s+o,y=Ul(s,l,b,T,f);if(e!==null&&e<y)return{header:null,bytesAdvanced:1};let A;return c===3?A=l===3?384:1152:l===3?A=384:l===2?A=1152:A=576,{header:{totalSize:y,mpegVersionId:c,lowSamplingFrequency:s,layer:l,bitrate:b,frequencyIndex:d,sampleRate:T,channel:m,modeExtension:p,copyright:h,original:k,emphasis:w,audioSamplesInFrame:A},bytesAdvanced:1}};var an=r=>{let e=2130706432,t=0;for(;e!==0;)t>>=1,t|=r&e,e>>=8;return t},yt;(function(r){r[r.FrameCount=1]="FrameCount",r[r.FileSize=2]="FileSize",r[r.Toc=4]="Toc",r[r.Quality=8]="Quality"})(yt||(yt={}));var Ot=r=>r===3?1:2;var rr=[48e3,44100,32e3],Gs=[24e3,22050,16e3];var zl="1.65.0",on=`Mediabunny v${zl}`;var he;(function(r){r[r.NON_IDR_SLICE=1]="NON_IDR_SLICE",r[r.SLICE_DPA=2]="SLICE_DPA",r[r.SLICE_DPB=3]="SLICE_DPB",r[r.SLICE_DPC=4]="SLICE_DPC",r[r.IDR=5]="IDR",r[r.SEI=6]="SEI",r[r.SPS=7]="SPS",r[r.PPS=8]="PPS",r[r.AUD=9]="AUD",r[r.SPS_EXT=13]="SPS_EXT"})(he||(he={}));var se;(function(r){r[r.RASL_N=8]="RASL_N",r[r.RASL_R=9]="RASL_R",r[r.BLA_W_LP=16]="BLA_W_LP",r[r.RSV_IRAP_VCL23=23]="RSV_IRAP_VCL23",r[r.VPS_NUT=32]="VPS_NUT",r[r.SPS_NUT=33]="SPS_NUT",r[r.PPS_NUT=34]="PPS_NUT",r[r.AUD_NUT=35]="AUD_NUT",r[r.PREFIX_SEI_NUT=39]="PREFIX_SEI_NUT",r[r.SUFFIX_SEI_NUT=40]="SUFFIX_SEI_NUT"})(se||(se={}));var xr=function*(r){let e=0,t=-1;for(;e<r.length-2;){let i=r.indexOf(0,e);if(i===-1||i>=r.length-2)break;e=i;let n=0;if(e+3<r.length&&r[e+1]===0&&r[e+2]===0&&r[e+3]===1?n=4:r[e+1]===0&&r[e+2]===1&&(n=3),n===0){e++;continue}t!==-1&&e>t&&(yield{offset:t,length:e-t}),t=e+n,e=t}t!==-1&&t<r.length&&(yield{offset:t,length:r.length-t})},wo=function*(r,e){let t=0,i=new DataView(r.buffer,r.byteOffset,r.byteLength);for(;t+e<=r.length;){let n;e===1?n=i.getUint8(t):e===2?n=i.getUint16(t,!1):e===3?n=li(i,t,!1):(g(e===4),n=i.getUint32(t,!1)),t+=e,yield{offset:t,length:n},t+=n}},Nl=(r,e)=>{if(e.description){let n=(ke(e.description)[4]&3)+1;return wo(r,n)}else return xr(r)},ln=r=>r&31,un=r=>{let e=new Uint8Array(r.length),t=r.length,i=0;for(let n=0;n<t;n++)n+2<t&&r[n]===0&&r[n+1]===0&&r[n+2]===3?(e[i++]=0,e[i++]=0,n+=2):e[i++]=r[n];return e.subarray(0,i)};var Tf=new Uint8Array([0,0,0,1]);var bo=(r,e)=>{let t=r.reduce((a,s)=>a+e+s.byteLength,0),i=new Uint8Array(t),n=0;for(let a of r){let s=new DataView(i.buffer,i.byteOffset,i.byteLength);switch(e){case 1:s.setUint8(n,a.byteLength);break;case 2:s.setUint16(n,a.byteLength,!1);break;case 3:io(s,n,a.byteLength,!1);break;case 4:s.setUint32(n,a.byteLength,!1);break}n+=e,i.set(a,n),n+=a.byteLength}return i};var zt=r=>{try{let e=[],t=[],i=[];for(let o of xr(r)){let c=r.subarray(o.offset,o.offset+o.length),l=ln(c[0]);l===he.SPS&&e.length<31?e.push(c):l===he.PPS&&t.length<255?t.push(c):l===he.SPS_EXT&&i.length<255&&i.push(c)}if(e.length===0||t.length===0)return null;let n=e[0],a=nr(n);if(!a)return null;let s=a.profileIdc===100||a.profileIdc===110||a.profileIdc===122||a.profileIdc===144;return{configurationVersion:1,avcProfileIndication:a.profileIdc,profileCompatibility:a.constraintFlags,avcLevelIndication:a.levelIdc,lengthSizeMinusOne:3,sequenceParameterSets:e,pictureParameterSets:t,chromaFormat:s?a.chromaFormatIdc:null,bitDepthLumaMinus8:s?a.bitDepthLumaMinus8:null,bitDepthChromaMinus8:s?a.bitDepthChromaMinus8:null,sequenceParameterSetExt:s?i:null}}catch(e){return H._error("Error building AVC Decoder Configuration Record:",e),null}},To=r=>{let e=[];e.push(r.configurationVersion),e.push(r.avcProfileIndication),e.push(r.profileCompatibility),e.push(r.avcLevelIndication),e.push(252|r.lengthSizeMinusOne&3),e.push(224|r.sequenceParameterSets.length&31);for(let t of r.sequenceParameterSets){let i=t.byteLength;e.push(i>>8),e.push(i&255);for(let n=0;n<i;n++)e.push(t[n])}e.push(r.pictureParameterSets.length);for(let t of r.pictureParameterSets){let i=t.byteLength;e.push(i>>8),e.push(i&255);for(let n=0;n<i;n++)e.push(t[n])}if((r.avcProfileIndication===100||r.avcProfileIndication===110||r.avcProfileIndication===122||r.avcProfileIndication===144)&&r.chromaFormat!==null){g(r.bitDepthLumaMinus8!==null),g(r.bitDepthChromaMinus8!==null),g(r.sequenceParameterSetExt!==null),e.push(252|r.chromaFormat&3),e.push(248|r.bitDepthLumaMinus8&7),e.push(248|r.bitDepthChromaMinus8&7),e.push(r.sequenceParameterSetExt.length);for(let t of r.sequenceParameterSetExt){let i=t.byteLength;e.push(i>>8),e.push(i&255);for(let n=0;n<i;n++)e.push(t[n])}}return new Uint8Array(e)},dn=r=>{try{let e=W(r),t=0,i=e.getUint8(t++),n=e.getUint8(t++),a=e.getUint8(t++),s=e.getUint8(t++),o=e.getUint8(t++)&3,c=e.getUint8(t++)&31,l=[];for(let m=0;m<c;m++){let p=e.getUint16(t,!1);t+=2,l.push(r.subarray(t,t+p)),t+=p}let u=e.getUint8(t++),d=[];for(let m=0;m<u;m++){let p=e.getUint16(t,!1);t+=2,d.push(r.subarray(t,t+p)),t+=p}let f={configurationVersion:i,avcProfileIndication:n,profileCompatibility:a,avcLevelIndication:s,lengthSizeMinusOne:o,sequenceParameterSets:l,pictureParameterSets:d,chromaFormat:null,bitDepthLumaMinus8:null,bitDepthChromaMinus8:null,sequenceParameterSetExt:null};if((n===100||n===110||n===122||n===144)&&t+4<=r.length){let m=e.getUint8(t++)&3,p=e.getUint8(t++)&7,h=e.getUint8(t++)&7,k=e.getUint8(t++);f.chromaFormat=m,f.bitDepthLumaMinus8=p,f.bitDepthChromaMinus8=h;let w=[];for(let S=0;S<k;S++){let b=e.getUint16(t,!1);t+=2,w.push(r.subarray(t,t+b)),t+=b}f.sequenceParameterSetExt=w}return f}catch(e){return H._error("Error deserializing AVC Decoder Configuration Record:",e),null}},So={1:{num:1,den:1},2:{num:12,den:11},3:{num:10,den:11},4:{num:16,den:11},5:{num:40,den:33},6:{num:24,den:11},7:{num:20,den:11},8:{num:32,den:11},9:{num:80,den:33},10:{num:18,den:11},11:{num:15,den:11},12:{num:64,den:33},13:{num:160,den:99},14:{num:4,den:3},15:{num:3,den:2},16:{num:2,den:1}},nr=r=>{try{let e=un(r),t=new q(e);if(t.skipBits(1),t.skipBits(2),t.readBits(5)!==7)return null;let n=t.readAlignedByte(),a=t.readAlignedByte(),s=t.readAlignedByte();F(t);let o=1,c=0,l=0,u=0;if((n===100||n===110||n===122||n===244||n===44||n===83||n===86||n===118||n===128)&&(o=F(t),o===3&&(u=t.readBits(1)),c=F(t),l=F(t),t.skipBits(1),t.readBits(1))){for(let j=0;j<(o!==3?8:12);j++)if(t.readBits(1)){let we=j<6?16:64,Me=8,de=8;for(let vt=0;vt<we;vt++){if(de!==0){let Xt=nt(t);de=(Me+Xt+256)%256}Me=de===0?Me:de}}}F(t);let d=F(t);if(d===0)F(t);else if(d===1){t.skipBits(1),nt(t),nt(t);let z=F(t);for(let j=0;j<z;j++)nt(t)}F(t),t.skipBits(1);let f=F(t),m=F(t),p=16*(f+1),h=16*(m+1),k=p,w=h,S=t.readBits(1);if(S||t.skipBits(1),t.skipBits(1),t.readBits(1)){let z=F(t),j=F(t),ee=F(t),we=F(t),Me,de;if((u===0?o:0)===0)Me=1,de=2-S;else{let Xt=o===3?1:2,Gi=o===1?2:1;Me=Xt,de=Gi*(2-S)}k-=Me*(z+j),w-=de*(ee+we)}if(k<=0||w<=0)return null;let T=2,y=2,A=2,x=0,C={num:1,den:1},E=null,I=null,R=null,D=null,O=t.pos;if(t.readBits(1)){if(t.readBits(1)){let Xt=t.readBits(8);if(Xt===255)C={num:t.readBits(16),den:t.readBits(16)};else{let Gi=So[Xt];Gi&&(C=Gi)}}t.readBits(1)&&t.skipBits(1),t.readBits(1)&&(t.skipBits(3),x=t.readBits(1),t.readBits(1)&&(T=t.readBits(8),y=t.readBits(8),A=t.readBits(8))),t.readBits(1)&&(F(t),F(t)),t.readBits(1)&&(t.skipBits(32),t.skipBits(32),t.skipBits(1));let de=t.readBits(1);de&&po(t);let vt=t.readBits(1);vt&&po(t),(de||vt)&&t.skipBits(1),t.skipBits(1),R=t.pos,D=t.readBits(1),D&&(t.skipBits(1),F(t),F(t),F(t),F(t),E=Math.min(F(t),16),I=Math.min(F(t),16))}if(E===null){g(I===null);let z=a&16;if((n===44||n===86||n===100||n===110||n===122||n===244)&&z)E=0,I=0;else{let j=f+1,ee=m+1,we=(2-S)*ee,Me=Qs.find(vt=>vt.level>=s)??$(Qs),de=Math.min(Math.floor(Me.maxDpbMbs/(j*we)),16);E=de,I=de}}return g(I!==null),{emulationUnpreventedBytes:e,profileIdc:n,constraintFlags:a,levelIdc:s,frameMbsOnlyFlag:S,chromaFormatIdc:o,bitDepthLumaMinus8:c,bitDepthChromaMinus8:l,codedWidth:p,codedHeight:h,displayWidth:k,displayHeight:w,pixelAspectRatio:C,colourPrimaries:T,matrixCoefficients:A,transferCharacteristics:y,fullRangeFlag:x,numReorderFrames:E,maxDecFrameBuffering:I,vuiParametersFlagBitOffset:O,bitstreamRestrictionFlagBitOffset:R,bitstreamRestrictionFlag:D}}catch(e){return H._error("Error parsing AVC SPS:",e),null}},po=r=>{let e=F(r);r.skipBits(4),r.skipBits(4);for(let t=0;t<=e;t++)F(r),F(r),r.skipBits(1);r.skipBits(5),r.skipBits(5),r.skipBits(5),r.skipBits(5)};var Vl=(r,e)=>{if(e.description){let n=(ke(e.description)[21]&3)+1;return wo(r,n)}else return xr(r)},ki=r=>r>>1&63,sr=r=>{try{let e=new q(un(r));e.skipBits(16),e.readBits(4);let t=e.readBits(3),i=e.readBits(1),{general_profile_space:n,general_tier_flag:a,general_profile_idc:s,general_profile_compatibility_flags:o,general_constraint_indicator_flags:c,general_level_idc:l}=Ll(e,t);F(e);let u=F(e),d=0;u===3&&(d=e.readBits(1));let f=F(e),m=F(e),p=f,h=m;if(e.readBits(1)){let D=F(e),O=F(e),V=F(e),z=F(e),j=1,ee=1,we=d===0?u:0;we===1?(j=2,ee=2):we===2&&(j=2,ee=1),p-=(D+O)*j,h-=(V+z)*ee}if(p<=0||h<=0)return null;let k=F(e),w=F(e);F(e);let b=e.readBits(1)?0:t,T=0;for(let D=b;D<=t;D++)F(e),T=F(e),F(e);F(e),F(e),F(e),F(e),F(e),F(e),e.readBits(1)&&e.readBits(1)&&Hl(e),e.skipBits(1),e.skipBits(1),e.readBits(1)&&(e.skipBits(4),e.skipBits(4),F(e),F(e),e.skipBits(1));let y=F(e);if(Wl(e,y),e.readBits(1)){let D=F(e);for(let O=0;O<D;O++)F(e),e.skipBits(1)}e.skipBits(1),e.skipBits(1);let A=2,x=2,C=2,E=0,I=0,R={num:1,den:1};if(e.readBits(1)){let D=Kl(e,t);R=D.pixelAspectRatio,A=D.colourPrimaries,x=D.transferCharacteristics,C=D.matrixCoefficients,E=D.fullRangeFlag,I=D.minSpatialSegmentationIdc}return{displayWidth:p,displayHeight:h,pixelAspectRatio:R,colourPrimaries:A,transferCharacteristics:x,matrixCoefficients:C,fullRangeFlag:E,maxDecFrameBuffering:Math.min(T+1,16),spsMaxSubLayersMinus1:t,spsTemporalIdNestingFlag:i,generalProfileSpace:n,generalTierFlag:a,generalProfileIdc:s,generalProfileCompatibilityFlags:o,generalConstraintIndicatorFlags:c,generalLevelIdc:l,chromaFormatIdc:u,bitDepthLumaMinus8:k,bitDepthChromaMinus8:w,minSpatialSegmentationIdc:I}}catch(e){return H._error("Error parsing HEVC SPS:",e),null}},Nt=r=>{try{let e=[],t=[],i=[],n=[];for(let u of xr(r)){let d=r.subarray(u.offset,u.offset+u.length),f=ki(d[0]);f===se.VPS_NUT&&e.length<65535?e.push(d):f===se.SPS_NUT&&t.length<65535?t.push(d):f===se.PPS_NUT&&i.length<65535?i.push(d):(f===se.PREFIX_SEI_NUT||f===se.SUFFIX_SEI_NUT)&&n.length<65535&&n.push(d)}if(t.length===0||i.length===0)return null;let s=sr(t[0]);if(!s)return null;let o=0;if(i.length>0){let u=i[0],d=new q(un(u));d.skipBits(16),F(d),F(d),d.skipBits(1),d.skipBits(1),d.skipBits(3),d.skipBits(1),d.skipBits(1),F(d),F(d),nt(d),d.skipBits(1),d.skipBits(1),d.readBits(1)&&F(d),nt(d),nt(d),d.skipBits(1),d.skipBits(1),d.skipBits(1),d.skipBits(1);let f=d.readBits(1),m=d.readBits(1);!f&&!m?o=0:f&&!m?o=2:!f&&m?o=3:o=0}let c=[...e.length?[{arrayCompleteness:1,nalUnitType:se.VPS_NUT,nalUnits:e}]:[],...t.length?[{arrayCompleteness:1,nalUnitType:se.SPS_NUT,nalUnits:t}]:[],...i.length?[{arrayCompleteness:1,nalUnitType:se.PPS_NUT,nalUnits:i}]:[],...n.length?[{arrayCompleteness:1,nalUnitType:ki(n[0][0]),nalUnits:n}]:[]];return{configurationVersion:1,generalProfileSpace:s.generalProfileSpace,generalTierFlag:s.generalTierFlag,generalProfileIdc:s.generalProfileIdc,generalProfileCompatibilityFlags:s.generalProfileCompatibilityFlags,generalConstraintIndicatorFlags:s.generalConstraintIndicatorFlags,generalLevelIdc:s.generalLevelIdc,minSpatialSegmentationIdc:s.minSpatialSegmentationIdc,parallelismType:o,chromaFormatIdc:s.chromaFormatIdc,bitDepthLumaMinus8:s.bitDepthLumaMinus8,bitDepthChromaMinus8:s.bitDepthChromaMinus8,avgFrameRate:0,constantFrameRate:0,numTemporalLayers:s.spsMaxSubLayersMinus1+1,temporalIdNested:s.spsTemporalIdNestingFlag,lengthSizeMinusOne:3,arrays:c}}catch(e){return H._error("Error building HEVC Decoder Configuration Record:",e),null}},Ll=(r,e)=>{let t=r.readBits(2),i=r.readBits(1),n=r.readBits(5),a=0;for(let u=0;u<32;u++)a=a<<1|r.readBits(1);let s=new Uint8Array(6);for(let u=0;u<6;u++)s[u]=r.readBits(8);let o=r.readBits(8),c=[],l=[];for(let u=0;u<e;u++)c.push(r.readBits(1)),l.push(r.readBits(1));if(e>0)for(let u=e;u<8;u++)r.skipBits(2);for(let u=0;u<e;u++)c[u]&&r.skipBits(88),l[u]&&r.skipBits(8);return{general_profile_space:t,general_tier_flag:i,general_profile_idc:n,general_profile_compatibility_flags:a,general_constraint_indicator_flags:s,general_level_idc:o}},Hl=r=>{for(let e=0;e<4;e++)for(let t=0;t<(e===3?2:6);t++)if(!r.readBits(1))F(r);else{let n=Math.min(64,1<<4+(e<<1));e>1&&nt(r);for(let a=0;a<n;a++)nt(r)}},Wl=(r,e)=>{let t=[];for(let i=0;i<e;i++)t[i]=ql(r,i,e,t)},ql=(r,e,t,i)=>{let n=0,a=0,s=0;if(e!==0&&(a=r.readBits(1)),a){if(e===t){let c=F(r);s=e-(c+1)}else s=e-1;r.readBits(1),F(r);let o=i[s]??0;for(let c=0;c<=o;c++)r.readBits(1)||r.readBits(1);n=i[s]}else{let o=F(r),c=F(r);for(let l=0;l<o;l++)F(r),r.readBits(1);for(let l=0;l<c;l++)F(r),r.readBits(1);n=o+c}return n},Kl=(r,e)=>{let t=2,i=2,n=2,a=0,s=0,o={num:1,den:1};if(r.readBits(1)){let c=r.readBits(8);if(c===255)o={num:r.readBits(16),den:r.readBits(16)};else{let l=So[c];l&&(o=l)}}return r.readBits(1)&&r.readBits(1),r.readBits(1)&&(r.readBits(3),a=r.readBits(1),r.readBits(1)&&(t=r.readBits(8),i=r.readBits(8),n=r.readBits(8))),r.readBits(1)&&(F(r),F(r)),r.readBits(1),r.readBits(1),r.readBits(1),r.readBits(1)&&(F(r),F(r),F(r),F(r)),r.readBits(1)&&(r.readBits(32),r.readBits(32),r.readBits(1)&&F(r),r.readBits(1)&&jl(r,!0,e)),r.readBits(1)&&(r.readBits(1),r.readBits(1),r.readBits(1),s=F(r),F(r),F(r),F(r),F(r)),{pixelAspectRatio:o,colourPrimaries:t,transferCharacteristics:i,matrixCoefficients:n,fullRangeFlag:a,minSpatialSegmentationIdc:s}},jl=(r,e,t)=>{let i=!1,n=!1,a=!1;e&&(i=r.readBits(1)===1,n=r.readBits(1)===1,(i||n)&&(a=r.readBits(1)===1,a&&(r.readBits(8),r.readBits(5),r.readBits(1),r.readBits(5)),r.readBits(4),r.readBits(4),a&&r.readBits(4),r.readBits(5),r.readBits(5),r.readBits(5)));for(let s=0;s<=t;s++){let o=r.readBits(1)===1,c=!0;o||(c=r.readBits(1)===1);let l=!1;c?F(r):l=r.readBits(1)===1;let u=1;l||(u=F(r)+1),i&&go(r,u,a),n&&go(r,u,a)}},go=(r,e,t)=>{for(let i=0;i<e;i++)F(r),F(r),t&&(F(r),F(r)),r.readBits(1)},Ao=r=>{let e=[];e.push(r.configurationVersion),e.push((r.generalProfileSpace&3)<<6|(r.generalTierFlag&1)<<5|r.generalProfileIdc&31),e.push(r.generalProfileCompatibilityFlags>>>24&255),e.push(r.generalProfileCompatibilityFlags>>>16&255),e.push(r.generalProfileCompatibilityFlags>>>8&255),e.push(r.generalProfileCompatibilityFlags&255),e.push(...r.generalConstraintIndicatorFlags),e.push(r.generalLevelIdc&255),e.push(240|r.minSpatialSegmentationIdc>>8&15),e.push(r.minSpatialSegmentationIdc&255),e.push(252|r.parallelismType&3),e.push(252|r.chromaFormatIdc&3),e.push(248|r.bitDepthLumaMinus8&7),e.push(248|r.bitDepthChromaMinus8&7),e.push(r.avgFrameRate>>8&255),e.push(r.avgFrameRate&255),e.push((r.constantFrameRate&3)<<6|(r.numTemporalLayers&7)<<3|(r.temporalIdNested&1)<<2|r.lengthSizeMinusOne&3),e.push(r.arrays.length&255);for(let t of r.arrays){e.push((t.arrayCompleteness&1)<<7|0|t.nalUnitType&63),e.push(t.nalUnits.length>>8&255),e.push(t.nalUnits.length&255);for(let i of t.nalUnits){e.push(i.length>>8&255),e.push(i.length&255);for(let n=0;n<i.length;n++)e.push(i[n])}}return new Uint8Array(e)},fn=r=>{try{let e=W(r),t=0,i=e.getUint8(t++),n=e.getUint8(t++),a=n>>6&3,s=n>>5&1,o=n&31,c=e.getUint32(t,!1);t+=4;let l=r.subarray(t,t+6);t+=6;let u=e.getUint8(t++),d=(e.getUint8(t++)&15)<<8|e.getUint8(t++),f=e.getUint8(t++)&3,m=e.getUint8(t++)&3,p=e.getUint8(t++)&7,h=e.getUint8(t++)&7,k=e.getUint16(t,!1);t+=2;let w=e.getUint8(t++),S=w>>6&3,b=w>>3&7,T=w>>2&1,y=w&3,A=e.getUint8(t++),x=[];for(let C=0;C<A;C++){let E=e.getUint8(t++),I=E>>7&1,R=E&63,D=e.getUint16(t,!1);t+=2;let O=[];for(let V=0;V<D;V++){let z=e.getUint16(t,!1);t+=2,O.push(r.subarray(t,t+z)),t+=z}x.push({arrayCompleteness:I,nalUnitType:R,nalUnits:O})}return{configurationVersion:i,generalProfileSpace:a,generalTierFlag:s,generalProfileIdc:o,generalProfileCompatibilityFlags:c,generalConstraintIndicatorFlags:l,generalLevelIdc:u,minSpatialSegmentationIdc:d,parallelismType:f,chromaFormatIdc:m,bitDepthLumaMinus8:p,bitDepthChromaMinus8:h,avgFrameRate:k,constantFrameRate:S,numTemporalLayers:b,temporalIdNested:T,lengthSizeMinusOne:y,arrays:x}}catch(e){return H._error("Error deserializing HEVC Decoder Configuration Record:",e),null}},ko;(function(r){r[r.audAllowed=0]="audAllowed",r[r.beforeFirstVcl=1]="beforeFirstVcl",r[r.afterFirstVcl=2]="afterFirstVcl",r[r.eoBitstreamAllowed=3]="eoBitstreamAllowed",r[r.noMoreDataAllowed=4]="noMoreDataAllowed"})(ko||(ko={}));var Gl={1:{colourPrimaries:5,transferCharacteristics:6,matrixCoefficients:5},2:{colourPrimaries:1,transferCharacteristics:1,matrixCoefficients:1},3:{colourPrimaries:6,transferCharacteristics:6,matrixCoefficients:6},4:{colourPrimaries:7,transferCharacteristics:7,matrixCoefficients:7},5:{colourPrimaries:9,transferCharacteristics:14,matrixCoefficients:9},7:{colourPrimaries:1,transferCharacteristics:13,matrixCoefficients:0}},hn=r=>{let e=new q(r);if(e.readBits(2)!==2)return null;let i=e.readBits(1),a=(e.readBits(1)<<1)+i;if(a===3&&e.skipBits(1),e.readBits(1)===1||e.readBits(1)!==0||(e.skipBits(2),e.readBits(24)!==4817730))return null;let l=8;a>=2&&(l=e.readBits(1)?12:10);let u=e.readBits(3),d=0,f=0;if(u!==7)if(f=e.readBits(1),a===1||a===3){let C=e.readBits(1),E=e.readBits(1);d=!C&&!E?3:C&&!E?2:1,e.skipBits(1)}else d=1;else d=3,f=1;let m=e.readBits(16),p=e.readBits(16),h=m+1,k=p+1,w=h*k,S=$(ir).level;for(let x of ir)if(w<=x.maxPictureSize){S=x.level;break}let b=Gl[u],T=b?.colourPrimaries??2,y=b?.transferCharacteristics??2,A=b?.matrixCoefficients??2;return{profile:a,level:S,bitDepth:l,chromaSubsampling:d,videoFullRangeFlag:f,colourPrimaries:T,transferCharacteristics:y,matrixCoefficients:A}},xo=r=>r.colourPrimaries!==2||r.transferCharacteristics!==2||r.matrixCoefficients!==2,Co=function*(r){let e=new q(r),t=()=>{let i=0;for(let n=0;n<8;n++){let a=e.readAlignedByte();if(i+=(a&127)*2**(n*7),!(a&128))break;if(n===7&&a&128)return null}return i>2**32-1?null:i};for(;e.getBitsLeft()>=8;){e.skipBits(1);let i=e.readBits(4),n=e.readBits(1),a=e.readBits(1);e.skipBits(1),n&&e.skipBits(8);let s;if(a){let o=t();if(o===null)return;s=o}else s=Math.floor(e.getBitsLeft()/8);g(e.pos%8===0),yield{type:i,data:r.subarray(e.pos/8,e.pos/8+s)},e.skipBits(s*8)}},yi=r=>{for(let{type:e,data:t}of Co(r)){if(e!==1)continue;let i=new q(t),n=i.readBits(3),a=i.readBits(1),s=i.readBits(1),o=0,c=0,l=0;if(s)o=i.readBits(5);else{let I=i.readBits(1),R=0;if(I){if(i.skipBits(32),i.skipBits(32),i.readBits(1)){let z=0;for(;z<32&&!i.readBits(1);)z++;z<32&&i.skipBits(z)}R=i.readBits(1),R&&(l=i.readBits(5),i.skipBits(32),i.skipBits(5),i.skipBits(5))}let D=i.readBits(1),O=i.readBits(5);for(let V=0;V<=O;V++){i.skipBits(12);let z=i.readBits(5);if(V===0&&(o=z),z>7){let j=i.readBits(1);V===0&&(c=j)}if(R&&i.readBits(1)){let ee=l+1;i.skipBits(ee),i.skipBits(ee),i.skipBits(1)}D&&i.readBits(1)&&i.skipBits(4)}}let u=i.readBits(4),d=i.readBits(4),f=u+1;i.skipBits(f);let m=d+1;i.skipBits(m);let p=0;if(s?p=0:p=i.readBits(1),p&&(i.skipBits(4),i.skipBits(3)),i.skipBits(1),i.skipBits(1),i.skipBits(1),!s){i.skipBits(1),i.skipBits(1),i.skipBits(1),i.skipBits(1);let I=i.readBits(1);I&&(i.skipBits(1),i.skipBits(1));let R=i.readBits(1),D=0;R?D=2:D=i.readBits(1),D>0&&(i.readBits(1)||i.skipBits(1)),I&&i.skipBits(3)}i.skipBits(1),i.skipBits(1),i.skipBits(1);let h=i.readBits(1),k=8;n===2&&h?k=i.readBits(1)?12:10:n<=2&&(k=h?10:8);let w=0;n!==1&&(w=i.readBits(1));let S=2,b=2,T=2;i.readBits(1)&&(S=i.readBits(8),b=i.readBits(8),T=i.readBits(8));let A=0,x=1,C=1,E=0;return w?A=i.readBits(1):S===1&&b===13&&T===0?(A=1,x=0,C=0):(A=i.readBits(1),n===0?(x=1,C=1):n===1?(x=0,C=0):k===12?(x=i.readBits(1),C=x?i.readBits(1):0):(x=1,C=0),x&&C&&(E=i.readBits(2))),{profile:n,level:o,tier:c,bitDepth:k,monochrome:w,chromaSubsamplingX:x,chromaSubsamplingY:C,chromaSamplePosition:E,videoFullRangeFlag:A,colourPrimaries:S,transferCharacteristics:b,matrixCoefficients:T}}return null},mn=r=>r.colourPrimaries!==2||r.transferCharacteristics!==2||r.matrixCoefficients!==2,pn=r=>{if(r.length<36)return null;let t=W(r);return t.getUint32(4)!==1768124518||t.getUint16(8)<28?null:{fullRange:!1,colourPrimaries:t.getUint8(22),transferCharacteristics:t.getUint8(23),matrixCoefficients:t.getUint8(24)}},gn=r=>{if(r.byteLength<19)throw new Error("Invalid Opus identification header: too short.");let e=W(r),t=e.getUint8(9),i=e.getUint16(10,!0),n=e.getUint32(12,!0),a=e.getInt16(16,!0),s=e.getUint8(18),o=null;return s&&(o=r.subarray(19,21+t)),{outputChannelCount:t,preSkip:i,inputSampleRate:n,outputGain:a,channelMappingFamily:s,channelMappingTable:o}},Ql=[480,960,1920,2880,480,960,1920,2880,480,960,1920,2880,480,960,480,960,120,240,480,960,120,240,480,960,120,240,480,960,120,240,480,960],kn=r=>{let e=r[0]>>3,t=r[0]&3,i;return t===0?i=1:t===1||t===2?i=2:i=r[1]&63,{durationInSamples:Ql[e]*i}},Po=r=>{if(r.length<7)throw new Error("Setup header is too short.");if(r[0]!==5)throw new Error("Wrong packet type in Setup header.");if(String.fromCharCode(...r.slice(1,7))!=="vorbis")throw new Error("Invalid packet signature in Setup header.");let t=r.length,i=new Uint8Array(t);for(let d=0;d<t;d++)i[d]=r[t-1-d];let n=new q(i),a=0;for(;n.getBitsLeft()>97;)if(n.readBits(1)===1){a=n.pos;break}if(a===0)throw new Error("Invalid Setup header: framing bit not found.");let s=0,o=!1,c=0;for(;n.getBitsLeft()>=97;){let d=n.pos,f=n.readBits(8),m=n.readBits(16),p=n.readBits(16);if(f>63||m!==0||p!==0){n.pos=d;break}if(n.skipBits(1),s++,s>64)break;n.clone().readBits(6)+1===s&&(o=!0,c=s)}if(!o)throw new Error("Invalid Setup header: mode header not found.");if(c>63)throw new Error(`Unsupported mode count: ${c}.`);let l=c;n.pos=0,n.skipBits(a);let u=Array(l).fill(0);for(let d=l-1;d>=0;d--)n.skipBits(40),u[d]=n.readBits(1);return{modeBlockflags:u}},yn=(r,e,t)=>{switch(r){case"avc":{for(let i of Nl(t,e)){let n=t[i.offset],a=ln(n);if(a>=he.NON_IDR_SLICE&&a<=he.SLICE_DPC)return"delta";if(a===he.IDR)return"key";if(a===he.SEI&&!Ls()){let s=t.subarray(i.offset,i.offset+i.length),o=un(s),c=1;do{let l=0;for(;;){let f=o[c++];if(f===void 0||(l+=f,f<255))break}let u=0;for(;;){let f=o[c++];if(f===void 0||(u+=f,f<255))break}if(l===6){let f=new q(o);f.pos=8*c;let m=-1;try{m=F(f)}catch{}let p=f.readBits(1);if(m===0&&p===1)return"key"}c+=u}while(c<o.length-1)}}return"delta"}case"hevc":{for(let i of Vl(t,e)){let n=ki(t[i.offset]);if(n<se.BLA_W_LP)return"delta";if(n<=se.RSV_IRAP_VCL23)return"key"}return"delta"}case"vp8":return(t[0]&1)===0?"key":"delta";case"vp9":{let i=new q(t);if(i.readBits(2)!==2)return null;let n=i.readBits(1);return(i.readBits(1)<<1)+n===3&&i.skipBits(1),i.readBits(1)?null:i.readBits(1)===0?"key":"delta"}case"av1":{let i=!1;for(let{type:n,data:a}of Co(t))if(n===1){let s=new q(a);s.skipBits(4),i=!!s.readBits(1)}else if(n===3||n===6||n===7){if(i)return"key";let s=new q(a);return s.readBits(1)?null:s.readBits(2)===0?"key":"delta"}return null}case"prores":return"key";default:_e(r),g(!1)}},wn=(r,e)=>r==="truehd"?(e.byteLength>=8?W(e).getUint32(4):null)===4168249274?"key":"delta":"key",Ut;(function(r){r[r.STREAMINFO=0]="STREAMINFO",r[r.VORBIS_COMMENT=4]="VORBIS_COMMENT",r[r.PICTURE=6]="PICTURE"})(Ut||(Ut={}));var wi=(r,e)=>{let t=W(r),i=0;if(r.length<4)return;let n=t.getUint32(i,!0);i+=4;let a=ie.decode(r.subarray(i,i+n));if(i+=n,n>0&&(e.raw??={},e.raw.vendor??=a),i+4>r.length)return;let s=t.getUint32(i,!0);i+=4;for(let o=0;o<s&&!(i+4>r.length);o++){let c=t.getUint32(i,!0);i+=4;let l=ie.decode(r.subarray(i,i+c));i+=c;let u=l.indexOf("=");if(u===-1)continue;let d=l.slice(0,u).toUpperCase(),f=l.slice(u+1);switch(e.raw??={},Array.isArray(e.raw[d])?e.raw[d].push(f):typeof e.raw[d]=="string"?e.raw[d]=[e.raw[d],f]:e.raw[d]??=f,d){case"TITLE":e.title??=f;break;case"DESCRIPTION":e.description??=f;break;case"ARTIST":e.artist??=f;break;case"ALBUM":e.album??=f;break;case"ALBUMARTIST":e.albumArtist??=f;break;case"COMMENT":e.comment??=f;break;case"LYRICS":e.lyrics??=f;break;case"TRACKNUMBER":{let m=f.split("/"),p=Number.parseInt(m[0],10),h=m[1]&&Number.parseInt(m[1],10);Number.isInteger(p)&&p>0&&(e.trackNumber??=p),h&&Number.isInteger(h)&&h>0&&(e.tracksTotal??=h)}break;case"TRACKTOTAL":{let m=Number.parseInt(f,10);Number.isInteger(m)&&m>0&&(e.tracksTotal??=m)}break;case"DISCNUMBER":{let m=f.split("/"),p=Number.parseInt(m[0],10),h=m[1]&&Number.parseInt(m[1],10);Number.isInteger(p)&&p>0&&(e.discNumber??=p),h&&Number.isInteger(h)&&h>0&&(e.discsTotal??=h)}break;case"DISCTOTAL":{let m=Number.parseInt(f,10);Number.isInteger(m)&&m>0&&(e.discsTotal??=m)}break;case"DATE":{let m=new Date(f);Number.isNaN(m.getTime())||(e.date??=m)}break;case"BPM":{let m=Number.parseInt(f,10);Number.isInteger(m)&&m>0&&(e.beatsPerMinute??=m)}break;case"GENRE":e.genre??=f;break;case"METADATA_BLOCK_PICTURE":try{let m=di(f),p=W(m),h=p.getUint32(0,!1),k=p.getUint32(4,!1),w=ie.decode(m.subarray(8,8+k)),S=p.getUint32(8+k,!1),b=ie.decode(m.subarray(12+k,12+k+S)),T=p.getUint32(k+S+28),y=m.subarray(k+S+32,k+S+32+T);e.images??=[],e.images.push({data:y,mimeType:w,kind:h===3?"coverFront":h===4?"coverBack":"unknown",name:void 0,description:b||void 0})}catch{}break}}};var bi=[2,1,2,3,3,4,4,5],bn=r=>{if(r.length<7||r[0]!==11||r[1]!==119)return null;let e=new q(r);e.skipBits(16),e.skipBits(16);let t=e.readBits(2);if(t===3)return null;let i=e.readBits(6),n=e.readBits(5);if(n>8)return null;let a=e.readBits(3),s=e.readBits(3);(s&1)!==0&&s!==1&&e.skipBits(2),(s&4)!==0&&e.skipBits(2),s===2&&e.skipBits(2);let o=e.readBits(1),c=Math.floor(i/2);return{fscod:t,bsid:n,bsmod:a,acmod:s,lfeon:o,bitRateCode:c}},Eo=[128,138,192,128,140,192,160,174,240,160,176,240,192,208,288,192,210,288,224,242,336,224,244,336,256,278,384,256,280,384,320,348,480,320,350,480,384,416,288*2,384,418,288*2,448,486,336*2,448,488,336*2,256*2,278*2,384*2,256*2,279*2,384*2,320*2,348*2,480*2,320*2,349*2,480*2,384*2,417*2,576*2,384*2,418*2,576*2,448*2,487*2,672*2,448*2,488*2,672*2,512*2,557*2,768*2,512*2,558*2,768*2,640*2,696*2,960*2,640*2,697*2,960*2,768*2,835*2,1152*2,768*2,836*2,1152*2,896*2,975*2,1344*2,896*2,976*2,1344*2,1024*2,1114*2,1536*2,1024*2,1115*2,1536*2,1152*2,1253*2,1728*2,1152*2,1254*2,1728*2,1280*2,1393*2,1920*2,1280*2,1394*2,1920*2],_o=1536,Sf=new Uint8Array([5,4,65,67,45,51]),Af=new Uint8Array([5,4,69,65,67,51]),Xs=[1,2,3,6],Tn=r=>{if(r.length<6||r[0]!==11||r[1]!==119)return null;let e=new q(r);e.skipBits(16);let t=e.readBits(2);if(e.skipBits(3),t!==0&&t!==2)return null;let i=e.readBits(11),n=e.readBits(2),a=0,s;n===3?(a=e.readBits(2),s=3):s=e.readBits(2);let o=e.readBits(3),c=e.readBits(1),l=e.readBits(5);if(l<11||l>16)return null;let u=Xs[s],d;return n<3?d=rr[n]/1e3:d=Gs[a]/1e3,{dataRate:Math.round((i+1)*d/(u*16)),substreams:[{fscod:n,fscod2:a,bsid:l,bsmod:0,acmod:o,lfeon:c,numDepSub:0,chanLoc:0}]}},Io=r=>{if(r.length<2)return null;let e=new q(r),t=e.readBits(13),i=e.readBits(3),n=[];for(let a=0;a<=i&&!(Math.ceil(e.pos/8)+3>r.length);a++){let s=e.readBits(2),o=e.readBits(5);e.skipBits(1),e.skipBits(1);let c=e.readBits(3),l=e.readBits(3),u=e.readBits(1);e.skipBits(3);let d=e.readBits(4),f=0;d>0?f=e.readBits(9):e.skipBits(1),n.push({fscod:s,fscod2:null,bsid:o,bsmod:c,acmod:l,lfeon:u,numDepSub:d,chanLoc:f})}return n.length===0?null:{dataRate:t,substreams:n}},Sn=r=>{let e=r.substreams[0];return g(e),e.fscod<3?rr[e.fscod]:e.fscod2!==null&&e.fscod2<3?Gs[e.fscod2]:null},An=r=>{let e=r.substreams[0];g(e);let t=bi[e.acmod]+e.lfeon;if(e.numDepSub>0){let i=[2,2,1,1,2,2,2,1,1];for(let n=0;n<9;n++)e.chanLoc&1<<8-n&&(t+=i[n])}return t};var Xl=1683496997,Ti=18,xn=10,vo=4096,yo=32,Cn=20,$l=8,Yl=[0,8e3,16e3,32e3,0,0,11025,22050,44100,0,0,12e3,24e3,48e3,96e3,192e3],Zl=[32e3,56e3,64e3,96e3,112e3,128e3,192e3,224e3,256e3,32e4,384e3,448e3,512e3,576e3,64e4,768e3,96e4,1024e3,1152e3,128e4,1344e3,1408e3,1411200,1472e3,1536e3,192e4,2048e3,3072e3,384e4,0,0,0],Jl=[16,16,20,20,0,24,24,0],cn=[1,2,2,2,2,3,3,4,4,5,6,6,6,7,8,8],eu=[1,2,2,2,2,3,18,19,6,7,518,323,83,519,582,535],tu=8,ru=44646,iu=[32e3,44100,48e3,0],nu=[8e3,16e3,32e3,64e3,128e3,22050,44100,88200,176400,352800,12e3,24e3,48e3,96e3,192e3,384e3],Ro=[512,1024,2048,4096],Si=r=>{let e=$s(r),t=W(r),i=e?Math.ceil(e.frameSize/4)*4:0,n=null;for(;i+4<=r.length&&t.getUint32(i)===Xl;){let s=Ai(r.subarray(i));if(!s)break;n??=s,i+=s.frameSize}if(e)return{frameSize:n?i:e.frameSize,sampleRate:e.sampleRate,numberOfChannels:e.numberOfChannels,sampleCount:e.sampleCount,channelLayout:e.channelLayout,pcmResolution:e.pcmResolution,bitRate:e.bitRate,core:e,hasExtensions:n!==null};if(!n?.asset)return null;let{asset:a}=n;return{frameSize:i,sampleRate:a.sampleRate,numberOfChannels:a.numberOfChannels,sampleCount:a.sampleCount,channelLayout:a.channelLayout,pcmResolution:a.pcmResolution,bitRate:0,core:null,hasExtensions:!0}},Pn=r=>{let e=Si(r);return e?.core?e.hasExtensions?"dtsh":"dtsc":null},$s=r=>{if(r.length<Ti||r[0]!==127||r[1]!==254||r[2]!==128||r[3]!==1)return null;let e=new q(r);if(e.skipBits(32),e.skipBits(1),e.readBits(5)!==yo-1)return null;let t=e.readBits(1),i=e.readBits(7)+1;if(i%$l!==0)return null;let n=e.readBits(14)+1;if(n<96)return null;let a=e.readBits(6);if(a>=cn.length)return null;let s=Yl[e.readBits(4)];if(s===0)return null;let o=Zl[e.readBits(5)];if(e.readBits(1)!==0)return null;e.skipBits(4),e.skipBits(5);let c=e.readBits(2);if(c===3)return null;e.skipBits(1),t&&e.skipBits(16),e.skipBits(7);let l=Jl[e.readBits(3)];if(l===0)return null;let u=c!==0;return{frameSize:n,sampleRate:s,numberOfChannels:cn[a]+(u?1:0),sampleCount:i*yo,channelLayout:eu[a]|(u?tu:0),amode:a,lfePresent:u,bitRate:o,pcmResolution:l}},Ai=r=>{if(r.length<xn||r[0]!==100||r[1]!==88||r[2]!==32||r[3]!==37)return null;let e=new q(r);e.skipBits(32),e.skipBits(8);let t=e.readBits(2),i=e.readBits(1),n=8+4*i,a=16+4*i;e.skipBits(n);let s=e.readBits(a)+1,o={frameSize:s,asset:null};if(!e.readBits(1))return o;let c=iu[e.readBits(2)],l=512*(e.readBits(3)+1);e.readBits(1)&&e.skipBits(36);let u=e.readBits(3)+1,d=e.readBits(3)+1,f=[];for(let w=0;w<u;w++)f.push(e.readBits(t+1));for(let w of f)e.skipBits(8*tn(w));if(e.readBits(1)){e.skipBits(2);let w=e.readBits(2)+1<<2,S=e.readBits(2)+1;e.skipBits(S*w)}for(let w=0;w<d;w++)e.skipBits(a);e.skipBits(9),e.skipBits(3),e.readBits(1)&&e.skipBits(4),e.readBits(1)&&e.skipBits(24),e.readBits(1)&&e.skipBits(8*(e.readBits(10)+1));let m=e.readBits(5)+1,p=nu[e.readBits(4)],h=e.readBits(8)+1,k=0;if(e.readBits(1)&&(h>2&&e.skipBits(1),h>6&&e.skipBits(1),e.readBits(1))){let w=e.readBits(2)+1<<2;k=e.readBits(w)}return c===0||e.getBitsLeft()<0?o:{frameSize:s,asset:{sampleRate:p,numberOfChannels:h,sampleCount:Math.round(l*p/c),channelLayout:k,pcmResolution:m}}},Bo=r=>{if(r.length<Cn)return null;let e=W(r),t=e.getUint32(0);if(t===0)return null;let i=new q(r);i.seekToByte(13);let n=i.readBits(2);i.skipBits(5);let a=i.readBits(1),s=i.readBits(6);i.skipBits(14),i.skipBits(1),i.skipBits(3);let o=i.readBits(16),c=null;return o!==0?c=su(o):s<cn.length&&(c=cn[s]+a),{sampleRate:t,maxBitrate:e.getUint32(4),avgBitrate:e.getUint32(8),pcmSampleDepth:r[12],sampleCount:Ro[n],channelLayout:o,numberOfChannels:c}},Fo=r=>{let e=new Uint8Array(Cn),t=W(e);t.setUint32(0,r.sampleRate),t.setUint32(4,r.bitRate),t.setUint32(8,r.bitRate),e[12]=r.pcmResolution;let i=r.core&&!r.hasExtensions?1:0,n=new q(e);return n.seekToByte(13),n.writeBits(2,Math.max(Ro.indexOf(r.sampleCount),0)),n.writeBits(5,i),n.writeBits(1,r.core?.lfePresent?1:0),n.writeBits(6,r.core?.amode??0),n.writeBits(14,r.core?r.core.frameSize-1:0),n.writeBits(1,0),n.writeBits(3,0),n.writeBits(16,r.channelLayout),n.writeBits(1,0),n.writeBits(1,0),n.writeBits(1,0),n.writeBits(5,0),e},su=r=>tn(r)+tn(r&ru);var Ys=/<(?:(\d{2}):)?(\d{2}):(\d{2}).(\d{3})>/g;var Mo=r=>{let e=Math.floor(r/36e5),t=Math.floor(r%(3600*1e3)/(60*1e3)),i=Math.floor(r%(60*1e3)/1e3),n=r%1e3;return e.toString().padStart(2,"0")+":"+t.toString().padStart(2,"0")+":"+i.toString().padStart(2,"0")+"."+n.toString().padStart(3,"0")};var Do=[],Oo=[];var ce=new Uint8Array(0),Y=class r{constructor(e,t,i,n,a=-1,s,o){if(this.data=e,this.type=t,this.timestamp=i,this.duration=n,this.sequenceNumber=a,e===ce&&s===void 0)throw new Error("Internal error: byteLength must be explicitly provided when constructing metadata-only packets.");if(s===void 0&&(s=e.byteLength),!(e instanceof Uint8Array))throw new TypeError("data must be a Uint8Array.");if(t!=="key"&&t!=="delta")throw new TypeError('type must be either "key" or "delta".');if(!Number.isFinite(i))throw new TypeError("timestamp must be a number.");if(!Number.isFinite(n)||n<0)throw new TypeError("duration must be a non-negative number.");if(!Number.isFinite(a))throw new TypeError("sequenceNumber must be a number.");if(!Number.isInteger(s)||s<0)throw new TypeError("byteLength must be a non-negative integer.");if(o!==void 0&&(typeof o!="object"||!o))throw new TypeError("sideData, when provided, must be an object.");if(o?.alpha!==void 0&&!(o.alpha instanceof Uint8Array))throw new TypeError("sideData.alpha, when provided, must be a Uint8Array.");if(o?.alphaByteLength!==void 0&&(!Number.isInteger(o.alphaByteLength)||o.alphaByteLength<0))throw new TypeError("sideData.alphaByteLength, when provided, must be a non-negative integer.");this.byteLength=s,this.sideData=o??{},this.sideData.alpha&&this.sideData.alphaByteLength===void 0&&(this.sideData.alphaByteLength=this.sideData.alpha.byteLength)}get isMetadataOnly(){return this.data===ce}get microsecondTimestamp(){return Math.trunc(Vs*this.timestamp)}get microsecondDuration(){return Math.trunc(Vs*this.duration)}toEncodedVideoChunk(){if(this.isMetadataOnly)throw new TypeError("Metadata-only packets cannot be converted to a video chunk.");if(typeof EncodedVideoChunk>"u")throw new Error("EncodedVideoChunk is not available in this environment.");return new EncodedVideoChunk({data:this.data,type:this.type,timestamp:this.microsecondTimestamp,duration:this.microsecondDuration})}alphaToEncodedVideoChunk(e=this.type){if(!this.sideData.alpha)throw new TypeError("This packet does not contain alpha side data.");if(this.isMetadataOnly)throw new TypeError("Metadata-only packets cannot be converted to a video chunk.");if(typeof EncodedVideoChunk>"u")throw new Error("EncodedVideoChunk is not available in this environment.");return new EncodedVideoChunk({data:this.sideData.alpha,type:e,timestamp:this.microsecondTimestamp,duration:this.microsecondDuration})}toEncodedAudioChunk(){if(this.isMetadataOnly)throw new TypeError("Metadata-only packets cannot be converted to an audio chunk.");if(typeof EncodedAudioChunk>"u")throw new Error("EncodedAudioChunk is not available in this environment.");return new EncodedAudioChunk({data:this.data,type:this.type,timestamp:this.microsecondTimestamp,duration:this.microsecondDuration})}static fromEncodedChunk(e,t){if(!(e instanceof EncodedVideoChunk||e instanceof EncodedAudioChunk))throw new TypeError("chunk must be an EncodedVideoChunk or EncodedAudioChunk.");let i=new Uint8Array(e.byteLength);return e.copyTo(i),new r(i,e.type,e.timestamp/1e6,(e.duration??0)/1e6,void 0,void 0,t)}clone(e){if(e!==void 0&&(typeof e!="object"||e===null))throw new TypeError("options, when provided, must be an object.");if(e?.data!==void 0&&!(e.data instanceof Uint8Array))throw new TypeError("options.data, when provided, must be a Uint8Array.");if(e?.type!==void 0&&e.type!=="key"&&e.type!=="delta")throw new TypeError('options.type, when provided, must be either "key" or "delta".');if(e?.timestamp!==void 0&&!Number.isFinite(e.timestamp))throw new TypeError("options.timestamp, when provided, must be a number.");if(e?.duration!==void 0&&!Number.isFinite(e.duration))throw new TypeError("options.duration, when provided, must be a number.");if(e?.sequenceNumber!==void 0&&!Number.isFinite(e.sequenceNumber))throw new TypeError("options.sequenceNumber, when provided, must be a number.");if(e?.sideData!==void 0&&(typeof e.sideData!="object"||e.sideData===null))throw new TypeError("options.sideData, when provided, must be an object.");return new r(e?.data??this.data,e?.type??this.type,e?.timestamp??this.timestamp,e?.duration??this.duration,e?.sequenceNumber??this.sequenceNumber,this.byteLength,e?.sideData??this.sideData)}};var le=class{constructor(e){this.input=e}dispose(){}};var En=2082844800,_n=r=>{let t=(r.hasVideo?"video/":r.hasAudio?"audio/":"application/")+(r.isQuickTime?"quicktime":"mp4");if(r.codecStrings.length>0){let i=[...new Set(r.codecStrings)];t+=`; codecs="${i.join(", ")}"`}return t},In=r=>{if(r.length<24)throw new Error("Invalid pssh box: too small.");let e=W(r),t=0,i=e.getUint8(t);t+=1,t+=3;let n=Ft(r.subarray(t,t+16));t+=16;let a=null;if(i>0){let o=e.getUint32(t);if(t+=4,t+16*o+4>r.length)throw new Error("Invalid pssh box: key ID count exceeds box size.");if(o>0){a=[];for(let c=0;c<o;c++)a.push(Ft(r.subarray(t,t+16))),t+=16}}let s=e.getUint32(t);return t+=4,{systemId:n,keyIds:a,data:r.slice(t,t+s)}},vn=(r,e)=>r.systemId===e.systemId&&ao(r.data,e.data);var Ge=16,wt=new Uint32Array(256),Cr=new Uint32Array(256),Pr=new Uint32Array(256),Er=new Uint32Array(256),_r=new Uint32Array(256),pe=new Uint32Array(256),Uo=new Uint32Array(10),zo=!1,au=()=>{let r=new Uint8Array(256),e=new Uint8Array(256),t=new Uint8Array(256);for(let a=0,s=1;a<256;a++)t[a]=s,e[s]=a,s=s^s<<1^(s&128?283:0);let i=(a,s)=>a&&s?t[(e[a]+e[s])%255]:0;r[0]=99;for(let a=1;a<256;a++){let s=t[255-e[a]],o=s^s<<1^s<<2^s<<3^s<<4;o=o>>>8^o&255^99,r[a]=o}for(let a=0;a<256;a++){let s=r[a],o=r.indexOf(a);wt[a]=s<<24|s<<16|s<<8|s,pe[a]=o<<24|o<<16|o<<8|o;let c=i(o,14),l=i(o,9),u=i(o,13),d=i(o,11),f=c<<24|l<<16|u<<8|d;Cr[a]=f,Pr[a]=f>>>8|f<<24,Er[a]=f>>>16|f<<16,_r[a]=f>>>24|f<<8}let n=1;for(let a=0;a<10;a++)Uo[a]=n<<24,n=n<<1^(n&128?283:0);zo=!0},xi=class{constructor(){this.roundkey=new Uint32Array(44),this.iv=new Uint32Array(Ge/Uint32Array.BYTES_PER_ELEMENT),this.in=new Uint8Array(Ge),this.out=new Uint8Array(Ge),this.inView=new DataView(this.in.buffer),this.outView=new DataView(this.out.buffer)}init({key:e,iv:t}){g(e.byteLength===16),g(t.byteLength===16),zo||au();let i=new DataView(e.buffer,e.byteOffset,e.byteLength),n=new DataView(t.buffer,t.byteOffset,t.byteLength);this.roundkey[0]=i.getUint32(0,!1),this.roundkey[1]=i.getUint32(4,!1),this.roundkey[2]=i.getUint32(8,!1),this.roundkey[3]=i.getUint32(12,!1),this.iv[0]=n.getUint32(0,!1),this.iv[1]=n.getUint32(4,!1),this.iv[2]=n.getUint32(8,!1),this.iv[3]=n.getUint32(12,!1);for(let a=4;a<44;a+=4){let s=this.roundkey[a-1];this.roundkey[a]=this.roundkey[a-4]^wt[s>>>16&255]&4278190080^wt[s>>>8&255]&16711680^wt[s>>>0&255]&65280^wt[s>>>24&255]&255^Uo[a/4-1],this.roundkey[a+1]=this.roundkey[a-3]^this.roundkey[a],this.roundkey[a+2]=this.roundkey[a-2]^this.roundkey[a+1],this.roundkey[a+3]=this.roundkey[a-1]^this.roundkey[a+2]}for(let a=0,s=40;a<s;a+=4,s-=4)for(let o=0;o<4;o++){let c=this.roundkey[a+o];this.roundkey[a+o]=this.roundkey[s+o],this.roundkey[s+o]=c}for(let a=4;a<40;a+=4)for(let s=0;s<4;s++){let o=this.roundkey[a+s];this.roundkey[a+s]=Cr[wt[o>>>24&255]&255]^Pr[wt[o>>>16&255]&255]^Er[wt[o>>>8&255]&255]^_r[wt[o>>>0&255]&255]}}decrypt(){let e=this.inView.getUint32(0,!1)^this.roundkey[0],t=this.inView.getUint32(4,!1)^this.roundkey[1],i=this.inView.getUint32(8,!1)^this.roundkey[2],n=this.inView.getUint32(12,!1)^this.roundkey[3],a=this.inView.getUint32(0,!1),s=this.inView.getUint32(4,!1),o=this.inView.getUint32(8,!1),c=this.inView.getUint32(12,!1),l,u,d,f;for(let w=1;w<10;w++){let S=w*4;l=Cr[e>>>24]^Pr[n>>>16&255]^Er[i>>>8&255]^_r[t&255]^this.roundkey[S],u=Cr[t>>>24]^Pr[e>>>16&255]^Er[n>>>8&255]^_r[i&255]^this.roundkey[S+1],d=Cr[i>>>24]^Pr[t>>>16&255]^Er[e>>>8&255]^_r[n&255]^this.roundkey[S+2],f=Cr[n>>>24]^Pr[i>>>16&255]^Er[t>>>8&255]^_r[e&255]^this.roundkey[S+3],e=l,t=u,i=d,n=f}let m=pe[e>>>24&255]&4278190080^pe[n>>>16&255]&16711680^pe[i>>>8&255]&65280^pe[t>>>0&255]&255^this.roundkey[40],p=pe[t>>>24&255]&4278190080^pe[e>>>16&255]&16711680^pe[n>>>8&255]&65280^pe[i>>>0&255]&255^this.roundkey[41],h=pe[i>>>24&255]&4278190080^pe[t>>>16&255]&16711680^pe[e>>>8&255]&65280^pe[n>>>0&255]&255^this.roundkey[42],k=pe[n>>>24&255]&4278190080^pe[i>>>16&255]&16711680^pe[t>>>8&255]&65280^pe[e>>>0&255]&255^this.roundkey[43];this.outView.setUint32(0,m^this.iv[0],!1),this.outView.setUint32(4,p^this.iv[1],!1),this.outView.setUint32(8,h^this.iv[2],!1),this.outView.setUint32(12,k^this.iv[3],!1),this.iv[0]=a,this.iv[1]=s,this.iv[2]=o,this.iv[3]=c}},No=(r,e,t)=>{let i=!1,n=0,a=2**16,s=16,o=new xi;return new ReadableStream({pull:async c=>{i||(o.init(await e()),i=!0);let l=a+s,u=r.requestSliceRange(n,0,l);if(P(u)&&(u=await u),!u||u.length===0)throw new Error("Invalid ciphertext.");let d=u.length;if(d%16!==0)throw new Error("Invalid ciphertext.");let f=d===l?d-s:d,m=M(u,f),p=new Uint8Array(f);for(let h=0;h<f;h+=16)o.in.set(m.subarray(h,h+16)),o.decrypt(),p.set(o.out,h);if(f<d)c.enqueue(p),n+=f;else{let h=p[f-1];if(h===0||h>16)throw new Error("Invalid PKCS#7 padding. Incorrect key or corrupted data.");let k=p.subarray(0,f-h);c.enqueue(k),c.close(),t()}},cancel:()=>{t()}})};var Vo=[2,1,1,2,2,2,2,1,1,2,2,1,1],ou=64,Bn=class r extends le{constructor(e){super(e),this.moovSlice=null,this.currentTrack=null,this.tracks=[],this.idToTrack=new Map,this.metadataPromise=null,this.movieTimescale=-1,this.movieDurationInTimescale=-1,this.movieMatrix=Bt,this.isQuickTime=!1,this.metadataTags={},this.currentMetadataKeys=null,this.isFragmented=!1,this.fragmentTrackDefaults=new Map,this.psshBoxes=[],this.currentFragment=null,this.isReadingTraf=!1,this.lastReadFragment=null,this.fragmentSummaries=new Map,this.decryptionKeyCache=new Map,this.boxNestingDepth=0,this.reader=e._reader}async getTrackBackings(){return await this.readMetadata(),this.tracks.map(e=>e.trackBacking)}async getMimeType(){await this.readMetadata();let e=await this.getTrackBackings(),t=await Promise.all(e.map(i=>i.getDecoderConfig().then(n=>n?.codec??null)));return _n({isQuickTime:this.isQuickTime,hasVideo:this.tracks.some(i=>i.info?.type==="video"),hasAudio:this.tracks.some(i=>i.info?.type==="audio"),codecStrings:t.filter(Boolean)})}async getMetadataTags(){return await this.readMetadata(),this.metadataTags}readMetadata(){return this.metadataPromise??=(async()=>{let e=0,t=!1,i=!1;for(;;){let n=this.reader.requestSliceRange(e,$e,St);if(P(n)&&(n=await n),!n)break;let a=e,s=bt(n);if(!s)break;if((s.name==="ftyp"||s.name==="styp")&&n.remainingLength>=4){let o=J(n,4);this.isQuickTime=o==="qt  "}else if(s.name==="moov"){let o=this.reader.requestSlice(n.filePos,s.contentSize);if(P(o)&&(o=await o),!o)break;if(this.moovSlice=o,this.readContiguousBoxes(this.moovSlice),this.movieTimescale===-1)throw new Error("Invalid moov box: missing mvhd box.");for(let c of this.tracks){let l=c.editListPreviousSegmentDurations/this.movieTimescale;c.editListOffset-=Math.round(l*c.timescale)}t=this.isFragmented&&this.reader.fileSize!==null&&this.reader.fileSize>a+s.totalSize,i=!0;break}else if(s.name==="moof"){if(!this.input._initInput)throw new Error('"moof" box encountered with no "moov" box present; this file is likely a Segment as described in ISO/IEC 14496-12 Section 8.16. A separate init file that contains a "moov" box is required to read this file, please provide it using InputOptions.initInput.');await this.copyMetadataFromInitInput(this.input._initInput),t=!1,i=!0;break}e=a+s.totalSize}if(!i&&this.input._initInput&&await this.copyMetadataFromInitInput(this.input._initInput),t){g(this.reader.fileSize!==null);let n=this.reader.requestSlice(this.reader.fileSize-4,4);P(n)&&(n=await n),g(n);let a=B(n),s=this.reader.fileSize-a;if(s>=0&&s<=this.reader.fileSize-St){let o=this.reader.requestSliceRange(s,$e,St);if(P(o)&&(o=await o),o){let c=bt(o);if(c&&c.name==="mfra"){let l=this.reader.requestSlice(o.filePos,c.contentSize);P(l)&&(l=await l),l&&this.readContiguousBoxes(l)}}}}for(let n of this.tracks){let a=n.fragmentLookupTable;a.sort((o,c)=>o.timestamp-c.timestamp);let s=0;for(let o of a)(s===0||o.timestamp!==a[s-1].timestamp)&&(a[s++]=o);a.length=s}})()}async copyMetadataFromInitInput(e){let t=await e._getDemuxer();if(t.constructor!==r)throw new Error("Init input must match the input's format.");await t.readMetadata(),this.movieTimescale=t.movieTimescale,this.movieDurationInTimescale=t.movieDurationInTimescale,this.movieMatrix=t.movieMatrix,this.metadataTags=t.metadataTags,this.isFragmented=!0,this.fragmentTrackDefaults=t.fragmentTrackDefaults,this.psshBoxes=t.psshBoxes;for(let i of t.tracks){let n={id:i.id,demuxer:this,trackBacking:null,disposition:i.disposition,timescale:i.timescale,durationInMediaTimescale:i.durationInMediaTimescale,durationInMovieTimescale:i.durationInMovieTimescale,matrix:i.matrix,internalCodecId:i.internalCodecId,name:i.name,languageCode:i.languageCode,sampleTableByteOffset:null,sampleTable:null,fragmentLookupTable:[],currentFragmentState:null,fragmentPositionCache:[],editListPreviousSegmentDurations:i.editListPreviousSegmentDurations,editListOffset:i.editListOffset,encryptionInfo:i.encryptionInfo,encryptionAuxInfo:null,frmaCodecString:null,maxBitrate:i.maxBitrate,avgBitrate:i.avgBitrate,info:i.info};if(i.trackBacking){if(g(n.info),n.info.type==="video"&&n.info.width!==-1){let a=n;n.trackBacking=new Mn(a),this.tracks.push(n),this.idToTrack.set(n.id,n)}else if(n.info.type==="audio"&&n.info.numberOfChannels!==-1){let a=n;n.trackBacking=new Dn(a),this.tracks.push(n),this.idToTrack.set(n.id,n)}}}}getSampleTableForTrack(e){if(e.sampleTable)return e.sampleTable;let t={sampleTimingEntries:[],sampleCompositionTimeOffsets:[],sampleSizes:[],sampleCount:0,cumulativeSampleSizes:null,keySampleIndices:null,chunkOffsets:[],sampleToChunk:[],sortedCompositionTimeOffsets:null};if(e.sampleTable=t,e.sampleTableByteOffset===null)return t;g(this.moovSlice);let i=this.moovSlice.slice(e.sampleTableByteOffset);this.currentTrack=e;try{this.traverseBox(i)}catch(c){throw e.sampleTable=null,c}finally{this.currentTrack=null}let n=$(t.sampleTimingEntries),a=Q(t.sampleToChunk,t.chunkOffsets.length-1,c=>c.startChunkIndex),s=t.sampleToChunk[a];if(t.sampleCount=Math.min(t.sampleCount,n?n.startIndex+n.count:0,s?s.startSampleIndex+(t.chunkOffsets.length-s.startChunkIndex)*s.samplesPerChunk:0),qo(t.sampleTimingEntries,t.sampleCount),qo(t.sampleCompositionTimeOffsets,t.sampleCount),e.info?.type==="audio"&&e.info.codec&&be.includes(e.info.codec)&&t.sampleCompositionTimeOffsets.length===0&&t.sampleTimingEntries.length>0){g(e.info?.type==="audio");let c=Ye(e.info.codec),l=[],u=[];for(let d=0;d<t.sampleToChunk.length;d++){let f=t.sampleToChunk[d],m=t.sampleToChunk[d+1],p=Math.min(m?m.startChunkIndex:1/0,t.chunkOffsets.length)-f.startChunkIndex,h=u.length;for(let k=0;k<p;k++){let w=f.startSampleIndex+k*f.samplesPerChunk,S=w+f.samplesPerChunk,b=Q(t.sampleTimingEntries,w,D=>D.startIndex),T=t.sampleTimingEntries[b],y=Q(t.sampleTimingEntries,S,D=>D.startIndex),A=t.sampleTimingEntries[y],x=T.startDecodeTimestamp+(w-T.startIndex)*T.delta,E=A.startDecodeTimestamp+(S-A.startIndex)*A.delta-x,I=$(l);I&&I.delta===E?I.count++:l.push({startIndex:u.length,startDecodeTimestamp:x,count:1,delta:E});let R=f.samplesPerChunk*c.sampleSize*e.info.numberOfChannels;u.push(R)}f.startSampleIndex=h,f.samplesPerChunk=1}t.sampleTimingEntries=l,t.sampleSizes=u,t.sampleCount=u.length}if(t.sampleCompositionTimeOffsets.length>0){let c=t.sampleCompositionTimeOffsets,l=$(c),u=l.startIndex+l.count;u<t.sampleCount&&c.push({startIndex:u,count:t.sampleCount-u,offset:0,startTimestamp:-1,lastTimestamp:-1,maxLastTimestamp:-1});let d=c.filter(k=>k.count>0),f=t.sampleTimingEntries,m=0,p=k=>{for(;m+1<f.length&&f[m+1].startIndex<=k;)m++;let w=f[m];return w.startDecodeTimestamp+(k-w.startIndex)*w.delta};for(let k of d){let w=k.startIndex+k.count-1;k.startTimestamp=p(k.startIndex)+k.offset,k.lastTimestamp=p(w)+k.offset}d.sort((k,w)=>k.startTimestamp-w.startTimestamp||k.startIndex-w.startIndex);let h=-1/0;for(let k of d)h=Math.max(h,k.lastTimestamp),k.maxLastTimestamp=h;t.sortedCompositionTimeOffsets=d}if(t.sampleSizes.length>1){t.cumulativeSampleSizes=[0];for(let c=0;c<t.sampleSizes.length;c++)t.cumulativeSampleSizes.push(t.cumulativeSampleSizes[c]+t.sampleSizes[c])}return t}async readFragment(e){if(this.lastReadFragment?.moofOffset===e)return this.lastReadFragment;let t=this.reader.requestSliceRange(e,$e,St);P(t)&&(t=await t),g(t);let i=bt(t);g(i?.name==="moof");let n=this.reader.requestSlice(e,i.totalSize);if(P(n)&&(n=await n),!n)return null;this.traverseBox(n);let a=this.lastReadFragment;g(a&&a.moofOffset===e),this.fragmentSummaries.set(e,{moofSize:a.moofSize,trackIds:new Set(a.trackData.keys())});for(let[,s]of a.trackData){let o=s.track,{fragmentPositionCache:c}=o;if(!s.startTimestampIsFinal){let f=pt(o.fragmentLookupTable,a.moofOffset,h=>h.moofOffset),m=o.fragmentLookupTable[f];if(m&&s.trunSampleCounts.length>=m.trunNumber&&s.trunSampleCounts[m.trunNumber-1]>=m.sampleNumber){let h=0;for(let S=1;S<m.trunNumber;S++)h+=s.trunSampleCounts[S-1];h+=m.sampleNumber-1;let k=s.samples[h];g(k);let w=m.timestamp-k.presentationTimestamp;Zs(s,w)}else{let h=Q(c,a.moofOffset-1,k=>k.moofOffset);if(h!==-1){let k=c[h];Zs(s,k.endTimestamp)}}s.startTimestampIsFinal=!0}let l=Q(c,s.startTimestamp,f=>f.startTimestamp),u=c[l],d=c[l+1];if((!u||u.moofOffset<a.moofOffset)&&(!d||d.moofOffset>a.moofOffset)&&c.splice(l+1,0,{moofOffset:a.moofOffset,startTimestamp:s.startTimestamp,endTimestamp:s.endTimestamp}),s.encryptionAuxInfo&&o.encryptionInfo){let f=await $o(this.reader,o.encryptionInfo,s.encryptionAuxInfo);for(let m=0;m<Math.min(s.samples.length,f.length);m++){let p=f[m];s.samples[m].encryption=p}}}return a}readContiguousBoxes(e){if(this.boxNestingDepth===ou)throw new Error("Invalid file: boxes are nested too deeply.");let t=e.filePos;this.boxNestingDepth++;try{for(;e.filePos-t<=e.length-$e&&this.traverseBox(e););}finally{this.boxNestingDepth--}}*iterateContiguousBoxes(e){let t=e.filePos;for(;e.filePos-t<=e.length-$e;){let i=e.filePos,n=bt(e);if(!n)break;yield{boxInfo:n,slice:e},e.filePos=i+n.totalSize}}traverseBox(e){let t=e.filePos,i=bt(e);if(!i)return!1;let n=e.filePos,a=t+i.totalSize;switch(i.name){case"mdia":case"minf":case"dinf":case"mfra":case"edts":case"sinf":case"schi":this.readContiguousBoxes(e.slice(n,i.contentSize));break;case"mvhd":{let s=U(e);e.skip(3);let o;if(s===1?(o=ge(e),e.skip(8),this.movieTimescale=B(e),this.movieDurationInTimescale=ge(e)):(o=B(e),e.skip(4),this.movieTimescale=B(e),this.movieDurationInTimescale=B(e)),o!==0&&(this.metadataTags.creationTime=new Date(1e3*(o-En))),this.movieTimescale===0)throw new Error("Invalid mvhd box: timescale must not be 0.");e.skip(16),this.movieMatrix=Lo(e)}break;case"trak":{if(this.currentFragment||this.currentTrack)break;let s={id:-1,demuxer:this,trackBacking:null,disposition:{...fe,primary:!1},info:null,timescale:-1,durationInMovieTimescale:-1,durationInMediaTimescale:-1,matrix:Bt,internalCodecId:null,name:null,languageCode:ne,sampleTableByteOffset:-1,sampleTable:null,fragmentLookupTable:[],currentFragmentState:null,fragmentPositionCache:[],editListPreviousSegmentDurations:0,editListOffset:0,encryptionInfo:null,encryptionAuxInfo:null,frmaCodecString:null,maxBitrate:null,avgBitrate:null};if(this.currentTrack=s,this.readContiguousBoxes(e.slice(n,i.contentSize)),s.id!==-1&&s.timescale!==-1&&s.info!==null&&s.sampleTableByteOffset!==-1){if(s.info.type==="video"&&s.info.width!==-1){let o=s;s.trackBacking=new Mn(o),this.tracks.push(s),this.idToTrack.set(s.id,s)}else if(s.info.type==="audio"&&s.info.numberOfChannels!==-1){let o=s;s.trackBacking=new Dn(o),this.tracks.push(s),this.idToTrack.set(s.id,s)}}this.currentTrack=null}break;case"tkhd":{let s=this.currentTrack;if(!s||this.currentFragment)break;let o=U(e),l=!!(Xe(e)&1);if(s.disposition.default=l,o===0)e.skip(8),s.id=B(e),e.skip(4),s.durationInMovieTimescale=B(e);else if(o===1)e.skip(16),s.id=B(e),e.skip(4),s.durationInMovieTimescale=ge(e);else throw new Error(`Incorrect track header version ${o}.`);e.skip(16);let u=Lo(e);s.matrix=Rt(u,this.movieMatrix)}break;case"elst":{let s=this.currentTrack;if(!s)break;let o=U(e);e.skip(3);let c=!1,l=0,u=B(e);for(let d=0;d<u;d++){let f=o===1?ge(e):B(e),m=o===1?Zo(e):Tt(e),p=Vt(e);if(c){H._warn("Unsupported edit list: multiple edits are not currently supported. Only using first edit.");break}if(m===-1){l+=f;continue}if(p!==1){H._warn("Unsupported edit list entry: media rate must be 1.");break}s.editListPreviousSegmentDurations=l,s.editListOffset=m,c=!0}}break;case"mdhd":{let s=this.currentTrack;if(!s)break;let o=U(e);if(e.skip(3),o===0?(e.skip(8),s.timescale=B(e),s.durationInMediaTimescale=B(e)):o===1&&(e.skip(16),s.timescale=B(e),s.durationInMediaTimescale=ge(e)),s.timescale===0)throw new Error("Invalid mdhd box: timescale must not be 0.");let c=re(e);if(c>0){s.languageCode="";for(let l=0;l<3;l++)s.languageCode=String.fromCharCode(96+(c&31))+s.languageCode,c>>=5;Tr(s.languageCode)||(s.languageCode=ne)}}break;case"hdlr":{let s=this.currentTrack;if(!s)break;e.skip(8);let o=J(e,4);o==="vide"?s.info={type:"video",width:-1,height:-1,squarePixelWidth:-1,squarePixelHeight:-1,codec:null,codecDescription:null,colorSpace:{...Zi},avcType:null,avcCodecInfo:null,hevcCodecInfo:null,vp9CodecInfo:null,av1CodecInfo:null,proresCodecInfo:null,proresFormat:null}:o==="soun"&&(s.info={type:"audio",numberOfChannels:-1,sampleRate:-1,codec:null,codecDescription:null,aacCodecInfo:null,dtsFormat:null,pcmLittleEndian:!1,pcmSampleSize:null})}break;case"stbl":{let s=this.currentTrack;if(!s)break;s.sampleTableByteOffset=t,this.readContiguousBoxes(e.slice(n,i.contentSize))}break;case"stsd":{let s=this.currentTrack;if(!s||s.info===null||s.sampleTable)break;let o=U(e);e.skip(3);let c=B(e);for(let l=0;l<c;l++){let u=e.filePos,d=bt(e);if(!d)break;s.internalCodecId=d.name;let f=d.name.toLowerCase();if(s.info.type==="video"){e.skip(24),s.info.width=re(e),s.info.height=re(e),s.info.squarePixelWidth=s.info.width,s.info.squarePixelHeight=s.info.height,e.skip(50),s.frmaCodecString=null,this.readContiguousBoxes(e.slice(e.filePos,u+d.totalSize-e.filePos));let m=f==="encv"?s.frmaCodecString:f;s.frmaCodecString=null,m==="avc1"||m==="avc3"?(s.info.codec="avc",s.info.avcType=m==="avc1"?1:3):m==="hvc1"||m==="hev1"?s.info.codec="hevc":m==="vp08"?s.info.codec="vp8":m==="vp09"?s.info.codec="vp9":m==="av01"?s.info.codec="av1":At.includes(f)?(s.info.codec="prores",s.info.proresFormat=f):m===null?H._warn("Unknown encrypted video codec due to missing frma box."):H._warn(`Unsupported video codec (sample entry type '${d.name}').`)}else{e.skip(8);let m=re(e);e.skip(6);let p=re(e),h=re(e);e.skip(4);let k=B(e)/65536,w=null;o===0&&m>0&&(m===1?(e.skip(4),h=8*B(e),e.skip(8)):m===2&&(e.skip(4),k=On(e),p=B(e),e.skip(4),h=B(e),w=B(e),e.skip(8))),s.info.numberOfChannels=p,s.info.sampleRate=k,s.frmaCodecString=null,this.readContiguousBoxes(e.slice(e.filePos,u+d.totalSize-e.filePos));let S=f==="enca"?s.frmaCodecString:f;if(s.frmaCodecString=null,S!=="mp4a")if(S==="opus")s.info.codec="opus",s.info.sampleRate=ct;else if(S==="flac")s.info.codec="flac";else if(S==="ulaw")s.info.codec="ulaw";else if(S==="alaw")s.info.codec="alaw";else if(S==="ac-3")s.info.codec="ac3";else if(S==="ec-3")s.info.codec="eac3";else if(Pi.includes(S))s.info.codec="dts",s.info.dtsFormat=S;else if(S==="mlpa")s.info.codec="truehd";else if(S==="twos")h===8?s.info.codec="pcm-s8":h===16?s.info.codec=s.info.pcmLittleEndian?"pcm-s16":"pcm-s16be":(H._warn(`Unsupported sample size ${h} for codec 'twos'.`),s.info.codec=null);else if(S==="sowt")h===8?s.info.codec="pcm-s8":h===16?s.info.codec="pcm-s16":(H._warn(`Unsupported sample size ${h} for codec 'sowt'.`),s.info.codec=null);else if(S==="raw ")s.info.codec="pcm-u8";else if(S==="in24")s.info.codec=s.info.pcmLittleEndian?"pcm-s24":"pcm-s24be";else if(S==="in32")s.info.codec=s.info.pcmLittleEndian?"pcm-s32":"pcm-s32be";else if(S==="fl32")s.info.codec=s.info.pcmLittleEndian?"pcm-f32":"pcm-f32be";else if(S==="fl64")s.info.codec=s.info.pcmLittleEndian?"pcm-f64":"pcm-f64be";else if(S==="ipcm"){let b=s.info.pcmSampleSize;s.info.pcmLittleEndian?b===16?s.info.codec="pcm-s16":b===24?s.info.codec="pcm-s24":b===32?s.info.codec="pcm-s32":(H._warn(`Invalid ipcm sample size ${b}.`),s.info.codec=null):b===16?s.info.codec="pcm-s16be":b===24?s.info.codec="pcm-s24be":b===32?s.info.codec="pcm-s32be":(H._warn(`Invalid ipcm sample size ${b}.`),s.info.codec=null)}else if(S==="fpcm"){let b=s.info.pcmSampleSize;s.info.pcmLittleEndian?b===32?s.info.codec="pcm-f32":b===64?s.info.codec="pcm-f64":(H._warn(`Invalid fpcm sample size ${b}.`),s.info.codec=null):b===32?s.info.codec="pcm-f32be":b===64?s.info.codec="pcm-f64be":(H._warn(`Invalid fpcm sample size ${b}.`),s.info.codec=null)}else if(S==="lpcm"&&w!==null){let b=h+7>>3,T=!!(w&1),y=!!(w&2),A=w&4?-1:0;h>0&&h<=64&&(T?h===32&&(s.info.codec=y?"pcm-f32be":"pcm-f32"):A&1<<b-1?b===1?s.info.codec="pcm-s8":b===2?s.info.codec=y?"pcm-s16be":"pcm-s16":b===3?s.info.codec=y?"pcm-s24be":"pcm-s24":b===4&&(s.info.codec=y?"pcm-s32be":"pcm-s32"):b===1&&(s.info.codec="pcm-u8")),s.info.codec===null&&H._warn("Unsupported PCM format.")}else S===null?H._warn("Unknown encrypted audio codec due to missing frma box."):H._warn(`Unsupported audio codec (sample entry type '${d.name}').`)}e.filePos=u+d.totalSize}}break;case"frma":{let s=this.currentTrack;if(!s)break;let c=J(e,4).toLowerCase();s.frmaCodecString=c}break;case"schm":{let s=this.currentTrack;if(!s)break;e.skip(4);let o=J(e,4);o==="cenc"||o==="cens"||o==="cbcs"?s.encryptionInfo={scheme:o,defaultKid:null,defaultIsProtected:null,defaultPerSampleIvSize:null,defaultConstantIv:null,defaultCryptByteBlock:null,defaultSkipByteBlock:null}:H._warn(`Unsupported encryption scheme '${o}'.`)}break;case"tenc":{let s=this.currentTrack;if(!s||!s.encryptionInfo)break;let o=U(e);e.skip(3),e.skip(1);let c=U(e);if(o>0?(s.encryptionInfo.defaultCryptByteBlock=c>>4,s.encryptionInfo.defaultSkipByteBlock=c&15):(s.encryptionInfo.defaultCryptByteBlock=0,s.encryptionInfo.defaultSkipByteBlock=0),s.encryptionInfo.defaultIsProtected=U(e)!==0,s.encryptionInfo.defaultPerSampleIvSize=U(e),s.encryptionInfo.defaultKid=Ft(M(e,16)),s.encryptionInfo.defaultPerSampleIvSize>16)throw new Error("Invalid tenc box: IV size must not exceed 16 bytes.");if(s.encryptionInfo.defaultIsProtected&&s.encryptionInfo.defaultPerSampleIvSize===0){let l=U(e);if(l>16)throw new Error("Invalid tenc box: IV size must not exceed 16 bytes.");let u=new Uint8Array(16);u.set(M(e,l),0),s.encryptionInfo.defaultConstantIv=u}}break;case"avcC":{let s=this.currentTrack;if(!s||s.info?.type!=="video"||i.contentSize===0)break;s.info.codecDescription=M(e,i.contentSize);let o=dn(s.info.codecDescription)?.sequenceParameterSets[0],c=o&&nr(o);c&&Ho(s,c.pixelAspectRatio)}break;case"hvcC":{let s=this.currentTrack;if(!s||s.info?.type!=="video"||i.contentSize===0)break;s.info.codecDescription=M(e,i.contentSize);let o=fn(s.info.codecDescription)?.arrays.find(l=>l.nalUnitType===se.SPS_NUT)?.nalUnits[0],c=o&&sr(o);c&&Ho(s,c.pixelAspectRatio)}break;case"vpcC":{let s=this.currentTrack;if(!s||s.info?.type!=="video")break;e.skip(4);let o=U(e),c=U(e),l=U(e),u=l>>4,d=l>>1&7,f=l&1,m=U(e),p=U(e),h=U(e);s.info.vp9CodecInfo={profile:o,level:c,bitDepth:u,chromaSubsampling:d,videoFullRangeFlag:f,colourPrimaries:m,transferCharacteristics:p,matrixCoefficients:h}}break;case"av1C":{let s=this.currentTrack;if(!s||s.info?.type!=="video")break;e.skip(1);let o=U(e),c=o>>5,l=o&31,u=U(e),d=u>>7,f=u>>6&1,m=u>>5&1,p=u>>4&1,h=u>>3&1,k=u>>2&1,w=u&3,S=c===2&&f?m?12:10:f?10:8;e.skip(1);let b=M(e,i.contentSize-4),T=yi(b);s.info.av1CodecInfo={profile:c,level:l,tier:d,bitDepth:S,monochrome:p,chromaSubsamplingX:h,chromaSubsamplingY:k,chromaSamplePosition:w,videoFullRangeFlag:T?.videoFullRangeFlag??0,colourPrimaries:T?.colourPrimaries??2,transferCharacteristics:T?.transferCharacteristics??2,matrixCoefficients:T?.matrixCoefficients??2}}break;case"colr":{let s=this.currentTrack;if(!s||s.info?.type!=="video")break;let o=J(e,4);if(o!=="nclx"&&o!=="nclc")break;let c=re(e),l=re(e),u=re(e),d;o==="nclx"&&(d=!!(U(e)&128)),s.info.colorSpace={primaries:De[c],transfer:Oe[l],matrix:Ue[u],fullRange:d}}break;case"pasp":{let s=this.currentTrack;if(!s||s.info?.type!=="video")break;let o=B(e),c=B(e);o>0&&c>0&&(s.info.squarePixelWidth=s.info.width,s.info.squarePixelHeight=s.info.height,o>c?s.info.squarePixelWidth=Math.round(s.info.width*o/c):s.info.squarePixelHeight=Math.round(s.info.height*c/o))}break;case"btrt":{let s=this.currentTrack;if(!s)break;e.skip(4);let o=B(e),c=B(e);s.maxBitrate=o>0?o:null,s.avgBitrate=c>0?c:null}break;case"wave":this.readContiguousBoxes(e.slice(n,i.contentSize));break;case"esds":{let s=this.currentTrack;if(!s||s.info?.type!=="audio")break;e.skip(4);let{objectTypeIndication:o,decoderSpecificInfo:c}=Jo(e);if(o===64||o===103?(s.info.codec="aac",s.info.aacCodecInfo={isMpeg2:o===103,objectType:null}):o===105||o===107?s.info.codec="mp3":o===221?s.info.codec="vorbis":o===169?s.info.codec="dts":H._warn(`Unsupported audio codec (objectTypeIndication ${o}) - discarding track.`),c&&(s.info.codecDescription=c,s.info.codec==="aac")){let l=mi(s.info.codecDescription);l.outputNumberOfChannels!==null&&(s.info.numberOfChannels=l.outputNumberOfChannels),l.outputSampleRate!==null&&(s.info.sampleRate=l.outputSampleRate)}}break;case"enda":{let s=this.currentTrack;if(!s||s.info?.type!=="audio")break;s.info.pcmLittleEndian=!!(re(e)&255)}break;case"pcmC":{let s=this.currentTrack;if(!s||s.info?.type!=="audio")break;e.skip(4);let o=U(e);s.info.pcmLittleEndian=!!(o&1),s.info.pcmSampleSize=U(e)}break;case"dOps":{let s=this.currentTrack;if(!s||s.info?.type!=="audio")break;e.skip(1);let o=U(e),c=re(e),l=B(e),u=Ci(e),d=U(e),f;d!==0?f=M(e,2+o):f=new Uint8Array(0);let m=new Uint8Array(19+f.byteLength),p=new DataView(m.buffer);p.setUint32(0,1332770163,!1),p.setUint32(4,1214603620,!1),p.setUint8(8,1),p.setUint8(9,o),p.setUint16(10,c,!0),p.setUint32(12,l,!0),p.setInt16(16,u,!0),p.setUint8(18,d),m.set(f,19),s.info.codecDescription=m,s.info.numberOfChannels=o}break;case"dfLa":{let s=this.currentTrack;if(!s||s.info?.type!=="audio")break;e.skip(4);let o=127,c=128,l=e.filePos;for(;e.filePos<a;){let p=U(e),h=Xe(e);if((p&o)===Ut.STREAMINFO){e.skip(10);let w=B(e),S=w>>>12,b=(w>>9&7)+1;s.info.sampleRate=S,s.info.numberOfChannels=b,e.skip(20)}else e.skip(h);if(p&c)break}let u=e.filePos;e.filePos=l;let d=M(e,u-l),f=new Uint8Array(4+d.byteLength);new DataView(f.buffer).setUint32(0,1716281667,!1),f.set(d,4),s.info.codecDescription=f}break;case"dac3":{let s=this.currentTrack;if(!s||s.info?.type!=="audio")break;let o=M(e,3),c=new q(o),l=c.readBits(2);c.skipBits(8);let u=c.readBits(3),d=c.readBits(1);l<3&&(s.info.sampleRate=rr[l]),s.info.numberOfChannels=bi[u]+d}break;case"dec3":{let s=this.currentTrack;if(!s||s.info?.type!=="audio")break;let o=M(e,i.contentSize),c=Io(o);if(!c){H._warn("Invalid dec3 box contents, ignoring.");break}let l=Sn(c);l!==null&&(s.info.sampleRate=l),s.info.numberOfChannels=An(c)}break;case"ddts":{let s=this.currentTrack;if(!s||s.info?.type!=="audio")break;let o=M(e,Math.min(i.contentSize,Cn)),c=Bo(o);if(!c){H._warn("Invalid ddts box contents, ignoring.");break}s.info.sampleRate=c.sampleRate,c.numberOfChannels!==null&&(s.info.numberOfChannels=c.numberOfChannels)}break;case"dmlp":{let s=this.currentTrack;if(!s||s.info?.type!=="audio")break;let o=B(e),c=o>>>28;if(c===15){H._warn("Invalid dmlp box contents, ignoring.");break}s.info.sampleRate=(c&8?44100:48e3)<<(c&7);let l=o>>>15&31,d=o&8191||l,f=0;for(let m=0;m<Vo.length;m++)d&1<<m&&(f+=Vo[m]);s.info.numberOfChannels=f}break;case"stts":{let s=this.currentTrack;if(!s||!s.sampleTable)break;e.skip(4);let o=B(e),c=0,l=0;for(let u=0;u<o;u++){let d=B(e),f=B(e);s.sampleTable.sampleTimingEntries.push({startIndex:c,startDecodeTimestamp:l,count:d,delta:f}),c+=d,l+=d*f}}break;case"ctts":{let s=this.currentTrack;if(!s||!s.sampleTable)break;e.skip(4);let o=B(e),c=0;for(let l=0;l<o;l++){let u=B(e),d=Tt(e);s.sampleTable.sampleCompositionTimeOffsets.push({startIndex:c,count:u,offset:d,startTimestamp:-1,lastTimestamp:-1,maxLastTimestamp:-1}),c+=u}}break;case"stsz":{let s=this.currentTrack;if(!s||!s.sampleTable)break;e.skip(4);let o=B(e),c=B(e);if(o===0)for(let l=0;l<c;l++){let u=B(e);s.sampleTable.sampleSizes.push(u)}else s.sampleTable.sampleSizes.push(o);s.sampleTable.sampleCount=c}break;case"stz2":{let s=this.currentTrack;if(!s||!s.sampleTable)break;e.skip(4),e.skip(3);let o=U(e),c=B(e);if(o!==4&&o!==8&&o!==16)throw new Error(`Invalid stz2 box: unsupported field size ${o}.`);let l=M(e,Math.ceil(c*o/8)),u=new q(l);for(let d=0;d<c;d++){let f=u.readBits(o);s.sampleTable.sampleSizes.push(f)}s.sampleTable.sampleCount=c}break;case"stss":{let s=this.currentTrack;if(!s||!s.sampleTable)break;e.skip(4),s.sampleTable.keySampleIndices=[];let o=B(e);for(let c=0;c<o;c++){let l=B(e)-1;s.sampleTable.keySampleIndices.push(l)}s.sampleTable.keySampleIndices.sort((c,l)=>c-l),s.sampleTable.keySampleIndices[0]!==0&&s.sampleTable.keySampleIndices.unshift(0)}break;case"stsc":{let s=this.currentTrack;if(!s||!s.sampleTable)break;e.skip(4);let o=B(e),c=0;for(let u=0;u<o;u++){let d=B(e)-1,f=B(e),m=B(e),p=$(s.sampleTable.sampleToChunk);if(p&&d<=p.startChunkIndex){c++;continue}s.sampleTable.sampleToChunk.push({startSampleIndex:-1,startChunkIndex:d,samplesPerChunk:f,sampleDescriptionIndex:m})}c>0&&H._warn(`Skipped ${c} invalid stsc entries whose chunk indices weren't strictly increasing.`);let l=0;for(let u=0;u<s.sampleTable.sampleToChunk.length;u++)if(s.sampleTable.sampleToChunk[u].startSampleIndex=l,u<s.sampleTable.sampleToChunk.length-1){let f=s.sampleTable.sampleToChunk[u+1].startChunkIndex-s.sampleTable.sampleToChunk[u].startChunkIndex;l+=f*s.sampleTable.sampleToChunk[u].samplesPerChunk}}break;case"stco":{let s=this.currentTrack;if(!s||!s.sampleTable)break;e.skip(4);let o=B(e);for(let c=0;c<o;c++){let l=B(e);s.sampleTable.chunkOffsets.push(l)}}break;case"co64":{let s=this.currentTrack;if(!s||!s.sampleTable)break;e.skip(4);let o=B(e);for(let c=0;c<o;c++){let l=ge(e);s.sampleTable.chunkOffsets.push(l)}}break;case"mvex":this.isFragmented=!0,this.readContiguousBoxes(e.slice(n,i.contentSize));break;case"mehd":{let s=U(e);e.skip(3);let o=s===1?ge(e):B(e);this.movieDurationInTimescale=o}break;case"trex":{e.skip(4);let s=B(e),o=B(e),c=B(e),l=B(e),u=B(e);this.fragmentTrackDefaults.set(s,{trackId:s,defaultSampleDescriptionIndex:o,defaultSampleDuration:c,defaultSampleSize:l,defaultSampleFlags:u})}break;case"tfra":{let s=U(e);e.skip(3);let o=B(e),c=this.idToTrack.get(o);if(!c)break;let l=B(e),u=(l&48)>>4,d=(l&12)>>2,f=l&3,m=[U,re,Xe,B],p=m[u],h=m[d],k=m[f],w=B(e);for(let S=0;S<w;S++){let b=s===1?ge(e):B(e),T=s===1?ge(e):B(e);p(e);let y=h(e),A=k(e);y>=1&&A>=1&&c.fragmentLookupTable.push({timestamp:b,moofOffset:T,trunNumber:y,sampleNumber:A})}}break;case"moof":{if(this.currentFragment)break;this.currentFragment={moofOffset:t,moofSize:i.totalSize,implicitBaseDataOffset:t,trackData:new Map,psshBoxes:[],sampleCount:0};try{this.readContiguousBoxes(e.slice(n,i.contentSize)),this.lastReadFragment=this.currentFragment}finally{this.currentFragment=null,this.currentTrack=null}}break;case"traf":{if(!this.currentFragment||this.isReadingTraf)break;this.isReadingTraf=!0;try{this.readContiguousBoxes(e.slice(n,i.contentSize))}finally{this.isReadingTraf=!1}if(this.currentTrack){let s=this.currentFragment.trackData.get(this.currentTrack.id);e:if(s){if(s.samples.length===0){this.currentFragment.trackData.delete(this.currentTrack.id);break e}s.presentationTimestamps=s.samples.map((u,d)=>({presentationTimestamp:u.presentationTimestamp,sampleIndex:d})).sort((u,d)=>u.presentationTimestamp-d.presentationTimestamp);for(let u=0;u<s.presentationTimestamps.length;u++){let d=s.presentationTimestamps[u],f=s.samples[d.sampleIndex];if(s.firstKeyFrameTimestamp===null&&f.isKeyFrame&&(s.firstKeyFrameTimestamp=f.presentationTimestamp),u<s.presentationTimestamps.length-1){let p=s.presentationTimestamps[u+1].presentationTimestamp-d.presentationTimestamp;f.duration=p}}let o=s.samples[s.presentationTimestamps[0].sampleIndex],c=s.samples[$(s.presentationTimestamps).sampleIndex];s.startTimestamp=o.presentationTimestamp,s.endTimestamp=c.presentationTimestamp+c.duration;let{currentFragmentState:l}=this.currentTrack;g(l),l.startTimestamp!==null&&(Zs(s,l.startTimestamp),s.startTimestampIsFinal=!0),l.encryptionAuxInfo&&!s.samples[0].encryption&&(s.encryptionAuxInfo=l.encryptionAuxInfo)}this.currentTrack.currentFragmentState=null,this.currentTrack=null}}break;case"pssh":{if(this.input._formatOptions.isobmff?._suppressPsshParsing)break;let s=In(M(e,i.contentSize));this.currentFragment?this.currentFragment.psshBoxes.push(s):this.currentTrack||this.psshBoxes.push(s)}break;case"tfhd":{if(!this.currentFragment||!this.isReadingTraf||this.currentTrack)break;e.skip(1);let s=Xe(e),o=!!(s&1),c=!!(s&2),l=!!(s&8),u=!!(s&16),d=!!(s&32),f=!!(s&65536),m=!!(s&131072),p=B(e),h=this.idToTrack.get(p);if(!h)break;if(this.currentFragment.trackData.has(p)){H._warn(`Multiple traf boxes for track ${p} in the same moof box; skipping.`);break}let k=this.fragmentTrackDefaults.get(p);this.currentTrack=h,h.currentFragmentState={baseDataOffset:this.currentFragment.implicitBaseDataOffset,sampleDescriptionIndex:k?.defaultSampleDescriptionIndex??null,defaultSampleDuration:k?.defaultSampleDuration??null,defaultSampleSize:k?.defaultSampleSize??null,defaultSampleFlags:k?.defaultSampleFlags??null,startTimestamp:null,encryptionAuxInfo:null},o?h.currentFragmentState.baseDataOffset=ge(e):m&&(h.currentFragmentState.baseDataOffset=this.currentFragment.moofOffset),c&&(h.currentFragmentState.sampleDescriptionIndex=B(e)),l&&(h.currentFragmentState.defaultSampleDuration=B(e)),u&&(h.currentFragmentState.defaultSampleSize=B(e)),d&&(h.currentFragmentState.defaultSampleFlags=B(e)),f&&(h.currentFragmentState.defaultSampleDuration=0)}break;case"tfdt":{let s=this.currentTrack;if(!s?.currentFragmentState)break;let o=U(e);e.skip(3);let c=o===0?B(e):ge(e);s.currentFragmentState.startTimestamp=c}break;case"trun":{let s=this.currentTrack;if(!s?.currentFragmentState||!this.currentFragment)break;e.skip(1);let o=Xe(e),c=!!(o&1),l=!!(o&4),u=!!(o&256),d=!!(o&512),f=!!(o&1024),m=!!(o&2048),p=B(e),{defaultSampleDuration:h,defaultSampleSize:k,defaultSampleFlags:w}=s.currentFragmentState;if(p>0&&(!u&&h===null||!d&&k===null||!f&&w===null))throw new Error("Invalid trun box: sample values are missing and there are no defaults.");if(this.currentFragment.sampleCount+=p,this.currentFragment.sampleCount>2**20)throw new Error("Too many (> 2^20) samples in fragment.");let S=null;c&&(S=Tt(e));let b=null;l&&(b=B(e));let T;this.currentFragment.trackData.has(s.id)?(T=this.currentFragment.trackData.get(s.id),S!==null&&(T.currentOffset=s.currentFragmentState.baseDataOffset+S)):(T={track:s,currentTimestamp:0,currentOffset:s.currentFragmentState.baseDataOffset+(S??0),startTimestamp:0,endTimestamp:0,firstKeyFrameTimestamp:null,samples:[],presentationTimestamps:[],startTimestampIsFinal:!1,trunSampleCounts:[],encryptionAuxInfo:null},this.currentFragment.trackData.set(s.id,T)),T.trunSampleCounts.push(p);for(let y=0;y<p;y++){let A;u?A=B(e):A=h;let x;d?x=B(e):x=k;let C;f?C=B(e):C=w,y===0&&b!==null&&(C=b);let E=0;m&&(E=Tt(e));let I=!(C&65536);T.samples.push({presentationTimestamp:T.currentTimestamp+E,duration:A,byteOffset:T.currentOffset,byteSize:x,isKeyFrame:I,encryption:null}),T.currentOffset+=x,T.currentTimestamp+=A}this.currentFragment.implicitBaseDataOffset=T.currentOffset}break;case"saiz":{let s=this.currentTrack;if(!s||!s.encryptionInfo)break;if(e.skip(1),Xe(e)&1){let f=J(e,4),m=B(e);if(f!==s.encryptionInfo.scheme||m!==0)break}let c=U(e),l=B(e),u=null;c===0&&l>0&&(u=M(e,l));let d=Ko(s);d.defaultSampleInfoSize=c,d.sampleSizes=u,d.sampleCount=l}break;case"saio":{let s=this.currentTrack;if(!s||!s.encryptionInfo)break;let o=U(e);if(Xe(e)&1){let f=J(e,4),m=B(e);if(f!==s.encryptionInfo.scheme||m!==0)break}let l=B(e);if(l===0)break;l>1&&H._warn("Multiple saio entries are not supported; using the first offset only.");let u=o===0?B(e):Number(ge(e));this.currentFragment&&(u+=this.currentFragment.moofOffset);let d=Ko(s);d.offset=u}break;case"senc":{let s=this.currentTrack;if(!s||!s.encryptionInfo)break;let o=this.currentFragment?.trackData.get(s.id);if(!o)break;e.skip(1);let l=!!(Xe(e)&2),u=B(e),d=s.encryptionInfo.defaultPerSampleIvSize;if(d===null)throw new Error("Invalid file: encrypted track is missing its tenc box.");for(let f=0;f<Math.min(u,o.samples.length);f++){let m=new Uint8Array(16);if(d>0)m.set(M(e,d),0);else if(s.encryptionInfo.defaultConstantIv)m.set(s.encryptionInfo.defaultConstantIv,0);else throw new Error("Invalid file: encrypted sample has no IV.");let p=null;if(l){let k=re(e);p=[];for(let w=0;w<k;w++){let S=re(e),b=B(e);p.push({clearLen:S,protectedLen:b})}}let h=o.samples[f];h.encryption={iv:m,subsamples:p}}}break;case"udta":{let s=this.iterateContiguousBoxes(e.slice(n,i.contentSize));for(let{boxInfo:o,slice:c}of s){if(o.name!=="meta"&&!this.currentTrack){let l=c.filePos;this.metadataTags.raw??={},o.name[0]==="\xA9"?this.metadataTags.raw[o.name]??=Qe(c):this.metadataTags.raw[o.name]??=M(c,o.contentSize),c.filePos=l}switch(o.name){case"meta":c.skip(-o.headerSize),this.traverseBox(c);break;case"\xA9nam":case"name":this.currentTrack?this.currentTrack.name=ie.decode(M(c,o.contentSize)):this.metadataTags.title??=Qe(c);break;case"\xA9des":this.currentTrack||(this.metadataTags.description??=Qe(c));break;case"\xA9ART":this.currentTrack||(this.metadataTags.artist??=Qe(c));break;case"\xA9alb":this.currentTrack||(this.metadataTags.album??=Qe(c));break;case"albr":this.currentTrack||(this.metadataTags.albumArtist??=Qe(c));break;case"\xA9gen":this.currentTrack||(this.metadataTags.genre??=Qe(c));break;case"\xA9day":if(!this.currentTrack){let l=new Date(Qe(c));Number.isNaN(l.getTime())||(this.metadataTags.date??=l)}break;case"\xA9cmt":this.currentTrack||(this.metadataTags.comment??=Qe(c));break;case"\xA9lyr":this.currentTrack||(this.metadataTags.lyrics??=Qe(c));break}}}break;case"meta":{if(this.currentTrack)break;let o=B(e)!==0;this.currentMetadataKeys=new Map,o?this.readContiguousBoxes(e.slice(n,i.contentSize)):this.readContiguousBoxes(e.slice(n+4,i.contentSize-4)),this.currentMetadataKeys=null}break;case"keys":{if(!this.currentMetadataKeys)break;e.skip(4);let s=B(e);for(let o=0;o<s;o++){let c=B(e);if(c<8)throw new Error("Invalid keys box: key size must be at least 8.");e.skip(4);let l=ie.decode(M(e,c-8));this.currentMetadataKeys.set(o+1,l)}}break;case"ilst":{if(!this.currentMetadataKeys)break;let s=this.iterateContiguousBoxes(e.slice(n,i.contentSize));for(let{boxInfo:o,slice:c}of s){let l=o.name,u=(l.charCodeAt(0)<<24)+(l.charCodeAt(1)<<16)+(l.charCodeAt(2)<<8)+l.charCodeAt(3);this.currentMetadataKeys.has(u)&&(l=this.currentMetadataKeys.get(u));let d=ec(c);switch(this.metadataTags.raw??={},this.metadataTags.raw[l]??=d,l){case"\xA9nam":case"titl":case"com.apple.quicktime.title":case"title":typeof d=="string"&&(this.metadataTags.title??=d);break;case"\xA9des":case"desc":case"dscp":case"com.apple.quicktime.description":case"description":typeof d=="string"&&(this.metadataTags.description??=d);break;case"\xA9ART":case"com.apple.quicktime.artist":case"artist":typeof d=="string"&&(this.metadataTags.artist??=d);break;case"\xA9alb":case"albm":case"com.apple.quicktime.album":case"album":typeof d=="string"&&(this.metadataTags.album??=d);break;case"aART":case"album_artist":typeof d=="string"&&(this.metadataTags.albumArtist??=d);break;case"\xA9cmt":case"com.apple.quicktime.comment":case"comment":typeof d=="string"&&(this.metadataTags.comment??=d);break;case"\xA9gen":case"gnre":case"com.apple.quicktime.genre":case"genre":typeof d=="string"&&(this.metadataTags.genre??=d);break;case"\xA9lyr":case"lyrics":typeof d=="string"&&(this.metadataTags.lyrics??=d);break;case"\xA9day":case"rldt":case"com.apple.quicktime.creationdate":case"date":if(typeof d=="string"){let f=new Date(d);Number.isNaN(f.getTime())||(this.metadataTags.date??=f)}break;case"tmpo":if(d instanceof Uint8Array&&d.length>=2){let f=W(d).getInt16(0,!1);f>0&&(this.metadataTags.beatsPerMinute??=f)}break;case"covr":case"com.apple.quicktime.artwork":d instanceof je?(this.metadataTags.images??=[],this.metadataTags.images.push({data:d.data,kind:"coverFront",mimeType:d.mimeType})):d instanceof Uint8Array&&(this.metadataTags.images??=[],this.metadataTags.images.push({data:d,kind:"coverFront",mimeType:"image/*"}));break;case"track":if(typeof d=="string"){let f=d.split("/"),m=Number.parseInt(f[0],10),p=f[1]&&Number.parseInt(f[1],10);Number.isInteger(m)&&m>0&&(this.metadataTags.trackNumber??=m),p&&Number.isInteger(p)&&p>0&&(this.metadataTags.tracksTotal??=p)}break;case"trkn":if(d instanceof Uint8Array&&d.length>=6){let f=W(d),m=f.getUint16(2,!1),p=f.getUint16(4,!1);m>0&&(this.metadataTags.trackNumber??=m),p>0&&(this.metadataTags.tracksTotal??=p)}break;case"disc":case"disk":if(d instanceof Uint8Array&&d.length>=6){let f=W(d),m=f.getUint16(2,!1),p=f.getUint16(4,!1);m>0&&(this.metadataTags.discNumber??=m),p>0&&(this.metadataTags.discsTotal??=p)}break}}}break}return e.filePos=a,!0}},Fn=class{constructor(e){this.internalTrack=e,this.packetToSampleIndex=new WeakMap,this.packetToFragmentLocation=new WeakMap}getId(){return this.internalTrack.id}getNumber(){let e=this.internalTrack.demuxer,t=this.internalTrack.trackBacking.getType(),i=0;for(let n of e.tracks)if(n.trackBacking.getType()===t&&i++,n===this.internalTrack)break;return i}getCodec(){throw new Error("Not implemented on base class.")}getInternalCodecId(){return this.internalTrack.internalCodecId}getName(){return this.internalTrack.name}getLanguageCode(){return this.internalTrack.languageCode}getTimeResolution(){return this.internalTrack.timescale}isRelativeToUnixEpoch(){return!1}getUnixTimeForTimestamp(){return null}getDisposition(){return this.internalTrack.disposition}getPairingMask(){return 1n}getBitrate(){return this.internalTrack.maxBitrate}getAverageBitrate(){return this.internalTrack.avgBitrate}async getDurationFromMetadata(){let e=this.internalTrack;return e.durationInMediaTimescale<=0?null:(g(e.trackBacking),((await e.trackBacking.getFirstPacket({metadataOnly:!0}))?.timestamp??0)+e.durationInMediaTimescale/e.timescale)}async getLiveRefreshInterval(){return null}async getFirstPacket(e){let t=await this.fetchPacketForSampleIndex(0,e);return t||!this.internalTrack.demuxer.isFragmented?t:this.performFragmentedLookup(null,i=>i.trackData.get(this.internalTrack.id)?{sampleIndex:0,correctSampleFound:!0}:{sampleIndex:-1,correctSampleFound:!1},-1/0,1/0,e)}mapTimestampIntoTimescale(e){return kt(e*this.internalTrack.timescale)+this.internalTrack.editListOffset}async getPacket(e,t){let i=this.mapTimestampIntoTimescale(e),n=this.internalTrack.demuxer.getSampleTableForTrack(this.internalTrack),a=Js(n,i),s=await this.fetchPacketForSampleIndex(a,t);return!Wo(n)||!this.internalTrack.demuxer.isFragmented?s:this.performFragmentedLookup(null,o=>{let c=o.trackData.get(this.internalTrack.id);if(!c)return{sampleIndex:-1,correctSampleFound:!1};let l=Q(c.presentationTimestamps,i,f=>f.presentationTimestamp),u=l!==-1?c.presentationTimestamps[l].sampleIndex:-1,d=l!==-1&&i<c.endTimestamp;return{sampleIndex:u,correctSampleFound:d}},i,i,t)}async getNextPacket(e,t){let i=this.packetToSampleIndex.get(e);if(i!==void 0)return this.fetchPacketForSampleIndex(i+1,t);let n=this.packetToFragmentLocation.get(e);if(n===void 0)throw new Error("Packet was not created from this track.");return this.performFragmentedLookup(n.fragment,a=>{if(a===n.fragment){let s=a.trackData.get(this.internalTrack.id);if(n.sampleIndex+1<s.samples.length)return{sampleIndex:n.sampleIndex+1,correctSampleFound:!0}}else if(a.trackData.get(this.internalTrack.id))return{sampleIndex:0,correctSampleFound:!0};return{sampleIndex:-1,correctSampleFound:!1}},-1/0,1/0,t)}async getKeyPacket(e,t){let i=this.mapTimestampIntoTimescale(e),n=this.internalTrack.demuxer.getSampleTableForTrack(this.internalTrack),a=cu(n,i),s=await this.fetchPacketForSampleIndex(a,t);return!Wo(n)||!this.internalTrack.demuxer.isFragmented?s:this.performFragmentedLookup(null,o=>{let c=o.trackData.get(this.internalTrack.id);if(!c)return{sampleIndex:-1,correctSampleFound:!1};let l=br(c.presentationTimestamps,f=>c.samples[f.sampleIndex].isKeyFrame&&f.presentationTimestamp<=i),u=l!==-1?c.presentationTimestamps[l].sampleIndex:-1,d=l!==-1&&i<c.endTimestamp;return{sampleIndex:u,correctSampleFound:d}},i,i,t)}async getNextKeyPacket(e,t){let i=this.packetToSampleIndex.get(e);if(i!==void 0){let a=this.internalTrack.demuxer.getSampleTableForTrack(this.internalTrack),s=du(a,i);return this.fetchPacketForSampleIndex(s,t)}let n=this.packetToFragmentLocation.get(e);if(n===void 0)throw new Error("Packet was not created from this track.");return this.performFragmentedLookup(n.fragment,a=>{if(a===n.fragment){let s=a.trackData.get(this.internalTrack.id);for(let o=n.sampleIndex+1;o<s.samples.length;o++)if(s.samples[o].isKeyFrame)return{sampleIndex:o,correctSampleFound:!0}}else{let s=a.trackData.get(this.internalTrack.id);if(s&&s.firstKeyFrameTimestamp!==null){let o=s.samples.findIndex(c=>c.isKeyFrame);return g(o!==-1),{sampleIndex:o,correctSampleFound:!0}}}return{sampleIndex:-1,correctSampleFound:!1}},-1/0,1/0,t)}async fetchPacketForSampleIndex(e,t){if(e===-1)return null;let i=this.internalTrack.demuxer.getSampleTableForTrack(this.internalTrack),n=lu(i,e);if(!n)return null;let a;if(t.metadataOnly)a=ce;else{let l=this.internalTrack.demuxer.reader.requestSlice(n.sampleOffset,n.sampleSize);if(P(l)&&(l=await l),!l)return null;if(a=M(l,n.sampleSize),this.internalTrack.encryptionInfo){let u=null;if(this.internalTrack.encryptionAuxInfo){let d=await $o(this.internalTrack.demuxer.reader,this.internalTrack.encryptionInfo,this.internalTrack.encryptionAuxInfo);e<d.length&&(u=d[e])}u??=jo(this.internalTrack.encryptionInfo),u&&(a=await Go(this.internalTrack,u,a,null))}}let s=(n.presentationTimestamp-this.internalTrack.editListOffset)/this.internalTrack.timescale,o=n.duration/this.internalTrack.timescale,c=new Y(a,n.isKeyFrame?"key":"delta",s,o,e,n.sampleSize);return this.packetToSampleIndex.set(c,e),c}async fetchPacketInFragment(e,t,i){if(t===-1)return null;let a=e.trackData.get(this.internalTrack.id).samples[t];g(a);let s;if(i.metadataOnly)s=ce;else{let u=this.internalTrack.demuxer.reader.requestSlice(a.byteOffset,a.byteSize);if(P(u)&&(u=await u),!u)return null;if(s=M(u,a.byteSize),this.internalTrack.encryptionInfo){let d=a.encryption??jo(this.internalTrack.encryptionInfo);d&&(s=await Go(this.internalTrack,d,s,e))}}let o=(a.presentationTimestamp-this.internalTrack.editListOffset)/this.internalTrack.timescale,c=a.duration/this.internalTrack.timescale,l=new Y(s,a.isKeyFrame?"key":"delta",o,c,e.moofOffset+t,a.byteSize);return this.packetToFragmentLocation.set(l,{fragment:e,sampleIndex:t}),l}async performFragmentedLookup(e,t,i,n,a,s=1/0,o=0){let c=this.internalTrack.demuxer,l=null,u=null,d=-1;if(e){let{sampleIndex:T,correctSampleFound:y}=t(e);if(y)return this.fetchPacketInFragment(e,T,a);T!==-1&&(u=e,d=T)}let f=Q(this.internalTrack.fragmentLookupTable,i,T=>T.timestamp),m=f!==-1?this.internalTrack.fragmentLookupTable[f]:null,p=Q(this.internalTrack.fragmentPositionCache,i,T=>T.startTimestamp),h=p!==-1?this.internalTrack.fragmentPositionCache[p]:null,k=Math.max(m?.moofOffset??0,h?.moofOffset??0)||null,w=!!m&&m.moofOffset>=(h?.moofOffset??0),S;e?k===null||e.moofOffset>=k?(S=e.moofOffset+e.moofSize,l=e):S=k:S=k??0;let b=l?l.moofOffset:S;for(;S<s;){if(l){let C=l.trackData.get(this.internalTrack.id);if(C&&C.startTimestamp>n)break;l=null}let T=c.fragmentSummaries.get(S);if(T&&!T.trackIds.has(this.internalTrack.id)){S+=T.moofSize;continue}let y=c.reader.requestSliceRange(S,$e,St);if(P(y)&&(y=await y),!y)break;let A=S,x=bt(y);if(!x)break;if(x.name==="moof"){if(l=await c.readFragment(A),!l)break;let{sampleIndex:C,correctSampleFound:E}=t(l);if(E)return this.fetchPacketInFragment(l,C,a);C!==-1&&(u=l,d=C)}S=A+x.totalSize}if(k!==null&&(!u||u.moofOffset<k)){let T=1<<o,A=(w?this.internalTrack.fragmentLookupTable[f-T]?.timestamp:this.internalTrack.fragmentPositionCache[p-T]?.startTimestamp)??-1/0;return this.performFragmentedLookup(null,t,A,n,a,b,o+1)}return u?this.fetchPacketInFragment(u,d,a):null}},Mn=class extends Fn{constructor(e){super(e),this.decoderConfigPromise=null}getType(){return"video"}getCodec(){return this.internalTrack.info.codec}getCodedWidth(){return this.internalTrack.info.width}getCodedHeight(){return this.internalTrack.info.height}getSquarePixelWidth(){return this.internalTrack.info.squarePixelWidth}getSquarePixelHeight(){return this.internalTrack.info.squarePixelHeight}getTransformationMatrix(){return[...this.internalTrack.matrix]}async getColorSpace(){let e=await this.getDecoderConfig();return e?{primaries:e.colorSpace?.primaries,transfer:e.colorSpace?.transfer,matrix:e.colorSpace?.matrix,fullRange:e.colorSpace?.fullRange}:this.internalTrack.info.colorSpace}async canBeTransparent(){return this.internalTrack.info.codec==="prores"&&(this.internalTrack.info.proresFormat==="ap4h"||this.internalTrack.info.proresFormat==="ap4x")}async getDecoderConfig(){return this.internalTrack.info.codec?this.decoderConfigPromise??=(async()=>{if(this.internalTrack.info.codec==="avc"&&!this.internalTrack.info.codecDescription){let t=await this.getFirstPacket({});this.internalTrack.info.avcCodecInfo=t&&zt(t.data)}else if(this.internalTrack.info.codec==="hevc"&&!this.internalTrack.info.codecDescription){let t=await this.getFirstPacket({});this.internalTrack.info.hevcCodecInfo=t&&Nt(t.data)}else if(this.internalTrack.info.codec==="vp9"&&(!this.internalTrack.info.vp9CodecInfo||!xo(this.internalTrack.info.vp9CodecInfo))){let t=await this.getFirstPacket({}),i=t&&hn(t.data);i&&(this.internalTrack.info.vp9CodecInfo={...this.internalTrack.info.vp9CodecInfo??i,videoFullRangeFlag:i.videoFullRangeFlag,colourPrimaries:i.colourPrimaries,transferCharacteristics:i.transferCharacteristics,matrixCoefficients:i.matrixCoefficients})}else if(this.internalTrack.info.codec==="av1"&&(!this.internalTrack.info.av1CodecInfo||!mn(this.internalTrack.info.av1CodecInfo))){let t=await this.getFirstPacket({}),i=t&&yi(t.data);i&&(this.internalTrack.info.av1CodecInfo=i)}else if(this.internalTrack.info.codec==="prores"&&!this.internalTrack.info.proresCodecInfo){let t=await this.getFirstPacket({});this.internalTrack.info.proresCodecInfo=t&&pn(t.data)}if(!ci(this.internalTrack.info.colorSpace)){let t=Un(this.internalTrack.info);this.internalTrack.info.colorSpace.primaries??=t.primaries,this.internalTrack.info.colorSpace.transfer??=t.transfer,this.internalTrack.info.colorSpace.matrix??=t.matrix,this.internalTrack.info.colorSpace.fullRange??=t.fullRange}let e={codec:ar(this.internalTrack.info),codedWidth:this.internalTrack.info.width,codedHeight:this.internalTrack.info.height,description:this.internalTrack.info.codecDescription??void 0,colorSpace:this.internalTrack.info.colorSpace};return(this.internalTrack.info.width!==this.internalTrack.info.squarePixelWidth||this.internalTrack.info.height!==this.internalTrack.info.squarePixelHeight)&&(e.displayAspectWidth=this.internalTrack.info.squarePixelWidth,e.displayAspectHeight=this.internalTrack.info.squarePixelHeight),e})():null}},Dn=class extends Fn{constructor(e){super(e),this.decoderConfigPromise=null}getType(){return"audio"}getCodec(){return this.internalTrack.info.codec}getNumberOfChannels(){return this.internalTrack.info.numberOfChannels}getSampleRate(){return this.internalTrack.info.sampleRate}async getDecoderConfig(){return this.internalTrack.info.codec?this.decoderConfigPromise??=(async()=>{if(this.internalTrack.info.codec==="dts"&&!this.internalTrack.info.dtsFormat){let e=await this.getFirstPacket({});this.internalTrack.info.dtsFormat=e&&Pn(e.data)}return{codec:Ir(this.internalTrack.info),numberOfChannels:this.internalTrack.info.numberOfChannels,sampleRate:this.internalTrack.info.sampleRate,description:this.internalTrack.info.codecDescription??void 0}})():null}},Js=(r,e)=>{if(r.sortedCompositionTimeOffsets)return Qo(r,e,!1);{let t=Q(r.sampleTimingEntries,e,n=>n.startDecodeTimestamp);if(t===-1)return-1;let i=r.sampleTimingEntries[t];return i.delta===0?i.startIndex+i.count-1:i.startIndex+Math.min(Math.floor((e-i.startDecodeTimestamp)/i.delta),i.count-1)}},cu=(r,e)=>{if(!r.keySampleIndices)return Js(r,e);if(r.sortedCompositionTimeOffsets)return Qo(r,e,!0);{let t=Js(r,e),i=Q(r.keySampleIndices,t,n=>n);return r.keySampleIndices[i]??-1}},lu=(r,e)=>{if(e>=r.sampleCount)return null;let t=Q(r.sampleTimingEntries,e,k=>k.startIndex),i=r.sampleTimingEntries[t],a=i.startDecodeTimestamp+(e-i.startIndex)*i.delta,s=Q(r.sampleCompositionTimeOffsets,e,k=>k.startIndex),o=r.sampleCompositionTimeOffsets[s];o&&e-o.startIndex<o.count&&(a+=o.offset);let c=r.sampleSizes[Math.min(e,r.sampleSizes.length-1)],l=Q(r.sampleToChunk,e,k=>k.startSampleIndex),u=r.sampleToChunk[l],d=u.startChunkIndex+Math.floor((e-u.startSampleIndex)/u.samplesPerChunk),f=r.chunkOffsets[d],m=u.startSampleIndex+(d-u.startChunkIndex)*u.samplesPerChunk,p=f;r.sampleSizes.length===1?p+=c*(e-m):p+=r.cumulativeSampleSizes[e]-r.cumulativeSampleSizes[m];let h=i.delta;if(r.sortedCompositionTimeOffsets){let k=uu(r,e,a);k!==null&&(h=k-a)}return{presentationTimestamp:a,duration:h,sampleOffset:p,sampleSize:c,chunkOffset:f,isKeyFrame:r.keySampleIndices?pt(r.keySampleIndices,e,k=>k)!==-1:!0}},Qo=(r,e,t)=>{let i=r.sortedCompositionTimeOffsets,n=-1,a=-1/0,s=Q(i,e,o=>o.startTimestamp);for(let o=s;o>=0;o--){let c=i[o];if(c.maxLastTimestamp<a)break;let l=c.lastTimestamp<=e?c.startIndex+c.count-1:Xo(r,c,(d,f)=>f>e)-1;if(t){let d=Q(r.keySampleIndices,l,f=>f);l=r.keySampleIndices[d]??-1}if(l<c.startIndex)continue;let u=ea(r,l)+c.offset;(u>a||u===a&&l>n)&&(n=l,a=u)}return n},uu=(r,e,t)=>{let i=r.sortedCompositionTimeOffsets,n=Q(i,t,s=>s.startTimestamp),a=i[n+1]?.startTimestamp??null;for(let s=n;s>=0;s--){let o=i[s];if(o.maxLastTimestamp<t)break;let c=Xo(r,o,(u,d)=>d>t||d===t&&u>e);if(c===o.startIndex+o.count)continue;let l=ea(r,c)+o.offset;(a===null||l<a)&&(a=l)}return a},Xo=(r,e,t)=>{let i=e.startIndex,n=e.startIndex+e.count;for(;i<n;){let a=Math.floor((i+n)/2);t(a,ea(r,a)+e.offset)?n=a:i=a+1}return i},ea=(r,e)=>{let t=Q(r.sampleTimingEntries,e,n=>n.startIndex),i=r.sampleTimingEntries[t];return i.startDecodeTimestamp+(e-i.startIndex)*i.delta},du=(r,e)=>{if(!r.keySampleIndices)return e+1;let t=Q(r.keySampleIndices,e,i=>i);return r.keySampleIndices[t+1]??-1},Zs=(r,e)=>{r.startTimestamp+=e,r.endTimestamp+=e;for(let t of r.samples)t.presentationTimestamp+=e;for(let t of r.presentationTimestamps)t.presentationTimestamp+=e},Lo=r=>[Vt(r),Vt(r),Rn(r),Vt(r),Vt(r),Rn(r),Vt(r),Vt(r),Rn(r)],Ho=(r,e)=>{let t=r.info;if(t.type!=="video")return;let{num:i,den:n}=e;!(i>0&&n>0)||i===n||(i>n?(t.squarePixelWidth=Math.round(t.width*i/n),t.squarePixelHeight=t.height):(t.squarePixelWidth=t.width,t.squarePixelHeight=Math.round(t.height*n/i)))},Wo=r=>r.sampleSizes.length===0,qo=(r,e)=>{for(;r.length>0&&$(r).startIndex>=e;)r.pop();let t=$(r);t&&(t.count=Math.min(t.count,e-t.startIndex))},Ko=r=>r.currentFragmentState?r.currentFragmentState.encryptionAuxInfo??={defaultSampleInfoSize:0,sampleSizes:null,sampleCount:0,offset:null,resolved:null}:r.encryptionAuxInfo??={defaultSampleInfoSize:0,sampleSizes:null,sampleCount:0,offset:null,resolved:null},$o=async(r,e,t)=>{if(t.resolved)return t.resolved;if(t.offset===null||t.sampleCount===0)throw new Error("Incomplete saiz/saio info; cannot resolve encryption data.");let i=0;if(t.defaultSampleInfoSize>0)i=t.defaultSampleInfoSize*t.sampleCount;else{g(t.sampleSizes);for(let o=0;o<t.sampleCount;o++)i+=t.sampleSizes[o]}let n=r.requestSlice(t.offset,i);if(P(n)&&(n=await n),!n)throw new Error("Failed to read auxiliary encryption info.");let a=e.defaultPerSampleIvSize;if(a===null)throw new Error("Invalid file: encrypted track is missing its tenc box.");let s=[];for(let o=0;o<t.sampleCount;o++){let c=t.defaultSampleInfoSize>0?t.defaultSampleInfoSize:t.sampleSizes[o],l=new Uint8Array(16);if(a>0)l.set(M(n,a),0);else if(e.defaultConstantIv)l.set(e.defaultConstantIv,0);else throw new Error("Invalid file: encrypted sample has no IV.");let u=null;if(c>a){let d=re(n);u=[];for(let f=0;f<d;f++){let m=re(n),p=B(n);u.push({clearLen:m,protectedLen:p})}}s.push({iv:l,subsamples:u})}return t.resolved=s,s},jo=r=>r.defaultConstantIv?{iv:r.defaultConstantIv,subsamples:null}:null,Go=async(r,e,t,i)=>{g(r.encryptionInfo);let n=r.encryptionInfo;if(n.defaultKid===null)throw new Error("Invalid file: encrypted track is missing its tenc box.");let a=n.defaultKid,s,o=r.demuxer.decryptionKeyCache.get(a);if(o)s=await o;else{if(!r.demuxer.input._formatOptions.isobmff?.resolveKeyId)throw new Error("Encrypted media samples encountered. To decrypt them, please provide a callback for InputOptions.formatOptions.isobmff.resolveKeyId.");let c=(async()=>{let l=r.demuxer.psshBoxes;if(i){l=[...l,...i.psshBoxes].filter(d=>d.keyIds===null||d.keyIds.includes(a));for(let d=0;d<l.length-1;d++)for(let f=d+1;f<l.length;f++)vn(l[d],l[f])&&(l.splice(f,1),f--)}let u=await r.demuxer.input._formatOptions.isobmff.resolveKeyId({keyId:a,psshBoxes:l});if(!(typeof u=="string"&&u.length===32&&to.test(u)||u instanceof Uint8Array&&u.byteLength===16))throw new TypeError("resolveKeyId must return a 32-character hex string or a 16-byte Uint8Array containing the decryption key.");return u instanceof Uint8Array?u:ro(u)})();r.demuxer.decryptionKeyCache.set(a,c),s=await c}return n.scheme==="cenc"||n.scheme==="cens"?fu(s,n,e,t):hu(s,n,e,t)},fu=async(r,e,t,i)=>{let n=new Uint8Array(16);n.set(t.iv,0);let a=await crypto.subtle.importKey("raw",r,{name:"AES-CTR"},!1,["decrypt"]),s=async p=>{let h=await crypto.subtle.decrypt({name:"AES-CTR",counter:n,length:64},a,p);return new Uint8Array(h)};if(!t.subsamples)return s(i);g(e.defaultCryptByteBlock!==null&&e.defaultSkipByteBlock!==null);let o=Yo(t.subsamples,e.defaultCryptByteBlock,e.defaultSkipByteBlock,i.length),c=0;for(let p of o)for(let h of p.perSubsample)c+=h.length;let l=new Uint8Array(c),u=0;for(let p of o)for(let h of p.perSubsample)l.set(i.subarray(h.offset,h.offset+h.length),u),u+=h.length;let d=await s(l),f=new Uint8Array(i),m=0;for(let p of o)for(let h of p.perSubsample)f.set(d.subarray(m,m+h.length),h.offset),m+=h.length;return f},hu=(r,e,t,i)=>{let n=new xi;n.init({key:r,iv:t.iv});let a=e.defaultCryptByteBlock,s=e.defaultSkipByteBlock;if(g(a!==null&&s!==null),!t.subsamples){let u=new Uint8Array(i),d=Math.floor(i.length/16);for(let f=0;f<d;f++){let m=f*16;n.in.set(i.subarray(m,m+16)),n.decrypt(),u.set(n.out,m)}return u}if(a===0&&s===0)throw new Error("cbcs with subsamples requires pattern encryption.");let o=new Uint8Array(i),c=Yo(t.subsamples,a,s,i.length),l=new DataView(t.iv.buffer,t.iv.byteOffset,16);for(let u of c){n.iv[0]=l.getUint32(0,!1),n.iv[1]=l.getUint32(4,!1),n.iv[2]=l.getUint32(8,!1),n.iv[3]=l.getUint32(12,!1);for(let d of u.perSubsample){let f=d.length/16;for(let m=0;m<f;m++){let p=d.offset+m*16;n.in.set(i.subarray(p,p+16)),n.decrypt(),o.set(n.out,p)}}}return o},Yo=(r,e,t,i)=>{let n=[],a=e!==0||t!==0,s=0;for(let o of r){if(s+o.clearLen+o.protectedLen>i)throw new Error("Invalid encryption info: subsamples exceed the sample size.");s+=o.clearLen;let c=[];if(!a)o.protectedLen>0&&c.push({offset:s,length:o.protectedLen}),s+=o.protectedLen;else{let l=o.protectedLen,u=s;for(;l>0&&!(l<16*e);){let d=16*e;c.push({offset:u,length:d}),u+=d,l-=d;let f=Math.min(16*t,l);u+=f,l-=f}s+=o.protectedLen}n.push({perSubsample:c})}return n};var _;(function(r){r[r.EBML=440786851]="EBML",r[r.EBMLVersion=17030]="EBMLVersion",r[r.EBMLReadVersion=17143]="EBMLReadVersion",r[r.EBMLMaxIDLength=17138]="EBMLMaxIDLength",r[r.EBMLMaxSizeLength=17139]="EBMLMaxSizeLength",r[r.DocType=17026]="DocType",r[r.DocTypeVersion=17031]="DocTypeVersion",r[r.DocTypeReadVersion=17029]="DocTypeReadVersion",r[r.Void=236]="Void",r[r.Segment=408125543]="Segment",r[r.SeekHead=290298740]="SeekHead",r[r.Seek=19899]="Seek",r[r.SeekID=21419]="SeekID",r[r.SeekPosition=21420]="SeekPosition",r[r.Duration=17545]="Duration",r[r.Info=357149030]="Info",r[r.TimestampScale=2807729]="TimestampScale",r[r.DateUTC=17505]="DateUTC",r[r.MuxingApp=19840]="MuxingApp",r[r.WritingApp=22337]="WritingApp",r[r.Tracks=374648427]="Tracks",r[r.TrackEntry=174]="TrackEntry",r[r.TrackNumber=215]="TrackNumber",r[r.TrackUID=29637]="TrackUID",r[r.TrackType=131]="TrackType",r[r.FlagEnabled=185]="FlagEnabled",r[r.FlagDefault=136]="FlagDefault",r[r.FlagForced=21930]="FlagForced",r[r.FlagOriginal=21934]="FlagOriginal",r[r.FlagHearingImpaired=21931]="FlagHearingImpaired",r[r.FlagVisualImpaired=21932]="FlagVisualImpaired",r[r.FlagCommentary=21935]="FlagCommentary",r[r.FlagLacing=156]="FlagLacing",r[r.Name=21358]="Name",r[r.Language=2274716]="Language",r[r.LanguageBCP47=2274717]="LanguageBCP47",r[r.CodecID=134]="CodecID",r[r.CodecPrivate=25506]="CodecPrivate",r[r.CodecDelay=22186]="CodecDelay",r[r.SeekPreRoll=22203]="SeekPreRoll",r[r.DefaultDuration=2352003]="DefaultDuration",r[r.Video=224]="Video",r[r.PixelWidth=176]="PixelWidth",r[r.PixelHeight=186]="PixelHeight",r[r.DisplayWidth=21680]="DisplayWidth",r[r.DisplayHeight=21690]="DisplayHeight",r[r.DisplayUnit=21682]="DisplayUnit",r[r.AlphaMode=21440]="AlphaMode",r[r.Audio=225]="Audio",r[r.SamplingFrequency=181]="SamplingFrequency",r[r.Channels=159]="Channels",r[r.BitDepth=25188]="BitDepth",r[r.SimpleBlock=163]="SimpleBlock",r[r.BlockGroup=160]="BlockGroup",r[r.Block=161]="Block",r[r.BlockAdditions=30113]="BlockAdditions",r[r.BlockMore=166]="BlockMore",r[r.BlockAdditional=165]="BlockAdditional",r[r.BlockAddID=238]="BlockAddID",r[r.BlockDuration=155]="BlockDuration",r[r.ReferenceBlock=251]="ReferenceBlock",r[r.Cluster=524531317]="Cluster",r[r.Timestamp=231]="Timestamp",r[r.Cues=475249515]="Cues",r[r.CuePoint=187]="CuePoint",r[r.CueTime=179]="CueTime",r[r.CueTrackPositions=183]="CueTrackPositions",r[r.CueTrack=247]="CueTrack",r[r.CueClusterPosition=241]="CueClusterPosition",r[r.CueRelativePosition=240]="CueRelativePosition",r[r.Colour=21936]="Colour",r[r.MatrixCoefficients=21937]="MatrixCoefficients",r[r.TransferCharacteristics=21946]="TransferCharacteristics",r[r.Primaries=21947]="Primaries",r[r.Range=21945]="Range",r[r.Projection=30320]="Projection",r[r.ProjectionType=30321]="ProjectionType",r[r.ProjectionPoseYaw=30323]="ProjectionPoseYaw",r[r.ProjectionPosePitch=30324]="ProjectionPosePitch",r[r.ProjectionPoseRoll=30325]="ProjectionPoseRoll",r[r.Attachments=423732329]="Attachments",r[r.AttachedFile=24999]="AttachedFile",r[r.FileDescription=18046]="FileDescription",r[r.FileName=18030]="FileName",r[r.FileMediaType=18016]="FileMediaType",r[r.FileData=18012]="FileData",r[r.FileUID=18094]="FileUID",r[r.Chapters=272869232]="Chapters",r[r.Tags=307544935]="Tags",r[r.Tag=29555]="Tag",r[r.Targets=25536]="Targets",r[r.TargetTypeValue=26826]="TargetTypeValue",r[r.TargetType=25546]="TargetType",r[r.TagTrackUID=25541]="TagTrackUID",r[r.TagEditionUID=25545]="TagEditionUID",r[r.TagChapterUID=25540]="TagChapterUID",r[r.TagAttachmentUID=25542]="TagAttachmentUID",r[r.SimpleTag=26568]="SimpleTag",r[r.TagName=17827]="TagName",r[r.TagLanguage=17530]="TagLanguage",r[r.TagString=17543]="TagString",r[r.TagBinary=17541]="TagBinary",r[r.ContentEncodings=28032]="ContentEncodings",r[r.ContentEncoding=25152]="ContentEncoding",r[r.ContentEncodingOrder=20529]="ContentEncodingOrder",r[r.ContentEncodingScope=20530]="ContentEncodingScope",r[r.ContentCompression=20532]="ContentCompression",r[r.ContentCompAlgo=16980]="ContentCompAlgo",r[r.ContentCompSettings=16981]="ContentCompSettings",r[r.ContentEncryption=20533]="ContentEncryption"})(_||(_={}));var mu=[_.EBML,_.Segment],vr=[_.SeekHead,_.Info,_.Cluster,_.Tracks,_.Cues,_.Attachments,_.Chapters,_.Tags],Ei=[...mu,...vr];var tc=Date.UTC(2001,0,1),rc=8,Te=2,Le=2*rc,ta=r=>{if(r.remainingLength<1)return null;let e=U(r);if(r.skip(-1),e===0)return null;let t=1,i=128;for(;(e&i)===0;)t++,i>>=1;return r.remainingLength<t?null:t},Rr=r=>{if(r.remainingLength<1)return null;let e=U(r);if(e===0)return null;let t=1,i=128;for(;(e&i)===0;)t++,i>>=1;if(r.remainingLength<t-1)return null;let n=e&i-1;for(let a=1;a<t;a++)n*=256,n+=U(r);return n},K=(r,e)=>{if(e>8)throw new Error("Bad unsigned int size "+e);let t=0;for(let i=0;i<e;i++)t*=256,t+=U(r);return t},ra=(r,e)=>{if(e<1||e>8)throw new Error("Bad unsigned int size "+e);let t=0n;for(let i=0;i<e;i++)t<<=8n,t+=BigInt(U(r));return t};var ic=(r,e)=>e===0?0n:BigInt.asIntN(8*e,ra(r,e)),zn=r=>{let e=ta(r);return e===null||r.remainingLength<e?null:K(r,e)},ia=r=>{if(r.remainingLength<1)return null;if(U(r)===255)return;r.skip(-1);let t=Rr(r);if(t===null)return null;if(t!==72057594037927940)return t},He=r=>{g(r.remainingLength>=Te);let e=zn(r);if(e===null)return null;let t=ia(r);return t===null?null:{id:e,size:t}},Lt=(r,e)=>{let t=M(r,e),i="";for(let n=0;n<e&&t[n]!==0;n++)i+=String.fromCharCode(t[n]);return i},Br=(r,e)=>{let t=M(r,e),i=0;for(;i<e&&t[i]!==0;)i+=1;return ie.decode(t.subarray(0,i))},Fr=(r,e)=>{if(e===0)return 0;if(e!==4&&e!==8)throw new Error("Bad float size "+e);return e===4?nc(r):On(r)},Nn=async(r,e,t,i)=>{let n=new Set(t),a=e;for(;i===null||a<i;){let s=r.requestSliceRange(a,Te,Le);if(P(s)&&(s=await s),!s)break;let o=He(s);if(!o)break;if(n.has(o.id))return{pos:a,found:!0};lt(o.size),a=s.filePos+o.size}return{pos:i!==null&&i>a?i:a,found:!1}},na=async(r,e,t,i)=>{let a=new Set(t),s=e;for(;s<i;){let o=r.requestSliceRange(s,0,Math.min(65536,i-s));if(P(o)&&(o=await o),!o||o.length===0)break;let c=Math.max(o.length-rc,1);for(let l=0;l<c;l++){o.filePos=s;let u=zn(o);if(u!==null&&a.has(u))return s;s++}}return null},ye={avc:"V_MPEG4/ISO/AVC",hevc:"V_MPEGH/ISO/HEVC",vp8:"V_VP8",vp9:"V_VP9",av1:"V_AV1",prores:"V_PRORES",aac:"A_AAC",mp3:"A_MPEG/L3",opus:"A_OPUS",vorbis:"A_VORBIS",flac:"A_FLAC",ac3:"A_AC3",eac3:"A_EAC3",dts:"A_DTS",truehd:"A_TRUEHD","pcm-u8":"A_PCM/INT/LIT","pcm-s16":"A_PCM/INT/LIT","pcm-s16be":"A_PCM/INT/BIG","pcm-s24":"A_PCM/INT/LIT","pcm-s24be":"A_PCM/INT/BIG","pcm-s32":"A_PCM/INT/LIT","pcm-s32be":"A_PCM/INT/BIG","pcm-f32":"A_PCM/FLOAT/IEEE","pcm-f64":"A_PCM/FLOAT/IEEE",webvtt:"S_TEXT/WEBVTT"};function lt(r){if(r===void 0)throw new Error("Undefined element size is used in a place where it is not supported.")}var sc=r=>{let t=(r.hasVideo?"video/":r.hasAudio?"audio/":"application/")+(r.isWebM?"webm":"x-matroska");if(r.codecStrings.length>0){let i=[...new Set(r.codecStrings.filter(Boolean))];t+=`; codecs="${i.join(", ")}"`}return t};var xt;(function(r){r[r.None=0]="None",r[r.Xiph=1]="Xiph",r[r.FixedSize=2]="FixedSize",r[r.Ebml=3]="Ebml"})(xt||(xt={}));var Vn;(function(r){r[r.Block=1]="Block",r[r.Private=2]="Private",r[r.Next=4]="Next"})(Vn||(Vn={}));var _i;(function(r){r[r.Zlib=0]="Zlib",r[r.Bzlib=1]="Bzlib",r[r.lzo1x=2]="lzo1x",r[r.HeaderStripping=3]="HeaderStripping"})(_i||(_i={}));var sa=[{id:_.SeekHead,flag:"seekHeadSeen"},{id:_.Info,flag:"infoSeen"},{id:_.Tracks,flag:"tracksSeen"},{id:_.Cues,flag:"cuesSeen"}],ac=10*2**20,pu=64,Ln=class extends le{constructor(e){super(e),this.readMetadataPromise=null,this.segments=[],this.currentSegment=null,this.currentTrack=null,this.currentCluster=null,this.currentBlock=null,this.currentBlockAdditional=null,this.currentCueTime=null,this.currentDecodingInstruction=null,this.currentTagTargetIsMovie=!0,this.currentSimpleTagName=null,this.currentAttachedFile=null,this.isWebM=!1,this.claimedSeekTargets=new Set,this.elementNestingDepth=0,this.reader=e._reader}async getTrackBackings(){return await this.readMetadata(),this.segments.flatMap(e=>e.tracks.map(t=>t.trackBacking))}async getMimeType(){await this.readMetadata();let e=await this.getTrackBackings(),t=await Promise.all(e.map(i=>i.getDecoderConfig().then(n=>n?.codec??null)));return sc({isWebM:this.isWebM,hasVideo:this.segments.some(i=>i.tracks.some(n=>n.info?.type==="video")),hasAudio:this.segments.some(i=>i.tracks.some(n=>n.info?.type==="audio")),codecStrings:t.filter(Boolean)})}async getMetadataTags(){await this.readMetadata();for(let t of this.segments)t.metadataTagsPromise||(this.reader.fileSize!==null?t.metadataTagsPromise=this.loadSegmentMetadata(t):t.metadataTagsPromise=Promise.resolve()),await t.metadataTagsPromise;let e={};for(let t of this.segments)e={...e,...t.metadataTags};return e}readMetadata(){return this.readMetadataPromise??=(async()=>{let e=0;for(;;){let t=this.reader.requestSliceRange(e,Te,Le);if(P(t)&&(t=await t),!t)break;let i=He(t);if(!i)break;let n=i.id,a=i.size,s=t.filePos;if(n===_.EBML){lt(a);let o=this.reader.requestSlice(s,a);if(P(o)&&(o=await o),!o)break;this.readContiguousElements(o)}else if(n===_.Segment){if(await this.readSegment(s,a),a===void 0||this.reader.fileSize===null)break}else if(n===_.Cluster){if(this.reader.fileSize===null)break;a===void 0&&(a=(await Nn(this.reader,s,Ei,this.reader.fileSize)).pos-s);let o=$(this.segments);o&&(o.elementEndPos=s+a)}lt(a),e=s+a}})()}async readSegment(e,t){this.currentSegment={seekHeadSeen:!1,infoSeen:!1,tracksSeen:!1,cuesSeen:!1,tagsSeen:!1,attachmentsSeen:!1,timestampScale:-1,timestampFactor:-1,duration:-1,seekEntries:[],tracks:[],idToTrack:new Map,cuePoints:[],dataStartPos:e,elementEndPos:t===void 0?null:e+t,clusterSeekStartPos:e,lastReadCluster:null,clusterSummaries:new Map,metadataTags:{},metadataTagsPromise:null},this.segments.push(this.currentSegment);let i=e,n=new Set;for(;this.currentSegment.elementEndPos===null||i<this.currentSegment.elementEndPos;){let o=this.reader.requestSliceRange(i,Te,Le);if(P(o)&&(o=await o),!o)break;let c=i,l=He(o);if(!l||!vr.includes(l.id)&&l.id!==_.Void){let p=await na(this.reader,c+1,vr,Math.min(this.currentSegment.elementEndPos??1/0,c+ac));if(p){i=p;continue}else break}let{id:u,size:d}=l,f=o.filePos,m=sa.findIndex(p=>p.id===u);if(m!==-1){let p=sa[m].flag;this.currentSegment[p]=!0,u===_.SeekHead&&n.add(c-e),lt(d);let h=this.reader.requestSlice(f,d);P(h)&&(h=await h),h&&this.readContiguousElements(h)}else if(u===_.Tags||u===_.Attachments){u===_.Tags?this.currentSegment.tagsSeen=!0:this.currentSegment.attachmentsSeen=!0,lt(d);let p=this.reader.requestSlice(f,d);P(p)&&(p=await p),p&&this.readContiguousElements(p)}else if(u===_.Cluster){this.currentSegment.clusterSeekStartPos=c;break}if(d===void 0)break;i=f+d}if(this.reader.fileSize!==null)for(let o=0;o<this.currentSegment.seekEntries.length;o++){let c=this.currentSegment.seekEntries[o];if(c.id!==_.SeekHead||n.has(c.segmentPosition)||(n.add(c.segmentPosition),!this.claimSeekTarget(e+c.segmentPosition)))continue;let l=this.reader.requestSliceRange(e+c.segmentPosition,Te,Le);if(P(l)&&(l=await l),!l)continue;let u=He(l);if(!u||u.id!==_.SeekHead)continue;let{size:d}=u;lt(d);let f=this.reader.requestSlice(l.filePos,d);P(f)&&(f=await f),f&&this.readContiguousElements(f)}if(this.currentSegment.seekEntries.sort((o,c)=>o.segmentPosition-c.segmentPosition),this.reader.fileSize!==null)for(let o of this.currentSegment.seekEntries){let c=sa.find(p=>p.id===o.id);if(!c||this.currentSegment[c.flag]||!this.claimSeekTarget(e+o.segmentPosition))continue;let l=this.reader.requestSliceRange(e+o.segmentPosition,Te,Le);if(P(l)&&(l=await l),!l)continue;let u=He(l);if(!u)continue;let{id:d,size:f}=u;if(d!==c.id)continue;lt(f),this.currentSegment[c.flag]=!0;let m=this.reader.requestSlice(l.filePos,f);P(m)&&(m=await m),m&&this.readContiguousElements(m)}this.currentSegment.timestampScale===-1&&(this.currentSegment.timestampScale=1e6,this.currentSegment.timestampFactor=1e9/1e6);for(let o of this.currentSegment.tracks)o.defaultDurationNs!==null&&(o.defaultDuration=this.currentSegment.timestampFactor*o.defaultDurationNs/1e9),o.codecDelay=Math.round(this.currentSegment.timestampFactor*o.codecDelayNs/1e9);for(let o of this.currentSegment.cuePoints){let c=this.currentSegment.idToTrack.get(o.trackId);c&&c.cuePoints.push(o)}for(let o of this.currentSegment.tracks){let c=o.cuePoints;c.sort((u,d)=>u.time-d.time);let l=0;for(let u of c)(l===0||u.time!==c[l-1].time)&&(c[l++]=u);c.length=l}let a=null,s=-1/0;for(let o of this.currentSegment.tracks)o.cuePoints.length>s&&(s=o.cuePoints.length,a=o);for(let o of this.currentSegment.tracks)o.cuePoints.length===0&&(o.cuePoints=a.cuePoints);this.currentSegment=null}async readCluster(e,t){if(t.lastReadCluster?.elementStartPos===e)return t.lastReadCluster;let i=this.reader.requestSliceRange(e,Te,Le);P(i)&&(i=await i),g(i);let n=e,a=He(i);g(a);let s=a.id;g(s===_.Cluster);let o=a.size,c=i.filePos;o===void 0&&(o=(await Nn(this.reader,c,Ei,t.elementEndPos)).pos-c);let l=this.reader.requestSlice(c,o);P(l)&&(l=await l);let u={segment:t,elementStartPos:n,elementEndPos:c+o,dataStartPos:c,timestamp:-1,trackData:new Map};if(l){this.currentCluster=u;try{let d=this.readContiguousElements(l,Ei);u.elementEndPos=d}finally{this.currentCluster=null,this.currentBlock=null}}for(let[,d]of u.trackData){let f=d.track;g(d.blocks.length>0);let m=!1;for(let b=0;b<d.blocks.length;b++){let T=d.blocks[b];T.timestamp+=u.timestamp,m||=T.lacing!==xt.None}d.presentationTimestamps=d.blocks.map((b,T)=>({timestamp:b.timestamp,blockIndex:T})).sort((b,T)=>b.timestamp-T.timestamp);for(let b=0;b<d.presentationTimestamps.length;b++){let T=d.presentationTimestamps[b],y=d.blocks[T.blockIndex];if(d.firstKeyFrameTimestamp===null&&y.isKeyFrame&&(d.firstKeyFrameTimestamp=y.timestamp),b<d.presentationTimestamps.length-1){let A=d.presentationTimestamps[b+1];y.duration=A.timestamp-y.timestamp}else y.duration===0&&f.defaultDuration!=null&&y.lacing===xt.None&&(y.duration=f.defaultDuration)}m&&(d.blocks=this.expandLacedBlocks(d.blocks,f),d.presentationTimestamps=d.blocks.map((b,T)=>({timestamp:b.timestamp,blockIndex:T})).sort((b,T)=>b.timestamp-T.timestamp));let p=d.blocks[d.presentationTimestamps[0].blockIndex],h=d.blocks[$(d.presentationTimestamps).blockIndex];d.startTimestamp=p.timestamp,d.endTimestamp=h.timestamp+h.duration;let k=Q(f.clusterPositionCache,d.startTimestamp,b=>b.startTimestamp),w=f.clusterPositionCache[k],S=f.clusterPositionCache[k+1];(!w||w.elementStartPos<n)&&(!S||S.elementStartPos>n)&&f.clusterPositionCache.splice(k+1,0,{elementStartPos:u.elementStartPos,startTimestamp:d.startTimestamp})}return t.lastReadCluster=u,t.clusterSummaries.set(e,{elementEndPos:u.elementEndPos,trackIds:new Set(u.trackData.keys())}),u}getTrackDataInCluster(e,t){let i=e.trackData.get(t);if(!i){let n=e.segment.idToTrack.get(t);if(!n)return null;i={track:n,startTimestamp:0,endTimestamp:0,firstKeyFrameTimestamp:null,blocks:[],presentationTimestamps:[]},e.trackData.set(t,i)}return i}expandLacedBlocks(e,t){let i=[];for(let n of e){if(n.lacing===xt.None){i.push(n);continue}let a=Se.tempFromBytes(n.data);if(a.length===0)throw new Error("Invalid laced block: no data.");let s=[],o=U(a)+1;switch(n.lacing){case xt.Xiph:{let l=0;for(let u=0;u<o-1;u++){let d=0;for(;a.bufferPos<a.length;){let f=U(a);if(d+=f,f<255){s.push(d),l+=d;break}}}s.push(a.length-(a.bufferPos+l))}break;case xt.FixedSize:{let l=a.length-1,u=Math.floor(l/o);for(let d=0;d<o;d++)s.push(u)}break;case xt.Ebml:{let l=Rr(a);if(l===null)throw new Error("Invalid EBML lacing: bad frame size.");let u=l;s.push(u);let d=u;for(let f=1;f<o-1;f++){let m=a.bufferPos,p=Rr(a);if(p===null)throw new Error("Invalid EBML lacing: bad frame size.");let h=p,w=(1<<(a.bufferPos-m)*7-1)-1,S=h-w;u+=S,s.push(u),d+=u}s.push(a.length-(a.bufferPos+d))}break;default:g(!1)}if(s.length!==o||s.some(l=>l<=0))throw new Error("Invalid block lacing: frame sizes don't match the block.");let c=n.duration||o*(t.defaultDuration??0);for(let l=0;l<o;l++){let u=s[l],d=M(a,u),f=n.timestamp+c*l/o,m=c/o;i.push({timestamp:f,duration:m,isKeyFrame:n.isKeyFrame,data:d,lacing:xt.None,decoded:n.decoded,postProcessed:!1,mainAdditional:n.mainAdditional})}}return i}async loadSegmentMetadata(e){for(let t of e.seekEntries){if(!(t.id===_.Tags&&!e.tagsSeen)){if(!(t.id===_.Attachments&&!e.attachmentsSeen))continue}if(!this.claimSeekTarget(e.dataStartPos+t.segmentPosition))continue;let i=this.reader.requestSliceRange(e.dataStartPos+t.segmentPosition,Te,Le);if(P(i)&&(i=await i),!i)continue;let n=He(i);if(!n||n.id!==t.id)continue;let{size:a}=n;lt(a);let s=this.reader.requestSlice(i.filePos,a);if(P(s)&&(s=await s),s){g(!this.currentSegment),this.currentSegment=e;try{this.readContiguousElements(s)}finally{this.currentSegment=null}}t.id===_.Tags?e.tagsSeen=!0:t.id===_.Attachments&&(e.attachmentsSeen=!0)}}claimSeekTarget(e){return this.claimedSeekTargets.has(e)?!1:(this.claimedSeekTargets.add(e),!0)}readContiguousElements(e,t){if(this.elementNestingDepth===pu)throw new Error("Invalid file: elements are nested too deeply.");this.elementNestingDepth++;try{for(;e.remainingLength>=Te;){let i=e.filePos;if(!this.traverseElement(e,t))return i}return e.filePos}finally{this.elementNestingDepth--}}traverseElement(e,t){let i=He(e);if(!i||t&&t.includes(i.id))return!1;let{id:n,size:a}=i,s=e.filePos;if(lt(a),s+a>e.end)return!1;switch(n){case _.DocType:this.isWebM=Lt(e,a)==="webm";break;case _.Seek:{if(!this.currentSegment)break;let o={id:-1,segmentPosition:-1};this.currentSegment.seekEntries.push(o),this.readContiguousElements(e.slice(s,a)),(o.id===-1||o.segmentPosition===-1)&&this.currentSegment.seekEntries.pop()}break;case _.SeekID:{let o=this.currentSegment?.seekEntries[this.currentSegment.seekEntries.length-1];if(!o)break;o.id=K(e,a)}break;case _.SeekPosition:{let o=this.currentSegment?.seekEntries[this.currentSegment.seekEntries.length-1];if(!o)break;o.segmentPosition=K(e,a)}break;case _.TimestampScale:{if(!this.currentSegment)break;let o=K(e,a);if(o===0)throw new Error("Invalid TimestampScale element: must not be 0.");this.currentSegment.timestampScale=o,this.currentSegment.timestampFactor=1e9/o}break;case _.Duration:{if(!this.currentSegment)break;this.currentSegment.duration=Fr(e,a)}break;case _.DateUTC:{if(!this.currentSegment)break;let o=ic(e,a);this.currentSegment.metadataTags.creationTime=new Date(tc+Number(o/1000000n))}break;case _.TrackEntry:{if(!this.currentSegment||(this.currentTrack={id:-1,segment:this.currentSegment,demuxer:this,clusterPositionCache:[],cuePoints:[],disposition:{...fe,primary:!1},trackBacking:null,codecId:null,codecPrivate:null,defaultDuration:null,defaultDurationNs:null,codecDelay:0,codecDelayNs:0,name:null,languageCode:"eng",hasLanguageBcp47:!1,decodingInstructions:[],info:null},this.readContiguousElements(e.slice(s,a)),!this.currentTrack))break;if(this.currentTrack.decodingInstructions.some(o=>o.data?.type!=="decompress"||o.scope!==Vn.Block||o.data.algorithm!==_i.HeaderStripping)&&(H._warn(`Track #${this.currentTrack.id} has an unsupported content encoding; dropping.`),this.currentTrack=null),this.currentTrack&&this.currentSegment.idToTrack.has(this.currentTrack.id)&&(H._warn(`Track #${this.currentTrack.id} is defined more than once; dropping.`),this.currentTrack=null),this.currentTrack&&this.currentTrack.id!==-1&&this.currentTrack.codecId&&this.currentTrack.info){let o=this.currentTrack.codecId.indexOf("/"),c=o===-1?this.currentTrack.codecId:this.currentTrack.codecId.slice(0,o);if(this.currentTrack.info.type==="video"&&this.currentTrack.info.width!==-1&&this.currentTrack.info.height!==-1){if(this.currentTrack.info.squarePixelWidth=this.currentTrack.info.width,this.currentTrack.info.squarePixelHeight=this.currentTrack.info.height,this.currentTrack.info.displayWidth!==null&&this.currentTrack.info.displayHeight!==null){let u=this.currentTrack.info.displayWidth*this.currentTrack.info.height,d=this.currentTrack.info.displayHeight*this.currentTrack.info.width;u>0&&d>0&&(u>d?this.currentTrack.info.squarePixelWidth=Math.round(this.currentTrack.info.width*u/d):this.currentTrack.info.squarePixelHeight=Math.round(this.currentTrack.info.height*d/u))}if(this.currentTrack.codecId===ye.avc)this.currentTrack.info.codec="avc",this.currentTrack.info.codecDescription=this.currentTrack.codecPrivate;else if(this.currentTrack.codecId===ye.hevc)this.currentTrack.info.codec="hevc",this.currentTrack.info.codecDescription=this.currentTrack.codecPrivate;else if(c===ye.vp8)this.currentTrack.info.codec="vp8";else if(c===ye.vp9)this.currentTrack.info.codec="vp9";else if(c===ye.av1)this.currentTrack.info.codec="av1";else if(c===ye.prores){let u=this.currentTrack.codecPrivate?ie.decode(this.currentTrack.codecPrivate):"";At.includes(u)&&(this.currentTrack.info.codec="prores",this.currentTrack.info.proresFormat=u)}let l=this.currentTrack;this.currentTrack.trackBacking=new aa(l),this.currentSegment.tracks.push(this.currentTrack),this.currentSegment.idToTrack.set(this.currentTrack.id,this.currentTrack)}else if(this.currentTrack.info.type==="audio"){c===ye.aac?(this.currentTrack.info.codec="aac",this.currentTrack.info.aacCodecInfo={isMpeg2:this.currentTrack.codecId.includes("MPEG2"),objectType:null},this.currentTrack.info.codecDescription=this.currentTrack.codecPrivate):this.currentTrack.codecId===ye.mp3?this.currentTrack.info.codec="mp3":c===ye.opus?(this.currentTrack.info.codec="opus",this.currentTrack.info.codecDescription=this.currentTrack.codecPrivate,this.currentTrack.info.sampleRate=ct):c===ye.vorbis?(this.currentTrack.info.codec="vorbis",this.currentTrack.info.codecDescription=this.currentTrack.codecPrivate):c===ye.flac?(this.currentTrack.info.codec="flac",this.currentTrack.info.codecDescription=this.currentTrack.codecPrivate):c===ye.ac3?(this.currentTrack.info.codec="ac3",this.currentTrack.info.codecDescription=this.currentTrack.codecPrivate):c===ye.eac3?(this.currentTrack.info.codec="eac3",this.currentTrack.info.codecDescription=this.currentTrack.codecPrivate):c===ye.dts?(this.currentTrack.info.codec="dts",this.currentTrack.codecId==="A_DTS/EXPRESS"?this.currentTrack.info.dtsFormat="dtse":this.currentTrack.codecId==="A_DTS/LOSSLESS"&&(this.currentTrack.info.dtsFormat="dtsl")):c===ye.truehd?this.currentTrack.info.codec="truehd":this.currentTrack.codecId==="A_PCM/INT/LIT"?this.currentTrack.info.bitDepth===8?this.currentTrack.info.codec="pcm-u8":this.currentTrack.info.bitDepth===16?this.currentTrack.info.codec="pcm-s16":this.currentTrack.info.bitDepth===24?this.currentTrack.info.codec="pcm-s24":this.currentTrack.info.bitDepth===32&&(this.currentTrack.info.codec="pcm-s32"):this.currentTrack.codecId==="A_PCM/INT/BIG"?this.currentTrack.info.bitDepth===8?this.currentTrack.info.codec="pcm-u8":this.currentTrack.info.bitDepth===16?this.currentTrack.info.codec="pcm-s16be":this.currentTrack.info.bitDepth===24?this.currentTrack.info.codec="pcm-s24be":this.currentTrack.info.bitDepth===32&&(this.currentTrack.info.codec="pcm-s32be"):this.currentTrack.codecId==="A_PCM/FLOAT/IEEE"&&(this.currentTrack.info.bitDepth===32?this.currentTrack.info.codec="pcm-f32":this.currentTrack.info.bitDepth===64&&(this.currentTrack.info.codec="pcm-f64"));let l=this.currentTrack;this.currentTrack.trackBacking=new oa(l),this.currentSegment.tracks.push(this.currentTrack),this.currentSegment.idToTrack.set(this.currentTrack.id,this.currentTrack)}}this.currentTrack=null}break;case _.TrackNumber:{if(!this.currentTrack)break;this.currentTrack.id=K(e,a)}break;case _.TrackType:{if(!this.currentTrack)break;let o=K(e,a);o===1?this.currentTrack.info={type:"video",width:-1,height:-1,displayWidth:null,displayHeight:null,displayUnit:null,squarePixelWidth:-1,squarePixelHeight:-1,horizontalScale:1,verticalScale:1,rotation:0,codec:null,codecDescription:null,colorSpace:{...Zi},alphaMode:!1,proresFormat:null}:o===2&&(this.currentTrack.info={type:"audio",numberOfChannels:1,sampleRate:8e3,bitDepth:-1,codec:null,codecDescription:null,aacCodecInfo:null,dtsFormat:null})}break;case _.FlagEnabled:{if(!this.currentTrack)break;K(e,a)||(this.currentTrack=null)}break;case _.FlagDefault:{if(!this.currentTrack)break;this.currentTrack.disposition.default=!!K(e,a)}break;case _.FlagForced:{if(!this.currentTrack)break;this.currentTrack.disposition.forced=!!K(e,a)}break;case _.FlagOriginal:{if(!this.currentTrack)break;this.currentTrack.disposition.original=!!K(e,a)}break;case _.FlagHearingImpaired:{if(!this.currentTrack)break;this.currentTrack.disposition.hearingImpaired=!!K(e,a)}break;case _.FlagVisualImpaired:{if(!this.currentTrack)break;this.currentTrack.disposition.visuallyImpaired=!!K(e,a)}break;case _.FlagCommentary:{if(!this.currentTrack)break;this.currentTrack.disposition.commentary=!!K(e,a)}break;case _.CodecID:{if(!this.currentTrack)break;this.currentTrack.codecId=Lt(e,a)}break;case _.CodecPrivate:{if(!this.currentTrack)break;this.currentTrack.codecPrivate=M(e,a)}break;case _.DefaultDuration:{if(!this.currentTrack)break;this.currentTrack.defaultDurationNs=K(e,a)}break;case _.CodecDelay:{if(!this.currentTrack)break;this.currentTrack.codecDelayNs=K(e,a)}break;case _.Name:{if(!this.currentTrack)break;this.currentTrack.name=Br(e,a)}break;case _.Language:{if(!this.currentTrack||this.currentTrack.hasLanguageBcp47)break;this.currentTrack.languageCode=Lt(e,a),Tr(this.currentTrack.languageCode)||(this.currentTrack.languageCode=ne)}break;case _.LanguageBCP47:{if(!this.currentTrack)break;let c=Lt(e,a).split("-")[0];c?this.currentTrack.languageCode=c:this.currentTrack.languageCode=ne,this.currentTrack.hasLanguageBcp47=!0}break;case _.Video:{if(this.currentTrack?.info?.type!=="video")break;this.readContiguousElements(e.slice(s,a))}break;case _.PixelWidth:{if(this.currentTrack?.info?.type!=="video")break;this.currentTrack.info.width=K(e,a)}break;case _.PixelHeight:{if(this.currentTrack?.info?.type!=="video")break;this.currentTrack.info.height=K(e,a)}break;case _.DisplayWidth:{if(this.currentTrack?.info?.type!=="video")break;this.currentTrack.info.displayWidth=K(e,a)}break;case _.DisplayHeight:{if(this.currentTrack?.info?.type!=="video")break;this.currentTrack.info.displayHeight=K(e,a)}break;case _.DisplayUnit:{if(this.currentTrack?.info?.type!=="video")break;this.currentTrack.info.displayUnit=K(e,a)}break;case _.AlphaMode:{if(this.currentTrack?.info?.type!=="video")break;this.currentTrack.info.alphaMode=K(e,a)===1}break;case _.Colour:{if(this.currentTrack?.info?.type!=="video")break;this.readContiguousElements(e.slice(s,a))}break;case _.MatrixCoefficients:{if(this.currentTrack?.info?.type!=="video")break;let o=K(e,a),c=Ue[o];this.currentTrack.info.colorSpace.matrix=c}break;case _.Range:{if(this.currentTrack?.info?.type!=="video")break;let o=K(e,a);this.currentTrack.info.colorSpace.fullRange=o===1||o===2?o===2:void 0}break;case _.TransferCharacteristics:{if(this.currentTrack?.info?.type!=="video")break;let o=K(e,a),c=Oe[o];this.currentTrack.info.colorSpace.transfer=c}break;case _.Primaries:{if(this.currentTrack?.info?.type!=="video")break;let o=K(e,a),c=De[o];this.currentTrack.info.colorSpace.primaries=c}break;case _.Projection:{if(this.currentTrack?.info?.type!=="video")break;this.readContiguousElements(e.slice(s,a))}break;case _.ProjectionPoseYaw:{if(this.currentTrack?.info?.type!=="video")break;let o=Fr(e,a);try{let c=ai(o);this.currentTrack.info.horizontalScale=Math.round(Math.cos(c*Qi))}catch{}}break;case _.ProjectionPosePitch:{if(this.currentTrack?.info?.type!=="video")break;let o=Fr(e,a);try{let c=ai(o);this.currentTrack.info.verticalScale=Math.round(Math.cos(c*Qi))}catch{}}break;case _.ProjectionPoseRoll:{if(this.currentTrack?.info?.type!=="video")break;let c=-Fr(e,a);try{this.currentTrack.info.rotation=ai(c)}catch{}}break;case _.Audio:{if(this.currentTrack?.info?.type!=="audio")break;this.readContiguousElements(e.slice(s,a))}break;case _.SamplingFrequency:{if(this.currentTrack?.info?.type!=="audio")break;let o=Fr(e,a);if(!(o>0)||!Number.isFinite(o))throw new Error("Invalid SamplingFrequency element: must be a positive, finite number.");this.currentTrack.info.sampleRate=o}break;case _.Channels:{if(this.currentTrack?.info?.type!=="audio")break;let o=K(e,a);if(o===0)throw new Error("Invalid Channels element: must not be 0.");this.currentTrack.info.numberOfChannels=o}break;case _.BitDepth:{if(this.currentTrack?.info?.type!=="audio")break;this.currentTrack.info.bitDepth=K(e,a)}break;case _.CuePoint:{if(!this.currentSegment)break;this.readContiguousElements(e.slice(s,a)),this.currentCueTime=null}break;case _.CueTime:this.currentCueTime=K(e,a);break;case _.CueTrackPositions:{if(this.currentCueTime===null||!this.currentSegment)break;let o={time:this.currentCueTime,trackId:-1,clusterPosition:-1};this.currentSegment.cuePoints.push(o),this.readContiguousElements(e.slice(s,a)),(o.trackId===-1||o.clusterPosition===-1)&&this.currentSegment.cuePoints.pop()}break;case _.CueTrack:{let o=this.currentSegment?.cuePoints[this.currentSegment.cuePoints.length-1];if(!o)break;o.trackId=K(e,a)}break;case _.CueClusterPosition:{let o=this.currentSegment?.cuePoints[this.currentSegment.cuePoints.length-1];if(!o)break;g(this.currentSegment),o.clusterPosition=this.currentSegment.dataStartPos+K(e,a)}break;case _.Timestamp:{if(!this.currentCluster)break;this.currentCluster.timestamp=K(e,a)}break;case _.SimpleBlock:{if(!this.currentCluster)break;let o=e.slice(s,a),c=Rr(o);if(c===null||o.remainingLength<3)break;let l=this.getTrackDataInCluster(this.currentCluster,c);if(!l)break;let u=Ci(o),d=U(o),f=d>>1&3,m=!!(d&128);l.track.info?.type==="audio"&&l.track.info.codec&&!Ii.includes(l.track.info.codec)&&(m=!0);let p=M(o,o.remainingLength),h=l.track.decodingInstructions.length>0;l.blocks.push({timestamp:u,duration:0,isKeyFrame:m,data:p,lacing:f,decoded:!h,postProcessed:!1,mainAdditional:null})}break;case _.BlockGroup:{if(!this.currentCluster)break;this.readContiguousElements(e.slice(s,a)),this.currentBlock=null}break;case _.Block:{if(!this.currentCluster)break;let o=e.slice(s,a),c=Rr(o);if(c===null||o.remainingLength<3)break;let l=this.getTrackDataInCluster(this.currentCluster,c);if(!l)break;let u=Ci(o),f=U(o)>>1&3,m=M(o,o.remainingLength),p=l.track.decodingInstructions.length>0;this.currentBlock={timestamp:u,duration:0,isKeyFrame:!0,data:m,lacing:f,decoded:!p,postProcessed:!1,mainAdditional:null},l.blocks.push(this.currentBlock)}break;case _.BlockAdditions:this.readContiguousElements(e.slice(s,a));break;case _.BlockMore:{let o=this.currentBlock;if(!o)break;let c={addId:1,data:null};this.currentBlockAdditional=c,this.readContiguousElements(e.slice(s,a)),c.data&&c.addId===1&&(o.mainAdditional=c.data),this.currentBlockAdditional=null}break;case _.BlockAdditional:{if(!this.currentBlockAdditional)break;this.currentBlockAdditional.data=M(e,a)}break;case _.BlockAddID:{if(!this.currentBlockAdditional)break;this.currentBlockAdditional.addId=K(e,a)}break;case _.BlockDuration:{if(!this.currentBlock)break;this.currentBlock.duration=K(e,a)}break;case _.ReferenceBlock:{if(!this.currentBlock)break;this.currentBlock.isKeyFrame=!1}break;case _.Tag:this.currentTagTargetIsMovie=!0,this.readContiguousElements(e.slice(s,a));break;case _.Targets:this.readContiguousElements(e.slice(s,a));break;case _.TargetTypeValue:K(e,a)!==50&&(this.currentTagTargetIsMovie=!1);break;case _.TagTrackUID:case _.TagEditionUID:case _.TagChapterUID:case _.TagAttachmentUID:this.currentTagTargetIsMovie=!1;break;case _.SimpleTag:{if(!this.currentTagTargetIsMovie)break;this.currentSimpleTagName=null,this.readContiguousElements(e.slice(s,a))}break;case _.TagName:this.currentSimpleTagName=Br(e,a);break;case _.TagString:{if(!this.currentSimpleTagName)break;let o=Br(e,a);this.processTagValue(this.currentSimpleTagName,o)}break;case _.TagBinary:{if(!this.currentSimpleTagName)break;let o=M(e,a);this.processTagValue(this.currentSimpleTagName,o)}break;case _.AttachedFile:{if(!this.currentSegment||this.currentAttachedFile)break;this.currentAttachedFile={fileUid:null,fileName:null,fileMediaType:null,fileData:null,fileDescription:null},this.readContiguousElements(e.slice(s,a));let o=this.currentSegment.metadataTags;if(this.currentAttachedFile.fileUid&&this.currentAttachedFile.fileData&&(o.raw??={},o.raw[this.currentAttachedFile.fileUid.toString()]=new hi(this.currentAttachedFile.fileData,this.currentAttachedFile.fileMediaType??void 0,this.currentAttachedFile.fileName??void 0,this.currentAttachedFile.fileDescription??void 0)),this.currentAttachedFile.fileMediaType?.startsWith("image/")&&this.currentAttachedFile.fileData){let c=this.currentAttachedFile.fileName,l="unknown";if(c){let u=c.toLowerCase();u.startsWith("cover.")?l="coverFront":u.startsWith("back.")&&(l="coverBack")}o.images??=[],o.images.push({data:this.currentAttachedFile.fileData,mimeType:this.currentAttachedFile.fileMediaType,kind:l,name:this.currentAttachedFile.fileName??void 0,description:this.currentAttachedFile.fileDescription??void 0})}this.currentAttachedFile=null}break;case _.FileUID:{if(!this.currentAttachedFile)break;this.currentAttachedFile.fileUid=ra(e,a)}break;case _.FileName:{if(!this.currentAttachedFile)break;this.currentAttachedFile.fileName=Br(e,a)}break;case _.FileMediaType:{if(!this.currentAttachedFile)break;this.currentAttachedFile.fileMediaType=Lt(e,a)}break;case _.FileData:{if(!this.currentAttachedFile)break;this.currentAttachedFile.fileData=M(e,a)}break;case _.FileDescription:{if(!this.currentAttachedFile)break;this.currentAttachedFile.fileDescription=Br(e,a)}break;case _.ContentEncodings:{let o=this.currentTrack;if(!o)break;this.readContiguousElements(e.slice(s,a)),o.decodingInstructions.sort((c,l)=>l.order-c.order)}break;case _.ContentEncoding:{let o=this.currentTrack;if(!o)break;let c={order:0,scope:Vn.Block,data:null};this.currentDecodingInstruction=c,this.readContiguousElements(e.slice(s,a)),c.data&&o.decodingInstructions.push(c),this.currentDecodingInstruction=null}break;case _.ContentEncodingOrder:{if(!this.currentDecodingInstruction)break;this.currentDecodingInstruction.order=K(e,a)}break;case _.ContentEncodingScope:{if(!this.currentDecodingInstruction)break;this.currentDecodingInstruction.scope=K(e,a)}break;case _.ContentCompression:{if(!this.currentDecodingInstruction)break;this.currentDecodingInstruction.data={type:"decompress",algorithm:_i.Zlib,settings:null},this.readContiguousElements(e.slice(s,a))}break;case _.ContentCompAlgo:{if(this.currentDecodingInstruction?.data?.type!=="decompress")break;this.currentDecodingInstruction.data.algorithm=K(e,a)}break;case _.ContentCompSettings:{if(this.currentDecodingInstruction?.data?.type!=="decompress")break;this.currentDecodingInstruction.data.settings=M(e,a)}break;case _.ContentEncryption:{if(!this.currentDecodingInstruction)break;this.currentDecodingInstruction.data={type:"decrypt"}}break}return e.filePos=s+a,!0}decodeBlockData(e,t){g(e.decodingInstructions.length>0);let i=t;for(let n of e.decodingInstructions)switch(g(n.data),n.data.type){case"decompress":switch(n.data.algorithm){case _i.HeaderStripping:if(n.data.settings&&n.data.settings.length>0){let a=n.data.settings,s=new Uint8Array(a.length+i.length);s.set(a,0),s.set(i,a.length),i=s}break;default:}break;default:}return i}processTagValue(e,t){if(!this.currentSegment?.metadataTags)return;let i=this.currentSegment.metadataTags;if(i.raw??={},i.raw[e]??=t,typeof t=="string")switch(e.toLowerCase()){case"title":i.title??=t;break;case"description":i.description??=t;break;case"artist":i.artist??=t;break;case"album":i.album??=t;break;case"album_artist":i.albumArtist??=t;break;case"genre":i.genre??=t;break;case"bpm":{let n=Number.parseInt(t,10);Number.isInteger(n)&&n>0&&(i.beatsPerMinute??=n)}break;case"comment":i.comment??=t;break;case"lyrics":i.lyrics??=t;break;case"date":{let n=new Date(t);Number.isNaN(n.getTime())||(i.date??=n)}break;case"track_number":case"part_number":{let n=t.split("/"),a=Number.parseInt(n[0],10),s=n[1]&&Number.parseInt(n[1],10);Number.isInteger(a)&&a>0&&(i.trackNumber??=a),s&&Number.isInteger(s)&&s>0&&(i.tracksTotal??=s)}break;case"disc_number":case"disc":{let n=t.split("/"),a=Number.parseInt(n[0],10),s=n[1]&&Number.parseInt(n[1],10);Number.isInteger(a)&&a>0&&(i.discNumber??=a),s&&Number.isInteger(s)&&s>0&&(i.discsTotal??=s)}break}}getDurationFromMetadata(e){if(e.duration<=0)return null;let t=Math.min(...e.tracks.map(i=>i.codecDelay));return(e.duration-t)/e.timestampFactor}},Hn=class{constructor(e){this.internalTrack=e,this.packetToClusterLocation=new WeakMap}getId(){return this.internalTrack.id}getNumber(){let e=this.internalTrack.demuxer,t=this.internalTrack.trackBacking.getType(),i=0;for(let n of e.segments)for(let a of n.tracks)if(a.trackBacking.getType()===t&&i++,a===this.internalTrack)break;return i}getCodec(){throw new Error("Not implemented on base class.")}getInternalCodecId(){return this.internalTrack.codecId}getName(){return this.internalTrack.name}getLanguageCode(){return this.internalTrack.languageCode}getTimeResolution(){return this.internalTrack.segment.timestampFactor}isRelativeToUnixEpoch(){return!1}getUnixTimeForTimestamp(){return null}getDisposition(){return this.internalTrack.disposition}getPairingMask(){return 1n}getBitrate(){return null}getAverageBitrate(){return null}async getDurationFromMetadata(){return this.internalTrack.demuxer.getDurationFromMetadata(this.internalTrack.segment)}async getLiveRefreshInterval(){return null}async getFirstPacket(e){return this.performClusterLookup(null,t=>t.trackData.get(this.internalTrack.id)?{blockIndex:0,correctBlockFound:!0}:{blockIndex:-1,correctBlockFound:!1},-1/0,1/0,e)}intoTimescale(e){return kt(e*this.internalTrack.segment.timestampFactor)+this.internalTrack.codecDelay}async getPacket(e,t){let i=this.intoTimescale(e);return this.performClusterLookup(null,n=>{let a=n.trackData.get(this.internalTrack.id);if(!a)return{blockIndex:-1,correctBlockFound:!1};let s=Q(a.presentationTimestamps,i,l=>l.timestamp),o=s!==-1?a.presentationTimestamps[s].blockIndex:-1,c=s!==-1&&i<a.endTimestamp;return{blockIndex:o,correctBlockFound:c}},i,i,t)}async getNextPacket(e,t){let i=this.packetToClusterLocation.get(e);if(i===void 0)throw new Error("Packet was not created from this track.");return this.performClusterLookup(i.cluster,n=>{if(n===i.cluster){let a=n.trackData.get(this.internalTrack.id);if(i.blockIndex+1<a.blocks.length)return{blockIndex:i.blockIndex+1,correctBlockFound:!0}}else if(n.trackData.get(this.internalTrack.id))return{blockIndex:0,correctBlockFound:!0};return{blockIndex:-1,correctBlockFound:!1}},-1/0,1/0,t)}async getKeyPacket(e,t){let i=this.intoTimescale(e);return this.performClusterLookup(null,n=>{let a=n.trackData.get(this.internalTrack.id);if(!a)return{blockIndex:-1,correctBlockFound:!1};let s=br(a.presentationTimestamps,l=>a.blocks[l.blockIndex].isKeyFrame&&l.timestamp<=i),o=s!==-1?a.presentationTimestamps[s].blockIndex:-1,c=s!==-1&&i<a.endTimestamp;return{blockIndex:o,correctBlockFound:c}},i,i,t)}async getNextKeyPacket(e,t){let i=this.packetToClusterLocation.get(e);if(i===void 0)throw new Error("Packet was not created from this track.");return this.performClusterLookup(i.cluster,n=>{if(n===i.cluster){let a=n.trackData.get(this.internalTrack.id);for(let s=i.blockIndex+1;s<a.blocks.length;s++)if(a.blocks[s].isKeyFrame)return{blockIndex:s,correctBlockFound:!0}}else{let a=n.trackData.get(this.internalTrack.id);if(a&&a.firstKeyFrameTimestamp!==null){let s=a.blocks.findIndex(o=>o.isKeyFrame);return g(s!==-1),{blockIndex:s,correctBlockFound:!0}}}return{blockIndex:-1,correctBlockFound:!1}},-1/0,1/0,t)}async fetchPacketInCluster(e,t,i){if(t===-1)return null;let a=e.trackData.get(this.internalTrack.id).blocks[t];if(g(a),a.decoded||(a.data=this.internalTrack.demuxer.decodeBlockData(this.internalTrack,a.data),a.decoded=!0),!a.postProcessed){if(this.internalTrack.info?.codec==="prores"&&!(a.data.length>=8&&a.data[4]===105&&a.data[5]===99&&a.data[6]===112&&a.data[7]===102)){let p=new Uint8Array(a.data.length+8);W(p).setUint32(0,p.length,!1),p[4]=105,p[5]=99,p[6]=112,p[7]=102,p.set(a.data,8),a.data=p}a.postProcessed=!0}let s=i.metadataOnly?ce:a.data,{codecDelay:o,segment:c}=this.internalTrack,l=(a.timestamp-o)/c.timestampFactor,u=a.duration/c.timestampFactor,d={};a.mainAdditional&&this.internalTrack.info?.type==="video"&&this.internalTrack.info.alphaMode&&(d.alpha=i.metadataOnly?ce:a.mainAdditional,d.alphaByteLength=a.mainAdditional.byteLength);let f=new Y(s,a.isKeyFrame?"key":"delta",l,u,e.dataStartPos+t,a.data.byteLength,d);return this.packetToClusterLocation.set(f,{cluster:e,blockIndex:t}),f}async performClusterLookup(e,t,i,n,a,s=1/0,o=0){let{demuxer:c,segment:l}=this.internalTrack,u=null,d=null,f=-1;if(e){let{blockIndex:y,correctBlockFound:A}=t(e);if(A)return this.fetchPacketInCluster(e,y,a);y!==-1&&(d=e,f=y)}let m=Q(this.internalTrack.cuePoints,i,y=>y.time),p=m!==-1?this.internalTrack.cuePoints[m]:null,h=Q(this.internalTrack.clusterPositionCache,i,y=>y.startTimestamp),k=h!==-1?this.internalTrack.clusterPositionCache[h]:null,w=Math.max(p?.clusterPosition??0,k?.elementStartPos??0)||null,S=!!p&&p.clusterPosition>=(k?.elementStartPos??0),b;e?w===null||e.elementStartPos>=w?(b=e.elementEndPos,u=e):b=w:b=w??l.clusterSeekStartPos;let T=u?u.elementStartPos:b;for(;(l.elementEndPos===null||b<=l.elementEndPos-Te)&&b<s;){if(u){let O=u.trackData.get(this.internalTrack.id);if(O&&O.startTimestamp>n)break;u=null}let y=l.clusterSummaries.get(b);if(y&&!y.trackIds.has(this.internalTrack.id)){b=y.elementEndPos;continue}let A=c.reader.requestSliceRange(b,Te,Le);if(P(A)&&(A=await A),!A)break;let x=b,C=He(A);if(!C||!vr.includes(C.id)&&C.id!==_.Void){let O=await na(c.reader,x+1,vr,Math.min(l.elementEndPos??1/0,x+ac));if(O){b=O;continue}else break}let E=C.id,I=C.size,R=A.filePos;if(E===_.Cluster){u=await c.readCluster(x,l),I=u.elementEndPos-R;let{blockIndex:O,correctBlockFound:V}=t(u);if(V)return this.fetchPacketInCluster(u,O,a);O!==-1&&(d=u,f=O)}I===void 0&&(g(E!==_.Cluster),I=(await Nn(c.reader,R,Ei,l.elementEndPos)).pos-R);let D=R+I;if(l.elementEndPos===null){let O=c.reader.requestSliceRange(D,Te,Le);if(P(O)&&(O=await O),!O)break;if(zn(O)===_.Segment){l.elementEndPos=D;break}}b=D}if(w!==null&&(!d||d.elementStartPos<w)){let y=1<<o,x=(S?this.internalTrack.cuePoints[m-y]?.time:this.internalTrack.clusterPositionCache[h-y]?.startTimestamp)??-1/0;return this.performClusterLookup(null,t,x,n,a,T,o+1)}return d?this.fetchPacketInCluster(d,f,a):null}},aa=class extends Hn{constructor(e){super(e),this.decoderConfigPromise=null}getType(){return"video"}getCodec(){return this.internalTrack.info.codec}getCodedWidth(){return this.internalTrack.info.width}getCodedHeight(){return this.internalTrack.info.height}getSquarePixelWidth(){return this.internalTrack.info.squarePixelWidth}getSquarePixelHeight(){return this.internalTrack.info.squarePixelHeight}getTransformationMatrix(){let e=this.internalTrack.info,t=Rt(Yi(e.horizontalScale,e.verticalScale),$i(e.rotation));return Xi(t,e.width,e.height)}async getColorSpace(){let e=await this.getDecoderConfig();return e?{primaries:e.colorSpace?.primaries,transfer:e.colorSpace?.transfer,matrix:e.colorSpace?.matrix,fullRange:e.colorSpace?.fullRange}:this.internalTrack.info.colorSpace}async canBeTransparent(){return this.internalTrack.info.alphaMode||this.internalTrack.info.codec==="prores"&&(this.internalTrack.info.proresFormat==="ap4h"||this.internalTrack.info.proresFormat==="ap4x")}async getDecoderConfig(){return this.internalTrack.info.codec?this.decoderConfigPromise??=(async()=>{let e=null;(this.internalTrack.info.codec==="vp9"||this.internalTrack.info.codec==="av1"||this.internalTrack.info.codec==="prores"||this.internalTrack.info.codec==="avc"&&!this.internalTrack.info.codecDescription||this.internalTrack.info.codec==="hevc"&&!this.internalTrack.info.codecDescription)&&(e=await this.getFirstPacket({}));let i={width:this.internalTrack.info.width,height:this.internalTrack.info.height,codec:this.internalTrack.info.codec,codecDescription:this.internalTrack.info.codecDescription,colorSpace:this.internalTrack.info.colorSpace,avcType:1,avcCodecInfo:this.internalTrack.info.codec==="avc"&&e?zt(e.data):null,hevcCodecInfo:this.internalTrack.info.codec==="hevc"&&e?Nt(e.data):null,vp9CodecInfo:this.internalTrack.info.codec==="vp9"&&e?hn(e.data):null,av1CodecInfo:this.internalTrack.info.codec==="av1"&&e?yi(e.data):null,proresCodecInfo:this.internalTrack.info.codec==="prores"&&e?pn(e.data):null,proresFormat:this.internalTrack.info.proresFormat};if(!ci(this.internalTrack.info.colorSpace)){let a=Un(i);this.internalTrack.info.colorSpace.primaries??=a.primaries,this.internalTrack.info.colorSpace.transfer??=a.transfer,this.internalTrack.info.colorSpace.matrix??=a.matrix,this.internalTrack.info.colorSpace.fullRange??=a.fullRange}let n={codec:ar(i),codedWidth:this.internalTrack.info.width,codedHeight:this.internalTrack.info.height,description:this.internalTrack.info.codecDescription??void 0,colorSpace:this.internalTrack.info.colorSpace};return(this.internalTrack.info.width!==this.internalTrack.info.squarePixelWidth||this.internalTrack.info.height!==this.internalTrack.info.squarePixelHeight)&&(n.displayAspectWidth=this.internalTrack.info.squarePixelWidth,n.displayAspectHeight=this.internalTrack.info.squarePixelHeight),n})():null}},oa=class extends Hn{constructor(e){super(e),this.decoderConfigPromise=null}getType(){return"audio"}getCodec(){return this.internalTrack.info.codec}getNumberOfChannels(){return this.internalTrack.info.numberOfChannels}getSampleRate(){return this.internalTrack.info.sampleRate}async getDecoderConfig(){return this.internalTrack.info.codec?this.decoderConfigPromise??=(async()=>{if(this.internalTrack.info.codec==="dts"&&!this.internalTrack.info.dtsFormat){let e=await this.getFirstPacket({});this.internalTrack.info.dtsFormat=e&&Pn(e.data)}return{codec:Ir({codec:this.internalTrack.info.codec,codecDescription:this.internalTrack.info.codecDescription,aacCodecInfo:this.internalTrack.info.aacCodecInfo,dtsFormat:this.internalTrack.info.dtsFormat}),numberOfChannels:this.internalTrack.info.numberOfChannels,sampleRate:this.internalTrack.info.sampleRate,description:this.internalTrack.info.codecDescription??void 0}})():null}};var or;(function(r){r[r.Unsynchronisation=128]="Unsynchronisation",r[r.ExtendedHeader=64]="ExtendedHeader",r[r.ExperimentalIndicator=32]="ExperimentalIndicator",r[r.Footer=16]="Footer"})(or||(or={}));var Dr;(function(r){r[r.ISO_8859_1=0]="ISO_8859_1",r[r.UTF_16_WITH_BOM=1]="UTF_16_WITH_BOM",r[r.UTF_16_BE_NO_BOM=2]="UTF_16_BE_NO_BOM",r[r.UTF_8=3]="UTF_8"})(Dr||(Dr={}));var vi=128,me=10,Or=["Blues","Classic rock","Country","Dance","Disco","Funk","Grunge","Hip-hop","Jazz","Metal","New age","Oldies","Other","Pop","Rhythm and blues","Rap","Reggae","Rock","Techno","Industrial","Alternative","Ska","Death metal","Pranks","Soundtrack","Euro-techno","Ambient","Trip-hop","Vocal","Jazz & funk","Fusion","Trance","Classical","Instrumental","Acid","House","Game","Sound clip","Gospel","Noise","Alternative rock","Bass","Soul","Punk","Space","Meditative","Instrumental pop","Instrumental rock","Ethnic","Gothic","Darkwave","Techno-industrial","Electronic","Pop-folk","Eurodance","Dream","Southern rock","Comedy","Cult","Gangsta","Top 40","Christian rap","Pop/funk","Jungle music","Native US","Cabaret","New wave","Psychedelic","Rave","Showtunes","Trailer","Lo-fi","Tribal","Acid punk","Acid jazz","Polka","Retro","Musical","Rock 'n' roll","Hard rock","Folk","Folk rock","National folk","Swing","Fast fusion","Bebop","Latin","Revival","Celtic","Bluegrass","Avantgarde","Gothic rock","Progressive rock","Psychedelic rock","Symphonic rock","Slow rock","Big band","Chorus","Easy listening","Acoustic","Humour","Speech","Chanson","Opera","Chamber music","Sonata","Symphony","Booty bass","Primus","Porn groove","Satire","Slow jam","Club","Tango","Samba","Folklore","Ballad","Power ballad","Rhythmic Soul","Freestyle","Duet","Punk rock","Drum solo","A cappella","Euro-house","Dance hall","Goa music","Drum & bass","Club-house","Hardcore techno","Terror","Indie","Britpop","Negerpunk","Polsk punk","Beat","Christian gangsta rap","Heavy metal","Black metal","Crossover","Contemporary Christian","Christian rock","Merengue","Salsa","Thrash metal","Anime","Jpop","Synthpop","Christmas","Art rock","Baroque","Bhangra","Big beat","Breakbeat","Chillout","Downtempo","Dub","EBM","Eclectic","Electro","Electroclash","Emo","Experimental","Garage","Global","IDM","Illbient","Industro-Goth","Jam Band","Krautrock","Leftfield","Lounge","Math rock","New romantic","Nu-breakz","Post-punk","Post-rock","Psytrance","Shoegaze","Space rock","Trop rock","World music","Neoclassical","Audiobook","Audio theatre","Neue Deutsche Welle","Podcast","Indie rock","G-Funk","Dubstep","Garage rock","Psybient"],oc=(r,e)=>{let t=r.filePos;e.raw??={},e.raw.TAG??=M(r,vi-3),r.filePos=t;let i=Mr(r,30);i&&(e.title??=i);let n=Mr(r,30);n&&(e.artist??=n);let a=Mr(r,30);a&&(e.album??=a);let s=Mr(r,4),o=Number.parseInt(s,10);Number.isInteger(o)&&o>0&&(e.date??=new Date(String(o)));let c=M(r,30),l;if(c[28]===0&&c[29]!==0){let d=c[29];d>0&&(e.trackNumber??=d),r.skip(-30),l=Mr(r,28),r.skip(2)}else r.skip(-30),l=Mr(r,30);l&&(e.comment??=l);let u=U(r);u<Or.length&&(e.genre??=Or[u])},Mr=(r,e)=>{let t=M(r,e),i=er(t.indexOf(0),t.length),n=t.subarray(0,i),a="";for(let s=0;s<n.length;s++)a+=String.fromCharCode(n[s]);return a.trimEnd()},Ie=r=>{let e=r.filePos,t=J(r,3),i=U(r),n=U(r),a=U(r),s=B(r);if(t!=="ID3"||i===255||n===255||(s&2155905152)!==0)return r.filePos=e,null;let o=an(s);return a&or.Footer&&(o+=me),{majorVersion:i,revision:n,flags:a,size:o}},Ht=(r,e,t)=>{if(![2,3,4].includes(e.majorVersion)){H._warn(`Unsupported ID3v2 major version: ${e.majorVersion}`);return}let i=e.flags&or.Footer?e.size-me:e.size,n=M(r,i),a=new ca(e,n);if(e.flags&or.Unsynchronisation&&e.majorVersion===3&&a.ununsynchronizeAll(),e.flags&or.ExtendedHeader){if(a.bytes.length<4)return;let s=a.readU32();e.majorVersion===3?a.pos+=s:a.pos+=s-4}for(;a.pos<=a.bytes.length-a.frameHeaderSize();){let s=a.readId3V2Frame();if(!s)break;let o=a.pos,c=Math.min(a.pos+s.size,a.bytes.length),l=c,u=!1,d=!1,f=!1;if(e.majorVersion===3?(u=!!(s.flags&64),d=!!(s.flags&128)):e.majorVersion===4&&(u=!!(s.flags&4),d=!!(s.flags&8),f=!!(s.flags&2)||!!(e.flags&or.Unsynchronisation)),u){H._warn(`Skipping encrypted ID3v2 frame ${s.id}`),a.pos=c;continue}if(d){H._warn(`Skipping compressed ID3v2 frame ${s.id}`),a.pos=c;continue}f&&(l=a.ununsynchronizeRegion(a.pos,l));let m=p=>{if(l-a.pos<p)throw new Error(`Invalid ID3v2 ${s.id} frame: too short.`)};if(t.raw??={},s.id==="TXXX"){let p=t.raw.TXXX??={};m(1);let h=a.readId3V2TextEncoding(),k=a.readId3V2Text(h,l),w=a.readId3V2Text(h,l);p[k]??=w}else if(s.id[0]==="T")t.raw[s.id]??=a.readId3V2EncodingAndText(l);else{let p=a.readBytes(l-a.pos),h=t.raw[s.id];h instanceof Uint8Array?t.raw[s.id]=[h,p]:Array.isArray(h)?h.push(p):t.raw[s.id]??=p}switch(a.pos=o,s.id){case"TIT2":case"TT2":t.title??=a.readId3V2EncodingAndText(l);break;case"TIT3":case"TT3":t.description??=a.readId3V2EncodingAndText(l);break;case"TPE1":case"TP1":t.artist??=a.readId3V2EncodingAndText(l);break;case"TALB":case"TAL":t.album??=a.readId3V2EncodingAndText(l);break;case"TPE2":case"TP2":t.albumArtist??=a.readId3V2EncodingAndText(l);break;case"TRCK":case"TRK":{let h=a.readId3V2EncodingAndText(l).split("/"),k=Number.parseInt(h[0],10),w=h[1]&&Number.parseInt(h[1],10);Number.isInteger(k)&&k>0&&(t.trackNumber??=k),w&&Number.isInteger(w)&&w>0&&(t.tracksTotal??=w)}break;case"TPOS":case"TPA":{let h=a.readId3V2EncodingAndText(l).split("/"),k=Number.parseInt(h[0],10),w=h[1]&&Number.parseInt(h[1],10);Number.isInteger(k)&&k>0&&(t.discNumber??=k),w&&Number.isInteger(w)&&w>0&&(t.discsTotal??=w)}break;case"TCON":case"TCO":{let p=a.readId3V2EncodingAndText(l),h=/^\((\d+)\)/.exec(p);if(h){let k=Number.parseInt(h[1]);if(Or[k]!==void 0){t.genre??=Or[k];break}}if(h=/^\d+$/.exec(p),h){let k=Number.parseInt(h[0]);if(Or[k]!==void 0){t.genre??=Or[k];break}}t.genre??=p}break;case"TDRC":case"TDAT":{let p=a.readId3V2EncodingAndText(l),h=new Date(p);Number.isNaN(h.getTime())||(t.date??=h)}break;case"TYER":case"TYE":{let p=a.readId3V2EncodingAndText(l),h=Number.parseInt(p,10);Number.isInteger(h)&&(t.date??=new Date(String(h)))}break;case"TBPM":case"TBP":{let p=a.readId3V2EncodingAndText(l),h=Number.parseInt(p,10);Number.isInteger(h)&&(t.beatsPerMinute??=h)}break;case"USLT":case"ULT":{m(4);let p=a.readU8();a.pos+=3,a.readId3V2Text(p,l),t.lyrics??=a.readId3V2Text(p,l)}break;case"COMM":case"COM":{m(4);let p=a.readU8();a.pos+=3,a.readId3V2Text(p,l),t.comment??=a.readId3V2Text(p,l)}break;case"APIC":case"PIC":{m(1);let p=a.readId3V2TextEncoding(),h;if(e.majorVersion===2){m(3);let b=a.readAscii(3);h=b==="PNG"?"image/png":b==="JPG"?"image/jpeg":"image/*"}else h=a.readId3V2Text(p,l);m(1);let k=a.readU8(),w=a.readId3V2Text(p,l).trimEnd(),S=l-a.pos;if(S>=0){let b=a.readBytes(S);t.images||(t.images=[]),t.images.push({data:b,mimeType:h,kind:k===3?"coverFront":k===4?"coverBack":"unknown",description:w})}}break;default:a.pos+=s.size;break}a.pos=c}},ca=class{constructor(e,t){this.header=e,this.bytes=t,this.pos=0,this.ownsBytes=!1,this.view=new DataView(t.buffer,t.byteOffset,t.byteLength)}frameHeaderSize(){return this.header.majorVersion===2?6:10}ununsynchronizeAll(){let e=[];for(let t=0;t<this.bytes.length;t++){let i=this.bytes[t];e.push(i),i===255&&t!==this.bytes.length-1&&this.bytes[t]===0&&t++}this.bytes=new Uint8Array(e),this.view=new DataView(this.bytes.buffer)}ununsynchronizeRegion(e,t){this.ownsBytes||(this.bytes=this.bytes.slice(),this.view=W(this.bytes),this.ownsBytes=!0);let i=e;for(let n=e;n<t;n++){let a=this.bytes[n];this.bytes[i++]=a,a===255&&n!==t-1&&this.bytes[n+1]===0&&n++}return i}readBytes(e){let t=this.bytes.subarray(this.pos,this.pos+e);return this.pos+=e,t}readU8(){let e=this.view.getUint8(this.pos);return this.pos+=1,e}readU16(){let e=this.view.getUint16(this.pos,!1);return this.pos+=2,e}readU24(){let e=this.view.getUint16(this.pos,!1),t=this.view.getUint8(this.pos+2);return this.pos+=3,e*256+t}readU32(){let e=this.view.getUint32(this.pos,!1);return this.pos+=4,e}readAscii(e){let t="";for(let i=0;i<e;i++)t+=String.fromCharCode(this.view.getUint8(this.pos+i));return this.pos+=e,t}readId3V2Frame(){if(this.header.majorVersion===2){let e=this.readAscii(3);if(e==="\0\0\0")return null;let t=this.readU24();return{id:e,size:t,flags:0}}else{let e=this.readAscii(4);if(e==="\0\0\0\0")return null;let t=this.readU32(),i=this.header.majorVersion===4?an(t):t,n=this.readU16(),a=this.pos,s=o=>{let c=this.pos+o;if(c>this.bytes.length)return!1;if(c<=this.bytes.length-this.frameHeaderSize()){this.pos+=o;let l=this.readAscii(4);if(l!=="\0\0\0\0"&&!/[0-9A-Z]{4}/.test(l))return!1}return!0};if(!s(i)){let o=this.header.majorVersion===4?t:an(t);s(o)&&(i=o)}return this.pos=a,{id:e,size:i,flags:n}}}readId3V2TextEncoding(){let e=this.readU8();if(e>3)throw new Error(`Unsupported text encoding: ${e}`);return e}readId3V2Text(e,t){let i=this.pos,n=this.readBytes(t-this.pos);switch(e){case Dr.ISO_8859_1:{let a="";for(let s=0;s<n.length;s++){let o=n[s];if(o===0){this.pos=i+s+1;break}a+=String.fromCharCode(o)}return a}case Dr.UTF_16_WITH_BOM:if(n[0]===255&&n[1]===254){let a=new $t("utf-16le"),s=er(n.findIndex((o,c)=>o===0&&n[c+1]===0&&c%2===0),n.length);return this.pos=i+Math.min(s+2,n.length),a.decode(n.subarray(2,s))}else if(n[0]===254&&n[1]===255){let a=new $t("utf-16be"),s=er(n.findIndex((o,c)=>o===0&&n[c+1]===0&&c%2===0),n.length);return this.pos=i+Math.min(s+2,n.length),a.decode(n.subarray(2,s))}else{let a=er(n.findIndex(s=>s===0),n.length);return this.pos=i+Math.min(a+1,n.length),ie.decode(n.subarray(0,a))}case Dr.UTF_16_BE_NO_BOM:{let a=new $t("utf-16be"),s=er(n.findIndex((o,c)=>o===0&&n[c+1]===0&&c%2===0),n.length);return this.pos=i+Math.min(s+2,n.length),a.decode(n.subarray(0,s))}case Dr.UTF_8:{let a=er(n.findIndex(s=>s===0),n.length);return this.pos=i+Math.min(a+1,n.length),ie.decode(n.subarray(0,a))}}}readId3V2EncodingAndText(e){if(this.pos>=e)return"";let t=this.readId3V2TextEncoding();return this.readId3V2Text(t,e)}};var Ri=async(r,e,t,i=null)=>{let a=e;for(;t===null||a<t;){let s=t!==null?Math.min(65536,t-a):65536,o=r.requestSliceRange(a,4,s);if(P(o)&&(o=await o),!o||o.length<4)break;for(;o.remainingLength>=4;){let c=o.filePos,l=B(o),u=r.fileSize!==null?r.fileSize-a:null,d=gi(l,u);if(d.header&&(!i||d.header.sampleRate===i.sampleRate&&d.header.mpegVersionId===i.mpegVersionId&&d.header.layer===i.layer&&Ot(d.header.channel)===Ot(i.channel)))return{header:d.header,startPos:a};o.filePos=c+d.bytesAdvanced,a=o.filePos}}return null};var Wn=class extends le{constructor(e){super(e),this.metadataPromise=null,this.firstFrameHeader=null,this.firstFrameHeaderPos=null,this.xingFrameHeader=null,this.xingFrameHeaderPos=null,this.loadedSamples=[],this.metadataTags=null,this.xingData=null,this.trackBackings=[],this.readingMutex=new Pe,this.lastSampleLoaded=!1,this.lastLoadedPos=0,this.nextTimestampInSamples=0,this.primingDelay=0,this.reader=e._reader}async readMetadata(){return this.metadataPromise??=(async()=>{for(;!this.firstFrameHeader&&!this.lastSampleLoaded;)await this.advanceReader();if(!this.firstFrameHeader&&this.xingFrameHeader&&(this.firstFrameHeader=this.xingFrameHeader,this.firstFrameHeaderPos=this.xingFrameHeaderPos),!this.firstFrameHeader)throw new Error("No valid MP3 frame found.");this.trackBackings=[new la(this)]})()}async advanceReader(){if(this.lastLoadedPos===0)for(;;){let o=this.reader.requestSlice(this.lastLoadedPos,me);if(P(o)&&(o=await o),!o){this.lastSampleLoaded=!0;return}let c=Ie(o);if(!c)break;this.lastLoadedPos=o.filePos+c.size}let e=await Ri(this.reader,this.lastLoadedPos,this.reader.fileSize,this.firstFrameHeader);if(!e){this.lastSampleLoaded=!0;return}let t=e.header;this.lastLoadedPos=e.startPos+t.totalSize-1;let i=sn(t.mpegVersionId,t.channel),n=this.reader.requestSlice(e.startPos+i,4);if(P(n)&&(n=await n),n){let o=B(n);if(o===pi||o===nn){if(this.xingFrameHeader||(this.xingFrameHeader=t,this.xingFrameHeaderPos=e.startPos),!this.xingData){let l=this.reader.requestSlice(e.startPos+i+4,12);if(P(l)&&(l=await l),l){let u=M(l,12),d=W(u),f=d.getUint32(0,!1);this.xingData={isVbr:o===pi,frameCount:f&yt.FrameCount?d.getUint32(4,!1):null,fileSize:f&yt.FileSize?d.getUint32(8,!1):null};let m=e.startPos+i+8+(f&yt.FrameCount?4:0)+(f&yt.FileSize?4:0)+(f&yt.Toc?100:0)+(f&yt.Quality?4:0);if(!this.firstFrameHeader&&m+24<=e.startPos+t.totalSize){let p=this.reader.requestSlice(m,24);if(P(p)&&(p=await p),p){let h=M(p,24),k=String.fromCharCode(...h.subarray(0,4));(k==="LAME"||k==="Lavf"||k==="Lavc")&&(this.primingDelay=(h[21]<<4|h[22]>>4)+529,this.nextTimestampInSamples=-this.primingDelay)}}}}return}}this.firstFrameHeader||(this.firstFrameHeader=t,this.firstFrameHeaderPos=e.startPos);let a=t.audioSamplesInFrame/this.firstFrameHeader.sampleRate,s={timestamp:this.nextTimestampInSamples/this.firstFrameHeader.sampleRate,duration:a,dataStart:e.startPos,dataSize:t.totalSize};this.loadedSamples.push(s),this.nextTimestampInSamples+=t.audioSamplesInFrame}async getMimeType(){return"audio/mpeg"}async getTrackBackings(){return await this.readMetadata(),this.trackBackings}async getMetadataTags(){let e=await this.readingMutex.acquire();try{if(await this.readMetadata(),this.metadataTags)return this.metadataTags;this.metadataTags={};let t=0,i=!1;for(;;){let n=this.reader.requestSlice(t,me);if(P(n)&&(n=await n),!n)break;let a=Ie(n);if(!a)break;i=!0;let s=this.reader.requestSlice(n.filePos,a.size);if(P(s)&&(s=await s),!s)break;Ht(s,a,this.metadataTags),t=n.filePos+a.size}if(!i&&this.reader.fileSize!==null&&this.reader.fileSize>=vi){let n=this.reader.requestSlice(this.reader.fileSize-vi,vi);P(n)&&(n=await n),g(n),J(n,3)==="TAG"&&oc(n,this.metadataTags)}return this.metadataTags}finally{e()}}},la=class{constructor(e){this.demuxer=e}getType(){return"audio"}getId(){return 1}getNumber(){return 1}getTimeResolution(){return g(this.demuxer.firstFrameHeader),this.demuxer.firstFrameHeader.sampleRate}isRelativeToUnixEpoch(){return!1}getUnixTimeForTimestamp(){return null}getPairingMask(){return 1n}getBitrate(){return null}getAverageBitrate(){return null}async getDurationFromMetadata(){let e=this.demuxer;if(g(e.firstFrameHeader!==null),g(e.firstFrameHeaderPos!==null),e.xingData&&e.xingData.frameCount!==null)return(e.xingData.frameCount*e.firstFrameHeader.audioSamplesInFrame-e.primingDelay)/e.firstFrameHeader.sampleRate;if(!e.xingData?.isVbr&&e.reader.fileSize!==null){let t=mo(e.firstFrameHeader.lowSamplingFrequency,e.firstFrameHeader.layer,e.firstFrameHeader.bitrate,e.firstFrameHeader.sampleRate),i=(e.reader.fileSize-e.firstFrameHeaderPos)/t;return(Math.round(i)*e.firstFrameHeader.audioSamplesInFrame-e.primingDelay)/e.firstFrameHeader.sampleRate}return null}async getLiveRefreshInterval(){return null}getName(){return null}getLanguageCode(){return ne}getCodec(){return"mp3"}getInternalCodecId(){return null}getNumberOfChannels(){return g(this.demuxer.firstFrameHeader),Ot(this.demuxer.firstFrameHeader.channel)}getSampleRate(){return g(this.demuxer.firstFrameHeader),this.demuxer.firstFrameHeader.sampleRate}getDisposition(){return{...fe}}async getDecoderConfig(){return g(this.demuxer.firstFrameHeader),{codec:"mp3",numberOfChannels:Ot(this.demuxer.firstFrameHeader.channel),sampleRate:this.demuxer.firstFrameHeader.sampleRate}}async getPacketAtIndex(e,t){if(e===-1)return null;let i=this.demuxer.loadedSamples[e];if(!i)return null;let n;if(t.metadataOnly)n=ce;else{let a=this.demuxer.reader.requestSlice(i.dataStart,i.dataSize);if(P(a)&&(a=await a),!a)return null;n=M(a,i.dataSize)}return new Y(n,"key",i.timestamp,i.duration,e,i.dataSize)}getFirstPacket(e){return this.getPacketAtIndex(0,e)}async getNextPacket(e,t){let i=await this.demuxer.readingMutex.acquire();try{let n=pt(this.demuxer.loadedSamples,e.timestamp,s=>s.timestamp);if(n===-1)throw new Error("Packet was not created from this track.");let a=n+1;for(;a>=this.demuxer.loadedSamples.length&&!this.demuxer.lastSampleLoaded;)await this.demuxer.advanceReader();return this.getPacketAtIndex(a,t)}finally{i()}}async getPacket(e,t){let i=await this.demuxer.readingMutex.acquire();try{for(;;){let n=Q(this.demuxer.loadedSamples,e,a=>a.timestamp);if(n===-1&&this.demuxer.loadedSamples.length>0)return null;if(this.demuxer.lastSampleLoaded)return this.getPacketAtIndex(n,t);if(n>=0&&n+1<this.demuxer.loadedSamples.length)return this.getPacketAtIndex(n,t);await this.demuxer.advanceReader()}}finally{i()}}getKeyPacket(e,t){return this.getPacket(e,t)}getNextKeyPacket(e,t){return this.getNextPacket(e,t)}};var ua=1399285583,ku=79764919,yu=new Uint32Array(256);for(let r=0;r<256;r++){let e=r<<24;for(let t=0;t<8;t++)e=e&2147483648?e<<1^ku:e<<1;yu[r]=e>>>0&4294967295}var da=(r,e,t)=>{let i=0,n=null;if(r.length>0)if(e.codec==="vorbis"){g(e.vorbisInfo);let a=e.vorbisInfo.modeBlockflags.length,o=(1<<no(a-1))-1<<1,c=(r[0]&o)>>1;if(c>=e.vorbisInfo.modeBlockflags.length)throw new Error("Invalid mode number.");let l=t??e.vorbisInfo.blocksizes[0],u=e.vorbisInfo.modeBlockflags[c];if(n=e.vorbisInfo.blocksizes[u],u===1){let d=(o|1)+1,f=r[0]&d?1:0;l=e.vorbisInfo.blocksizes[f]}i=l+n>>2}else e.codec==="opus"&&(i=kn(r).durationInSamples);return{durationInSamples:i,vorbisBlockSize:n}},cc=r=>{let e="audio/ogg";if(r.codecStrings){let t=[...new Set(r.codecStrings)];e+=`; codecs="${t.join(", ")}"`}return e};var Ct=27,cr=282,lc=cr+65025,Ur=r=>{let e=r.filePos;if(Wt(r)!==ua)return null;r.skip(1);let i=U(r),n=dc(r),a=Wt(r),s=Wt(r),o=Wt(r),c=U(r);if(c===0||r.remainingLength<c)return null;let l=new Uint8Array(c);for(let m=0;m<c;m++)l[m]=U(r);let u=27+c,d=l.reduce((m,p)=>m+p,0),f=u+d;return{headerStartPos:e,totalSize:f,dataStartPos:e+u,dataSize:d,headerType:i,granulePosition:n,serialNumber:a,sequenceNumber:s,checksum:o,lacingValues:l}},uc=(r,e,t)=>{for(;r.filePos<e-3;){let i=Wt(r),n=i&255,a=i>>>8&255,s=i>>>16&255,o=i>>>24&255,c=79;if(!(n!==c&&a!==c&&s!==c&&o!==c)){if(r.skip(-4),i===ua){if(t===void 0||r.filePos+18>r.end)return!0;r.skip(14);let l=Wt(r);if(r.skip(-18),l===t)return!0}r.skip(1)}}return!1};var fc=64,wu=30,bu=19,qn=class extends le{constructor(e){super(e),this.metadataPromise=null,this.bitstreams=[],this.trackBackings=[],this.metadataTags={},this.reader=e._reader}async readMetadata(){return this.metadataPromise??=(async()=>{let e=0;for(;;){let t=this.reader.requestSliceRange(e,Ct,cr);if(P(t)&&(t=await t),!t)break;let i=Ur(t);if(!i||!!!(i.headerType&2))break;if(this.bitstreams.length===fc)throw new Error(`Too many (> ${fc}) logical bitstreams.`);this.bitstreams.push({serialNumber:i.serialNumber,bosPage:i,description:null,numberOfChannels:-1,sampleRate:-1,codecInfo:{codec:null,vorbisInfo:null,opusInfo:null},lastMetadataPacket:null}),e=i.headerStartPos+i.totalSize}for(let t of this.bitstreams){let i=await this.readPacket(t.bosPage,0);i&&(i.data.byteLength>=wu&&i.data[0]===1&&i.data[1]===118&&i.data[2]===111&&i.data[3]===114&&i.data[4]===98&&i.data[5]===105&&i.data[6]===115?await this.readVorbisMetadata(i,t):i.data.byteLength>=bu&&i.data[0]===79&&i.data[1]===112&&i.data[2]===117&&i.data[3]===115&&i.data[4]===72&&i.data[5]===101&&i.data[6]===97&&i.data[7]===100&&await this.readOpusMetadata(i,t),t.codecInfo.codec!==null&&this.trackBackings.push(new fa(t,this)))}})()}async readVorbisMetadata(e,t){let i=await this.findNextPacketStart(e);if(!i)return;let n=await this.readPacket(i.startPage,i.startSegmentIndex);if(!n||(i=await this.findNextPacketStart(n),!i))return;let a=await this.readPacket(i.startPage,i.startSegmentIndex);if(!a||n.data[0]!==3||a.data[0]!==5)return;let s=W(e.data),o=s.getUint8(11),c=s.getUint32(12,!0);if(o===0||c===0)throw new Error("Invalid Vorbis identification header: channel count and sample rate must not be 0.");let l=[],u=m=>{for(;l.push(Math.min(255,m)),!(m<255);)m-=255};u(e.data.length),u(n.data.length);let d=new Uint8Array(1+l.length+e.data.length+n.data.length+a.data.length);d[0]=2,d.set(l,1),d.set(e.data,1+l.length),d.set(n.data,1+l.length+e.data.length),d.set(a.data,1+l.length+e.data.length+n.data.length),t.codecInfo.codec="vorbis",t.description=d,t.lastMetadataPacket=a,t.numberOfChannels=o,t.sampleRate=c;let f=s.getUint8(28);t.codecInfo.vorbisInfo={blocksizes:[1<<(f&15),1<<(f>>4)],modeBlockflags:Po(a.data).modeBlockflags},wi(n.data.subarray(7),this.metadataTags)}async readOpusMetadata(e,t){let i=await this.findNextPacketStart(e);if(!i)return;let n=await this.readPacket(i.startPage,i.startSegmentIndex);if(!n)return;t.codecInfo.codec="opus",t.description=e.data,t.lastMetadataPacket=n;let a=gn(e.data);t.numberOfChannels=a.outputChannelCount,t.sampleRate=ct,t.codecInfo.opusInfo={preSkip:a.preSkip},wi(n.data.subarray(8),this.metadataTags)}async readPacket(e,t){g(t<e.lacingValues.length);let i=0;for(let d=0;d<t;d++)i+=e.lacingValues[d];let n=e,a=i,s=t,o=[];e:for(;;){let d=this.reader.requestSlice(n.dataStartPos,n.dataSize);if(P(d)&&(d=await d),!d)return null;let f=M(d,n.dataSize);for(;;){if(s===n.lacingValues.length){o.push(f.subarray(i,a));break}let p=n.lacingValues[s];if(a+=p,p<255){o.push(f.subarray(i,a));break e}s++}let m=n.headerStartPos+n.totalSize;for(;;){let p=this.reader.requestSliceRange(m,Ct,cr);if(P(p)&&(p=await p),!p)return null;let h=Ur(p);if(!h)return null;if(n=h,n.serialNumber===e.serialNumber)break;m=n.headerStartPos+n.totalSize}i=0,a=0,s=0}let c=o.reduce((d,f)=>d+f.length,0);if(c===0)return null;let l=new Uint8Array(c),u=0;for(let d=0;d<o.length;d++){let f=o[d];l.set(f,u),u+=f.length}return{data:l,endPage:n,endSegmentIndex:s}}async findNextPacketStart(e){if(e.endSegmentIndex<e.endPage.lacingValues.length-1)return{startPage:e.endPage,startSegmentIndex:e.endSegmentIndex+1};if(!!(e.endPage.headerType&4))return null;let i=e.endPage.headerStartPos+e.endPage.totalSize;for(;;){let n=this.reader.requestSliceRange(i,Ct,cr);if(P(n)&&(n=await n),!n)return null;let a=Ur(n);if(!a)return null;if(a.serialNumber===e.endPage.serialNumber)return{startPage:a,startSegmentIndex:0};i=a.headerStartPos+a.totalSize}}async getMimeType(){await this.readMetadata();let e=await Promise.all(this.trackBackings.map(t=>t.getDecoderConfig().then(i=>i?.codec??null)));return cc({codecStrings:e.filter(Boolean)})}async getTrackBackings(){return await this.readMetadata(),this.trackBackings}async getMetadataTags(){return await this.readMetadata(),this.metadataTags}},fa=class{constructor(e,t){this.bitstream=e,this.demuxer=t,this.encodedPacketToMetadata=new WeakMap,this.sequentialScanCache=[],this.sequentialScanMutex=new Pe,this.firstTimestampInSamplesPromise=null,this.internalSampleRate=e.codecInfo.codec==="opus"?ct:e.sampleRate}getType(){return"audio"}getId(){return this.bitstream.serialNumber}getNumber(){let e=this.demuxer.trackBackings.findIndex(t=>t.bitstream===this.bitstream);return g(e!==-1),e+1}getNumberOfChannels(){return this.bitstream.numberOfChannels}getSampleRate(){return this.bitstream.sampleRate}getTimeResolution(){return this.bitstream.sampleRate}isRelativeToUnixEpoch(){return!1}getUnixTimeForTimestamp(){return null}getPairingMask(){return 1n}getBitrate(){return null}getAverageBitrate(){return null}async getDurationFromMetadata(){return null}async getLiveRefreshInterval(){return null}getCodec(){return this.bitstream.codecInfo.codec}getInternalCodecId(){return null}async getDecoderConfig(){return g(this.bitstream.codecInfo.codec),{codec:this.bitstream.codecInfo.codec,numberOfChannels:this.bitstream.numberOfChannels,sampleRate:this.bitstream.sampleRate,description:this.bitstream.description??void 0}}getName(){return null}getLanguageCode(){return ne}getDisposition(){return{...fe,primary:!1}}granulePositionToTimestampInSamples(e){return this.bitstream.codecInfo.codec==="opus"?(g(this.bitstream.codecInfo.opusInfo),e-this.bitstream.codecInfo.opusInfo.preSkip):e}createEncodedPacketFromOggPacket(e,t,i){if(!e)return null;let n=da(e.data,this.bitstream.codecInfo,t.vorbisLastBlocksize),{vorbisBlockSize:a}=n,{durationInSamples:s}=n;if(!!(e.endPage.headerType&4)&&e.endSegmentIndex===e.endPage.lacingValues.length-1){let l=this.granulePositionToTimestampInSamples(e.endPage.granulePosition);s=st(l-t.timestampInSamples,0,s)}let c=new Y(i.metadataOnly?ce:e.data,"key",t.timestampInSamples/this.internalSampleRate,s/this.internalSampleRate,e.endPage.headerStartPos+e.endSegmentIndex,e.data.byteLength);return this.encodedPacketToMetadata.set(c,{packet:e,timestampInSamples:t.timestampInSamples,durationInSamples:s,vorbisLastBlockSize:t.vorbisLastBlocksize,vorbisBlockSize:a}),c}getFirstTimestampInSamples(){return this.firstTimestampInSamplesPromise??=(async()=>{let e=this.granulePositionToTimestampInSamples(0);g(this.bitstream.lastMetadataPacket);let t=await this.demuxer.findNextPacketStart(this.bitstream.lastMetadataPacket);if(!t)return e;let i=null,n=0,a=null,s=null;for(;t;){let c=await this.demuxer.readPacket(t.startPage,t.startSegmentIndex);if(!c||(i??=c.endPage,c.endPage.headerStartPos!==i.headerStartPos))break;let{durationInSamples:l,vorbisBlockSize:u}=da(c.data,this.bitstream.codecInfo,s);n+=l,a??=l,s=u,t=await this.demuxer.findNextPacketStart(c)}if(!i)return e;g(a!==null);let o=this.bitstream.codecInfo.codec==="vorbis"?-a:0;return e+Math.max(i.granulePosition-n,o)})()}async getFirstPacket(e){g(this.bitstream.lastMetadataPacket);let t=await this.demuxer.findNextPacketStart(this.bitstream.lastMetadataPacket);if(!t)return null;let i=await this.getFirstTimestampInSamples(),n=await this.demuxer.readPacket(t.startPage,t.startSegmentIndex);return this.createEncodedPacketFromOggPacket(n,{timestampInSamples:i,vorbisLastBlocksize:null},e)}async getNextPacket(e,t){let i=this.encodedPacketToMetadata.get(e);if(!i)throw new Error("Packet was not created from this track.");let n=await this.demuxer.findNextPacketStart(i.packet);if(!n)return null;let a=i.timestampInSamples+i.durationInSamples,s=await this.demuxer.readPacket(n.startPage,n.startSegmentIndex);return this.createEncodedPacketFromOggPacket(s,{timestampInSamples:a,vorbisLastBlocksize:i.vorbisBlockSize},t)}async getPacket(e,t){if(this.demuxer.reader.fileSize===null)return this.getPacketSequential(e,t);let i=kt(e*this.internalSampleRate),n=await this.getFirstTimestampInSamples();if(i===n)return this.getFirstPacket(t);if(i<n)return null;g(this.bitstream.lastMetadataPacket);let a=await this.demuxer.findNextPacketStart(this.bitstream.lastMetadataPacket);if(!a)return null;let s=a.startPage,o=this.demuxer.reader.fileSize,c=[s];e:for(;s.headerStartPos+s.totalSize<o;){let b=s.headerStartPos,T=Math.floor((b+o)/2),y=T;for(;;){let A=Math.min(y+lc,o-Ct),x=this.demuxer.reader.requestSlice(y,Math.max(A-y,0));if(P(x)&&(x=await x),!x||!uc(x,A,this.bitstream.serialNumber)){if(o<=T+Ct)break e;o=T+Ct;continue e}let C=x.filePos,E=this.demuxer.reader.requestSliceRange(C,Ct,cr);P(E)&&(E=await E);let I=E&&Ur(E);if(!I||I.serialNumber!==this.bitstream.serialNumber){y=C+4;continue}if(I.granulePosition===-1){y=I.headerStartPos+I.totalSize;continue}this.granulePositionToTimestampInSamples(I.granulePosition)>i?o=I.headerStartPos:(s=I,c.push(I));continue e}}let l=a.startPage;for(let b of c){if(b.granulePosition===s.granulePosition)break;(!l||b.headerStartPos>l.headerStartPos)&&(l=b)}let u=l,d=[u];for(;!(u.serialNumber===this.bitstream.serialNumber&&u.granulePosition===s.granulePosition);){let b=u.headerStartPos+u.totalSize,T=this.demuxer.reader.requestSliceRange(b,Ct,cr);P(T)&&(T=await T);let y=T&&Ur(T);if(!y){u=s,d.push(s);break}u=y,u.serialNumber===this.bitstream.serialNumber&&d.push(u)}let f=null,m,p,h=u,k=0;if(u.headerStartPos===a.startPage.headerStartPos)m=n,p=!0,f=0;else{g(u.granulePosition!==-1),m=0,p=!1;for(let y=u.lacingValues.length-1;y>=0;y--)if(u.lacingValues[y]<255){f=y+1;break}if(f===null)throw new Error("Invalid page with granule position: no packets end on this page.");k=f-1;let b={data:ce,endPage:h,endSegmentIndex:k},T=await this.demuxer.findNextPacketStart(b);if(T){let y=mc(d,u,f);g(y);let A=hc(d,y.page,y.segmentIndex);A?(u=A.page,f=A.segmentIndex):(u=T.startPage,f=T.startSegmentIndex)}else for(;;){let y=mc(d,u,f);if(!y)break;let A=hc(d,y.page,y.segmentIndex);if(!A)break;if(u=A.page,f=A.segmentIndex,y.page.headerStartPos!==h.headerStartPos){h=y.page,k=y.segmentIndex;break}}}let w=null,S=null;for(;u!==null;){g(f!==null);let b=await this.demuxer.readPacket(u,f);if(!b)break;if(!(u.headerStartPos===a.startPage.headerStartPos&&f<a.startSegmentIndex)){let A=this.createEncodedPacketFromOggPacket(b,{timestampInSamples:m,vorbisLastBlocksize:S?.vorbisBlockSize??null},t);g(A);let x=this.encodedPacketToMetadata.get(A);if(g(x),!p&&b.endPage.headerStartPos===h.headerStartPos&&b.endSegmentIndex===k?(m=this.granulePositionToTimestampInSamples(u.granulePosition),p=!0,A=this.createEncodedPacketFromOggPacket(b,{timestampInSamples:m-x.durationInSamples,vorbisLastBlocksize:S?.vorbisBlockSize??null},t),g(A),x=this.encodedPacketToMetadata.get(A),g(x)):m+=x.durationInSamples,w=A,S=x,p&&(m>i||x.timestampInSamples===i))break}let y=await this.demuxer.findNextPacketStart(b);if(!y)break;u=y.startPage,f=y.startSegmentIndex}return w}async getPacketSequential(e,t){let i=await this.sequentialScanMutex.acquire();try{let n=kt(e*this.internalSampleRate);e=n/this.internalSampleRate;let a=Q(this.sequentialScanCache,n,c=>c.timestampInSamples),s;if(a!==-1){let c=this.sequentialScanCache[a];s=this.createEncodedPacketFromOggPacket(c.packet,{timestampInSamples:c.timestampInSamples,vorbisLastBlocksize:c.vorbisLastBlockSize},t)}else if(s=await this.getFirstPacket(t),s&&s.timestamp>e)return null;let o=0;for(;s&&s.timestamp<e;){let c=await this.getNextPacket(s,t);if(!c||c.timestamp>e)break;if(s=c,o++,o===100){o=0;let l=this.encodedPacketToMetadata.get(s);g(l),this.sequentialScanCache.length>0&&g($(this.sequentialScanCache).timestampInSamples<=l.timestampInSamples),this.sequentialScanCache.push(l)}}return s}finally{i()}}getKeyPacket(e,t){return this.getPacket(e,t)}getNextKeyPacket(e,t){return this.getNextPacket(e,t)}},hc=(r,e,t)=>{let i=e,n=t;e:for(;;){for(n--,n;n>=0;n--)if(i.lacingValues[n]<255){n++;break e}if(g(n===-1),!(i.headerType&1)){n=0;break}let s=Ns(r,o=>o.headerStartPos<i.headerStartPos);if(!s)return null;i=s,n=i.lacingValues.length}if(g(n!==-1),n===i.lacingValues.length){let a=r[r.indexOf(i)+1];g(a),i=a,n=0}return{page:i,segmentIndex:n}},mc=(r,e,t)=>{if(t>0)return{page:e,segmentIndex:t-1};let i=Ns(r,n=>n.headerStartPos<e.headerStartPos);return i?{page:i,segmentIndex:i.lacingValues.length-1}:null};var Ae;(function(r){r[r.PCM=1]="PCM",r[r.IEEE_FLOAT=3]="IEEE_FLOAT",r[r.ALAW=6]="ALAW",r[r.MULAW=7]="MULAW",r[r.EXTENSIBLE=65534]="EXTENSIBLE"})(Ae||(Ae={}));var Kn=class extends le{constructor(e){super(e),this.metadataPromise=null,this.dataStart=-1,this.dataSize=-1,this.audioInfo=null,this.trackBackings=[],this.lastKnownPacketIndex=0,this.metadataTags={},this.reader=e._reader}async readMetadata(){return this.metadataPromise??=(async()=>{let e=this.reader.requestSlice(0,12);P(e)&&(e=await e),g(e);let t=J(e,4),i=t!=="RIFX",n=t==="RF64",a=Pt(e,i),s=n?this.reader.fileSize:Math.min(a+8,this.reader.fileSize??1/0);if(J(e,4)!=="WAVE")throw new Error("Invalid WAVE file - wrong format");let c=0,l=null,u=e.filePos;for(;s===null||u<s;){let f=this.reader.requestSlice(u,8);if(P(f)&&(f=await f),!f)break;let m=J(f,4),p=Pt(f,i),h=f.filePos;if(n&&c===0&&m!=="ds64")throw new Error('Invalid RF64 file: First chunk must be "ds64".');if(m==="fmt ")await this.parseFmtChunk(h,p,i);else if(m==="data"){if(l??=p,this.dataStart=f.filePos,this.dataSize=Math.max(Math.min(l,(s??1/0)-this.dataStart),0),this.reader.fileSize===null)break}else if(m==="ds64"){let k=this.reader.requestSlice(h,p);if(P(k)&&(k=await k),!k)break;if(p<16)throw new Error('Invalid RF64 file: "ds64" chunk is too small.');let w=ma(k,i);l=ma(k,i),s=Math.min(w+8,this.reader.fileSize??1/0)}else m==="LIST"?await this.parseListChunk(h,p,i):(m==="ID3 "||m==="id3 ")&&await this.parseId3Chunk(h,p);u=h+p+(p&1),c++}if(!this.audioInfo)throw new Error('Invalid WAVE file - missing "fmt " chunk');if(this.dataStart===-1)throw new Error('Invalid WAVE file - missing "data" chunk');let d=this.audioInfo.blockSizeInBytes;this.dataSize=Math.floor(this.dataSize/d)*d,this.trackBackings.push(new ha(this))})()}async parseFmtChunk(e,t,i){let n=this.reader.requestSlice(e,t);if(P(n)&&(n=await n),!n)return;if(t<14)throw new Error('Invalid WAVE file - "fmt " chunk is too small');let a=Nr(n,i),s=Nr(n,i),o=Pt(n,i);n.skip(4);let c=Nr(n,i);if(s===0||o===0||c===0)throw new Error("Invalid WAVE file - channel count, sample rate and block align must be positive");let l;if(t<16?l=8:l=Nr(n,i),t>=18&&a!==357){let u=Nr(n,i),d=t-18;if(Math.min(d,u)>=22&&a===Ae.EXTENSIBLE){n.skip(6);let m=M(n,16);a=m[0]|m[1]<<8}}if((a===Ae.MULAW||a===Ae.ALAW)&&(l=8),a!==Ae.PCM&&a!==Ae.IEEE_FLOAT&&a!==Ae.ALAW&&a!==Ae.MULAW)throw new Error(`Unsupported WAVE codec (format tag ${a}). Only integer/float PCM, A-law, and \u03BC-law are supported.`);if(a===Ae.PCM&&![8,16,24,32].includes(l))throw new Error(`Unsupported WAVE PCM bit depth (${l}). Only 8, 16, 24, and 32 bits are supported.`);if(a===Ae.IEEE_FLOAT&&![32,64].includes(l))throw new Error(`Unsupported WAVE float bit depth (${l}). Only 32 and 64 bits are supported.`);this.audioInfo={format:a,numberOfChannels:s,sampleRate:o,sampleSizeInBytes:Math.ceil(l/8),blockSizeInBytes:c}}async parseListChunk(e,t,i){if(t<4)return;let n=this.reader.requestSlice(e,t);if(P(n)&&(n=await n),!n)return;let a=J(n,4);if(a!=="INFO"&&a!=="INF0")return;let s=n.filePos;for(;s<=e+t-8;){n.filePos=s;let o=J(n,4),c=Pt(n,i);if(c>n.remainingLength)break;let l=M(n,c),u="";for(let d=0;d<l.length&&l[d]!==0;d++)u+=String.fromCharCode(l[d]);switch(this.metadataTags.raw??={},this.metadataTags.raw[o]=u,o){case"INAM":case"TITL":this.metadataTags.title??=u;break;case"TIT3":this.metadataTags.description??=u;break;case"IART":this.metadataTags.artist??=u;break;case"IPRD":this.metadataTags.album??=u;break;case"IPRT":case"ITRK":case"TRCK":{let d=u.split("/"),f=Number.parseInt(d[0],10),m=d[1]&&Number.parseInt(d[1],10);Number.isInteger(f)&&f>0&&(this.metadataTags.trackNumber??=f),m&&Number.isInteger(m)&&m>0&&(this.metadataTags.tracksTotal??=m)}break;case"ICRD":case"IDIT":{let d=new Date(u);Number.isNaN(d.getTime())||(this.metadataTags.date??=d)}break;case"YEAR":{let d=Number.parseInt(u,10);Number.isInteger(d)&&d>0&&(this.metadataTags.date??=new Date(d,0,1))}break;case"IGNR":case"GENR":this.metadataTags.genre??=u;break;case"ICMT":case"CMNT":case"COMM":this.metadataTags.comment??=u;break}s+=8+c+(c&1)}}async parseId3Chunk(e,t){if(t<me)return;let i=this.reader.requestSlice(e,t);if(P(i)&&(i=await i),!i)return;let n=Ie(i);if(n){let a=t-me;if(n.size=Math.min(n.size,a),n.size>0){let s=i.slice(e+me,n.size);Ht(s,n,this.metadataTags)}}}getCodec(){if(g(this.audioInfo),this.audioInfo.format===Ae.MULAW)return"ulaw";if(this.audioInfo.format===Ae.ALAW)return"alaw";if(this.audioInfo.format===Ae.PCM){if(this.audioInfo.sampleSizeInBytes===1)return"pcm-u8";if(this.audioInfo.sampleSizeInBytes===2)return"pcm-s16";if(this.audioInfo.sampleSizeInBytes===3)return"pcm-s24";if(this.audioInfo.sampleSizeInBytes===4)return"pcm-s32"}if(this.audioInfo.format===Ae.IEEE_FLOAT){if(this.audioInfo.sampleSizeInBytes===4)return"pcm-f32";if(this.audioInfo.sampleSizeInBytes===8)return"pcm-f64"}g(!1)}async getMimeType(){return"audio/wav"}async getTrackBackings(){return await this.readMetadata(),this.trackBackings}async getMetadataTags(){return await this.readMetadata(),this.metadataTags}},zr=2048,ha=class{constructor(e){this.demuxer=e}getType(){return"audio"}getId(){return 1}getNumber(){return 1}getCodec(){return this.demuxer.getCodec()}getInternalCodecId(){return g(this.demuxer.audioInfo),this.demuxer.audioInfo.format}async getDecoderConfig(){let e=this.demuxer.getCodec();return e?(g(this.demuxer.audioInfo),{codec:e,numberOfChannels:this.demuxer.audioInfo.numberOfChannels,sampleRate:this.demuxer.audioInfo.sampleRate}):null}getNumberOfChannels(){return g(this.demuxer.audioInfo),this.demuxer.audioInfo.numberOfChannels}getSampleRate(){return g(this.demuxer.audioInfo),this.demuxer.audioInfo.sampleRate}getTimeResolution(){return g(this.demuxer.audioInfo),this.demuxer.audioInfo.sampleRate}isRelativeToUnixEpoch(){return!1}getUnixTimeForTimestamp(){return null}getPairingMask(){return 1n}getBitrate(){return null}getAverageBitrate(){return null}async getDurationFromMetadata(){return g(this.demuxer.dataSize!==-1),this.demuxer.dataSize/this.demuxer.audioInfo.blockSizeInBytes/this.demuxer.audioInfo.sampleRate}async getLiveRefreshInterval(){return null}getName(){return null}getLanguageCode(){return ne}getDisposition(){return{...fe}}async getPacketAtIndex(e,t){g(e>=0),g(this.demuxer.audioInfo);let i=e*zr*this.demuxer.audioInfo.blockSizeInBytes;if(i>=this.demuxer.dataSize)return null;let n=Math.min(zr*this.demuxer.audioInfo.blockSizeInBytes,this.demuxer.dataSize-i);if(this.demuxer.reader.fileSize===null){let c=this.demuxer.reader.requestSlice(this.demuxer.dataStart+i,n);if(P(c)&&(c=await c),!c)return null}let a;if(t.metadataOnly)a=ce;else{let c=this.demuxer.reader.requestSlice(this.demuxer.dataStart+i,n);P(c)&&(c=await c),g(c),a=M(c,n)}let s=e*zr/this.demuxer.audioInfo.sampleRate,o=n/this.demuxer.audioInfo.blockSizeInBytes/this.demuxer.audioInfo.sampleRate;return this.demuxer.lastKnownPacketIndex=Math.max(e,this.demuxer.lastKnownPacketIndex),new Y(a,"key",s,o,e,n)}getFirstPacket(e){return this.getPacketAtIndex(0,e)}async getPacket(e,t){g(this.demuxer.audioInfo);let i=Math.floor(Math.min(e*this.demuxer.audioInfo.sampleRate/zr,(this.demuxer.dataSize-1)/(zr*this.demuxer.audioInfo.blockSizeInBytes)));if(i<0)return null;let n=await this.getPacketAtIndex(i,t);if(n)return n;if(i===0)return null;g(this.demuxer.reader.fileSize===null);let a=await this.getPacketAtIndex(this.demuxer.lastKnownPacketIndex,t);for(;a;){let s=await this.getNextPacket(a,t);if(!s)break;a=s}return a}getNextPacket(e,t){g(this.demuxer.audioInfo);let i=Math.round(e.timestamp*this.demuxer.audioInfo.sampleRate/zr);return this.getPacketAtIndex(i+1,t)}getKeyPacket(e,t){return this.getPacket(e,t)}getNextKeyPacket(e,t){return this.getNextPacket(e,t)}};var Et=7,Ze=9,Je=r=>{let e=r.filePos;if(r.remainingLength<Et)return null;let t=M(r,Et),i=new q(t);if(i.readBits(12)!==4095||(i.skipBits(1),i.readBits(2)!==0))return null;let s=i.readBits(1),o=i.readBits(2)+1,c=i.readBits(4);if(c>=Ve.length)return null;i.skipBits(1);let l=i.readBits(3);if(l===0)throw new Error("ADTS frames with channel configuration 0 are not supported.");i.skipBits(1),i.skipBits(1),i.skipBits(1),i.skipBits(1);let u=i.readBits(13);i.skipBits(11);let d=i.readBits(2)+1;if(d!==1)throw new Error("ADTS frames with more than one AAC frame are not supported.");let f=null;if(s===0){if(r.remainingLength<2)return null;f=re(r)}return u<r.filePos-e?null:{objectType:o,samplingFrequencyIndex:c,channelConfiguration:l,frameLength:u,numberOfAacFrames:d,crcCheck:f,startPos:e}};var jn=1024,Gn=class extends le{constructor(e){super(e),this.metadataPromise=null,this.firstFrameHeader=null,this.loadedSamples=[],this.metadataTags=null,this.trackBackings=[],this.readingMutex=new Pe,this.lastSampleLoaded=!1,this.lastLoadedPos=0,this.nextTimestampInSamples=0,this.reader=e._reader}async readMetadata(){return this.metadataPromise??=(async()=>{for(;!this.firstFrameHeader&&!this.lastSampleLoaded;)await this.advanceReader();g(this.firstFrameHeader),this.trackBackings=[new pa(this)]})()}async advanceReader(){if(this.lastLoadedPos===0)for(;;){let s=this.reader.requestSlice(this.lastLoadedPos,me);if(P(s)&&(s=await s),!s){this.lastSampleLoaded=!0;return}let o=Ie(s);if(!o)break;this.lastLoadedPos=s.filePos+o.size}let e=this.reader.requestSliceRange(this.lastLoadedPos,Et,Ze);if(P(e)&&(e=await e),!e){this.lastSampleLoaded=!0;return}let t=Je(e);if(!t){this.lastSampleLoaded=!0;return}if(this.reader.fileSize!==null&&t.startPos+t.frameLength>this.reader.fileSize){this.lastSampleLoaded=!0;return}this.firstFrameHeader||(this.firstFrameHeader=t);let i=Ve[t.samplingFrequencyIndex];g(i!==void 0);let n=jn/i,a={timestamp:this.nextTimestampInSamples/i,duration:n,dataStart:t.startPos,dataSize:t.frameLength};this.loadedSamples.push(a),this.nextTimestampInSamples+=jn,this.lastLoadedPos=t.startPos+t.frameLength}async getMimeType(){return"audio/aac"}async getTrackBackings(){return await this.readMetadata(),this.trackBackings}async getMetadataTags(){let e=await this.readingMutex.acquire();try{if(await this.readMetadata(),this.metadataTags)return this.metadataTags;this.metadataTags={};let t=0;for(;;){let i=this.reader.requestSlice(t,me);if(P(i)&&(i=await i),!i)break;let n=Ie(i);if(!n)break;let a=this.reader.requestSlice(i.filePos,n.size);if(P(a)&&(a=await a),!a)break;Ht(a,n,this.metadataTags),t=i.filePos+n.size}return this.metadataTags}finally{e()}}},pa=class{constructor(e){this.demuxer=e}getType(){return"audio"}getId(){return 1}getNumber(){return 1}getTimeResolution(){return this.getSampleRate()}isRelativeToUnixEpoch(){return!1}getUnixTimeForTimestamp(){return null}getPairingMask(){return 1n}getBitrate(){return null}getAverageBitrate(){return null}async getDurationFromMetadata(){return null}async getLiveRefreshInterval(){return null}getName(){return null}getLanguageCode(){return ne}getCodec(){return"aac"}getInternalCodecId(){return g(this.demuxer.firstFrameHeader),this.demuxer.firstFrameHeader.objectType}getNumberOfChannels(){g(this.demuxer.firstFrameHeader);let e=Dt[this.demuxer.firstFrameHeader.channelConfiguration];return g(e!==void 0),e}getSampleRate(){g(this.demuxer.firstFrameHeader);let e=Ve[this.demuxer.firstFrameHeader.samplingFrequencyIndex];return g(e!==void 0),e}getDisposition(){return{...fe}}async getDecoderConfig(){return g(this.demuxer.firstFrameHeader),{codec:`mp4a.40.${this.demuxer.firstFrameHeader.objectType}`,numberOfChannels:this.getNumberOfChannels(),sampleRate:this.getSampleRate()}}async getPacketAtIndex(e,t){if(e===-1)return null;let i=this.demuxer.loadedSamples[e];if(!i)return null;let n;if(t.metadataOnly)n=ce;else{let a=this.demuxer.reader.requestSlice(i.dataStart,i.dataSize);if(P(a)&&(a=await a),!a)return null;n=M(a,i.dataSize)}return new Y(n,"key",i.timestamp,i.duration,e,i.dataSize)}getFirstPacket(e){return this.getPacketAtIndex(0,e)}async getNextPacket(e,t){let i=await this.demuxer.readingMutex.acquire();try{let n=pt(this.demuxer.loadedSamples,e.timestamp,s=>s.timestamp);if(n===-1)throw new Error("Packet was not created from this track.");let a=n+1;for(;a>=this.demuxer.loadedSamples.length&&!this.demuxer.lastSampleLoaded;)await this.demuxer.advanceReader();return this.getPacketAtIndex(a,t)}finally{i()}}async getPacket(e,t){let i=await this.demuxer.readingMutex.acquire();try{for(;;){let n=Q(this.demuxer.loadedSamples,e,a=>a.timestamp);if(n===-1&&this.demuxer.loadedSamples.length>0)return null;if(this.demuxer.lastSampleLoaded)return this.getPacketAtIndex(n,t);if(n>=0&&n+1<this.demuxer.loadedSamples.length)return this.getPacketAtIndex(n,t);await this.demuxer.advanceReader()}}finally{i()}}getKeyPacket(e,t){return this.getPacket(e,t)}getNextKeyPacket(e,t){return this.getNextPacket(e,t)}};var pc=r=>r===0?null:r===1?192:r>=2&&r<=5?144*2**r:r===6?"uncommon-u8":r===7?"uncommon-u16":r>=8&&r<=15?2**r:null,gc=(r,e)=>{switch(r){case 0:return e;case 1:return 88200;case 2:return 176400;case 3:return 192e3;case 4:return 8e3;case 5:return 16e3;case 6:return 22050;case 7:return 24e3;case 8:return 32e3;case 9:return 44100;case 10:return 48e3;case 11:return 96e3;case 12:return"uncommon-u8";case 13:return"uncommon-u16";case 14:return"uncommon-u16-10";default:return null}},kc=r=>{let e=0,t=new q(M(r,1));for(;t.readBits(1)===1;)e++;if(e===0)return t.readBits(7);let i=[],n=e-1,a=new q(M(r,n)),s=8-e-1;for(let c=0;c<s;c++)i.unshift(t.readBits(1));for(let c=0;c<n;c++)for(let l=0;l<8;l++){let u=a.readBits(1);l<2||i.unshift(u)}return i.reduce((c,l,u)=>c|l<<u,0)},yc=(r,e)=>{if(e==="uncommon-u16")return re(r)+1;if(e==="uncommon-u8")return U(r)+1;if(typeof e=="number")return e;_e(e),g(!1)},wc=(r,e)=>e==="uncommon-u16"?re(r):e==="uncommon-u16-10"?re(r)*10:e==="uncommon-u8"?U(r):typeof e=="number"?e:null,bc=r=>{let t=0;for(let i of r){t^=i;for(let n=0;n<8;n++)(t&128)!==0?t=t<<1^7:t<<=1,t&=255}return t};var Qn=class extends le{constructor(e){super(e),this.loadedSamples=[],this.metadataPromise=null,this.trackBacking=null,this.metadataTags={},this.audioInfo=null,this.lastLoadedPos=null,this.blockingBit=null,this.readingMutex=new Pe,this.lastSampleLoaded=!1,this.reader=e._reader}async getMetadataTags(){return await this.readMetadata(),this.metadataTags}async getTrackBackings(){return await this.readMetadata(),g(this.trackBacking),[this.trackBacking]}async getMimeType(){return"audio/flac"}async readMetadata(){return this.metadataPromise??=(async()=>{let e=0;for(;;){let t=this.reader.requestSlice(e,me);if(P(t)&&(t=await t),!t)break;let i=Ie(t);if(!i)break;let n=this.reader.requestSlice(t.filePos,i.size);P(n)&&(n=await n),g(n),Ht(n,i,this.metadataTags),e=t.filePos+i.size}for(e+=4;this.reader.fileSize===null||e<this.reader.fileSize;){let t=this.reader.requestSlice(e,4);if(P(t)&&(t=await t),e+=4,t===null)throw new Error(`Metadata block at position ${e} is too small! Corrupted file.`);g(t);let i=U(t),n=Xe(t),a=(i&128)!==0;switch(i&127){case Ut.STREAMINFO:{if(n<34)throw new Error(`StreamInfo block at position ${e} is too small! Corrupted file.`);let o=this.reader.requestSlice(e,n);if(P(o)&&(o=await o),o===null)throw new Error(`StreamInfo block at position ${e} is too small! Corrupted file.`);let c=M(o,34),l=new q(c),u=l.readBits(16),d=l.readBits(16),f=l.readBits(24),m=l.readBits(24),p=l.readBits(20);if(p===0)throw new Error("Invalid StreamInfo block: sample rate is 0. Corrupted file.");let h=l.readBits(3)+1;l.readBits(5);let k=l.readBits(36);l.skipBits(128);let w=new Uint8Array(42);w.set(new Uint8Array([102,76,97,67]),0),w.set(new Uint8Array([128,0,0,34]),4),w.set(c,8),this.audioInfo={numberOfChannels:h,sampleRate:p,totalSamples:k,minimumBlockSize:u,maximumBlockSize:d,minimumFrameSize:f,maximumFrameSize:m,description:w},this.trackBacking=new ga(this);break}case Ut.VORBIS_COMMENT:{let o=this.reader.requestSlice(e,n);if(P(o)&&(o=await o),!o)throw new Error(`Vorbis comment block at position ${e} exceeds the file. Corrupted file.`);wi(M(o,n),this.metadataTags);break}case Ut.PICTURE:{let o=this.reader.requestSlice(e,n);if(P(o)&&(o=await o),!o)throw new Error(`Picture block at position ${e} exceeds the file. Corrupted file.`);try{let c=B(o),l=B(o),u=ie.decode(M(o,l)),d=B(o),f=ie.decode(M(o,d));o.skip(16);let m=B(o),p=M(o,m);this.metadataTags.images??=[],this.metadataTags.images.push({data:p,mimeType:u,kind:c===3?"coverFront":c===4?"coverBack":"unknown",description:f})}catch{}break}default:break}if(e+=n,a)break}if(this.lastLoadedPos=e,!this.audioInfo)throw new Error("Missing STREAMINFO metadata block! Corrupted FLAC file.")})()}async readNextFlacFrame(e){g(this.audioInfo);let t=6,i=16,n=10,a=this.audioInfo.maximumBlockSize*this.audioInfo.numberOfChannels*4+i+2,s=this.audioInfo.minimumFrameSize||n,c=(this.audioInfo.maximumFrameSize||a)+i,l=await this.reader.requestSliceRange(e,t,c);if(!l)return null;let u=this.readFlacFrameHeader(l);if(!u)return null;for(l.filePos=e+s;;){if(l.filePos>l.end-t)return{num:u.num,blockSize:u.blockSize,sampleRate:u.sampleRate,size:l.end-e,isLastFrame:!0};if(U(l)===255){let f=l.filePos,m=U(l),p=this.blockingBit===1?249:248;if(m!==p){l.filePos=f;continue}l.skip(-2);let h=l.filePos-e,k=this.readFlacFrameHeader(l);if(!k){l.filePos=f;continue}if(this.blockingBit===0){if(k.num-u.num!==1){l.filePos=f;continue}}else if(k.num-u.num!==u.blockSize){l.filePos=f;continue}return{num:u.num,blockSize:u.blockSize,sampleRate:u.sampleRate,size:h,isLastFrame:!1}}}}readFlacFrameHeader(e){let t=e.filePos,i=M(e,4),n=new q(i);if(n.readBits(15)!==32764)return null;let s=n.readBits(1);if(this.blockingBit!==null&&s!==this.blockingBit)return null;let o=pc(n.readBits(4));if(!o)return null;g(this.audioInfo);let c=gc(n.readBits(4),this.audioInfo.sampleRate);if(!c||(n.readBits(4),n.readBits(3),n.readBits(1)!==0))return null;let u=U(e);e.skip(-1);let f=4+Math.max(Math.clz32(~u<<24),1)+(o==="uncommon-u16"?2:o==="uncommon-u8"?1:0)+(c==="uncommon-u8"?1:typeof c=="number"?0:2)+1;if(t+f>e.end)return null;let m=kc(e),p=yc(e,o),h=wc(e,c);if(h===null||h!==this.audioInfo.sampleRate)return null;let k=e.filePos-t,w=U(e);e.skip(-k),e.skip(-1);let S=bc(M(e,k));return w!==S?null:(this.blockingBit=s,{num:m,blockSize:p,sampleRate:h})}async advanceReader(){await this.readMetadata(),g(this.lastLoadedPos!==null),g(this.audioInfo);let e=this.lastLoadedPos,t=await this.readNextFlacFrame(e);if(!t){this.lastSampleLoaded=!0;return}let i=this.loadedSamples[this.loadedSamples.length-1],a={blockOffset:i?i.blockOffset+i.blockSize:0,blockSize:t.blockSize,byteOffset:e,byteSize:t.size};if(this.lastLoadedPos=this.lastLoadedPos+t.size,this.loadedSamples.push(a),t.isLastFrame){this.lastSampleLoaded=!0;return}}},ga=class{constructor(e){this.demuxer=e}getType(){return"audio"}getId(){return 1}getNumber(){return 1}getCodec(){return"flac"}getInternalCodecId(){return null}getNumberOfChannels(){return g(this.demuxer.audioInfo),this.demuxer.audioInfo.numberOfChannels}getSampleRate(){return g(this.demuxer.audioInfo),this.demuxer.audioInfo.sampleRate}getName(){return null}getLanguageCode(){return ne}getTimeResolution(){return g(this.demuxer.audioInfo),this.demuxer.audioInfo.sampleRate}isRelativeToUnixEpoch(){return!1}getUnixTimeForTimestamp(){return null}getPairingMask(){return 1n}getBitrate(){return null}getAverageBitrate(){return null}async getDurationFromMetadata(){return g(this.demuxer.audioInfo),this.demuxer.audioInfo.totalSamples===0?null:this.demuxer.audioInfo.totalSamples/this.demuxer.audioInfo.sampleRate}async getLiveRefreshInterval(){return null}getDisposition(){return{...fe}}async getDecoderConfig(){return g(this.demuxer.audioInfo),{codec:"flac",numberOfChannels:this.demuxer.audioInfo.numberOfChannels,sampleRate:this.demuxer.audioInfo.sampleRate,description:this.demuxer.audioInfo.description}}async getPacket(e,t){if(g(this.demuxer.audioInfo),e<0)return null;let i=await this.demuxer.readingMutex.acquire();try{for(;;){let n=Q(this.demuxer.loadedSamples,e,c=>c.blockOffset/this.demuxer.audioInfo.sampleRate);if(n===-1){if(this.demuxer.lastSampleLoaded)return null;await this.demuxer.advanceReader();continue}let a=this.demuxer.loadedSamples[n],s=a.blockOffset/this.demuxer.audioInfo.sampleRate,o=a.blockSize/this.demuxer.audioInfo.sampleRate;if(s+o<=e){if(this.demuxer.lastSampleLoaded)return this.getPacketAtIndex(this.demuxer.loadedSamples.length-1,t);await this.demuxer.advanceReader();continue}return this.getPacketAtIndex(n,t)}}finally{i()}}async getNextPacket(e,t){let i=await this.demuxer.readingMutex.acquire();try{let n=e.sequenceNumber+1;if(this.demuxer.lastSampleLoaded&&n>=this.demuxer.loadedSamples.length)return null;for(;n>=this.demuxer.loadedSamples.length&&!this.demuxer.lastSampleLoaded;)await this.demuxer.advanceReader();return this.getPacketAtIndex(n,t)}finally{i()}}getKeyPacket(e,t){return this.getPacket(e,t)}getNextKeyPacket(e,t){return this.getNextPacket(e,t)}async getPacketAtIndex(e,t){let i=this.demuxer.loadedSamples[e];if(!i)return null;let n;if(t.metadataOnly)n=ce;else{let o=this.demuxer.reader.requestSlice(i.byteOffset,i.byteSize);if(P(o)&&(o=await o),!o)return null;n=M(o,i.byteSize)}g(this.demuxer.audioInfo);let a=i.blockOffset/this.demuxer.audioInfo.sampleRate,s=i.blockSize/this.demuxer.audioInfo.sampleRate;return new Y(n,"key",a,s,e,i.byteSize)}async getFirstPacket(e){for(;this.demuxer.loadedSamples.length===0&&!this.demuxer.lastSampleLoaded;)await this.demuxer.advanceReader();return this.getPacketAtIndex(0,e)}};var xe=9e4,Bi=2**33,Ce=188,Tc=r=>{let e="video/MP2T",t=[...new Set(r.filter(Boolean))];return t.length>0&&(e+=`; codecs="${t.join(", ")}"`),e};var Xn=r=>{let e=60*xe;return{reference:r-e,offset:r>=Bi-e?-Bi:Bi}},$n=(r,e)=>{let{reference:t,offset:i}=e;return i<0&&r>=t||i>0&&r<t?r+i:r};var xc="PES packet is missing PTS where it was expected. PES packets without PTS are not currently supported. If you think this file should be supported, please report it.",Sc=5,Tu=1212435798,Su=1212436562,Au=1146376960,xu=new Set([133,134,162]),Ac=new Set,Yn=class extends le{constructor(e){super(e),this.metadataPromise=null,this.elementaryStreams=[],this.trackBackingEntries=[],this.packetOffset=0,this.packetStride=-1,this.sectionEndPositions=[],this.seekChunkSize=5*1024*1024,this.minReferencePointByteDistance=-1,this.timestampWrapInfo=null,this.reader=e._reader}async readMetadata(){return this.metadataPromise??=(async()=>{let e=Ce+16+1,t=this.reader.requestSlice(0,e);P(t)&&(t=await t),g(t);let i=M(t,e);if(i[0]===71&&i[Ce]===71)this.packetOffset=0,this.packetStride=Ce;else if(i[0]===71&&i[Ce+16]===71)this.packetOffset=0,this.packetStride=Ce+16;else if(i[4]===71&&i[4+Ce+4]===71)this.packetOffset=4,this.packetStride=Ce+4;else throw new Error("Unreachable.");let n=256;this.minReferencePointByteDistance=n*this.packetStride;let a=this.packetOffset,s=null,o=!1,c=!1;for(;;){let l=await this.readPacketHeader(a);if(!l)break;if(l.payloadUnitStartIndicator===0){a+=this.packetStride;continue}if(c&&!this.elementaryStreams.some(h=>h.pid===l.pid&&!h.initialized)){a+=this.packetStride;continue}let u=await this.readSection(a,!0,!c);if(!u)break;let d=3,f=32,m=!1;if(!c&&u.pid!==0&&!(u.payload[0]===0&&u.payload[1]===0&&u.payload[2]===1)){let k=new q(u.payload),w=k.readAlignedByte();k.skipBits(8*w),m=k.readBits(8)===2}if(u.pid===0&&!o){let h=new q(u.payload),k=h.readAlignedByte();h.skipBits(8*k),h.skipBits(14);let w=h.readBits(10);for(h.skipBits(40);8*(w+d)-h.pos>f;){let S=h.readBits(16);h.skipBits(3);let b=h.readBits(13);if(S!==0){if(s!==null)throw new Error("Only files with a single program are supported.");s=b}}if(s===null)throw new Error("Program Association Table must link to a Program Map Table.");o=!0}else if((u.pid===s||m)&&!c){let h=new q(u.payload),k=h.readAlignedByte();h.skipBits(8*k),h.skipBits(12);let w=h.readBits(12);h.skipBits(43);let S=h.readBits(13);h.skipBits(6);let b=h.readBits(10),T=h.pos+8*b,y=!1;for(;h.pos<T;){let A=h.readBits(8),x=h.readBits(8),C=h.pos+8*x;if(A===Sc&&x>=4){let E=h.readBits(32);y||=E===Tu||E===Su}h.pos=C}for(h.pos=T;8*(w+d)-h.pos>f;){let A=h.readBits(8);h.skipBits(3);let x=h.readBits(13);h.skipBits(6);let C=h.readBits(10),E=h.pos+8*C,I=!1,R=!1,D=!1;for(;h.pos<E;){let z=h.readBits(8),j=h.readBits(8),ee=h.pos+8*j;if(z===106)I=!0;else if(z===122||z===204)R=!0;else if(z===123)D=!0;else if(z===Sc&&j>=4){let we=h.readBits(32);D||=(we&4294967040)===Au}h.pos=ee}let O=null,V=y&&xu.has(A)?130:A;switch(V){case 27:case 36:O={type:"video",codec:A===27?"avc":"hevc",decoderConfig:null,avcCodecInfo:null,hevcCodecInfo:null,colorSpace:{primaries:null,transfer:null,matrix:null,fullRange:null},width:-1,height:-1,squarePixelWidth:-1,squarePixelHeight:-1,reorderSize:-1};break;case 3:case 4:case 15:case 129:case 135:case 130:case 138:{let z;V===3||V===4?z="mp3":V===15?z="aac":V===129?z="ac3":V===135?z="eac3":z="dts",O={type:"audio",codec:z,decoderConfig:null,aacCodecInfo:null,dtsFormat:null,numberOfChannels:-1,sampleRate:-1}}break;case 6:R?O={type:"audio",codec:"eac3",decoderConfig:null,aacCodecInfo:null,dtsFormat:null,numberOfChannels:-1,sampleRate:-1}:I?O={type:"audio",codec:"ac3",decoderConfig:null,aacCodecInfo:null,dtsFormat:null,numberOfChannels:-1,sampleRate:-1}:D&&(O={type:"audio",codec:"dts",decoderConfig:null,aacCodecInfo:null,dtsFormat:null,numberOfChannels:-1,sampleRate:-1});break;default:Ac.has(A)||(H._warn(`Note: MPEG-TS streams with stream_type 0x${A.toString(16)} are not currently supported.`),Ac.add(A))}O&&this.elementaryStreams.push({demuxer:this,pid:x,streamType:A,initialized:!1,firstSection:null,canBeTrustedWithKeyPackets:!1,info:O,referencePesPackets:[]})}c=!0}else{let h=this.elementaryStreams.find(k=>k.pid===u.pid);e:if(h&&!h.initialized){let k=Vr(this,u,!0);if(!k)throw new Error(`Couldn't read first PES packet for Elementary Stream with PID ${h.pid}`);if(h.firstSection=u,h.canBeTrustedWithKeyPackets=u.randomAccessIndicator===1,this.input._initInput){let b=(await this.input._initInput._getDemuxer()).elementaryStreams.find(T=>T.pid===u.pid&&T.info.codec===h.info.codec&&T.initialized);if(b){h.info=b.info,h.initialized=!0;break e}}let w=new ur(h,k);if(h.info.type==="video"){for(;;){let S=w;if(S.suppliedPacket=null,await w.markNextPacket(),h.info.codec==="avc"){if(!w.suppliedPacket)throw new Error("Invalid AVC video stream; could not extract AVCDecoderConfigurationRecord from any packet.");if(h.info.avcCodecInfo=zt(w.suppliedPacket.data),!h.info.avcCodecInfo)continue;let b=h.info.avcCodecInfo.sequenceParameterSets[0];g(b);let T=nr(b);h.info.width=T.displayWidth,h.info.height=T.displayHeight;let y=T.pixelAspectRatio.num,A=T.pixelAspectRatio.den;h.info.squarePixelWidth=h.info.width,h.info.squarePixelHeight=h.info.height,y>0&&A>0&&(y>A?h.info.squarePixelWidth=Math.round(h.info.width*y/A):h.info.squarePixelHeight=Math.round(h.info.height*A/y)),h.info.colorSpace={primaries:De[T.colourPrimaries],transfer:Oe[T.transferCharacteristics],matrix:Ue[T.matrixCoefficients],fullRange:!!T.fullRangeFlag},h.info.reorderSize=T.maxDecFrameBuffering;break}else if(h.info.codec==="hevc"){if(!w.suppliedPacket)throw new Error("Invalid HEVC video stream; could not extract HVCDecoderConfigurationRecord from first packet.");if(h.info.hevcCodecInfo=Nt(w.suppliedPacket.data),!h.info.hevcCodecInfo)continue;let T=h.info.hevcCodecInfo.arrays.find(C=>C.nalUnitType===se.SPS_NUT).nalUnits[0];g(T);let y=sr(T);h.info.width=y.displayWidth,h.info.height=y.displayHeight;let A=y.pixelAspectRatio.num,x=y.pixelAspectRatio.den;h.info.squarePixelWidth=h.info.width,h.info.squarePixelHeight=h.info.height,A>0&&x>0&&(A>x?h.info.squarePixelWidth=Math.round(h.info.width*A/x):h.info.squarePixelHeight=Math.round(h.info.height*x/A)),h.info.colorSpace={primaries:De[y.colourPrimaries],transfer:Oe[y.transferCharacteristics],matrix:Ue[y.matrixCoefficients],fullRange:!!y.fullRangeFlag},h.info.reorderSize=y.maxDecFrameBuffering;break}else throw new Error("Unhandled.")}h.info.decoderConfig={codec:ar({width:h.info.width,height:h.info.height,codec:h.info.codec,codecDescription:null,colorSpace:h.info.colorSpace,avcType:1,avcCodecInfo:h.info.avcCodecInfo,hevcCodecInfo:h.info.hevcCodecInfo,vp9CodecInfo:null,av1CodecInfo:null,proresFormat:null}),codedWidth:h.info.width,codedHeight:h.info.height,colorSpace:h.info.colorSpace},(h.info.width!==h.info.squarePixelWidth||h.info.height!==h.info.squarePixelHeight)&&(h.info.decoderConfig.displayAspectWidth=h.info.squarePixelWidth,h.info.decoderConfig.displayAspectHeight=h.info.squarePixelHeight),h.initialized=!0}else{if(await w.markNextPacket(),!w.suppliedPacket)throw new Error(`Couldn't parse first media packet for Elementary Stream with PID ${h.pid}`);if(h.info.codec==="aac"){let S=Se.tempFromBytes(w.suppliedPacket.data),b=Je(S);if(!b)throw new Error("Invalid AAC audio stream; could not read ADTS frame header from first packet.");h.info.aacCodecInfo={isMpeg2:!1,objectType:b.objectType},h.info.numberOfChannels=Dt[b.channelConfiguration],h.info.sampleRate=Ve[b.samplingFrequencyIndex]}else if(h.info.codec==="mp3"){let S=B(Se.tempFromBytes(w.suppliedPacket.data)),b=gi(S,w.suppliedPacket.data.byteLength);if(!b.header)throw new Error("Invalid MP3 audio stream; could not read frame header from first packet.");h.info.numberOfChannels=Ot(b.header.channel),h.info.sampleRate=b.header.sampleRate}else if(h.info.codec==="ac3"){let S=bn(w.suppliedPacket.data);if(!S)throw new Error("Invalid AC-3 audio stream; could not read sync frame from first packet.");if(S.fscod===3)throw new Error("Invalid AC-3 audio stream; reserved sample rate code found in first packet.");h.info.numberOfChannels=bi[S.acmod]+S.lfeon,h.info.sampleRate=rr[S.fscod]}else if(h.info.codec==="eac3"){let S=Tn(w.suppliedPacket.data);if(!S)throw new Error("Invalid E-AC-3 audio stream; could not read sync frame from first packet.");let b=Sn(S);if(b===null)throw new Error("Invalid E-AC-3 audio stream; reserved sample rate code found in first packet.");h.info.numberOfChannels=An(S),h.info.sampleRate=b}else if(h.info.codec==="dts"){let S=Si(w.suppliedPacket.data);if(!S)throw new Error("Invalid DTS audio stream; could not read frame header from first packet.");h.info.numberOfChannels=S.numberOfChannels,h.info.sampleRate=S.sampleRate,S.core&&(h.info.dtsFormat=S.hasExtensions?"dtsh":"dtsc")}else throw new Error("Unhandled.");h.info.decoderConfig={codec:Ir({codec:h.info.codec,codecDescription:null,aacCodecInfo:h.info.aacCodecInfo,dtsFormat:h.info.dtsFormat}),numberOfChannels:h.info.numberOfChannels,sampleRate:h.info.sampleRate},h.initialized=!0}}}if(c&&this.elementaryStreams.every(h=>h.initialized))break;a+=this.packetStride}if(!c)throw o?new Error("No Program Map Table found in the file."):new Error("No Program Association Table found in the file.");for(let l of this.elementaryStreams)l.initialized&&(l.info.type==="video"?this.trackBackingEntries.push(new ka(l)):this.trackBackingEntries.push(new ya(l)))})()}async getTrackBackings(){return await this.readMetadata(),this.trackBackingEntries}async getMetadataTags(){return{}}async getMimeType(){await this.readMetadata();let e=await Promise.all(this.trackBackingEntries.map(t=>t.getDecoderConfig().then(i=>i?.codec??null)));return Tc(e)}async readSection(e,t,i=!1){let n=e,a=e,s=[],o=0,c=null,l=!0,u=0;for(;;){let f=await this.readPacket(a);if(a+=this.packetStride,!f)break;if(c){if(f.pid!==c.pid){if(i)break;continue}if(f.payloadUnitStartIndicator===1)break}else{if(f.payloadUnitStartIndicator===0)break;c=f}let m=!!(f.adaptationFieldControl&2),p=!!(f.adaptationFieldControl&1),h=0;if(m&&(h=1+f.body[0],f===c&&h>1&&(u=f.body[1]>>6&1)),p&&(h===0?(s.push(f.body),o+=f.body.byteLength):(s.push(f.body.subarray(h)),o+=f.body.byteLength-h)),n=a,!t&&o>=64){l=!1;break}if(pt(this.sectionEndPositions,n,w=>w)!==-1){l=!1;break}}if(l){let f=Q(this.sectionEndPositions,n,m=>m);this.sectionEndPositions.splice(f+1,0,n)}if(!c)return null;let d;if(s.length===1)d=s[0];else{let f=s.reduce((p,h)=>p+h.length,0);d=new Uint8Array(f);let m=0;for(let p of s)d.set(p,m),m+=p.length}return{startPos:e,endPos:t?n:null,pid:c.pid,payload:d,randomAccessIndicator:u}}async readPacketHeader(e){let t=this.reader.requestSlice(e,4);if(P(t)&&(t=await t),!t)return null;if(U(t)!==71)throw new Error("Invalid TS packet sync byte; the file is likely corrupted.");let n=re(t),a=n>>15,s=n>>14&1,o=n>>13&1,c=n&8191,l=U(t),u=l>>6,d=l>>4&3,f=l&15;return{payloadUnitStartIndicator:s,pid:c,adaptationFieldControl:d}}async readPacket(e){let t=this.reader.requestSlice(e,Ce);if(P(t)&&(t=await t),!t)return null;let i=M(t,Ce);if(i[0]!==71)throw new Error("Invalid TS packet sync byte; the file is likely corrupted.");let a=(i[1]<<8)+i[2],s=a>>15,o=a>>14&1,c=a>>13&1,l=a&8191,u=i[3],d=u>>6,f=u>>4&3,m=u&15;return{payloadUnitStartIndicator:o,pid:l,adaptationFieldControl:f,body:i.subarray(4)}}normalizeTimestamp(e){return this.timestampWrapInfo??=Xn(e),$n(e,this.timestampWrapInfo)}},lr=(r,e,t)=>{if(e.payload.byteLength<3)return null;let i=new q(e.payload);if(i.readBits(24)!==1)return null;let a=i.readBits(8);if(i.skipBits(16),a===188||a===190||a===191||a===240||a===241||a===255||a===242||a===248)return null;i.skipBits(8);let s=i.readBits(2);i.skipBits(14);let o=null;if(s===2||s===3)o=0,i.skipBits(4),o+=i.readBits(3)*(1<<30),i.skipBits(1),o+=i.readBits(15)*32768,i.skipBits(1),o+=i.readBits(15),o=r.normalizeTimestamp(o);else if(t)throw new Error(xc);return{sectionStartPos:e.startPos,sectionEndPos:e.endPos,pts:o,randomAccessIndicator:e.randomAccessIndicator}},Vr=(r,e,t)=>{g(e.endPos!==null);let i=lr(r,e,t);if(!i)return null;let n=new q(e.payload);n.skipBits(32);let a=n.readBits(16),s=6;n.skipBits(16);let o=n.readBits(8),c=n.pos+8*o;n.pos=c;let l=c/8;g(Number.isInteger(l));let u=e.payload.subarray(l,a>0?s+a:e.payload.byteLength);return{...i,data:u}},Zn=class r{constructor(e){this.elementaryStream=e,this.packetBuffers=new WeakMap,this.packetSectionStarts=new WeakMap}getId(){return this.elementaryStream.pid}getNumber(){let e=this.elementaryStream.demuxer,t=this.elementaryStream.info.type,i=0;for(let n of e.trackBackingEntries)if(n.getType()===t&&i++,g(n instanceof r),n.elementaryStream===this.elementaryStream)break;return i}getCodec(){throw new Error("Not implemented on base class.")}getInternalCodecId(){return this.elementaryStream.streamType}getName(){return null}getLanguageCode(){return ne}getDisposition(){return{...fe,primary:!1}}getTimeResolution(){return xe}isRelativeToUnixEpoch(){return!1}getUnixTimeForTimestamp(){return null}getPairingMask(){return 1n}getBitrate(){return null}getAverageBitrate(){return null}async getDurationFromMetadata(){return null}async getLiveRefreshInterval(){return null}createEncodedPacket(e,t,i){let n;return this.allPacketsAreKeyPackets()?n="key":n=e.randomAccessIndicator===1?"key":"delta",new Y(i.metadataOnly?ce:e.data,n,e.pts/xe,Math.max(t/xe,0),e.sequenceNumber,e.data.byteLength)}async getFirstPacket(e){let t=this.elementaryStream.firstSection;g(t);let i=Vr(this.elementaryStream.demuxer,t,!0);g(i);let n=new ur(this.elementaryStream,i),a=new Fi(this,n),s=await a.readNext();if(!s)return null;let o=this.createEncodedPacket(s.packet,s.duration,e);return this.packetBuffers.set(o,a),this.packetSectionStarts.set(o,s.packet.sectionStartPos),o}async getNextPacket(e,t){let i=this.packetBuffers.get(e);if(i){let u=await i.readNext();if(!u)return null;this.packetBuffers.delete(e);let d=this.createEncodedPacket(u.packet,u.duration,t);return this.packetBuffers.set(d,i),this.packetSectionStarts.set(d,u.packet.sectionStartPos),d}let n=this.packetSectionStarts.get(e);if(n===void 0)throw new Error("Packet was not created from this track.");let a=this.elementaryStream.demuxer,s=await a.readSection(n,!0);g(s);let o=Vr(a,s,!0);g(o);let c=new ur(this.elementaryStream,o);i=new Fi(this,c);let l=e.sequenceNumber;for(;;){let u=await i.readNext();if(!u)return null;if(u.packet.sequenceNumber>l){let d=this.createEncodedPacket(u.packet,u.duration,t);return this.packetBuffers.set(d,i),this.packetSectionStarts.set(d,u.packet.sectionStartPos),d}}}async getNextKeyPacket(e,t){let i=e;for(;;){if(i=await this.getNextPacket(i,t),!i)return null;if(i.type==="key")return i}}getPacket(e,t){return this.doPacketLookup(e,!1,t)}getKeyPacket(e,t){return this.doPacketLookup(e,!0,t)}async doPacketLookup(e,t,i){let n=kt(e*xe),a=this.elementaryStream.demuxer,{reader:s,seekChunkSize:o}=a,c=this.elementaryStream.pid,l=async(T,y,A)=>{let x=T;for(;x<y;){let C=await a.readPacketHeader(x);if(!C)return null;if(C.pid===c&&C.payloadUnitStartIndicator===1){let E=await a.readSection(x,A);if(!E)return null;let I=lr(a,E,!1);if(I&&I.pts!==null)return{pesPacketHeader:I,section:E}}x+=a.packetStride}return null},u=this.elementaryStream.firstSection;g(u);let d=lr(a,u,!0);if(g(d),n<d.pts)return null;let f,m=this.elementaryStream.referencePesPackets,p=Q(m,n,T=>T.pts),h=p!==-1?m[p]:null;if(h&&n-h.pts<xe/2)f=h.sectionStartPos;else{let T=0;if(s.fileSize!==null){let y=Math.ceil(s.fileSize/o);if(y>1){let A=0,x=y-1;for(T=A;A<=x;){let C=Math.floor((A+x)/2),E=en(C*o,a.packetStride)+d.sectionStartPos,I=E+o,R=await l(E,I,!1);if(!R){x=C-1;continue}R.pesPacketHeader.pts<=n?(T=C,A=C+1):x=C-1}}}f=en(T*o,a.packetStride)+d.sectionStartPos}let w=(await l(f,s.fileSize??1/0,!1))?.pesPacketHeader??null;w||(w=d);let S=this.getReorderSize(),b=async(T,y)=>{let A=await a.readSection(T,!0);g(A);let x=Vr(a,A,!0);g(x);let C=new ur(this.elementaryStream,x),E=new Fi(this,C);for(;!(($(E.presentationOrderPackets)?.pts??-1/0)>=n||!await E.readNextPacket()););let I=br(E.presentationOrderPackets,y);if(I===-1)return null;let R=E.presentationOrderPackets[I],D=I===0?0:R.pts-E.presentationOrderPackets[I-1].pts;E.decodeOrderPackets.splice(0,E.decodeOrderPackets.indexOf(R)),E.lastDuration=D;let O=await E.readNext();g(O);let V=this.createEncodedPacket(O.packet,O.duration,i);return this.packetBuffers.set(V,E),this.packetSectionStarts.set(V,O.packet.sectionStartPos),V};if(!t||this.allPacketsAreKeyPackets()){e:for(;;){let T=w.sectionStartPos+a.packetStride;for(;;){let y=await a.readPacketHeader(T);if(!y)break e;if(y.pid===c&&y.payloadUnitStartIndicator===1){let A=await a.readSection(T,!1);if(A){let x=lr(a,A,!1);if(x&&x.pts!==null){if(x.pts>n)break e;w=x,wa(this.elementaryStream,w);break}}}T+=a.packetStride}}e:for(let T=0;T<S+1;T++){let y=w.sectionStartPos-a.packetStride;for(;y>=a.packetOffset;){let A=await a.readPacketHeader(y);if(!A)break e;if(A.pid===c&&A.payloadUnitStartIndicator===1){let x=await a.readSection(y,!1);if(x){let C=lr(a,x,!1);if(C&&C.pts!==null){w=C;break}}}y-=a.packetStride}if(y<a.packetOffset)break}return b(w.sectionStartPos,T=>T.pts<=n)}else{let T=f,y=null,A=!this.elementaryStream.canBeTrustedWithKeyPackets;for(;;){let x=null,C=T<=d.sectionStartPos,E,I=null;if(C)E=d,I=u;else{let V=await l(T,y??s.fileSize??1/0,A);E=V?.pesPacketHeader??null,I=V?.section??null}let R=!1,D=0,O=null;e:for(;E&&!(y!==null&&E.sectionStartPos>=y);){if(E.pts<=n){let z;if(this.elementaryStream.canBeTrustedWithKeyPackets)z=E.randomAccessIndicator===1;else{if(!O){g(I);let j=Vr(a,I,!0);g(j),O=new ur(this.elementaryStream,j)}for(;(!O.suppliedPacket||O.suppliedPacket.sectionStartPos<E.sectionStartPos)&&(O.suppliedPacket=null,await O.markNextPacket(),!!O.suppliedPacket););z=O.suppliedPacket?.sectionStartPos===E.sectionStartPos&&O.suppliedPacket.randomAccessIndicator===1}z&&(x=E)}if(E.pts>n&&(R=!0),R&&(D++,D>S))break;let V=E.sectionStartPos+a.packetStride;for(;;){let z=await a.readPacketHeader(V);if(!z)break e;if(z.pid===c&&z.payloadUnitStartIndicator===1){let j=await a.readSection(V,A);if(j){let ee=lr(a,j,!1);if(ee&&ee.pts!==null){E=ee,I=j,wa(this.elementaryStream,E);break}}}V+=a.packetStride}}if(x){let V=x;if(D===0)e:for(let j=0;j<S;j++){let ee=V.sectionStartPos-a.packetStride;for(;ee>=a.packetOffset;){let we=await a.readPacketHeader(ee);if(!we)break e;if(we.pid===c&&we.payloadUnitStartIndicator===1){let Me=await a.readSection(ee,A);if(Me){let de=lr(a,Me,!1);if(de&&de.pts!==null){V=de;break}}}ee-=a.packetStride}if(ee<a.packetOffset)break}let z=await b(V.sectionStartPos,j=>j.pts<=n&&j.randomAccessIndicator===1);if(z)return z}if(C)return null;y=T,T=Math.max(en(T-d.sectionStartPos-o,a.packetStride)+d.sectionStartPos,d.sectionStartPos)}}}},ka=class extends Zn{getType(){return"video"}getCodec(){return this.elementaryStream.info.codec}getCodedWidth(){return this.elementaryStream.info.width}getCodedHeight(){return this.elementaryStream.info.height}getSquarePixelWidth(){return this.elementaryStream.info.squarePixelWidth}getSquarePixelHeight(){return this.elementaryStream.info.squarePixelHeight}getTransformationMatrix(){return[...Bt]}async getColorSpace(){return this.elementaryStream.info.colorSpace}async canBeTransparent(){return!1}async getDecoderConfig(){return g(this.elementaryStream.info.decoderConfig),this.elementaryStream.info.decoderConfig}allPacketsAreKeyPackets(){return!1}getReorderSize(){return this.elementaryStream.info.reorderSize}},ya=class extends Zn{getType(){return"audio"}getCodec(){return this.elementaryStream.info.codec}getNumberOfChannels(){return this.elementaryStream.info.numberOfChannels}getSampleRate(){return this.elementaryStream.info.sampleRate}async getDecoderConfig(){return g(this.elementaryStream.info.decoderConfig),this.elementaryStream.info.decoderConfig}allPacketsAreKeyPackets(){return!0}getReorderSize(){return 0}},wa=(r,e)=>{let t=r.referencePesPackets,i=Q(t,e.sectionStartPos,n=>n.sectionStartPos);if(i>=0){let n=t[i];if(e.pts<=n.pts)return!1;let a=r.demuxer.minReferencePointByteDistance;if(e.sectionStartPos-n.sectionStartPos<a)return!1;if(i<t.length-1){let s=t[i+1];if(s.pts<e.pts||s.sectionStartPos-e.sectionStartPos<a)return!1}}return t.splice(i+1,0,{sectionStartPos:e.sectionStartPos,sectionEndPos:e.sectionEndPos,pts:e.pts,randomAccessIndicator:e.randomAccessIndicator}),!0},ur=class{constructor(e,t){this.currentPos=0,this.pesPackets=[],this.currentPesPacketIndex=0,this.currentPesPacketPos=0,this.endPos=0,this.lastSuppliedPesPacket=null,this.nextPts=null,this.suppliedPacket=null,this.elementaryStream=e,this.pid=e.pid,this.demuxer=e.demuxer,this.startingPesPacket=t}ensureBuffered(e){let t=this.endPos-this.currentPos;return t>=e?e:this.bufferData(e-t).then(()=>Math.min(this.endPos-this.currentPos,e))}getCurrentPesPacket(){let e=this.pesPackets[this.currentPesPacketIndex];return g(e),e}async bufferData(e){let t=this.endPos+e;for(;this.endPos<t;){let i;if(this.pesPackets.length===0)i=this.startingPesPacket;else{let n=$(this.pesPackets).sectionEndPos;for(g(n!==null);;){let a=await this.demuxer.readPacketHeader(n);if(!a)return;if(a.pid===this.pid){let s=await this.demuxer.readSection(n,!0);if(!s)return;let o=Vr(this.demuxer,s,!1);if(o){i=o;break}}n+=this.demuxer.packetStride}}this.pesPackets.push(i),this.endPos+=i.data.byteLength}}readBytes(e){let t=this.getCurrentPesPacket(),i=this.currentPos-this.currentPesPacketPos,n=i+e;if(this.currentPos+=e,n<=t.data.byteLength)return t.data.subarray(i,n);let a=new Uint8Array(e);a.set(t.data.subarray(i));let s=t.data.byteLength-i;for(;;){this.advanceCurrentPacket();let o=this.getCurrentPesPacket(),c=e-s;if(c<=o.data.byteLength){a.set(o.data.subarray(0,c),s);break}a.set(o.data,s),s+=o.data.byteLength}return a}readU8(){let e=this.getCurrentPesPacket(),t=this.currentPos-this.currentPesPacketPos;if(this.currentPos++,t<e.data.byteLength)return e.data[t];do this.advanceCurrentPacket(),e=this.getCurrentPesPacket();while(e.data.byteLength===0);return e.data[0]}seekTo(e){if(e!==this.currentPos){if(e<this.currentPos)for(;e<this.currentPesPacketPos;){this.currentPesPacketIndex--;let t=this.getCurrentPesPacket();this.currentPesPacketPos-=t.data.byteLength}else for(;;){let t=this.getCurrentPesPacket(),i=this.currentPesPacketPos+t.data.byteLength;if(e<i)break;this.currentPesPacketPos+=t.data.byteLength,this.currentPesPacketIndex++}this.currentPos=e}}skip(e){this.seekTo(this.currentPos+e)}advanceCurrentPacket(){this.currentPesPacketPos+=this.getCurrentPesPacket().data.byteLength,this.currentPesPacketIndex++}async markNextPacket(){g(!this.suppliedPacket);let e=this.elementaryStream;if(e.info.type==="video"){let t=e.info.codec,i=1024;if(t!=="avc"&&t!=="hevc")throw new Error("Unhandled.");let n=t==="avc"?1:2,a=null,s=!1,o=0;for(;;){let c=this.ensureBuffered(i);if(P(c)&&(c=await c),c===0)break;let l=this.currentPos,u=this.readBytes(c),d=u.byteLength,f=0;for(;f<d;){let m=u.indexOf(0,f);if(m===-1||m>=d)break;f=m;let p=l+f;if(f+3>=d){this.seekTo(p);break}let h=u[f+1],k=u[f+2],w=u[f+3],S=0;if(h===0&&k===0&&w===1?S=4:h===0&&k===1&&(S=3),S===0){f++;continue}let b=p;a??=b;let T=f+S,y=T+n,A=6;if(y+(t==="avc"?A:1)>d){this.seekTo(p);break}let C=u[T],E,I,R,D;if(t==="avc")E=ln(C),I=E===he.NON_IDR_SLICE||E===he.SLICE_DPA||E===he.IDR,R=E===he.SEI||E===he.SPS||E===he.PPS||E===he.AUD,D=E===he.AUD;else{if(E=ki(C),((C&1)<<5|u[T+1]>>3)>0){f+=S;continue}I=E<=se.RASL_R||E>=se.BLA_W_LP&&E<=21,R=E>=se.VPS_NUT&&E<=37||E===se.PREFIX_SEI_NUT||E>=41&&E<=44||E>=48&&E<=55,D=E===se.AUD_NUT}let O=!1;if(I){let V;if(t==="avc"){let z=u.subarray(y,y+A),j=F(new q(z));V=!s||j<=o,o=j}else V=u[y]>>7===1;V&&(s?O=!0:s=!0)}else R&&s?O=!0:D&&(a=b);if(O){let V=b-a;return this.seekTo(a),this.supplyPacket(V,0)}f+=S}if(c<i)break}if(s){g(a!==null);let c=this.endPos-a;return this.seekTo(a),this.supplyPacket(c,0)}}else{let t=e.info.codec,i=128;for(;;){let n=this.ensureBuffered(i);P(n)&&(n=await n);let a=this.currentPos;for(;this.currentPos-a<n;){let s=this.readU8();if(t==="aac"){if(s!==255)continue;this.skip(-1);let o=this.currentPos,c=this.ensureBuffered(Ze);if(P(c)&&(c=await c),c<Ze)return;let l=this.readBytes(Ze),u=Je(Se.tempFromBytes(l));if(u){this.seekTo(o);let d=this.ensureBuffered(u.frameLength);return P(d)&&(d=await d),this.supplyPacket(d,Math.round(jn*xe/e.info.sampleRate))}else this.seekTo(o+1)}else if(t==="mp3"){if(s!==255)continue;this.skip(-1);let o=this.currentPos,c=this.ensureBuffered(4);if(P(c)&&(c=await c),c<4)return;let l=this.readBytes(4),u=W(l).getUint32(0),d=gi(u,null);if(d.header){this.seekTo(o);let f=this.ensureBuffered(d.header.totalSize);P(f)&&(f=await f);let m=d.header.audioSamplesInFrame*xe/e.info.sampleRate;return this.supplyPacket(f,Math.round(m))}else this.seekTo(o+1)}else if(t==="ac3"){if(s!==11)continue;this.skip(-1);let o=this.currentPos,c=this.ensureBuffered(5);if(P(c)&&(c=await c),c<5)return;let l=this.readBytes(5);if(l[0]!==11||l[1]!==119){this.seekTo(o+1);continue}let u=l[4]>>6,d=l[4]&63;if(u===3||d>37){this.seekTo(o+1);continue}let f=Eo[3*d+u];g(f!==void 0),this.seekTo(o),c=this.ensureBuffered(f),P(c)&&(c=await c);let m=Math.round(_o*xe/e.info.sampleRate);return this.supplyPacket(c,m)}else if(t==="eac3"){if(s!==11)continue;this.skip(-1);let o=this.currentPos,c=this.ensureBuffered(5);if(P(c)&&(c=await c),c<5)return;let l=this.readBytes(5);if(l[0]!==11||l[1]!==119){this.seekTo(o+1);continue}let d=(((l[2]&7)<<8|l[3])+1)*2,m=l[4]>>6===3?3:l[4]>>4&3,p=Xs[m];this.seekTo(o),c=this.ensureBuffered(d),P(c)&&(c=await c);let h=p*256,k=Math.round(h*xe/e.info.sampleRate);return this.supplyPacket(c,k)}else if(t==="dts"){if(s!==127&&s!==100)continue;this.skip(-1);let o=this.currentPos,c=this.ensureBuffered(Ti);if(P(c)&&(c=await c),c<Ti)return;let l=this.readBytes(Ti),u=$s(l),d=u?null:Ai(l);if(!u&&!d){this.seekTo(o+1);continue}if(d&&!d.asset){this.seekTo(o);let h=Math.min(d.frameSize,vo),k=this.ensureBuffered(h);P(k)&&(k=await k),d=Ai(this.readBytes(k))??d}let f=u?u.frameSize:d.frameSize;if(u){let h=Math.ceil(u.frameSize/4)*4;for(;;){this.seekTo(o);let k=h+xn,w=this.ensureBuffered(k);if(P(w)&&(w=await w),w<k)break;this.seekTo(o+h);let S=Ai(this.readBytes(xn));if(!S)break;h+=S.frameSize,f=h}}let m=u?.sampleCount??d.asset?.sampleCount;if(m===void 0){this.seekTo(o+1);continue}this.seekTo(o),c=this.ensureBuffered(f),P(c)&&(c=await c);let p=Math.round(m*xe/e.info.sampleRate);return this.supplyPacket(c,p)}else throw new Error("Unhandled.")}if(n<i)break}}}supplyPacket(e,t){let i=this.getCurrentPesPacket(),n;if(this.lastSuppliedPesPacket===i)g(this.nextPts!==null),n=this.nextPts;else{if(i.pts===null)throw new Error(xc);n=i.pts,wa(this.elementaryStream,i)}this.lastSuppliedPesPacket=i,this.nextPts=n+t;let a=i.sectionStartPos,s=a+(this.currentPos-this.currentPesPacketPos),o=this.readBytes(e),c=i.randomAccessIndicator;if(c===0&&!this.elementaryStream.canBeTrustedWithKeyPackets){if(this.elementaryStream.info.type==="audio")c=1;else if(this.elementaryStream.info.decoderConfig){let l=yn(this.elementaryStream.info.codec,this.elementaryStream.info.decoderConfig,o)==="key";c=Number(l)}}this.suppliedPacket={pts:n,data:o,sequenceNumber:s,sectionStartPos:a,randomAccessIndicator:c},this.pesPackets.splice(0,this.currentPesPacketIndex),this.currentPesPacketIndex=0}},Fi=class{constructor(e,t){this.decodeOrderPackets=[],this.reorderBuffer=[],this.presentationOrderPackets=[],this.reachedEnd=!1,this.lastDuration=0,this.backing=e,this.context=t,this.reorderSize=e.getReorderSize(),g(this.reorderSize>=0)}async readNext(){if(this.decodeOrderPackets.length===0&&!await this.readNextPacket())return null;await this.ensureCurrentPacketHasNext();let e=this.decodeOrderPackets[0],t=this.presentationOrderPackets.indexOf(e),i;for(t===-1||t===this.presentationOrderPackets.length-1?i=this.lastDuration:(i=this.presentationOrderPackets[t+1].pts-e.pts,this.lastDuration=i),this.decodeOrderPackets.shift();this.presentationOrderPackets.length>0;){let n=this.presentationOrderPackets[0];if(this.decodeOrderPackets.includes(n))break;this.presentationOrderPackets.shift()}return{packet:e,duration:i}}async readNextPacket(){if(this.reachedEnd)return!1;let e;return this.context.suppliedPacket?e=this.context.suppliedPacket:(await this.context.markNextPacket(),e=this.context.suppliedPacket),this.context.suppliedPacket=null,e?(this.decodeOrderPackets.push(e),this.processPacketThroughReorderBuffer(e),!0):(this.reachedEnd=!0,this.flushReorderBuffer(),!1)}async ensureCurrentPacketHasNext(){let e=this.decodeOrderPackets[0];for(g(e);;){let t=this.presentationOrderPackets.indexOf(e);if(t!==-1&&t<=this.presentationOrderPackets.length-2||this.decodeOrderPackets.length>4*(this.reorderSize+1)||!await this.readNextPacket())break}}processPacketThroughReorderBuffer(e){if(this.reorderBuffer.push(e),this.reorderBuffer.length>this.reorderSize){let t=0;for(let n=1;n<this.reorderBuffer.length;n++)this.reorderBuffer[n].pts<this.reorderBuffer[t].pts&&(t=n);let i=this.reorderBuffer[t];this.presentationOrderPackets.push(i),this.reorderBuffer.splice(t,1)}}flushReorderBuffer(){this.reorderBuffer.sort((e,t)=>e.pts-t.pts),this.presentationOrderPackets.push(...this.reorderBuffer),this.reorderBuffer.length=0}};var Jn="application/vnd.apple.mpegurl",ba="#EXT-X-STREAM-INF:",Ta="#EXT-X-I-FRAME-STREAM-INF:",Sa="#EXT-X-MEDIA:",Hr="#EXT-X-DEFINE:",Mi="#EXTINF:",Aa="#EXT-X-MAP:",xa="#EXT-X-KEY:",Ca="#EXT-X-MEDIA-SEQUENCE:",Pa="#EXT-X-BYTERANGE:",Ea="#EXT-X-PROGRAM-DATE-TIME:",Cc="#EXT-X-DISCONTINUITY",_a="#EXT-X-DISCONTINUITY-SEQUENCE:",Ia="#EXT-X-TARGETDURATION:",Pc="#EXT-X-ENDLIST",va="#EXT-X-PLAYLIST-TYPE:",Ec="#EXT-X-I-FRAMES-ONLY",dr="com.apple.streaming.transportStreamTimestamp",es=r=>r.length===0||r.startsWith("#")&&!r.startsWith("#EXT"),dt=class{constructor(e,t){this._attributes={};let i="",n="",a=!1,s=!1,o=!1,c=()=>{if(!i)return;let l=i.trim().toLowerCase();Object.prototype.hasOwnProperty.call(this._attributes,l)&&H._warn(`Duplicate AttributeName "${l}"; using last value`);let u=o||n.startsWith("0x")||n.startsWith("0X");this._attributes[l]=u&&t?t.substitute(n):n,i="",n="",a=!1,o=!1};for(let l=0;l<e.length;l++){let u=e[l];u==='"'?(a&&!s&&n.length===0&&(o=!0),s=!s):u==="="&&!a&&!s?a=!0:u===","&&!s?c():a?n+=u:i+=u}if(s)throw new Error("Invalid M3U8 file; unterminated quoted-string AttributeValue.");c()}get(e){return this._attributes[e.toLowerCase()]??null}getAsNumber(e){let t=this.get(e);if(t===null)return null;let i=Number(t);return Number.isFinite(i)?i:null}merge(e){Object.assign(this._attributes,e._attributes)}},Cu=/^[A-Za-z0-9_-]+$/,Pu=/\{\$([A-Za-z0-9_-]+)\}/g,Eu=2**26,Lr=class{constructor(e,t){this.playlistPath=e,this.importedVariables=t,this.variables=new Map,this.totalSubstitutedLength=0}define(e){let t=new dt(e,this),i=t.get("name"),n=t.get("import"),a=t.get("queryparam");if([i,n,a].filter(o=>o!==null).length!==1)throw new Error("Invalid #EXT-X-DEFINE tag; exactly one of NAME, IMPORT, or QUERYPARAM must be present.");if(i!==null){let o=t.get("value");if(o===null)throw new Error("Invalid #EXT-X-DEFINE tag; NAME requires VALUE.");this.set(i,o)}else if(n!==null){let o=this.importedVariables?.get(n);if(o===void 0)throw new Error(`Invalid #EXT-X-DEFINE tag; cannot import undefined variable "${n}".`);this.set(n,o)}else if(a!==null){let o=oo(this.playlistPath,a);if(o===null)throw new Error(`Invalid #EXT-X-DEFINE tag; query parameter "${a}" is missing.`);this.set(a,o)}}substitute(e){return e.replaceAll(Pu,(t,i)=>{let n=this.variables.get(i);if(n===void 0)throw new Error(`Invalid M3U8 file; variable "${i}" is referenced before being defined.`);if(this.totalSubstitutedLength+=n.length,this.totalSubstitutedLength>Eu)throw new Error("Invalid M3U8 file; variable substitution produces an excessive amount of data.");return n})}get(e){return this.variables.get(e)}set(e,t){if(!Cu.test(e))throw new Error(`Invalid #EXT-X-DEFINE tag; invalid variable name "${e}".`);if(this.variables.has(e))throw new Error(`Invalid #EXT-X-DEFINE tag; variable "${e}" is already defined.`);this.variables.set(e,t)}};var ts=class{constructor(e,t,i){this.nextInputCacheAge=0,this.inputCache=[],this.trackBackingsPromise=null,this.firstSegment=null,this.learnedSegmentTimestampOffset=null,this.segmentMediaOffsets=new WeakMap,this.input=e,this.path=t,this.trackDeclarations=i}async getDurationFromMetadata(e){let t=await this.getSegmentAt(1/0,{skipLiveWait:e.skipLiveWait});return t?t.timestamp+await this.getFirstSegmentTimestampOffset()+t.duration:null}async getUnixTimeForTimestamp(e){let t=await this.getSegmentAt(e,{});if(t??=await this.getFirstSegment({}),!t||t.unixEpochTimestamp===null)return null;let i=e-(t.timestamp+await this.getFirstSegmentTimestampOffset());return t.unixEpochTimestamp+i}async getTrackBackings(){return this.trackBackingsPromise??=(async()=>{let e=[];if(this.trackDeclarations){for(let t of this.trackDeclarations)if(t.type==="video"){let i=tr(e,n=>n.getType()==="video")+1;e.push(new is(this,t,i))}else if(t.type==="audio"){let i=tr(e,n=>n.getType()==="audio")+1;e.push(new ns(this,t,i))}}else{if(this.firstSegment=await this.getFirstSegment({}),!this.firstSegment)return[];let i=await this.getInputForSegment(this.firstSegment).getTracks();for(let n of i)if(n.type==="video"){let a=tr(e,s=>s.getType()==="video")+1;e.push(new is(this,{id:e.length+1,type:"video"},a))}else if(n.type==="audio"){let a=tr(e,s=>s.getType()==="audio")+1;e.push(new ns(this,{id:e.length+1,type:"audio"},a))}}return e})()}getMediaOffset(e,t){let i=this.segmentMediaOffsets.get(e);return i||(i=(async()=>{let n=await this.getRawTimestampOffset(t);if(n===null)return e.timestamp;let a=n+await this.getMediaOffsetForDiscontinuity(e.discontinuityNumber),s=this.getTimestampWrapPeriod();if(s<1/0){let o=await t.getTracks(),c=o.find(u=>u.type==="video")??o[0];g(c);let l=await c.getFirstTimestamp()+a;a+=s*Math.round((e.timestamp-l)/s)}return a})(),this.segmentMediaOffsets.set(e,i),i)}dispose(){for(let e of this.inputCache)e.input.dispose();this.inputCache.length=0}},rs=class{constructor(e,t,i){this.packetInfos=new WeakMap,this.hydrationPromise=null,this.firstInputTrack=null,this.firstSegment=null,this.segmentedInput=e,this.decl=t,this.number=i}hydrate(){return this.hydrationPromise??=(async()=>{if(this.segmentedInput.firstSegment??=await this.segmentedInput.getFirstSegment({}),!this.segmentedInput.firstSegment)throw new Error("Missing first segment, can't retrieve track.");let e=this.segmentedInput.firstSegment,t=null;for(;e&&(t=(await this.segmentedInput.getInputForSegment(e).getTracks()).find(a=>a.type===this.decl.type&&a.number===this.number)??null,!t);)e=await this.segmentedInput.getNextSegment(e,{});if(!t)throw new Error("No matching track found in underlying media data.");this.firstInputTrack=t,this.firstSegment=e})()}getId(){return this.decl.id}getType(){return this.decl.type}getNumber(){return this.number}delegate(e){return this.firstInputTrack?e():this.hydrate().then(e)}async getDecoderConfig(){return this.delegate(()=>this.firstInputTrack._backing.getDecoderConfig())}getHasOnlyKeyPackets(){return this.delegate(()=>this.firstInputTrack._backing.getHasOnlyKeyPackets?.()??null)}getPairingMask(){return 1n}getCodec(){return this.delegate(()=>this.firstInputTrack._backing.getCodec())}getInternalCodecId(){return this.delegate(()=>this.firstInputTrack._backing.getInternalCodecId())}getDisposition(){return this.delegate(()=>this.firstInputTrack._backing.getDisposition())}getLanguageCode(){return this.delegate(()=>this.firstInputTrack._backing.getLanguageCode())}getName(){return this.delegate(()=>this.firstInputTrack._backing.getName())}getTimeResolution(){return this.delegate(()=>this.firstInputTrack._backing.getTimeResolution())}async isRelativeToUnixEpoch(){return await this.hydrate(),g(this.segmentedInput.firstSegment),this.segmentedInput.firstSegment.unixEpochTimestamp===this.segmentedInput.firstSegment.timestamp}getUnixTimeForTimestamp(e){return this.segmentedInput.getUnixTimeForTimestamp(e)}getBitrate(){return this.delegate(()=>this.firstInputTrack._backing.getBitrate())}getAverageBitrate(){return this.delegate(()=>this.firstInputTrack._backing.getAverageBitrate())}getDurationFromMetadata(e){return this.segmentedInput.getDurationFromMetadata(e)}getLiveRefreshInterval(){return this.segmentedInput.getLiveRefreshInterval()}async createAdjustedPacket(e,t,i){g(e.sequenceNumber>=0),g(this.segmentedInput.firstSegment);let n=await this.segmentedInput.getMediaOffset(t,i.input),a=t.timestamp-this.segmentedInput.firstSegment.timestamp,s=e.clone({timestamp:Ji(e.timestamp+n,await i.getTimeResolution()),sequenceNumber:Math.floor(1e8*a)+e.sequenceNumber});return this.packetInfos.set(s,{segment:t,track:i,sourcePacket:e}),s}async getFirstPacket(e){await this.hydrate(),g(this.firstInputTrack),g(this.firstSegment);let t=this.firstInputTrack,i=this.firstSegment;for(;;){if(t){let s=await t._backing.getFirstPacket(e);if(s)return this.createAdjustedPacket(s,i,t)}if(i=await this.segmentedInput.getNextSegment(i,{skipLiveWait:e.skipLiveWait}),!i)break;t=(await this.segmentedInput.getInputForSegment(i).getTracks()).find(s=>s.type===this.firstInputTrack.type&&s.number===this.firstInputTrack.number)??null}return null}getNextPacket(e,t){return this._getNextInternal(e,t,!1)}getNextKeyPacket(e,t){return this._getNextInternal(e,t,!0)}async _getNextInternal(e,t,i){let n=this.packetInfos.get(e);if(!n)throw new Error("Packet was not created from this track.");let a=i?await n.track._backing.getNextKeyPacket(n.sourcePacket,t):await n.track._backing.getNextPacket(n.sourcePacket,t);if(a)return this.createAdjustedPacket(a,n.segment,n.track);let s=n.segment;for(;;){let o=await this.segmentedInput.getNextSegment(s,{skipLiveWait:t.skipLiveWait});if(!o)return null;let u=(await this.segmentedInput.getInputForSegment(o).getTracks()).find(f=>f.type===n.track.type&&f.number===n.track.number);if(!u){s=o;continue}let d=await u._backing.getFirstPacket(t);if(d&&i&&d.type!=="key"&&(d=await u._backing.getNextKeyPacket(d,t)),!d){s=o;continue}return this.createAdjustedPacket(d,o,u)}}getPacket(e,t){return this._getPacketInternal(e,t,!1)}getKeyPacket(e,t){return this._getPacketInternal(e,t,!0)}async _getPacketInternal(e,t,i){let n=await this.segmentedInput.getSegmentAt(e,{skipLiveWait:t.skipLiveWait});if(!n)return null;for(await this.hydrate();n;){let a=this.segmentedInput.getInputForSegment(n),o=(await a.getTracks()).find(m=>m.type===this.firstInputTrack.type&&m.number===this.firstInputTrack.number);if(!o){n=await this.segmentedInput.getPreviousSegment(n,{skipLiveWait:t.skipLiveWait});continue}let c=await this.segmentedInput.getMediaOffset(n,a),l=this.segmentedInput.learnedSegmentTimestampOffset===null?await o._backing.getFirstPacket({...t,metadataOnly:!0}):null;if(l){let m=l.timestamp+c;this.segmentedInput.learnedSegmentTimestampOffset=m-n.timestamp;let p=e-m;if(p<-n.duration||p>=2*n.duration){let h=await this.segmentedInput.getSegmentAt(e,{skipLiveWait:t.skipLiveWait});if(h!==n){n=h;continue}}}let u=e-c,d=i?await o._backing.getKeyPacket(u,t):await o._backing.getPacket(u,t);if(!d){n=await this.segmentedInput.getPreviousSegment(n,{skipLiveWait:t.skipLiveWait});continue}let f=i?await o._backing.getPacket(u,{...t,metadataOnly:!0}):d;if(g(f),u>=f.timestamp+f.duration){let m=await this.segmentedInput.getNextSegment(n,{skipLiveWait:t.skipLiveWait});if(m){let p=this.segmentedInput.getInputForSegment(m),k=(await p.getTracks()).find(S=>S.type===this.firstInputTrack.type&&S.number===this.firstInputTrack.number),w=k?await k._backing.getFirstPacket({...t,metadataOnly:!0}):null;if(w&&i&&w.type!=="key"&&(w=await k._backing.getNextKeyPacket(w,{...t,metadataOnly:!0})),w){let S=await this.segmentedInput.getMediaOffset(m,p);if(w.timestamp+S<=e){n=m;continue}}}}return this.createAdjustedPacket(d,n,o)}return null}},is=class extends rs{getType(){return"video"}getCodec(){return this.delegate(()=>this.firstInputTrack._backing.getCodec())}getCodedWidth(){return this.delegate(()=>this.firstInputTrack._backing.getCodedWidth())}getCodedHeight(){return this.delegate(()=>this.firstInputTrack._backing.getCodedHeight())}getSquarePixelWidth(){return this.delegate(()=>this.firstInputTrack._backing.getSquarePixelWidth())}getSquarePixelHeight(){return this.delegate(()=>this.firstInputTrack._backing.getSquarePixelHeight())}getTransformationMatrix(){return this.delegate(()=>this.firstInputTrack._backing.getTransformationMatrix())}async getColorSpace(){return this.delegate(()=>this.firstInputTrack._backing.getColorSpace())}async canBeTransparent(){return this.delegate(()=>this.firstInputTrack._backing.canBeTransparent())}async getDecoderConfig(){return this.delegate(()=>this.firstInputTrack._backing.getDecoderConfig())}},ns=class extends rs{getType(){return"audio"}getCodec(){return this.delegate(()=>this.firstInputTrack._backing.getCodec())}getNumberOfChannels(){return this.delegate(()=>this.firstInputTrack._backing.getNumberOfChannels())}getSampleRate(){return this.delegate(()=>this.firstInputTrack._backing.getSampleRate())}async getDecoderConfig(){return this.delegate(()=>this.firstInputTrack._backing.getDecoderConfig())}};rn();var Ba=0,Fa=1/0,_u=null;typeof FinalizationRegistry<"u"&&(_u=new FinalizationRegistry(r=>{r()}));var ve=class extends Ne{constructor(){super(),this._disposed=!1,this._refCount=0,this._usedForHls=!1,this._refFinalizationRegistry=null,this._sizePromise=null,this.onread=null,typeof FinalizationRegistry<"u"&&(this._refFinalizationRegistry=new FinalizationRegistry(e=>{e._decrementRefCount()}))}async getSizeOrNull(){if(this._disposed)throw new ue;return this._sizePromise??=(async()=>{let e=this._getFileSize();return e!==void 0||(await this._read(0,1,Ba,Fa),e=this._getFileSize(),g(e!==void 0)),e})()}async getSize(){if(this._disposed)throw new ue;let e=await this.getSizeOrNull();if(e===null)throw new Error("Cannot determine the size of an unsized source.");return e}slice(e,t){if(!Number.isInteger(e)||e<0)throw new TypeError("offset must be a non-negative integer.");if(t!==void 0&&(!Number.isInteger(t)||t<0))throw new TypeError("length, when provided, must be a non-negative integer.");return new ss(this,e,t)}_dispatchRead(e,t){this.onread?.(e,t),this._emit("read",{start:e,end:t})}ref(){return new fr(this)}_incrementRefCount(){this._refCount++}_decrementRefCount(){this._refCount--,this._refCount===0&&(this._dispose(),this._disposed=!0)}},fr=class{constructor(e){if(this._freed=!1,e._disposed)throw new Error("Cannot ref a disposed source.");e._incrementRefCount(),e._refFinalizationRegistry?.register(this,e,this),this._source=e}get source(){if(!this._source)throw new Error("Can't get source; ref has already been freed.");return this._source}get freed(){return this._freed}free(){if(this._freed)throw new Error("Illegal operation: double free on SourceRef.");let e=this.source;g(e._refCount>0),e._decrementRefCount(),e._refFinalizationRegistry?.unregister(this),this._freed=!0,this._source=null}[Symbol.dispose](){this.freed||this.free()}},We=class extends ve{constructor(e,t){if(typeof e!="string")throw new TypeError("rootPath must be a string.");if(typeof t!="function")throw new TypeError("requestHandler must be a function.");super(),this.rootPath=e,this.requestHandler=t}_resolveRequest(e){let t=this.requestHandler(e),i=n=>{if(!(n instanceof ve||n instanceof fr))throw new TypeError("requestHandler must return or resolve to a Source or SourceRef.");let a=n instanceof ve?n.ref():n;return a.source._usedForHls||=this._usedForHls,a};return P(t)?t.then(i):i(t)}},Ma=(r,e)=>r.path===e.path,Di=class extends We{constructor(){super(...arguments),this._root=null,this._rootRequest=null}_read(e,t,i,n){if(!this._root){if(!this._rootRequest){let a=this._resolveRequest({path:this.rootPath,isRoot:!0}),s=o=>{let c=o instanceof ve?o.ref():o;return this._root=c,this._rootRequest=null,c};P(a)?this._rootRequest=a.then(s):(s(a),g(this._root))}if(this._rootRequest)return this._rootRequest.then(a=>a.source._read(e,t,i,n))}return this._root.source._read(e,t,i,n)}_getFileSize(){if(this._root)return this._root.source._getFileSize()}_dispose(){this._root?this._root.free():this._rootRequest&&this._rootRequest.then(e=>e.free()).catch(()=>{})}},Oi=class extends ve{constructor(e){if(!(e instanceof ArrayBuffer)&&!(typeof SharedArrayBuffer<"u"&&e instanceof SharedArrayBuffer)&&!ArrayBuffer.isView(e))throw new TypeError("buffer must be an ArrayBuffer, SharedArrayBuffer, or ArrayBufferView.");super(),this._onreadCalled=!1,this._bytes=ke(e),this._view=W(e)}_getFileSize(){return this._bytes.byteLength}_read(){return this._onreadCalled||(this._dispatchRead(0,this._bytes.byteLength),this._onreadCalled=!0),{bytes:this._bytes,view:this._view,offset:0}}_dispose(){}},tp=typeof FinalizationRegistry<"u"?new FinalizationRegistry(r=>{r.cancel().catch(()=>{})}):null;var rp=.5*2**20;var Ui=class extends ve{constructor(e,t={}){if(!(e instanceof ReadableStream))throw new TypeError("stream must be a ReadableStream.");if(!t||typeof t!="object")throw new TypeError("options must be an object.");if(t.handleUnhandledError!==void 0&&typeof t.handleUnhandledError!="function")throw new TypeError("options.handleUnhandledError, when provided, must be a function.");if(t.maxCacheSize!==void 0&&(!Mt(t.maxCacheSize)||t.maxCacheSize<0))throw new TypeError("options.maxCacheSize, when provided, must be a non-negative number.");super(),this._reader=null,this._cache=[],this._pendingSlices=[],this._currentIndex=0,this._targetIndex=0,this._maxRequestedIndex=0,this._endIndex=null,this._pulling=!1,this._cacheMissErrorMessage="Attempted to read data from an already-evicted part of the cache. With ReadableStreamSource, you must access the data more sequentially or increase the size of its cache.",this._stream=e,this._maxCacheSize=t.maxCacheSize??32*2**20,this._handleUnhandledError=t.handleUnhandledError}_getFileSize(){return this._endIndex}_read(e,t){if(this._endIndex!==null&&t>this._endIndex)return null;this._maxRequestedIndex=Math.max(this._maxRequestedIndex,t);let i=Q(this._cache,e,u=>u.start),n=i!==-1?this._cache[i]:null;if(n&&n.start<=e&&t<=n.end)return{bytes:n.bytes,view:n.view,offset:n.start};let a=e,s=[];if(i!==-1)for(let u=i;u<this._cache.length;u++){let d=this._cache[u];if(d.start>=t)break;let f=Math.max(e,d.start);f>a&&this._throwDueToCacheMiss();let m=Math.min(t,d.end);f<m&&(s.push({start:f,bytes:d.bytes.subarray(f-d.start,m-d.start)}),a=m)}if(a===t)return _c(e,t,s);this._currentIndex>a&&this._throwDueToCacheMiss();let{promise:o,resolve:c,reject:l}=gt();return this._pendingSlices.push({start:e,end:t,parts:s,resolve:c,reject:l}),this._targetIndex=Math.max(this._targetIndex,t),this._pulling||(this._pulling=!0,this._pull().catch(u=>{if(this._pulling=!1,this._pendingSlices.length>0)this._pendingSlices.forEach(d=>d.reject(u)),this._pendingSlices.length=0;else if(this._handleUnhandledError)this._handleUnhandledError(u);else throw u})),o}_throwDueToCacheMiss(){throw new Error(this._cacheMissErrorMessage)}async _pull(){for(this._reader??=this._stream.getReader();this._currentIndex<this._targetIndex&&!this._disposed;){let{done:e,value:t}=await this._reader.read();if(e){for(let a of this._pendingSlices)a.resolve(null);this._pendingSlices.length=0,this._endIndex=this._currentIndex;break}let i=this._currentIndex,n=this._currentIndex+t.byteLength;this._dispatchRead(i,n);for(let a=0;a<this._pendingSlices.length;a++){let s=this._pendingSlices[a],o=Math.max(i,s.start),c=Math.min(n,s.end);o<c&&(s.parts.push({start:o,bytes:t.subarray(o-i,c-i)}),c===s.end&&(s.resolve(_c(s.start,s.end,s.parts)),this._pendingSlices.splice(a,1),a--))}for(this._cache.push({start:i,end:n,bytes:t,view:W(t),age:0});this._cache.length>0;){let a=this._cache[0];if(this._maxRequestedIndex-a.end<=this._maxCacheSize)break;this._cache.shift()}this._currentIndex+=t.byteLength}this._pulling=!1}_dispose(){for(let e of this._pendingSlices)e.reject(new ue);this._pendingSlices.length=0,this._cache.length=0,this._reader?.cancel().catch(()=>{})}},_c=(r,e,t)=>{let i=new Uint8Array(e-r);for(let n of t)i.set(n.bytes,n.start-r);return{bytes:i,view:W(i),offset:r}};var ss=class extends ve{constructor(e,t,i){if(super(),this._ref=null,e._disposed)throw new Error("Cannot create a slice of a disposed source.");this._baseSource=e,this._offset=t,this._length=i??null}_getFileSize(){let e=this._baseSource._getFileSize();return e===void 0?this._length!==null?this._length:void 0:e===null?this._length!==null?this._length:null:st(e-this._offset,0,this._length??1/0)}_read(e,t,i,n){if(this._length!==null&&t>this._length)return null;let a=this._baseSource._read(this._offset+e,this._offset+t,this._offset+i,this._offset+n),s=o=>o?(o.offset-=this._offset,o):null;return P(a)?a.then(s):s(a)}_dispose(){this._ref?.free()}ref(){return this._ref??=this._baseSource.ref(),super.ref()}};var Ic=function(r,e,t){if(e!=null){if(typeof e!="object"&&typeof e!="function")throw new TypeError("Object expected.");var i,n;if(t){if(!Symbol.asyncDispose)throw new TypeError("Symbol.asyncDispose is not defined.");i=e[Symbol.asyncDispose]}if(i===void 0){if(!Symbol.dispose)throw new TypeError("Symbol.dispose is not defined.");i=e[Symbol.dispose],t&&(n=i)}if(typeof i!="function")throw new TypeError("Object not disposable.");n&&(i=function(){try{n.call(this)}catch(a){return Promise.reject(a)}}),r.stack.push({value:e,dispose:i,async:t})}else t&&r.stack.push({async:!0});return e},vc=(function(r){return function(e){function t(s){e.error=e.hasError?new r(s,e.error,"An error was suppressed during disposal."):s,e.hasError=!0}var i,n=0;function a(){for(;i=e.stack.pop();)try{if(!i.async&&n===1)return n=0,e.stack.push(i),Promise.resolve().then(a);if(i.dispose){var s=i.dispose.call(i.value);if(i.async)return n|=2,Promise.resolve(s).then(a,function(o){return t(o),a()})}else n|=1}catch(o){t(o)}if(n===1)return e.hasError?Promise.reject(e.error):Promise.resolve();if(e.hasError)throw e.error}return a()}})(typeof SuppressedError=="function"?SuppressedError:function(r,e,t){var i=new Error(t);return i.name="SuppressedError",i.error=r,i.suppressed=e,i}),Iu=/^0[xX][0-9a-fA-F]+$/,vu=/^data:.*;base64,/i,Rc=1e9,zi=class extends ts{constructor(e,t,i,n){super(e.input,t,i),this.segments=[],this.nextLines=null,this.currentUpdateSegmentsPromise=null,this.streamHasEnded=!1,this.neverRemovesSegments=!1,this.lastSegmentUpdateTime=-1/0,this.refreshInterval=5,this.segmentTimestampOffsetPromise=null,this.rootPath=t,this.demuxer=e,this.nextLines=n}runUpdateSegments(){return this.currentUpdateSegmentsPromise??=(async()=>{try{let e=this.getRemainingWaitTimeMs();e>0&&await Hs(e),this.lastSegmentUpdateTime=performance.now(),await this.updateSegments()}finally{this.currentUpdateSegmentsPromise=null}})()}getRemainingWaitTimeMs(){let e=performance.now()-this.lastSegmentUpdateTime,t=Math.max(0,1e3*this.refreshInterval-e);return t<=50?0:t}async updateSegments(){let e=this.nextLines;if(this.nextLines=null,!e){let b={stack:[],error:void 0,hasError:!1};try{let T=Ic(b,await this.demuxer.input._getSourceUncached({path:this.rootPath,isRoot:!1}),!1),y=new qt(T.source),A=y.requestSliceRange(0,0,64);if(P(A)&&(A=await A),A&&!ie.decode(M(A,A.length)).trimStart().startsWith("#EXTM3U"))throw new Error("Invalid M3U8 file; expected first line to be #EXTM3U.");let x=await y.requestEntireFile();g(x),e=as(x,x.length,{ignore:es}),T.source instanceof We&&(this.rootPath=T.source.rootPath)}catch(T){b.error=T,b.hasError=!0}finally{vc(b)}}let t=this.input._formatOptions.hls?.offsetTimestampsByDateTime!==!1,i=new Lr(this.rootPath,this.demuxer.hasMasterPlaylist?this.demuxer.masterPlaylistVariables:null),n=!1,a=0,s=null,o=null,c=null,l=0,u=0,d=null,f=null,m=null,p=null,h=null,k=$(this.segments)??null,w=b=>{let T=b.indexOf("@"),y=Number(T===-1?b:b.slice(0,T));if(!Number.isInteger(y)||y<0)throw new Error(`Invalid #EXT-X-BYTERANGE length '${b}'.`);let A=null;if(T!==-1&&(A=Number(b.slice(T+1)),!Number.isInteger(A)||A<0))throw new Error(`Invalid #EXT-X-BYTERANGE offset '${b}'.`);return{length:y,offset:A}},S=b=>{l=b,k&&(g(k.sequenceNumber!==null),k.sequenceNumber<b&&(a=k.timestamp+k.duration,d=k.firstSegment,f=k.initSegment,h=k.lastProgramDateTimeSeconds,s=k.unixEpochTimestamp!==null?k.unixEpochTimestamp+k.duration:null,k=null))};for(let b=0;b<e.length;b++){let T=e[b];if(!n){if(T!=="#EXTM3U")throw new Error("Invalid M3U8 file; expected first line to be #EXTM3U.");n=!0;continue}if(!T.startsWith("#")){if(!k){if(o===null)throw new Error("Invalid M3U8 file; a segment must be preceded by an #EXTINF tag.");let y=c;if(y&&y.method==="AES-128"&&!y.iv){let E=new Uint8Array(Ge),I=W(E);I.setUint32(8,Math.floor(l/2**32)),I.setUint32(12,l),y={...y,iv:E}}let x={path:at(this.rootPath,i.substitute(T)),offset:p?.offset??0,length:p?.length??null},C={index:this.segments.length,timestamp:a,unixEpochTimestamp:s,discontinuityNumber:u,firstSegment:d,sequenceNumber:l,location:x,duration:o,encryption:y,initSegment:f,lastProgramDateTimeSeconds:h};d??=C,a+=o,s!==null&&(s+=o),this.segments.push(C)}o=null,p===null?m=null:p=null,S(l+1)}if(T.startsWith(Mi)){if(k)continue;let y=T.slice(Mi.length),A=y.indexOf(","),x=A===-1?y:y.slice(0,A),C=Number(x);if(!Number.isFinite(C)||C<0||C>Rc)throw new Error(`Invalid #EXTINF tag duration '${x}'.`);o=C}else if(T.startsWith(Hr))i.define(T.slice(Hr.length));else if(T.startsWith(Aa)){let y=new dt(T.slice(Aa.length),i),A=y.get("uri");if(!A)throw new Error("Invalid #EXT-X-MAP tag; missing URI attribute.");let x=y.get("byterange"),C=null;if(x!==null&&(C=w(x)),C&&C.offset===null)throw new Error("Invalid #EXT-X-MAP tag; BYTERANGE attribute must have a specified offset.");if(!k){let I={path:at(this.rootPath,A),offset:C?.offset??0,length:C?.length??null};if(c?.method==="AES-128"&&!c.iv)throw new Error("IV attribute must be set on #EXT-X-KEY tag preceding the #EXT-X-MAP tag.");f={index:-1,timestamp:a,unixEpochTimestamp:s,discontinuityNumber:u,firstSegment:null,sequenceNumber:null,location:I,duration:0,encryption:c,initSegment:null,lastProgramDateTimeSeconds:h}}o=null,p===null?m=null:p=null}else if(T.startsWith(xa)){let y=new dt(T.slice(xa.length),i),A=y.get("method");if(A==="NONE")c=null;else if(A==="AES-128"){let x=y.get("uri");if(!x)throw new Error("Invalid #EXT-X-KEY: AES-128 requires a URI attribute.");let C=null,E=y.get("iv");if(E){if(!Iu.test(E))throw new Error(`Unsupported IV format '${E}'.`);let R=E.slice(2);R=R.padStart(2*Ge,"0"),R=R.slice(-2*Ge),C=new Uint8Array(Ge);for(let D=0;D<Ge;D++){let O=2*D;C[D]=parseInt(R.slice(O,O+2),16)}}let I=y.get("keyformat")??"identity";if(I!=="identity")throw new Error("For AES-128 encryption, only the 'identity' KEYFORMAT is currently supported. If you think other formats should be supported, please raise an issue.");c={method:"AES-128",keyUri:at(this.rootPath,x),iv:C,keyFormat:I}}else if(A==="SAMPLE-AES"||A==="SAMPLE-AES-CTR"){let x=y.get("uri");if(!x)throw new Error(`Invalid #EXT-X-KEY: ${A} requires a URI attribute.`);if((y.get("keyformat")??"identity")==="identity")throw new Error("For SAMPLE-AES and SAMPLE-AES-CTR encryption, the 'identity' KEYFORMAT is not supported. If you think this format should be supported, please raise an issue.");let E=null;if(vu.test(x)){let I=x.indexOf(","),R=di(x.slice(I+1));if(R.length>=8&&R[4]===112&&R[5]===115&&R[6]===115&&R[7]===104){let D=W(R).getUint32(0);E=In(R.subarray(8,Math.min(D,R.length)))}}c={method:A,psshBox:E}}else throw new Error(`Unsupported encryption method '${A}'. If you think this method should be supported, please raise an issue.`)}else if(T.startsWith(Ca)){let y=T.slice(Ca.length),A=Number(y);if(!Number.isSafeInteger(A)||A<0)throw new Error(`Invalid EXT-X-MEDIA-SEQUENCE value '${y}'.`);S(A)}else if(T.startsWith(Pa)){let y=w(T.slice(Pa.length));if(y.offset===null){if(m===null)throw new Error("Invalid M3U8 file; #EXT-X-BYTERANGE without offset requires a previous byte range.");y.offset=m}p=y,m=y.offset+y.length}else if(T.startsWith(Ea)){if(k)continue;let y=T.slice(Ea.length),A=Date.parse(y);if(!Number.isFinite(A))continue;let x=A/1e3;if(h===x)continue;if(h===null&&this.segments.length>0){let C=$(this.segments),E=C.timestamp+C.duration,I=x-E;for(let R of this.segments)R.unixEpochTimestamp=R.timestamp+I,t&&(R.timestamp=R.unixEpochTimestamp)}h=x,s=x,t&&(a=x)}else if(T===Cc)d=null,u++;else if(T.startsWith(_a)){let y=T.slice(_a.length),A=Number(y);if(!Number.isSafeInteger(A)||A<0)throw new Error(`Invalid EXT-X-DISCONTINUITY-SEQUENCE value '${y}'.`);u=A}else if(T.startsWith(Ia)){let y=T.slice(Ia.length),A=Number(y);if(!Number.isFinite(A)||A<0||A>Rc)throw new Error(`Invalid EXT-X-TARGETDURATION value '${y}'.`);this.refreshInterval=st(A,.5,3600)}else if(T===Pc){this.streamHasEnded=!0;break}else if(T.startsWith(va)){let y=T.slice(va.length).toLowerCase();y==="vod"&&(this.streamHasEnded=!0),(y==="vod"||y==="event")&&(this.neverRemovesSegments=!0)}}if(!n)throw new Error("Invalid M3U8 file; no #EXTM3U header.")}async getFirstSegment(){return this.segments.length===0&&await this.runUpdateSegments(),this.segments[0]??null}async getSegmentAt(e,t){this.segments.length===0&&await this.runUpdateSegments();let i=e-(this.learnedSegmentTimestampOffset??0),n=!!t.skipLiveWait&&this.getRemainingWaitTimeMs()>0;for(;;){let a=Q(this.segments,i,o=>o.timestamp);if(a===-1)return null;if(a<this.segments.length-1||this.streamHasEnded||n)return this.segments[a];let s=this.segments[a];if(i<s.timestamp+s.duration)return s;await this.runUpdateSegments(),t.skipLiveWait&&(n=!0)}}async getNextSegment(e,t){let i=e.index;g(i!==-1);let n=i+1,a=!!t.skipLiveWait&&this.getRemainingWaitTimeMs()>0;for(;;){if(n<this.segments.length)return this.segments[n];if(this.streamHasEnded||a)return null;await this.runUpdateSegments(),t.skipLiveWait&&(a=!0)}}async getPreviousSegment(e){let t=e.index;return g(t!==-1),this.segments[t-1]??null}getInputForSegment(e){let t=e,i=this.inputCache.find(c=>c.segment===t);if(i)return i.age=this.nextInputCacheAge++,i.input;let n=null;(t.initSegment||t.firstSegment)&&(n=this.getInputForSegment(t.initSegment??t.firstSegment));let a={...this.input._formatOptions,isobmff:{...this.input._formatOptions.isobmff,resolveKeyId:this.input._formatOptions.isobmff?.resolveKeyId&&(c=>{if(!t.encryption||!(t.encryption.method==="SAMPLE-AES"||t.encryption.method==="SAMPLE-AES-CTR")||!t.encryption.psshBox)return this.input._formatOptions.isobmff.resolveKeyId(c);let l=c.psshBoxes,{psshBox:u}=t.encryption;return(u.keyIds===null||u.keyIds.includes(c.keyId))&&!l.some(d=>vn(d,u))&&(l=[...l,u]),this.input._formatOptions.isobmff.resolveKeyId({...c,psshBoxes:l})})}},s=new hr({source:new Di(t.location.path,async c=>{g(c.isRoot);let l={...c,isRoot:!1},u,d=t.location.offset>0||t.location.length!==null;if(!t.encryption||t.encryption.method==="SAMPLE-AES"||t.encryption.method==="SAMPLE-AES-CTR"){if(u=await this.input._getSourceCached(l),d){let m=u.source.slice(t.location.offset,t.location.length??void 0).ref();u.free(),u=m}}else if(t.encryption.method==="AES-128"){let f=t.encryption;g(f.iv);let m=await this.input._getSourceCached(l);if(d){let w=m.source.slice(t.location.offset,t.location.length??void 0).ref();m.free(),m=w}let p=new qt(m.source),h=No(p,async()=>{let k={stack:[],error:void 0,hasError:!1};try{let w=Ic(k,await this.input._getSourceCached({path:f.keyUri,isRoot:!1},Bc),!1),b=await new qt(w.source).requestSlice(0,Ge);if(!b)throw new Error("Invalid AES-128 key; expected at least 16 bytes of data.");return{key:M(b,Ge),iv:f.iv}}catch(w){k.error=w,k.hasError=!0}finally{vc(k)}},()=>{m.free()});u=new Ui(h).ref()}else g(!1);return u}),formats:this.input._formats.filter(c=>!(c instanceof Wr)),initInput:n??void 0,formatOptions:a});if(s._onFormatDetermined=c=>{if((t.encryption?.method==="SAMPLE-AES"||t.encryption?.method==="SAMPLE-AES-CTR")&&!c._isIsobmff)throw new Error("The SAMPLE-AES and SAMPLE-AES-CTR encryption methods are currently only supported for ISOBMFF files.")},this.inputCache.push({segment:t,input:s,age:this.nextInputCacheAge++}),this.inputCache.length>4){let c=Sr(this.inputCache,l=>l.age);g(c!==-1),this.inputCache.splice(c,1)}return s}async getLiveRefreshInterval(){return!this.streamHasEnded&&this.getRemainingWaitTimeMs()===0&&await this.runUpdateSegments(),this.streamHasEnded?null:this.refreshInterval}getMediaOffsetForDiscontinuity(e){return this.demuxer.getMediaOffsetForDiscontinuity(e)}getFirstSegmentTimestampOffset(){return this.segmentTimestampOffsetPromise??=(async()=>{let e=await this.getFirstSegment();g(e);let t=this.demuxer.getReferenceSegmentedInput();if(this===t)return 0;let i=await t.getFirstSegment();if(i&&(this.listsAllSegments()&&t.listsAllSegments()||e.unixEpochTimestamp===e.timestamp&&i.unixEpochTimestamp===i.timestamp))return 0;let n=this.getInputForSegment(e);if(await this.getRawTimestampOffset(n)===null)return 0;let a=await n.getTracks(),s=a.find(l=>l.type==="video")??a[0];if(!s)throw new Error("The playlist's first segment contains no tracks.");let o=await this.getMediaOffset(e,n),c=await s.getFirstTimestamp()+o-e.timestamp;return this.learnedSegmentTimestampOffset??=c,c})()}listsAllSegments(){return this.segments[0].sequenceNumber===0||this.neverRemovesSegments}async getRawTimestampOffset(e){if((await e.getFormat()).supportsTimestampedMediaData)return 0;let n=(await e.getMetadataTags()).raw?.PRIV;for(let a of Ar(n)){if(!(a instanceof Uint8Array)||a.length!==dr.length+1+8||ie.decode(a.subarray(0,dr.length))!==dr||a[dr.length]!==0)continue;let s=W(a),o=s.getUint32(dr.length+1),c=s.getUint32(dr.length+5);if(o>1)continue;let l=2**32*o+c;return $n(l,Xn(l))/xe-await e.getFirstTimestamp()}return null}getTimestampWrapPeriod(){return Bi/xe}};var Ru=256,Bu=256,cs=class extends le{constructor(e){super(e),this.metadataPromise=null,this.trackBackings=null,this.internalTracks=null,this.segmentedInputs=[],this.hasMasterPlaylist=!0,this.masterPlaylistVariables=null,this.mediaOffsets=new Map}readMetadata(){return this.metadataPromise??=(async()=>{g(this.input._rootSource instanceof We);let e=await this.input._reader.requestEntireFile();g(e);let t=as(e,e.length,{ignore:es}),{rootPath:i}=this.input._rootSource,n=new Lr(i,null),a=[],s=[];for(let u=1;u<t.length;u++){let d=t[u];if(d.startsWith(Hr))n.define(d.slice(Hr.length));else if(d.startsWith(ba)){let f=u,m=t[++u];if(m===void 0)throw new Error("Incorrect M3U8 file; a line must follow the #EXT-X-STREAM-INF tag.");m=n.substitute(m);let p=at(i,m),h=new dt(d.slice(ba.length),n);if(h.getAsNumber("bandwidth")===null)throw new Error("Invalid M3U8 file; #EXT-X-STREAM-INF tag requires a BANDWIDTH attribute with a valid numerical value.");a.push({fullPath:p,attributes:h,lineNumber:f,hasOnlyKeyPackets:!1})}else if(d.startsWith(Ta)){let f=new dt(d.slice(Ta.length),n),m=f.get("uri");if(m===null)throw new Error("Invalid M3U8 file; #EXT-X-I-FRAME-STREAM-INF tag requires a URI attribute.");if(f.getAsNumber("bandwidth")===null)throw new Error("Invalid M3U8 file; #EXT-X-I-FRAME-STREAM-INF tag requires a BANDWIDTH attribute with a valid numerical value.");let h=at(i,m);a.push({fullPath:h,attributes:f,lineNumber:u,hasOnlyKeyPackets:!0})}else if(d.startsWith(Sa)){let f=new dt(d.slice(Sa.length),n);if(f.get("type")===null)throw new Error("Invalid M3U8 file; #EXT-X-MEDIA tag requires a TYPE attribute.");if(f.get("group-id")===null)throw new Error("Invalid M3U8 file; #EXT-X-MEDIA tag requires a GROUP-ID attribute.");let h=null,k=f.get("uri");k!==null&&(h=at(i,k)),s.push({fullPath:h,attributes:f,lineNumber:u})}else if(d!==Ec){if(d.startsWith(Mi)){let f=new zi(this,i,null,t);this.segmentedInputs=[f],this.hasMasterPlaylist=!1,this.trackBackings=await f.getTrackBackings();return}}}if(a.length>Ru||s.length>Bu)throw new Error("Unsupported M3U8 file; too many variant streams or media tags.");this.masterPlaylistVariables=n;let o=await Promise.all(a.map(async(u,d)=>{let f=[],m=u.attributes.get("codecs"),p;if(m)p=m.split(",").map(C=>C.trim());else{let E=await this.getSegmentedInputForPath(u.fullPath).getTrackBackings(),I=await Promise.all(E.map(async R=>({track:R,codec:await R.getCodec()})));p=await Promise.all(I.filter(R=>R.codec!==null).map(R=>R.track.getDecoderConfig().then(D=>D.codec)))}let h=u.attributes.get("video"),k=u.attributes.get("audio"),w=p.some(C=>et.includes(Kt(C))),S=p.some(C=>_t.includes(Kt(C)));if(h!==null&&!w){let C=s.find(E=>{let I=E.attributes.get("group-id"),R=E.attributes.get("type");return I===h&&R.toLowerCase()==="video"});e:if(C){let E=C.attributes.get("uri");if(E===null)break e;let I=at(i,E),O=(await this.getSegmentedInputForPath(I).getTrackBackings()).find(z=>z.getType()==="video");if(!O||await O.getCodec()===null)break e;let V=await O.getDecoderConfig().then(z=>z?.codec??null);g(V!==null),p.push(V)}}if(k!==null&&!S){let C=s.find(E=>{let I=E.attributes.get("group-id"),R=E.attributes.get("type");return I===k&&R.toLowerCase()==="audio"});e:if(C){let E=C.attributes.get("uri");if(E===null)break e;let I=at(i,E),O=(await this.getSegmentedInputForPath(I).getTrackBackings()).find(z=>z.getType()==="audio");if(!O||await O.getCodec()===null)break e;let V=await O.getDecoderConfig().then(z=>z?.codec??null);g(V!==null),p.push(V)}}p=[...new Set(p)];let b=null,T=null,y=u.attributes.getAsNumber("bandwidth");g(y!==null);let A=u.attributes.getAsNumber("average-bandwidth"),x=u.attributes.get("name");for(let C of p){let E=Kt(C);if(E!==null){if(et.includes(E)){if(b!==null)throw new Error("Unsupported M3U8 file; multiple video codecs found in the CODECS attribute of a variant stream.");b=C;let I=u.attributes.get("video");if(I===null){let R=u.attributes.get("resolution"),D=null,O=null;if(R){let V=R.match(/^(\d+)x(\d+)$/);V&&(D=Number(V[1]),O=Number(V[2]))}f.push({id:-1,demuxer:this,backingTrack:null,default:!0,autoselect:!0,languageCode:ne,lineNumber:u.lineNumber,fullPath:u.fullPath,fullCodecString:b,pairingMask:1n<<BigInt(d),peakBitrate:y,averageBitrate:A,name:x,hasOnlyKeyPackets:u.hasOnlyKeyPackets,info:{type:"video",width:D,height:O}})}else for(let R of s){let D=R.attributes.get("group-id"),O=R.attributes.get("type");if(D!==I||O.toLowerCase()!=="video")continue;let V=R.attributes.get("resolution")??u.attributes.get("resolution"),z=null,j=null;if(V){let ee=V.match(/^(\d+)x(\d+)$/);ee&&(z=Number(ee[1]),j=Number(ee[2]))}f.push({id:-1,demuxer:this,backingTrack:null,default:os(R.attributes),autoselect:os(R.attributes)||Fc(R.attributes),languageCode:Mc(R.attributes.get("language")),lineNumber:R.lineNumber,fullPath:R.fullPath??u.fullPath,fullCodecString:b,pairingMask:1n<<BigInt(d),peakBitrate:R.fullPath===null?y:null,averageBitrate:R.fullPath===null?A:null,name:R.attributes.get("name"),hasOnlyKeyPackets:u.hasOnlyKeyPackets,info:{type:"video",width:z,height:j}})}}else if(_t.includes(E)){if(T!==null)throw new Error("Unsupported M3U8 file; multiple audio codecs found in the CODECS attribute of a variant stream.");T=C;let I=u.attributes.get("audio");if(I===null){let R=u.attributes.get("channels"),D=R!==null?Number(R.split("/")[0]):null;f.push({id:-1,demuxer:this,backingTrack:null,default:!0,autoselect:!0,languageCode:ne,lineNumber:u.lineNumber,fullPath:u.fullPath,fullCodecString:T,pairingMask:1n<<BigInt(d),peakBitrate:y,averageBitrate:A,name:x,hasOnlyKeyPackets:u.hasOnlyKeyPackets,info:{type:"audio",numberOfChannels:D!==null&&Number.isInteger(D)&&D>0?D:null}})}else for(let R of s){let D=R.attributes.get("group-id"),O=R.attributes.get("type");if(D!==I||O.toLowerCase()!=="audio")continue;let V=R.attributes.get("channels")??u.attributes.get("channels"),z=V!==null?Number(V.split("/")[0]):null;f.push({id:-1,demuxer:this,backingTrack:null,default:os(R.attributes),autoselect:os(R.attributes)||Fc(R.attributes),languageCode:Mc(R.attributes.get("language")),lineNumber:R.lineNumber,fullPath:R.fullPath??u.fullPath,fullCodecString:T,pairingMask:1n<<BigInt(d),peakBitrate:R.fullPath===null?y:null,averageBitrate:R.fullPath===null?A:null,name:R.attributes.get("name"),hasOnlyKeyPackets:u.hasOnlyKeyPackets,info:{type:"audio",numberOfChannels:z!==null&&Number.isInteger(z)&&z>0?z:null}})}}}}return f})),c=[],l=u=>{let d=c.find(f=>f.fullPath===u.fullPath&&f.info.type===u.info.type);d?(d.pairingMask|=u.pairingMask,d.default||=u.default,d.autoselect||=u.autoselect,d.lineNumber=Math.min(d.lineNumber,u.lineNumber),u.peakBitrate!==null&&(d.peakBitrate=Math.max(d.peakBitrate??-1/0,u.peakBitrate)),u.averageBitrate!==null&&(d.averageBitrate=Math.max(d.averageBitrate??-1/0,u.averageBitrate)),d.languageCode===ne&&(d.languageCode=u.languageCode)):(u.id=c.length+1,c.push(u))};for(let u of o)for(let d of u)l(d);c.sort((u,d)=>u.lineNumber-d.lineNumber),this.trackBackings=[];for(let u of c)u.info.type==="video"?this.trackBackings.push(new us(u)):this.trackBackings.push(new ds(u));this.internalTracks=c})()}async getTrackBackings(){return await this.readMetadata(),g(this.trackBackings),this.trackBackings}getMediaOffsetForDiscontinuity(e){let t=this.mediaOffsets.get(e);return t||(t=(async()=>{let i=this.getReferenceSegmentedInput(),n=await i.getFirstSegment();for(;n&&n.discontinuityNumber<e;)n=await i.getNextSegment(n,{});if(!n||n.discontinuityNumber!==e)throw new Error(`The reference playlist contains no segment in discontinuity ${e}, so the discontinuity can't be synchronized across tracks. If you think this is a bug, please raise an issue and include the playlist.`);let a=i.getInputForSegment(n),s=await i.getRawTimestampOffset(a)??0,o=await a.getTracks(),c=o.find(l=>l.type==="video")??o[0];if(!c)throw new Error("The reference playlist's segment contains no tracks.");return n.timestamp-(s+await c.getFirstTimestamp())})(),this.mediaOffsets.set(e,t),t)}getReferenceSegmentedInput(){if(!this.hasMasterPlaylist)return this.segmentedInputs[0];g(this.internalTracks);let e=this.internalTracks.filter(a=>!a.hasOnlyKeyPackets),t=e.filter(a=>a.info.type==="video"),i=t.length>0?t:e,n=Sr(i,a=>a.peakBitrate??1/0);return g(n!==-1),this.getSegmentedInputForPath(i[n].fullPath)}getSegmentedInputForPath(e){let t=this.segmentedInputs.find(n=>n.path===e);if(t)return t;let i=null;return this.internalTracks&&(i=this.internalTracks.filter(a=>a.fullPath===e).map(a=>({id:a.id,type:a.info.type}))),t=new zi(this,e,i,null),this.segmentedInputs.push(t),t}async getMetadataTags(){return{}}async getMimeType(){return Jn}dispose(){if(this.segmentedInputs){for(let e of this.segmentedInputs)e.dispose();this.segmentedInputs.length=0}}},ls=class{constructor(e){this.internalTrack=e,this.hydrationPromise=null}hydrate(){return this.hydrationPromise??=(async()=>{let e=this.internalTrack.demuxer.getSegmentedInputForPath(this.internalTrack.fullPath),t=null,n=(await e.getTrackBackings()).filter(a=>a.getType()===this.getType());if(n.length===1)t=n[0];else if(this instanceof us){for(let a of n)if(await a.getCodec()===this.getCodec()){t=a;break}}else{g(this instanceof ds);for(let a of n)if(await a.getCodec()===this.getCodec()){t=a;break}}if(!t)throw new Error("Could not find matching track in underlying media data.");this.internalTrack.backingTrack=t})()}delegate(e){return this.internalTrack.backingTrack?e():this.hydrate().then(e)}getCodec(){throw new Error("Not implemented on base class.")}getDisposition(){return{...fe,default:this.internalTrack.autoselect,primary:this.internalTrack.default}}getId(){return this.internalTrack.id}getPairingMask(){return this.internalTrack.pairingMask}getInternalCodecId(){return null}getLanguageCode(){return this.internalTrack.languageCode}getName(){return this.internalTrack.name}getNumber(){g(this.internalTrack.demuxer.internalTracks);let e=this.internalTrack.info.type,t=0;for(let i of this.internalTrack.demuxer.internalTracks)if(i.info.type===e&&t++,i===this.internalTrack)break;return t}getTimeResolution(){return this.delegate(()=>this.internalTrack.backingTrack.getTimeResolution())}isRelativeToUnixEpoch(){return this.delegate(()=>this.internalTrack.backingTrack.isRelativeToUnixEpoch())}getUnixTimeForTimestamp(e){return this.delegate(()=>this.internalTrack.backingTrack.getUnixTimeForTimestamp(e))}getBitrate(){return this.internalTrack.peakBitrate}getAverageBitrate(){return this.internalTrack.averageBitrate}async getDurationFromMetadata(e){return await this.hydrate(),this.internalTrack.backingTrack.getDurationFromMetadata(e)}async getLiveRefreshInterval(){return await this.hydrate(),this.internalTrack.backingTrack.getLiveRefreshInterval()}getHasOnlyKeyPackets(){return this.internalTrack.hasOnlyKeyPackets||null}async getFirstPacket(e){return await this.hydrate(),this.internalTrack.backingTrack.getFirstPacket(e)}async getPacket(e,t){return await this.hydrate(),this.internalTrack.backingTrack.getPacket(e,t)}async getKeyPacket(e,t){return await this.hydrate(),this.internalTrack.backingTrack.getKeyPacket(e,t)}async getNextPacket(e,t){return await this.hydrate(),this.internalTrack.backingTrack.getNextPacket(e,t)}async getNextKeyPacket(e,t){return await this.hydrate(),this.internalTrack.backingTrack.getNextKeyPacket(e,t)}},us=class extends ls{constructor(e){super(e)}get backingVideoTrack(){return this.internalTrack.backingTrack}getType(){return"video"}getCodec(){return Kt(this.internalTrack.fullCodecString)}getCodedWidth(){return this.delegate(()=>this.backingVideoTrack.getCodedWidth())}getCodedHeight(){return this.delegate(()=>this.backingVideoTrack.getCodedHeight())}getSquarePixelWidth(){return this.delegate(()=>this.backingVideoTrack.getSquarePixelWidth())}getSquarePixelHeight(){return this.delegate(()=>this.backingVideoTrack.getSquarePixelHeight())}getMetadataDisplayWidth(){return this.backingVideoTrack?null:this.internalTrack.info.width}getMetadataDisplayHeight(){return this.backingVideoTrack?null:this.internalTrack.info.height}getTransformationMatrix(){return this.delegate(()=>this.backingVideoTrack.getTransformationMatrix())}async getColorSpace(){return await this.hydrate(),this.backingVideoTrack.getColorSpace()}async canBeTransparent(){return await this.hydrate(),this.backingVideoTrack.canBeTransparent()}getMetadataCodecParameterString(){return this.backingVideoTrack?null:this.internalTrack.fullCodecString}async getDecoderConfig(){if(await this.hydrate(),await this.backingVideoTrack.getCodec()!==this.getCodec())throw new Error("The codec in the playlist doesn't match the codec of the media data.");return this.backingVideoTrack.getDecoderConfig()}},ds=class extends ls{constructor(e){super(e)}get backingAudioTrack(){return this.internalTrack.backingTrack}getType(){return"audio"}getCodec(){return Kt(this.internalTrack.fullCodecString)}getNumberOfChannels(){return this.internalTrack.info.numberOfChannels!==null?this.internalTrack.info.numberOfChannels:this.delegate(()=>this.backingAudioTrack.getNumberOfChannels())}getSampleRate(){return this.delegate(()=>this.backingAudioTrack.getSampleRate())}getMetadataCodecParameterString(){return this.backingAudioTrack?null:this.internalTrack.fullCodecString}async getDecoderConfig(){if(await this.hydrate(),await this.backingAudioTrack.getCodec()!==this.getCodec())throw new Error("The codec in the playlist doesn't match the codec of the media data.");return this.backingAudioTrack.getDecoderConfig()}},os=r=>{let e=r.get("default");if(e===null)return!1;let t=e.toUpperCase();if(t==="YES")return!0;if(t==="NO")return!1;throw new Error(`Invalid M3U8 file; #EXT-X-MEDIA DEFAULT attribute must be YES or NO, got "${e}".`)},Fc=r=>{let e=r.get("autoselect");if(e===null)return!1;let t=e.toUpperCase();if(t==="YES")return!0;if(t==="NO")return!1;throw new Error(`Invalid M3U8 file; #EXT-X-MEDIA AUTOSELECT attribute must be YES or NO, got "${e}".`)},Mc=r=>{if(r===null)return ne;let e=r.split("-")[0];return e||ne};var Re=class{constructor(){this._isIsobmff=!1}},Ni=class extends Re{constructor(){super(...arguments),this._isIsobmff=!0}async _getMajorBrand(e){let t=e._reader.requestSlice(0,12);if(P(t)&&(t=await t),!t)return null;t.skip(4);let i=J(t,4);return i!=="ftyp"&&i!=="styp"?null:J(t,4)}_createDemuxer(e){return new Bn(e)}get supportsTimestampedMediaData(){return!0}},fs=class extends Ni{async _canReadInput(e){let t=await this._getMajorBrand(e);if(t!==null)return t!=="qt  ";let i=0;for(let n=0;n<10;n++){let a=e._reader.requestSlice(i,8);if(P(a)&&(a=await a),!a)return!1;let s=B(a),o=8;if(s===1){let l=e._reader.requestSlice(i+8,8);if(P(l)&&(l=await l),!l)return!1;s=ge(l),o=16}if(s<o)return!1;let c=J(a,4);if(c==="moof"||c==="sidx")return!0;if(c==="emsg"||c==="prft"||c==="free")i+=s;else return!1}return!1}get name(){return"MP4"}get mimeType(){return"video/mp4"}},hs=class extends Ni{async _canReadInput(e){return await this._getMajorBrand(e)==="qt  "}get name(){return"QuickTime File Format"}get mimeType(){return"video/quicktime"}},Vi=class extends Re{async isSupportedEBMLOfDocType(e,t){let i=e._reader.requestSlice(0,Le);if(P(i)&&(i=await i),!i)return!1;let n=ta(i);if(n===null||n<1||n>8||K(i,n)!==_.EBML)return!1;let s=ia(i);if(typeof s!="number")return!1;let o=e._reader.requestSlice(i.filePos,s);if(P(o)&&(o=await o),!o)return!1;let c=i.filePos;for(;o.filePos<=c+s-Te;){let l=He(o);if(!l)break;let{id:u,size:d}=l,f=o.filePos;if(d===void 0||f+d>c+s||d>8&&u!==_.DocType)return!1;switch(u){case _.EBMLVersion:if(K(o,d)!==1)return!1;break;case _.EBMLReadVersion:if(K(o,d)!==1)return!1;break;case _.DocType:if(Lt(o,d)!==t)return!1;break;case _.DocTypeVersion:if(K(o,d)>4)return!1;break}o.filePos=f+d}return!0}_canReadInput(e){return this.isSupportedEBMLOfDocType(e,"matroska")}_createDemuxer(e){return new Ln(e)}get name(){return"Matroska"}get mimeType(){return"video/x-matroska"}get supportsTimestampedMediaData(){return!0}},ms=class extends Vi{_canReadInput(e){return this.isSupportedEBMLOfDocType(e,"webm")}get name(){return"WebM"}get mimeType(){return"video/webm"}},ps=class extends Re{async _canReadInput(e){let t=0;for(;;){let d=e._reader.requestSlice(t,me);if(P(d)&&(d=await d),!d)break;let f=Ie(d);if(!f)break;t=d.filePos+f.size}let i=await Ri(e._reader,t,t+4096);if(!i)return!1;let n=i.header,a=sn(n.mpegVersionId,n.channel),s=e._reader.requestSlice(i.startPos+a,4);if(P(s)&&(s=await s),!s)return!1;let o=B(s);if(o===pi||o===nn)return!0;t=i.startPos+i.header.totalSize;let l=await Ri(e._reader,t,t+4);if(!l)return!1;let u=l.header;return!(n.channel!==u.channel||n.sampleRate!==u.sampleRate)}_createDemuxer(e){return new Wn(e)}get name(){return"MP3"}get mimeType(){return"audio/mpeg"}get supportsTimestampedMediaData(){return!1}},gs=class extends Re{async _canReadInput(e){let t=e._reader.requestSlice(0,12);if(P(t)&&(t=await t),!t)return!1;let i=J(t,4);return i!=="RIFF"&&i!=="RIFX"&&i!=="RF64"?!1:(t.skip(4),J(t,4)==="WAVE")}_createDemuxer(e){return new Kn(e)}get name(){return"WAVE"}get mimeType(){return"audio/wav"}get supportsTimestampedMediaData(){return!1}},ks=class extends Re{async _canReadInput(e){let t=e._reader.requestSlice(0,4);return P(t)&&(t=await t),t?J(t,4)==="OggS":!1}_createDemuxer(e){return new qn(e)}get name(){return"Ogg"}get mimeType(){return"application/ogg"}get supportsTimestampedMediaData(){return!0}},ys=class extends Re{async _canReadInput(e){let t=0;for(;;){let n=e._reader.requestSlice(t,me);if(P(n)&&(n=await n),!n)break;let a=Ie(n);if(!a)break;t=n.filePos+a.size}let i=e._reader.requestSlice(t,4);return P(i)&&(i=await i),i?J(i,4)==="fLaC":!1}get name(){return"FLAC"}get mimeType(){return"audio/flac"}get supportsTimestampedMediaData(){return!1}_createDemuxer(e){return new Qn(e)}},ws=class extends Re{async _canReadInput(e){let t=0;for(;;){let s=e._reader.requestSlice(t,me);if(P(s)&&(s=await s),!s)break;let o=Ie(s);if(!o)break;t=s.filePos+o.size}let i=e._reader.requestSliceRange(t,Et,Ze);if(P(i)&&(i=await i),!i)return!1;let n=Je(i);if(!n||(t+=n.frameLength,i=e._reader.requestSliceRange(t,Et,Ze),P(i)&&(i=await i),!i))return!1;let a=Je(i);return a?n.objectType===a.objectType&&n.samplingFrequencyIndex===a.samplingFrequencyIndex&&n.channelConfiguration===a.channelConfiguration:!1}_createDemuxer(e){return new Gn(e)}get name(){return"ADTS"}get mimeType(){return"audio/aac"}get supportsTimestampedMediaData(){return!1}},bs=class extends Re{async _canReadInput(e){let t=Ce+16+1,i=e._reader.requestSlice(0,t);if(P(i)&&(i=await i),!i)return!1;let n=M(i,t);return n[0]===71&&n[Ce]===71||n[0]===71&&n[Ce+16]===71?!0:n[4]===71&&n[4+Ce+4]===71}_createDemuxer(e){return new Yn(e)}get name(){return"MPEG Transport Stream"}get mimeType(){return"video/MP2T"}get supportsTimestampedMediaData(){return!0}},Wr=class extends Re{async _canReadInput(e){let t=e._reader.requestSlice(0,7);if(P(t)&&(t=await t),!t||!(J(t,7)==="#EXTM3U"))return!1;if(!(e._rootSource instanceof We))throw new TypeError("HLS inputs require `InputOptions.source` to be a PathedSource or a ref to one.");return e._rootSource._usedForHls=!0,!0}_createDemuxer(e){return new cs(e)}get name(){return"HTTP Live Streaming (HLS)"}get mimeType(){return Jn}get supportsTimestampedMediaData(){return!0}},Dc=new fs,Oc=new hs,Uc=new Vi,zc=new ms,Nc=new ps,Vc=new gs,Lc=new ks,Hc=new ws,Wc=new ys,qc=new bs,Kc=new Wr,Da=[Kc,Dc,Oc,Uc,zc,Vc,Lc,Wc,Nc,Hc,qc];var jc=(r,e)=>{if(!r||typeof r!="object")throw new TypeError(`${e}, when provided, must be an object.`);if(r.isobmff!==void 0){if(!r.isobmff||typeof r.isobmff!="object")throw new TypeError(`${e}.isobmff, when provided, must be an object.`);if(r.isobmff.resolveKeyId!==void 0&&typeof r.isobmff.resolveKeyId!="function")throw new TypeError(`${e}.isobmff.resolveKeyId, when provided, must be a function.`)}if(r.hls!==void 0){if(!r.hls||typeof r.hls!="object")throw new TypeError(`${e}.hls, when provided, must be an object.`);if(r.hls.offsetTimestampsByDateTime!==void 0&&typeof r.hls.offsetTimestampsByDateTime!="boolean")throw new TypeError(`${e}.hls.offsetTimestampsByDateTime, when provided, must be a boolean.`)}};var mr=r=>{if(!r||typeof r!="object")throw new TypeError("options must be an object.");if(r.metadataOnly!==void 0&&typeof r.metadataOnly!="boolean")throw new TypeError("options.metadataOnly, when defined, must be a boolean.");if(r.verifyKeyPackets!==void 0&&typeof r.verifyKeyPackets!="boolean")throw new TypeError("options.verifyKeyPackets, when defined, must be a boolean.");if(r.verifyKeyPackets&&r.metadataOnly)throw new TypeError("options.verifyKeyPackets and options.metadataOnly cannot be enabled together.");if(r.skipLiveWait!==void 0&&typeof r.skipLiveWait!="boolean")throw new TypeError("options.skipLiveWait, when defined, must be a boolean.")},Gc=r=>{if(!Mt(r))throw new TypeError("timestamp must be a number.")},Oa=(r,e,t)=>t.verifyKeyPackets?e.then(async i=>{if(!i||i.type==="delta")return i;let n=await r.determinePacketType(i);return n&&(i.type=n),i}):e,jt=class{constructor(e){if(!(e instanceof qr))throw new TypeError("track must be an InputTrack.");this._track=e}async getFirstPacket(e={}){if(mr(e),this._track.input._disposed)throw new ue;return Oa(this._track,this._track._backing.getFirstPacket(e),e)}async getFirstKeyPacket(e={}){mr(e);let t=await this.getFirstPacket(e);return t?t.type==="key"?t:this.getNextKeyPacket(t,e):null}async getPacket(e,t={}){if(Gc(e),mr(t),this._track.input._disposed)throw new ue;return Oa(this._track,this._track._backing.getPacket(e,t),t)}async getNextPacket(e,t={}){if(!(e instanceof Y))throw new TypeError("packet must be an EncodedPacket.");if(mr(t),this._track.input._disposed)throw new ue;return Oa(this._track,this._track._backing.getNextPacket(e,t),t)}async getKeyPacket(e,t={}){if(Gc(e),mr(t),this._track.input._disposed)throw new ue;if(!t.verifyKeyPackets)return this._track._backing.getKeyPacket(e,t);let i=await this._track._backing.getKeyPacket(e,t);for(;i;){if(g(i.type==="key"),await this._track.determinePacketType(i)!=="delta")return i;let a=1/await this._track.getTimeResolution(),s;for(;s=await this._track._backing.getKeyPacket(i.timestamp-a,t),!(!s||s.timestamp<i.timestamp);)a*=2;i=s}return null}async getNextKeyPacket(e,t={}){if(!(e instanceof Y))throw new TypeError("packet must be an EncodedPacket.");if(mr(t),this._track.input._disposed)throw new ue;if(!t.verifyKeyPackets)return this._track._backing.getNextKeyPacket(e,t);let i=await this._track._backing.getNextKeyPacket(e,t);for(;i;){if(g(i.type==="key"),await this._track.determinePacketType(i)!=="delta")return i;i=await this._track._backing.getNextKeyPacket(i,t)}return null}packets(e,t,i={}){if(e!==void 0&&!(e instanceof Y))throw new TypeError("startPacket must be an EncodedPacket.");if(e!==void 0&&e.isMetadataOnly&&!i?.metadataOnly)throw new TypeError("startPacket can only be metadata-only if options.metadataOnly is enabled.");if(t!==void 0&&!(t instanceof Y))throw new TypeError("endPacket must be an EncodedPacket.");if(mr(i),this._track.input._disposed)throw new ue;let n=[],{promise:a,resolve:s}=gt(),{promise:o,resolve:c}=gt(),l=!1,u=!1,d=null,f=!1,m=[],p=()=>Math.max(2,m.length);(async()=>{let k=e??await this.getFirstPacket(i);for(;k&&!u&&!this._track.input._disposed&&!(t&&k.sequenceNumber>=t?.sequenceNumber);){if(n.length>p()){({promise:o,resolve:c}=gt()),await o;continue}n.push(k),s(),{promise:a,resolve:s}=gt(),k=await this.getNextPacket(k,i)}l=!0,s()})().catch(k=>{f||(d=k,f=!0,s())});let h=this._track;return{async next(){for(;;){if(h.input._disposed)throw new ue;if(u)return{value:void 0,done:!0};if(f)throw d;if(n.length>0){let k=n.shift(),w=performance.now();for(m.push(w);m.length>0&&w-m[0]>=1e3;)m.shift();return c(),{value:k,done:!1}}else{if(l)return{value:void 0,done:!0};await a}}},async return(){return u=!0,c(),s(),{value:void 0,done:!0}},async throw(k){throw k},[Symbol.asyncIterator](){return this}}}};var qr=class r{constructor(e,t){this.input=e,this._backing=t}isVideoTrack(){return this instanceof Kr}isAudioTrack(){return this instanceof jr}get id(){return this._backing.getId()}get number(){return this._backing.getNumber()}async getInternalCodecId(){return this._backing.getInternalCodecId()}get internalCodecId(){return ae(this._backing.getInternalCodecId(),"internalCodecId","getInternalCodecId")}async getLanguageCode(){return this._backing.getLanguageCode()}get languageCode(){return ae(this._backing.getLanguageCode(),"languageCode","getLanguageCode")}async getName(){return this._backing.getName()}get name(){return ae(this._backing.getName(),"name","getName")}async getTimeResolution(){return this._backing.getTimeResolution()}get timeResolution(){return ae(this._backing.getTimeResolution(),"timeResolution","getTimeResolution")}async isRelativeToUnixEpoch(){return this._backing.isRelativeToUnixEpoch()}async getUnixTimeForTimestamp(e){return this._backing.getUnixTimeForTimestamp(e)}async hasUnixTimeMapping(){return await this._backing.getUnixTimeForTimestamp(await this.getFirstTimestamp())!==null}async getDisposition(){return this._backing.getDisposition()}get disposition(){return ae(this._backing.getDisposition(),"disposition","getDisposition")}async getBitrate(){return this._backing.getBitrate()}async getAverageBitrate(){return this._backing.getAverageBitrate()}async getFirstTimestamp(){return(await this._backing.getFirstPacket({metadataOnly:!0}))?.timestamp??0}async computeDuration(e){let t=await this._backing.getPacket(1/0,{metadataOnly:!0,...e}),i=(t?.timestamp??0)+(t?.duration??0);return Ji(i,await this.getTimeResolution())}async getDurationFromMetadata(e={}){return this._backing.getDurationFromMetadata(e)}async computePacketStats(e=1/0,t){let i=new jt(this),n=1/0,a=-1/0,s=0,o=0;for await(let c of i.packets(void 0,void 0,{metadataOnly:!0,...t})){if(s>=e&&c.timestamp>=a)break;n=Math.min(n,c.timestamp),a=Math.max(a,c.timestamp+c.duration),s++,o+=c.byteLength}return{packetCount:s,averagePacketRate:s?Number((s/(a-n)).toPrecision(16)):0,averageBitrate:s?Number((8*o/(a-n)).toPrecision(16)):0}}async isLive(){return await this._backing.getLiveRefreshInterval()!==null}async getLiveRefreshInterval(){return this._backing.getLiveRefreshInterval()}canBePairedWith(e){if(!(e instanceof r))throw new TypeError("other must be an InputTrack.");return this.input!==e.input||this===e?!1:(this._backing.getPairingMask()&e._backing.getPairingMask())!==0n}async getPairableTracks(e){return this.input.getTracks(Gt({filter:t=>t.canBePairedWith(this)},e))}async getPairableVideoTracks(e){return this.input.getVideoTracks(Gt({filter:t=>t.canBePairedWith(this)},e))}async getPairableAudioTracks(e){return this.input.getAudioTracks(Gt({filter:t=>t.canBePairedWith(this)},e))}async getPrimaryPairableVideoTrack(e){return this.input.getPrimaryVideoTrack(Gt({filter:t=>t.canBePairedWith(this)},e))}async getPrimaryPairableAudioTrack(e){return this.input.getPrimaryAudioTrack(Gt({filter:t=>t.canBePairedWith(this)},e))}async hasPairableTrack(e){e&&=Ua(e);let t=await this.input.getTracks();for(let i of t)if(this.canBePairedWith(i)&&(!e||await e(i)))return!0;return!1}hasPairableVideoTrack(e){return e&&=Ua(e),this.hasPairableTrack(async t=>t.isVideoTrack()&&(!e||await e(t)))}hasPairableAudioTrack(e){return e&&=Ua(e),this.hasPairableTrack(async t=>t.isAudioTrack()&&(!e||await e(t)))}},ae=(r,e,t)=>{if(P(r))throw new Error(`'${e}' is deprecated and not available synchronously for this track. Use the preferred '${t}()' instead.`);return r},Ua=r=>{if(r!==void 0&&typeof r!="function")throw new TypeError("predicate, when provided, must be a function.");return r?e=>{let t=n=>{if(typeof n!="boolean")throw new TypeError("predicate must return or resolve to a boolean value.");return n},i=r(e);return P(i)?i.then(t):t(i)}:void 0},Kr=class extends qr{constructor(e,t){super(e,t),this._pixelAspectRatioCache=null}get type(){return"video"}async getCodec(){return this._backing.getCodec()}get codec(){return ae(this._backing.getCodec(),"codec","getCodec")}async hasOnlyKeyPackets(){return await this._backing.getHasOnlyKeyPackets?.()??await this._backing.getCodec()==="prores"}async getCodedWidth(){return this._backing.getCodedWidth()}get codedWidth(){return ae(this._backing.getCodedWidth(),"codedWidth","getCodedWidth")}async getCodedHeight(){return this._backing.getCodedHeight()}get codedHeight(){return ae(this._backing.getCodedHeight(),"codedHeight","getCodedHeight")}async getTransformationMatrix(){return this._backing.getTransformationMatrix()}async getRotation(){return oi(await this._backing.getTransformationMatrix())}get rotation(){return oi(ae(this._backing.getTransformationMatrix(),"rotation","getRotation"))}async getFlip(){return Ms(await this._backing.getTransformationMatrix())}async getSquarePixelWidth(){return this._backing.getSquarePixelWidth()}get squarePixelWidth(){return ae(this._backing.getSquarePixelWidth(),"squarePixelWidth","getSquarePixelWidth")}async getSquarePixelHeight(){return this._backing.getSquarePixelHeight()}get squarePixelHeight(){return ae(this._backing.getSquarePixelHeight(),"squarePixelHeight","getSquarePixelHeight")}async getPixelAspectRatio(){return this._pixelAspectRatioCache??=Qc(await this.getSquarePixelWidth()*await this.getCodedHeight(),await this.getSquarePixelHeight()*await this.getCodedWidth())}get pixelAspectRatio(){return this._pixelAspectRatioCache??=Qc(ae(this._backing.getSquarePixelWidth(),"pixelAspectRatio","getPixelAspectRatio")*ae(this._backing.getCodedHeight(),"pixelAspectRatio","getPixelAspectRatio"),ae(this._backing.getSquarePixelHeight(),"pixelAspectRatio","getPixelAspectRatio")*ae(this._backing.getCodedWidth(),"pixelAspectRatio","getPixelAspectRatio"))}async getDisplayWidth(){let e=await this._backing.getMetadataDisplayWidth?.();return e??(await this.getRotation()%180===0?this.getSquarePixelWidth():this.getSquarePixelHeight())}get displayWidth(){let e=this._backing.getMetadataDisplayWidth?.();if(e!==void 0){let n=ae(e,"displayWidth","getDisplayWidth");if(n!==null)return n}let i=oi(ae(this._backing.getTransformationMatrix(),"displayWidth","getDisplayWidth"))%180===0?this._backing.getSquarePixelWidth():this._backing.getSquarePixelHeight();return ae(i,"displayWidth","getDisplayWidth")}async getDisplayHeight(){let e=await this._backing.getMetadataDisplayHeight?.();return e??(await this.getRotation()%180===0?this.getSquarePixelHeight():this.getSquarePixelWidth())}get displayHeight(){let e=this._backing.getMetadataDisplayHeight?.();if(e!==void 0){let n=ae(e,"displayHeight","getDisplayHeight");if(n!==null)return n}let i=oi(ae(this._backing.getTransformationMatrix(),"displayHeight","getDisplayHeight"))%180===0?this._backing.getSquarePixelHeight():this._backing.getSquarePixelWidth();return ae(i,"displayHeight","getDisplayHeight")}async getColorSpace(){return this._backing.getColorSpace()}async hasHighDynamicRange(){let e=await this._backing.getColorSpace();return e.primaries==="bt2020"||e.primaries==="smpte432"||e.transfer==="pq"||e.transfer==="hlg"||e.matrix==="bt2020-ncl"}async canBeTransparent(){return this._backing.canBeTransparent()}async getDecoderConfig(){return this._backing.getDecoderConfig()}async getCodecParameterString(){let e=await this._backing.getMetadataCodecParameterString?.();return e??(await this._backing.getDecoderConfig())?.codec??null}async canDecode(){try{let e=await this._backing.getDecoderConfig();if(!e)return!1;let t=await this._backing.getCodec();return g(t!==null),Do.some(n=>n.supports(t,e))?!0:typeof VideoDecoder>"u"?!1:(await VideoDecoder.isConfigSupported(e)).supported===!0}catch(e){return H._error("Error during decodability check:",e),!1}}async determinePacketType(e){if(!(e instanceof Y))throw new TypeError("packet must be an EncodedPacket.");if(e.isMetadataOnly)throw new TypeError("packet must not be metadata-only to determine its type.");let t=await this.getCodec();if(t===null)return null;let i=await this.getDecoderConfig();return g(i),yn(t,i,e.data)}async computeFrameRateMetrics(e={}){if(!e||typeof e!="object")throw new TypeError("options must be an object.");if(e.targetPacketCount!==void 0&&(!Mt(e.targetPacketCount)||e.targetPacketCount<0))throw new TypeError("options.targetPacketCount must be a non-negative number.");let t=await this.getTimeResolution(),i=e.targetPacketCount??256,n=new jt(this),a=[],s=-1/0,o=0;for await(let I of n.packets(void 0,void 0,{metadataOnly:!0})){if(a.length>=i&&I.timestamp>=s)break;a.push(I.timestamp),s=Math.max(s,I.timestamp),o++}let c=new Float64Array(a.length);for(let I=0;I<a.length;I++)c[I]=Math.round(a[I]*t);c.sort();let l=1;for(let I=1;I<c.length;I++)c[I]!==c[l-1]&&(c[l++]=c[I]);if(l<2)return{underlyingFrameRate:null,bestGuessFrameRate:t,minFrameRate:t,maxFrameRate:t,averageFrameRate:t,medianFrameRate:t,frameRateIsConstant:!0,probedPacketCount:o};let u=c.subarray(0,l),d=Fu(u,t),f=d??t,m=d!==null?t/d:null,p=new Map,h=1/0,k=-1/0,w=0;for(let I=1;I<l;I++){let R=u[I]-u[I-1],D=m!==null?Math.max(1,Math.round(R/m)):R;p.set(D,(p.get(D)??0)+1),h=Math.min(h,D),k=Math.max(k,D),w+=D}let S=l-1,b=[...p.keys()].sort((I,R)=>I-R),T=S-1>>1,y=S>>1,A=0,x=0,C=0;for(let I of b)if(C+=p.get(I),A===0&&C>T&&(A=I),C>y){x=I;break}let E=(f/A+f/x)/2;return{underlyingFrameRate:d,bestGuessFrameRate:d!==null?d:Mu(E),minFrameRate:f/k,maxFrameRate:f/h,averageFrameRate:f*S/w,medianFrameRate:E,frameRateIsConstant:d!==null&&h===1&&k===1,probedPacketCount:o}}},Qc=(r,e)=>r===0||e===0?{num:1,den:1}:fi({num:r,den:e}),jr=class extends qr{constructor(e,t){super(e,t)}get type(){return"audio"}async getCodec(){return this._backing.getCodec()}get codec(){return ae(this._backing.getCodec(),"codec","getCodec")}async hasOnlyKeyPackets(){let e=await this._backing.getCodec();return await this._backing.getHasOnlyKeyPackets?.()??(e===null||!Ii.includes(e))}async getNumberOfChannels(){return this._backing.getNumberOfChannels()}get numberOfChannels(){return ae(this._backing.getNumberOfChannels(),"numberOfChannels","getNumberOfChannels")}async getSampleRate(){return this._backing.getSampleRate()}get sampleRate(){return ae(this._backing.getSampleRate(),"sampleRate","getSampleRate")}async getDecoderConfig(){return this._backing.getDecoderConfig()}async getCodecParameterString(){let e=await this._backing.getMetadataCodecParameterString?.();return e??(await this._backing.getDecoderConfig())?.codec??null}async getPreRollDuration(){let e=await this._backing.getCodec();if(e===null)return null;let t=await this._backing.getDecoderConfig();return g(t),$c(e,t)}async canDecode(){try{let e=await this._backing.getDecoderConfig();if(!e)return!1;let t=await this._backing.getCodec();return g(t!==null),Oo.some(i=>i.supports(t,e))||be.includes(e.codec)?!0:typeof AudioDecoder>"u"?!1:(await AudioDecoder.isConfigSupported(e)).supported===!0}catch(e){return H._error("Error during decodability check:",e),!1}}async determinePacketType(e){if(!(e instanceof Y))throw new TypeError("packet must be an EncodedPacket.");if(e.isMetadataOnly)throw new TypeError("packet must not be metadata-only to determine its type.");let t=await this.getCodec();return t===null?null:wn(t,e.data)}};var za=r=>-(r??-1/0),Gr=r=>-r,Qr=r=>{if(typeof r!="object"||!r)throw new TypeError("query must be an object.");if(r.filter!==void 0&&typeof r.filter!="function")throw new TypeError("query.filter, when provided, must be a function.");if(r.sortBy!==void 0&&typeof r.sortBy!="function")throw new TypeError("query.sortBy, when provided, must be a function.");return{filter:r.filter?e=>{let t=n=>{if(typeof n!="boolean")throw new TypeError("query.filter must return or resolve to a boolean.");return n},i=r.filter(e);return P(i)?i.then(t):t(i)}:void 0,sortBy:r.sortBy?e=>{let t=n=>{if(typeof n!="number"&&(!Array.isArray(n)||!n.every(a=>typeof a=="number")))throw new TypeError("query.sortBy must return or resolve to a number or an array of numbers.");return n},i=r.sortBy(e);return P(i)?i.then(t):t(i)}:void 0}},Gt=(r,e)=>({filter:r?.filter||e?.filter?t=>{let i=r?.filter?.(t)??!0,n=a=>a===!1?!1:e?.filter?.(t)??!0;return P(i)?i.then(n):n(i)}:void 0,sortBy:r?.sortBy||e?.sortBy?t=>{let i=r?.sortBy?.(t)??[],n=e?.sortBy?.(t)??[],a=(s,o)=>[...Array.isArray(s)?s:[s],...Array.isArray(o)?o:[o]];return P(i)||P(n)?Promise.all([i,n]).then(([s,o])=>a(s,o)):a(i,n)}:void 0}),Ts=async(r,e)=>{let t=r;if(e?.filter){let s=r.map(c=>e.filter(c));if(s.some(c=>P(c))){let c=await Promise.all(s);t=r.filter((l,u)=>c[u])}else t=r.filter((c,l)=>s[l])}if(!e?.sortBy)return t;let i=t.map(s=>e.sortBy(s)),a=i.some(s=>P(s))?await Promise.all(i):i;return t.map((s,o)=>({track:s,sortValue:a[o]})).sort((s,o)=>{let c=Array.isArray(s.sortValue)?s.sortValue:[s.sortValue],l=Array.isArray(o.sortValue)?o.sortValue:[o.sortValue],u=Math.max(c.length,l.length);for(let d=0;d<u;d++){let f=c[d]??0,m=l[d]??0;if(f!==m)return f-m}return 0}).map(s=>s.track)},Fu=(r,e)=>{let n=1.000000001,a=1e3,s=[12,15,20,24e3/1001,24,25,3e4/1001,30,48,50,6e4/1001,60,100,12e4/1001,120,144,240];if(r.length<2)return null;let o=new Float64Array(r.length-1);for(let x=1;x<r.length;x++){let C=r[x]-r[x-1];if(!(C>0))return null;o[x-1]=C}let c=o.slice();c.sort();let l=c[Math.floor(c.length*.05)];for(let x=0;x<6;x++){let C=0,E=0;for(let R of o){let D=Math.max(1,Math.round(R/l));Math.abs(R-D*l)>=n||(C+=R,E+=D)}if(E===0)return null;let I=C/E;if(Math.abs(I-l)<=1e-12*Math.max(1,l)){l=I;break}l=I}let u=0,d=0,f=0;for(let x of o){let C=Math.max(1,Math.round(x/l));Math.abs(x-C*l)>=n||(u++,d+=x,f+=C)}if(u/o.length<.98)return null;l=d/f;let m=1/Math.min(f,a),p=Math.max(Number.EPSILON,l-m),h=l+m,k=e/h,w=e/p,S=e/l,b=null,T=1/0;for(let x of s){if(x<k||x>w)continue;let C=Math.abs(x/S-1);C<T&&(b=x,T=C)}if(b===null){let x=Xc(p,h,1e6),C=Xc(k,w,1e6);if(C&&(!x||C.den<x.den||C.den===x.den&&C.num<=x.num))b=C.num/C.den;else if(x)b=e*x.den/x.num;else return null}let y=e/b,A=0;for(let x of o){let C=Math.max(1,Math.round(x/y));Math.abs(x-C*y)<n&&A++}return A/o.length<.98?null:b},Xc=(r,e,t)=>{for(let i=1;i<=t;i++){let n=Math.floor(r*i)+1;if(n/i<e)return fi({num:n,den:i})}return null},Mu=r=>{let e=[23.976023976023978,29.970029970029973,59.940059940059946,119.88011988011989],t=[12,15,20,24,25,30,48,50,60,100,120,144,240],i=5e-4,n=.025;for(let o of e)if(Math.abs(o/r-1)<=i)return o;let a=r,s=1/0;for(let o of t){let c=Math.abs(o/r-1);c<=n&&c<s&&(a=o,s=c)}return a};rn();var Du=1,Bc=2,hr=class r extends Ne{get disposed(){return this._disposed}constructor(e){if(super(),this._demuxerPromise=null,this._format=null,this._trackBackingsCache=null,this._backingToTrack=new Map,this._disposed=!1,this._nextSourceCacheAge=0,this._sourceRefs=[],this._sourceCache=[],this._sourceCachePromises=[],this._onFormatDetermined=null,!e||typeof e!="object")throw new TypeError("options must be an object.");if(!Array.isArray(e.formats)||e.formats.some(t=>!(t instanceof Re)))throw new TypeError("options.formats must be an array of InputFormat.");if(!(e.source instanceof ve||e.source instanceof fr))throw new TypeError("options.source must be a Source or SourceRef.");if(e.source instanceof ve&&e.source._disposed)throw new TypeError("options.source must not be a disposed Source.");if(e.initInput!==void 0&&!(e.initInput instanceof r))throw new TypeError("options.initInput, when provided, must be an Input.");e.formatOptions!==void 0&&jc(e.formatOptions,"formatOptions"),this._formats=e.formats,this._initInput=e.initInput??null,this._formatOptions=e.formatOptions??{},e.source instanceof ve?this._rootRef=e.source.ref():this._rootRef=e.source,this._sourceRefs.push(this._rootRef)}get _rootSource(){return this._rootRef.source}async _getSourceUncached(e){g(this._rootSource instanceof We);let t=await this._rootSource._resolveRequest(e);return this._emit("source",{source:t.source,request:e,isRoot:e.isRoot}),t}_getSourceCached(e,t=Du){let i=this._sourceCache.find(s=>s.cacheGroup===t&&Ma(s.request,e));if(i)return i.age++,Promise.resolve(i.sourceRef.source.ref());let n=this._sourceCachePromises.find(s=>s.cacheGroup===t&&Ma(s.request,e));if(n)return n.promise.then(s=>s.sourceRef.source.ref());let a=(async()=>{let s=await this._getSourceUncached(e);if(this._disposed)throw s.free(),new ue;if(tr(this._sourceCache,d=>d.cacheGroup===t&&d.sourceRef.source._refCount===1)>=4){let d=Sr(this._sourceCache,m=>m.cacheGroup===t&&m.sourceRef.source._refCount===1?m.age:1/0);g(d!==-1);let f=this._sourceCache[d];this._sourceCache.splice(d,1),f.sourceRef.free(),zs(this._sourceRefs,f.sourceRef)}this._sourceRefs.push(s);let l=this._sourceCachePromises.findIndex(d=>d.request===e);return g(l!==-1),this._sourceCachePromises.splice(l,1),{request:e,sourceRef:s,age:this._nextSourceCacheAge++,cacheGroup:t}})();return this._sourceCachePromises.push({request:e,cacheGroup:t,promise:a}),a.then(s=>{let o=s.sourceRef.source.ref();return this._sourceCache.push(s),o})}_getDemuxer(){return this._demuxerPromise??=(async()=>{this._reader=new qt(this._rootSource),this._emit("source",{source:this._rootSource,request:null,isRoot:!0});for(let e of this._formats)if(await e._canReadInput(this))return this._format=e,this._onFormatDetermined?.(e),e._createDemuxer(this);throw new Li})()}get source(){return this._rootSource}async getFormat(){return await this._getDemuxer(),g(this._format),this._format}async canRead(){try{return await this._getDemuxer(),!0}catch(e){if(e instanceof Li)return!1;throw e}}async getFirstTimestamp(e){e??=await this.getTracks();let t=e.filter(a=>a!==null);if(t.length===0)return 0;let i=await Promise.all(t.map(a=>a._backing.getFirstPacket({metadataOnly:!0}))),n=Math.min(...i.map(a=>a?.timestamp??1/0));return n===1/0?0:n}async computeDuration(e,t){e??=await this.getTracks();let i=e.filter(a=>a!==null);if(i.length===0)return 0;let n=await Promise.all(i.map(a=>a.computeDuration(t)));return Math.max(...n)}async getDurationFromMetadata(e,t){e??=await this.getTracks();let i=e.filter(s=>s!==null),a=(await Promise.all(i.map(s=>s.getDurationFromMetadata(t)))).filter(s=>s!==null);return a.length===0?null:Math.max(...a)}async getTracks(e){e&&=Qr(e);let i=(await this._getTrackBackings()).map(n=>this._wrapBackingAsTrack(n));return Ts(i,e)}async getVideoTracks(e){e&&=Qr(e);let i=(await this.getTracks()).filter(n=>n.isVideoTrack());return Ts(i,e)}async getAudioTracks(e){e&&=Qr(e);let i=(await this.getTracks()).filter(n=>n.isAudioTrack());return Ts(i,e)}async getPrimaryVideoTrack(e){e&&=Qr(e);let t=Gt(e,{sortBy:async n=>[Gr((await n.getDisposition()).default),Gr(await n.hasPairableAudioTrack()),Gr(!await n.hasOnlyKeyPackets()),za(await n.getBitrate())]});return(await this.getVideoTracks(t))[0]??null}async getPrimaryAudioTrack(e){e&&=Qr(e);let t=await this.getPrimaryVideoTrack(),i=Gt(e,{sortBy:async a=>[Gr(!t||a.canBePairedWith(t)),Gr((await a.getDisposition()).default),za(await a.getBitrate())]});return(await this.getAudioTracks(i))[0]??null}async _getTrackBackings(){let e=await this._getDemuxer();return this._trackBackingsCache??=await e.getTrackBackings()}_wrapBackingAsTrack(e){let t=this._backingToTrack.get(e);if(t)return t;let n=e.getType()==="video"?new Kr(this,e):new jr(this,e);return this._backingToTrack.set(e,n),n}async getMimeType(){return(await this._getDemuxer()).getMimeType()}async getMetadataTags(){return(await this._getDemuxer()).getMetadataTags()}dispose(){if(!this._disposed){this._disposed=!0;for(let e of this._sourceRefs)e.free();this._sourceRefs.length=0,this._demuxerPromise&&this._demuxerPromise.then(e=>e.dispose()).catch(()=>{})}}[Symbol.dispose](){this.dispose()}},Li=class extends Error{constructor(e="Input has an unsupported or unrecognizable format."){super(e),this.name="UnsupportedInputFormatError"}},ue=class extends Error{constructor(e="Input has been disposed."){super(e),this.name="InputDisposedError"}};var qt=class{constructor(e){this.source=e}get fileSize(){let e=this.source._getFileSize();if(e===void 0)throw new Error("Reading file size too early; read required first.");return e}get fileSizeNonStrict(){return this.source._getFileSize()??null}requestSlice(e,t){if(this.source._disposed)throw new ue;if(e<0||this.fileSizeNonStrict!==null&&e+t>this.fileSizeNonStrict)return null;if(t===0){let a=new Uint8Array(0);return new Se(a,W(a),0,e,e)}let i=e+t,n=this.source._read(e,i,Ba,Fa);return P(n)?n.then(a=>a?new Se(a.bytes,a.view,a.offset,e,i):null):n?new Se(n.bytes,n.view,n.offset,e,i):null}requestSliceRange(e,t,i){if(this.source._disposed)throw new ue;if(e<0)return null;if(this.fileSizeNonStrict!==null)return this.requestSlice(e,st(this.fileSizeNonStrict-e,t,i));{let n=this.requestSlice(e,i),a=s=>s||(g(this.fileSizeNonStrict!==null),this.requestSlice(e,st(this.fileSizeNonStrict-e,t,i)));return P(n)?n.then(a):a(n)}}requestEntireFile(){if(this.fileSizeNonStrict!==null)return this.requestSlice(0,this.fileSizeNonStrict);let e=1024;return(async()=>{let t=[],i=0;for(;;){if(t.length===1&&this.fileSizeNonStrict!==null)return this.requestSlice(0,this.fileSizeNonStrict);let s=this.requestSliceRange(i,0,e);if(P(s)&&(s=await s),!s||s.length===0)break;let o=M(s,s.length);t.push(o),i+=s.length}let n=new Uint8Array(i),a=0;for(let s of t)n.set(s,a),a+=s.length;return new Se(n,W(n),0,0,i)})()}},Se=class r{constructor(e,t,i,n,a){this.bytes=e,this.view=t,this.offset=i,this.start=n,this.end=a,this.bufferPos=n-i}static tempFromBytes(e){return new r(e,W(e),0,0,e.length)}get length(){return this.end-this.start}get filePos(){return this.offset+this.bufferPos}set filePos(e){this.bufferPos=e-this.offset}get remainingLength(){return Math.max(this.end-this.filePos,0)}skip(e){this.bufferPos+=e}slice(e,t=this.end-e){if(e<this.start||e+t>this.end)throw new RangeError("Slicing outside of original slice.");return new r(this.bytes,this.view,this.offset,e,e+t)}},Be=(r,e)=>{if(e<0||r.filePos<r.start||r.filePos+e>r.end)throw new RangeError(`Tried reading [${r.filePos}, ${r.filePos+e}), but slice is [${r.start}, ${r.end}). This is likely an internal error, please report it alongside the file that caused it.`)},M=(r,e)=>{Be(r,e);let t=r.bytes.subarray(r.bufferPos,r.bufferPos+e);return r.bufferPos+=e,t},U=r=>(Be(r,1),r.view.getUint8(r.bufferPos++)),Nr=(r,e)=>{Be(r,2);let t=r.view.getUint16(r.bufferPos,e);return r.bufferPos+=2,t},re=r=>{Be(r,2);let e=r.view.getUint16(r.bufferPos,!1);return r.bufferPos+=2,e},Xe=r=>{Be(r,3);let e=li(r.view,r.bufferPos,!1);return r.bufferPos+=3,e},Ci=r=>{Be(r,2);let e=r.view.getInt16(r.bufferPos,!1);return r.bufferPos+=2,e},Pt=(r,e)=>{Be(r,4);let t=r.view.getUint32(r.bufferPos,e);return r.bufferPos+=4,t},B=r=>{Be(r,4);let e=r.view.getUint32(r.bufferPos,!1);return r.bufferPos+=4,e},Wt=r=>{Be(r,4);let e=r.view.getUint32(r.bufferPos,!0);return r.bufferPos+=4,e},Tt=r=>{Be(r,4);let e=r.view.getInt32(r.bufferPos,!1);return r.bufferPos+=4,e},Ou=r=>{Be(r,4);let e=r.view.getInt32(r.bufferPos,!0);return r.bufferPos+=4,e},ma=(r,e)=>{let t,i;return e?(t=Pt(r,!0),i=Pt(r,!0)):(i=Pt(r,!1),t=Pt(r,!1)),i*4294967296+t},ge=r=>{let e=B(r),t=B(r);return e*4294967296+t},Zo=r=>{let e=Tt(r),t=B(r);return e*4294967296+t},dc=r=>{let e=Wt(r);return Ou(r)*4294967296+e},nc=r=>{Be(r,4);let e=r.view.getFloat32(r.bufferPos,!1);return r.bufferPos+=4,e},On=r=>{Be(r,8);let e=r.view.getFloat64(r.bufferPos,!1);return r.bufferPos+=8,e},J=(r,e)=>{Be(r,e);let t="";for(let i=0;i<e;i++)t+=String.fromCharCode(r.bytes[r.bufferPos++]);return t},as=(r,e,t)=>ie.decode(M(r,e)).split(`
`).map(a=>a.trim()).filter(a=>a.length>0&&!t?.ignore?.(a));var $e=8,St=16,bt=r=>{let e=B(r),t=J(r,4),i=8;e===1&&(e=ge(r),i=16);let a=e-i;return a<0?null:{name:t,totalSize:e,headerSize:i,contentSize:a}},Vt=r=>Tt(r)/65536,Rn=r=>Tt(r)/1073741824,Na=r=>{let e=0;for(let t=0;t<4;t++){e<<=7;let i=U(r);if(e|=i&127,(i&128)===0)break}return e},Jo=r=>{if(U(r)!==3)throw new Error("Invalid esds: expected ES_Descriptor.");Na(r),r.skip(2);let t=U(r),i=(t&128)!==0,n=(t&64)!==0,a=(t&32)!==0;if(i&&r.skip(2),n){let d=U(r);r.skip(d)}if(a&&r.skip(2),U(r)!==4)throw new Error("Invalid esds: expected DecoderConfigDescriptor.");let o=Na(r),c=r.filePos,l=U(r);r.skip(12);let u=null;if(o>r.filePos-c){if(U(r)!==5)throw new Error("Invalid esds: expected DecoderSpecificInfo.");let f=Na(r);u=M(r,f)}return{objectTypeIndication:l,decoderSpecificInfo:u}},Qe=r=>{let e=re(r);return r.skip(2),e=Math.min(e,r.remainingLength),ie.decode(M(r,e))},ec=r=>{let e=bt(r);if(!e||e.name!=="data"||e.contentSize<8||r.remainingLength<8)return null;let t=B(r);r.skip(4);let i=M(r,e.contentSize-8);switch(t){case 1:return ie.decode(i);case 2:return new $t("utf-16be").decode(i);case 13:return new je(i,"image/jpeg");case 14:return new je(i,"image/png");case 27:return new je(i,"image/bmp");default:return i}};var Xr=class{constructor(){this._connectedTrack=null,this._closingPromise=null,this._closed=!1,this._nominalBitrate=null}_ensureValidAdd(){if(!this._connectedTrack)throw new Error("Source is not connected to an output track.");if(this._connectedTrack.output.state==="canceled")throw new Error("Output has been canceled.");if(this._connectedTrack.output.state==="finalizing"||this._connectedTrack.output.state==="finalized")throw new Error("Output has been finalized.");if(this._connectedTrack.output.state==="pending")throw new Error("Output has not started.");if(this._closed)throw new Error("Source is closed.")}async _start(){}async _flushAndClose(e){}close(){if(this._closingPromise)return;let e=this._connectedTrack;if(!e)throw new Error("Cannot call close without connecting the source to an output track.");if(e.output.state==="pending")throw new Error("Cannot call close before output has been started.");this._closingPromise=(async()=>{await this._flushAndClose(!1),this._closed=!0,!(e.output.state==="finalizing"||e.output.state==="finalized")&&e.output._muxer.onTrackClose(e)})()}async _flushOrWaitForOngoingClose(e){return this._closingPromise??=(async()=>{await this._flushAndClose(e),this._closed=!0})()}},$r=class extends Xr{constructor(e){if(super(),!et.includes(e))throw new TypeError(`Invalid video codec '${e}'. Must be one of: ${et.join(", ")}.`);this._codec=e}},Uu=(r,e)=>{if(r.metadata.hasOnlyKeyPackets&&e.type!=="key")throw new Error("Cannot add non-key packets to a hasOnlyKeyPackets video track.")},Hi=class extends $r{constructor(e){super(e)}add(e,t){if(!(e instanceof Y))throw new TypeError("packet must be an EncodedPacket.");if(e.isMetadataOnly)throw new TypeError("Metadata-only packets cannot be added.");if(t!==void 0&&(!t||typeof t!="object"))throw new TypeError("meta, when provided, must be an object.");return this._ensureValidAdd(),Uu(this._connectedTrack,e),this._connectedTrack.output._muxer.addEncodedVideoPacket(this._connectedTrack,e,t)}};var Yr=class extends Xr{constructor(e){if(super(),!_t.includes(e))throw new TypeError(`Invalid audio codec '${e}'. Must be one of: ${_t.join(", ")}.`);this._codec=e}},Wi=class extends Yr{constructor(e){super(e)}add(e,t){if(!(e instanceof Y))throw new TypeError("packet must be an EncodedPacket.");if(e.isMetadataOnly)throw new TypeError("Metadata-only packets cannot be added.");if(t!==void 0&&(!t||typeof t!="object"))throw new TypeError("meta, when provided, must be an object.");return this._ensureValidAdd(),this._connectedTrack.output._muxer.addEncodedAudioPacket(this._connectedTrack,e,t)}};var qi=class extends Xr{constructor(e){if(super(),!pr.includes(e))throw new TypeError(`Invalid subtitle codec '${e}'. Must be one of: ${pr.join(", ")}.`);this._codec=e}};var et=["avc","hevc","vp9","av1","vp8","prores"],be=["pcm-s16","pcm-s16be","pcm-s24","pcm-s24be","pcm-s32","pcm-s32be","pcm-f32","pcm-f32be","pcm-f64","pcm-f64be","pcm-u8","pcm-s8","ulaw","alaw"],Ss=["aac","opus","mp3","vorbis","flac","ac3","eac3","dts","truehd"],_t=[...Ss,...be],pr=["webvtt"],Ii=["truehd"],Qs=[{maxMacroblocks:99,maxBitrate:64e3,maxDpbMbs:396,level:10},{maxMacroblocks:396,maxBitrate:192e3,maxDpbMbs:900,level:11},{maxMacroblocks:396,maxBitrate:384e3,maxDpbMbs:2376,level:12},{maxMacroblocks:396,maxBitrate:768e3,maxDpbMbs:2376,level:13},{maxMacroblocks:396,maxBitrate:2e6,maxDpbMbs:2376,level:20},{maxMacroblocks:792,maxBitrate:4e6,maxDpbMbs:4752,level:21},{maxMacroblocks:1620,maxBitrate:4e6,maxDpbMbs:8100,level:22},{maxMacroblocks:1620,maxBitrate:1e7,maxDpbMbs:8100,level:30},{maxMacroblocks:3600,maxBitrate:14e6,maxDpbMbs:18e3,level:31},{maxMacroblocks:5120,maxBitrate:2e7,maxDpbMbs:20480,level:32},{maxMacroblocks:8192,maxBitrate:2e7,maxDpbMbs:32768,level:40},{maxMacroblocks:8192,maxBitrate:5e7,maxDpbMbs:32768,level:41},{maxMacroblocks:8704,maxBitrate:5e7,maxDpbMbs:34816,level:42},{maxMacroblocks:22080,maxBitrate:135e6,maxDpbMbs:110400,level:50},{maxMacroblocks:36864,maxBitrate:24e7,maxDpbMbs:184320,level:51},{maxMacroblocks:36864,maxBitrate:24e7,maxDpbMbs:184320,level:52},{maxMacroblocks:139264,maxBitrate:24e7,maxDpbMbs:696320,level:60},{maxMacroblocks:139264,maxBitrate:48e7,maxDpbMbs:696320,level:61},{maxMacroblocks:139264,maxBitrate:8e8,maxDpbMbs:696320,level:62}];var ir=[{maxPictureSize:36864,maxBitrate:2e5,level:10},{maxPictureSize:73728,maxBitrate:8e5,level:11},{maxPictureSize:122880,maxBitrate:18e5,level:20},{maxPictureSize:245760,maxBitrate:36e5,level:21},{maxPictureSize:552960,maxBitrate:72e5,level:30},{maxPictureSize:983040,maxBitrate:12e6,level:31},{maxPictureSize:2228224,maxBitrate:18e6,level:40},{maxPictureSize:2228224,maxBitrate:3e7,level:41},{maxPictureSize:8912896,maxBitrate:6e7,level:50},{maxPictureSize:8912896,maxBitrate:12e7,level:51},{maxPictureSize:8912896,maxBitrate:18e7,level:52},{maxPictureSize:35651584,maxBitrate:18e7,level:60},{maxPictureSize:35651584,maxBitrate:24e7,level:61},{maxPictureSize:35651584,maxBitrate:48e7,level:62}];var Yc=".01.01.01.01.00",Zc=".0.110.01.01.01.0",At=["ap4x","ap4h","apch","apcn","apcs","apco"],Pi=["dtsc","dtsh","dtsl","dtse"];var Jc=r=>{let e=r.split("."),n=(1<<7)+1,a=Number(e[1]),s=e[2],o=Number(s.slice(0,-1)),c=(a<<5)+o,l=s.slice(-1)==="H"?1:0,u=Number(e[3]),d=u===8?0:1,f=u===12?1:0,m=e[4]?Number(e[4]):0,p=e[5]?Number(e[5][0]):1,h=e[5]?Number(e[5][1]):1,k=e[5]?Number(e[5][2]):0,w=(l<<7)+(d<<6)+(f<<5)+(m<<4)+(p<<3)+(h<<2)+k;return[n,c,w,0]},ar=r=>{let{codec:e,codecDescription:t,colorSpace:i,avcCodecInfo:n,hevcCodecInfo:a,vp9CodecInfo:s,av1CodecInfo:o,proresFormat:c}=r;if(e==="avc"){if(g(r.avcType!==null),n){let l=new Uint8Array([n.avcProfileIndication,n.profileCompatibility,n.avcLevelIndication]);return`avc${r.avcType}.${Ft(l)}`}if(!t||t.byteLength<4)throw new TypeError("AVC decoder description is not provided or is not at least 4 bytes long.");return`avc${r.avcType}.${Ft(t.subarray(1,4))}`}else if(e==="hevc"){let l,u,d,f,m,p;if(a)l=a.generalProfileSpace,u=a.generalProfileIdc,d=Us(a.generalProfileCompatibilityFlags),f=a.generalTierFlag,m=a.generalLevelIdc,p=[...a.generalConstraintIndicatorFlags];else{if(!t||t.byteLength<23)throw new TypeError("HEVC decoder description is not provided or is not at least 23 bytes long.");let k=W(t),w=k.getUint8(1);l=w>>6&3,u=w&31,d=Us(k.getUint32(2)),f=w>>5&1,m=k.getUint8(12),p=[];for(let S=0;S<6;S++)p.push(k.getUint8(6+S))}let h="hev1.";for(h+=["","A","B","C"][l]+u,h+=".",h+=d.toString(16).toUpperCase(),h+=".",h+=f===0?"L":"H",h+=m;p.length>0&&p[p.length-1]===0;)p.pop();return p.length>0&&(h+=".",h+=p.map(k=>k.toString(16).toUpperCase()).join(".")),h}else{if(e==="vp8")return"vp8";if(e==="vp9"){if(!s){let S=r.width*r.height,b=$(ir).level;for(let T of ir)if(S<=T.maxPictureSize){b=T.level;break}return`vp09.00.${b.toString().padStart(2,"0")}.08`}let l=s.profile.toString().padStart(2,"0"),u=s.level.toString().padStart(2,"0"),d=s.bitDepth.toString().padStart(2,"0"),f=s.chromaSubsampling.toString().padStart(2,"0"),m=s.colourPrimaries.toString().padStart(2,"0"),p=s.transferCharacteristics.toString().padStart(2,"0"),h=s.matrixCoefficients.toString().padStart(2,"0"),k=s.videoFullRangeFlag.toString().padStart(2,"0"),w=`vp09.${l}.${u}.${d}.${f}`;return w+=`.${m}.${p}.${h}.${k}`,w.endsWith(Yc)&&(w=w.slice(0,-Yc.length)),w}else if(e==="av1"){if(!o){let T=r.width*r.height,y=$(ir).level;for(let A of ir)if(T<=A.maxPictureSize){y=A.level;break}return`av01.0.${y.toString().padStart(2,"0")}M.08`}let l=o.profile,u=o.level.toString().padStart(2,"0"),d=o.tier?"H":"M",f=o.bitDepth.toString().padStart(2,"0"),m=o.monochrome?"1":"0",p=100*o.chromaSubsamplingX+10*o.chromaSubsamplingY+1*(o.chromaSubsamplingX&&o.chromaSubsamplingY?o.chromaSamplePosition:0),h,k,w,S;mn(o)?(h=o.colourPrimaries,k=o.transferCharacteristics,w=o.matrixCoefficients,S=o.videoFullRangeFlag):(h=i?.primaries?Yt[i.primaries]:1,k=i?.transfer?Zt[i.transfer]:1,w=i?.matrix?Jt[i.matrix]:1,S=i?.fullRange?1:0);let b=`av01.${l}.${u}${d}.${f}`;return b+=`.${m}.${p.toString().padStart(3,"0")}`,b+=`.${h.toString().padStart(2,"0")}`,b+=`.${k.toString().padStart(2,"0")}`,b+=`.${w.toString().padStart(2,"0")}`,b+=`.${S}`,b.endsWith(Zc)&&(b=b.slice(0,-Zc.length)),b}else{if(e==="prores")return c??"apch";e!==null&&_e(e)}}throw new TypeError(`Unhandled codec '${e}'.`)},Un=r=>{switch(r.codec){case"avc":{let e=r.avcCodecInfo?.sequenceParameterSets[0];if(!e&&r.codecDescription&&(e=dn(r.codecDescription)?.sequenceParameterSets[0]),e){let t=nr(e);if(t)return{primaries:De[t.colourPrimaries],transfer:Oe[t.transferCharacteristics],matrix:Ue[t.matrixCoefficients],fullRange:!!t.fullRangeFlag}}}break;case"hevc":{let e=r.hevcCodecInfo?.arrays.find(t=>t.nalUnitType===se.SPS_NUT)?.nalUnits[0];if(!e&&r.codecDescription&&(e=fn(r.codecDescription)?.arrays.find(t=>t.nalUnitType===se.SPS_NUT)?.nalUnits[0]),e){let t=sr(e);if(t)return{primaries:De[t.colourPrimaries],transfer:Oe[t.transferCharacteristics],matrix:Ue[t.matrixCoefficients],fullRange:!!t.fullRangeFlag}}}break;case"vp8":break;case"vp9":if(r.vp9CodecInfo)return{primaries:De[r.vp9CodecInfo.colourPrimaries],transfer:Oe[r.vp9CodecInfo.transferCharacteristics],matrix:Ue[r.vp9CodecInfo.matrixCoefficients],fullRange:!!r.vp9CodecInfo.videoFullRangeFlag};break;case"av1":if(r.av1CodecInfo)return{primaries:De[r.av1CodecInfo.colourPrimaries],transfer:Oe[r.av1CodecInfo.transferCharacteristics],matrix:Ue[r.av1CodecInfo.matrixCoefficients],fullRange:!!r.av1CodecInfo.videoFullRangeFlag};break;case"prores":if(r.proresCodecInfo)return{primaries:De[r.proresCodecInfo.colourPrimaries],transfer:Oe[r.proresCodecInfo.transferCharacteristics],matrix:Ue[r.proresCodecInfo.matrixCoefficients],fullRange:r.proresCodecInfo.fullRange};break}return{primaries:void 0,transfer:void 0,matrix:void 0,fullRange:void 0}};var Ir=r=>{let{codec:e,codecDescription:t,aacCodecInfo:i,dtsFormat:n}=r;if(e==="aac"){if(!i)throw new TypeError("AAC codec info must be provided.");if(i.isMpeg2)return"mp4a.67";{let a;return i.objectType!==null?a=i.objectType:a=mi(t).objectType,`mp4a.40.${a}`}}else{if(e==="mp3")return"mp3";if(e==="opus")return"opus";if(e==="vorbis")return"vorbis";if(e==="flac")return"flac";if(e==="ac3")return"ac-3";if(e==="eac3")return"ec-3";if(e==="dts")return n??"dtsc";if(e==="truehd")return"mlpa";if(e&&be.includes(e))return e}throw new TypeError(`Unhandled codec '${e}'.`)};var $c=(r,e)=>{switch(r){case"aac":{if(!e.description)return 1024/e.sampleRate;let t=mi(ke(e.description));if(t.coreSampleRate===null)throw new Error("Invalid AAC sampling frequency index.");return t.frameLength/t.coreSampleRate}case"opus":return Va;case"mp3":{let{sampleRate:t,numberOfChannels:i}=e,n=t>=32e3,a=n?1152:576,s=n?32e3:8e3,o=n?511:255,c=n?i===1?17:32:i===1?9:17,u=Math.floor(a/8*s/t)-4-c;return(1+Math.ceil(o/u))*a/t}case"vorbis":{g(e.description);let t=ke(e.description),i=1,n=2;for(;n>0;)t[i++]<255&&n--;return(1<<(t[i+28]>>4))/2/e.sampleRate}case"ac3":case"eac3":return 256/e.sampleRate;case"dts":return 512/e.sampleRate;case"flac":case"truehd":case"pcm-s16":case"pcm-s16be":case"pcm-s24":case"pcm-s24be":case"pcm-s32":case"pcm-s32be":case"pcm-f32":case"pcm-f32be":case"pcm-f64":case"pcm-f64be":case"pcm-u8":case"pcm-s8":case"ulaw":case"alaw":return 0;default:_e(r),g(!1)}};var ct=48e3,Va=.4,el=/^pcm-([usf])(\d+)(be)?$/,Ye=r=>{if(g(be.includes(r)),r==="ulaw")return{dataType:"ulaw",sampleSize:1,littleEndian:!0,silentValue:255};if(r==="alaw")return{dataType:"alaw",sampleSize:1,littleEndian:!0,silentValue:213};let e=el.exec(r);g(e);let t;e[1]==="u"?t="unsigned":e[1]==="s"?t="signed":t="float";let i=Number(e[2])/8,n=e[3]!=="be",a=r==="pcm-u8"?2**7:0;return{dataType:t,sampleSize:i,littleEndian:n,silentValue:a}},Kt=r=>r.startsWith("avc1")||r.startsWith("avc3")?"avc":r.startsWith("hev1")||r.startsWith("hvc1")?"hevc":r==="vp8"?"vp8":r.startsWith("vp09")?"vp9":r.startsWith("av01")?"av1":At.includes(r)?"prores":r==="mp3"||r==="mp4a.69"||r==="mp4a.6B"||r==="mp4a.6b"||r==="mp4a.40.34"?"mp3":r.startsWith("mp4a.40.")||r==="mp4a.67"?"aac":r==="opus"||r==="Opus"?"opus":r==="vorbis"?"vorbis":r==="flac"?"flac":r==="ac-3"||r==="ac3"?"ac3":r==="ec-3"||r==="eac3"?"eac3":Pi.includes(r)?"dts":r==="mlpa"?"truehd":r==="ulaw"?"ulaw":r==="alaw"?"alaw":el.test(r)?r:r==="webvtt"?"webvtt":null;var zu=["avc1","avc3","hev1","hvc1","vp8","vp09","av01",...At],Nu=/^(avc1|avc3)\.[0-9a-fA-F]{6}$/,Vu=/^(hev1|hvc1)\.(?:[ABC]?\d+)\.[0-9a-fA-F]{1,8}\.[LH]\d+(?:\.[0-9a-fA-F]{1,2}){0,6}$/,Lu=/^vp09(?:\.\d{2}){3}(?:(?:\.\d{2}){5})?$/,Hu=/^av01\.\d\.\d{2}[MH]\.\d{2}(?:\.\d\.\d{3}\.\d{2}\.\d{2}\.\d{2}\.\d)?$/,As=(r,e)=>{if(!r)throw new TypeError("Video chunk metadata must be provided.");if(typeof r!="object")throw new TypeError("Video chunk metadata must be an object.");if(!r.decoderConfig)throw new TypeError("Video chunk metadata must include a decoder configuration.");if(typeof r.decoderConfig!="object")throw new TypeError("Video chunk metadata decoder configuration must be an object.");if(typeof r.decoderConfig.codec!="string")throw new TypeError("Video chunk metadata decoder configuration must specify a codec string.");if(!zu.some(t=>r.decoderConfig.codec.startsWith(t)))throw new TypeError("Video chunk metadata decoder configuration codec string must be a valid video codec string as specified in the Mediabunny Codec Registry.");if(!Number.isInteger(r.decoderConfig.codedWidth)||r.decoderConfig.codedWidth<=0)throw new TypeError("Video chunk metadata decoder configuration must specify a valid codedWidth (positive integer).");if(!Number.isInteger(r.decoderConfig.codedHeight)||r.decoderConfig.codedHeight<=0)throw new TypeError("Video chunk metadata decoder configuration must specify a valid codedHeight (positive integer).");if(r.decoderConfig.displayAspectWidth!==void 0&&(!Number.isInteger(r.decoderConfig.displayAspectWidth)||r.decoderConfig.displayAspectWidth<=0))throw new TypeError("Video chunk metadata decoder configuration displayAspectWidth, when defined, must be a positive integer.");if(r.decoderConfig.displayAspectHeight!==void 0&&(!Number.isInteger(r.decoderConfig.displayAspectHeight)||r.decoderConfig.displayAspectHeight<=0))throw new TypeError("Video chunk metadata decoder configuration displayAspectHeight, when defined, must be a positive integer.");if(r.decoderConfig.displayAspectWidth!==void 0!=(r.decoderConfig.displayAspectHeight!==void 0))throw new TypeError("Video chunk metadata decoder configuration must specify both displayAspectWidth and displayAspectHeight, or neither.");if(r.decoderConfig.description!==void 0&&!Os(r.decoderConfig.description))throw new TypeError("Video chunk metadata decoder configuration description, when defined, must be an ArrayBuffer or an ArrayBuffer view.");if(r.decoderConfig.colorSpace!==void 0){let{colorSpace:t}=r.decoderConfig;if(typeof t!="object")throw new TypeError("Video chunk metadata decoder configuration colorSpace, when provided, must be an object.");let i=Object.keys(Yt);if(t.primaries!=null&&!i.includes(t.primaries))throw new TypeError(`Video chunk metadata decoder configuration colorSpace primaries, when defined, must be one of ${i.join(", ")}.`);let n=Object.keys(Zt);if(t.transfer!=null&&!n.includes(t.transfer))throw new TypeError(`Video chunk metadata decoder configuration colorSpace transfer, when defined, must be one of ${n.join(", ")}.`);let a=Object.keys(Jt);if(t.matrix!=null&&!a.includes(t.matrix))throw new TypeError(`Video chunk metadata decoder configuration colorSpace matrix, when defined, must be one of ${a.join(", ")}.`);if(t.fullRange!=null&&typeof t.fullRange!="boolean")throw new TypeError("Video chunk metadata decoder configuration colorSpace fullRange, when defined, must be a boolean.")}if(r.decoderConfig.codec.startsWith("avc1")||r.decoderConfig.codec.startsWith("avc3")){if(!Nu.test(r.decoderConfig.codec))throw new TypeError("Video chunk metadata decoder configuration codec string for AVC must be a valid AVC codec string as specified in Section 3.4 of RFC 6381.")}else if(r.decoderConfig.codec.startsWith("hev1")||r.decoderConfig.codec.startsWith("hvc1")){if(!Vu.test(r.decoderConfig.codec))throw new TypeError("Video chunk metadata decoder configuration codec string for HEVC must be a valid HEVC codec string as specified in Section E.3 of ISO 14496-15.")}else if(r.decoderConfig.codec.startsWith("vp8")){if(r.decoderConfig.codec!=="vp8")throw new TypeError('Video chunk metadata decoder configuration codec string for VP8 must be "vp8".')}else if(r.decoderConfig.codec.startsWith("vp09")){if(!Lu.test(r.decoderConfig.codec))throw new TypeError('Video chunk metadata decoder configuration codec string for VP9 must be a valid VP9 codec string as specified in Section "Codecs Parameter String" of https://www.webmproject.org/vp9/mp4/.')}else if(r.decoderConfig.codec.startsWith("av01")){if(!Hu.test(r.decoderConfig.codec))throw new TypeError('Video chunk metadata decoder configuration codec string for AV1 must be a valid AV1 codec string as specified in Section "Codecs Parameter String" of https://aomediacodec.github.io/av1-isobmff/.')}else if(At.some(t=>r.decoderConfig.codec.startsWith(t))&&!At.some(t=>r.decoderConfig.codec===t))throw new TypeError(`Video chunk metadata decoder configuration codec string for ProRes must be one of the valid ProRes four-character codes: ${At.join(", ")}.`);if(e!==null&&Kt(r.decoderConfig.codec)!==e)throw new TypeError(`Video chunk metadata decoder configuration codec string '${r.decoderConfig.codec}' does not fit to the track codec '${e}'.`)},Wu=["mp4a","mp3","opus","vorbis","flac","ulaw","alaw","pcm","ac-3","ec-3","dts","mlpa"],xs=(r,e)=>{if(!r)throw new TypeError("Audio chunk metadata must be provided.");if(typeof r!="object")throw new TypeError("Audio chunk metadata must be an object.");if(!r.decoderConfig)throw new TypeError("Audio chunk metadata must include a decoder configuration.");if(typeof r.decoderConfig!="object")throw new TypeError("Audio chunk metadata decoder configuration must be an object.");if(typeof r.decoderConfig.codec!="string")throw new TypeError("Audio chunk metadata decoder configuration must specify a codec string.");if(!Wu.some(t=>r.decoderConfig.codec.startsWith(t)))throw new TypeError("Audio chunk metadata decoder configuration codec string must be a valid audio codec string as specified in the Mediabunny Codec Registry.");if(!Number.isInteger(r.decoderConfig.sampleRate)||r.decoderConfig.sampleRate<=0)throw new TypeError("Audio chunk metadata decoder configuration must specify a valid sampleRate (positive integer).");if(!Number.isInteger(r.decoderConfig.numberOfChannels)||r.decoderConfig.numberOfChannels<=0)throw new TypeError("Audio chunk metadata decoder configuration must specify a valid numberOfChannels (positive integer).");if(r.decoderConfig.description!==void 0&&!Os(r.decoderConfig.description))throw new TypeError("Audio chunk metadata decoder configuration description, when defined, must be an ArrayBuffer or an ArrayBuffer view.");if(r.decoderConfig.codec.startsWith("mp4a")&&r.decoderConfig.codec!=="mp4a.69"&&r.decoderConfig.codec!=="mp4a.6B"&&r.decoderConfig.codec!=="mp4a.6b"){if(!["mp4a.40.2","mp4a.40.02","mp4a.40.5","mp4a.40.05","mp4a.40.29","mp4a.67"].includes(r.decoderConfig.codec))throw new TypeError("Audio chunk metadata decoder configuration codec string for AAC must be a valid AAC codec string as specified in https://www.w3.org/TR/webcodecs-aac-codec-registration/.")}else if(r.decoderConfig.codec.startsWith("mp3")||r.decoderConfig.codec.startsWith("mp4a")){if(r.decoderConfig.codec!=="mp3"&&r.decoderConfig.codec!=="mp4a.69"&&r.decoderConfig.codec!=="mp4a.6B"&&r.decoderConfig.codec!=="mp4a.6b")throw new TypeError('Audio chunk metadata decoder configuration codec string for MP3 must be "mp3", "mp4a.69" or "mp4a.6B".')}else if(r.decoderConfig.codec.startsWith("opus")){if(r.decoderConfig.codec!=="opus")throw new TypeError('Audio chunk metadata decoder configuration codec string for Opus must be "opus".');if(r.decoderConfig.description&&r.decoderConfig.description.byteLength<18)throw new TypeError("Audio chunk metadata decoder configuration description, when specified, is expected to be an Identification Header as specified in Section 5.1 of RFC 7845.")}else if(r.decoderConfig.codec.startsWith("vorbis")){if(r.decoderConfig.codec!=="vorbis")throw new TypeError('Audio chunk metadata decoder configuration codec string for Vorbis must be "vorbis".');if(!r.decoderConfig.description)throw new TypeError("Audio chunk metadata decoder configuration for Vorbis must include a description, which is expected to adhere to the format described in https://www.w3.org/TR/webcodecs-vorbis-codec-registration/.")}else if(r.decoderConfig.codec.startsWith("flac")){if(r.decoderConfig.codec!=="flac")throw new TypeError('Audio chunk metadata decoder configuration codec string for FLAC must be "flac".');if(!r.decoderConfig.description||r.decoderConfig.description.byteLength<42)throw new TypeError("Audio chunk metadata decoder configuration for FLAC must include a description, which is expected to adhere to the format described in https://www.w3.org/TR/webcodecs-flac-codec-registration/.")}else if(r.decoderConfig.codec.startsWith("ac-3")||r.decoderConfig.codec.startsWith("ac3")){if(r.decoderConfig.codec!=="ac-3")throw new TypeError('Audio chunk metadata decoder configuration codec string for AC-3 must be "ac-3".')}else if(r.decoderConfig.codec.startsWith("ec-3")||r.decoderConfig.codec.startsWith("eac3")){if(r.decoderConfig.codec!=="ec-3")throw new TypeError('Audio chunk metadata decoder configuration codec string for EC-3 must be "ec-3".')}else if(r.decoderConfig.codec.startsWith("dts")){if(!Pi.includes(r.decoderConfig.codec))throw new TypeError(`Audio chunk metadata decoder configuration codec string for DTS must be one of the following four-character codes: ${Pi.join(", ")}.`)}else if(r.decoderConfig.codec.startsWith("mlpa")){if(r.decoderConfig.codec!=="mlpa")throw new TypeError('Audio chunk metadata decoder configuration codec string for TrueHD must be "mlpa".')}else if((r.decoderConfig.codec.startsWith("pcm")||r.decoderConfig.codec.startsWith("ulaw")||r.decoderConfig.codec.startsWith("alaw"))&&!be.includes(r.decoderConfig.codec))throw new TypeError(`Audio chunk metadata decoder configuration codec string for PCM must be one of the supported PCM codecs (${be.join(", ")}).`);if(e!==null&&Kt(r.decoderConfig.codec)!==e)throw new TypeError(`Audio chunk metadata decoder configuration codec string '${r.decoderConfig.codec}' does not fit to the track codec '${e}'.`)},tl=r=>{if(!r)throw new TypeError("Subtitle metadata must be provided.");if(typeof r!="object")throw new TypeError("Subtitle metadata must be an object.");if(!r.config)throw new TypeError("Subtitle metadata must include a config object.");if(typeof r.config!="object")throw new TypeError("Subtitle metadata config must be an object.");if(typeof r.config.description!="string")throw new TypeError("Subtitle metadata config description must be a string.")};var Cs=class{constructor(e){this.mutex=new Pe,this.trackTimestampInfo=new WeakMap,this.output=e}onTrackClose(e){}validateTimestamp(e,t,i){let n=this.trackTimestampInfo.get(e);if(n){if(i&&(n.maxTimestampBeforeLastKeyPacket=n.maxTimestamp),n.maxTimestampBeforeLastKeyPacket!==null&&t<n.maxTimestampBeforeLastKeyPacket)throw new Error(`Timestamps cannot be smaller than the largest timestamp of the previous GOP (a GOP begins with a key packet and ends right before the next key packet). Got ${t}s, but largest timestamp is ${n.maxTimestampBeforeLastKeyPacket}s.`);n.maxTimestamp=Math.max(n.maxTimestamp,t)}else{if(!i)throw new Error("First packet must be a key packet.");n={maxTimestamp:t,maxTimestampBeforeLastKeyPacket:null},this.trackTimestampInfo.set(e,n)}}};var gr=class{constructor(e){this.writer=e,this.helper=new Uint8Array(8),this.helperView=new DataView(this.helper.buffer),this.offsets=new WeakMap}writeU32(e){this.helperView.setUint32(0,e,!1),this.writer.write(this.helper.subarray(0,4))}writeU64(e){this.helperView.setUint32(0,Math.floor(e/2**32),!1),this.helperView.setUint32(4,e,!1),this.writer.write(this.helper.subarray(0,8))}writeAscii(e){for(let t=0;t<e.length;t++)this.helperView.setUint8(t%8,e.charCodeAt(t)),t%8===7&&this.writer.write(this.helper);e.length%8!==0&&this.writer.write(this.helper.subarray(0,e.length%8))}writeBox(e){if(this.offsets.set(e,this.writer.getPos()),e.contents&&!e.children)this.writeBoxHeader(e,e.size??e.contents.byteLength+8),this.writer.write(e.contents);else{let t=this.writer.getPos();if(this.writeBoxHeader(e,0),e.contents&&this.writer.write(e.contents),e.children)for(let a of e.children)a&&this.writeBox(a);let i=this.writer.getPos(),n=e.size??i-t;this.writer.seek(t),this.writeBoxHeader(e,n),this.writer.seek(i)}}writeBoxHeader(e,t){this.writeU32(e.largeSize?1:t),this.writeAscii(e.type),e.largeSize&&this.writeU64(t)}measureBoxHeader(e){return 8+(e.largeSize?8:0)}patchBox(e){let t=this.offsets.get(e);g(t!==void 0);let i=this.writer.getPos();this.writer.seek(t),this.writeBox(e),this.writer.seek(i)}measureBox(e){if(e.contents&&!e.children)return this.measureBoxHeader(e)+e.contents.byteLength;{let t=this.measureBoxHeader(e);if(e.contents&&(t+=e.contents.byteLength),e.children)for(let i of e.children)i&&(t+=this.measureBox(i));return t}}},G=new Uint8Array(8),Ke=new DataView(G.buffer),oe=r=>[(r%256+256)%256],L=r=>(Ke.setUint16(0,r,!1),[G[0],G[1]]),Ps=r=>(Ke.setInt16(0,r,!1),[G[0],G[1]]),sl=r=>(Ke.setUint32(0,r,!1),[G[1],G[2],G[3]]),v=r=>(Ke.setUint32(0,r,!1),[G[0],G[1],G[2],G[3]]),mt=r=>(Ke.setInt32(0,r,!1),[G[0],G[1],G[2],G[3]]),rt=r=>(Ke.setUint32(0,Math.floor(r/2**32),!1),Ke.setUint32(4,r,!1),[G[0],G[1],G[2],G[3],G[4],G[5],G[6],G[7]]),rl=r=>(Ke.setInt32(0,Math.floor(r/2**32),!1),Ke.setUint32(4,r,!1),[G[0],G[1],G[2],G[3],G[4],G[5],G[6],G[7]]),al=r=>(Ke.setInt16(0,2**8*r,!1),[G[0],G[1]]),qe=r=>(Ke.setInt32(0,2**16*r,!1),[G[0],G[1],G[2],G[3]]),La=r=>(Ke.setInt32(0,2**30*r,!1),[G[0],G[1],G[2],G[3]]),Ha=(r,e)=>{let t=[],i=r;do{let n=i&127;i>>=7,t.length>0&&(n|=128),t.push(n),e!==void 0&&e--}while(i>0||e);return t.reverse()},Z=(r,e=!1)=>{let t=Array(r.length).fill(null).map((i,n)=>r.charCodeAt(n));return e&&t.push(0),t},ol=r=>[qe(r[0]),qe(r[1]),La(r[2]),qe(r[3]),qe(r[4]),La(r[5]),qe(r[6]),qe(r[7]),La(r[8])],N=(r,e,t)=>({type:r,contents:e&&new Uint8Array(e.flat(10)),children:t}),X=(r,e,t,i,n)=>N(r,[oe(e),sl(t),i??[]],n),cl=r=>r.isQuickTime?N("ftyp",[Z("qt  "),v(512),Z("qt  ")]):r.fragmented?r.cmaf?N("ftyp",[Z("iso5"),v(512),Z("iso5"),Z("iso6"),Z("mp41"),Z("cmfc"),Z("dash")]):N("ftyp",[Z("iso5"),v(512),Z("iso5"),Z("iso6"),Z("mp41")]):N("ftyp",[Z("isom"),v(512),Z("isom"),r.holdsAvc?Z("avc1"):[],Z("mp41")]),qa=()=>N("styp",[Z("iso5"),v(0),Z("iso5"),Z("iso6"),Z("mp41"),Z("cmfc"),Z("dash")]),Ka=(r,e)=>{let t=Math.max(0,r.minWrittenTimestamp),i=Math.max(0,r.maxWrittenEndTimestamp-t);return Number.isFinite(i)||(i=0),X("sidx",1,0,[v(1),v(Fe),rt(te(t,Fe)),rt(0),L(0),L(1),v(e&2147483647),v(te(i,Fe)),v(0)])},Ki=r=>({type:"mdat",largeSize:r}),ll=r=>({type:"free",size:r}),Zr=r=>N("moov",void 0,[qu(r.creationTime,r.trackDatas),...r.trackDatas.map(e=>Ku(e,r.creationTime)),r.isFragmented?Bd(r.trackDatas):null,Ld(r)]),qu=(r,e)=>{let t=Math.max(0,...e.map(s=>Math.max(0,te(kr(s),Fe)+te(s.startTimestampOffset??0,Fe)))),i=Math.max(0,...e.map(s=>s.track.id))+1,n=!it(r)||!it(t),a=n?rt:v;return X("mvhd",+n,0,[a(r),a(r),v(Fe),a(t),qe(1),al(1),Array(10).fill(0),ol(Bt),Array(24).fill(0),v(i)])},Ku=(r,e)=>{let t=wl(r),i=r.startTimestampOffset!==null&&r.startTimestampOffset!==0;return N("trak",void 0,[ju(r,e),i?Gu(r):null,Qu(r,e),t.name!==void 0?N("udta",void 0,[N("name",[...Ee.encode(t.name)])]):null])},ju=(r,e)=>{let t=Math.max(0,te(kr(r),Fe)+te(r.startTimestampOffset??0,Fe)),i=!it(e)||!it(t),n=i?rt:v,a;if(r.type==="video"&&r.track.metadata.transformationMatrix)a=r.track.metadata.transformationMatrix;else if(r.type==="video"){let{rotation:c,flip:l}=r.track.metadata,u=Rt($i(c??0),Yi(l?-1:1,1));a=Xi(u,r.info.width,r.info.height)}else a=Bt;let s=2;r.track.metadata.disposition?.default!==!1&&(s|=1);let o=r.type==="video"?0:r.type==="audio"?1:r.type==="subtitle"?2:_e(r);return X("tkhd",+i,s,[n(e),n(e),v(r.track.id),v(0),n(t),Array(8).fill(0),L(0),L(o),al(r.type==="audio"?1:0),L(0),ol(a),qe(r.type==="video"?r.info.width:0),qe(r.type==="video"?r.info.height:0)])},Gu=r=>{let e=r.startTimestampOffset;if(g(e!==null),e>0){let t=te(e,Fe),i=te(kr(r),Fe),n=!it(t)||!it(i),a=n?rt:v,s=n?rl:mt;return N("edts",void 0,[X("elst",n?1:0,0,[v(2),a(t),s(-1),qe(1),a(i),s(0),qe(1)])])}else{let t=te(-e,r.timescale),i=Math.max(0,te(kr(r),Fe)+te(e,Fe)),n=!Ja(t)||!it(i),a=n?rt:v,s=n?rl:mt;return N("edts",void 0,[X("elst",n?1:0,0,[v(1),a(i),s(t),qe(1)])])}},Qu=(r,e)=>N("mdia",void 0,[Xu(r,e),ja(!0,$u[r.type],Yu[r.type]),Zu(r)]),Xu=(r,e)=>{let t=te(kr(r),r.timescale),i=!it(e)||!it(t),n=i?rt:v;return X("mdhd",+i,0,[n(e),n(e),v(r.timescale),n(t),L(yl(r.track.metadata.languageCode??ne)),L(0)])},$u={video:"vide",audio:"soun",subtitle:"text"},Yu={video:"MediabunnyVideoHandler",audio:"MediabunnySoundHandler",subtitle:"MediabunnyTextHandler"},ja=(r,e,t,i="\0\0\0\0")=>X("hdlr",0,0,[r?Z("mhlr"):v(0),Z(e),Z(i),v(0),v(0),Z(t,!0)]),Zu=r=>N("minf",void 0,[rd[r.type](),id(),ad(r)]),Ju=()=>X("vmhd",0,1,[L(0),L(0),L(0),L(0)]),ed=()=>X("smhd",0,0,[L(0),L(0)]),td=()=>X("nmhd",0,0),rd={video:Ju,audio:ed,subtitle:td},id=()=>N("dinf",void 0,[nd()]),nd=()=>X("dref",0,0,[v(1)],[sd()]),sd=()=>X("url ",0,1),ad=r=>{let e=r.compositionTimeOffsetTable.length>1||r.compositionTimeOffsetTable.some(t=>t.sampleCompositionTimeOffset!==0);return N("stbl",void 0,[od(r),Cd(r),e?vd(r):null,e?Rd(r):null,Ed(r),_d(r),Id(r),Pd(r),...ul(r.samples,!1)])},od=r=>{let e;if(r.type==="video")e=cd(jd(r.track.source._codec,r.info.decoderConfig.codec),r);else if(r.type==="audio"){let t=kl(r.track.source._codec,r.info.decoderConfig.codec,r.muxer.isQuickTime);g(t),e=md(t,r)}else r.type==="subtitle"&&(e=Ad(Xd[r.track.source._codec],r));return g(e),X("stsd",0,0,[v(1)],[e])},cd=(r,e)=>N(r,[Array(6).fill(0),L(1),L(0),L(0),Array(12).fill(0),L(e.info.width),L(e.info.height),v(4718592),v(4718592),v(0),L(1),oe(on.length),Z(on),Array(31-on.length).fill(0),L(e.info.hasAlphaChannel?32:24),Ps(65535)],[Gd[e.track.source._codec]?.(e)??null,ld(e),eo(e.info.decoderConfig.colorSpace)?null:ud(e),Ga(e)]),Ga=r=>r.avgBitrate===0&&r.maxBitrate===0?null:N("btrt",[v(0),v(r.maxBitrate),v(r.avgBitrate)]),ld=r=>r.info.pixelAspectRatio.num===r.info.pixelAspectRatio.den?null:N("pasp",[v(r.info.pixelAspectRatio.num),v(r.info.pixelAspectRatio.den)]),ud=r=>{let e=r.info.decoderConfig.colorSpace;return N("colr",[Z(r.muxer.isQuickTime?"nclc":"nclx"),L(e?.primaries!=null?Yt[e.primaries]:2),L(e?.transfer!=null?Zt[e.transfer]:2),L(e?.matrix!=null?Jt[e.matrix]:2),r.muxer.isQuickTime?[]:oe((e?.fullRange?1:0)<<7)])},dd=r=>r.info.decoderConfig&&N("avcC",[...ke(r.info.decoderConfig.description)]),fd=r=>r.info.decoderConfig&&N("hvcC",[...ke(r.info.decoderConfig.description)]),il=r=>{if(!r.info.decoderConfig)return null;let e=r.info.decoderConfig,t=e.codec.split("."),i=Number(t[1]),n=Number(t[2]),a=Number(t[3]),s=t[4]?Number(t[4]):1,o=t[8]?Number(t[8]):Number(e.colorSpace?.fullRange??0),c=(a<<4)+(s<<1)+o,l=t[5]?Number(t[5]):e.colorSpace?.primaries?Yt[e.colorSpace.primaries]:1,u=t[6]?Number(t[6]):e.colorSpace?.transfer?Zt[e.colorSpace.transfer]:1,d=t[7]?Number(t[7]):e.colorSpace?.matrix?Jt[e.colorSpace.matrix]:1;return X("vpcC",1,0,[oe(i),oe(n),oe(c),oe(l),oe(u),oe(d),L(0)])},hd=r=>N("av1C",Jc(r.info.decoderConfig.codec)),md=(r,e)=>{let t=0,i,n=16,a=be.includes(e.track.source._codec);if(a){let s=e.track.source._codec,{sampleSize:o}=Ye(s);n=8*o,n>16&&(t=1)}if(e.muxer.isQuickTime&&e.track.source._codec!=="truehd"&&(t=1),t===0)i=[Array(6).fill(0),L(1),L(t),L(0),v(0),L(e.info.numberOfChannels),L(n),L(0),L(0),e.track.source._codec==="truehd"?v(e.info.sampleRate):[L(e.info.sampleRate<2**16?e.info.sampleRate:0),L(0)]];else{let s=a?0:-2;i=[Array(6).fill(0),L(1),L(t),L(0),v(0),L(e.info.numberOfChannels),L(Math.min(n,16)),Ps(s),L(0),L(e.info.sampleRate<2**16?e.info.sampleRate:0),L(0),a?[v(1),v(n/8),v(e.info.numberOfChannels*n/8)]:[v(0),v(0),v(0)],v(2)]}return N(r,i,[Qd(e.track.source._codec,e.muxer.isQuickTime)?.(e)??null,Ga(e)])},Wa=r=>{let e;switch(r.track.source._codec){case"aac":e=64;break;case"mp3":e=107;break;case"vorbis":e=221;break;default:throw new Error(`Unhandled audio codec: ${r.track.source._codec}`)}let t=[...oe(e),...oe(21),...sl(0),...v(r.maxBitrate),...v(r.avgBitrate)];if(r.info.decoderConfig.description){let i=ke(r.info.decoderConfig.description);t=[...t,...oe(5),...Ha(i.byteLength),...i]}return t=[...L(1),...oe(0),...oe(4),...Ha(t.length),...t,...oe(6),...oe(1),...oe(2)],t=[...oe(3),...Ha(t.length),...t],X("esds",0,0,t)},Qt=r=>N("wave",void 0,[pd(r),gd(r),N("\0\0\0\0")]),pd=r=>N("frma",[Z(kl(r.track.source._codec,r.info.decoderConfig.codec,r.muxer.isQuickTime))]),gd=r=>{let{littleEndian:e}=Ye(r.track.source._codec);return N("enda",[L(+e)])},kd=r=>{let e=r.info.numberOfChannels,t=312,i=r.info.sampleRate,n=0,a=0,s=new Uint8Array(0),o=r.info.decoderConfig?.description;if(o){g(o.byteLength>=18);let c=ke(o),l=gn(c);e=l.outputChannelCount,t=l.preSkip,i=l.inputSampleRate,n=l.outputGain,a=l.channelMappingFamily,l.channelMappingTable&&(s=l.channelMappingTable)}return N("dOps",[oe(0),oe(e),L(t),v(i),Ps(n),oe(a),...s])},yd=r=>{let e=r.info.decoderConfig?.description;g(e);let t=ke(e);return X("dfLa",0,0,[...t.subarray(4)])},ft=r=>{let{littleEndian:e,sampleSize:t}=Ye(r.track.source._codec),i=+e;return X("pcmC",0,0,[oe(i),oe(8*t)])},wd=r=>{g(r.info.primingPacket);let e=bn(r.info.primingPacket.data);if(!e)throw new Error("Couldn't extract AC-3 frame info from the audio packet. Ensure the packets contain valid AC-3 sync frames (as specified in ETSI TS 102 366).");let t=new Uint8Array(3),i=new q(t);return i.writeBits(2,e.fscod),i.writeBits(5,e.bsid),i.writeBits(3,e.bsmod),i.writeBits(3,e.acmod),i.writeBits(1,e.lfeon),i.writeBits(5,e.bitRateCode),i.writeBits(5,0),N("dac3",[...t])},bd=r=>{g(r.info.primingPacket);let e=Tn(r.info.primingPacket.data);if(!e)throw new Error("Couldn't extract E-AC-3 frame info from the audio packet. Ensure the packets contain valid E-AC-3 sync frames (as specified in ETSI TS 102 366).");let t=16;for(let s of e.substreams)t+=23,s.numDepSub>0?t+=9:t+=1;let i=Math.ceil(t/8),n=new Uint8Array(i),a=new q(n);a.writeBits(13,e.dataRate),a.writeBits(3,e.substreams.length-1);for(let s of e.substreams)a.writeBits(2,s.fscod),a.writeBits(5,s.bsid),a.writeBits(1,0),a.writeBits(1,0),a.writeBits(3,s.bsmod),a.writeBits(3,s.acmod),a.writeBits(1,s.lfeon),a.writeBits(3,0),a.writeBits(4,s.numDepSub),s.numDepSub>0?a.writeBits(9,s.chanLoc):a.writeBits(1,0);return N("dec3",[...n])},Td=r=>{g(r.info.primingPacket);let e=Si(r.info.primingPacket.data);if(!e)throw new Error("Couldn't extract DTS frame info from the audio packet. Ensure the packets contain valid DTS frames as specified in ETSI TS 102 114.");return N("ddts",[...Fo(e)])},Sd=r=>{g(r.info.primingPacket);let e=r.info.primingPacket.data;if(wn("truehd",e)!=="key")throw new Error("Couldn't extract TrueHD stream info from the audio packet. Ensure the first packet is an access unit carrying a major sync.");let t=W(e),i=t.getUint32(8),n=t.getUint16(18)&32767;return N("dmlp",[v(i),L(n<<1),v(0)])},Ad=(r,e)=>N(r,[Array(6).fill(0),L(1)],[$d[e.track.source._codec](e),Ga(e)]),xd=r=>N("vttC",[...Ee.encode(r.info.config.description)]);var Cd=r=>X("stts",0,0,[v(r.timeToSampleTable.length),r.timeToSampleTable.map(e=>[v(e.sampleCount),v(e.sampleDelta)])]),Pd=r=>{if(r.samples.every(t=>t.type==="key"))return null;let e=[...r.samples.entries()].filter(([,t])=>t.type==="key");return X("stss",0,0,[v(e.length),e.map(([t])=>v(t+1))])},Ed=r=>X("stsc",0,0,[v(r.compactlyCodedChunkTable.length),r.compactlyCodedChunkTable.map(e=>[v(e.firstChunk),v(e.samplesPerChunk),v(1)])]),_d=r=>{if(r.type==="audio"&&r.info.requiresPcmTransformation){let{sampleSize:e}=Ye(r.track.source._codec);return X("stsz",0,0,[v(e*r.info.numberOfChannels),v(r.samples.reduce((t,i)=>t+te(i.duration,r.timescale),0))])}return X("stsz",0,0,[v(0),v(r.samples.length),r.samples.map(e=>v(e.size))])},Id=r=>r.finalizedChunks.length>0&&$(r.finalizedChunks).offset>=2**32?X("co64",0,0,[v(r.finalizedChunks.length),r.finalizedChunks.map(e=>rt(e.offset))]):X("stco",0,0,[v(r.finalizedChunks.length),r.finalizedChunks.map(e=>v(e.offset))]),vd=r=>X("ctts",1,0,[v(r.compositionTimeOffsetTable.length),r.compositionTimeOffsetTable.map(e=>[v(e.sampleCount),mt(e.sampleCompositionTimeOffset)])]),Rd=r=>{if(g(r.compositionTimeOffsetTable.length>0),r.samples.length===0)return null;let e=1/0,t=-1/0,i=1/0,n=-1/0;for(let s=0;s<r.compositionTimeOffsetTable.length;s++){let o=r.compositionTimeOffsetTable[s];e=Math.min(e,o.sampleCompositionTimeOffset),t=Math.max(t,o.sampleCompositionTimeOffset)}for(let s=0;s<r.samples.length;s++){let o=r.samples[s];i=Math.min(i,te(o.timestamp,r.timescale)),n=Math.max(n,te(o.timestamp+o.duration,r.timescale))}let a=Math.max(-e,0);return n>=2**31?null:X("cslg",0,0,[mt(a),mt(e),mt(t),mt(i),mt(n)])},ul=(r,e)=>{let t=[];for(let a of r)if(t.length===0)t.push({sampleCount:1,prerollSamples:a.prerollSamples});else{let s=t[t.length-1];s.prerollSamples===a.prerollSamples?s.sampleCount++:t.push({sampleCount:1,prerollSamples:a.prerollSamples})}let i=t.filter(a=>a.prerollSamples!==0);if(i.length===0)return[];let n=e?65537:1;return[X("sgpd",1,0,[Z("roll"),v(2),v(i.length),...i.map(a=>Ps(a.prerollSamples))]),X("sbgp",0,0,[Z("roll"),v(t.length),...t.map(a=>[v(a.sampleCount),v(a.prerollSamples!==0?n++:0)])])]},Bd=r=>N("mvex",void 0,r.map(Fd)),Fd=r=>X("trex",0,0,[v(r.track.id),v(1),v(0),v(0),v(0)]),Qa=(r,e)=>N("moof",void 0,[Md(r),...e.map(Dd)]),Md=r=>X("mfhd",0,0,[v(r)]),dl=r=>{let e=0,t=0,i=0,n=0,a=r.type==="delta";return t|=+a,a?e|=1:e|=2,e<<24|t<<16|i<<8|n},Dd=r=>N("traf",void 0,[Od(r),Ud(r),zd(r),...ul(r.currentChunk.samples,!0)]),Od=r=>{g(r.currentChunk);let e=0;e|=8,e|=16,e|=32,e|=131072;let t=r.currentChunk.samples[1]??r.currentChunk.samples[0],i={duration:t.timescaleUnitsToNextSample,size:t.size,flags:dl(t)};return X("tfhd",0,e,[v(r.track.id),v(i.duration),v(i.size),v(i.flags)])},Ud=r=>(g(r.currentChunk),X("tfdt",1,0,[rt(te(r.currentChunk.startTimestamp,r.timescale))])),zd=r=>{g(r.currentChunk);let e=r.currentChunk.samples.map(h=>h.timescaleUnitsToNextSample),t=r.currentChunk.samples.map(h=>h.size),i=r.currentChunk.samples.map(dl),n=r.currentChunk.samples.map(h=>te(h.timestamp-h.decodeTimestamp,r.timescale)),a=new Set(e),s=new Set(t),o=new Set(i),c=new Set(n),l=o.size===2&&i[0]!==i[1],u=a.size>1,d=s.size>1,f=!l&&o.size>1,m=c.size>1||[...c].some(h=>h!==0),p=0;return p|=1,p|=4*+l,p|=256*+u,p|=512*+d,p|=1024*+f,p|=2048*+m,X("trun",1,p,[v(r.currentChunk.samples.length),v(r.currentChunk.offset-r.currentChunk.moofOffset||0),l?v(i[0]):[],r.currentChunk.samples.map((h,k)=>[u?v(e[k]):[],d?v(t[k]):[],f?v(i[k]):[],m?mt(n[k]):[]])])},fl=r=>N("mfra",void 0,[...r.map(Nd),Vd()]),Nd=r=>{let t=[];for(let i of r.finalizedChunks){let n=i.samples.findIndex(s=>s.type==="key");if(n===-1)continue;let a=i.samples[n];t.push([rt(te(a.timestamp,r.timescale)),rt(i.moofOffset),v(i.trafIndex+1),v(1),v(n+1)])}return X("tfra",1,0,[v(r.track.id),v(63),v(t.length),t])},Vd=()=>X("mfro",0,0,[v(0)]),hl=()=>N("vtte"),ml=(r,e,t,i,n)=>N("vttc",void 0,[n!==null?N("vsid",[mt(n)]):null,t!==null?N("iden",[...Ee.encode(t)]):null,e!==null?N("ctim",[...Ee.encode(Mo(e))]):null,i!==null?N("sttg",[...Ee.encode(i)]):null,N("payl",[...Ee.encode(r)])]),pl=r=>N("vtta",[...Ee.encode(r)]),Ld=r=>{let e=[],t=r.format._options.metadataFormat??"auto",i=r.output._metadataTags;if(t==="mdir"||t==="auto"&&!r.isQuickTime){let n=qd(i);n&&e.push(n)}else if(t==="mdta"){let n=Kd(i);n&&e.push(n)}else(t==="udta"||t==="auto"&&r.isQuickTime)&&Hd(e,r.output._metadataTags);return e.length===0?null:N("udta",void 0,e)},Hd=(r,e)=>{for(let{key:t,value:i}of ui(e))switch(t){case"title":r.push(ht("\xA9nam",i));break;case"description":r.push(ht("\xA9des",i));break;case"artist":r.push(ht("\xA9ART",i));break;case"album":r.push(ht("\xA9alb",i));break;case"albumArtist":r.push(ht("albr",i));break;case"genre":r.push(ht("\xA9gen",i));break;case"date":r.push(ht("\xA9day",i.toISOString().slice(0,10)));break;case"comment":r.push(ht("\xA9cmt",i));break;case"lyrics":r.push(ht("\xA9lyr",i));break;case"raw":break;case"creationTime":break;case"discNumber":case"discsTotal":case"trackNumber":case"tracksTotal":case"beatsPerMinute":case"images":break;default:_e(t)}if(e.raw)for(let t in e.raw){let i=e.raw[t];i==null||t.length!==4||r.some(n=>n.type===t)||(typeof i=="string"?r.push(ht(t,i)):i instanceof Uint8Array&&r.push(N(t,Array.from(i))))}},ht=(r,e)=>{let t=Ee.encode(e);return N(r,[L(t.length),L(yl("und")),Array.from(t)])},nl={"image/jpeg":13,"image/png":14,"image/bmp":27},Wd=new Set(["HMMT","loci","chpl"]),gl=(r,e)=>{let t=[];for(let{key:i,value:n}of ui(r))switch(i){case"title":t.push({key:e?"title":"\xA9nam",value:tt(n)});break;case"description":t.push({key:e?"description":"\xA9des",value:tt(n)});break;case"artist":t.push({key:e?"artist":"\xA9ART",value:tt(n)});break;case"album":t.push({key:e?"album":"\xA9alb",value:tt(n)});break;case"albumArtist":t.push({key:e?"album_artist":"aART",value:tt(n)});break;case"comment":t.push({key:e?"comment":"\xA9cmt",value:tt(n)});break;case"genre":t.push({key:e?"genre":"\xA9gen",value:tt(n)});break;case"beatsPerMinute":e||t.push({key:"tmpo",value:N("data",[v(21),v(0),L(n)])});break;case"lyrics":t.push({key:e?"lyrics":"\xA9lyr",value:tt(n)});break;case"date":t.push({key:e?"date":"\xA9day",value:tt(n.toISOString().slice(0,10))});break;case"images":for(let a of n)a.kind==="coverFront"&&t.push({key:"covr",value:N("data",[v(nl[a.mimeType]??0),v(0),Array.from(a.data)])});break;case"trackNumber":if(e){let a=r.tracksTotal!==void 0?`${n}/${r.tracksTotal}`:n.toString();t.push({key:"track",value:tt(a)})}else t.push({key:"trkn",value:N("data",[v(0),v(0),L(0),L(n),L(r.tracksTotal??0),L(0)])});break;case"discNumber":e||t.push({key:"disc",value:N("data",[v(0),v(0),L(0),L(n),L(r.discsTotal??0),L(0)])});break;case"tracksTotal":case"discsTotal":break;case"raw":break;case"creationTime":break;default:_e(i)}if(r.raw)for(let i in r.raw){let n=r.raw[i];n==null||!e&&(i.length!==4||Wd.has(i))||t.some(a=>a.key===i)||(typeof n=="string"?t.push({key:i,value:tt(n)}):n instanceof Uint8Array?t.push({key:i,value:N("data",[v(0),v(0),Array.from(n)])}):n instanceof je&&t.push({key:i,value:N("data",[v(nl[n.mimeType]??0),v(0),Array.from(n.data)])}))}return t},qd=r=>{let e=gl(r,!1);return e.length===0?null:X("meta",0,0,void 0,[ja(!1,"mdir","","appl"),N("ilst",void 0,e.map(t=>N(t.key,void 0,[t.value])))])},Kd=r=>{let e=gl(r,!0);return e.length===0?null:N("meta",void 0,[ja(!1,"mdta",""),X("keys",0,0,[v(e.length)],e.map(t=>N("mdta",[...Ee.encode(t.key)]))),N("ilst",void 0,e.map((t,i)=>{let n=String.fromCharCode(...v(i+1));return N(n,void 0,[t.value])}))])},tt=r=>N("data",[v(1),v(0),...Ee.encode(r)]),jd=(r,e)=>{switch(r){case"avc":return e.startsWith("avc3")?"avc3":"avc1";case"hevc":return"hvc1";case"vp8":return"vp08";case"vp9":return"vp09";case"av1":return"av01";case"prores":return e}},Gd={avc:dd,hevc:fd,vp8:il,vp9:il,av1:hd,prores:null},kl=(r,e,t)=>{switch(r){case"aac":return"mp4a";case"mp3":return"mp4a";case"opus":return"Opus";case"vorbis":return"mp4a";case"flac":return"fLaC";case"ulaw":return"ulaw";case"alaw":return"alaw";case"pcm-u8":return"raw ";case"pcm-s8":return"sowt";case"ac3":return"ac-3";case"eac3":return"ec-3";case"dts":return e;case"truehd":return"mlpa"}if(t)switch(r){case"pcm-s16":return"sowt";case"pcm-s16be":return"twos";case"pcm-s24":return"in24";case"pcm-s24be":return"in24";case"pcm-s32":return"in32";case"pcm-s32be":return"in32";case"pcm-f32":return"fl32";case"pcm-f32be":return"fl32";case"pcm-f64":return"fl64";case"pcm-f64be":return"fl64"}else switch(r){case"pcm-s16":return"ipcm";case"pcm-s16be":return"ipcm";case"pcm-s24":return"ipcm";case"pcm-s24be":return"ipcm";case"pcm-s32":return"ipcm";case"pcm-s32be":return"ipcm";case"pcm-f32":return"fpcm";case"pcm-f32be":return"fpcm";case"pcm-f64":return"fpcm";case"pcm-f64be":return"fpcm"}},Qd=(r,e)=>{switch(r){case"aac":return Wa;case"mp3":return Wa;case"opus":return kd;case"vorbis":return Wa;case"flac":return yd;case"ac3":return wd;case"eac3":return bd;case"dts":return Td;case"truehd":return Sd}if(e)switch(r){case"pcm-s24":return Qt;case"pcm-s24be":return Qt;case"pcm-s32":return Qt;case"pcm-s32be":return Qt;case"pcm-f32":return Qt;case"pcm-f32be":return Qt;case"pcm-f64":return Qt;case"pcm-f64be":return Qt}else switch(r){case"pcm-s16":return ft;case"pcm-s16be":return ft;case"pcm-s24":return ft;case"pcm-s24be":return ft;case"pcm-s32":return ft;case"pcm-s32be":return ft;case"pcm-f32":return ft;case"pcm-f32be":return ft;case"pcm-f64":return ft;case"pcm-f64be":return ft}return null},Xd={webvtt:"wvtt"},$d={webvtt:xd},yl=r=>{g(r.length===3);let e=0;for(let t=0;t<3;t++)e<<=5,e+=r.charCodeAt(t)-96;return e};var yr=class{constructor(e,t){if(this.finalized=!1,this.started=!1,this.pos=0,this.trackedWrites=null,this.trackedStart=-1,this.trackedEnd=-1,e._writerAcquired)throw new Error("Can't have multiple Writers for the same Target.");this.target=e,e._setMonotonicity(t),e._writerAcquired=!0}start(){g(!this.started),this.target._start(),this.started=!0}write(e){g(this.started&&!this.finalized),this.maybeTrackWrites(e),this.target._write(e,this.pos),this.pos+=e.byteLength}seek(e){this.pos=e}getPos(){return this.pos}async flush(){return g(this.started&&!this.finalized),this.target._flush()}async finalize(){g(this.started&&!this.finalized),await this.target._finalize(),this.finalized=!0}maybeTrackWrites(e){if(!this.trackedWrites)return;let t=this.getPos();if(t<this.trackedStart){if(t+e.byteLength<=this.trackedStart)return;e=e.subarray(this.trackedStart-t),t=0}let i=t+e.byteLength-this.trackedStart,n=this.trackedWrites.byteLength;for(;n<i;)n*=2;if(n!==this.trackedWrites.byteLength){let a=new Uint8Array(n);a.set(this.trackedWrites,0),this.trackedWrites=a}this.trackedWrites.set(e,t-this.trackedStart),this.trackedEnd=Math.max(this.trackedEnd,t+e.byteLength)}startTrackingWrites(){this.trackedWrites=new Uint8Array(2**10),this.trackedStart=this.getPos(),this.trackedEnd=this.trackedStart}stopTrackingWrites(){if(!this.trackedWrites)throw new Error("Internal error: Can't get tracked writes since nothing was tracked.");let t={data:this.trackedWrites.subarray(0,this.trackedEnd-this.trackedStart),start:this.trackedStart,end:this.trackedEnd};return this.trackedWrites=null,t}};var ze=class extends Ne{constructor(){super(...arguments),this._writerAcquired=!1,this._monotonicity=null,this.onwrite=null}_setMonotonicity(e){this._monotonicity!==!1&&(this._monotonicity=e)}_dispatchWrite(e,t){this.onwrite?.(e,t),this._emit("write",{start:e,end:t})}slice(e){if(!Number.isInteger(e)||e<0)throw new TypeError("offset must be a non-negative integer.");return new Es(this,e)}},Xa=2**16,$a=2**32,It=class extends ze{constructor(e={}){if(super(),this.buffer=null,this._maxPos=0,!e||typeof e!="object")throw new TypeError("BufferTarget options, when provided, must be an object.");if(e.onFinalize!==void 0&&typeof e.onFinalize!="function")throw new TypeError("options.onFinalize, when provided, must be a function.");if(this._options=e,this._supportsResize="resize"in new ArrayBuffer(0),this._supportsResize)try{this._buffer=new ArrayBuffer(Xa,{maxByteLength:$a})}catch{this._buffer=new ArrayBuffer(Xa),this._supportsResize=!1}else this._buffer=new ArrayBuffer(Xa);this._bytes=new Uint8Array(this._buffer)}_ensureSize(e){g(this._buffer),g(this._bytes);let t=this._buffer.byteLength;for(;t<e;)t*=2;if(t!==this._buffer.byteLength){if(t>$a)throw new Error(`ArrayBuffer exceeded maximum size of ${$a} bytes. Please consider using another target.`);if(this._supportsResize)this._buffer.resize(t);else{let i=new ArrayBuffer(t),n=new Uint8Array(i);n.set(this._bytes,0),this._buffer=i,this._bytes=n}}}_start(){}_write(e,t){g(this._bytes),this._ensureSize(t+e.byteLength),this._bytes.set(e,t),this._maxPos=Math.max(this._maxPos,t+e.byteLength),this._dispatchWrite(t,t+e.byteLength)}async _flush(){}async _finalize(){g(this._buffer),"transferToFixedLength"in this._buffer?this.buffer=this._buffer.transferToFixedLength(this._maxPos):this.buffer=this._buffer.slice(0,this._maxPos),this._buffer=null,this._bytes=null,this._options.onFinalize&&await this._options.onFinalize(this.buffer),this._emit("finalized")}async _close(){}_getSlice(e,t){return g(this._bytes),this._bytes.slice(e,t)}},Qg=2**24;var Es=class extends ze{constructor(e,t){super(),this._baseTarget=e,this._offset=t}_start(){}_write(e,t){this._baseTarget._write(e,this._offset+t),this._dispatchWrite(t,t+e.byteLength)}_flush(){return this._baseTarget._flush()}async _finalize(){this._emit("finalized")}async _close(){}_setMonotonicity(e){super._setMonotonicity(e),this._baseTarget._setMonotonicity(e)}},wr=class{constructor(e,t){if(this.rootPath=e,this.getTarget=t,typeof e!="string")throw new TypeError("rootPath must be a string.");if(typeof t!="function")throw new TypeError("getTarget must be a function.")}};var Fe=57600,bl=.5,wl=r=>{let e={},t=r.track;return t.metadata.name!==void 0&&(e.name=t.metadata.name),e},te=(r,e,t=!0)=>{let i=r*e;return t?Math.round(i):i},kr=r=>{if(r.samples.length===0)return 0;let e=1/0,t=-1/0;for(let i=0;i<r.samples.length;i++){let n=r.samples[i];n.timestamp<e&&(e=n.timestamp),n.timestamp+n.duration>t&&(t=n.timestamp+n.duration)}return e===1/0?0:t-e},_s=class extends Cs{constructor(e,t){super(e),this.writer=null,this.boxWriter=null,this.initWriter=null,this.initBoxWriter=null,this.auxTarget=new It,this.auxWriter=new yr(this.auxTarget,!1),this.auxBoxWriter=new gr(this.auxWriter),this.mdat=null,this.ftypSize=null,this.trackDatas=[],this.allTracksKnown=gt(),this.finalizedChunks=[],this.wroteFragmentedHeader=!1,this.nextFragmentNumber=1,this.maxWrittenTimestamp=-1/0,this.minWrittenTimestamp=1/0,this.maxWrittenEndTimestamp=-1/0,this.segmentHeaderSize=null,this.format=t,this.formatOptions={...t._options},this.isQuickTime=t instanceof ei,this.isCmaf=t instanceof Jr,this.minimumFragmentDuration=this.formatOptions.minimumFragmentDuration??(t instanceof Jr?1/0:1),this.auxWriter.start()}async start(){let e=await this.mutex.acquire(),t=this.output._metadataTags.creationTime===void 0?new Date:this.output._metadataTags.creationTime;if(this.creationTime=t?Math.floor(t.getTime()/1e3)+En:0,t&&this.creationTime<=0)throw new Error("creationTime must be after 1904-01-01T00:00:00Z for MP4/QuickTime files.");if(this.isCmaf?(this.fastStart="fragmented",this.isFragmented=!0):(this.writer=await this.output._getRootWriter(n=>this.formatOptions.fastStart!==void 0?this.formatOptions.fastStart==="fragmented":n instanceof It),this.boxWriter=new gr(this.writer),this.fastStart=this.formatOptions.fastStart??(this.writer.target instanceof It?"in-memory":!1),this.isFragmented=this.fastStart==="fragmented"),this.isCmaf){if(!this.output._hasInitTarget())throw new Error("CMAF outputs require the initTarget field in OutputOptions to be set; the init segment will be written to it.");let n=await this.output._getInitTarget(),a=new yr(n,!0);a.start(),this.initWriter=a,this.initBoxWriter=new gr(a)}let i=this.output.tracks.some(n=>n.isVideoTrack()&&n.source._codec==="avc");{let n=this.initBoxWriter??this.boxWriter;if(g(n),this.formatOptions.onFtyp&&n.writer.startTrackingWrites(),n.writeBox(cl({isQuickTime:this.isQuickTime,holdsAvc:i,fragmented:this.isFragmented,cmaf:this.isCmaf})),this.formatOptions.onFtyp){let{data:a,start:s}=n.writer.stopTrackingWrites();this.formatOptions.onFtyp(a,s)}this.ftypSize=n.writer.getPos(),this.isCmaf&&await this.initWriter.flush()}if(this.fastStart!=="in-memory")if(this.fastStart==="reserve")for(let n of this.output.tracks){if(n.metadata.maximumPacketCount===void 0)throw new Error("All tracks must specify maximumPacketCount in their metadata when using fastStart: 'reserve'.");if(n.metadata.maximumPacketCount>2**32-1)throw new Error(`Track #${n.id} has a maximumPacketCount of ${n.metadata.maximumPacketCount}, which exceeds the maximum of ${2**32-1} packets per track that a non-fragmented file can hold.`)}else this.isFragmented||(g(this.writer),g(this.boxWriter),this.formatOptions.onMdat&&this.writer.startTrackingWrites(),this.mdat=Ki(!0),this.boxWriter.writeBox(this.mdat));await this.writer?.flush();for(let n of this.output.tracks)n.isVideoTrack()&&n.metadata.decoderConfig?this.getVideoTrackData(n,n.metadata.primingPacket??null,{decoderConfig:n.metadata.decoderConfig}):n.isAudioTrack()&&n.metadata.decoderConfig&&this.getAudioTrackData(n,n.metadata.primingPacket??null,{decoderConfig:n.metadata.decoderConfig});e()}allTracksAreKnown(){for(let e of this.output.tracks)if(!e.source._closed&&!this.trackDatas.some(t=>t.track===e))return!1;return!0}async getMimeType(){await this.allTracksKnown.promise;let e=this.trackDatas.map(t=>t.type==="video"||t.type==="audio"?t.info.decoderConfig.codec:{webvtt:"wvtt"}[t.track.source._codec]);return _n({isQuickTime:this.isQuickTime,hasVideo:this.trackDatas.some(t=>t.type==="video"),hasAudio:this.trackDatas.some(t=>t.type==="audio"),codecStrings:e})}getVideoTrackData(e,t,i){let n=this.trackDatas.find(m=>m.track===e);if(n)return n;As(i,e.source._codec),g(i),g(i.decoderConfig);let a={...i.decoderConfig};g(a.codedWidth!==void 0),g(a.codedHeight!==void 0);let s=!1;if(e.source._codec==="avc"&&!a.description){if(!t)throw new Error("No AVC description provided; you must therefore provide a priming packet.");let m=zt(t.data);if(!m)throw new Error("Couldn't extract an AVCDecoderConfigurationRecord from the AVC packet. Make sure the packets are in Annex B format (as specified in ITU-T-REC-H.264) when not providing a description, or provide a description (must be an AVCDecoderConfigurationRecord as specified in ISO 14496-15) and ensure the packets are in AVCC format.");a.description=To(m),s=!0}else if(e.source._codec==="hevc"&&!a.description){if(!t)throw new Error("No HEVC description provided; you must therefore provide a priming packet.");let m=Nt(t.data);if(!m)throw new Error("Couldn't extract an HEVCDecoderConfigurationRecord from the HEVC packet. Make sure the packets are in Annex B format (as specified in ITU-T-REC-H.265) when not providing a description, or provide a description (must be an HEVCDecoderConfigurationRecord as specified in ISO 14496-15) and ensure the packets are in HEVC format.");a.description=Ao(m),s=!0}let o=so(1/(e.metadata.frameRate??Fe),1e6).den,c=a.displayAspectWidth,l=a.displayAspectHeight,u=c===void 0||l===void 0?{num:1,den:1}:fi({num:c*a.codedHeight,den:l*a.codedWidth}),d=a.codec==="ap4h"||a.codec==="ap4x",f={muxer:this,track:e,type:"video",info:{width:a.codedWidth,height:a.codedHeight,pixelAspectRatio:u,decoderConfig:a,requiresAnnexBTransformation:s,hasAlphaChannel:d},timescale:o,samples:[],sampleQueue:[],timestampProcessingQueue:[],timeToSampleTable:[],compositionTimeOffsetTable:[],lastTimescaleUnits:null,lastSample:null,startTimestampOffset:null,finalizedChunks:[],currentChunk:null,compactlyCodedChunkTable:[],closed:!1,avgBitrate:e.source._nominalBitrate??e.metadata.averageBitrate??0,maxBitrate:e.source._nominalBitrate??e.metadata.bitrate??0};return this.trackDatas.push(f),this.trackDatas.sort((m,p)=>m.track.id-p.track.id),this.allTracksAreKnown()&&this.allTracksKnown.resolve(),f}getAudioTrackData(e,t,i){let n=this.trackDatas.find(c=>c.track===e);if(n)return n;xs(i,e.source._codec),g(i),g(i.decoderConfig);let a={...i.decoderConfig},s=!1;if(e.source._codec==="aac"&&!a.description){if(!t)throw new Error("No AAC description provided; you must therefore provide a priming packet.");let c=Je(Se.tempFromBytes(t.data));if(!c)throw new Error("Couldn't parse ADTS header from the AAC packet. Make sure the packets are in ADTS format (as specified in ISO 13818-7) when not providing a description, or provide a description (must be an AudioSpecificConfig as specified in ISO 14496-3) and ensure the packets are raw AAC data.");let l=Ve[c.samplingFrequencyIndex],u=Dt[c.channelConfiguration];if(l===void 0||u===void 0)throw new Error("Invalid ADTS frame header.");a.description=ho({objectType:c.objectType,outputSampleRate:l,outputNumberOfChannels:u}),s=!0}if(!t){if(e.source._codec==="ac3"||e.source._codec==="eac3")throw new Error("AC-3/E-AC-3 require a priming packet.");if(e.source._codec==="dts")throw new Error("DTS requires a priming packet.");if(e.source._codec==="truehd")throw new Error("TrueHD requires a priming packet.")}let o={muxer:this,track:e,type:"audio",info:{numberOfChannels:i.decoderConfig.numberOfChannels,sampleRate:i.decoderConfig.sampleRate,decoderConfig:a,requiresPcmTransformation:!this.isFragmented&&be.includes(e.source._codec),expectedNextPcmPacketTimestamp:null,requiresAdtsStripping:s,primingPacket:t,preroll:{packetCount:0,accumulatedAudioSamples:0,audioSampleDurationHistory:[]}},timescale:a.sampleRate,samples:[],sampleQueue:[],timestampProcessingQueue:[],timeToSampleTable:[],compositionTimeOffsetTable:[],lastTimescaleUnits:null,lastSample:null,startTimestampOffset:null,finalizedChunks:[],currentChunk:null,compactlyCodedChunkTable:[],closed:!1,avgBitrate:e.source._nominalBitrate??e.metadata.averageBitrate??0,maxBitrate:e.source._nominalBitrate??e.metadata.bitrate??0};return this.trackDatas.push(o),this.trackDatas.sort((c,l)=>c.track.id-l.track.id),this.allTracksAreKnown()&&this.allTracksKnown.resolve(),o}getSubtitleTrackData(e,t){let i=this.trackDatas.find(a=>a.track===e);if(i)return i;tl(t),g(t),g(t.config);let n={muxer:this,track:e,type:"subtitle",info:{config:t.config},timescale:1e3,samples:[],sampleQueue:[],timestampProcessingQueue:[],timeToSampleTable:[],compositionTimeOffsetTable:[],lastTimescaleUnits:null,lastSample:null,startTimestampOffset:null,finalizedChunks:[],currentChunk:null,compactlyCodedChunkTable:[],closed:!1,avgBitrate:e.source._nominalBitrate??e.metadata.averageBitrate??0,maxBitrate:e.source._nominalBitrate??e.metadata.bitrate??0,lastCueEndTimestamp:null,cueQueue:[],nextSourceId:0,cueToSourceId:new WeakMap};return this.trackDatas.push(n),this.trackDatas.sort((a,s)=>a.track.id-s.track.id),this.allTracksAreKnown()&&this.allTracksKnown.resolve(),n}async addEncodedVideoPacket(e,t,i){let n=await this.mutex.acquire();try{let a=this.getVideoTrackData(e,t,i),s=t.data;if(a.info.requiresAnnexBTransformation){let c=[...xr(s)].map(l=>s.subarray(l.offset,l.offset+l.length));if(c.length===0)throw new Error("Failed to transform packet data. Make sure all packets are provided in Annex B format, as specified in ITU-T-REC-H.264 and ITU-T-REC-H.265.");s=bo(c,4)}this.validateTimestamp(a.track,t.timestamp,t.type==="key");let o=this.createSampleForTrack(a,s,t.timestamp,t.duration,t.type,0);await this.registerSample(a,o)}finally{n()}}async addEncodedAudioPacket(e,t,i){let n=await this.mutex.acquire();try{let a=this.getAudioTrackData(e,t,i),s=t.data;if(a.info.requiresAdtsStripping){let f=Je(Se.tempFromBytes(s));if(!f)throw new Error("Expected ADTS frame, didn't get one.");let m=f.crcCheck===null?Et:Ze;s=s.subarray(m)}this.validateTimestamp(a.track,t.timestamp,t.type==="key");let o=t.timestamp,c=t.duration;if(a.info.requiresPcmTransformation){let m=Ye(a.info.decoderConfig.codec).sampleSize*a.info.numberOfChannels;if(c=s.byteLength/m/a.info.sampleRate,a.info.expectedNextPcmPacketTimestamp!==null){let p=o-a.info.expectedNextPcmPacketTimestamp;if(p<.01)o=a.info.expectedNextPcmPacketTimestamp;else{let h=await this.padWithSilence(a,a.info.expectedNextPcmPacketTimestamp,p);o=a.info.expectedNextPcmPacketTimestamp+h}}a.info.expectedNextPcmPacketTimestamp=o+c}let{preroll:l}=a.info,u=0;if(e.source._codec==="aac"||e.source._codec==="vorbis")u=-Math.min(1,l.packetCount);else if(e.source._codec==="mp3")u=-Math.min(2,l.packetCount);else if(e.source._codec==="opus"){let f=Math.round(Va*ct);u=-l.audioSampleDurationHistory.length;let m=kn(s);for(l.accumulatedAudioSamples+=m.durationInSamples,l.audioSampleDurationHistory.push(m.durationInSamples);l.accumulatedAudioSamples-l.audioSampleDurationHistory[0]>=f;)l.accumulatedAudioSamples-=l.audioSampleDurationHistory.shift(),g(l.audioSampleDurationHistory.length>0)}l.packetCount++;let d=this.createSampleForTrack(a,s,o,c,t.type,u);await this.registerSample(a,d)}finally{n()}}async padWithSilence(e,t,i){let n=te(i,e.timescale);if(i=n/e.timescale,n>0){let{sampleSize:a,silentValue:s}=Ye(e.info.decoderConfig.codec),o=n*e.info.numberOfChannels,c=new Uint8Array(a*o).fill(s),l=this.createSampleForTrack(e,new Uint8Array(c.buffer),t,i,"key",0);await this.registerSample(e,l)}return i}async addSubtitleCue(e,t,i){let n=await this.mutex.acquire();try{let a=this.getSubtitleTrackData(e,i);this.validateTimestamp(a.track,t.timestamp,!0),e.source._codec==="webvtt"&&(a.cueQueue.push(t),await this.processWebVTTCues(a,t.timestamp))}finally{n()}}async processWebVTTCues(e,t){for(;e.cueQueue.length>0;){e.lastCueEndTimestamp??=Math.min(0,e.cueQueue[0].timestamp);let i=new Set([]);for(let l of e.cueQueue)g(l.timestamp<=t),g(e.lastCueEndTimestamp<=l.timestamp+l.duration),i.add(Math.max(l.timestamp,e.lastCueEndTimestamp)),i.add(l.timestamp+l.duration);let n=[...i].sort((l,u)=>l-u),a=n[0],s=n[1]??a;if(t<s)break;if(e.lastCueEndTimestamp<a){this.auxWriter.seek(0);let l=hl();this.auxBoxWriter.writeBox(l);let u=this.auxTarget._getSlice(0,this.auxWriter.getPos()),d=this.createSampleForTrack(e,u,e.lastCueEndTimestamp,a-e.lastCueEndTimestamp,"key",0);await this.registerSample(e,d),e.lastCueEndTimestamp=a}this.auxWriter.seek(0);for(let l=0;l<e.cueQueue.length;l++){let u=e.cueQueue[l];if(u.timestamp>=s)break;Ys.lastIndex=0;let d=Ys.test(u.text),f=u.timestamp+u.duration,m=e.cueToSourceId.get(u);if(m===void 0&&s<f&&(m=e.nextSourceId++,e.cueToSourceId.set(u,m)),u.notes){let h=pl(u.notes);this.auxBoxWriter.writeBox(h)}let p=ml(u.text,d?a:null,u.identifier??null,u.settings??null,m??null);this.auxBoxWriter.writeBox(p),f===s&&e.cueQueue.splice(l--,1)}let o=this.auxTarget._getSlice(0,this.auxWriter.getPos()),c=this.createSampleForTrack(e,o,a,s-a,"key",0);await this.registerSample(e,c),e.lastCueEndTimestamp=s}}createSampleForTrack(e,t,i,n,a,s){return{timestamp:i,decodeTimestamp:i,duration:n,data:t,size:t.byteLength,type:a,timescaleUnitsToNextSample:te(n,e.timescale),prerollSamples:s}}processTimestamps(e,t){if(e.timestampProcessingQueue.length===0)return;if(e.type==="audio"&&e.info.requiresPcmTransformation){g(!this.isFragmented),e.startTimestampOffset??=e.timestampProcessingQueue[0].timestamp;let n=0;for(let a=0;a<e.timestampProcessingQueue.length;a++){let s=e.timestampProcessingQueue[a],o=te(s.duration,e.timescale);n+=o}if(e.timeToSampleTable.length===0)e.timeToSampleTable.push({sampleCount:n,sampleDelta:1});else{let a=$(e.timeToSampleTable);a.sampleCount+=n}e.timestampProcessingQueue.length=0;return}let i=e.timestampProcessingQueue.map(n=>n.timestamp).sort((n,a)=>n-a);this.isFragmented?e.startTimestampOffset??=Math.min(i[0],0):e.startTimestampOffset??=i[0];for(let n=0;n<e.timestampProcessingQueue.length;n++){let a=e.timestampProcessingQueue[n];a.decodeTimestamp=i[n];let s=te(a.timestamp-a.decodeTimestamp,e.timescale),o=te(a.duration,e.timescale);if(e.lastTimescaleUnits!==null){g(e.lastSample);let c=te(a.decodeTimestamp,e.timescale,!1),l=Math.round(c-e.lastTimescaleUnits);if(g(l>=0),e.lastTimescaleUnits+=l,e.lastSample.timescaleUnitsToNextSample=l,!this.isFragmented){let u=$(e.timeToSampleTable);if(g(u),u.sampleCount===1){u.sampleDelta=l;let f=e.timeToSampleTable[e.timeToSampleTable.length-2];f&&f.sampleDelta===l&&(f.sampleCount++,e.timeToSampleTable.pop(),u=f)}else u.sampleDelta!==l&&(u.sampleCount--,e.timeToSampleTable.push(u={sampleCount:1,sampleDelta:l}));u.sampleDelta===o?u.sampleCount++:e.timeToSampleTable.push({sampleCount:1,sampleDelta:o});let d=$(e.compositionTimeOffsetTable);g(d),d.sampleCompositionTimeOffset===s?d.sampleCount++:e.compositionTimeOffsetTable.push({sampleCount:1,sampleCompositionTimeOffset:s})}}else e.lastTimescaleUnits=te(a.decodeTimestamp,e.timescale,!1),this.isFragmented||(e.timeToSampleTable.push({sampleCount:1,sampleDelta:o}),e.compositionTimeOffsetTable.push({sampleCount:1,sampleCompositionTimeOffset:s}));e.lastSample=a}if(e.timestampProcessingQueue.length=0,g(e.lastSample),g(e.lastTimescaleUnits!==null),t!==void 0&&e.lastSample.timescaleUnitsToNextSample===0){g(t.type==="key");let n=te(t.timestamp,e.timescale,!1),a=Math.round(n-e.lastTimescaleUnits);e.lastSample.timescaleUnitsToNextSample=a}}async registerSample(e,t){t.type==="key"&&this.processTimestamps(e,t),e.timestampProcessingQueue.push(t),e.sampleQueue.push(t),await this.interleaveSamples()}async addSampleToTrack(e,t){if(!this.isFragmented&&(e.samples.push(t),this.fastStart==="reserve")){let n=e.track.metadata.maximumPacketCount;if(g(n!==void 0),e.samples.length>n)throw new Error(`Track #${e.track.id} has already reached the maximum packet count (${n}). Either add less packets or increase the maximum packet count.`)}let i=!1;if(!e.currentChunk)i=!0;else{e.currentChunk.startTimestamp=Math.min(e.currentChunk.startTimestamp,t.timestamp);let n=t.timestamp-e.currentChunk.startTimestamp;if(this.isFragmented){let a=this.trackDatas.every(s=>{if(e===s)return t.type==="key";let o=s.sampleQueue[0];return o?o.type==="key":s.closed});n>=this.minimumFragmentDuration&&a&&t.timestamp>this.maxWrittenTimestamp&&(i=!0,await this.finalizeFragment())}else i=n>=bl}if(i){if(!this.isFragmented){let n=this.trackDatas.filter(a=>a.currentChunk&&t.timestamp-a.currentChunk.startTimestamp>=bl).sort((a,s)=>a.currentChunk.startTimestamp-s.currentChunk.startTimestamp);for(let a of n)await this.finalizeCurrentChunk(a)}e.currentChunk={startTimestamp:t.timestamp,samples:[],offset:null,moofOffset:null,trafIndex:null}}g(e.currentChunk),e.currentChunk.samples.push(t),this.isFragmented&&(this.maxWrittenTimestamp=Math.max(this.maxWrittenTimestamp,t.timestamp),this.maxWrittenEndTimestamp=Math.max(this.maxWrittenEndTimestamp,t.timestamp+t.duration),this.minWrittenTimestamp=Math.min(this.minWrittenTimestamp,t.timestamp))}async finalizeCurrentChunk(e){g(!this.isFragmented),g(this.writer);let t=e.currentChunk;g(t),e.currentChunk=null,e.finalizedChunks.push(t),this.finalizedChunks.push(t);let i=t.samples.length;if(e.type==="audio"&&e.info.requiresPcmTransformation&&(i=t.samples.reduce((n,a)=>n+te(a.duration,e.timescale),0)),(e.compactlyCodedChunkTable.length===0||$(e.compactlyCodedChunkTable).samplesPerChunk!==i)&&e.compactlyCodedChunkTable.push({firstChunk:e.finalizedChunks.length,samplesPerChunk:i}),this.fastStart==="in-memory"){t.offset=0;return}t.offset=this.writer.getPos();for(let n of t.samples)g(n.data),this.writer.write(n.data),n.data=null;await this.writer.flush()}async interleaveSamples(e=!1){if(!(!e&&!this.allTracksAreKnown())){this.fastStart==="reserve"&&!this.mdat&&await this.createFastStartReserveMdat();e:for(;;){let t=null,i=1/0;for(let a of this.trackDatas){if(!e&&a.sampleQueue.length===0&&!a.closed)break e;a.sampleQueue.length>0&&a.sampleQueue[0].timestamp<i&&(t=a,i=a.sampleQueue[0].timestamp)}if(!t)break;let n=t.sampleQueue.shift();await this.addSampleToTrack(t,n)}}}async finalizeFragment(e=!this.isCmaf){if(g(this.isFragmented),!this.wroteFragmentedHeader){this.wroteFragmentedHeader=!0;let m=this.initBoxWriter??this.boxWriter;g(m),this.formatOptions.onMoov&&m.writer.startTrackingWrites(),this.ensureOneEnabledTrack();let p=Zr(this);if(m.writeBox(p),this.formatOptions.onMoov){let{data:h,start:k}=m.writer.stopTrackingWrites();this.formatOptions.onMoov(h,k)}if(this.isCmaf){g(this.initWriter),await this.initWriter.flush(),await this.initWriter.finalize(),this.writer=await this.output._getRootWriter(!0),this.boxWriter=new gr(this.writer);let h=this.boxWriter.measureBox(qa()),k=this.boxWriter.measureBox(Ka(this,0));this.segmentHeaderSize=h+k,this.writer.seek(this.segmentHeaderSize)}}g(this.writer),g(this.boxWriter);let t=this.trackDatas.filter(m=>m.currentChunk);if(t.length===0){e&&await this.writer.flush();return}let i=this.nextFragmentNumber++,n=Qa(i,t),a=this.writer.getPos(),s=a+this.boxWriter.measureBox(n),o=s+$e,c=1/0;for(let m=0;m<t.length;m++){let p=t[m];g(p.currentChunk),g(p.startTimestampOffset!==null),p.currentChunk.offset=o,p.currentChunk.moofOffset=a,p.currentChunk.trafIndex=m,p.currentChunk.startTimestamp-=p.startTimestampOffset;for(let h of p.currentChunk.samples)o+=h.size,h.timestamp-=p.startTimestampOffset,h.decodeTimestamp-=p.startTimestampOffset;c=Math.min(c,p.currentChunk.startTimestamp)}let l=o-s,u=l>=2**32;if(u)for(let m of t)m.currentChunk.offset+=St-$e;this.formatOptions.onMoof&&this.writer.startTrackingWrites();let d=Qa(i,t);if(this.boxWriter.writeBox(d),this.formatOptions.onMoof){let{data:m,start:p}=this.writer.stopTrackingWrites();this.formatOptions.onMoof(m,p,c)}g(this.writer.getPos()===s),this.formatOptions.onMdat&&this.writer.startTrackingWrites();let f=Ki(u);f.size=l,this.boxWriter.writeBox(f),this.writer.seek(s+(u?St:$e));for(let m of t)for(let p of m.currentChunk.samples)this.writer.write(p.data),p.data=null;if(this.formatOptions.onMdat){let{data:m,start:p}=this.writer.stopTrackingWrites();this.formatOptions.onMdat(m,p)}for(let m of t)m.finalizedChunks.push(m.currentChunk),this.finalizedChunks.push(m.currentChunk),m.currentChunk=null;e&&await this.writer.flush()}async createFastStartReserveMdat(){g(this.writer),g(this.boxWriter),this.ensureOneEnabledTrack();let e=Zr(this),i=this.boxWriter.measureBox(e)+this.computeSampleTableSizeUpperBound()+4096;g(this.ftypSize!==null),this.writer.seek(this.ftypSize+i),this.formatOptions.onMdat&&this.writer.startTrackingWrites(),this.mdat=Ki(!0),this.boxWriter.writeBox(this.mdat)}computeSampleTableSizeUpperBound(){g(this.fastStart==="reserve");let e=0;for(let t of this.trackDatas){let i=t.track.metadata.maximumPacketCount;g(i!==void 0),e+=8*Math.ceil(2/3*i),e+=4*i,e+=8*Math.ceil(2/3*i),e+=12*Math.ceil(2/3*i),e+=4*i,e+=8*i,t.type==="audio"&&(e+=2*i,e+=8*i)}return e}async onTrackClose(e){let t=await this.mutex.acquire(),i=this.trackDatas.find(n=>n.track===e);i&&(i.closed=!0,i.type==="subtitle"&&e.source._codec==="webvtt"&&await this.processWebVTTCues(i,1/0),this.processTimestamps(i)),this.allTracksAreKnown()&&this.allTracksKnown.resolve(),await this.interleaveSamples(),t()}ensureOneEnabledTrack(){for(let e of["video","audio","subtitle"]){let t=this.trackDatas.filter(n=>n.type===e);if(t.length===0)continue;if(!t.some(n=>n.track.metadata.disposition?.default!==!1)){let n=t[0];n.track.metadata.disposition={...n.track.metadata.disposition,default:!0}}}}async forceFragmentFinalization(){g(this.isFragmented);let e=await this.mutex.acquire();try{for(let t of this.trackDatas)t.type==="subtitle"&&t.track.source._codec==="webvtt"&&await this.processWebVTTCues(t,1/0),this.processTimestamps(t);await this.interleaveSamples(!0),await this.finalizeFragment()}finally{e()}}async finalize(){let e=await this.mutex.acquire();this.allTracksKnown.resolve(),this.ensureOneEnabledTrack();for(let t of this.trackDatas)t.closed=!0,t.type==="subtitle"&&t.track.source._codec==="webvtt"&&await this.processWebVTTCues(t,1/0),this.processTimestamps(t);if(await this.interleaveSamples(!0),this.isFragmented)await this.finalizeFragment(!1);else{let t=this.trackDatas.filter(i=>i.currentChunk).sort((i,n)=>i.currentChunk.startTimestamp-n.currentChunk.startTimestamp);for(let i of t)await this.finalizeCurrentChunk(i);for(let i of this.trackDatas){let n=kr(i);if(n>0){let c=0;for(let l of i.samples)c+=l.size;i.avgBitrate=Math.round(8*c/n)}else i.avgBitrate=0;let a=0,s=0,o=0;for(let c=0;c<i.samples.length;c++){let l=i.samples[c];for(s+=l.size;l.decodeTimestamp-i.samples[a].decodeTimestamp>=1;)s-=i.samples[a].size,a++;o=Math.max(o,s)}if(i.maxBitrate=8*o,i.startTimestampOffset!==null)for(let c=0;c<i.samples.length;c++){let l=i.samples[c];l.timestamp-=i.startTimestampOffset,l.decodeTimestamp-=i.startTimestampOffset}}}if(g(this.writer),g(this.boxWriter),this.fastStart==="in-memory"){this.mdat=Ki(!1);let t;for(let n=0;n<2;n++){let a=Zr(this),s=this.boxWriter.measureBox(a);t=this.boxWriter.measureBox(this.mdat);let o=this.writer.getPos()+s+t;for(let c of this.finalizedChunks){c.offset=o;for(let{data:l}of c.samples)g(l),o+=l.byteLength,t+=l.byteLength}if(o<2**32)break;t>=2**32&&(this.mdat.largeSize=!0)}this.formatOptions.onMoov&&this.writer.startTrackingWrites();let i=Zr(this);if(this.boxWriter.writeBox(i),this.formatOptions.onMoov){let{data:n,start:a}=this.writer.stopTrackingWrites();this.formatOptions.onMoov(n,a)}this.formatOptions.onMdat&&this.writer.startTrackingWrites(),this.mdat.size=t,this.boxWriter.writeBox(this.mdat);for(let n of this.finalizedChunks)for(let a of n.samples)g(a.data),this.writer.write(a.data),a.data=null;if(this.formatOptions.onMdat){let{data:n,start:a}=this.writer.stopTrackingWrites();this.formatOptions.onMdat(n,a)}}else if(this.isFragmented)if(this.isCmaf){let t=this.segmentHeaderSize!==null?this.writer.getPos()-this.segmentHeaderSize:0;this.writer.seek(0),this.boxWriter.writeBox(qa()),this.boxWriter.writeBox(Ka(this,t))}else{let t=this.writer.getPos(),i=fl(this.trackDatas);this.boxWriter.writeBox(i);let n=this.writer.getPos()-t;this.writer.seek(this.writer.getPos()-4),this.boxWriter.writeU32(n)}else{g(this.mdat);let t=this.boxWriter.offsets.get(this.mdat);g(t!==void 0);let i=this.writer.getPos()-t;if(this.mdat.size=i,this.mdat.largeSize=i>=2**32,this.boxWriter.patchBox(this.mdat),this.formatOptions.onMdat){let{data:a,start:s}=this.writer.stopTrackingWrites();this.formatOptions.onMdat(a,s)}let n=Zr(this);if(this.fastStart==="reserve"){g(this.ftypSize!==null);let a=this.boxWriter.offsets.get(this.mdat)-this.ftypSize,s=this.boxWriter.measureBox(n);if(s+8>a)throw new Error(`The moov box (${s} bytes) plus a free box (8 bytes) exceed the space reserved for them (${a} bytes) with fastStart: 'reserve'. This is a bug; please report it.`);this.writer.seek(this.ftypSize),this.formatOptions.onMoov&&this.writer.startTrackingWrites(),this.boxWriter.writeBox(n),this.boxWriter.writeBox(ll(a-s))}else this.formatOptions.onMoov&&this.writer.startTrackingWrites(),this.boxWriter.writeBox(n);if(this.formatOptions.onMoov){let{data:a,start:s}=this.writer.stopTrackingWrites();this.formatOptions.onMoov(a,s)}}e()}};var ti=class{get supportsVideoRotationMetadata(){return this.supportsVideoTransformationMetadata}get requiresMaximumPacketCount(){return!1}getSupportedVideoCodecs(){return this.getSupportedCodecs().filter(e=>et.includes(e))}getSupportedAudioCodecs(){return this.getSupportedCodecs().filter(e=>_t.includes(e))}getSupportedSubtitleCodecs(){return this.getSupportedCodecs().filter(e=>pr.includes(e))}_codecUnsupportedHint(e){return""}_isFragmentedIsobmff(){return!1}},ri=class extends ti{constructor(e={}){if(!e||typeof e!="object")throw new TypeError("options must be an object.");if(e.fastStart!==void 0&&![!1,"in-memory","reserve","fragmented"].includes(e.fastStart))throw new TypeError("options.fastStart, when provided, must be false, 'in-memory', 'reserve', or 'fragmented'.");if(e.minimumFragmentDuration!==void 0&&(!Mt(e.minimumFragmentDuration)||e.minimumFragmentDuration<0))throw new TypeError("options.minimumFragmentDuration, when provided, must be a non-negative number.");if(e.onFtyp!==void 0&&typeof e.onFtyp!="function")throw new TypeError("options.onFtyp, when provided, must be a function.");if(e.onMoov!==void 0&&typeof e.onMoov!="function")throw new TypeError("options.onMoov, when provided, must be a function.");if(e.onMdat!==void 0&&typeof e.onMdat!="function")throw new TypeError("options.onMdat, when provided, must be a function.");if(e.onMoof!==void 0&&typeof e.onMoof!="function")throw new TypeError("options.onMoof, when provided, must be a function.");if(e.metadataFormat!==void 0&&!["mdir","mdta","udta","auto"].includes(e.metadataFormat))throw new TypeError("options.metadataFormat, when provided, must be either 'auto', 'mdir', 'mdta', or 'udta'.");super(),this._options=e}getSupportedTrackCounts(){return{video:{min:0,max:4294967295},audio:{min:0,max:4294967295},subtitle:{min:0,max:4294967295},total:{min:0,max:4294967295}}}get supportsVideoTransformationMetadata(){return!0}get supportsTimestampedMediaData(){return!0}get negativeTimestampSupport(){return"full"}get requiresMaximumPacketCount(){return this._options.fastStart==="reserve"}_createMuxer(e){return new _s(e,this)}_isFragmentedIsobmff(){return this._options.fastStart==="fragmented"}},ii=class extends ri{constructor(e){super(e)}get _name(){return"MP4"}get fileExtension(){return".mp4"}get mimeType(){return"video/mp4"}getSupportedCodecs(){return[...et,...Ss,"pcm-s16","pcm-s16be","pcm-s24","pcm-s24be","pcm-s32","pcm-s32be","pcm-f32","pcm-f32be","pcm-f64","pcm-f64be",...pr]}_codecUnsupportedHint(e){return new ei().getSupportedCodecs().includes(e)?" Switching to MOV will grant support for this codec.":""}},Jr=class extends ri{constructor(e){super(e)}get _name(){return"CMAF"}get fileExtension(){return".m4s"}get mimeType(){return"video/mp4"}getSupportedCodecs(){return[...et,...Ss,"pcm-s16","pcm-s16be","pcm-s24","pcm-s24be","pcm-s32","pcm-s32be","pcm-f32","pcm-f32be","pcm-f64","pcm-f64be",...pr]}},ei=class extends ri{constructor(e){super(e)}get _name(){return"MOV"}get fileExtension(){return".mov"}get mimeType(){return"video/quicktime"}getSupportedCodecs(){return[...et,..._t]}_codecUnsupportedHint(e){return new ii().getSupportedCodecs().includes(e)?" Switching to MP4 will grant support for this codec.":""}};var Tl=["video","audio","subtitle"],ni=class r{constructor(e,t,i,n,a){this.id=e,this.output=t,this.type=i,this.source=n,this.metadata=a}isVideoTrack(){return this.type==="video"}isAudioTrack(){return this.type==="audio"}isSubtitleTrack(){return this.type==="subtitle"}canBePairedWith(e){if(!(e instanceof r))throw new TypeError("other must be an OutputTrack.");if(this===e)return!1;let t=Ar(this.metadata.group),i=Ar(e.metadata.group);for(let n of t)if(this.type!==e.type&&i.some(o=>n===o)||i.some(o=>n._pairedGroups.has(o)))return!0;return!1}},Is=class extends ni{constructor(e,t,i,n){super(e,t,"video",i,n)}},vs=class extends ni{constructor(e,t,i,n){super(e,t,"audio",i,n)}},Rs=class extends ni{constructor(e,t,i,n){super(e,t,"subtitle",i,n)}},si=class r{constructor(){this._pairedGroups=new Set}pairWith(e){if(!(e instanceof r))throw new TypeError("other must be an OutputTrackGroup.");if(this===e)throw new TypeError("Cannot pair a group with itself.");this._pairedGroups.add(e),e._pairedGroups.add(this)}},Ya=r=>{if(!r||typeof r!="object")throw new TypeError("metadata must be an object.");if(r.languageCode!==void 0&&!Tr(r.languageCode))throw new TypeError("metadata.languageCode, when provided, must be a three-letter, ISO 639-2/T language code.");if(r.name!==void 0&&typeof r.name!="string")throw new TypeError("metadata.name, when provided, must be a string.");if(r.disposition!==void 0&&lo(r.disposition),r.maximumPacketCount!==void 0&&(!Number.isInteger(r.maximumPacketCount)||r.maximumPacketCount<0))throw new TypeError("metadata.maximumPacketCount, when provided, must be a non-negative integer.");if(r.bitrate!==void 0&&(!Number.isFinite(r.bitrate)||r.bitrate<0))throw new TypeError("metadata.bitrate, when provided, must be a non-negative number.");if(r.averageBitrate!==void 0&&(!Number.isFinite(r.averageBitrate)||r.averageBitrate<0))throw new TypeError("metadata.averageBitrate, when provided, must be a non-negative number.");if(r.group!==void 0&&!(r.group instanceof si)&&(!Array.isArray(r.group)||r.group.some(e=>!(e instanceof si))))throw new TypeError("metadata.group, when provided, must be an OutputTrackGroup instance or an array of OutputTrackGroup instances.")},ji=class extends Ne{get target(){let e="Output.target cannot be used when using PathedTarget with an async callback. Use the 'target' event instead.";if(this._rootTargetPromise)throw new TypeError(e);let t=this._getRootTarget();if(P(t))throw new TypeError(e);return t}constructor(e){if(super(),this.state="pending",this.defaultTrackGroup=new si,this.tracks=[],this._onFinalize=null,this._unfinalizedTargets=new Set,this._rootWriterPromise=null,this._startPromise=null,this._cancelPromise=null,this._finalizePromise=null,this._mutex=new Pe,this._metadataTags={},this._rootTarget=null,this._rootTargetPromise=null,this._firstMediaStreamTimestamp=null,!e||typeof e!="object")throw new TypeError("options must be an object.");if(!(e.format instanceof ti))throw new TypeError("options.format must be an OutputFormat.");if(!(e.target instanceof ze||e.target instanceof wr))throw new TypeError("options.target must be a Target or a PathedTarget.");if(e.target instanceof ze&&this._rememberTarget(e.target),e.initTarget!==void 0&&!(e.initTarget instanceof ze)&&typeof e.initTarget!="function")throw new Error("options.initTarget, when provided, must be a Target or a function that returns or resolves to a Target.");if(e.onFinalize!==void 0&&typeof e.onFinalize!="function")throw new TypeError("options.onFinalize, when provided, must be a function.");this.format=e.format,this._target=e.target,this._onFinalize=e.onFinalize??null,this._initTarget=e.initTarget??null,this._initTarget instanceof ze&&this._rememberTarget(this._initTarget),this._muxer=e.format._createMuxer(this)}_getTargetValidated(e){g(this._target instanceof wr);let t=this._target.getTarget(e),i=n=>{if(!(n instanceof ze))throw new TypeError("getTarget must return a Target.");return n};return P(t)?t.then(i):i(t)}async _getTarget(e){g(this._target instanceof wr);let t=await this._getTargetValidated(e);return this._emit("target",{target:t,request:e,isRoot:e.isRoot}),this.state==="canceled"?await t._close():this._rememberTarget(t),t}_rememberTarget(e){this._unfinalizedTargets.add(e),e.on("finalized",()=>this._unfinalizedTargets.delete(e),{once:!0})}async _getInitTarget(){if(g(this._initTarget!==null),this._initTarget instanceof ze)return this._initTarget;let e=await this._initTarget();return this.state==="canceled"?await e._close():this._rememberTarget(e),e}_hasInitTarget(){return this._initTarget!==null}_getRootTarget(){if(this._rootTarget)return this._rootTarget;if(this._rootTargetPromise)return this._rootTargetPromise;if(this._target instanceof ze)return this._emit("target",{target:this._target,request:null,isRoot:!0}),this._rootTarget=this._target,this._target;let e={path:this._target.rootPath,isRoot:!0,mimeType:this.format.mimeType},t=this._getTargetValidated(e),i=n=>(this.state==="canceled"?n._close():this._rememberTarget(n),this._emit("target",{target:n,request:e,isRoot:!0}),this._rootTarget=n,n);return P(t)?this._rootTargetPromise=t.then(i):i(t)}_getRootWriter(e){return this._rootWriterPromise??=(async()=>{let t=await this._getRootTarget(),i=new yr(t,typeof e=="boolean"?e:e(t));return i.start(),i})()}addVideoTrack(e,t={}){if(!(e instanceof $r))throw new TypeError("source must be a VideoSource.");if(Ya(t),t.rotation!==void 0&&![0,90,180,270].includes(t.rotation))throw new TypeError(`Invalid video rotation: ${t.rotation}. Has to be 0, 90, 180 or 270.`);if(t.flip!==void 0&&typeof t.flip!="boolean")throw new TypeError("metadata.flip, when provided, must be a boolean.");if(t.transformationMatrix!==void 0&&(!Array.isArray(t.transformationMatrix)||t.transformationMatrix.length!==9||!t.transformationMatrix.every(n=>Number.isFinite(n))))throw new TypeError("metadata.transformationMatrix, when provided, must be an array of 9 finite numbers.");if(t.frameRate!==void 0&&(!Number.isFinite(t.frameRate)||t.frameRate<=0))throw new TypeError(`Invalid video frame rate: ${t.frameRate}. Must be a positive number.`);if(t.hasOnlyKeyPackets!==void 0&&typeof t.hasOnlyKeyPackets!="boolean")throw new TypeError("metadata.hasOnlyKeyPackets, when provided, must be a boolean.");if(t.canBeTransparent!==void 0&&typeof t.canBeTransparent!="boolean")throw new TypeError("metadata.canBeTransparent, when provided, must be a boolean.");if(t.decoderConfig!==void 0&&As({decoderConfig:t.decoderConfig},e._codec),t.primingPacket!==void 0){if(!(t.primingPacket instanceof Y))throw new TypeError("metadata.primingPacket, when provided, must be an EncodedPacket.");if(t.decoderConfig===void 0)throw new TypeError("metadata.primingPacket can only be provided alongside metadata.decoderConfig.")}let i={...t};return i.group??=this.defaultTrackGroup,this._addTrack(new Is(this.tracks.length+1,this,e,i))}addAudioTrack(e,t={}){if(!(e instanceof Yr))throw new TypeError("source must be an AudioSource.");if(Ya(t),t.decoderConfig!==void 0&&xs({decoderConfig:t.decoderConfig},e._codec),t.primingPacket!==void 0){if(!(t.primingPacket instanceof Y))throw new TypeError("metadata.primingPacket, when provided, must be an EncodedPacket.");if(t.decoderConfig===void 0)throw new TypeError("metadata.primingPacket can only be provided alongside metadata.decoderConfig.")}let i={...t};return i.group??=this.defaultTrackGroup,this._addTrack(new vs(this.tracks.length+1,this,e,i))}addSubtitleTrack(e,t={}){if(!(e instanceof qi))throw new TypeError("source must be a SubtitleSource.");Ya(t);let i={...t};return i.group??=this.defaultTrackGroup,this._addTrack(new Rs(this.tracks.length+1,this,e,i))}setMetadataTags(e){if(co(e),this.state!=="pending")throw new Error("Cannot set metadata tags after output has been started or canceled.");this._metadataTags=e}_addTrack(e){if(this.state!=="pending")throw new Error("Cannot add track after output has been started or canceled.");if(e.source._connectedTrack)throw new Error("Source is already used for a track.");let t=this.format.getSupportedTrackCounts(),i=this.tracks.reduce((s,o)=>s+(o.type===e.type?1:0),0),n=t[e.type].max;if(i===n)throw new Error(n===0?`${this.format._name} does not support ${e.type} tracks.`:`${this.format._name} does not support more than ${n} ${e.type} track${n===1?"":"s"}.`);let a=t.total.max;if(this.tracks.length===a)throw new Error(`${this.format._name} does not support more than ${a} tracks${a===1?"":"s"} in total.`);if(e.isVideoTrack()){let s=this.format.getSupportedVideoCodecs();if(s.length===0)throw new Error(`${this.format._name} does not support video tracks.`+this.format._codecUnsupportedHint(e.source._codec));if(!s.includes(e.source._codec))throw new Error(`Codec '${e.source._codec}' cannot be contained within ${this.format._name}. Supported video codecs are: ${s.map(o=>`'${o}'`).join(", ")}.`+this.format._codecUnsupportedHint(e.source._codec))}else if(e.isAudioTrack()){let s=this.format.getSupportedAudioCodecs();if(s.length===0)throw new Error(`${this.format._name} does not support audio tracks.`+this.format._codecUnsupportedHint(e.source._codec));if(!s.includes(e.source._codec))throw new Error(`Codec '${e.source._codec}' cannot be contained within ${this.format._name}. Supported audio codecs are: ${s.map(o=>`'${o}'`).join(", ")}.`+this.format._codecUnsupportedHint(e.source._codec))}else if(e.isSubtitleTrack()){let s=this.format.getSupportedSubtitleCodecs();if(s.length===0)throw new Error(`${this.format._name} does not support subtitle tracks.`+this.format._codecUnsupportedHint(e.source._codec));if(!s.includes(e.source._codec))throw new Error(`Codec '${e.source._codec}' cannot be contained within ${this.format._name}. Supported subtitle codecs are: ${s.map(o=>`'${o}'`).join(", ")}.`+this.format._codecUnsupportedHint(e.source._codec))}return this.tracks.push(e),e.source._connectedTrack=e,e}hasEnoughTracks(){let e=this.format.getSupportedTrackCounts();for(let i of Tl){let n=this.tracks.reduce((s,o)=>s+(o.type===i?1:0),0),a=e[i].min;if(n<a)return!1}let t=e.total.min;return!(this.tracks.length<t)}async start(){let e=this.format.getSupportedTrackCounts();for(let i of Tl){let n=this.tracks.reduce((s,o)=>s+(o.type===i?1:0),0),a=e[i].min;if(n<a)throw new Error(a===e[i].max?`${this.format._name} requires exactly ${a} ${i} track${a===1?"":"s"}.`:`${this.format._name} requires at least ${a} ${i} track${a===1?"":"s"}.`)}let t=e.total.min;if(this.tracks.length<t)throw new Error(t===e.total.max?`${this.format._name} requires exactly ${t} track${t===1?"":"s"}.`:`${this.format._name} requires at least ${t} track${t===1?"":"s"}.`);if(this.state==="canceled")throw new Error("Output has been canceled.");return this._startPromise?(H._warn("Output has already been started."),this._startPromise):this._startPromise=(async()=>{this.state="started";let i=this._mutex.acquire();try{await this._muxer.start();let n=this.tracks.map(a=>a.source._start());await Promise.all(n)}finally{(await i)()}})()}getMimeType(){return this._muxer.getMimeType()}async cancel(){if(this.state==="canceled")return this._cancelPromise??void 0;if(this.state==="finalizing"||this.state==="finalized"){this.state==="finalized"&&H._warn("Output has already been finalized.");return}return this._cancelPromise=(async()=>{this.state="canceled";let e=await this._mutex.acquire();try{let t=this.tracks.map(i=>i.source._flushOrWaitForOngoingClose(!0));await Promise.all(t),await Promise.all([...this._unfinalizedTargets].map(i=>i._close())),this._unfinalizedTargets.clear()}finally{e()}})()}async finalize(){if(this.state==="pending")throw new Error("Cannot finalize before starting.");if(this.state==="canceled")throw new Error("Cannot finalize after canceling.");return this._finalizePromise?(H._warn("Output has already been finalized."),this._finalizePromise):this._finalizePromise=(async()=>{this.state="finalizing";let e=await this._mutex.acquire();try{let t=this.tracks.map(i=>i.source._flushOrWaitForOngoingClose(!1));if(await Promise.all(t),await this._muxer.finalize(),this._rootWriterPromise){let i=await this._rootWriterPromise;i.finalized||(await i.flush(),await i.finalize())}this._onFinalize&&await this._onFinalize(),this.state="finalized"}catch(t){throw this.state="canceled",t}finally{await Promise.all([...this._unfinalizedTargets].map(t=>t._close().catch(()=>{}))),this._unfinalizedTargets.clear(),e()}})()}};var Sl=Symbol.for("mediabunny loaded");globalThis[Sl]&&H._error(`[WARNING]
Mediabunny was loaded twice. This will likely cause Mediabunny not to work correctly. Check if multiple dependencies are importing different versions of Mediabunny, or if something is being bundled incorrectly.`);globalThis[Sl]=!0;return _l(Yd);})();
try { if (typeof Mediabunny !== "undefined" && !globalThis.Mediabunny) { globalThis.Mediabunny = Mediabunny; } } catch (eMB) { console.warn("mediabunny bridge failed", eMB); }
})();
