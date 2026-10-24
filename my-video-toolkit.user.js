// ==UserScript==
// @name         我的视频工具箱 v2
// @namespace    whxclp
// @version      2.0.2
// @description  自研轻量视频增强：倍速调速、画面旋转/镜像/缩放/位移、亮度对比度饱和度滤镜、截图、画中画、循环播放。下载推荐用本机 yt-dlp 脚本（① 当前页 / ② 任意链接），兜底为分片合并与边播边录。菜单固定向左展开，绝不超出屏幕右侧。
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

  function capFetch(url, p) {
    if (!p || typeof p.then !== 'function') return p;
    return p.then(function (r) {
      try {
        var ct = (r.headers && r.headers.get) ? (r.headers.get('content-type') || '') : '';
        if (!mediaKind(url, ct)) return r;
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
    '  background:rgba(20,20,24,.92);border:1px solid rgba(255,255,255,.14);border-top:none;border-radius:0 0 8px 8px;',
    '  padding:4px 6px;box-shadow:0 4px 16px rgba(0,0,0,.4);font-size:13px;user-select:none;',
    '  transform:translateY(calc(-100% + 3px));transition:transform .22s ease;}',
    '.mvt-bar.mvt-on{transform:translateY(0);}',
    '.mvt-btn{position:relative;color:#eee;background:transparent;border:none;border-radius:6px;',
    '  padding:5px 9px;cursor:pointer;font-size:13px;line-height:1;white-space:nowrap;font-family:inherit;}',
    '.mvt-btn:hover{background:rgba(255,255,255,.14);}',
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
   * bakedUrl 非空 => 把链接烤进脚本；为空 => 运行时粘贴/拖放链接。 */
  function buildYtDlpBat(bakedUrl) {
    var L = [
      '@echo off',
      'chcp 65001 >nul',
      'setlocal EnableDelayedExpansion',
      '',
      'set "TOOLS=%LOCALAPPDATA%\\mvt\\bin"',
      'if not exist "%TOOLS%" mkdir "%TOOLS%" >nul 2>nul',
      'set "YTDLP=%TOOLS%\\yt-dlp.exe"',
      'if not exist "%YTDLP%" (',
      '  echo [mvt] 首次运行：下载 yt-dlp ...',
      '  curl.exe -L --ssl-no-revoke -o "%YTDLP%" "https://github.com/yt-dlp/yt-dlp/releases/latest/download/yt-dlp.exe"',
      '  for %%F in ("%YTDLP%") do if %%~zF LSS 1000000 del /f /q "%YTDLP%" >nul 2>nul',
      "  if not exist \"%YTDLP%\" powershell -NoProfile -Command \"Invoke-WebRequest -Uri 'https://github.com/yt-dlp/yt-dlp/releases/latest/download/yt-dlp.exe' -OutFile '%YTDLP%' -UseBasicParsing\"",
      '  del /f /q "%YTDLP%:Zone.Identifier" 2>nul',
      ')',
      'if not exist "%YTDLP%" (',
      '  echo [mvt] yt-dlp 下载失败，请检查网络后重试。',
      '  pause & exit /b 1',
      ')',
      '',
      'set "FFDIR=%TOOLS%\\ffmpeg\\bin"',
      'if not exist "%FFDIR%\\ffmpeg.exe" (',
      '  echo [mvt] 首次运行：下载 ffmpeg（约 70MB，请稍候）...',
      '  set "FFZIP=%TOOLS%\\ffmpeg.zip"',
      '  curl.exe -L --ssl-no-revoke -o "!FFZIP!" "https://www.gyan.dev/ffmpeg/builds/ffmpeg-release-essentials.zip"',
      '  for %%F in ("!FFZIP!") do if %%~zF LSS 1000000 del /f /q "!FFZIP!" >nul 2>nul',
      "  if not exist \"!FFZIP!\" powershell -NoProfile -Command \"Invoke-WebRequest -Uri 'https://www.gyan.dev/ffmpeg/builds/ffmpeg-release-essentials.zip' -OutFile '!FFZIP!' -UseBasicParsing\"",
      '  if exist "!FFZIP!" (',
      '    echo [mvt] 解压 ffmpeg ...',
      '    if not exist "%TOOLS%\\ffmpeg_extract" mkdir "%TOOLS%\\ffmpeg_extract"',
      '    tar -xf "!FFZIP!" -C "%TOOLS%\\ffmpeg_extract"',
      '    for /d %%D in ("%TOOLS%\\ffmpeg_extract\\ffmpeg-*") do (',
      '      if exist "%%D\\bin\\ffmpeg.exe" xcopy /E /Y "%%D\\*" "%TOOLS%\\ffmpeg\\" >nul',
      '    )',
      '    rd /s /q "%TOOLS%\\ffmpeg_extract" >nul 2>nul',
      '    del /f /q "!FFZIP!" >nul 2>nul',
      '  )',
      ')',
      'if not exist "%FFDIR%\\ffmpeg.exe" (',
      '  echo [mvt] ffmpeg 下载/解压失败，请检查网络后重试。',
      '  pause & exit /b 1',
      ')',
      '',
      'set "OUTDIR=%USERPROFILE%\\Desktop\\视频下载"',
      'if not exist "%OUTDIR%" mkdir "%OUTDIR%" >nul 2>nul',
      ''
    ];
    if (bakedUrl) {
      L.push('set "URL=' + bakedUrl + '"');
      L.push('if "%URL%"=="" (');
      L.push('  echo  [mvt] 链接为空。');
      L.push('  pause & exit /b 1');
      L.push(')');
    } else {
      L.push('set "URL=%~1"');
      L.push('if "%URL%"=="" (');
      L.push('  echo.');
      L.push('  echo  [mvt] 粘贴视频链接（支持 B站/YouTube 等 yt-dlp 站点）后回车：');
      L.push('  set /p "URL=> "');
      L.push(')');
      L.push('if "%URL%"=="" (');
      L.push('  echo  [mvt] 未输入链接。');
      L.push('  pause & exit /b 1');
      L.push(')');
    }
    L.push('');
    L.push('echo.');
    L.push('echo  [mvt] 下载中 ... 输出目录：%OUTDIR%');
    L.push('echo.');
    L.push('"%YTDLP%" --no-playlist -f "bv*+ba/b" --merge-output-format mp4 --ffmpeg-location "%FFDIR%" -P "%OUTDIR%" --no-mtime "%URL%"');
    L.push('');
    L.push('echo.');
    L.push('if errorlevel 1 ( echo  [mvt] 下载失败，见上方信息。 ) else ( echo  [mvt] 完成，文件在：%OUTDIR% )');
    L.push('pause');
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
  function buildYtDlpSegBat(startSec, endSec, bakedUrl) {
    var S = fmtTime(startSec), E = fmtTime(endSec);
    function pad(n) { return n < 10 ? '0' + n : '' + n; }
    function fn(sec) {
      sec = Math.max(0, Math.floor(sec || 0));
      return pad(Math.floor(sec / 3600)) + pad(Math.floor((sec % 3600) / 60)) + pad(sec % 60);
    }
    var outName = '片段_' + fn(startSec) + '-' + fn(endSec) + '.mp4';
    var L = [
      '@echo off',
      'chcp 65001 >nul',
      'setlocal EnableDelayedExpansion',
      '',
      'set "TOOLS=%LOCALAPPDATA%\\mvt\\bin"',
      'if not exist "%TOOLS%" mkdir "%TOOLS%" >nul 2>nul',
      'set "YTDLP=%TOOLS%\\yt-dlp.exe"',
      'if not exist "%YTDLP%" (',
      '  echo [mvt] 首次运行：下载 yt-dlp ...',
      '  curl.exe -L --ssl-no-revoke -o "%YTDLP%" "https://github.com/yt-dlp/yt-dlp/releases/latest/download/yt-dlp.exe"',
      '  for %%F in ("%YTDLP%") do if %%~zF LSS 1000000 del /f /q "%YTDLP%" >nul 2>nul',
      "  if not exist \"%YTDLP%\" powershell -NoProfile -Command \"Invoke-WebRequest -Uri 'https://github.com/yt-dlp/yt-dlp/releases/latest/download/yt-dlp.exe' -OutFile '%YTDLP%' -UseBasicParsing\"",
      '  del /f /q "%YTDLP%:Zone.Identifier" 2>nul',
      ')',
      'if not exist "%YTDLP%" (',
      '  echo [mvt] yt-dlp 下载失败，请检查网络后重试。',
      '  pause & exit /b 1',
      ')',
      '',
      'set "FFDIR=%TOOLS%\\ffmpeg\\bin"',
      'if not exist "%FFDIR%\\ffmpeg.exe" (',
      '  echo [mvt] 首次运行：下载 ffmpeg（约 70MB，请稍候）...',
      '  set "FFZIP=%TOOLS%\\ffmpeg.zip"',
      '  curl.exe -L --ssl-no-revoke -o "!FFZIP!" "https://www.gyan.dev/ffmpeg/builds/ffmpeg-release-essentials.zip"',
      '  for %%F in ("!FFZIP!") do if %%~zF LSS 1000000 del /f /q "!FFZIP!" >nul 2>nul',
      "  if not exist \"!FFZIP!\" powershell -NoProfile -Command \"Invoke-WebRequest -Uri 'https://www.gyan.dev/ffmpeg/builds/ffmpeg-release-essentials.zip' -OutFile '!FFZIP!' -UseBasicParsing\"",
      '  if exist "!FFZIP!" (',
      '    echo [mvt] 解压 ffmpeg ...',
      '    if not exist "%TOOLS%\\ffmpeg_extract" mkdir "%TOOLS%\\ffmpeg_extract"',
      '    tar -xf "!FFZIP!" -C "%TOOLS%\\ffmpeg_extract"',
      '    for /d %%D in ("%TOOLS%\\ffmpeg_extract\\ffmpeg-*") do (',
      '      if exist "%%D\\bin\\ffmpeg.exe" xcopy /E /Y "%%D\\*" "%TOOLS%\\ffmpeg\\" >nul',
      '    )',
      '    rd /s /q "%TOOLS%\\ffmpeg_extract" >nul 2>nul',
      '    del /f /q "!FFZIP!" >nul 2>nul',
      '  )',
      ')',
      'if not exist "%FFDIR%\\ffmpeg.exe" (',
      '  echo [mvt] ffmpeg 下载/解压失败，请检查网络后重试。',
      '  pause & exit /b 1',
      ')',
      '',
      'set "OUTDIR=%USERPROFILE%\\Desktop\\视频下载"',
      'if not exist "%OUTDIR%" mkdir "%OUTDIR%" >nul 2>nul',
      'set "URL=' + bakedUrl + '"',
      'if "%URL%"=="" (',
      '  echo  [mvt] 链接为空。',
      '  pause & exit /b 1',
      ')',
      '',
      'set "TMPD=%OUTDIR%\\__seg_tmp"',
      'if not exist "%TMPD%" mkdir "%TMPD%"',
      'echo.',
      'echo  [mvt] 步骤1/2：下载完整视频到临时目录...',
      '"%YTDLP%" --no-playlist -f "bv*+ba/b" --merge-output-format mp4 --ffmpeg-location "%FFDIR%" -o "%TMPD%\\full.%%(ext)s" --no-mtime "%URL%"',
      'if not exist "%TMPD%\\full.mp4" (',
      '  echo  [mvt] 完整视频下载失败，见上方信息。',
      '  pause & exit /b 1',
      ')',
      'echo.',
      'echo  [mvt] 步骤2/2：ffmpeg 精确裁剪 ' + S + ' ~ ' + E + ' -> ' + outName,
      '"%FFDIR%\\ffmpeg.exe" -ss ' + S + ' -to ' + E + ' -i "%TMPD%\\full.mp4" -c:v libx264 -c:a aac -preset veryfast "%OUTDIR%\\' + outName + '"',
      'echo.',
      'if errorlevel 1 ( echo  [mvt] 裁剪失败，完整视频已保留在 %TMPD% ) else ( echo  [mvt] 完成：%OUTDIR%\\' + outName + ' )',
      'del /f /q "%TMPD%\\full.mp4" 2>nul',
      'rd /s /q "%TMPD%" 2>nul',
      'pause'
    ];
    return L.join('\r\n') + '\r\n';
  }

  function genSegBat() {
    var v = cur;
    if (!v || !v.currentTime) { toast('没有正在播放的视频，无法定位播放点', 3000); return; }
    var ct = v.currentTime;
    var url = String(location.href || '').split('#')[0];
    if (!/bilibili\\.com/i.test(url) && cur) {
      var s = cur.currentSrc || cur.src || '';
      if (s && s.indexOf('http') === 0) url = s;
    }
    if (!url) { toast('拿不到视频地址', 3000); return; }
    showSegPanel(ct, url);
  }

  function showSegPanel(ct, url) {
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
      var bat = buildYtDlpSegBat(start, end, url);
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

    var bat = buildYtDlpBat(url);
    saveBlob(new Blob([bat], { type: 'application/octet-stream' }), '下载本视频.bat');
    if (navigator.clipboard && navigator.clipboard.writeText) {
      navigator.clipboard.writeText(bat).then(
        function () { toast('已生成「下载本视频.bat」并复制命令，双击即自动下载合并（首次会先拉取依赖）', 6000); },
        function () { toast('已生成「下载本视频.bat」，双击即自动下载合并', 4000); }
      );
    } else {
      toast('已生成「下载本视频.bat」，双击即自动下载合并', 4000);
    }
  }

  /* ================= 下载模式五：生成「通用」下载脚本（运行后粘贴任意链接） =================
   * 等价桌面那个 视频下载合并.bat，但更稳：自举补齐 yt-dlp/ffmpeg，不限 B站、不限是否在视频页。 */
  function genDownBatGeneric() {
    var bat = buildYtDlpBat('');
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
    bar.setAttribute('data-mvt-ver', '2.0.2');

    var logo = document.createElement('span');
    logo.className = 'mvt-logo';
    logo.textContent = '工具箱';
    bar.appendChild(logo);

    /* 版本角标：页面上看到 v1.5.1 才说明新版真的生效了 */
    var ver = document.createElement('span');
    ver.className = 'mvt-ver';
    ver.textContent = 'v2.0.2';
    ver.title = '脚本版本号';
    bar.appendChild(ver);

    /* --- 倍速 --- */
    rateBtn = mBtn('倍速 1x', true);
    var mRate = document.createElement('div');
    mRate.className = 'mvt-menu';
    [0.5, 0.75, 1, 1.25, 1.5, 2, 2.5, 3].forEach(function (r) {
      mRate.appendChild(mItem(r + 'x', function () { setRate(cur, r); }));
    });
    rateBtn.appendChild(mRate);
    bar.appendChild(rateBtn);

    /* --- 画面 --- */
    var picBtn = mBtn('画面', true);
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
    var fltBtn = mBtn('滤镜', true);
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
    var dlBtn = mBtn('下载', true);
    var mDl = document.createElement('div');
    mDl.className = 'mvt-menu';
    /* 优化：把真正能用的 yt-dlp 路径放到最前并标推荐，B站会出垃圾的①降级标注 */
    mDl.appendChild(mItem('① 本地下载脚本（推荐·yt-dlp）', function () { genDownBat(); }));
    mDl.appendChild(mItem('② 通用下载脚本（粘链接）', function () { genDownBatGeneric(); }));
    mDl.appendChild(mItem('③ 智能下载（部分站点）', function () { downloadVideo(); }));
    mDl.appendChild(mItem('④ 分片合并（仅部分站点）', function () { segDownload(); }));
    mDl.appendChild(mItem('⑤ 边播边录（兜底·慢）', function () { mergeRecord(cur); }));
    mDl.appendChild(mItem('⑥ 片段下载（整段下完再剪）', function () { genSegBat(); }));
    mDl.appendChild(mSep());
    mDl.appendChild(mItem('分片状态', function () { reportSeg(); }));
    mDl.appendChild(mItem('清空分片缓存', function () {
      CAP.items = []; CAP.bytes = 0; CAP.seq = 0; CAP.overflow = false;
      toast('分片缓存已清空');
    }));
    dlBtn.appendChild(mDl);
    bar.appendChild(dlBtn);

    /* --- 工具 --- */
    var toolBtn = mBtn('工具', true);
    var mTool = document.createElement('div');
    mTool.className = 'mvt-menu';
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

    document.body.appendChild(bar);
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
    if (cur) {
      var r = cur.getBoundingClientRect();
      left = r.right - bar.offsetWidth - 8;
    } else {
      left = 40;
    }
    bar.style.left = Math.max(8, Math.min(left, window.innerWidth - bar.offsetWidth - 8)) + 'px';
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
