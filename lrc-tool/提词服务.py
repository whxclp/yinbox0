# -*- coding: utf-8 -*-
"""歌词配轴工具的本地提词服务

用法：双击「启动提词服务.cmd」，浏览器会自动打开 http://127.0.0.1:8094/
接口：
  GET  /ping            健康检查
  POST /extract?name=x.mp4&fps=1&offset=-1.2   请求体=视频原始字节，返回 {job}
  POST /remux?name=x.webm      请求体=录好的视频字节；ffmpeg 无损重封装补时长，存到桌面
  GET  /job/<id>        查询进度 / 结果
"""
import json, os, sys, tempfile, threading, time, traceback, uuid, webbrowser
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import urlparse, parse_qs

HERE = os.path.dirname(os.path.abspath(__file__))
LOG = os.path.join(HERE, "提词服务_日志.txt")
if sys.stdout is None:            # pythonw 后台启动时没有控制台，输出写日志
    _f = open(LOG, "a", encoding="utf-8", buffering=1)
    sys.stdout = sys.stderr = _f
HTML_NAMES = ["歌词配轴工具.html", "index.html"]
DESKTOP = os.path.join(os.path.expanduser("~"), "Desktop")
EXTRACT_DIR = os.environ.get("LRC_TOOL_DIR", r"C:\Users\whx\Desktop\视频提歌词")
PORT = int(os.environ.get("LRC_PORT", "8094"))

sys.path.insert(0, EXTRACT_DIR)
sys.path.insert(0, HERE)
try:
    import lrc_from_video as ex
except Exception as e:                     # 没装提取器也能起服务，只是接口会报错
    ex = None
    IMPORT_ERR = "%s" % e
else:
    IMPORT_ERR = None

_jobs = {}
_lock = threading.Lock()
_engine = None
_engine_lock = threading.Lock()


def get_engine():
    global _engine
    with _engine_lock:
        if _engine is None:
            import logging
            logging.getLogger().setLevel(logging.ERROR)
            logging.disable(logging.INFO)
            from rapidocr import RapidOCR
            _engine = RapidOCR()
    return _engine


def worker(job_id, path, fps, offset, band, name):
    job = _jobs[job_id]

    def progress(i, n):
        job["done"], job["total"] = i, n

    work = os.path.join(tempfile.gettempdir(), "lrc_jobs", job_id)
    try:
        if ex is None:
            raise RuntimeError("找不到提取器 lrc_from_video.py：%s" % IMPORT_ERR)
        job["phase"] = "抽帧/识别中"
        res = ex.extract_video(path, fps=fps, offset=offset, band=band,
                               progress=progress, engine=get_engine(), workdir=work)
        job["lines"] = res["lines"]
        job["meta"] = {k: res[k] for k in ("title", "duration", "width", "height",
                                          "frames", "band", "dropped")}
        job["meta"]["title"] = os.path.splitext(os.path.basename(name))[0]
        job["status"] = "done"
    except Exception as e:
        job["status"] = "error"
        job["reason"] = str(e) or e.__class__.__name__
        job["error"] = traceback.format_exc()[-1500:]
    finally:
        job["phase"] = "结束"
        for p in (path, work):
            try:
                if os.path.isdir(p):
                    import shutil
                    shutil.rmtree(p, ignore_errors=True)
                elif os.path.exists(p):
                    os.remove(p)
            except Exception:
                pass


class Handler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"
    server_version = "LrcTool/1.0"

    def log_message(self, fmt, *args):
        pass

    def _send(self, code, body, ctype="application/json; charset=utf-8"):
        if isinstance(body, (dict, list)):
            body = json.dumps(body, ensure_ascii=False).encode("utf-8")
        elif isinstance(body, str):
            body = body.encode("utf-8")
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Allow-Headers", "Content-Type")
        self.send_header("Access-Control-Allow-Methods", "GET,POST,OPTIONS")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def do_OPTIONS(self):
        self.send_response(204)
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Allow-Headers", "Content-Type")
        self.send_header("Access-Control-Allow-Methods", "GET,POST,OPTIONS")
        self.send_header("Access-Control-Allow-Private-Network", "true")
        self.send_header("Content-Length", "0")
        self.end_headers()

    def do_GET(self):
        u = urlparse(self.path)
        if u.path == "/ping":
            return self._send(200, {"ok": True, "extractor": ex is not None,
                                    "error": IMPORT_ERR})
        if u.path.startswith("/job/"):
            jid = u.path.split("/")[-1]
            job = _jobs.get(jid)
            if not job:
                return self._send(404, {"error": "没有这个任务"})
            out = {k: job[k] for k in ("status", "done", "total", "phase")}
            if job["status"] == "done":
                out["lines"] = job["lines"]
                out["meta"] = job["meta"]
            elif job["status"] == "error":
                out["error"] = job["error"]
                out["reason"] = job.get("reason") or "识别失败"
            return self._send(200, out)
        # 主页直接给工具本体，保证同源
        for name in HTML_NAMES:
            p = os.path.join(HERE, name)
            if os.path.exists(p):
                body = open(p, "rb").read()
                return self._send(200, body, "text/html; charset=utf-8")
        return self._send(404, "没找到 歌词配轴工具.html，请把它和本服务放同一目录。")

    def do_POST(self):
        u = urlparse(self.path)
        if u.path.startswith("/remux"):
            return self.do_remux(u)
        if not u.path.startswith("/extract"):
            return self._send(404, {"error": "未知接口"})
        qs = parse_qs(u.query)
        name = qs.get("name", ["video.mp4"])[0].replace("\\", "_").replace("/", "_")
        fps = float(qs.get("fps", ["1"])[0] or 1)
        offset = float(qs.get("offset", ["-1.2"])[0] or 0)
        band = qs.get("band", [None])[0]
        band = int(band) if band not in (None, "", "null") else None
        length = int(self.headers.get("Content-Length") or 0)
        if length <= 0:
            return self._send(400, {"error": "没有收到视频数据"})
        ext = os.path.splitext(name)[1] or ".mp4"
        path = os.path.join(tempfile.gettempdir(), "lrc_upload_%s%s" % (uuid.uuid4().hex[:8], ext))
        got = 0
        with open(path, "wb") as f:
            while got < length:
                chunk = self.rfile.read(min(4 << 20, length - got))
                if not chunk:
                    break
                f.write(chunk)
                got += len(chunk)
        if got < length:
            return self._send(400, {"error": "上传中断（%d/%d 字节）" % (got, length)})
        jid = uuid.uuid4().hex[:10]
        _jobs[jid] = {"status": "running", "done": 0, "total": 0, "phase": "排队中",
                     "name": name, "created": time.time()}
        threading.Thread(target=worker, args=(jid, path, fps, offset, band, name),
                         daemon=True).start()
        return self._send(200, {"job": jid})

    def do_remux(self, u):
        """浏览器录出的 webm 没写时长信息，PotPlayer 里会显示不出总长、进度不能拖。
        这里用本机 ffmpeg 无损重封装一次（补时长/索引），直接存到桌面。"""
        qs = parse_qs(u.query)
        name = os.path.basename(qs.get("name", [""])[0]) or "导出视频.webm"
        name = name.replace("\\", "_").replace("/", "_")
        length = int(self.headers.get("Content-Length") or 0)
        if length <= 0:
            return self._send(400, {"error": "没有收到视频数据"})
        ext = os.path.splitext(name)[1].lower() or ".webm"
        tmp = os.path.join(tempfile.gettempdir(), "lrc_remux_%s%s" % (uuid.uuid4().hex[:8], ext))
        got = 0
        with open(tmp, "wb") as f:
            while got < length:
                chunk = self.rfile.read(min(4 << 20, length - got))
                if not chunk:
                    break
                f.write(chunk)
                got += len(chunk)
        if got < length:
            try:
                os.remove(tmp)
            except Exception:
                pass
            return self._send(400, {"error": "上传中断（%d/%d 字节）" % (got, length)})
        try:
            if ex is None:
                raise RuntimeError("提取器未加载：%s" % IMPORT_ERR)
            ex.find_ffmpeg()
            out = os.path.join(DESKTOP, name)
            base, e2 = os.path.splitext(out)
            i = 2
            while os.path.exists(out):
                out = "%s(%d)%s" % (base, i, e2)
                i += 1
            cmd = [ex.FFMPEG or "ffmpeg", "-y", "-loglevel", "error",
                   "-i", tmp, "-c", "copy", "-map", "0"]
            if ext == ".webm":
                cmd += ["-f", "webm"]
            cmd += [out]
            ex._call(cmd, timeout=900, check=True)
            size = os.path.getsize(out)
            dur = 0
            try:
                r = ex._call([ex.FFPROBE or "ffprobe", "-v", "error",
                              "-show_entries", "format=duration", "-of", "json", out], timeout=120)
                dur = round(float(json.loads(r.stdout)["format"]["duration"]), 1)
            except Exception:
                dur = 0
            print("[remux] %s → %s (%d 字节, %s 秒)" % (name, out, size, dur))
            return self._send(200, {"ok": True, "name": os.path.basename(out),
                                    "path": out, "size": size, "duration": dur})
        except Exception as e:
            return self._send(200, {"ok": False, "reason": str(e) or e.__class__.__name__})
        finally:
            try:
                os.remove(tmp)
            except Exception:
                pass


def main():
    port = PORT
    while True:
        try:
            httpd = ThreadingHTTPServer(("127.0.0.1", port), Handler)
            break
        except OSError:
            port += 1
            if port > PORT + 20:
                raise
    print("提词服务已启动： http://127.0.0.1:%d/" % port)
    print("提取器： %s" % ("已加载 " + EXTRACT_DIR if ex else "未找到！" + str(IMPORT_ERR)))
    print("关掉这个窗口就停止服务。")
    if "--open" in sys.argv:
        webbrowser.open("http://127.0.0.1:%d/" % port)
    try:
        httpd.serve_forever()
    except KeyboardInterrupt:
        pass


if __name__ == "__main__":
    main()
