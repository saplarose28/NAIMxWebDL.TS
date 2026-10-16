#!/usr/bin/env python3
"""Direct MPEG-TS recorder with bounded 30s rolling buffer and Telegram controls.

Important: the local rolling buffer can replay only bytes already received.
It cannot recover bytes the source server never sent. True 30s catch-up requires
a source URL with DVR/rewind support or a documented way to request an earlier
time window.
"""
from __future__ import annotations
import os, sys, time, queue, logging, threading
from pathlib import Path
from collections import deque
from datetime import datetime, timezone
import requests

TS_PACKET = 188
STREAM_URL = os.getenv("STREAM_URL", "").strip()
BOT_TOKEN = os.getenv("TELEGRAM_BOT_TOKEN", "").strip()
CHAT_ID = os.getenv("TELEGRAM_CHAT_ID", "").strip()
PART_SIZE_GB = max(1, int(os.getenv("PART_SIZE_GB", "4")))
PART_BYTES = PART_SIZE_GB * 1024**3
MAX_RUNTIME_MINUTES = max(1, int(os.getenv("MAX_RUNTIME_MINUTES", "350")))
AUTO_RECONNECT = os.getenv("AUTO_RECONNECT", "true").lower() == "true"
UPLOAD_TO_GOFILE = os.getenv("UPLOAD_TO_GOFILE", "true").lower() == "true"
CONNECT_TIMEOUT = max(5, int(os.getenv("CONNECT_TIMEOUT_SECONDS", "20")))
READ_TIMEOUT = max(30, int(os.getenv("READ_TIMEOUT_SECONDS", "180")))
RECONNECT_LIMIT = max(0, int(os.getenv("MAX_RECONNECTS", "0")))  # 0 = runtime-limited
BUFFER_SECONDS = max(0, int(os.getenv("ROLLING_BUFFER_SECONDS", "30")))
# Bound memory use. If stream bitrate exceeds this cap, oldest buffered data is discarded.
BUFFER_MAX_MB = max(16, int(os.getenv("BUFFER_MAX_MB", "128")))
BUFFER_MAX_BYTES = BUFFER_MAX_MB * 1024 * 1024
CHUNK_SIZE = 16 * 1024
OUT_DIR = Path("recordings")
OUT_DIR.mkdir(exist_ok=True)

logging.basicConfig(level=logging.INFO,
    format="%(asctime)s %(levelname)s %(message)s",
    handlers=[logging.StreamHandler(sys.stdout), logging.FileHandler("recorder.log", encoding="utf-8")])
log = logging.getLogger("recorder")

http = requests.Session()
http.headers.update({
    "User-Agent": os.getenv("STREAM_USER_AGENT", "VLC/3.0.20 LibVLC/3.0.20"),
    "Accept": "*/*",
    "Connection": "keep-alive",
    "Icy-MetaData": "0",
})
tg_http = requests.Session()
stop_event = threading.Event()
split_event = threading.Event()
state_lock = threading.Lock()
buffer_lock = threading.Lock()
# deque of received chunks and monotonic timestamps; capped by both time and bytes.
rolling_buffer = deque()
rolling_bytes = 0
state = {"recording": False, "started": None, "bytes": 0, "parts": 0,
         "last_error": "", "current_file": "", "reconnects": 0, "buffer_bytes": 0}
upload_queue: queue.Queue[Path | None] = queue.Queue()

def tg(method, payload=None):
    if not BOT_TOKEN:
        return None
    r = tg_http.post(f"https://api.telegram.org/bot{BOT_TOKEN}/{method}",
                     json=payload or {}, timeout=20)
    r.raise_for_status()
    data = r.json()
    if not data.get("ok"):
        raise RuntimeError(str(data))
    return data.get("result")

def send(text, keyboard=True):
    if not BOT_TOKEN or not CHAT_ID:
        log.info("Telegram: %s", text)
        return
    payload = {"chat_id": CHAT_ID, "text": text, "disable_web_page_preview": True}
    if keyboard:
        payload["reply_markup"] = {"inline_keyboard": [
            [{"text":"📊 Status","callback_data":"status"},{"text":"✂️ Split now","callback_data":"split"}],
            [{"text":"🛑 Stop","callback_data":"stop"}]]}
    try: tg("sendMessage", payload)
    except Exception as e: log.warning("Telegram send failed: %s", e)

def answer_callback(cid):
    try: tg("answerCallbackQuery", {"callback_query_id": cid})
    except Exception as e: log.warning("Stale callback ignored: %s", e)

def human(n):
    x=float(n)
    for u in ("B","KB","MB","GB","TB"):
        if x < 1024 or u == "TB": return f"{x:.1f} {u}"
        x /= 1024

def status_text():
    with state_lock:
        start=state["started"]
        elapsed=int(time.time()-start) if start else 0
        return (f"Recording: {'yes' if state['recording'] else 'no'}\n"
                f"Elapsed: {elapsed//3600:02d}:{elapsed%3600//60:02d}:{elapsed%60:02d}\n"
                f"Received: {human(state['bytes'])}\nParts closed: {state['parts']}\n"
                f"Reconnects: {state['reconnects']}\n"
                f"Rolling buffer: {human(state['buffer_bytes'])} (max {BUFFER_SECONDS}s / {BUFFER_MAX_MB} MiB)\n"
                f"Current part: {Path(state['current_file']).name if state['current_file'] else '-'}\n"
                f"Last error: {state['last_error'] or '-'}")

def add_buffer(data):
    global rolling_bytes
    if BUFFER_SECONDS <= 0: return
    now=time.monotonic()
    with buffer_lock:
        rolling_buffer.append((now, data))
        rolling_bytes += len(data)
        while rolling_buffer and (now-rolling_buffer[0][0] > BUFFER_SECONDS or rolling_bytes > BUFFER_MAX_BYTES):
            _, old=rolling_buffer.popleft()
            rolling_bytes -= len(old)
        with state_lock:
            state["buffer_bytes"] = rolling_bytes

def get_buffer_snapshot():
    with buffer_lock:
        return [chunk for _, chunk in rolling_buffer]

def upload_file(path):
    try:
        with path.open("rb") as f:
            r=requests.post("https://upload.gofile.io/uploadfile",
                files={"file":(path.name,f,"video/mp2t")}, timeout=(30,900))
        r.raise_for_status()
        data=r.json()
        if data.get("status") != "ok": raise RuntimeError(str(data))
        link=data.get("data",{}).get("downloadPage","(no link)")
        send(f"✅ Uploaded {path.name}\n{link}", False)
        log.info("Upload complete: %s %s", path.name, link)
    except Exception as e:
        log.exception("Gofile upload failed for %s", path)
        send(f"⚠️ Upload failed: {path.name}: {e}", False)
    finally:
        upload_queue.task_done()

def uploader():
    while True:
        p=upload_queue.get()
        if p is None:
            upload_queue.task_done()
            return
        if UPLOAD_TO_GOFILE: upload_file(p)
        else: upload_queue.task_done()

def new_path(index):
    stamp=datetime.now(timezone.utc).strftime("%Y%m%d_%H%M%S")
    return OUT_DIR/f"recording_{stamp}_part{index:03d}.ts"

def record():
    if not STREAM_URL: raise SystemExit("STREAM_URL is required")
    start=time.monotonic()
    reconnects=0
    index=0
    f=None; path=None; part_size=0
    tsbuf=bytearray()
    last_logged=0

    with state_lock:
        state.update(recording=True, started=time.time(), bytes=0, parts=0,
                     reconnects=0, last_error="", current_file="")

    def close_part():
        nonlocal f, path, part_size
        if f:
            f.flush(); f.close(); f=None
            if path and part_size:
                log.info("Closed part %s (%s)", path, human(part_size))
                upload_queue.put(path)
                with state_lock: state["parts"] += 1
            path=None; part_size=0

    def write_packet(pkt):
        nonlocal f, path, part_size, index
        if f is None or part_size + len(pkt) > PART_BYTES or split_event.is_set():
            close_part()
            split_event.clear()
            index += 1
            path=new_path(index)
            f=path.open("wb")
            with state_lock: state["current_file"]=str(path)
            log.info("Opened part %s", path)
        f.write(pkt)
        part_size += len(pkt)
        with state_lock: state["bytes"] += len(pkt)

    try:
        while not stop_event.is_set() and time.monotonic()-start < MAX_RUNTIME_MINUTES*60:
            response=None
            try:
                log.info("Connecting attempt %d to %s", reconnects+1, STREAM_URL.split("?",1)[0])
                response=http.get(STREAM_URL, stream=True,
                    timeout=(CONNECT_TIMEOUT, READ_TIMEOUT), allow_redirects=True)
                response.raise_for_status()
                ctype=response.headers.get("Content-Type","")
                log.info("Connected HTTP %s; Content-Type=%s; final URL=%s",
                         response.status_code, ctype, response.url.split("?",1)[0])
                if "text/html" in ctype.lower():
                    raise RuntimeError("Server returned HTML, not MPEG-TS")
                # Do not close a part on disconnect. Continue writing to same file after reconnect.
                for chunk in response.iter_content(chunk_size=CHUNK_SIZE):
                    if stop_event.is_set() or time.monotonic()-start >= MAX_RUNTIME_MINUTES*60: break
                    if not chunk: continue
                    add_buffer(chunk)
                    tsbuf.extend(chunk)
                    while len(tsbuf) >= TS_PACKET*2:
                        if tsbuf[0] == 0x47 and tsbuf[TS_PACKET] == 0x47:
                            write_packet(bytes(tsbuf[:TS_PACKET]))
                            del tsbuf[:TS_PACKET]
                        else:
                            found=-1
                            scan_end=len(tsbuf)-TS_PACKET*2
                            for i in range(1, max(1,scan_end+1)):
                                if tsbuf[i] == 0x47 and tsbuf[i+TS_PACKET] == 0x47:
                                    found=i; break
                            if found >= 0: del tsbuf[:found]
                            else:
                                keep=TS_PACKET*2-1
                                if len(tsbuf)>keep: del tsbuf[:-keep]
                                break
                if stop_event.is_set() or time.monotonic()-start >= MAX_RUNTIME_MINUTES*60: break
                raise ConnectionError("Server closed stream response (EOF)")
            except Exception as e:
                msg=f"{type(e).__name__}: {e}"
                with state_lock:
                    state["last_error"]=msg[:300]
                    state["reconnects"]=reconnects+1
                log.warning("Stream failure: %s", msg)
                if not AUTO_RECONNECT:
                    log.error("AUTO_RECONNECT=false; ending")
                    break
                reconnects += 1
                if RECONNECT_LIMIT and reconnects > RECONNECT_LIMIT:
                    log.error("Reconnect limit reached")
                    break
                wait=min(30, 2**min(reconnects,5))
                log.info("Reconnecting in %ss; keeping current output part open", wait)
                stop_event.wait(wait)
            finally:
                if response is not None: response.close()
        # Never claim missing bytes were recovered. The local buffer is diagnostic/short replay only.
        close_part()
    finally:
        with state_lock:
            state["recording"]=False
            state["current_file"]=""
        upload_queue.join()
        send("⏹️ Recording finished.\n"+status_text(), False)

def telegram_loop():
    offset=0
    while not stop_event.is_set() or state["recording"]:
        try:
            updates=tg("getUpdates", {"offset":offset,"timeout":20,
                "allowed_updates":["message","callback_query"]}) or []
            for u in updates:
                offset=max(offset,u["update_id"]+1)
                cb=u.get("callback_query")
                if cb:
                    answer_callback(cb.get("id",""))
                    if str(cb.get("message",{}).get("chat",{}).get("id")) != CHAT_ID: continue
                    action=cb.get("data","")
                else:
                    m=u.get("message",{})
                    if str(m.get("chat",{}).get("id")) != CHAT_ID: continue
                    action=m.get("text","").strip().lower().lstrip("/")
                if action in ("start","status"): send(status_text())
                elif action=="split":
                    split_event.set(); send("✂️ Split requested; next valid TS packet starts a new part.",False)
                elif action=="stop":
                    stop_event.set(); send("🛑 Stop requested.",False)
        except Exception as e:
            log.warning("Telegram polling failed: %s", e)
            stop_event.wait(3)

def main():
    if not STREAM_URL: raise SystemExit("Set STREAM_URL in workflow inputs")
    if UPLOAD_TO_GOFILE: threading.Thread(target=uploader,daemon=True).start()
    if BOT_TOKEN and CHAT_ID:
        send(f"▶️ Recorder started\nPart target: {PART_SIZE_GB} GiB\n"
             f"Runtime: {MAX_RUNTIME_MINUTES} min\nReconnect: {AUTO_RECONNECT}\n"
             f"Rolling buffer: {BUFFER_SECONDS}s (local only; does not fetch missing server data)\n"
             f"Gofile upload: {UPLOAD_TO_GOFILE}")
        threading.Thread(target=telegram_loop,daemon=True).start()
    else: log.warning("Telegram controls disabled: missing bot token/chat ID")
    try: record()
    finally:
        stop_event.set()
        if UPLOAD_TO_GOFILE:
            upload_queue.put(None)
            upload_queue.join()

if __name__=="__main__": main()
