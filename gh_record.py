#!/usr/bin/env python3
"""Telegram-controlled MPEG-TS recorder for GitHub Actions."""
from __future__ import annotations

import os
import sys
import time
import queue
import logging
import threading
from pathlib import Path
from datetime import datetime, timezone

import requests

TS_PACKET = 188
OUT_DIR = Path(os.getenv("OUTPUT_DIR", "recordings"))
OUT_DIR.mkdir(parents=True, exist_ok=True)

STREAM_URL = os.getenv("STREAM_URL", "").strip()
BOT_TOKEN = os.getenv("TELEGRAM_BOT_TOKEN", "").strip()
CHAT_ID = os.getenv("TELEGRAM_CHAT_ID", "").strip()
PART_SIZE_GB = max(1, int(os.getenv("PART_SIZE_GB", "4")))
PART_BYTES = PART_SIZE_GB * 1024**3
MAX_RUNTIME_MINUTES = max(1, int(os.getenv("MAX_RUNTIME_MINUTES", "350")))
AUTO_RECONNECT = os.getenv("AUTO_RECONNECT", "true").lower() == "true"
UPLOAD_TO_GOFILE = os.getenv("UPLOAD_TO_GOFILE", "true").lower() == "true"
CONNECT_TIMEOUT = max(5, int(os.getenv("CONNECT_TIMEOUT_SECONDS", "20")))
READ_TIMEOUT = max(15, int(os.getenv("READ_TIMEOUT_SECONDS", "90")))
MAX_RECONNECTS = max(0, int(os.getenv("MAX_RECONNECTS", "0")))  # 0 = unlimited, bounded by runtime

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s %(levelname)s %(message)s",
    handlers=[logging.StreamHandler(sys.stdout), logging.FileHandler("recorder.log", encoding="utf-8")],
)
log = logging.getLogger("recorder")

session = requests.Session()
session.headers.update({
    "User-Agent": os.getenv("STREAM_USER_AGENT", "VLC/3.0.20 LibVLC/3.0.20"),
    "Accept": "*/*",
    "Connection": "keep-alive",
    "Icy-MetaData": "0",
})

stop_event = threading.Event()
split_event = threading.Event()
state_lock = threading.Lock()
state = {
    "recording": False,
    "stopping": False,
    "started": None,
    "bytes": 0,
    "parts": 0,
    "last_error": "",
    "current_file": "",
}
upload_queue: queue.Queue[Path | None] = queue.Queue()
telegram_session = requests.Session()
telegram_offset = 0


def telegram(method: str, payload: dict | None = None):
    if not BOT_TOKEN:
        return None
    url = f"https://api.telegram.org/bot{BOT_TOKEN}/{method}"
    response = telegram_session.post(url, json=payload or {}, timeout=20)
    response.raise_for_status()
    data = response.json()
    if not data.get("ok"):
        raise RuntimeError(f"Telegram API error: {data}")
    return data.get("result")


def send_message(text: str, keyboard: bool = True):
    if not BOT_TOKEN or not CHAT_ID:
        log.info("Telegram not configured; message: %s", text)
        return
    payload = {"chat_id": CHAT_ID, "text": text, "disable_web_page_preview": True}
    if keyboard:
        payload["reply_markup"] = {
            "inline_keyboard": [
                [{"text": "📊 Status", "callback_data": "status"},
                 {"text": "✂️ Split now", "callback_data": "split"}],
                [{"text": "🛑 Stop recording", "callback_data": "stop"}],
            ]
        }
    try:
        telegram("sendMessage", payload)
    except Exception as exc:
        log.warning("Telegram sendMessage failed: %s", exc)


def answer_callback(callback_id: str, text: str = ""):
    # Telegram callback IDs can expire; never let that crash the recorder.
    try:
        telegram("answerCallbackQuery", {"callback_query_id": callback_id, "text": text[:180]})
    except Exception as exc:
        log.warning("Callback acknowledgement failed (usually stale callback): %s", exc)


def fmt_bytes(n: int) -> str:
    units = ("B", "KB", "MB", "GB", "TB")
    value = float(n)
    for unit in units:
        if value < 1024 or unit == units[-1]:
            return f"{value:.2f} {unit}"
        value /= 1024
    return f"{n} B"


def status_text() -> str:
    with state_lock:
        started = state["started"]
        elapsed = int(time.time() - started) if started else 0
        return (
            f"Recording: {'yes' if state['recording'] else 'no'}\n"
            f"Elapsed: {elapsed // 3600:02d}:{(elapsed % 3600) // 60:02d}:{elapsed % 60:02d}\n"
            f"Data received: {fmt_bytes(state['bytes'])}\n"
            f"Parts closed: {state['parts']}\n"
            f"Current file: {Path(state['current_file']).name if state['current_file'] else '-'}\n"
            f"Last stream error: {state['last_error'] or '-'}"
        )


def gofile_upload(path: Path):
    if not UPLOAD_TO_GOFILE:
        log.info("Gofile upload disabled; keeping %s locally", path)
        return
    try:
        # Gofile's public upload endpoint accepts multipart file uploads.
        with path.open("rb") as f:
            response = requests.post(
                "https://upload.gofile.io/uploadfile",
                files={"file": (path.name, f, "video/mp2t")},
                timeout=(30, 900),
            )
        response.raise_for_status()
        data = response.json()
        if data.get("status") != "ok":
            raise RuntimeError(f"Gofile returned: {data}")
        info = data.get("data", {})
        link = info.get("downloadPage") or info.get("directLink") or "(no link returned)"
        send_message(f"✅ Upload complete: {path.name}\n{link}", keyboard=False)
        log.info("Uploaded %s: %s", path.name, link)
    except Exception as exc:
        log.exception("Gofile upload failed for %s", path.name)
        send_message(f"⚠️ Gofile upload failed for {path.name}: {exc}", keyboard=False)
    finally:
        upload_queue.task_done()


def upload_worker():
    while True:
        path = upload_queue.get()
        if path is None:
            upload_queue.task_done()
            return
        gofile_upload(path)


def open_part(index: int):
    stamp = datetime.now(timezone.utc).strftime("%Y%m%d_%H%M%S")
    return OUT_DIR / f"recording_{stamp}_part{index:03d}.ts"


def record_stream():
    if not STREAM_URL:
        raise RuntimeError("STREAM_URL is empty")
    started_at = time.monotonic()
    reconnects = 0
    part_index = 0
    current = None
    current_path = None
    current_size = 0
    buffer = bytearray()
    last_notice = 0.0

    with state_lock:
        state.update(recording=True, stopping=False, started=time.time(), bytes=0, parts=0,
                     last_error="", current_file="")

    def close_part():
        nonlocal current, current_path, current_size
        if current:
            current.flush()
            current.close()
            current = None
            if current_path and current_size:
                log.info("Closed part %s (%s)", current_path, fmt_bytes(current_size))
                upload_queue.put(current_path)
                with state_lock:
                    state["parts"] += 1
            current_path = None
            current_size = 0

    def write_packet(packet: bytes):
        nonlocal current, current_path, current_size, part_index
        if current is None or current_size + len(packet) > PART_BYTES or split_event.is_set():
            close_part()
            split_event.clear()
            part_index += 1
            current_path = open_part(part_index)
            current = current_path.open("wb")
            with state_lock:
                state["current_file"] = str(current_path)
            log.info("Opened part %s", current_path)
        current.write(packet)
        current_size += len(packet)
        with state_lock:
            state["bytes"] += len(packet)

    try:
        while not stop_event.is_set():
            if time.monotonic() - started_at >= MAX_RUNTIME_MINUTES * 60:
                log.info("Maximum runtime reached")
                break
            response = None
            try:
                log.info("Connecting to stream (attempt %d): %s", reconnects + 1,
                         STREAM_URL.split("?", 1)[0])
                response = session.get(
                    STREAM_URL,
                    stream=True,
                    timeout=(CONNECT_TIMEOUT, READ_TIMEOUT),
                    allow_redirects=True,
                )
                response.raise_for_status()
                content_type = response.headers.get("Content-Type", "")
                log.info("Connected: HTTP %s, Content-Type=%s", response.status_code, content_type)
                if "text/html" in content_type.lower():
                    raise RuntimeError("Server returned HTML, not a raw MPEG-TS stream (possibly an expired/incorrect URL)")
                buffer.clear()
                for chunk in response.iter_content(chunk_size=64 * 1024):
                    if stop_event.is_set():
                        break
                    if time.monotonic() - started_at >= MAX_RUNTIME_MINUTES * 60:
                        break
                    if not chunk:
                        continue
                    buffer.extend(chunk)
                    # Align to MPEG-TS packet boundaries. Keep enough bytes to confirm the next sync byte.
                    while len(buffer) >= TS_PACKET * 2:
                        if buffer[0] == 0x47 and buffer[TS_PACKET] == 0x47:
                            packet = bytes(buffer[:TS_PACKET])
                            del buffer[:TS_PACKET]
                            write_packet(packet)
                        else:
                            max_scan = max(0, len(buffer) - TS_PACKET * 2)
                            found = -1
                            for i in range(1, max_scan + 1):
                                if buffer[i] == 0x47 and buffer[i + TS_PACKET] == 0x47:
                                    found = i
                                    break
                            if found >= 0:
                                del buffer[:found]
                            else:
                                # Preserve enough bytes for a possible sync pair split across chunks.
                                del buffer[:max(0, len(buffer) - TS_PACKET * 2 + 1)]
                                break
                if stop_event.is_set():
                    break
                if time.monotonic() - started_at >= MAX_RUNTIME_MINUTES * 60:
                    break
                raise ConnectionError("Stream ended (server closed the response)")
            except Exception as exc:
                msg = f"{type(exc).__name__}: {exc}"
                with state_lock:
                    state["last_error"] = msg[:300]
                log.warning("Stream connection failed: %s", msg)
                close_part()
                if not AUTO_RECONNECT:
                    log.error("AUTO_RECONNECT=false; stopping after stream failure")
                    break
                reconnects += 1
                if MAX_RECONNECTS and reconnects > MAX_RECONNECTS:
                    log.error("MAX_RECONNECTS limit reached")
                    break
                wait = min(30, 2 ** min(reconnects, 5))
                log.info("Reconnecting in %s seconds", wait)
                # Interruptible wait so Telegram Stop works immediately.
                stop_event.wait(wait)
            finally:
                if response is not None:
                    response.close()
        close_part()
    finally:
        with state_lock:
            state["recording"] = False
            state["stopping"] = False
            state["current_file"] = ""
        upload_queue.join()
        send_message("⏹️ Recording finished.\n" + status_text(), keyboard=False)


def telegram_loop():
    global telegram_offset
    if not BOT_TOKEN:
        log.warning("TELEGRAM_BOT_TOKEN is not configured; Telegram controls disabled")
        return
    while not stop_event.is_set() or state["recording"]:
        try:
            updates = telegram("getUpdates", {
                "offset": telegram_offset,
                "timeout": 20,
                "allowed_updates": ["message", "callback_query"],
            }) or []
            for update in updates:
                telegram_offset = max(telegram_offset, update["update_id"] + 1)
                callback = update.get("callback_query")
                if callback:
                    answer_callback(callback.get("id", ""))
                    data = callback.get("data", "")
                    if callback.get("message", {}).get("chat", {}).get("id") != int(CHAT_ID or "0"):
                        continue
                    if data == "status":
                        send_message(status_text(), keyboard=True)
                    elif data == "split":
                        split_event.set()
                        send_message("✂️ Split requested. A new part will start at the next valid TS packet.", keyboard=False)
                    elif data == "stop":
                        stop_event.set()
                        send_message("🛑 Stop requested; closing the current part safely.", keyboard=False)
                message = update.get("message")
                if message and str(message.get("chat", {}).get("id")) == CHAT_ID:
                    text = message.get("text", "").strip().lower()
                    if text in ("/status", "/start"):
                        send_message(status_text(), keyboard=True)
                    elif text == "/split":
                        split_event.set()
                        send_message("✂️ Split requested.", keyboard=False)
                    elif text == "/stop":
                        stop_event.set()
                        send_message("🛑 Stop requested.", keyboard=False)
        except requests.RequestException as exc:
            log.warning("Telegram polling network error: %s", exc)
            stop_event.wait(3)
        except Exception as exc:
            log.exception("Telegram polling error: %s", exc)
            stop_event.wait(3)


def main():
    if not STREAM_URL:
        raise SystemExit("Set STREAM_URL in the workflow inputs.")
    if UPLOAD_TO_GOFILE:
        threading.Thread(target=upload_worker, name="gofile-uploader", daemon=True).start()
    if BOT_TOKEN and CHAT_ID:
        send_message(
            f"▶️ Recorder started\nPart size: {PART_SIZE_GB} GiB\n"
            f"Max runtime: {MAX_RUNTIME_MINUTES} min\nAuto reconnect: {AUTO_RECONNECT}\n"
            f"Gofile upload: {UPLOAD_TO_GOFILE}",
            keyboard=True,
        )
        tg = threading.Thread(target=telegram_loop, name="telegram-poller", daemon=True)
        tg.start()
    else:
        log.warning("Set TELEGRAM_BOT_TOKEN and TELEGRAM_CHAT_ID to enable Telegram controls")

    try:
        record_stream()
    except KeyboardInterrupt:
        stop_event.set()
    finally:
        stop_event.set()
        if UPLOAD_TO_GOFILE:
            upload_queue.put(None)
            upload_queue.join()


if __name__ == "__main__":
    main()
