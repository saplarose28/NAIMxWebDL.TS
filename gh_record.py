import os
import time
import queue
import threading
import logging
from pathlib import Path
from datetime import datetime

import requests

# =============== CONFIG ===============
BOT_TOKEN = os.environ["TELEGRAM_BOT_TOKEN"]
CHAT_ID = str(os.environ["TELEGRAM_CHAT_ID"])
STREAM_URL = os.environ["STREAM_URL"]

PART_SIZE = 4 * 1024**3
TS_PACKET_SIZE = 188
MAX_PART_BYTES = (PART_SIZE // TS_PACKET_SIZE) * TS_PACKET_SIZE

OUTPUT_DIR = Path("recordings")
OUTPUT_DIR.mkdir(exist_ok=True)

GOFILE_URL = "https://upload.gofile.io/uploadfile"
MAX_RECONNECTS = 10

# =============== LOGGING ===============
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s | %(levelname)s | %(message)s",
    handlers=[
        logging.StreamHandler(),
        logging.FileHandler("recorder.log", encoding="utf-8")
    ]
)
log = logging.getLogger("recorder")

# =============== STATE ===============
stop_event = threading.Event()
split_event = threading.Event()
upload_queue = queue.Queue()
state_lock = threading.Lock()

state = {
    "connected": False,
    "current_file": "",
    "current_size": 0,
    "parts": 0,
    "bytes_received": 0,
    "last_error": "None",
    "started": time.time(),
}

telegram_session = requests.Session()
http_session = requests.Session()


def telegram(method, payload=None, timeout=15):
    response = telegram_session.post(
        f"https://api.telegram.org/bot{BOT_TOKEN}/{method}",
        json=payload or {},
        timeout=timeout
    )
    response.raise_for_status()
    result = response.json()

    if not result.get("ok"):
        raise RuntimeError(result.get("description", "Telegram API error"))

    return result["result"]


def send_message(text, keyboard=True):
    markup = None

    if keyboard:
        markup = {
            "inline_keyboard": [
                [
                    {"text": "📊 Status", "callback_data": "status"},
                    {"text": "✂️ Split now", "callback_data": "split"}
                ],
                [
                    {"text": "⏹ Stop & upload", "callback_data": "stop"}
                ]
            ]
        }

    try:
        telegram("sendMessage", {
            "chat_id": CHAT_ID,
            "text": text,
            "reply_markup": markup,
            "disable_web_page_preview": True
        })
    except Exception as exc:
        log.error("Telegram message failed: %s", exc)


def authorized(chat_id):
    return str(chat_id) == CHAT_ID


def format_bytes(number):
    number = float(number)
    for unit in ("B", "KB", "MB", "GB", "TB"):
        if number < 1024 or unit == "TB":
            return f"{number:.2f} {unit}"
        number /= 1024


def status_text():
    with state_lock:
        info = state.copy()

    elapsed = int(time.time() - info["started"])
    minutes, seconds = divmod(elapsed, 60)

    return (
        "📡 MPEG-TS RECORDER\n"
        "━━━━━━━━━━━━━━━━━━\n"
        f"Connection: {'🟢 Connected' if info['connected'] else '🟠 Reconnecting / waiting'}\n"
        f"Current file: {Path(info['current_file']).name if info['current_file'] else '—'}\n"
        f"Current size: {format_bytes(info['current_size'])}\n"
        f"Part limit: approximately {format_bytes(MAX_PART_BYTES)}\n"
        f"Completed parts: {info['parts']}\n"
        f"Data written: {format_bytes(info['bytes_received'])}\n"
        f"Uptime: {minutes}m {seconds}s\n"
        f"Last error: {info['last_error'][:250]}\n"
        "━━━━━━━━━━━━━━━━━━"
    )


def new_part():
    stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    path = OUTPUT_DIR / f"record_{stamp}_{time.time_ns() % 1000000:06d}.ts"
    handle = open(path, "wb")

    with state_lock:
        state["current_file"] = str(path)
        state["current_size"] = 0
        state["parts"] += 1

    log.info("Created new part: %s", path.name)
    return path, handle, 0


def finish_part(path, handle, size):
    handle.close()

    if size > 0:
        upload_queue.put(path)
        log.info("Part completed: %s (%s)", path.name, format_bytes(size))
        send_message(
            "📦 PART COMPLETED\n"
            f"File: {path.name}\n"
            f"Size: {format_bytes(size)}\n"
            "⬆️ Added to upload queue."
        )


def find_ts_packets(buffer):
    """Yield aligned 188-byte TS packets from an HTTP byte stream."""
    while len(buffer) >= TS_PACKET_SIZE:
        if buffer[0] != 0x47:
            idx = buffer.find(b"\x47")

            if idx < 0:
                del buffer[:-TS_PACKET_SIZE]
                return

            if len(buffer) < idx + TS_PACKET_SIZE + 1:
                del buffer[:idx]
                return

            if buffer[idx + TS_PACKET_SIZE] != 0x47:
                del buffer[:idx + 1]
                continue

            del buffer[:idx]

        if len(buffer) >= TS_PACKET_SIZE and buffer[0] == 0x47:
            packet = bytes(buffer[:TS_PACKET_SIZE])
            del buffer[:TS_PACKET_SIZE]
            yield packet


def record_stream():
    path, handle, size = new_part()
    reconnects = 0
    last_packet_time = time.time()
    buffer = bytearray()

    while not stop_event.is_set():
        response = None

        try:
            log.info("Connecting to MPEG-TS stream")

            response = http_session.get(
                STREAM_URL,
                stream=True,
                headers={"User-Agent": "Mozilla/5.0 MPEGTS-Recorder/1.0"},
                timeout=(15, 60)
            )
            response.raise_for_status()

            with state_lock:
                state["connected"] = True
                state["last_error"] = "None"

            send_message("🟢 Stream connected. Recording is active.")

            for chunk in response.iter_content(chunk_size=64 * 1024):
                if stop_event.is_set():
                    break

                if not chunk:
                    continue

                buffer.extend(chunk)

                for packet in find_ts_packets(buffer):
                    if stop_event.is_set():
                        break

                    if split_event.is_set() and size > 0:
                        finish_part(path, handle, size)
                        path, handle, size = new_part()
                        split_event.clear()
                        send_message("✂️ Manual split complete. New part started.")

                    if size + len(packet) > MAX_PART_BYTES:
                        finish_part(path, handle, size)
                        path, handle, size = new_part()

                    handle.write(packet)
                    size += len(packet)
                    last_packet_time = time.time()

                    with state_lock:
                        state["current_size"] = size
                        state["bytes_received"] += len(packet)

                    if size >= MAX_PART_BYTES:
                        finish_part(path, handle, size)
                        path, handle, size = new_part()

            if stop_event.is_set():
                break

            raise ConnectionError("Stream ended; reconnecting")

        except Exception as exc:
            log.warning("Stream error: %s", exc)

            with state_lock:
                state["connected"] = False
                state["last_error"] = str(exc)

            # Discard incomplete packet bytes before reconnecting.
            buffer.clear()

            if time.time() - last_packet_time > 10:
                reconnects += 1

            if reconnects > MAX_RECONNECTS:
                send_message(
                    "🔴 Stream failed repeatedly.\n"
                    "Automatic reconnect limit reached.\n"
                    "Check the URL and recorder.log."
                )
                stop_event.set()
                break

            delay = min(2 ** min(reconnects, 5), 30)
            send_message(
                f"🔄 Stream disconnected.\n"
                f"Retry: {reconnects}/{MAX_RECONNECTS}\n"
                f"Next attempt in {delay}s."
            )
            stop_event.wait(delay)

        finally:
            if response is not None:
                response.close()

    try:
        if size > 0:
            finish_part(path, handle, size)
        else:
            handle.close()
            path.unlink(missing_ok=True)
    except Exception:
        log.exception("Failed to finalize current part")


def upload_one(path):
    if not path.exists() or path.stat().st_size == 0:
        return True

    for attempt in range(1, 4):
        try:
            send_message(
                "⬆️ UPLOAD STARTED\n"
                f"File: {path.name}\n"
                f"Size: {format_bytes(path.stat().st_size)}\n"
                f"Attempt: {attempt}/3",
                keyboard=False
            )

            with path.open("rb") as file_obj:
                response = requests.post(
                    GOFILE_URL,
                    files={"file": (path.name, file_obj, "video/mp2t")},
                    timeout=(30, 3600)
                )

            response.raise_for_status()
            result = response.json()

            if result.get("status") != "ok":
                raise RuntimeError(str(result))

            data = result.get("data", {})
            link = data.get("downloadPage", "Link unavailable")

            send_message(
                "✅ UPLOAD SUCCESSFUL\n"
                f"📁 {path.name}\n"
                f"💾 {format_bytes(path.stat().st_size)}\n"
                f"🔗 {link}"
            )

            path.unlink(missing_ok=True)
            return True

        except Exception as exc:
            log.exception("Upload failed: %s", path.name)
            with state_lock:
                state["last_error"] = f"Upload: {exc}"

            if attempt < 3:
                time.sleep(attempt * 5)

    send_message(
        "❌ UPLOAD FAILED\n"
        f"File: {path.name}\n"
        "The local file was kept for recovery."
    )
    return False


def upload_worker():
    while True:
        item = upload_queue.get()

        try:
            if item is None:
                return
            upload_one(item)
        finally:
            upload_queue.task_done()


def handle_action(action):
    if action == "status":
        send_message(status_text())

    elif action == "split":
        split_event.set()
        send_message(
            "✂️ SPLIT REQUESTED\n"
            "The current part will close at the next TS packet, "
            "then a new file will start."
        )

    elif action == "stop":
        send_message("⏹ STOP REQUESTED\nFinalizing the current file and uploads.")
        stop_event.set()


def poll_telegram(offset):
    updates = telegram("getUpdates", {
        "offset": offset,
        "timeout": 2,
        "allowed_updates": ["message", "callback_query"]
    }, timeout=8)

    for update in updates:
        offset = update["update_id"] + 1

        try:
            callback = update.get("callback_query")

            if callback:
                message = callback.get("message", {})
                chat_id = message.get("chat", {}).get("id")

                telegram("answerCallbackQuery", {
                    "callback_query_id": callback["id"]
                })

                if authorized(chat_id):
                    handle_action(callback.get("data", ""))
                continue

            message = update.get("message", {})
            chat_id = message.get("chat", {}).get("id")

            if not authorized(chat_id):
                continue

            command = message.get("text", "").strip().lower()

            if command in ("/start", "/help"):
                send_message(
                    "🎬 MPEG-TS RECORDER\n"
                    "━━━━━━━━━━━━━━━━━━\n"
                    "/status — Show recorder status\n"
                    "/split — Close current part and start another\n"
                    "/stop — Stop recording and upload remaining data\n"
                    "━━━━━━━━━━━━━━━━━━\n"
                    "📦 Part limit: approximately 4 GiB\n"
                    "☁️ Completed parts upload automatically."
                )

            elif command == "/status":
                send_message(status_text())

            elif command == "/split":
                handle_action("split")

            elif command == "/stop":
                handle_action("stop")

        except Exception:
            log.exception("Failed to process Telegram update")

    return offset


def main():
    if not STREAM_URL.startswith(("http://", "https://")):
        raise ValueError("STREAM_URL must be an HTTP(S) MPEG-TS URL")

    recorder_thread = threading.Thread(target=record_stream, daemon=True)
    uploader_thread = threading.Thread(target=upload_worker, daemon=True)

    uploader_thread.start()
    recorder_thread.start()

    send_message(
        "🚀 RECORDER STARTED\n"
        "🎞 Input: direct MPEG-TS stream\n"
        "📦 Part limit: approximately 4 GiB\n"
        "☁️ Gofile upload: enabled\n"
        "🔄 Auto-reconnect: enabled"
    )

    offset = None

    try:
        while not stop_event.is_set():
            try:
                offset = poll_telegram(offset)
            except Exception as exc:
                log.warning("Telegram polling error: %s", exc)
                time.sleep(3)

            if not recorder_thread.is_alive():
                stop_event.set()
                break

    except KeyboardInterrupt:
        stop_event.set()

    finally:
        stop_event.set()
        recorder_thread.join()

        # All final files have now been queued.
        upload_queue.put(None)
        upload_queue.join()
        uploader_thread.join()

        send_message(
            "🏁 RECORDER STOPPED\n"
            "The recording process has ended.\n"
            "Check previous messages for upload results."
        )


if __name__ == "__main__":
    main()
