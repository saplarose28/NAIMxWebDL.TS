#!/usr/bin/env python3
import os
import sys
import time
import queue
import logging
import threading
from pathlib import Path
from datetime import datetime, timezone

import requests

# ================= CONFIG =================

STREAM_URL = os.getenv("STREAM_URL", "").strip()
BOT_TOKEN = os.getenv("TELEGRAM_BOT_TOKEN", "").strip()
CHAT_ID = os.getenv("TELEGRAM_CHAT_ID", "").strip()

PART_SIZE_GB = max(1, int(os.getenv("PART_SIZE_GB", "4")))
PART_BYTES = PART_SIZE_GB * 1024**3

MAX_RUNTIME_MINUTES = max(
    1, int(os.getenv("MAX_RUNTIME_MINUTES", "350"))
)

AUTO_RECONNECT = (
    os.getenv("AUTO_RECONNECT", "true").lower() == "true"
)
UPLOAD_TO_GOFILE = (
    os.getenv("UPLOAD_TO_GOFILE", "true").lower() == "true"
)

CONNECT_TIMEOUT = 20
READ_TIMEOUT = 180
CHUNK_SIZE = 16 * 1024
TS_PACKET = 188

OUT_DIR = Path("recordings")
OUT_DIR.mkdir(exist_ok=True)

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s %(levelname)s %(message)s",
    handlers=[
        logging.StreamHandler(sys.stdout),
        logging.FileHandler("recorder.log", encoding="utf-8"),
    ],
)
log = logging.getLogger("recorder")

http = requests.Session()
http.headers.update({
    "User-Agent": os.getenv("STREAM_USER_AGENT", "VLC/3.0.20"),
    "Accept": "*/*",
    "Connection": "keep-alive",
})

tg_http = requests.Session()

stop_event = threading.Event()
split_event = threading.Event()
state_lock = threading.Lock()

state = {
    "recording": False,
    "started": None,
    "bytes": 0,
    "parts": 0,
    "last_error": "",
    "current_file": "",
    "reconnects": 0,
}

upload_queue = queue.Queue()

# Gofile folder information is reused for the current process.
gofile_guest_token = ""
gofile_folder_id = ""
gofile_folder_link = ""


# ================= TELEGRAM =================

def tg(method, payload=None):
    if not BOT_TOKEN:
        return None

    timeout = (10, 35) if method == "getUpdates" else (10, 30)

    response = tg_http.post(
        f"https://api.telegram.org/bot{BOT_TOKEN}/{method}",
        json=payload or {},
        timeout=timeout,
    )
    response.raise_for_status()

    data = response.json()
    if not data.get("ok"):
        raise RuntimeError(str(data))

    return data.get("result")


def send(message, keyboard=True):
    if not BOT_TOKEN or not CHAT_ID:
        log.info("Telegram: %s", message)
        return

    payload = {
        "chat_id": CHAT_ID,
        "text": message,
        "disable_web_page_preview": True,
    }

    if keyboard:
        payload["reply_markup"] = {
            "inline_keyboard": [
                [
                    {"text": "📊 Status", "callback_data": "status"},
                    {"text": "✂️ Split now", "callback_data": "split"},
                ],
                [
                    {"text": "🛑 Stop", "callback_data": "stop"}
                ],
            ]
        }

    try:
        tg("sendMessage", payload)
    except Exception as exc:
        log.warning("Telegram send failed: %s", exc)


def human(number):
    number = float(number)
    for unit in ("B", "KB", "MB", "GB", "TB"):
        if number < 1024 or unit == "TB":
            return f"{number:.1f} {unit}"
        number /= 1024


def status_text():
    with state_lock:
        started = state["started"]
        elapsed = int(time.time() - started) if started else 0

        return (
            f"Recording: {'yes' if state['recording'] else 'no'}\n"
            f"Elapsed: {elapsed // 3600:02d}:"
            f"{(elapsed % 3600) // 60:02d}:"
            f"{elapsed % 60:02d}\n"
            f"Received: {human(state['bytes'])}\n"
            f"Parts closed: {state['parts']}\n"
            f"Reconnects: {state['reconnects']}\n"
            f"Current part: "
            f"{Path(state['current_file']).name if state['current_file'] else '-'}\n"
            f"Last error: {state['last_error'] or '-'}"
        )


# ================= GOFILE UPLOAD =================

def upload_file(path):
    """
    Upload a completed part, retry failures, and reuse folder details
    returned by Gofile. Verify the actual API response before assuming
    that all files belong to the same folder.
    """
    global gofile_guest_token
    global gofile_folder_id
    global gofile_folder_link

    max_attempts = max(
        1, int(os.getenv("GOFILE_UPLOAD_RETRIES", "8"))
    )

    last_error = None

    for attempt in range(1, max_attempts + 1):
        try:
            files = {
                "file": (path.name, path.open("rb"), "video/mp2t")
            }

            # Reuse the folder credentials when Gofile returns them.
            if gofile_folder_id:
                files["folderId"] = (None, gofile_folder_id)

            if gofile_guest_token:
                files["token"] = (None, gofile_guest_token)

            try:
                response = requests.post(
                    "https://upload.gofile.io/uploadfile",
                    files=files,
                    timeout=(60, 1800),
                )
            finally:
                files["file"][1].close()

            response.raise_for_status()
            result = response.json()

            if result.get("status") != "ok":
                raise RuntimeError(str(result))

            data = result.get("data", {})

            gofile_guest_token = (
                data.get("guestToken") or gofile_guest_token
            )
            gofile_folder_id = (
                data.get("parentFolder")
                or data.get("folderId")
                or gofile_folder_id
            )

            folder_code = (
                data.get("parentFolderCode")
                or data.get("folderCode")
            )

            if folder_code:
                gofile_folder_link = (
                    f"https://gofile.io/d/{folder_code}"
                )
            elif not gofile_folder_link:
                gofile_folder_link = data.get("downloadPage", "")

            link = gofile_folder_link or data.get(
                "downloadPage", ""
            )

            log.info("Upload complete: %s", path.name)

            send(
                f"✅ Uploaded: {path.name}\n"
                f"Folder link: {link or 'API returned no link'}",
                False,
            )
            return True

        except Exception as exc:
            last_error = exc
            log.warning(
                "Upload attempt %s/%s failed for %s: %s",
                attempt, max_attempts, path.name, exc,
            )

            if attempt < max_attempts:
                delay = min(300, 15 * (2 ** (attempt - 1)))
                log.info("Retrying upload in %s seconds", delay)
                stop_event.wait(delay)

    log.error("Upload failed: %s: %s", path.name, last_error)

    send(
        f"⚠️ Upload failed: {path.name}\n"
        f"Error: {last_error}\n"
        "The file remains in the recordings folder for recovery.",
        False,
    )
    return False


def uploader():
    while True:
        path = upload_queue.get()

        try:
            if path is None:
                return

            if UPLOAD_TO_GOFILE:
                upload_file(path)

        finally:
            upload_queue.task_done()


# ================= RECORDING =================

def new_path(index):
    stamp = datetime.now(timezone.utc).strftime("%Y%m%d_%H%M%S")
    return OUT_DIR / f"recording_{stamp}_part{index:03d}.ts"


def record():
    if not STREAM_URL:
        raise SystemExit("STREAM_URL is required")

    start = time.monotonic()
    index = 0
    reconnects = 0

    current_file = None
    current_path = None
    current_size = 0

    ts_buffer = bytearray()

    with state_lock:
        state.update(
            recording=True,
            started=time.time(),
            bytes=0,
            parts=0,
            reconnects=0,
            last_error="",
            current_file="",
        )

    def close_part():
        nonlocal current_file, current_path, current_size

        if current_file is None:
            return

        current_file.flush()
        current_file.close()
        current_file = None

        if current_path and current_size > 0:
            log.info(
                "Closed %s (%s)",
                current_path.name,
                human(current_size),
            )
            upload_queue.put(current_path)

            with state_lock:
                state["parts"] += 1

        current_path = None
        current_size = 0

    def write_packet(packet):
        nonlocal current_file, current_path, current_size, index

        must_split = (
            current_file is None
            or current_size + len(packet) > PART_BYTES
            or split_event.is_set()
        )

        if must_split:
            close_part()
            split_event.clear()

            index += 1
            current_path = new_path(index)
            current_file = current_path.open("wb")

            with state_lock:
                state["current_file"] = str(current_path)

            log.info("Opened part: %s", current_path.name)

        current_file.write(packet)
        current_size += len(packet)

        with state_lock:
            state["bytes"] += len(packet)

    try:
        while (
            not stop_event.is_set()
            and time.monotonic() - start < MAX_RUNTIME_MINUTES * 60
        ):
            response = None

            try:
                log.info("Connecting to stream")

                response = http.get(
                    STREAM_URL,
                    stream=True,
                    timeout=(CONNECT_TIMEOUT, READ_TIMEOUT),
                    allow_redirects=True,
                )
                response.raise_for_status()

                content_type = response.headers.get(
                    "Content-Type", ""
                )

                if "text/html" in content_type.lower():
                    raise RuntimeError(
                        "Server returned HTML instead of a stream"
                    )

                log.info(
                    "Stream connected; Content-Type=%s",
                    content_type,
                )

                # Keep the current part open across reconnects.
                for chunk in response.iter_content(
                    chunk_size=CHUNK_SIZE
                ):
                    if stop_event.is_set():
                        break

                    if time.monotonic() - start >= MAX_RUNTIME_MINUTES * 60:
                        break

                    if not chunk:
                        continue

                    ts_buffer.extend(chunk)

                    while len(ts_buffer) >= TS_PACKET * 2:
                        if (
                            ts_buffer[0] == 0x47
                            and ts_buffer[TS_PACKET] == 0x47
                        ):
                            write_packet(bytes(ts_buffer[:TS_PACKET]))
                            del ts_buffer[:TS_PACKET]

                        else:
                            found = -1
                            scan_end = len(ts_buffer) - TS_PACKET * 2

                            for pos in range(1, max(1, scan_end + 1)):
                                if (
                                    ts_buffer[pos] == 0x47
                                    and ts_buffer[pos + TS_PACKET] == 0x47
                                ):
                                    found = pos
                                    break

                            if found >= 0:
                                del ts_buffer[:found]
                            else:
                                keep = TS_PACKET * 2 - 1
                                if len(ts_buffer) > keep:
                                    del ts_buffer[:-keep]
                                break

                if stop_event.is_set():
                    break

                if time.monotonic() - start >= MAX_RUNTIME_MINUTES * 60:
                    break

                raise ConnectionError("Stream ended; reconnecting")

            except Exception as exc:
                message = f"{type(exc).__name__}: {exc}"

                with state_lock:
                    state["last_error"] = message[:300]
                    state["reconnects"] = reconnects + 1

                log.warning("Stream error: %s", message)

                if not AUTO_RECONNECT:
                    break

                reconnects += 1
                wait_seconds = min(30, 2 ** min(reconnects, 5))

                log.info(
                    "Reconnecting in %s seconds; keeping current part open",
                    wait_seconds,
                )

                stop_event.wait(wait_seconds)

            finally:
                if response is not None:
                    response.close()

        close_part()

    finally:
        with state_lock:
            state["recording"] = False
            state["current_file"] = ""

        upload_queue.join()
        send("⏹️ Recording finished.\n" + status_text(), False)


# ================= TELEGRAM COMMANDS =================

def telegram_loop():
    offset = 0

    while not stop_event.is_set() or state["recording"]:
        try:
            updates = tg(
                "getUpdates",
                {
                    "offset": offset,
                    "timeout": 20,
                    "allowed_updates": ["message", "callback_query"],
                },
            ) or []

            for update in updates:
                offset = max(offset, update["update_id"] + 1)

                callback = update.get("callback_query")

                if callback:
                    try:
                        tg(
                            "answerCallbackQuery",
                            {"callback_query_id": callback.get("id", "")},
                        )
                    except Exception:
                        pass

                    message = callback.get("message", {})
                    chat_id = str(
                        message.get("chat", {}).get("id", "")
                    )
                    action = callback.get("data", "")

                else:
                    message = update.get("message", {})
                    chat_id = str(
                        message.get("chat", {}).get("id", "")
                    )
                    action = (
                        message.get("text", "")
                        .strip()
                        .lower()
                        .lstrip("/")
                    )

                if chat_id != CHAT_ID:
                    continue

                if action in ("start", "status"):
                    send(status_text())

                elif action == "split":
                    split_event.set()
                    send("✂️ New part requested.", False)

                elif action == "stop":
                    stop_event.set()
                    send("🛑 Stop requested.", False)

        except requests.exceptions.ReadTimeout:
            # Long polling can occasionally time out normally.
            log.info("Telegram polling timed out; retrying")
            stop_event.wait(2)

        except Exception as exc:
            log.warning("Telegram polling failed: %s", exc)
            stop_event.wait(3)


# ================= MAIN =================

def main():
    if not STREAM_URL:
        raise SystemExit("Set STREAM_URL in your GitHub Secrets")

    if UPLOAD_TO_GOFILE:
        threading.Thread(
            target=uploader,
            daemon=True,
        ).start()

    if BOT_TOKEN and CHAT_ID:
        send(
            f"▶️ Recorder started\n"
            f"Part size: {PART_SIZE_GB} GiB\n"
            f"Runtime: {MAX_RUNTIME_MINUTES} minutes\n"
            f"Auto reconnect: {AUTO_RECONNECT}\n"
            f"Gofile upload: {UPLOAD_TO_GOFILE}"
        )

        threading.Thread(
            target=telegram_loop,
            daemon=True,
        ).start()

    else:
        log.warning("Telegram controls disabled: missing credentials")

    try:
        record()

    finally:
        stop_event.set()

        if UPLOAD_TO_GOFILE:
            upload_queue.put(None)
            upload_queue.join()


if __name__ == "__main__":
    main()
