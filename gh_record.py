
import os
import time
import signal
import subprocess
import threading
from pathlib import Path
from datetime import datetime

import requests

# ===== CONFIG =====
BOT_TOKEN = os.environ["TELEGRAM_BOT_TOKEN"]
ALLOWED_CHAT_ID = str(os.environ["TELEGRAM_CHAT_ID"])
STREAM_URL = os.environ["STREAM_URL"]

OUTPUT_DIR = Path("recordings")
OUTPUT_DIR.mkdir(exist_ok=True)

SEGMENT_SECONDS = int(os.getenv("SEGMENT_SECONDS", "600"))
MAX_RUNTIME_MINUTES = int(os.getenv("MAX_RUNTIME_MINUTES", "350"))

API = f"https://api.telegram.org/bot{BOT_TOKEN}"
GOFILE_UPLOAD_URL = "https://upload.gofile.io/uploadfile"

session = requests.Session()
process = None
started_at = time.time()
running = True
uploaded_files = set()
lock = threading.Lock()


def telegram(method, data=None, timeout=35):
    response = session.post(
        f"{API}/{method}",
        json=data or {},
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
                    {"text": "✂️ Split", "callback_data": "split"},
                ],
                [
                    {"text": "⏹ Stop", "callback_data": "stop"}
                ]
            ]
        }

    return telegram("sendMessage", {
        "chat_id": ALLOWED_CHAT_ID,
        "text": text,
        "reply_markup": markup
    })


def start_recording():
    global process

    stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    output_pattern = str(OUTPUT_DIR / f"record_{stamp}_%03d.ts")

    command = [
        "ffmpeg",
        "-hide_banner",
        "-loglevel", "warning",
        "-y",
        "-f", "mpegts",
        "-i", STREAM_URL,
        "-map", "0",
        "-c", "copy",
        "-f", "segment",
        "-segment_time", str(SEGMENT_SECONDS),
        "-reset_timestamps", "1",
        "-segment_format", "mpegts",
        output_pattern
    ]

    process = subprocess.Popen(
        command,
        stdin=subprocess.DEVNULL,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL
    )


def stop_recording():
    global process

    if process and process.poll() is None:
        process.send_signal(signal.SIGINT)

        try:
            process.wait(timeout=20)
        except subprocess.TimeoutExpired:
            process.terminate()
            try:
                process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                process.kill()
                process.wait()

    process = None


def upload_file(path):
    if not path.exists() or path.stat().st_size == 0:
        return False

    try:
        with path.open("rb") as file_obj:
            response = requests.post(
                GOFILE_UPLOAD_URL,
                files={"file": (path.name, file_obj, "video/mp2t")},
                timeout=300
            )

        response.raise_for_status()
        data = response.json()

        if data.get("status") != "ok":
            raise RuntimeError(str(data))

        link = data.get("data", {}).get("downloadPage", "Link unavailable")

        send_message(
            f"✅ Upload complete\n"
            f"File: {path.name}\n"
            f"Size: {path.stat().st_size / (1024 * 1024):.2f} MB\n"
            f"Gofile: {link}"
        )

        uploaded_files.add(str(path))
        path.unlink(missing_ok=True)
        return True

    except Exception as error:
        send_message(f"❌ Upload failed: {path.name}\n{error}")
        return False


def upload_finished_files(all_files=False):
    files = sorted(
        OUTPUT_DIR.glob("*.ts"),
        key=lambda p: p.stat().st_mtime
    )

    # Recording চললে সবচেয়ে নতুন ফাইলটি এখনও লেখা হতে পারে।
    if not all_files and files:
        files = files[:-1]

    for path in files:
        if str(path) not in uploaded_files:
            upload_file(path)


def status_text():
    elapsed = int(time.time() - started_at)
    alive = process is not None and process.poll() is None

    files = list(OUTPUT_DIR.glob("*.ts"))
    size = sum(f.stat().st_size for f in files if f.exists())

    return (
        f"📊 Recorder Status\n"
        f"Recording: {'RUNNING' if alive else 'STOPPED'}\n"
        f"Uptime: {elapsed // 60} minutes\n"
        f"Local TS files: {len(files)}\n"
        f"Local size: {size / (1024 * 1024):.2f} MB"
    )


def handle_action(action):
    global running

    if action == "status":
        send_message(status_text())

    elif action == "split":
        send_message("✂️ Splitting recording...")
        stop_recording()
        upload_finished_files(all_files=True)

        if running:
            start_recording()
            send_message("✅ New MPEG-TS recording started.")

    elif action == "stop":
        running = False
        stop_recording()
        upload_finished_files(all_files=True)
        send_message("⏹ Recording stopped. Final upload check complete.")


def authorized(chat_id):
    return str(chat_id) == ALLOWED_CHAT_ID


def poll_telegram():
    global running

    offset = None

    while running:
        try:
            updates = telegram("getUpdates", {
                "offset": offset,
                "timeout": 25,
                "allowed_updates": ["message", "callback_query"]
            }, timeout=35)

            for update in updates:
                offset = update["update_id"] + 1

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
                        "🎬 MPEG-TS Recorder\n"
                        "/status - Recording status\n"
                        "/split - Start a new recording file/session\n"
                        "/stop - Stop and upload remaining files"
                    )

                elif command == "/status":
                    send_message(status_text())

                elif command == "/split":
                    handle_action("split")

                elif command == "/stop":
                    handle_action("stop")

        except Exception as error:
            print(f"Telegram polling error: {error}")
            time.sleep(3)


def periodic_uploader():
    while running:
        time.sleep(30)

        if not running:
            break

        try:
            upload_finished_files(all_files=False)
        except Exception as error:
            print(f"Upload worker error: {error}")


def main():
    global running

    if not STREAM_URL.startswith(("http://", "https://")):
        raise ValueError("STREAM_URL must be an HTTP(S) MPEG-TS URL")

    start_recording()

    send_message(
        "▶️ MPEG-TS recorder started.\n"
        f"Segment length: {SEGMENT_SECONDS} seconds"
    )

    threading.Thread(target=periodic_uploader, daemon=True).start()

    deadline = time.time() + MAX_RUNTIME_MINUTES * 60

    try:
        while running and time.time() < deadline:
            if process is not None and process.poll() is not None:
                send_message(
                    "⚠️ FFmpeg stopped unexpectedly. "
                    "Check the stream URL and FFmpeg logs."
                )
                running = False
                break

            poll_telegram()
            time.sleep(0.2)

    except KeyboardInterrupt:
        running = False

    finally:
        running = False
        stop_recording()
        upload_finished_files(all_files=True)
        print("Recorder finished.")


if __name__ == "__main__":
    main()
