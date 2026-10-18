#!/usr/bin/env python3
"""Runs inside GitHub Actions.
Records an HLS / MPEG-TS link with ffmpeg -c copy (no quality loss) in ONE continuous stream, cuts it into files at
keyframes every PART_MB megabytes (default 4000 = 4 GB, whatever time that takes) and uploads each finished
file to Gofile while the recording keeps going. Telegram gets the links, the Status / Split / Stop buttons.

Reconnect behaviour:
  * a reader thread + big memory queue keep ffmpeg's pipe empty, so a slow disk/upload never makes the server drop us
  * when ffmpeg has to reconnect, HLS restarts RECON_BACK segments behind live (old data is skipped, nothing is lost)
  * if the server restarts its clock on reconnect, the timestamps are shifted so the video continues smoothly in the
    SAME file. A new file is made only at PART_MB (or the Split button), never because of a reconnect.

  python gh_record.py            record
  python gh_record.py finish     upload anything left over (used by the always() step)"""
import os, re, sys, json, glob, time, html, queue, signal, shutil, threading, subprocess, urllib.request, urllib.parse, urllib.error
try:
    import fcntl
except ImportError:
    fcntl = None

E = os.environ.get
TOKEN, CHAT = E("TG_TOKEN", ""), E("TG_CHAT", "")
REPO, RUN = E("REPO", ""), E("RUN_ID", "local")
URL = E("URL", "")
NAME = re.sub(r"[^\w\-]+", "_", E("NAME") or "ClipByNaim")
MINUTES = float(E("MINUTES") or 0)             # 0 = until Stop
PART_MIN = float(E("PART_MIN") or 0)            # optional: also split every N minutes (0 = off, split by size only)
PART_MAX = min(float(E("PART_MB") or 4000), 5000) * 1e6   # a new file every N MB (4000 = 4 GB)
BACK = E("BACK_SEGS") or "5"                    # start N segments behind live (safety)
RECON_BACK = E("RECON_BACK") or "12"            # after a reconnect (HLS): start N segments behind, repeated data is skipped
OUT = E("OUT_DIR") or "rec"
MP4_DIR = E("MP4_DIR") or OUT                    # finished .mp4 files (a different disk folder from the .ts files)
FAILED = E("FAILED_DIR") or "rec_failed"
DRY = E("DRY") == "1"                           # test mode: no uploads
TEST_ONCE = E("TEST_ONCE") == "1"               # test mode: do not restart when the input ends
GOFILE_URL = E("GOFILE_URL") or "https://upload.gofile.io/uploadfile"
IDLE_STOP = float(E("IDLE_STOP_MIN") or 10)     # stop the job when the stream sends no data for N minutes (saves GitHub minutes), 0 = off
ASKED = False                                   # True when the link came from Telegram (it is kept out of the GitHub page)
RETRY_BASE = float(E("RETRY_BASE") or 30)       # seconds, grows with every upload retry
GF = {"folder": "", "token": ""}
LIMIT = 345 * 60                                # one job runs ~6 h; a new run continues before that
STAMP = time.strftime("%Y%m%d_%H%M%S")
RUN_URL = "https://github.com/%s/actions/runs/%s" % (REPO, RUN)
UA = E("UA") or "Mozilla/5.0 (Linux; Android 13; Pixel 7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0 Mobile Safari/537.36"
REFERER = E("REFERER") or ""
HDR = ["-user_agent", UA]

M33 = 0x1FFFFFFFF                               # 33 bit timestamp mask (90 kHz clock)
JUMP_BACK = 90000                               # clock went back more than 1 s  -> source restarted
JUMP_FWD = 270000                               # clock jumped forward more than 3 s -> close the gap, keep it smooth
DUP_WINDOW = 90000 * 600                        # data up to 10 min older than what we saved counts as "already have it"

stop = threading.Event()
S = {"proc": None, "t0": time.time(), "restarts": 0, "done": [], "page": "", "last_data": time.time(), "reason": "", "qmax": 0}
upq = queue.Queue()
SP = None


# ---------------- small helpers ----------------
def esc(t):
    return html.escape(str(t), quote=False)


def human(b):
    return "%.2f GB" % (b / 1e9) if b >= 1e9 else "%.0f MB" % (b / 1e6)


def hms(s):
    s = int(max(0, s))
    return "%02d:%02d:%02d" % (s // 3600, s % 3600 // 60, s % 60)


def mmss(s):
    s = int(max(0, s))
    return "%d:%02d:%02d" % (s // 3600, s % 3600 // 60, s % 60) if s >= 3600 else "%d:%02d" % (s // 60, s % 60)


def mask(t):
    return (t or "").replace(URL, "<link>") if URL else (t or "")


def _origin(u):
    m = re.match(r"^(https?://[^/]+)", u or "")
    return m.group(1) if m else ""


KB = {"inline_keyboard": [[{"text": "📊 Status", "callback_data": "status"},
                           {"text": "✂️ Split", "callback_data": "split"},
                           {"text": "⏹ Stop", "callback_data": "stop"}]]}


def tg(method, **data):
    if not TOKEN or DRY:
        print("[telegram]", method, re.sub(r"<[^>]+>", "", str(data.get("text", ""))).replace("\n", " | "))
        return {}
    try:
        req = urllib.request.Request("https://api.telegram.org/bot%s/%s" % (TOKEN, method), urllib.parse.urlencode(data).encode())
        return json.load(urllib.request.urlopen(req, timeout=40))
    except urllib.error.HTTPError as e:
        try: body = e.read().decode()[:200]
        except Exception: body = ""
        print("Telegram error %s: %s" % (e.code, body), flush=True)
        return {"ok": False, "error_code": e.code}
    except Exception as e:
        print("telegram error:", e)
        return {}


def say(text, buttons=False):
    if not (CHAT or DRY):
        print("[msg]", re.sub(r"<[^>]+>", "", text))
        return
    d = dict(chat_id=CHAT, text=text, parse_mode="HTML", disable_web_page_preview="true")
    if buttons:
        d["reply_markup"] = json.dumps(KB)
    tg("sendMessage", **d)


def detect_chat():
    """If TG_CHAT is empty, use the chat of the latest message sent to the bot (send it 'hi' first)."""
    global CHAT
    if CHAT or not TOKEN or DRY:
        return
    r = tg("getUpdates", timeout=0)
    ids = [((u.get("message") or {}).get("chat") or {}).get("id") for u in r.get("result", [])]
    ids = [i for i in ids if i]
    if ids:
        CHAT = str(ids[-1]); print("Chat detected from the latest message sent to the bot.", flush=True)
    else:
        print("NO CHAT ID: send 'hi' to your bot in Telegram, then run again (within 24 hours).", flush=True)


def summary(text):
    p = E("GITHUB_STEP_SUMMARY")
    if p:
        try:
            with open(p, "a") as f:
                f.write(text + "\n")
        except OSError:
            pass


# ---------------- MPEG-TS splitter (cuts at keyframes, recording never stops) ----------------
def pes_times(pk):
    """(pts, dts) of the PES that starts in this packet; dts falls back to pts."""
    afc = (pk[3] >> 4) & 3
    if not afc & 1:
        return None, None
    p = 4 + ((1 + pk[4]) if afc & 2 else 0)
    if p + 14 > 188 or pk[p] or pk[p + 1] or pk[p + 2] != 1 or not (pk[p + 7] & 0x80):
        return None, None
    def ts(i):
        return ((pk[i] >> 1) & 7) * 1073741824 + ((pk[i + 1] << 22) | ((pk[i + 2] >> 1) << 15) | (pk[i + 3] << 7) | (pk[i + 4] >> 1))
    pts = ts(p + 9)
    dts = ts(p + 14) if (pk[p + 7] & 0x40) and p + 19 <= 188 else pts
    return pts, dts


def sdiff(a, b):
    """a - b on the 33 bit clock, as a signed number."""
    d = (a - b) & M33
    return d - (1 << 33) if d >= (1 << 32) else d


def shift_ts(pk, off):
    """Return a copy of the packet with PTS, DTS and PCR moved by off (90 kHz ticks)."""
    b = bytearray(pk)
    afc = (pk[3] >> 4) & 3
    if afc & 2 and pk[4] >= 7 and pk[5] & 0x10:                     # PCR in the adaptation field
        base = ((pk[6] << 25) | (pk[7] << 17) | (pk[8] << 9) | (pk[9] << 1) | (pk[10] >> 7))
        base = (base + off) & M33
        b[6] = (base >> 25) & 0xFF; b[7] = (base >> 17) & 0xFF; b[8] = (base >> 9) & 0xFF; b[9] = (base >> 1) & 0xFF
        b[10] = ((base & 1) << 7) | (pk[10] & 0x7F)
    if afc & 1 and (pk[1] & 0x40):                                   # PES header with PTS (and DTS)
        p = 4 + ((1 + pk[4]) if afc & 2 else 0)
        if p + 14 <= 188 and not pk[p] and not pk[p + 1] and pk[p + 2] == 1 and (pk[p + 7] & 0x80):
            def put(i):
                v = (((pk[i] >> 1) & 7) * 1073741824 + ((pk[i + 1] << 22) | ((pk[i + 2] >> 1) << 15) | (pk[i + 3] << 7) | (pk[i + 4] >> 1)) + off) & M33
                b[i] = (pk[i] & 0xF0) | (((v >> 30) & 7) << 1) | 1
                b[i + 1] = (v >> 22) & 0xFF
                b[i + 2] = (((v >> 15) & 0x7F) << 1) | 1
                b[i + 3] = (v >> 7) & 0xFF
                b[i + 4] = ((v & 0x7F) << 1) | 1
            put(p + 9)
            if (pk[p + 7] & 0x40) and p + 19 <= 188:
                put(p + 14)
    return b


def vsig(pk):
    """Fingerprint of a video picture: the first bytes of its data (after the PES header)."""
    afc = (pk[3] >> 4) & 3
    p = 4 + ((1 + pk[4]) if afc & 2 else 0)
    st = p + 9 + pk[p + 8]
    return bytes(pk[st:min(st + 24, 188)])


def same_sig(a, b):
    n = min(len(a), len(b) if b else 0)
    return b is not None and n >= 8 and a[:n] == b[:n]


class Splitter:
    def __init__(self, on_done):
        self.on_done = on_done
        self.buf = b""
        self.f = None; self.path = ""
        self.part_no = 0; self.cur_bytes = 0; self.total = 0
        self.start_pts = None; self.last_pts = None
        self.pat = None; self.pmt = None; self.pmt_pid = None; self.vid = None
        self.want_split = False; self.manual_flag = False; self.on_manual = None
        self.hist = []
        self.aud = set(); self.cc = {}; self.last_wr = {}
        self.off = 0; self.last_out_v = None; self.fdur = 3600; self.rebased = 0     # timestamp shift so reconnects join smoothly
        self.skip = None; self.dropping = set(); self.drop_bytes = 0; self.deduped = 0; self.last_write = time.time(); self.last_es = time.time()
        self.need_key = False; self.need_key_until = 0
        self.recent = {}; self.verify = False                # dts -> fingerprint of recently saved pictures

    def new_session(self, dedupe=True, verify=False):
        """ffmpeg was restarted: it re-sends some old data. Drop everything up to the last time we already wrote."""
        self.buf = b""
        marks = {k: v for k, v in self.last_wr.items() if v is not None}
        self.skip = dict(marks) if (marks and dedupe) else None
        self.dropping = set(); self.drop_bytes = 0
        # If we skip repeated data, the new data continues right after what is already saved (same picture group),
        # so no keyframe is needed. Otherwise wait for the next keyframe so there is no broken picture.
        self.verify = self.skip is not None and verify        # TS: the first old picture must really be one we saved (HLS replays many segments, no check)
        self.need_key = self.vid is not None and self.skip is None
        self.need_key_until = time.time() + 20
        print("New connection. Repeated data dropped so far: %.1f MB" % (self.deduped / 1e6), flush=True)

    def _write(self, pk):
        pid = ((pk[1] & 0x1f) << 8) | pk[2]
        b = bytearray(pk)
        if (pk[3] >> 4) & 1:                              # packet has payload: continue the counter without gaps
            c = (self.cc.get(pid, -1) + 1) & 15
            self.cc[pid] = c
        else:
            c = self.cc.get(pid, 0)
        b[3] = (b[3] & 0xF0) | c
        self.f.write(b)
        self.last_write = time.time()

    def media_secs(self):
        if self.start_pts is None or self.last_pts is None:
            return 0.0
        return ((self.last_pts - self.start_pts) % (1 << 33)) / 90000.0

    def speed_mbps(self):
        now = time.time()
        self.hist = [h for h in self.hist if now - h[0] <= 12]
        if len(self.hist) < 2:
            return 0.0
        dt = self.hist[-1][0] - self.hist[0][0]
        return (self.hist[-1][1] - self.hist[0][1]) * 8 / dt / 1e6 if dt > 0.5 else 0.0

    def _open(self):
        self.part_no += 1
        self.path = os.path.join(OUT, "%s_%s_part%03d.ts" % (NAME, STAMP, self.part_no))
        self.f = open(self.path, "wb")
        self.cur_bytes = 0
        self.start_pts = self.last_pts
        for p in (self.pat, self.pmt):                 # every file starts with PAT + PMT, then a keyframe
            if p:
                self._write(p); self.cur_bytes += 188

    def _close(self):
        if not self.f:
            return
        self.f.close(); self.f = None
        if self.cur_bytes > 188 * 40:
            self.on_done(self.path)
        else:
            try: os.remove(self.path)
            except OSError: pass

    def finish(self):
        self._close()

    def _pat(self, pk):
        self.pat = bytes(pk)
        p = 4 + ((1 + pk[4]) if (pk[3] >> 4) & 2 else 0)
        p += 1 + pk[p]
        sec = ((pk[p + 1] & 15) << 8) | pk[p + 2]
        q, end = p + 8, min(p + 3 + sec - 4, 188)
        while q + 4 <= end:
            if ((pk[q] << 8) | pk[q + 1]) != 0:
                self.pmt_pid = ((pk[q + 2] & 31) << 8) | pk[q + 3]
                break
            q += 4

    def _pmt(self, pk):
        self.pmt = bytes(pk)
        p = 4 + ((1 + pk[4]) if (pk[3] >> 4) & 2 else 0)
        p += 1 + pk[p]
        sec = ((pk[p + 1] & 15) << 8) | pk[p + 2]
        info = ((pk[p + 10] & 15) << 8) | pk[p + 11]
        q, end = p + 12 + info, min(p + 3 + sec - 4, 188)
        while q + 5 <= end:
            if pk[q] in (0x1b, 0x24, 0x02, 0x10) and self.vid is None:
                self.vid = ((pk[q + 1] & 31) << 8) | pk[q + 2]
            elif pk[q] in (0x0f, 0x11, 0x03, 0x04, 0x81, 0x87):
                self.aud.add(((pk[q + 1] & 31) << 8) | pk[q + 2])
            q += 5 + (((pk[q + 3] & 15) << 8) | pk[q + 4])

    def _should_split(self):
        # only: Split button, optional time limit, or the size limit. A reconnect / clock jump never splits a file.
        if self.want_split:
            self.want_split = False; self.manual_flag = True
            return True
        return (PART_MIN > 0 and self.media_secs() >= PART_MIN * 60) or self.cur_bytes >= PART_MAX

    def feed(self, data):
        self.buf += data
        n = len(self.buf); i = 0
        while i < n and self.buf[i] != 0x47:
            i += 1
        end = i + ((n - i) // 188) * 188
        buf = self.buf
        for o in range(i, end, 188):
            pk = buf[o:o + 188]
            pid = ((pk[1] & 0x1f) << 8) | pk[2]
            if pid == 0x1fff:
                continue                                  # drop empty padding packets
            pusi = pk[1] & 0x40
            key = False
            is_es = pid == self.vid or pid in self.aud
            pts, dts = pes_times(pk) if (pusi and is_es) else (None, None)
            if self.skip is not None and is_es:          # after a reconnect: skip data we already have
                if pusi:
                    k = "v" if pid == self.vid else pid
                    last = self.skip.get(k)
                    fresh = False
                    if last is None or dts is None:
                        ahead = True
                    else:
                        d = sdiff(dts, last)
                        ahead = d > 0 or d < -DUP_WINDOW   # newer than what we saved, or the server clock restarted
                        if not ahead and pid == self.vid and self.verify:
                            self.verify = False
                            if not same_sig(vsig(pk), self.recent.get(dts)):
                                fresh = True               # not a picture we saved: new content with a restarted clock
                    if fresh:
                        print("Server restarted its clock with NEW content: nothing is dropped, timeline is joined instead", flush=True)
                        self.skip = None; self.dropping = set()
                        self.need_key = True; self.need_key_until = time.time() + 20
                    elif ahead:
                        if pid == self.vid and last is not None and dts is not None:
                            self.verify = False
                            if not (0 < sdiff(dts, last) <= max(3 * self.fdur, 9000)):
                                self.need_key = True; self.need_key_until = time.time() + 20   # not the very next picture: gap, wait for keyframe
                        self.skip.pop(k, None); self.dropping.discard(pid)
                        if not self.skip:
                            self.skip = None
                    else:
                        self.dropping.add(pid)
                if pid in self.dropping:
                    self.drop_bytes += 188; self.deduped += 188
                    if self.drop_bytes > 400_000_000:     # timestamps do not match: stop skipping, keep recording
                        self.skip = None; self.dropping = set()
                    continue
            if self.need_key and is_es:
                if pid == self.vid and pusi and (pk[3] >> 4) & 2 and pk[4] > 0 and (pk[5] & 0x40):
                    self.need_key = False
                elif time.time() > self.need_key_until:
                    self.need_key = False
                else:
                    continue
            if pid == 0 and pusi:
                self._pat(pk)
                if self.vid is None and self.pmt:
                    key = True                            # audio-only stream: cut at PAT
            elif pid == self.pmt_pid and pusi:
                self._pmt(pk)
            elif pid == self.vid and pusi:
                if pts is not None:
                    lastv = self.last_wr.get("v")
                    if lastv is not None and self.skip is None:
                        dd = sdiff(dts, lastv)
                        if dd < -JUMP_BACK or dd > JUMP_FWD:
                            # the server clock jumped (reconnect / restart): shift all following timestamps so the
                            # picture continues one frame after the last one. Same file, no cut, no freeze.
                            if self.last_out_v is not None:
                                self.off = (self.last_out_v + self.fdur - dts) & M33
                                self.rebased += 1
                                print("Clock jump %+.1fs: timeline joined smoothly (join #%d)" % (dd / 90000.0, self.rebased), flush=True)
                        elif 0 < dd <= 18000:
                            self.fdur = dd                # normal picture spacing, used to place the first picture after a join
                    self.last_pts = (pts + self.off) & M33
                    self.last_out_v = (dts + self.off) & M33
                    self.last_wr["v"] = dts               # raw value, used to skip repeated data after a reconnect
                    self.recent[dts] = vsig(pk)
                    if len(self.recent) > 3000:
                        del self.recent[next(iter(self.recent))]
                if (pk[3] >> 4) & 2 and pk[4] > 0 and (pk[5] & 0x40):
                    key = True                            # random access indicator = keyframe starts here
            elif pid in self.aud and pusi and dts is not None:
                self.last_wr[pid] = dts
            if self.f is None:
                if (key or (self.vid is None and self.pmt and pid not in (0, self.pmt_pid))) and (self.pat and self.pmt):
                    self._open()
                else:
                    continue
            elif key and self._should_split():
                self._close(); self._open()
                if self.manual_flag:
                    self.manual_flag = False
                    if self.on_manual:
                        self.on_manual(self.part_no)
            if self.off and (pts is not None or ((pk[3] >> 4) & 2 and pk[4] >= 7 and pk[5] & 0x10)):
                pk = shift_ts(pk, self.off)
            self._write(pk); self.cur_bytes += 188
            if is_es:
                self.last_es = time.time()                # real video/audio data was saved (not just PAT/PMT)
        self.total += end - i
        self.buf = buf[end:]
        now = time.time()
        self.hist.append((now, self.total))
        if len(self.hist) > 1500:
            self.hist = [h for h in self.hist if now - h[0] <= 15]


# ---------------- messages ----------------
def status_text():
    el = time.time() - S["t0"]
    left = max(0, MINUTES * 60 - el) if MINUTES else None
    sp = SP
    saved = sum(d["size"] for d in S["done"])
    spd = sp.speed_mbps() if sp else 0
    nxt = ""
    if sp and sp.f:
        t_left = (PART_MIN * 60 - sp.media_secs()) if PART_MIN > 0 else 1e12
        if spd > 0.1:
            t_left = min(t_left, (PART_MAX - sp.cur_bytes) * 8 / (spd * 1e6))
        if t_left < 1e11:
            nxt = "\n✂️ <b>Next auto-split</b>  in ~%s  (at %s)" % (mmss(t_left), human(PART_MAX))
    lines = [
        "🔴 <b>Recording</b>  ·  %s" % esc(NAME), "",
        "⏱ <b>Elapsed</b>  %s%s" % (hms(el), ("   ·   left %s" % hms(left)) if left is not None else ""),
        "📦 <b>Current file</b>  #%02d  ·  %s  ·  %s" % (sp.part_no if sp else 0, human(sp.cur_bytes) if sp else "0 MB", mmss(sp.media_secs()) if sp else "0:00"),
        "✅ <b>Saved</b>  %d file(s)  ·  %s" % (len(S["done"]), human(saved)),
        "⚡ <b>Speed</b>  %.1f Mbps" % spd + nxt,
    ]
    if S["restarts"]:
        lines.append("♻️ <b>Reconnects</b>  %d  (files are NOT cut by reconnects)" % S["restarts"])
        if S["reason"]:
            lines.append("<code>%s</code>" % esc(S["reason"][:160]))
    if S["page"]:
        lines += ["", '📂 <a href="%s">Open the download page</a>' % S["page"]]
    return "\n".join(lines)


def do_action(act, cq_id=None):
    global SP
    if act == "status":
        txt = "Status sent"; say(status_text(), buttons=True)
    elif act == "split":
        if SP and SP.f:
            SP.want_split = True; txt = "Split requested"
            say("✂️ <b>Split requested</b>\nThe current file is closed at the next keyframe (a few seconds). Recording continues in a new file.", buttons=True)
        else:
            txt = "Not recording yet"; say("Recording has not started yet, nothing to split.")
    elif act == "stop":
        txt = "Stopping"
        say("⏹ <b>Stopping...</b>\nSaving the last file. This can take up to a minute.")
        halt()
    else:
        return
    if cq_id:
        tg("answerCallbackQuery", callback_query_id=cq_id, text=txt)


def halt():
    stop.set()
    p = S["proc"]
    if p and p.poll() is None:
        p.send_signal(signal.SIGINT)                  # ffmpeg finishes cleanly


def poll():
    off = 0
    r = tg("getUpdates", offset=-1, timeout=0)
    if r.get("error_code") == 409:
        return                                         # a webhook (worker) is active: it handles /stop
    for u in r.get("result", []):
        off = u["update_id"] + 1
    while not stop.is_set():
        r = tg("getUpdates", offset=off, timeout=15, allowed_updates=json.dumps(["message", "callback_query"]))
        if r.get("error_code") == 409:
            return
        for u in r.get("result", []):
            off = u["update_id"] + 1
            cq = u.get("callback_query")
            if cq:
                if str(((cq.get("message") or {}).get("chat") or {}).get("id")) == str(CHAT):
                    do_action(cq.get("data", ""), cq.get("id"))
                continue
            m = u.get("message") or {}
            if str((m.get("chat") or {}).get("id")) != str(CHAT):
                continue
            t = (m.get("text") or "").strip().lower().split("@")[0]
            for key in ("status", "split", "stop"):
                if t.startswith("/" + key) or (key == "split" and t.startswith("/slipt")):
                    do_action(key); break
            else:
                if t.startswith("/start") or t.startswith("/help"):
                    say("🎬 <b>ClipByNaim recorder</b>\nUse the buttons or send /status, /split, /stop.", buttons=True)
        if not r:
            time.sleep(3)


# ---------------- upload (Gofile) ----------------
def gofile_upload(path):
    """Upload to Gofile (no account). All files of one recording go into the same folder page."""
    if DRY:
        print("[dry] would upload to gofile", path); return True, "https://gofile.io/d/DRYRUN", ""
    err = ""
    for attempt in range(6):
        cmd = ["nice", "-n", "10", "curl", "-sS", "-m", "3600", "-F", "file=@" + path]   # low priority: never starve the recorder
        if GF["folder"] and GF["token"]:
            cmd += ["-F", "folderId=" + GF["folder"], "-F", "token=" + GF["token"]]
        r = subprocess.run(cmd + [GOFILE_URL], capture_output=True, text=True)
        try:
            j = json.loads(r.stdout)
        except Exception:
            err = (r.stderr or r.stdout or "no answer from Gofile").strip()[:200]
            j = None
        if j is not None:
            if j.get("status") == "ok":
                d = j.get("data") or {}
                GF["folder"] = d.get("parentFolder") or GF["folder"]
                GF["token"] = d.get("guestToken") or GF["token"]
                return True, d.get("downloadPage") or "", ""
            err = json.dumps(j)[:200]
            GF["folder"] = GF["token"] = ""          # maybe the folder/token was the problem, start a new folder
        print("gofile upload failed (try %d): %s" % (attempt + 1, err), flush=True)
        time.sleep(RETRY_BASE * (attempt + 1))
    return False, "", err


def media_info(path):
    try:
        r = subprocess.run(["ffprobe", "-v", "error", "-select_streams", "v:0", "-show_entries", "stream=width,height:format=duration",
                            "-of", "json", path], capture_output=True, text=True, timeout=60)
        j = json.loads(r.stdout or "{}"); st = (j.get("streams") or [{}])[0]
        return float((j.get("format") or {}).get("duration") or 0), int(st.get("width") or 0), int(st.get("height") or 0)
    except Exception:
        return 0.0, 0, 0


def process(ts):
    """remux the finished .ts to .mp4 (proper duration), upload it, tell Telegram, clean up."""
    os.makedirs(MP4_DIR, exist_ok=True)
    base = os.path.basename(ts)[:-3] + ".mp4"
    mp4 = os.path.join(MP4_DIR, base)
    r = subprocess.run(["nice", "-n", "10", "ffmpeg", "-hide_banner", "-loglevel", "error", "-y", "-i", ts, "-c", "copy", "-avoid_negative_ts", "make_zero", "-movflags", "+faststart", mp4],
                       capture_output=True, text=True)
    if r.returncode != 0 or not os.path.exists(mp4):
        mp4 = ts; base = os.path.basename(ts)
    elif not DRY:
        try: os.remove(ts)                           # free disk space right away
        except OSError: pass
    size = os.path.getsize(mp4)
    dur = media_info(mp4)[0]
    n = len(S["done"]) + 1
    ok, link, err = gofile_upload(mp4)
    head = "✅ <b>File %d saved</b>\n🎞 %s  ·  %s\n" % (n, mmss(dur), human(size))
    if ok:
        if link:
            S["page"] = link
        S["done"].append({"name": base, "size": size, "secs": dur})
        say(head + '⬇️ <a href="%s">Download page</a>  (all files of this recording are listed there)' % (link or S["page"]), buttons=True)
        if not DRY:
            for f in {ts, mp4}:
                try: os.remove(f)
                except OSError: pass
    else:
        os.makedirs(FAILED, exist_ok=True)
        try: shutil.move(mp4, os.path.join(FAILED, base))
        except OSError: pass
        S["done"].append({"name": base, "size": size, "secs": dur})
        say("⚠️ <b>Upload to Gofile failed</b> for %s (%s)\n<b>Reason:</b> <code>%s</code>\n\nThe file is still on the GitHub server until the run ends. If this keeps happening, try again later." %
            (esc(base), human(size), esc((err or "unknown")[:250])))


def uploader():
    while True:
        item = upq.get()
        if item is None:
            return
        try:
            process(item)
        except Exception as e:
            print("process error:", repr(e), flush=True)
            say("⚠️ Error while saving a file: <code>%s</code>" % esc(repr(e)[:200]))


# ---------------- link check + recording ----------------
def explain(err):
    e = (err or "").lower()
    if "403" in e or "forbidden" in e:
        return "403 Forbidden: the stream server refuses GitHub's server. Country/IP block, or the link needs a login or an expired token."
    if "401" in e or "unauthorized" in e:
        return "401 Unauthorized: the link needs a login or its token is wrong or expired."
    if "404" in e or "not found" in e:
        return "404 Not found: the link has expired or is wrong. Copy a fresh link and try again."
    if "timed out" in e or "timeout" in e:
        return "Connection timed out: the server does not answer GitHub's server. Usually an IP/country block."
    if "could not resolve" in e or "name or service not known" in e or "nodename" in e:
        return "The website name in the link could not be found. Check the link for typing mistakes."
    if "invalid data found" in e:
        return "This link is not a video playlist (.m3u8). Open it in a browser: it should give a playlist, not a web page."
    if "connection refused" in e or "reset by peer" in e or "end of file" in e:
        return "The server closed the connection. Usually it blocks GitHub's server."
    return "Unknown reason. Read the ffmpeg line above."


KIND = "hls"                                       # "hls" (.m3u8 playlist) or "ts" (live MPEG-TS over HTTP)


def kind_from_url():
    u = URL.lower()
    path = u.split("?")[0]
    if "m3u8" in u:
        return "hls"
    if path.endswith((".ts", ".mpegts", ".mts", ".m2ts")):
        return "ts"
    return "?"


def probe_kind():
    try:
        r = subprocess.run(["ffprobe", "-v", "error", "-rw_timeout", "20000000"] + HDR + ["-show_entries", "format=format_name", "-of", "csv=p=0", URL],
                           capture_output=True, text=True, timeout=60)
        names = (r.stdout or "").lower()
    except Exception:
        names = ""
    return "hls" if ("hls" in names or "applehttp" in names) else "ts"


def header_sets():
    sets = []
    if REFERER:
        o = _origin(REFERER)
        sets.append(("the referer you gave", ["-user_agent", UA, "-referer", REFERER] + (["-headers", "Origin: %s\r\n" % o] if o else [])))
    sets.append(("a normal browser User-Agent", ["-user_agent", UA]))
    o = _origin(URL)
    if o:
        sets.append(("browser headers with the stream's own site as referer", ["-user_agent", UA, "-referer", o + "/", "-headers", "Origin: %s\r\n" % o]))
    if kind_from_url() != "hls":
        sets.append(("a VLC player User-Agent", ["-user_agent", "VLC/3.0.20 LibVLC/3.0.20"]))   # IPTV servers often expect a player
        sets.append(("the default ffmpeg User-Agent", []))
    return sets


def precheck():
    global HDR
    last = ""
    for label, hdr in header_sets():
        try:
            r = subprocess.run(["ffmpeg", "-hide_banner", "-loglevel", "error"] + hdr + ["-t", "6", "-i", URL, "-f", "null", "-"],
                               capture_output=True, text=True, timeout=90)
        except Exception as e:
            last = str(e); continue
        if r.returncode == 0:
            HDR = hdr
            global KIND
            KIND = kind_from_url()
            if KIND == "?":
                KIND = probe_kind()
            forced = (E("STREAM_TYPE") or "auto").lower()
            if forced in ("hls", "ts"):
                KIND = forced
            print("Link opened using: %s | stream type: %s" % (label, "MPEG-TS (live)" if KIND == "ts" else "HLS (.m3u8)"), flush=True)
            return True, ""
        last = mask((r.stderr or "").strip())[-400:]
        print("Could not open with %s: %s" % (label, last.splitlines()[-1] if last else "?"), flush=True)
    return False, last


def ask_link():
    """URL = "ask": wait for the m3u8 link in Telegram, so a public repo never shows it."""
    global URL, ASKED
    r = tg("getUpdates", timeout=0)
    if r.get("error_code") == 409:
        print("::error title=Cannot read the link::A webhook is set on the bot. Paste the link in the Run workflow form instead.", flush=True)
        sys.exit(1)
    off = 0
    for u in r.get("result", []):
        off = u["update_id"] + 1
    say("🔗 <b>Send me the stream link</b> (.m3u8 or .ts address) as a normal message.\nI wait 15 minutes. The link stays only in this chat.")
    deadline = time.time() + 15 * 60
    while time.time() < deadline:
        r = tg("getUpdates", offset=off, timeout=20)
        for u in r.get("result", []):
            off = u["update_id"] + 1
            m = u.get("message") or {}
            if str((m.get("chat") or {}).get("id")) != str(CHAT):
                continue
            f = re.search(r"https?://\S+", m.get("text") or "")
            if f:
                URL = f.group(0).strip("<>\"'"); ASKED = True
                print("::add-mask::" + URL, flush=True)      # hide it in every log line from now on
                say("✅ <b>Link received.</b> Checking it...")
                return
        if not r:
            time.sleep(3)
    say("⏰ No link came in 15 minutes, so I stopped. Run the workflow again when you are ready.")
    print("::error title=No link received::Nothing was sent in 15 minutes.", flush=True)
    sys.exit(1)


def where():
    try:
        d = json.load(urllib.request.urlopen("https://ipinfo.io/json", timeout=8))
        return "%s, %s" % (d.get("city", "?"), d.get("country", "?"))
    except Exception:
        return "unknown"


def chain(rem_minutes):
    time.sleep(LIMIT - 300)
    if stop.is_set() or not shutil.which("gh"):
        return
    say("⏳ The 6 hour job limit is near. Starting the next run to continue...")
    if ASKED:
        say("🔁 A new run starts now. <b>Send the stream link again</b> when it asks, so the link is never shown on GitHub.")
    cmd = ["gh", "workflow", "run", "record.yml", "--repo", REPO, "-f", "url=" + ("ask" if ASKED else URL), "-f", "minutes=%d" % rem_minutes,
           "-f", "name=" + NAME, "-f", "part_min=%s" % PART_MIN, "-f", "part_mb=%d" % (PART_MAX / 1e6)]
    if REFERER:
        cmd += ["-f", "referer=" + REFERER]
    subprocess.run(cmd)


def why_exit(rc, lines):
    text = [l.strip() for l in lines if l.strip()]
    key = re.compile(r"error|failed|timed out|timeout|refused|forbidden|not found|invalid data|end of file|server returned|reset", re.I)
    hit = [l for l in text if key.search(l)]
    reason = mask((hit or text or ["no message"])[-1])[:180]
    return "exit code %s: %s" % (rc, reason)


def stderr_reader(p, box):
    for line in iter(p.stderr.readline, b""):
        box.append(line.decode("utf-8", "ignore"))
        del box[:-30]


def record():
    global SP
    os.makedirs(OUT, exist_ok=True)
    detect_chat()
    if URL.strip().lower() in ("", "ask", "telegram"):
        if not (TOKEN and CHAT) and not DRY:
            print("::error title=No Telegram chat::Send 'hi' to your bot first, then run again.", flush=True)
            sys.exit(1)
        ask_link()
    ok, err = precheck()
    if not ok:
        why = explain(err)
        print("PRECHECK FAILED. ffmpeg said:\n" + err, flush=True)
        print("::error title=Link could not be opened from GitHub::" + why, flush=True)
        summary("## Recording did not start\n**Reason:** " + why + "\n\n```\n" + err + "\n```")
        say("❌ <b>The link could not be opened from GitHub's server</b>\n<b>Reason:</b> %s\n\n<code>%s</code>" % (esc(why), esc(err[-300:])))
        sys.exit(1)
    plan = ("stops after %d min" % MINUTES) if MINUTES else "runs until you press Stop"
    kind_txt = "📡 <b>MPEG-TS live stream</b> (starts now, no rewind)" if KIND == "ts" else "📡 HLS stream"
    every = "every %s%s" % (human(PART_MAX), (" or %g min" % PART_MIN) if PART_MIN > 0 else "")
    say("🔴 <b>Recording started</b>\n🎬 %s\n%s\n⏱ %s\n✂️ New file %s (whichever comes first)\n📍 GitHub server: %s\nThe first download link comes after the first file is full." %
        (esc(NAME), kind_txt, plan, every, esc(where())), buttons=True)
    signal.signal(signal.SIGINT, lambda *a: halt())
    signal.signal(signal.SIGTERM, lambda *a: halt())
    total = MINUTES * 60
    if not total or total > LIMIT:
        threading.Thread(target=chain, args=(int((total - LIMIT) / 60) if total else 0,), daemon=True).start()
    if TOKEN and CHAT and not DRY:
        threading.Thread(target=poll, daemon=True).start()
    up = threading.Thread(target=uploader)
    up.start()
    SP = Splitter(upq.put)
    SP.on_manual = lambda n: say("✂️ <b>Split done</b>\nFile #%d started. Recording continues." % n, buttons=True)
    end_at = S["t0"] + (min(total, LIMIT) if total else LIMIT)

    # The reader (below) only moves bytes from ffmpeg into this queue. The splitter works on the other side.
    # So a slow disk, a busy CPU or an upload can never make the pipe full and the server drop the connection.
    rq = queue.Queue(maxsize=4000)

    def consumer():
        while True:
            it = rq.get()
            if it is None:
                return
            try:
                if it[0] == "d":
                    SP.feed(it[1])
                else:
                    SP.new_session(dedupe=it[1], verify=it[2])
            except Exception as e:
                print("splitter error:", repr(e), flush=True)
                SP.buf = b""
    ct = threading.Thread(target=consumer)
    ct.start()

    def watchdog():
        while not stop.is_set():
            if time.time() >= end_at:
                halt(); return
            if IDLE_STOP > 0 and time.time() - SP.last_es > IDLE_STOP * 60:
                say("⏹ <b>The stream sent no data for %g minutes</b>, so the match has probably ended.\nSaving what I have and ending the job to save your GitHub minutes." % IDLE_STOP)
                halt(); return
            time.sleep(2)
    threading.Thread(target=watchdog, daemon=True).start()

    def stream_monitor():
        warned, since = False, 0
        while not stop.is_set():
            idle = time.time() - SP.last_es
            if not warned and idle > 90:
                warned, since = True, time.time() - idle
                say("⚠️ <b>The stream has not sent data for %s.</b>\nStill trying. Short breaks are repaired automatically." % mmss(idle))
            elif warned and idle < 15:
                warned = False
                say("✅ <b>Stream is back</b> after %s. Recording continues in the same file." % mmss(time.time() - since))
            time.sleep(5)
    threading.Thread(target=stream_monitor, daemon=True).start()

    last_err = []; first = True; consec = 0
    while not stop.is_set():
        if KIND == "ts":
            # no ffmpeg-internal reconnect: after a drop a NEW ffmpeg starts quickly (small probe), and the splitter
            # joins the timeline, so a restarted server clock does not matter
            inopts = ["-fflags", "+discardcorrupt+genpts", "-rw_timeout", "20000000",
                      "-probesize", "2000000", "-analyzeduration", "1500000"]
        else:
            inopts = ["-fflags", "+discardcorrupt+genpts", "-rw_timeout", "60000000", "-reconnect", "1", "-reconnect_streamed", "1",
                      "-reconnect_delay_max", "15", "-seg_max_retry", "15", "-max_reload", "1000", "-m3u8_hold_counters", "1000",
                      "-http_persistent", "0", "-live_start_index", ("-" + BACK) if first else ("-" + RECON_BACK)]
        cmd = ["ffmpeg", "-hide_banner", "-loglevel", "warning", "-y"] + inopts + HDR + [
               "-i", URL, "-map", "0:v?", "-map", "0:a?", "-c", "copy", "-copyts", "-muxdelay", "0", "-muxpreload", "0",
               "-f", "mpegts", "-mpegts_flags", "+resend_headers", "pipe:1"]
        first = False
        t_run = time.time()
        p = S["proc"] = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, bufsize=0)
        if fcntl:
            try: fcntl.fcntl(p.stdout.fileno(), 1031, 1 << 20)       # F_SETPIPE_SZ: 1 MB pipe
            except Exception: pass
        last_err = []
        threading.Thread(target=stderr_reader, args=(p, last_err), daemon=True).start()
        while True:
            data = p.stdout.read(1 << 20)
            if not data:
                break
            rq.put(("d", data)); S["last_data"] = time.time()
            S["qmax"] = max(S["qmax"], rq.qsize())
        p.wait()
        if stop.is_set() or TEST_ONCE:
            break
        S["restarts"] += 1
        rq.put(("n", True, KIND == "ts"))                    # processed in order, after the data already queued
        S["reason"] = why_exit(p.returncode, last_err)
        consec = 0 if time.time() - t_run > 30 else consec + 1
        print("Reconnect %d (queue peak %d): %s" % (S["restarts"], S["qmax"], S["reason"]), flush=True)   # log only, no Telegram spam
        time.sleep(min(0.5 + 0.5 * consec, 5))
    rq.put(None)
    ct.join()
    SP.finish()
    upq.put(None)
    up.join()
    saved = sum(d["size"] for d in S["done"])
    page = S["page"]
    summary("## Recording finished\n%d file(s), %s. %s" % (len(S["done"]), human(saved), ("[Download page](%s)" % page) if page else ""))
    rows = "\n".join("%d.  %s  ·  %s" % (i + 1, human(d["size"]), mmss(d["secs"])) for i, d in enumerate(S["done"][:30]))
    say("🏁 <b>Recording finished</b>\n🎬 %s\n📁 %d file(s)  ·  %s\n⏱ %s\n\n%s%s" %
        (esc(NAME), len(S["done"]), human(saved), hms(time.time() - S["t0"]), rows,
         ('\n\n📂 <a href="%s">Download all files (one page)</a>' % page) if page else "\n\n⚠️ No file could be uploaded. See the run log."))


def finish():
    """always() step: upload leftovers if the main step was cancelled or killed."""
    leftovers = sorted(glob.glob(os.path.join(OUT, "*.ts")))
    if not leftovers:
        return
    for f in leftovers:
        process(f)
    say("⚠️ <b>Recording was interrupted.</b> Saved %d leftover file(s).%s" % (len(leftovers), ('\n📂 <a href="%s">Download page</a>' % S["page"]) if S["page"] else ""))


if __name__ == "__main__":
    finish() if len(sys.argv) > 1 and sys.argv[1] == "finish" else record()
