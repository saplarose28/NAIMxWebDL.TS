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
import hashlib, os, re, sys, math, json, glob, time, html, queue, signal, shutil, socket, threading, subprocess, urllib.request, urllib.parse, urllib.error
try:
    import fcntl
except ImportError:
    fcntl = None

E = os.environ.get
TOKEN, CHAT = E("TG_TOKEN", ""), E("TG_CHAT", "")
ALSO = [c.strip() for c in (E("TG_ALSO") or "").split(",") if c.strip()]   # extra chats that get a copy of every message (e.g. the owner)
WORKER_URL = (E("WORKER_URL") or "").rstrip("/")   # optional Cloudflare Worker: gives us the link and the Stop/Status/Split presses
WORKER_KEY = E("WORKER_KEY") or ""
TICKET = (E("TICKET") or "").strip()               # the worker keeps the stream link under this ticket, so it never shows on GitHub
REPO, RUN = E("REPO", ""), E("RUN_ID", "local")
URL = E("URL", "")
NAME = re.sub(r"[^\w\-]+", "_", E("NAME") or "ClipByNaim")
MINUTES = float(E("MINUTES") or 0)             # 0 = until Stop
PART_MIN = float(E("PART_MIN") or 0)            # optional: also split every N minutes (0 = off, split by size only)
PART_MAX = min(float(E("PART_MB") or 4000), 5000) * 1e6   # a new file every N MB (4000 = 4 GB)
PARALLEL = int(E("PARALLEL") or 16)             # heavy archive links: this many parallel connections (0 or 1 = off)
LIVE_PAR = E("LIVE_PAR") or "auto"             # live .m3u8: auto = parallel parts only if the normal way would skip some; 1 = always, 0 = never
HEAVY_MB = float(E("HEAVY_MB") or 300)          # a .ts archive at least this big counts as heavy
HEAVY_MIN = float(E("HEAVY_MIN") or 15)         # an .m3u8 archive at least this long (minutes) counts as heavy
BACK = E("BACK_SEGS") or "5"                    # start N segments behind live (safety)
PROXY = (E("PROXY") or "").strip()              # optional: http://user:pass@host:port - the stream is fetched through this proxy (e.g. a Bangladesh IP)
MODE = (E("MODE") or "auto").strip().lower()     # auto (finds out itself), live, or archive (a finished file: timeshift / catch-up .ts or .m3u8)
TEST_KILL_MB = float(E("TEST_KILL_MB") or 0)      # test only: cut the first HLS download after N MB to test resuming
ARCHIVE = False
TS_RAW = E("TS_RAW") != "0"                     # direct .ts links: download the bytes ourselves (no ffmpeg start/probe delay on reconnect)
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
LIMIT = float(E("LIMIT_MIN") or 345) * 60         # one GitHub job runs ~6 h (345 min); on your own phone/PC set LIMIT_MIN=1440 or more
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
D = {"got": 0, "total": None, "secs": 0.0, "dur": None}   # archive download progress
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
    t = (t or "").replace(URL, "<link>") if URL else (t or "")
    return t.replace(PROXY, "<proxy>") if PROXY else t


def fenv():
    """Environment for ffmpeg/ffprobe: only they get the proxy (Telegram and Gofile never go through it)."""
    e = dict(os.environ)
    for k in ("http_proxy", "https_proxy", "HTTP_PROXY", "HTTPS_PROXY", "no_proxy", "NO_PROXY"):
        e.pop(k, None)
    if PROXY:
        e["http_proxy"] = PROXY; e["https_proxy"] = PROXY
    return e


def stream_opener():
    """urllib opener for the stream: through PROXY if set, otherwise direct."""
    return urllib.request.build_opener(urllib.request.ProxyHandler({"http": PROXY, "https": PROXY} if PROXY else {}))


def _origin(u):
    m = re.match(r"^(https?://[^/]+)", u or "")
    return m.group(1) if m else ""


RUN = os.environ.get("GITHUB_RUN_ID", "")     # every run signs its own buttons, so two recordings never get mixed up
_s = ("@" + RUN) if RUN else ""
KB = {"inline_keyboard": [[{"text": "📊 Status", "callback_data": "status" + _s},
                           {"text": "✂️ Split", "callback_data": "split" + _s},
                           {"text": "⏹ Stop", "callback_data": "stop" + _s}]]}


def tg(method, **data):
    if not TOKEN or DRY:
        print("[telegram]", method, re.sub(r"<[^>]+>", "", str(data.get("text", ""))).replace("\n", " | "))
        return {}
    try:
        req = urllib.request.Request("%s/bot%s/%s" % (E("TG_API") or "https://api.telegram.org", TOKEN, method), urllib.parse.urlencode(data).encode())
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
        print("[msg]", re.sub(r"<[^>]+>", "", re.sub(r'<a href="([^"]+)">([^<]*)</a>', r"\2 \1", text)))
        return
    for cid in dict.fromkeys([c for c in [CHAT] + ALSO if c]):
        d = dict(chat_id=cid, text=text, parse_mode="HTML", disable_web_page_preview="true")
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


def nal_key(pk, vtype):
    """Many servers do not set the random-access flag. Then look into the first packet of the picture for a keyframe
    marker: H.264 SPS/IDR, HEVC VPS/SPS/IRAP, MPEG-2 sequence header / I picture."""
    p = 4
    if (pk[3] >> 4) & 2:
        p += 1 + pk[4]
    if p + 10 >= 188 or pk[p] != 0 or pk[p + 1] != 0 or pk[p + 2] != 1:
        return False
    d = pk[p + 9 + pk[p + 8]:]
    i = 0
    while True:
        j = d.find(b"\x00\x00\x01", i)
        if j < 0 or j + 4 >= len(d):
            return False
        b = d[j + 3]
        if vtype == 0x1b and (b & 0x1f) in (5, 7):
            return True
        if vtype == 0x24 and ((b >> 1) & 0x3f) in (16, 17, 18, 19, 20, 21, 32, 33):
            return True
        if vtype in (0x02, 0x10) and (b == 0xB3 or (b == 0x00 and ((d[j + 5] >> 3) & 7) == 1)):
            return True
        i = j + 3


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
        self.gap_total = 0.0
        self.skip = None; self.dropping = set(); self.drop_bytes = 0; self.deduped = 0; self.last_write = time.time(); self.last_es = time.time()
        self.need_key = False; self.need_key_until = 0
        self.vtype = None; self.nokey_pes = 0; self.nokey_warned = False
        self.first_pts = None
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

    def media_total(self):
        if self.first_pts is None or self.last_pts is None:
            return 0.0
        return ((self.last_pts - self.first_pts) % (1 << 33)) / 90000.0

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
                self.vid = ((pk[q + 1] & 31) << 8) | pk[q + 2]; self.vtype = pk[q]
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
        buf = self.buf; n = len(buf); i = 0
        while i < n:                                      # find a start where the sync bytes line up (raw streams can begin mid-packet)
            if buf[i] == 0x47 and all(buf[i + 188 * j] == 0x47 for j in (1, 2) if i + 188 * j < n):
                break
            i += 1
        end = i + ((n - i) // 188) * 188
        for o in range(i, end, 188):
            pk = buf[o:o + 188]
            if pk[0] != 0x47:                             # lost sync: look for it again in the next data
                end = o + 1; break
            pid = ((pk[1] & 0x1f) << 8) | pk[2]
            if pid == 0x1fff or (pk[1] & 0x80):
                continue                                  # drop empty padding packets and damaged packets
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
                if pid == self.vid and pusi and (((pk[3] >> 4) & 2 and pk[4] > 0 and (pk[5] & 0x40)) or nal_key(pk, self.vtype)):
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
                                if dd > 0:
                                    self.gap_total += dd / 90000.0
                                print("Clock jump %+.1fs: timeline joined smoothly (join #%d)" % (dd / 90000.0, self.rebased), flush=True)
                        elif 0 < dd <= 18000:
                            self.fdur = dd                # normal picture spacing, used to place the first picture after a join
                    self.last_pts = (pts + self.off) & M33
                    if self.first_pts is None:
                        self.first_pts = self.last_pts
                    self.last_out_v = (dts + self.off) & M33
                    self.last_wr["v"] = dts               # raw value, used to skip repeated data after a reconnect
                    self.recent[dts] = vsig(pk)
                    if len(self.recent) > 3000:
                        del self.recent[next(iter(self.recent))]
                if (pk[3] >> 4) & 2 and pk[4] > 0 and (pk[5] & 0x40):
                    key = True                            # random access indicator = keyframe starts here
                elif nal_key(pk, self.vtype):
                    key = True                            # the server sets no flag: the picture data itself shows a keyframe
                elif self.f is None and self.pat and self.pmt:
                    self.nokey_pes += 1                   # no marker at all for a long time: start at an ordinary picture, never lose the whole recording
                    if self.nokey_pes > 400:
                        key = True
                        if not self.nokey_warned:
                            self.nokey_warned = True
                            print("No keyframe marker found in the stream: the file starts at an ordinary picture", flush=True)
                elif self.f is not None and self.cur_bytes >= PART_MAX + 64_000_000:
                    key = True                            # never a keyframe marker and the file is too big: cut here
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
    """Status button: the same box panel plus time left and the next auto-split."""
    el = time.time() - S["t0"]
    left = max(0, MINUTES * 60 - el) if MINUTES else None
    sp = SP
    spd = sp.speed_mbps() if sp else 0
    extra = []
    if left is not None:
        extra.append("⏳ Limit left <code>%s</code>" % hms(left))
    if sp and sp.f and not ARCHIVE:
        t_left = (PART_MIN * 60 - sp.media_secs()) if PART_MIN > 0 else 1e12
        if spd > 0.1:
            t_left = min(t_left, (PART_MAX - sp.cur_bytes) * 8 / (spd * 1e6))
        if t_left < 1e11:
            extra.append("✂️ Next split <code>~%s</code> (at %s)" % (mmss(t_left), human(PART_MAX)))
    if S["reason"] and S["restarts"]:
        extra.append("<code>%s</code>" % esc(S["reason"][:160]))
    lines = live_text(int(time.time() / 3), stop.is_set(), HIST).split("\n")
    lines[-3:-3] = ["│ " + x for x in extra]
    return "\n".join(lines)



SPIN = "⠋⠙⠹⠸⠼⠴⠦⠧⠇⠏"
WAVE = "▁▂▃▄▅▆▇█▇▆▅▄▃▂"
LINE = "━" * 18


def bar(frac, n=20, head=True):
    k = max(0, min(n, int(frac * n)))
    if head and 0 < k < n:
        return "█" * (k - 1) + "▓" + "░" * (n - k)
    return "█" * k + "░" * (n - k)


def spark(vals):
    if not vals:
        return ""
    hi = max(max(vals), 0.1)
    return "".join(WAVE[:8][min(7, int(v / hi * 7.99))] for v in vals)


def clock(t=None):
    return time.strftime("%H:%M:%S", time.gmtime((t or time.time()) + float(E("TZ_HOURS") or 6) * 3600))


NAIM = "ℕ𝕒𝕚𝕞𝕏"
FIRE = ["🔥", "💥", "⚡", "🔥"]


def naim_sig(i):
    """The moving NaimX signature: a cursor runs through the letters, then a short glitch."""
    e = FIRE[i % len(FIRE)]
    return "%s <b>%s</b> %s" % (e, NAIM, e)


def note_box(title, *lines):
    V = "│ "
    return "\n".join([BOX_TOP, V + title + "  ·  <b>%s</b>" % esc(NAME), BOX_MID] + [V + x for x in lines]
                     + [BOX_MID, "%s%s  🕒 %s" % (V, naim_sig(int(time.time())), clock()), BOX_END])


def pbar(frac, n=20):
    return bar(frac, n)


BOX_TOP = "╭" + "─" * 22 + "╮"
BOX_MID = "├" + "─" * 22 + "┤"
BOX_END = "╰" + "─" * 22 + "╯"


def live_text(i, ended=False, hist=()):
    """Box style text panel, edited every few seconds (used when pictures are off or cannot be drawn)."""
    el = time.time() - S["t0"]
    sp = SP
    spd = sp.speed_mbps() if sp else 0
    saved = sum(d["size"] for d in S["done"])
    dot = "🔴" if i % 2 == 0 else "⭕"
    if ended:
        title = "✅ <b>𝗙𝗜𝗡𝗜𝗦𝗛𝗘𝗗</b>"
    elif ARCHIVE:
        title = "⬇️ <b>𝗗𝗢𝗪𝗡𝗟𝗢𝗔𝗗</b> %s" % SPIN[i % len(SPIN)]
    else:
        title = "%s <b>𝗟𝗜𝗩𝗘 𝗥𝗘𝗖</b> %s" % (dot, SPIN[i % len(SPIN)])
    V = "│ "
    L = [BOX_TOP, "%s%s  ·  <b>%s</b>" % (V, title, esc(NAME)), BOX_MID]
    if ARCHIVE:
        frac, eta, txt = None, None, ""
        if KIND == "ts" and D["total"]:
            frac = D["got"] / max(1, D["total"])
            txt = "%s / %s" % (human(D["got"]), human(D["total"]))
            if spd > 0.1:
                eta = (D["total"] - D["got"]) * 8 / (spd * 1e6)
        elif D["dur"]:
            frac = D["secs"] / max(1, D["dur"])
            txt = "%s done · %s left" % (mmss(D["secs"]), mmss(max(0, D["dur"] - D["secs"])))
            if D["secs"] > 5:
                eta = (D["dur"] - D["secs"]) * el / D["secs"]
        if frac is not None:
            frac = min(1.0, frac)
            L.append("%s⬇️ Download  <code>%s</code> <b>%d%%</b>" % (V, pbar(frac), int(frac * 100)))
            L.append("%s💾 Done      <code>%s</code>" % (V, txt))
            if eta and not ended:
                L.append("%s⏳ Left      <code>~%s</code> · ends <b>%s</b>" % (V, hms(eta), clock(time.time() + eta)))
    elif sp:
        f = min(1.0, sp.cur_bytes / PART_MAX) if PART_MAX else 0
        tot = sum(x.get("secs", 0) for x in S["done"]) + sp.media_secs()
        L += ["%s📁 File %02d    <code>%s</code> <b>%d%%</b>" % (V, sp.part_no, pbar(f), int(f * 100)),
              "%s💾 Size       <code>%s / %s</code>" % (V, human(sp.cur_bytes), human(PART_MAX)),
              "%s🎞 Video      <code>%s</code> (total <code>%s</code>)" % (V, mmss(sp.media_secs()), hms(tot))]
    L.append("%s⚡ Speed      <code>%.1f Mbps</code>" % (V, spd))
    if hist and not ended:
        L.append("%s<code>%s</code>" % (V, spark(hist)))
    L.append("%s⏱ Time       <code>%s</code>" % (V, hms(el)))
    if sp and not ARCHIVE and not ended:
        idle = time.time() - sp.last_es
        L.append("%s%s" % (V, "🟢 Stream     online" if idle < 10 else ("🟡 Stream     waiting %ds" % idle if idle < 60 else "🔴 Stream     no data %s" % mmss(idle))))
    L.append("%s💿 Saved      <code>%d file(s) · %s</code>" % (V, len(S["done"]), human(saved)))
    if S["restarts"]:
        L.append("%s🔁 Reconnect  <code>%d</code> (no data lost)" % (V, S["restarts"]))
    if S["page"]:
        L.append('%s📂 <a href="%s">Open the download page</a>' % (V, S["page"]))
    L += [BOX_MID, "%s%s  🕒 %s" % (V, naim_sig(i), clock()), BOX_END]
    return "\n".join(L)



_PIL = []


PIC_WHY = []
_PIC_TOLD = []


def pic_off(why):
    """Tell the person (once) why the dashboard is text instead of a picture."""
    print("Picture dashboard off: %s" % why, flush=True)
    if not _PIC_TOLD:
        _PIC_TOLD.append(1)
        say("ℹ️ Picture dashboard is off, showing text instead.\nReason: <code>%s</code>" % esc(str(why)[:200]))


def _pil():
    """Pillow draws the picture card. Installed on the fly if the runner does not have it; None = use the text panel."""
    if _PIL:
        return _PIL[0]
    mods = None
    for attempt in (0, 1):
        try:
            from PIL import Image, ImageDraw, ImageFont
            mods = (Image, ImageDraw, ImageFont)
            break
        except Exception:
            if attempt == 0:
                try:
                    pr = subprocess.run([sys.executable, "-m", "pip", "install", "-q", "--break-system-packages", "pillow"],
                                        timeout=150, capture_output=True)
                    PIC_WHY[:] = [(pr.stderr or pr.stdout or b"").decode("utf-8", "ignore").strip()[-160:]]
                except Exception as e:
                    PIC_WHY[:] = [repr(e)[:160]]
            else:
                PIC_WHY[:] = PIC_WHY or ["import failed"]
    _PIL.append(mods)
    return mods


def _font(ImageFont, size, bold=False):
    import glob
    names = (["DejaVuSans-Bold.ttf", "LiberationSans-Bold.ttf", "FreeSansBold.ttf", "NotoSans-Bold.ttf"] if bold else
             ["DejaVuSans.ttf", "LiberationSans-Regular.ttf", "FreeSans.ttf", "NotoSans-Regular.ttf"])
    for f in names:
        for d in ("/usr/share/fonts/truetype/dejavu/", "/usr/share/fonts/truetype/liberation/", "/usr/share/fonts/dejavu/", ""):
            try:
                return ImageFont.truetype(d + f, size)
            except Exception:
                continue
    for f in sorted(glob.glob("/usr/share/fonts/**/*.ttf", recursive=True)):      # any font on the machine
        try:
            return ImageFont.truetype(f, size)
        except Exception:
            continue
    try:
        return ImageFont.load_default(size=size)                                # Pillow 10.1+: a scalable built-in font
    except Exception:
        return ImageFont.load_default()


POPPINS = "https://github.com/google/fonts/raw/main/ofl/poppins/Poppins-%s.ttf"
FONT_DIR = E("FONT_DIR") or "/tmp/recfonts"
_FFAIL = set()


def _poppins(weight):
    """Path of a Poppins font file. Downloaded once from GitHub when missing; None = use the normal font."""
    name = "Poppins-%s.ttf" % weight
    for dd in (FONT_DIR, "/usr/share/fonts/truetype/google-fonts"):
        p = os.path.join(dd, name)
        try:
            if os.path.getsize(p) > 50000:
                return p
        except OSError:
            pass
    if weight in _FFAIL:
        return None
    try:
        os.makedirs(FONT_DIR, exist_ok=True)
        req = urllib.request.Request(POPPINS % weight, headers={"User-Agent": "Mozilla/5.0"})
        data = urllib.request.urlopen(req, timeout=20).read()
        if len(data) > 50000 and data[:4] in (b"\x00\x01\x00\x00", b"true", b"OTTO"):
            p = os.path.join(FONT_DIR, name)
            with open(p, "wb") as f:
                f.write(data)
            return p
    except Exception as e:
        print("font download (%s): %s" % (weight, repr(e)[:80]), flush=True)
    _FFAIL.add(weight)
    return None


def _pf(ImageFont, size, weight="Bold"):
    p = _poppins(weight)
    if p:
        try:
            return ImageFont.truetype(p, size)
        except Exception:
            pass
    return _font(ImageFont, size, weight in ("Bold", "BoldItalic"))


def _hue(Image, ImageChops, w, h, shift):
    """A rainbow (RGB) gradient image; shift moves the colours along."""
    ramp = Image.linear_gradient("L").rotate(90).resize((w, h))
    ramp = ImageChops.offset(ramp, int((shift % 1.0) * w), 0)
    one = Image.new("L", (w, h), 255)
    return Image.merge("HSV", (ramp, one, one)).convert("RGB")


def live_card(i, ended=False, hist=(), note=None):
    """The picture dashboard (RGB ring + big rows). One design for live, archive, finished and the Status/Split/Stop answers."""
    mods = _pil()
    if not mods:
        return None
    Image, ImageDraw, ImageFont = mods
    from PIL import ImageChops, ImageFilter
    import io
    K, W, H = 2, 1000, 600
    shift = (i * 0.06) % 1.0
    img = Image.new("RGB", (W * K, H * K), (6, 5, 14))
    G = _hue(Image, ImageChops, W * K, H * K, shift)
    img = ImageChops.add(img, G.point(lambda v: int(v * 0.07)))
    d = ImageDraw.Draw(img)
    M = Image.new("L", (W * K, H * K), 0)                       # everything that gets the rainbow colour
    md = ImageDraw.Draw(M)
    P = lambda sz, w="Bold": _pf(ImageFont, sz * K, w)
    white, muted, mid, track = (255, 255, 255), (150, 155, 200), (190, 195, 230), (26, 24, 44)
    later = []                                                  # white text is drawn after the glow, so it stays white

    def MT(x, y, t, f, a="la"): md.text((x * K, y * K), t, font=f, fill=255, anchor=a)
    def LT(x, y, t, f, c=white, a="la"): later.append(lambda: d.text((x * K, y * K), t, font=f, fill=c, anchor=a))
    def spaced(x, y, t, f, c, sp=5, a="l"):
        wid = sum(d.textlength(ch, font=f) / K for ch in t) + sp * (len(t) - 1)
        cx = x - (wid if a == "r" else wid / 2 if a == "c" else 0)
        for ch in t:
            later.append(lambda ch=ch, cx=cx: d.text((cx * K, y * K), ch, font=f, fill=c))
            cx += d.textlength(ch, font=f) / K + sp

    el = time.time() - S["t0"]
    sp = SP
    spd = sp.speed_mbps() if sp else 0
    saved = sum(x["size"] for x in S["done"])
    rec_secs = sum(x.get("secs", 0) for x in S["done"]) + (sp.media_secs() if (sp and not ended) else 0)
    frac, sub, under, rows = 0.0, "", "", []
    if ended:
        title = "FINISHED"
        rows = [("TOTAL TIME", hms(el), 64), ("FILES", "%d file%s" % (len(S["done"]), "" if len(S["done"]) == 1 else "s"), 64),
                ("TOTAL SIZE", human(saved), 40), ("DOWNLOADED" if ARCHIVE else "RECORDED", hms(rec_secs), 40)]
        frac = 1.0
    elif ARCHIVE:
        title = "DOWNLOADING"
        eta, got = None, human(D["got"])
        if KIND == "ts" and D["total"]:
            frac = D["got"] / max(1, D["total"])
            got = "%s / %s" % (human(D["got"]), human(D["total"]))
            if spd > 0.1:
                eta = (D["total"] - D["got"]) * 8 / (spd * 1e6)
        elif D["dur"]:
            frac = D["secs"] / max(1, D["dur"])
            got = "%s / %s" % (mmss(D["secs"]), mmss(D["dur"]))
            if D["secs"] > 5:
                eta = (D["dur"] - D["secs"]) * el / D["secs"]
        sub = "DOWNLOADED"
        under = ("ends ~%s" % clock(time.time() + eta)) if eta else ""
        rows = [("TIME LEFT", ("~" + hms(eta)) if eta else "--", 64), ("SPEED", "%.1f" % spd, 64),
                ("DOWNLOADED", got, 40), ("ELAPSED", hms(el), 40)]
    else:
        title = "LIVE"
        frac = min(1.0, sp.cur_bytes / PART_MAX) if (sp and PART_MAX) else 0.0
        sub = "FILE #%02d" % (sp.part_no if sp else 0)
        if sp and sp.f:
            t_left = (PART_MIN * 60 - sp.media_secs()) if PART_MIN > 0 else 1e12
            if spd > 0.1:
                t_left = min(t_left, (PART_MAX - sp.cur_bytes) * 8 / (spd * 1e6))
            if t_left < 1e11:
                under = "split in ~%s" % mmss(t_left)
        rows = [("RECORDED", hms(rec_secs), 64), ("SPEED", "%.1f" % spd, 64),
                ("FILE #%02d" % (sp.part_no if sp else 0), "%s / %s" % (human(sp.cur_bytes) if sp else "0 MB", human(PART_MAX)), 40),
                ("SAVED", "%d file%s · %s" % (len(S["done"]), "" if len(S["done"]) == 1 else "s", human(saved)), 40)]
    frac = max(0.0, min(1.0, frac))

    # ring
    cx, cy, r, rw = 235, 322, 170, 38
    box = ((cx - r) * K, (cy - r) * K, (cx + r) * K, (cy + r) * K)
    d.arc(box, 0, 360, fill=track, width=rw * K)
    for a in range(0, 360, 15):
        ca, sa = math.cos(math.radians(a)), math.sin(math.radians(a))
        d.line(((cx + (r + 30) * ca) * K, (cy + (r + 30) * sa) * K, (cx + (r + 40) * ca) * K, (cy + (r + 40) * sa) * K), fill=(50, 48, 80), width=3 * K)
    if frac > 0.004:
        md.arc(box, -90, -90 + 360 * frac, fill=255, width=rw * K)
    if ended:
        md.line([(cx * K - 62 * K, cy * K + 4 * K), (cx * K - 18 * K, cy * K + 46 * K), (cx * K + 66 * K, cy * K - 52 * K)], fill=255, width=20 * K, joint="curve")
        spaced(cx, cy + 66, "COMPLETE", P(22, "Medium"), mid, 4, "c")
    else:
        txt = "%d" % int(frac * 100)
        nw = d.textlength(txt, font=P(140)) / K
        LT(cx - 22, cy - 16, txt, P(140), white, "mm")
        LT(cx - 22 + nw / 2 + 4, cy + 20, "%", P(54), mid, "lm")
        spaced(cx, cy + 64, sub, P(20, "Medium"), muted, 4, "c")
        if under:
            LT(cx, cy + 100, under, P(22, "Medium"), mid, "mm")

    # header
    if note:
        nt, nc = note
        fw = P(22)
        tw = d.textlength(nt, font=fw) / K
        d.rounded_rectangle((40 * K, 22 * K, (40 + tw + 40) * K, 66 * K), radius=22 * K, fill=nc)
        d.text(((40 + tw / 2 + 20) * K, 44 * K), nt, font=fw, fill=(12, 14, 30), anchor="mm")
    md.ellipse((502 * K, 34 * K, 530 * K, 62 * K), fill=255)
    MT(546, 20, title, P(52 if len(title) < 9 else 40), "la")
    nm = NAME if len(NAME) <= 30 else NAME[:29] + "…"
    LT(500, 82, nm, P(24, "Medium"), (235, 235, 250))

    # rows
    y = 118
    for k, (lab, val, fs) in enumerate(rows):
        spaced(500, y, lab, P(19, "Medium"), muted, 5)
        base = y + 34 + fs * 0.74
        LT(500, base, val, P(fs), white, "ls")
        if lab == "SPEED":
            vw = d.textlength(val, font=P(fs)) / K
            LT(500 + vw + 10, base, "Mbps", P(28), mid, "ls")
            vals = list(hist)[-10:]
            if len(vals) >= 2 and not ended:
                mx = max(max(vals), 0.5)
                for n_, v in enumerate(vals):
                    bh = max(4, int(v / mx * 44))
                    md.rounded_rectangle(((800 + n_ * 15) * K, (y + 90 - bh) * K, (808 + n_ * 15) * K, (y + 90) * K), radius=3 * K, fill=255)
        md.rounded_rectangle((500 * K, (y + 98) * K, 952 * K, (y + 102) * K), radius=2 * K, fill=255)
        y += 102

    # footer
    foot = ("Reconnects %d (no data lost)" % S["restarts"]) if S["restarts"] else "No reconnects"
    foot += "   ·   " + ("finished %s" % clock() if ended else "updated %s" % clock())
    LT(40, 584, foot, P(18, "Medium"), muted, "lm")
    MT(952, 592, "NaimX", P(76, "BoldItalic"), "rs")

    glow = M.filter(ImageFilter.GaussianBlur(13 * K)).point(lambda v: int(v * 0.8))
    img.paste(G, (0, 0), glow)
    img.paste(G, (0, 0), M)
    d = ImageDraw.Draw(img)
    for f_ in later:
        f_()
    out = img.resize((W, H), Image.LANCZOS)
    b = io.BytesIO()
    out.save(b, "PNG")
    return b.getvalue()


def live_caption(ended=False):
    L = ["✅ <b>Finished</b>" if ended else ("⬇️ <b>Downloading</b>" if ARCHIVE else "🔴 <b>Recording</b>"), "🎬 %s" % esc(NAME)]
    if ARCHIVE and not ended and KIND == "ts" and D["total"] and SP and SP.speed_mbps() > 0.1:
        eta = (D["total"] - D["got"]) * 8 / (SP.speed_mbps() * 1e6)
        L.append("⏳ ~%s left  ·  done around <b>%s</b>" % (hms(eta), clock(time.time() + eta)))
    if S["page"]:
        L.append('📂 <a href="%s">Open the download page</a>' % S["page"])
    return "\n".join(L)


def tg_photo(method, fields, png):
    """multipart upload of the card (sendPhoto / editMessageMedia)."""
    if not TOKEN or DRY:
        return {}
    bd = "----rec%x" % int(time.time() * 1000)
    body = b""
    for k, v in fields.items():
        body += ("--%s\r\nContent-Disposition: form-data; name=\"%s\"\r\n\r\n%s\r\n" % (bd, k, v)).encode()
    fld = "photo" if method == "sendPhoto" else "card"      # sendPhoto wants the file in a field named photo; editMessageMedia points to it with attach://card
    body += ("--%s\r\nContent-Disposition: form-data; name=\"%s\"; filename=\"card.png\"\r\nContent-Type: image/png\r\n\r\n" % (bd, fld)).encode() + png + ("\r\n--%s--\r\n" % bd).encode()
    try:
        req = urllib.request.Request("%s/bot%s/%s" % (E("TG_API") or "https://api.telegram.org", TOKEN, method), body,
                                     {"Content-Type": "multipart/form-data; boundary=" + bd})
        return json.load(urllib.request.urlopen(req, timeout=60))
    except urllib.error.HTTPError as e:
        try: print("Telegram error %s: %s" % (e.code, e.read().decode()[:200]), flush=True)
        except Exception: pass
        return {"ok": False, "error_code": e.code}
    except Exception as e:
        print("telegram error:", e)
        return {}


HIST = []


def pic_reply(note, caption):
    """Status / Split / Stop answer as a picture card (falls back to text when pictures are off)."""
    if E("LIVE_CARD") == "0" or DRY:
        return False
    try:
        png = live_card(int(time.time() / 3), False, HIST, note)
    except Exception as e:
        print("pic reply:", repr(e)[:120], flush=True)
        return False
    if not png:
        return False
    kb = json.dumps({"inline_keyboard": []} if stop.is_set() else KB)
    ok = False
    for cid in dict.fromkeys([c for c in [CHAT] + ALSO if c]):
        r = tg_photo("sendPhoto", {"chat_id": cid, "caption": caption, "parse_mode": "HTML", "reply_markup": kb}, png)
        ok = ok or bool(r.get("ok"))
    return ok


def live_loop():
    cids = list(dict.fromkeys([c for c in [CHAT] + ALSO if c]))
    if not cids:
        return
    ids, bad, hist = {}, {}, []
    use_img = E("LIVE_CARD") != "0" and bool(_pil())    
    print("Live panel: %s" % ("picture card" if use_img else "text"), flush=True)
    if E("LIVE_CARD") == "0":
        pass
    elif not use_img:
        pic_off("Pillow could not be loaded. %s" % ((PIC_WHY or [""])[0]))
    i = 0
    while True:
        ended = stop.is_set()
        png = text = None
        try:
            hist = (hist + [SP.speed_mbps() if SP else 0.0])[-16:]
            HIST[:] = hist
            if use_img:
                png = live_card(i, ended, hist)
            if not png:
                text = live_text(i, ended, hist)
        except Exception as e:
            print("live panel:", repr(e)[:120], flush=True)
            if use_img:
                pic_off("card drawing failed: %s" % repr(e)[:120])
                use_img = False; ids.clear(); bad.clear()           # picture failed: use the text panel instead
            if ended:
                return
            time.sleep(5); i += 1; continue
        kb = json.dumps({"inline_keyboard": []} if ended else KB)
        for cid in cids:
            if bad.get(cid, 0) >= 3:
                continue
            if png:
                cap = live_caption(ended)
                if cid in ids:
                    r = tg_photo("editMessageMedia", {"chat_id": cid, "message_id": ids[cid], "reply_markup": kb,
                                 "media": json.dumps({"type": "photo", "media": "attach://card", "caption": cap, "parse_mode": "HTML"})}, png)
                else:
                    r = tg_photo("sendPhoto", {"chat_id": cid, "caption": cap, "parse_mode": "HTML", "reply_markup": kb}, png)
            else:
                d = dict(chat_id=cid, text=text, parse_mode="HTML", disable_web_page_preview="true", reply_markup=kb)
                if cid in ids:
                    d["message_id"] = ids[cid]
                r = tg("editMessageText" if cid in ids else "sendMessage", **d)
            if r.get("error_code") == 429:
                time.sleep(20)
            elif r.get("error_code"):
                bad[cid] = bad.get(cid, 0) + 1
                if r.get("error_code") == 400:
                    ids.pop(cid, None)                              # message deleted: send a new one
                if bad[cid] >= 3 and use_img and not ids:
                    pic_off("Telegram refused the picture (error %s)" % r.get("error_code"))
                    use_img = False; ids.clear(); bad.clear()       # picture keeps failing: switch to text
                    break
            else:
                bad[cid] = 0
                mid = (r.get("result") or {}).get("message_id")
                if mid and cid not in ids:
                    ids[cid] = mid
        if ended:
            return
        i += 1
        for _ in range(20 if use_img else 10):
            if stop.is_set():
                break
            time.sleep(0.5)


def do_action(act, cq_id=None):
    global SP
    act = (act or "").split("@")[0]
    if act == "status":
        txt = "Status sent"
        if not pic_reply(("STATUS", (80, 165, 255)), "📊 <b>Status</b> · %s" % esc(NAME)):
            say(status_text(), buttons=True)
    elif act == "split":
        if SP and SP.f:
            SP.want_split = True; txt = "Split requested"
            if not pic_reply(("SPLIT REQUESTED", (255, 190, 60)), "✂️ <b>Split requested</b>\nThe file closes at the next keyframe. Recording continues in a new file."):
                say(note_box("✂️ <b>𝗦𝗣𝗟𝗜𝗧</b>", "The file closes at the next keyframe (a few seconds).", "Recording continues in a new file."), buttons=True)
        else:
            txt = "Not recording yet"; say("Recording has not started yet, nothing to split.")
    elif act == "stop":
        txt = "Stopping"
        if not pic_reply(("STOPPING", (255, 77, 94)), "⏹ <b>Stopping...</b>\nSaving the last file. This can take up to a minute."):
            say(note_box("⏹ <b>𝗦𝗧𝗢𝗣𝗣𝗜𝗡𝗚</b>", "Saving the last file.", "This can take up to a minute."))
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
    r = S.get("resp")
    if r is not None:                                 # raw .ts download: cut the connection so the read stops now
        try: r.fp.raw._sock.shutdown(socket.SHUT_RDWR)
        except Exception: pass


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


def remux(ts, mp4):
    """.ts -> .mp4 without re-encoding. Tries a few ways because some streams carry data tracks or audio that mp4 cannot hold."""
    tries = [["-map", "0:v?", "-map", "0:a?", "-c", "copy"],
             ["-map", "0:v?", "-map", "0:a?", "-c:v", "copy", "-c:a", "aac", "-b:a", "160k"],
             ["-c", "copy"]]
    first = ""
    for extra in tries:
        r = subprocess.run(["nice", "-n", "10", "ffmpeg", "-hide_banner", "-loglevel", "error", "-y", "-i", ts] + extra +
                           ["-avoid_negative_ts", "make_zero", "-movflags", "+faststart", mp4], capture_output=True, text=True)
        if r.returncode == 0 and os.path.exists(mp4) and os.path.getsize(mp4) > 0:
            return True, ""
        if not first:
            lines = [l for l in (r.stderr or "").strip().splitlines() if l.strip()]
            first = lines[-1] if lines else "ffmpeg exit code %s" % r.returncode
        try: os.remove(mp4)
        except OSError: pass
    return False, first


def process(ts):
    """remux the finished .ts to .mp4 (proper duration), upload it, tell Telegram, clean up."""
    os.makedirs(MP4_DIR, exist_ok=True)
    base = os.path.basename(ts)[:-3] + ".mp4"
    mp4 = os.path.join(MP4_DIR, base)
    ok_mp4, why = remux(ts, mp4)
    note = ""
    if not ok_mp4:
        print("MP4 conversion failed, uploading the .ts instead:", why, flush=True)
        note = "\n⚠️ MP4 conversion failed, so this is the .ts file (it plays the same).\n<code>%s</code>" % esc(why[:150])
        mp4 = ts; base = os.path.basename(ts)
    elif not DRY:
        try: os.remove(ts)                           # free disk space right away
        except OSError: pass
    size = os.path.getsize(mp4)
    dur = media_info(mp4)[0]
    n = len(S["done"]) + 1
    ok, link, err = gofile_upload(mp4)
    head = "✅ <b>File %d saved</b>\n🎞 %s  ·  %s\n" % (n, mmss(dur), human(size)) + (note + "\n" if note else "")
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


MIN_FREE_GB = float(E("MIN_FREE_GB") or 12)       # archive download pauses while the disk has less free space than this
MAX_PENDING = int(E("MAX_PENDING_PARTS") or 4)    # ... or while this many finished parts wait for their upload
UPLOADING = [0]
_DW = [0.0, False]


def disk_wait():
    """Archive downloads can be much bigger than the disk (100 GB vs 70 GB). Finished parts are uploaded and deleted
    while the download goes on; if the download gets ahead of the uploads, it waits here (nothing is lost)."""
    if not ARCHIVE:
        return
    now = time.time()
    if now < _DW[0]:
        return
    _DW[0] = now + 1
    waited = False
    while not stop.is_set():
        try:
            free = shutil.disk_usage(OUT).free / 1e9
        except OSError:
            return
        pending = upq.qsize() + UPLOADING[0]
        if pending == 0 or (free >= MIN_FREE_GB and upq.qsize() < MAX_PENDING):
            break
        if not waited:
            waited = True
            print("Download waits for uploads: %.1f GB free, %d part(s) waiting" % (free, pending), flush=True)
            if not _DW[1]:
                _DW[1] = True
                say("⏸ <b>The download is ahead of the uploads.</b>\nIt waits for finished parts to be uploaded and deleted (disk: %.0f GB free). Nothing is lost, it continues by itself." % free)
        try:
            SP.last_es = time.time()
        except Exception:
            pass
        time.sleep(2)
    _DW[0] = time.time() + 1


def uploader():
    while True:
        item = upq.get()
        if item is None:
            return
        UPLOADING[0] += 1
        try:
            process(item)
        except Exception as e:
            print("process error:", repr(e), flush=True)
            say("⚠️ Error while saving a file: <code>%s</code>" % esc(repr(e)[:200]))
        finally:
            UPLOADING[0] -= 1


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
                           capture_output=True, text=True, timeout=60, env=fenv())
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
                               capture_output=True, text=True, timeout=90, env=fenv())
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


def worker_get(path):
    req = urllib.request.Request(WORKER_URL + path, headers={"X-Key": WORKER_KEY, "User-Agent": "recorder"})
    return json.load(urllib.request.urlopen(req, timeout=20))


def fetch_link():
    """The worker kept the stream link for us (so the link is never in the GitHub run page)."""
    global URL, ASKED
    for i in range(6):
        try:
            u = (worker_get("/link?ticket=" + urllib.parse.quote(TICKET)) or {}).get("url", "")
            if u:
                URL = u.strip(); ASKED = True
                print("::add-mask::" + URL, flush=True)
                return True
        except Exception as e:
            print("link request failed:", mask(repr(e))[:120], flush=True)
        time.sleep(3)
    return False


def worker_poll():
    """Stop / Status / Split presses arrive through the worker (Telegram only allows one reader of the bot)."""
    chats = ",".join(dict.fromkeys([c for c in [CHAT] + ALSO if c]))
    while not stop.is_set():
        try:
            for c in (worker_get("/cmd?chats=" + urllib.parse.quote(chats) + "&run=" + RUN + "&me=" + urllib.parse.quote(CHAT or "")) or {}).get("cmds", []):
                do_action(c)
        except Exception as e:
            print("worker poll failed:", repr(e)[:100], flush=True)
        for _ in range(8):
            if stop.is_set():
                return
            time.sleep(0.5)


def preflight():
    """Personal bot: check the secrets and the bot BEFORE asking for the link, with clear errors."""
    if DRY:
        return
    if not TOKEN:
        print("::error title=Secret TG_TOKEN is empty::Repo > Settings > Secrets and variables > Actions > New repository secret. Name: TG_TOKEN, value: the token from BotFather.", flush=True)
        sys.exit(1)
    me = tg("getMe")
    if not me.get("ok"):
        print("::error title=Bot token is wrong::Telegram refused TG_TOKEN (error %s). Copy the token again from BotFather and save it in the secret." % me.get("error_code", "?"), flush=True)
        sys.exit(1)
    print("Bot: @%s" % (me.get("result") or {}).get("username", "?"), flush=True)
    wh = (tg("getWebhookInfo").get("result") or {})
    if wh.get("url"):
        # The personal workflow has no Worker, so a webhook on this bot only blocks reading your link: remove it.
        print("This bot had a webhook (%s). Removing it so the bot can read your link." % wh["url"].split("/")[2], flush=True)
        d = tg("deleteWebhook")
        if not d.get("ok"):
            print("::error title=This bot has a webhook::Could not remove it. Open https://api.telegram.org/bot<TOKEN>/deleteWebhook once, or use a new bot from BotFather.", flush=True)
            sys.exit(1)
    if not CHAT:
        detect_chat()
    if not CHAT:
        print("::error title=No chat id::Open your personal bot in Telegram, press Start and send 'hi', then run again. (Or add secret TG_CHAT = your chat id.)", flush=True)
        sys.exit(1)
    r = tg("sendMessage", chat_id=CHAT, text="⏳ Workflow started. Getting ready...")
    if r.get("error_code") in (400, 403):
        print("::error title=The bot cannot write to your chat::Open your personal bot in Telegram, press Start, and check that TG_CHAT is YOUR chat id (a number). Telegram error %s." % r.get("error_code"), flush=True)
        sys.exit(1)


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
    """Place of the IP the stream server sees (the proxy's, if a proxy is set)."""
    try:
        d = json.load(stream_opener().open("https://ipinfo.io/json", timeout=10))
        return "%s, %s%s" % (d.get("city", "?"), d.get("country", "?"), " (via proxy)" if PROXY else "")
    except Exception:
        return "unknown" + (" (via proxy)" if PROXY else "")


def _ckey():
    return hashlib.sha256(("naimx-chain|" + (E("TG_TOKEN") or "")).encode()).digest()


def seal_link(u):
    """Hide the link for the next run: only a scrambled text goes through the GitHub inputs (key = your bot token)."""
    import base64, hmac
    raw = u.encode(); n = os.urandom(12); k = _ckey()
    ks = b"".join(hashlib.sha256(k + n + i.to_bytes(4, "big")).digest() for i in range(len(raw) // 32 + 1))
    ct = bytes(a ^ b for a, b in zip(raw, ks))
    tag = hmac.new(k, n + ct, hashlib.sha256).digest()[:16]
    return "enc:" + base64.urlsafe_b64encode(n + ct + tag).decode()


def open_link(t):
    import base64, hmac
    try:
        b = base64.urlsafe_b64decode(t[4:].encode()); n, ct, tag = b[:12], b[12:-16], b[-16:]
        k = _ckey()
        if not hmac.compare_digest(tag, hmac.new(k, n + ct, hashlib.sha256).digest()[:16]):
            return None
        ks = b"".join(hashlib.sha256(k + n + i.to_bytes(4, "big")).digest() for i in range(len(ct) // 32 + 1))
        return bytes(a ^ b for a, b in zip(ct, ks)).decode()
    except Exception:
        return None


def chain(rem_minutes):
    time.sleep(LIMIT - 300)
    if stop.is_set() or not shutil.which("gh"):
        return
    say("⏳ The 6 hour job limit is near. Starting the next run to continue...")
    say("🔁 The next run starts by itself with the same link. You do not need to send it again.")
    wf = E("WORKFLOW_FILE") or "record.yml"                  # the personal workflow starts itself again, not the shared one
    cmd = ["gh", "workflow", "run", wf, "--repo", REPO, "-f", "url=" + seal_link(URL), "-f", "minutes=%d" % rem_minutes,
           "-f", "name=" + NAME, "-f", "part_min=%s" % PART_MIN, "-f", "part_mb=%d" % (PART_MAX / 1e6)]
    if wf == "record.yml":
        cmd += ["-f", "ticket=" + TICKET, "-f", "chat=" + (CHAT or ""), "-f", "also=" + ",".join(ALSO)]
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


def hdr_dict():
    """The ffmpeg header options (HDR) as a normal dict for our own downloader."""
    h = {"User-Agent": UA, "Accept": "*/*"}
    a, i = HDR, 0
    while i + 1 < len(a):
        k, v = a[i], a[i + 1]
        if k == "-user_agent":
            h["User-Agent"] = v
        elif k == "-referer":
            h["Referer"] = v
        elif k == "-headers":
            for line in v.split("\r\n"):
                if ":" in line:
                    n, _, val = line.partition(":"); h[n.strip()] = val.strip()
        i += 2
    return h


def ts_pull(rq):
    """One connection to a direct MPEG-TS link. Bytes go straight into the queue. Returns (why it ended, bytes got)."""
    got = 0
    try:
        r = stream_opener().open(urllib.request.Request(URL, headers=hdr_dict()), timeout=20)
    except urllib.error.HTTPError as e:
        return "HTTP %s from the server" % e.code, 0
    except Exception as e:
        return mask(repr(e))[:150], 0
    S["resp"] = r
    try:
        while not stop.is_set():
            data = r.read1(1 << 16)
            if not data:
                return "server closed the connection", got
            got += len(data)
            rq.put(("d", data)); S["last_data"] = time.time()
            S["qmax"] = max(S["qmax"], rq.qsize())
        return "stopped", got
    except Exception as e:
        return mask(repr(e))[:150], got
    finally:
        S["resp"] = None
        try: r.close()
        except Exception: pass


ARCH_WHY = [""]
ARCH_URL = (r"timeshift|time-shift|catch-?up|/archive/|/vod/|/record(ing)?s?/|[?&](utc|lutc|start|from)=\d"
            r"|/\d{4}-\d{2}-\d{2}[:T_ -]\d{2}[-:]\d{2}/")


def expect_secs():
    """Timeshift links carry the length in minutes (/timeshift/user/pass/460/...). 0 = unknown."""
    m = re.search(r"/timeshift/[^/]+/[^/]+/(\d+)/", URL or "", re.I)
    return int(m.group(1)) * 60 if m else 0


def hls_is_archive():
    """(True/False, reason) for an .m3u8: a finished file or a running stream?"""
    import urllib.parse as up
    def get(x):
        return http_get(x, None, 25)[2].decode("utf-8", "ignore")
    u = URL
    text = get(u)
    for _ in range(2):                                         # a master playlist: look at the real stream inside it
        if "#EXT-X-STREAM-INF" not in text:
            break
        lines, best = text.splitlines(), None
        for k, l in enumerate(lines):
            if l.startswith("#EXT-X-STREAM-INF"):
                m = re.search(r"BANDWIDTH=(\d+)", l)
                bw = int(m.group(1)) if m else 0
                for l2 in lines[k + 1:]:
                    if l2.strip() and not l2.startswith("#"):
                        if best is None or bw > best[0]:
                            best = (bw, up.urljoin(u, l2.strip()))
                        break
        if not best:
            break
        u = best[1]; text = get(u)
    if "#EXT-X-ENDLIST" in text:
        return True, "the playlist has an end tag"
    if re.search(r"#EXT-X-PLAYLIST-TYPE:\s*VOD", text):
        return True, "the playlist says it is a VOD"
    def sig(t):
        return [l.strip() for l in t.splitlines() if l.strip() and not l.startswith("#")]
    m = re.search(r"#EXT-X-TARGETDURATION:(\d+)", text)
    wait = min(15.0, max(6.0, 1.6 * float(m.group(1)))) if m else 8.0
    time.sleep(wait)                                           # a running stream adds new parts meanwhile, a finished file does not
    text2 = get(u)
    if "#EXT-X-ENDLIST" in text2:
        return True, "the playlist has an end tag"
    if sig(text) == sig(text2):
        return True, "the playlist did not change for %d seconds, so it is a finished file" % wait
    return False, "the playlist keeps getting new parts"


def detect_archive():
    """True if the link is a finished file (timeshift / catch-up), False if it is a live stream."""
    if MODE == "live":
        ARCH_WHY[0] = "you chose live"; return False
    if MODE == "archive":
        ARCH_WHY[0] = "you chose archive"; return True
    if re.search(ARCH_URL, URL, re.I):                            # decided by the link itself: no network check needed
        ARCH_WHY[0] = "the link looks like a timeshift / archive link"; return True
    try:
        if KIND != "ts":
            ok, why = hls_is_archive()
            ARCH_WHY[0] = why
            return ok
        r = stream_opener().open(urllib.request.Request(URL, headers=hdr_dict()), timeout=20)
        try:
            cl = r.headers.get("Content-Length")               # a live stream has no length, a file has
            if cl and cl.isdigit() and int(cl) > 500_000:
                ARCH_WHY[0] = "the server gives a file size (%s)" % human(int(cl)); return True
        finally:
            r.close()
        ARCH_WHY[0] = "the server gives no file size"
        return False
    except Exception as e:
        ARCH_WHY[0] = "could not check (%s)" % mask(repr(e))[:80]
        return False


def dl_ts_once(rq):
    """One connection of a .ts file download. Always continues exactly where the last one stopped."""
    start = D["got"]
    h = hdr_dict()
    if start:
        h["Range"] = "bytes=%d-" % start
    try:
        r = stream_opener().open(urllib.request.Request(URL, headers=h), timeout=30)
    except urllib.error.HTTPError as e:
        if e.code == 416 and D["total"] and start >= D["total"]:
            return True, "complete"
        return False, "HTTP %s from the server" % e.code
    except Exception as e:
        return False, mask(repr(e))[:150]
    S["resp"] = r
    skip = 0
    n0 = D["got"]
    try:
        cr = r.headers.get("Content-Range") or ""
        cl = r.headers.get("Content-Length")
        if r.status == 206 and cr.rsplit("/", 1)[-1].isdigit():
            D["total"] = int(cr.rsplit("/", 1)[-1])
        elif r.status == 200:
            if cl and cl.isdigit():
                D["total"] = int(cl)
            skip = start                                      # the server ignored Range: skip what we already have
        while not stop.is_set():
            data = r.read1(1 << 16)
            if not data:
                break
            if skip:
                if len(data) <= skip:
                    skip -= len(data); continue
                data = data[skip:]; skip = 0
            rq.put(("d", data)); D["got"] += len(data); S["last_data"] = time.time()
        else:
            return False, "stopped"
        if D["total"] and D["got"] < D["total"]:
            return False, "connection closed at %s of %s" % (human(D["got"]), human(D["total"]))
        ex = expect_secs()
        if not D["total"] and ex and D["got"] > n0 and SP and SP.media_total() < ex * 0.97:
            return False, "connection closed early (%s of about %s)" % (mmss(SP.media_total()), mmss(ex))
        return True, "complete"
    except Exception as e:
        return False, mask(repr(e))[:150]
    finally:
        S["resp"] = None
        try: r.close()
        except Exception: pass


def wait_drain(rq):
    t = time.time()
    while not rq.empty() and time.time() - t < 60:
        time.sleep(0.2)
    time.sleep(0.6)


def dl_hls_once(rq, first):
    """One ffmpeg run over a finished .m3u8. After a failure it starts a few seconds before where it stopped."""
    before = D["secs"]
    ss = ["-ss", "%.1f" % (D["secs"] - 30)] if D["secs"] > 35 else []        # restart 30 s earlier, the repeated part is dropped
    cmd = ["ffmpeg", "-hide_banner", "-loglevel", "warning", "-y", "-fflags", "+discardcorrupt+genpts", "-rw_timeout", "60000000",
           "-reconnect", "1", "-reconnect_streamed", "1", "-reconnect_delay_max", "15", "-seg_max_retry", "15", "-live_start_index", "0", "-max_reload", "3", "-m3u8_hold_counters", "3", "-http_persistent", "0"] + ss + HDR + [
           "-i", URL, "-map", "0:v?", "-map", "0:a?", "-c", "copy", "-copyts", "-muxdelay", "0", "-muxpreload", "0",
           "-f", "mpegts", "-mpegts_flags", "+resend_headers", "pipe:1"]
    if not first:
        rq.put(("n", True, False))                           # the few repeated seconds are dropped (same clock)
    p = S["proc"] = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, bufsize=0, env=fenv())
    err = []
    threading.Thread(target=stderr_reader, args=(p, err), daemon=True).start()
    got = 0
    while True:
        data = p.stdout.read(1 << 16)
        if not data:
            break
        rq.put(("d", data)); got += len(data); S["last_data"] = time.time()
        if TEST_KILL_MB and first and got > TEST_KILL_MB * 1e6 and p.poll() is None:
            p.kill()
    p.wait()
    wait_drain(rq)
    D["secs"] = max(D["secs"], SP.media_total())
    if stop.is_set():
        return False, "stopped"
    if p.returncode == 0 and (D["dur"] is None or D["secs"] >= D["dur"] - 8 or D["secs"] - before < 2):
        return True, "complete"
    return False, why_exit(p.returncode, err)


def archive_report():
    """After an archive download: does the file have everything the playlist promised?"""
    try:
        if SP and SP.part_no == 0 and SP.total > 1_000_000:
            print("Archive report: data was read (%d MB) but no file was started" % (SP.total // 1_000_000), flush=True)
            say("⚠️ <b>The download ran but nothing could be saved.</b> The video data was not recognised. Tell the owner, with this run's log.")
            return
        got = D["secs"] if KIND != "ts" else (SP.media_total() if SP else 0)
        jumps = SP.rebased if SP else 0
        gap = SP.gap_total if SP else 0.0
        lines = []
        if KIND != "ts" and D["dur"]:
            miss = D["dur"] - got
            if miss > 15:
                lines.append("⚠️ <b>The file is %s shorter than the playlist</b> (playlist %s, file %s).\nSome parts could not be downloaded from the server." % (mmss(miss), mmss(D["dur"]), mmss(got)))
            else:
                lines.append("✅ <b>Complete:</b> the file is as long as the playlist (%s)." % mmss(D["dur"]))
        if jumps > 1:
            lines.append("ℹ️ The archive's own clock jumps %d times (%s skipped on its clock). If the length above matches, nothing was lost by the download: the provider's archive itself has these breaks." % (jumps, mmss(gap)))
        print("Archive report: playlist=%s file=%.1fs jumps=%d jump_total=%.1fs" % (D["dur"], got, jumps, gap), flush=True)
        if lines:
            say("\n".join(lines))
    except Exception as e:
        print("archive report failed:", repr(e)[:100], flush=True)


class NotParallel(Exception):
    """This link cannot be fetched in parallel pieces (server ignores Range, encrypted / fragmented playlist ...)."""


def qput(rq, item):
    while not stop.is_set():
        try:
            rq.put(item, timeout=1); return True
        except queue.Full:
            continue
    return False


def http_get(url, rng=None, timeout=40):
    h = hdr_dict()
    if rng:
        h["Range"] = rng
    r = stream_opener().open(urllib.request.Request(url, headers=h), timeout=timeout)
    try:
        return r.status, r.headers, r.read()
    finally:
        r.close()


_KA = threading.local()
KA_OK = [not PROXY]


def http_get_ka(url, rng):
    """Like http_get for one Range piece, but every download thread keeps its connection open between pieces
    (no new TCP + TLS handshake per piece). Anything unusual (redirect, error) falls back to the normal http_get."""
    if not KA_OK[0]:
        return http_get(url, rng)
    import http.client
    u = urllib.parse.urlsplit(url)
    key = (u.scheme, u.netloc)
    conns = getattr(_KA, "c", None)
    if conns is None:
        conns = _KA.c = {}
    c = conns.get(key)
    try:
        if c is None:
            c = conns[key] = (http.client.HTTPSConnection if u.scheme == "https" else http.client.HTTPConnection)(u.netloc, timeout=40)
        h = hdr_dict(); h["Range"] = rng
        c.request("GET", (u.path or "/") + ("?" + u.query if u.query else ""), headers=h)
        r = c.getresponse()
        body = r.read()
        if r.status in (301, 302, 303, 307, 308):
            KA_OK[0] = False                                   # redirects: use the normal way from now on
            raise IOError("redirect")
        return r.status, r.headers, body
    except Exception:
        conns.pop(key, None)
        try: c.close()
        except Exception: pass
        return http_get(url, rng)


def retry(fn, tries=6):
    last = None
    for a in range(tries):
        if stop.is_set():
            raise RuntimeError("stopped")
        try:
            return fn()
        except NotParallel:
            raise
        except Exception as e:
            last = e
            time.sleep(min(1 + a, 5))
    raise last


def ordered_parallel(n, fetch, emit, workers):
    """Run fetch(i) for i in 0..n-1 on many threads, call emit(i, data) strictly in order.
    Returns None when all n are emitted, else a short error text (everything before the failed piece was emitted)."""
    res, cond = {}, threading.Condition()
    st = {"next": 0, "emit": 0, "fail": None}
    window = max(4, workers * 2)                               # at most this many pieces in memory ahead of the writer

    def worker():
        while True:
            with cond:
                while st["next"] < n and st["next"] - st["emit"] >= window and st["fail"] is None and not stop.is_set():
                    cond.wait(1)
                if st["fail"] is not None or st["next"] >= n or stop.is_set():
                    return
                i = st["next"]; st["next"] += 1
            try:
                data = retry(lambda: fetch(i))
            except Exception as e:
                with cond:
                    if st["fail"] is None or i < st["fail"][0]:
                        st["fail"] = (i, e)
                    cond.notify_all()
                return
            with cond:
                res[i] = data; cond.notify_all()

    ths = [threading.Thread(target=worker, daemon=True) for _ in range(max(1, workers))]
    for t in ths:
        t.start()
    err = None
    while st["emit"] < n:
        with cond:
            while st["emit"] not in res and not stop.is_set() and not (st["fail"] and st["fail"][0] <= st["emit"]):
                cond.wait(1)
            if stop.is_set():
                err = "stopped"; break
            if st["emit"] not in res:
                err = st["fail"][1]; break
            data = res.pop(st["emit"])
        if not emit(st["emit"], data):
            err = "stopped"; break
        with cond:
            st["emit"] += 1; cond.notify_all()
    with cond:
        if err is not None and st["fail"] is None:
            st["fail"] = (-1, err)
        cond.notify_all()
    for t in ths:
        t.join(3)
    if err is None:
        return None
    return mask(repr(err))[:150] if isinstance(err, Exception) else str(err)


def parallel_ts(rq):
    """Heavy .ts archive: pieces of 4 MB over many connections, written in order. True = file complete."""
    try:
        h = hdr_dict(); h["Range"] = "bytes=0-0"
        r = stream_opener().open(urllib.request.Request(URL, headers=h), timeout=30)
        try:
            cr = r.headers.get("Content-Range") or ""
            ok = r.status == 206 and cr.rsplit("/", 1)[-1].isdigit()
        finally:
            r.close()
    except Exception:
        return False
    if not ok:
        return False                                           # the server ignores Range: normal download
    total = int(cr.rsplit("/", 1)[-1])
    D["total"] = total
    if total < HEAVY_MB * 1e6:
        return False
    start, CH = D["got"], int(float(E("PAR_CHUNK_MB") or 8) * (1 << 20))
    n = -(-(total - start) // CH)
    say("⚡ <b>Heavy file (%s)</b>\nDownloading with %d parallel connections. If the server refuses, it continues the normal way." % (human(total), PARALLEL))
    print("Parallel download: %d pieces of %.1f MB, %d connections" % (n, CH / 1048576, PARALLEL), flush=True)

    def fetch(i):
        a = start + i * CH
        b = min(total, a + CH) - 1
        stt, _, data = http_get_ka(URL, "bytes=%d-%d" % (a, b))
        if stt != 206:
            raise NotParallel("server ignored Range")
        if len(data) != b - a + 1:
            raise IOError("short piece")
        return data

    def emit(i, data):
        for k in range(0, len(data), 1 << 16):
            if not qput(rq, ("d", data[k:k + (1 << 16)])):
                return False
        D["got"] += len(data); S["last_data"] = time.time()
        return True
    err = ordered_parallel(n, fetch, emit, PARALLEL)
    wait_drain(rq)
    if err:
        print("Parallel download stopped (%s), continuing the normal way" % err, flush=True)
        return False
    return D["got"] >= total


TS_RE = re.compile(r"^(?P<pre>.*?/timeshift/[^/]+/[^/]+/)(?P<dur>\d+)/(?P<date>\d{4}-\d{2}-\d{2})(?P<sep>%3A|%3a|:)(?P<hh>\d{2})-(?P<mm>\d{2})(?P<post>/.*)$")
TS_MIN = float(E("TS_MINUTE_SECS") or 60)                 # one minute in seconds (only changed by tests)
TS_SLICE = int(E("TS_SLICE_MIN") or 5)                    # minutes per piece
TS_FAST_OVER = float(E("TS_FAST_OVER") or 150)           # one connection already this fast (Mbps): pieces would only slow it down
TS_PAR = int(E("TS_PAR") or 8)                            # connections for a timeshift link (providers often allow only a few)


def ts_url(i, minutes, n_min):
    """The link for 'n_min minutes starting minutes after the original start'. None if the link has another shape."""
    import datetime as dt
    m = TS_RE.match(URL)
    if not m:
        return None
    t0 = dt.datetime.strptime("%s %s:%s" % (m["date"], m["hh"], m["mm"]), "%Y-%m-%d %H:%M") + dt.timedelta(minutes=minutes)
    return "%s%d/%s%s%s%s" % (m["pre"], n_min, t0.strftime("%Y-%m-%d"), m["sep"], t0.strftime("%H-%M"), m["post"])


def ts_fetch_file(url, path, limit=None):
    """Download one piece to a file; returns its size. Raises when the server sends nothing."""
    h = hdr_dict()
    r = stream_opener().open(urllib.request.Request(url, headers=h), timeout=40)
    n = 0
    try:
        with open(path, "wb") as f:
            while not stop.is_set():
                d = r.read1(1 << 16)
                if not d:
                    break
                f.write(d); n += len(d)
                S["last_data"] = time.time()
                if limit and time.time() > limit:
                    raise IOError("too slow")
    finally:
        try: r.close()
        except Exception: pass
    if n < 100_000:
        raise IOError("piece too small (%d bytes)" % n)
    return n


def ts_probe(tmp):
    """Does the server cut a timeshift into pieces that join without any loss? Test with 3 short downloads:
    minute 0-1, minute 1-2 and minute 0-2. Safe only if every piece starts on a keyframe and 0-1 plus 1-2 is as long as 0-2."""
    def info(p):
        o = subprocess.run(["ffprobe", "-v", "error", "-select_streams", "v:0", "-show_entries", "packet=flags", "-read_intervals", "%+#1",
                            "-of", "csv=p=0", p], capture_output=True, text=True, timeout=60).stdout.strip().split("\n")[0]
        d = subprocess.run(["ffprobe", "-v", "error", "-show_entries", "format=duration", "-of", "csv=p=0", p],
                           capture_output=True, text=True, timeout=60).stdout.strip().split()[0]
        return ("K" in o), float(d)
    res, speed = [], [0.0]
    for k, (st, ln) in enumerate([(0, 1), (1, 1), (0, 2)]):
        p = os.path.join(tmp, "probe%d.ts" % k)
        t_a = time.time()
        nb = ts_fetch_file(ts_url(0, st, ln), p, time.time() + 240)
        if k == 2:
            speed[0] = nb * 8 / max(0.05, time.time() - t_a) / 1e6
        res.append(info(p))
        try: os.remove(p)
        except OSError: pass
    (ka, da), (kb, db), (kr, dr) = res
    ok = ka and kb and kr and abs((da + db) - dr) <= 1.0 and dr >= 2 * TS_MIN - 6
    print("Timeshift pieces test: starts on keyframe %s/%s/%s, lengths %.1f + %.1f vs %.1f s -> %s. One connection: %.0f Mbps" % (ka, kb, kr, da, db, dr, "safe" if ok else "NOT safe", speed[0]), flush=True)
    return ok, speed[0]


def parallel_timeshift(rq):
    """Timeshift .ts without file size or Range: download pieces of TS_SLICE minutes in parallel, join them in order.
    Only used when the test above proves the server cuts cleanly. True = complete, False = not used / could not finish
    (when some pieces were already written the rest continues piece by piece, so nothing is lost or repeated)."""
    if TS_SLICE <= 0 or TS_PAR <= 1:
        return False
    m = TS_RE.match(URL or "")
    if not m:
        return False
    total_min = int(m["dur"])
    if total_min < TS_SLICE * 2:
        return False
    tmp = os.path.join(OUT, "slices"); os.makedirs(tmp, exist_ok=True)
    try:
        ok, one = ts_probe(tmp)
        if not ok:
            return False
        if one >= TS_FAST_OVER:
            print("One connection already gives %.0f Mbps, so the normal download is used (pieces would be slower)." % one, flush=True)
            return False
    except Exception as e:
        print("Timeshift pieces test failed (%s): normal download" % mask(repr(e))[:120], flush=True)
        return False
    n = -(-total_min // TS_SLICE)
    D["dur"] = total_min * TS_MIN
    say("⚡ <b>Fast timeshift mode</b>\nThe server cuts this timeshift cleanly, so it is downloaded in %d pieces with %d connections and joined in order (nothing lost, nothing repeated)." % (n, TS_PAR))
    print("Timeshift parallel: %d pieces of %d min, %d connections" % (n, TS_SLICE, TS_PAR), flush=True)
    state = {"emitted": 0}

    def make(base):
        def fetch(i):
            k = base + i
            mins = TS_SLICE * k
            ln = min(TS_SLICE, total_min - mins)
            p = os.path.join(tmp, "piece%05d.ts" % k)
            ts_fetch_file(ts_url(0, mins, ln), p)
            return p
        def emit(i, p):
            k = base + i
            if k > 0:
                if not qput(rq, ("n", False, False)):
                    return False
            with open(p, "rb") as f:
                while True:
                    d = f.read(1 << 16)
                    if not d:
                        break
                    if not qput(rq, ("d", d)):
                        return False
                    D["got"] += len(d)
            try: os.remove(p)
            except OSError: pass
            state["emitted"] = k + 1
            D["secs"] = min(D["dur"], (k + 1) * TS_SLICE * TS_MIN)
            S["last_data"] = time.time()
            return True
        return fetch, emit
    for attempt in range(4):
        base = state["emitted"]
        if base >= n:
            break
        fetch, emit = make(base)
        err = ordered_parallel(n - base, fetch, emit, TS_PAR if attempt == 0 else 1)
        wait_drain(rq)
        if err is None:
            break
        if stop.is_set():
            return False
        S["restarts"] += 1; S["reason"] = str(err)[:150]
        print("Timeshift piece failed (%s): continuing with piece %d" % (mask(str(err))[:100], state["emitted"] + 1), flush=True)
        time.sleep(3)
    for fn in os.listdir(tmp):
        try: os.remove(os.path.join(tmp, fn))
        except OSError: pass
    return True if state["emitted"] >= n else (None if state["emitted"] > 0 else False)


def hls_plan():
    """For a simple finished .m3u8 (plain .ts segments, no encryption): [(url, seconds)...]. None if it needs ffmpeg."""
    import urllib.parse as up
    def get(u):
        stt, _, b = http_get(u, None, 30)
        return b.decode("utf-8", "ignore")
    u = URL
    text = get(u)
    if "#EXT-X-STREAM-INF" in text:                            # master playlist: take the best quality
        lines = text.splitlines(); best = None
        if "TYPE=AUDIO" in text and re.search(r"#EXT-X-MEDIA:[^\n]*URI=", text):
            return None                                        # separate audio playlist: let ffmpeg merge it
        for k, l in enumerate(lines):
            if l.startswith("#EXT-X-STREAM-INF"):
                m = re.search(r"BANDWIDTH=(\d+)", l)
                bw = int(m.group(1)) if m else 0
                for l2 in lines[k + 1:]:
                    if l2.strip() and not l2.startswith("#"):
                        if best is None or bw > best[0]:
                            best = (bw, up.urljoin(u, l2.strip()))
                        break
        if not best:
            return None
        u = best[1]; text = get(u)
    if "#EXT-X-STREAM-INF" in text or "#EXT-X-MAP" in text or "#EXT-X-BYTERANGE" in text:
        return None
    if re.search(r"#EXT-X-KEY:(?!METHOD=NONE)", text):
        return None                                            # encrypted
    segs, dur = [], 0.0
    for line in text.splitlines():
        line = line.strip()
        if line.startswith("#EXTINF:"):
            try: dur = float(line[8:].split(",")[0])
            except ValueError: dur = 0.0
        elif line and not line.startswith("#"):
            segs.append((up.urljoin(u, line), dur)); dur = 0.0
    return segs or None


P = {"seg": 0}


def parallel_hls(rq):
    """Heavy .m3u8 archive: segments fetched on many connections, written in order. True = complete."""
    try:
        segs = hls_plan()
    except Exception as e:
        print("Parallel plan failed:", mask(repr(e))[:120], flush=True)
        return False
    if not segs:
        return False
    total = sum(d for _, d in segs)
    D["dur"] = total
    if total < HEAVY_MIN * 60 or len(segs) < 20:
        return False
    say("⚡ <b>Heavy archive (%s, %d parts)</b>\nDownloading with %d parallel connections. If the server refuses, it continues the normal way." % (hms(total), len(segs), PARALLEL))
    print("Parallel download: %d segments, %d connections" % (len(segs), PARALLEL), flush=True)
    fails = 0
    while P["seg"] < len(segs) and not stop.is_set():
        base = P["seg"]

        def fetch(i):
            stt, _, data = http_get(segs[base + i][0])
            if stt != 200 or len(data) < 188 or data[0] != 0x47:
                if base + i == 0:
                    raise NotParallel("segments are not MPEG-TS")
                raise IOError("bad segment")
            return data

        def emit(i, data):
            for k in range(0, len(data), 1 << 16):
                if not qput(rq, ("d", data[k:k + (1 << 16)])):
                    return False
            P["seg"] = base + i + 1
            D["secs"] += segs[base + i][1]; S["last_data"] = time.time()
            return True
        err = ordered_parallel(len(segs) - base, fetch, emit, PARALLEL)
        if err is None:
            break
        fails = 0 if P["seg"] > base else fails + 1
        if stop.is_set():
            return False
        S["restarts"] += 1; S["reason"] = err
        print("Parallel download interrupted (%s) at part %d of %d" % (err, P["seg"], len(segs)), flush=True)
        if "segments are not MPEG-TS" in err or fails >= 6:
            return False                                       # let ffmpeg continue from here
        time.sleep(min(2 * fails + 1, 15))
    if P["seg"] < len(segs):
        return False
    wait_drain(rq)
    D["secs"] = max(SP.media_total(), 0.0) if SP else D["secs"]
    return True


PAR_LIVE = [False]      # live .m3u8 is recorded with many parallel connections (set by the probe or when gaps show up)
PAR_OK = [True]         # False once we know this playlist cannot be fetched by hand (encrypted, fMP4 ...)


def hls_media(u):
    """Follow a master playlist to the best stream. Returns (media_url, text) or None if ffmpeg has to do it."""
    import urllib.parse as up
    def get(x):
        return http_get(x, None, 25)[2].decode("utf-8", "ignore")
    text = get(u)
    if "#EXT-X-STREAM-INF" in text:
        if "TYPE=AUDIO" in text and re.search(r"#EXT-X-MEDIA:[^\n]*URI=", text):
            return None
        lines = text.splitlines(); best = None
        for k, l in enumerate(lines):
            if l.startswith("#EXT-X-STREAM-INF"):
                m = re.search(r"BANDWIDTH=(\d+)", l)
                bw = int(m.group(1)) if m else 0
                for l2 in lines[k + 1:]:
                    if l2.strip() and not l2.startswith("#"):
                        if best is None or bw > best[0]:
                            best = (bw, up.urljoin(u, l2.strip()))
                        break
        if not best:
            return None
        u = best[1]; text = get(u)
    if "#EXT-X-STREAM-INF" in text or "#EXT-X-MAP" in text or "#EXT-X-BYTERANGE" in text or re.search(r"#EXT-X-KEY:(?!METHOD=NONE)", text):
        return None
    return u, text


def hls_parse(text, base):
    import urllib.parse as up
    m = re.search(r"#EXT-X-MEDIA-SEQUENCE:(\d+)", text)
    seq = int(m.group(1)) if m else 0
    segs, dur = [], 0.0
    for line in text.splitlines():
        line = line.strip()
        if line.startswith("#EXTINF:"):
            try: dur = float(line[8:].split(",")[0])
            except ValueError: dur = 0.0
        elif line and not line.startswith("#"):
            segs.append((up.urljoin(base, line), dur)); dur = 0.0
    return seq, segs, "#EXT-X-ENDLIST" in text


def live_probe():
    """Is one segment slower to download than it is long? Then the normal way falls behind the live edge and skips parts."""
    try:
        r = hls_media(URL)
        if not r:
            PAR_OK[0] = False
            return False
        seq, segs, ended = hls_parse(r[1], r[0])
        if ended or len(segs) < 2:
            return False
        url, dur = segs[-2]
        t = time.time()
        http_get(url, None, 25)
        took = time.time() - t
        print("Speed check: one %.1fs part took %.1fs to download" % (dur, took), flush=True)
        return dur > 0 and took > 0.5 * dur
    except Exception as e:
        print("Speed check failed:", mask(repr(e))[:100], flush=True)
        return False


def live_hls_parallel(rq):
    """Live .m3u8: look at the playlist every second or two, fetch every new part at once on many connections,
    write them in order. A slow server can no longer make us fall behind the live edge."""
    try:
        r = hls_media(URL)
    except Exception as e:
        return "playlist: " + mask(repr(e))[:100]
    if not r:
        PAR_OK[0] = False
        return "fallback"
    media = r[0]
    jobs, res, cond = queue.Queue(), {}, threading.Condition()
    st = {"emit": None, "next": None, "end": False}
    my_stop = threading.Event()

    def worker():
        while not stop.is_set() and not my_stop.is_set():
            try:
                seq, url = jobs.get(timeout=1)
            except queue.Empty:
                continue
            data = None
            for a in range(3):
                try:
                    stt, _, b = http_get(url, None, 20)
                    if stt == 200 and len(b) >= 188:
                        data = b; break
                except Exception:
                    time.sleep(0.4)
            with cond:
                res[seq] = data; cond.notify_all()

    def emitter():
        while not stop.is_set() and not my_stop.is_set():
            with cond:
                while (st["emit"] is None or st["emit"] not in res) and not stop.is_set() and not my_stop.is_set():
                    cond.wait(1)
                if stop.is_set() or my_stop.is_set():
                    return
                data = res.pop(st["emit"]); n = st["emit"]; st["emit"] += 1
            if data is None:
                print("Part %d could not be downloaded (the server no longer has it)" % n, flush=True)
                continue
            for k in range(0, len(data), 1 << 16):
                if not qput(rq, ("d", data[k:k + (1 << 16)])):
                    return
            S["last_data"] = time.time()

    ths = [threading.Thread(target=worker, daemon=True) for _ in range(PARALLEL)] + [threading.Thread(target=emitter, daemon=True)]
    for t in ths:
        t.start()
    bad, why = 0, "stopped"
    back = int(BACK) if str(BACK).isdigit() else 3
    try:
        while not stop.is_set():
            try:
                text = http_get(media, None, 15)[2].decode("utf-8", "ignore")
                seq, segs, ended = hls_parse(text, media)
                bad = 0
            except Exception as e:
                bad += 1
                if bad >= 20:
                    why = "playlist not reachable: " + mask(repr(e))[:100]
                    break
                time.sleep(1); continue
            if segs:
                last = seq + len(segs) - 1
                if st["next"] is None:
                    avg = sum(d for _, d in segs if d) / max(1, len([1 for _, d in segs if d])) or 4.0
                    safe = max(back, int(-(-30 // avg)))          # start at least 30 seconds behind the live edge (repeats are dropped)
                    st["next"] = max(seq, last - safe + 1)
                    with cond:
                        st["emit"] = st["next"]
                for k, (url, _) in enumerate(segs):
                    if seq + k >= st["next"]:
                        jobs.put((seq + k, url)); st["next"] = seq + k + 1
                if st["next"] < seq:                            # we were so far behind that the server dropped parts
                    st["next"] = seq
            if ended:
                why = "playlist ended"
                break
            tgt = min((d for _, d in segs if d), default=4.0)
            time.sleep(max(0.7, min(2.0, tgt / 2.5)))
    finally:
        # let what is already downloaded go out, then end
        t_end = time.time()
        while time.time() - t_end < 15 and not stop.is_set():
            with cond:
                pending = [k for k in res] + [] if st["emit"] is not None else []
                if not pending and jobs.empty():
                    break
            time.sleep(0.3)
        my_stop.set()
        with cond:
            cond.notify_all()
    return why


def download_loop(rq):
    """Finished file (timeshift / catch-up): download everything, resume after every break. Returns True if complete."""
    if PARALLEL > 1:
        try:
            if (parallel_ts(rq) if KIND == "ts" else parallel_hls(rq)):
                archive_report()
                return True
        except Exception as e:
            print("Parallel download failed, normal download instead:", mask(repr(e))[:150], flush=True)
    if KIND == "ts" and not D["got"]:
        try:
            res = parallel_timeshift(rq)
        except Exception as e:
            print("Timeshift fast mode error:", mask(repr(e))[:150], flush=True)
            res = None if D["got"] else False
        if res:
            archive_report()
            return True
        if res is None:                                          # some pieces are saved but not all: a normal download would not match them
            say("❌ <b>The fast timeshift download stopped</b> and could not continue.\n<code>%s</code>\nWhat was downloaded is saved. Start again to get the rest." % esc(S["reason"][:200]))
            return False
    if KIND != "ts" and not D["dur"]:
        try:
            r = subprocess.run(["ffprobe", "-v", "error"] + HDR + ["-show_entries", "format=duration", "-of", "csv=p=0", URL],
                               capture_output=True, text=True, timeout=90, env=fenv())
            D["dur"] = float((r.stdout or "").strip().split()[0])
        except Exception:
            D["dur"] = None
    fails = 0
    n = 1 if (D["got"] or D["secs"]) else 0                      # parallel part already wrote data: continue like after a break
    while not stop.is_set():
        before = D["got"] if KIND == "ts" else D["secs"]
        done, why = dl_ts_once(rq) if KIND == "ts" else dl_hls_once(rq, n == 0)
        n += 1
        if done:
            wait_drain(rq)                                       # let the writer finish before the report counts the length
            archive_report()
            return True
        if stop.is_set():
            return False
        gain = (D["got"] if KIND == "ts" else D["secs"]) - before
        fails = 0 if gain > (1_000_000 if KIND == "ts" else 2) else fails + 1
        S["restarts"] += 1; S["reason"] = why
        print("Download interrupted (%s). Continuing where it stopped (try %d)" % (why, n), flush=True)
        if fails >= 8:
            say("❌ <b>The download stopped</b> and could not continue after several tries.\n<code>%s</code>" % esc(why[:200]))
            return False
        time.sleep(min(2 * fails + 1, 20))
    return False


def record():
    global SP, HDR, ARCHIVE
    os.makedirs(OUT, exist_ok=True)
    detect_chat()
    if PROXY:
        print("::add-mask::" + PROXY, flush=True)
    global URL
    if URL.startswith("enc:"):
        u = open_link(URL)
        if u:
            URL = u; print("::add-mask::" + URL, flush=True)
            print("Link taken over from the previous run.", flush=True)
        else:
            URL = "ask"                                      # could not unlock it: ask again
    if URL.startswith("http"):
        TICK_OK = True
    else:
        TICK_OK = False
    if not TICK_OK and TICKET and WORKER_URL and not fetch_link():
        say("❌ <b>Could not get the stream link from the worker.</b> Send the link again.")
        print("::error title=No link::The worker did not return the link for this ticket.", flush=True)
        sys.exit(1)
    if URL.strip().lower() in ("", "ask", "telegram"):
        preflight()
        ask_link()
    ok, err = precheck()
    if not ok:
        why = explain(err)
        print("PRECHECK FAILED. ffmpeg said:\n" + err, flush=True)
        print("::error title=Link could not be opened from GitHub::" + why, flush=True)
        summary("## Recording did not start\n**Reason:** " + why + "\n\n```\n" + err + "\n```")
        say("❌ <b>The link could not be opened from GitHub's server</b>\n<b>Reason:</b> %s\n\n<code>%s</code>" % (esc(why), esc(err[-300:])))
        sys.exit(1)
    ARCHIVE = detect_archive()
    print("Link type: %s (%s)" % ("finished file (archive): it is downloaded completely" if ARCHIVE else "live stream", ARCH_WHY[0]), flush=True)
    plan = ("stops after %d min" % MINUTES) if MINUTES else "runs until you press Stop"
    kind_txt = "📡 <b>MPEG-TS live stream</b> (starts now, no rewind)" if KIND == "ts" else "📡 HLS stream"
    every = "every %s%s" % (human(PART_MAX), (" or %g min" % PART_MIN) if PART_MIN > 0 else "")
    if ARCHIVE:
        say("⬇️ <b>Archive download started</b>\n🎬 %s\n📡 %s\n✂️ New file every %s\n📍 Stream server sees an IP in: %s\nEach file is uploaded when it is full. Use Status to see the progress.\n🔎 Detected as an archive: %s." %
            (esc(NAME), "finished .ts file" if KIND == "ts" else "finished .m3u8 playlist", human(PART_MAX), esc(where()), esc(ARCH_WHY[0])), buttons=True)
    else:
        say("🔴 <b>Recording started</b>\n🎬 %s\n%s\n⏱ %s\n✂️ New file %s (whichever comes first)\n📍 Stream server sees an IP in: %s\nThe first download link comes after the first file is full.\n🔎 Detected as a live stream: %s.%s" %
            (esc(NAME), kind_txt, plan, every, esc(where()), esc(ARCH_WHY[0]),
             "" if MODE != "auto" else "\nIf this is a finished archive, send the link again with the word <b>archive</b> after it."), buttons=True)
    signal.signal(signal.SIGINT, lambda *a: halt())
    signal.signal(signal.SIGTERM, lambda *a: halt())
    total = MINUTES * 60
    if (not total or total > LIMIT) and not ARCHIVE:
        threading.Thread(target=chain, args=(int((total - LIMIT) / 60) if total else 0,), daemon=True).start()
    if WORKER_URL and not DRY:
        threading.Thread(target=worker_poll, daemon=True).start()
    elif TOKEN and CHAT and not DRY:
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
                    disk_wait()
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
    if not DRY:
        threading.Thread(target=live_loop, daemon=True).start()

    last_err = []; first = True; consec = 0; hi = [0]
    dl_ok = True
    if ARCHIVE:
        dl_ok = download_loop(rq)
        stop.set()                                             # nothing more to fetch (also quiets the stream monitor)
    if KIND == "hls" and not ARCHIVE and PARALLEL > 1 and LIVE_PAR != "0":
        if LIVE_PAR == "1" or live_probe():
            PAR_LIVE[0] = True
            say("⚡ <b>Fast mode</b>\nThis link is slower than real time, so I record it with %d parallel connections. No parts are skipped." % PARALLEL)

        def gap_watch():
            while not stop.is_set():
                time.sleep(2)
                if PAR_OK[0] and not PAR_LIVE[0] and SP and SP.gap_total >= float(E("GAP_SWITCH") or 8):
                    PAR_LIVE[0] = True
                    say("⚡ <b>Parts are being skipped</b>, so I switch to %d parallel connections now." % PARALLEL)
                    pr = S["proc"]
                    if pr and pr.poll() is None:
                        pr.send_signal(signal.SIGINT)
        if LIVE_PAR != "1":
            threading.Thread(target=gap_watch, daemon=True).start()
    while not stop.is_set() and not ARCHIVE:
        if KIND == "hls" and PAR_LIVE[0] and PAR_OK[0]:
            t_run = time.time()
            why = live_hls_parallel(rq)
            first = False
            if stop.is_set() or TEST_ONCE:
                break
            if why == "fallback":
                PAR_LIVE[0] = False
                print("Parallel mode is not possible for this playlist, normal recording instead", flush=True)
            S["restarts"] += 1
            rq.put(("n", True, False))
            S["reason"] = why
            consec = 0 if time.time() - t_run > 30 else consec + 1
            print("Reconnect %d (parallel mode): %s" % (S["restarts"], why), flush=True)
            time.sleep(min(0.5 + 0.5 * consec, 5))
            continue
        if KIND == "ts" and TS_RAW:
            # Direct download of the MPEG-TS bytes: reconnect takes milliseconds (no ffmpeg start, no probing), so even a
            # server that drops the link every second costs (almost) nothing. The splitter joins / de-duplicates as before.
            t_run = time.time()
            reason, got = ts_pull(rq)
            first = False
            if stop.is_set() or TEST_ONCE:
                break
            S["restarts"] += 1
            rq.put(("n", True, True))
            S["reason"] = reason
            consec = 0 if got > 0 else consec + 1
            print("Reconnect %d: lasted %.1fs, got %.1f MB: %s" % (S["restarts"], time.time() - t_run, got / 1e6, reason), flush=True)
            if got == 0 and consec % 3 == 0:               # the server keeps refusing: try another set of headers (browser / referer / VLC ...)
                sets = header_sets(); hi[0] = (hi[0] + 1) % len(sets)
                HDR = sets[hi[0]][1]
                print("Server keeps refusing: now trying %s" % sets[hi[0]][0], flush=True)
            time.sleep(0.2 if got > 0 else min(0.5 + 0.5 * consec, 5))
            continue
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
        p = S["proc"] = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, bufsize=0, env=fenv())
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
    word = "Download" if ARCHIVE else "Recording"
    summary("## %s finished\n%d file(s), %s. %s" % (word, len(S["done"]), human(saved), ("[Download page](%s)" % page) if page else ""))
    rows = "\n".join("%d.  %s  ·  %s" % (i + 1, human(d["size"]), mmss(d["secs"])) for i, d in enumerate(S["done"][:30]))
    link = ('\n\n📂 <a href="%s">Download all files (one page)</a>' % page) if page else "\n\n⚠️ No file could be uploaded. See the run log."
    V = "│ "
    head = "\n".join([BOX_TOP, "%s%s <b>%s %s</b>%s  ·  <b>%s</b>" % (V, "🏁" if dl_ok else "⚠️", word, "𝗙𝗜𝗡𝗜𝗦𝗛𝗘𝗗", "" if dl_ok else " (NOT complete)", esc(NAME)), BOX_MID,
                       "%s📁 Files   <code>%d</code>" % (V, len(S["done"])), "%s💾 Size    <code>%s</code>" % (V, human(saved)),
                       "%s⏱ Time    <code>%s</code>" % (V, hms(time.time() - S["t0"])), BOX_MID,
                       "%s%s  🕒 %s" % (V, naim_sig(int(time.time())), clock()), BOX_END])
    sent = False
    if E("LIVE_CARD") != "0" and not DRY and _pil():
        try:
            png = live_card(len(HIST), True, HIST)
        except Exception as e:
            png = None
            print("final card:", repr(e)[:120], flush=True)
        if png:
            cap = head + "\n\n" + rows + link
            long = len(cap) > 1000
            if long:
                cap = head + link
            for cid in dict.fromkeys([c for c in [CHAT] + ALSO if c]):
                r = tg_photo("sendPhoto", {"chat_id": cid, "caption": cap, "parse_mode": "HTML"}, png)
                sent = sent or bool(r.get("ok"))
            if sent and long:
                say("📁 <b>Files</b>\n" + rows)
    if not sent:
        say("%s\n\n%s%s" % (head, rows, link))


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
