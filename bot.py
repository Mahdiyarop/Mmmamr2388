# ============================================================
# 🤖 Member Booster Pro — v11 FINAL (Railway Ready)
# 👨‍💻 Owner: @Mahdiyar_sfr2 (ID: 8438636173)
# ============================================================

import asyncio, sqlite3, time, random, re, logging, threading, os
from datetime import datetime, timezone
from collections import defaultdict
from pyrogram import Client, filters, idle
from pyrogram.types import Message, CallbackQuery, InlineKeyboardMarkup, InlineKeyboardButton
from pyrogram.enums import ParseMode, ChatMemberStatus
from pyrogram.errors import (
    FloodWait, PeerIdInvalid, UserAlreadyParticipant, ChatAdminRequired,
    UserNotParticipant, SessionPasswordNeeded, PhoneCodeInvalid,
    PhoneCodeExpired, PasswordHashInvalid, AuthKeyUnregistered,
    UserDeactivated, UserPrivacyRestricted, UsernameInvalid,
    UsernameNotOccupied, ChatWriteForbidden, RPCError, UserChannelsTooMuch,
    MessageNotModified, ReactionInvalid, UserNotMutualContact
)

# ==================== CONFIG ====================
OWNER_ID       = int(os.environ.get('OWNER_ID', 8438636173))
OWNER_USERNAME = "Mahdiyar_sfr2"
CREATOR        = "Mahdiyar"
API_ID         = int(os.environ.get('API_ID', 0))
API_HASH       = os.environ.get('API_HASH', '')
BOT_TOKEN      = os.environ.get('BOT_TOKEN', '')
BOT_NAME       = "Member Booster Pro v11"

OWNER_DAILY_LIMIT = 40
USER_DAILY_LIMIT  = 20
USER_MAX_ACCS     = 1
USER_MAX_TGTS     = 1

REACTIONS = ["💘", "🍓", "💔", "❤️‍🔥", "😭"]

ADD_DELAY_MIN   = 20
ADD_DELAY_MAX   = 40
ADD_CONCURRENCY = 5

REACT_DELAY_MIN = 1.5
REACT_DELAY_MAX = 3.0
REACT_DEFAULT   = 50
REACT_CONCURRENCY = 5

SCRAPE_DELAY = 0.05
ACTIVE_THRESHOLD = 5
MAX_CONCURRENT_JOBS = 10

# ==================== DB ====================
DB_FILE = os.environ.get('DB_FILE', 'booster_v11.db')

logging.basicConfig(format="%(asctime)s | %(levelname)s | %(message)s", level=logging.INFO)
log = logging.getLogger("booster")
SEP = "\n━━━━━━━━━━━━━━━━━━━\n"

conn = sqlite3.connect(DB_FILE, check_same_thread=False, timeout=30)
conn.execute("PRAGMA journal_mode=WAL")
conn.execute("PRAGMA synchronous=NORMAL")
cur = conn.cursor()

cur.executescript("""
CREATE TABLE IF NOT EXISTS users(
    user_id INTEGER PRIMARY KEY,
    username TEXT, first_name TEXT,
    is_banned INTEGER DEFAULT 0, ban_reason TEXT,
    max_accounts INTEGER DEFAULT 1,
    max_targets INTEGER DEFAULT 1,
    daily_react_limit INTEGER DEFAULT 1,
    joined_at TEXT DEFAULT CURRENT_TIMESTAMP,
    last_seen TEXT);

CREATE TABLE IF NOT EXISTS accounts(
    id INTEGER PRIMARY KEY AUTOINCREMENT, owner_id INTEGER NOT NULL,
    phone TEXT, name TEXT, session TEXT UNIQUE,
    is_active INTEGER DEFAULT 1, cooldown_until REAL DEFAULT 0,
    added_today INTEGER DEFAULT 0, day TEXT,
    total_added INTEGER DEFAULT 0, flood_count INTEGER DEFAULT 0,
    added_at TEXT DEFAULT CURRENT_TIMESTAMP);
CREATE INDEX IF NOT EXISTS ix_acc_owner ON accounts(owner_id);
CREATE INDEX IF NOT EXISTS ix_acc_phone ON accounts(owner_id, phone);

CREATE TABLE IF NOT EXISTS targets(
    id INTEGER PRIMARY KEY AUTOINCREMENT, owner_id INTEGER NOT NULL,
    chat_id INTEGER, title TEXT, is_active INTEGER DEFAULT 1,
    total_added INTEGER DEFAULT 0, added_at TEXT DEFAULT CURRENT_TIMESTAMP,
    UNIQUE(owner_id, chat_id));

CREATE TABLE IF NOT EXISTS harvested(
    id INTEGER PRIMARY KEY AUTOINCREMENT, owner_id INTEGER NOT NULL,
    user_id INTEGER NOT NULL, username TEXT, first_name TEXT,
    is_premium INTEGER DEFAULT 0, msg_count INTEGER DEFAULT 0,
    is_active INTEGER DEFAULT 0, source TEXT, used INTEGER DEFAULT 0,
    is_reactor INTEGER DEFAULT 0, react_count INTEGER DEFAULT 0,
    is_channel INTEGER DEFAULT 0,
    added_at TEXT DEFAULT CURRENT_TIMESTAMP,
    UNIQUE(owner_id, user_id));
CREATE INDEX IF NOT EXISTS ix_hv_owner ON harvested(owner_id);

CREATE TABLE IF NOT EXISTS reactions_sent(
    id INTEGER PRIMARY KEY AUTOINCREMENT, owner_id INTEGER NOT NULL,
    chat_id INTEGER, msg_id INTEGER, emoji TEXT,
    sent_at TEXT DEFAULT CURRENT_TIMESTAMP,
    UNIQUE(owner_id, chat_id, msg_id));

CREATE TABLE IF NOT EXISTS reaction_marks(
    id INTEGER PRIMARY KEY AUTOINCREMENT, owner_id INTEGER NOT NULL,
    account_id INTEGER NOT NULL, chat_id INTEGER, msg_id INTEGER, emoji TEXT,
    sent_at TEXT DEFAULT CURRENT_TIMESTAMP,
    UNIQUE(account_id, chat_id, msg_id));

CREATE TABLE IF NOT EXISTS watches(
    id INTEGER PRIMARY KEY AUTOINCREMENT, owner_id INTEGER NOT NULL,
    chat_id INTEGER, title TEXT, ref TEXT, last_id INTEGER DEFAULT -1,
    is_active INTEGER DEFAULT 1, total_reacted INTEGER DEFAULT 0,
    added_at TEXT DEFAULT CURRENT_TIMESTAMP,
    UNIQUE(owner_id, chat_id));

CREATE TABLE IF NOT EXISTS added_log(
    id INTEGER PRIMARY KEY AUTOINCREMENT, owner_id INTEGER NOT NULL,
    target_id INTEGER, target_title TEXT,
    user_id INTEGER, username TEXT, first_name TEXT,
    account_phone TEXT, status TEXT, error TEXT,
    added_at TEXT DEFAULT CURRENT_TIMESTAMP);
CREATE INDEX IF NOT EXISTS ix_log_owner ON added_log(owner_id, target_id);

CREATE TABLE IF NOT EXISTS reacted_log(
    id INTEGER PRIMARY KEY AUTOINCREMENT, owner_id INTEGER NOT NULL,
    chat_id INTEGER, chat_title TEXT, msg_id INTEGER,
    emoji TEXT, account_phone TEXT, status TEXT, error TEXT,
    sent_at TEXT DEFAULT CURRENT_TIMESTAMP);
CREATE INDEX IF NOT EXISTS ix_rlog_owner ON reacted_log(owner_id, chat_id);

CREATE TABLE IF NOT EXISTS authorized_users(
    user_id INTEGER PRIMARY KEY,
    username TEXT, first_name TEXT, approved_by INTEGER,
    approved_at TEXT DEFAULT CURRENT_TIMESTAMP, is_active INTEGER DEFAULT 1);

CREATE TABLE IF NOT EXISTS access_requests(
    user_id INTEGER PRIMARY KEY, username TEXT, first_name TEXT,
    requested_at TEXT DEFAULT CURRENT_TIMESTAMP,
    status TEXT DEFAULT 'pending');
""")
conn.commit()

# ==================== STATE ====================
db_lock = threading.RLock()
clients = {}
_me_ids = {}
_load_locks = {}
user_states = {}
running_jobs = set()
bg_tasks = set()
_daily_task = None
_watch_task = None

WATCH_INTERVAL    = 4
WATCH_CONCURRENCY = 5
_peer_cache  = {}
_peer_fail   = {}
_react_locks = {}
_watch_busy  = set()

COMMANDS = ["start", "stop", "status", "users", "revoke", "ban", "unban"]

PERMANENT_ERRORS = {"privacy_restricted", "not_mutual", "too_many_channels", "deleted",
                    "is_bot", "user_not_found", "not_joined_after_add", "user_kicked"}

def is_owner(uid): return uid == OWNER_ID

def is_authorized(uid):
    if is_owner(uid): return True
    with db_lock:
        row = cur.execute("SELECT is_active FROM authorized_users WHERE user_id=?", (uid,)).fetchone()
    return bool(row and row[0] == 1)

def _today_utc(): return datetime.now(timezone.utc).date().isoformat()

def daily_limit(owner):
    return OWNER_DAILY_LIMIT if is_owner(owner) else USER_DAILY_LIMIT

def get_or_create_user(uid, username="", first_name=""):
    with db_lock:
        row = cur.execute("SELECT user_id, is_banned FROM users WHERE user_id=?", (uid,)).fetchone()
        if not row:
            cur.execute(
                "INSERT INTO users(user_id, username, first_name, max_accounts, max_targets, daily_react_limit) "
                "VALUES(?,?,?,?,?,?)",
                (uid, username, first_name, USER_MAX_ACCS, USER_MAX_TGTS, 1))
            conn.commit()
            return {"user_id": uid, "is_banned": 0, "is_new": True}
        cur.execute("UPDATE users SET last_seen=?, username=?, first_name=? WHERE user_id=?",
                    (datetime.now(timezone.utc).isoformat(), username, first_name, uid))
        conn.commit()
        return {"user_id": uid, "is_banned": row[1], "is_new": False}

def get_user_limits(uid):
    if is_owner(uid):
        return {"max_accounts": 999, "max_targets": 999, "daily_react_limit": 10**9}
    with db_lock:
        r = cur.execute("SELECT max_accounts, max_targets, daily_react_limit FROM users WHERE user_id=?", (uid,)).fetchone()
    if not r:
        return {"max_accounts": USER_MAX_ACCS, "max_targets": USER_MAX_TGTS, "daily_react_limit": 1}
    return {"max_accounts": r[0] or USER_MAX_ACCS, "max_targets": r[1] or USER_MAX_TGTS,
            "daily_react_limit": r[2]}

def is_banned(uid):
    if is_owner(uid): return False
    with db_lock:
        r = cur.execute("SELECT is_banned FROM users WHERE user_id=?", (uid,)).fetchone()
    return bool(r and r[0])

def reset_daily():
    today = _today_utc()
    with db_lock:
        cur.execute("UPDATE accounts SET added_today=0, day=? WHERE day IS NULL OR day!=?", (today, today))
        conn.commit()

async def daily_reset_loop():
    while True:
        try:
            reset_daily()
        except Exception as e:
            log.error(f"daily_reset: {repr(e)[:100]}")
        await asyncio.sleep(600)

def user_jobs(uid):
    return [k for k in running_jobs if k.rsplit("_", 1)[-1] == str(uid)]

def stop_user_jobs(uid):
    keys = user_jobs(uid)
    for k in keys:
        running_jobs.discard(k)
    return len(keys)

def spawn(coro):
    t = asyncio.create_task(coro)
    bg_tasks.add(t)
    t.add_done_callback(bg_tasks.discard)
    return t

# ==================== BOT ====================
bot = Client("booster_bot_v11", api_id=API_ID, api_hash=API_HASH, bot_token=BOT_TOKEN, in_memory=True)

async def safe_send(target, text, **kw):
    text = text[:4000]
    for plain in (False, True):
        try:
            k = dict(kw)
            if plain: k["parse_mode"] = ParseMode.DISABLED
            if hasattr(target, "reply_text"):
                return await target.reply_text(text, **k)
            return await bot.send_message(target, text, **k)
        except MessageNotModified:
            return None
        except Exception as e:
            log.error(f"send({'plain' if plain else 'md'}): {repr(e)[:120]}")
    return None

async def safe_edit(msg, text, **kw):
    if not msg: return None
    text = text[:4000]
    for plain in (False, True):
        try:
            k = dict(kw)
            if plain: k["parse_mode"] = ParseMode.DISABLED
            return await msg.edit_text(text, **k)
        except MessageNotModified:
            return msg
        except Exception as e:
            log.error(f"edit({'plain' if plain else 'md'}): {repr(e)[:120]}")
    return None

async def throttled_edit(msg, text, st, interval=3, **kw):
    now = time.time()
    if now - st.get("last", 0) >= interval:
        st["last"] = now
        await safe_edit(msg, text, **kw)

# ==================== RESOLVE CHAT ====================
_TME = re.compile(r"^(?:https?://)?(?:www\.)?(?:t|telegram)\.me/(?!\+|joinchat/)([A-Za-z0-9_]{4,})/?(?:\?.*)?$", re.I)

def normalize_ref(text):
    if not isinstance(text, str): return text
    t = text.strip()
    m = _TME.match(t)
    if m: return m.group(1)
    if re.fullmatch(r"-?\d+", t): return int(t)
    if t.startswith("@"): return t[1:]
    return t

def is_invite(ref):
    return isinstance(ref, str) and ("joinchat/" in ref or "t.me/+" in ref or "telegram.me/+" in ref or ref.startswith("+"))

async def resolve_chat(c, ref, allow_join=False):
    ref = normalize_ref(ref)
    entity = None
    try:
        entity = await c.get_chat(ref)
    except Exception as e:
        if not (allow_join and is_invite(ref)):
            return None, None, f"get_chat: {repr(e)[:80]}"

    if entity is None or getattr(entity, "id", None) is None:
        if allow_join and is_invite(ref):
            try:
                entity = await c.join_chat(ref)
            except UserAlreadyParticipant:
                try:
                    entity = await c.get_chat(ref)
                except Exception as e:
                    return None, None, f"get_chat: {repr(e)[:80]}"
            except Exception as e:
                return None, None, f"join: {repr(e)[:80]}"
        else:
            return None, None, "لینک دعوت: اکانت عضو نیست"
        if entity is None or getattr(entity, "id", None) is None:
            return None, None, "cannot resolve chat"

    peer = None
    for cand in (entity.id, getattr(entity, "username", None), ref):
        if cand is None: continue
        try:
            peer = await c.resolve_peer(cand)
            break
        except Exception:
            continue
    if peer is None:
        return entity, None, "cannot resolve peer"
    return entity, peer, None

# ==================== ACCOUNT LOAD ====================
async def _safe_stop(c, timeout=5):
    try:
        await asyncio.wait_for(c.stop(), timeout=timeout)
        return True
    except Exception:
        return False

async def _safe_disconnect(c, timeout=5):
    try:
        await asyncio.wait_for(c.disconnect(), timeout=timeout)
        return True
    except Exception:
        return await _safe_stop(c, timeout)

async def load_account(aid):
    with db_lock:
        row = cur.execute("SELECT session, phone, owner_id FROM accounts WHERE id=?", (aid,)).fetchone()
    if not row: return False
    session, phone, owner = row

    old = clients.pop(aid, None)
    if old: await _safe_stop(old)

    try:
        c = Client(f"acc_{aid}", api_id=API_ID, api_hash=API_HASH,
                   session_string=session, in_memory=True, no_updates=True)
        await c.start()
        me = await c.get_me()
        clients[aid] = c
        _me_ids[aid] = me.id
        log.info(f"✅ Loaded {phone}")
        return True
    except (AuthKeyUnregistered, UserDeactivated):
        with db_lock:
            cur.execute("UPDATE accounts SET is_active=0 WHERE id=?", (aid,))
            conn.commit()
        log.warning(f"❌ Dead {phone}")
        return False
    except Exception as e:
        log.error(f"❌ Load {phone}: {repr(e)[:100]}")
        return False

async def ensure_loaded(aid):
    lock = _load_locks.setdefault(aid, asyncio.Lock())
    async with lock:
        c = clients.get(aid)
        if c is not None and getattr(c, "is_connected", False):
            return True
        return await load_account(aid)

async def ensure_accounts_loaded(accounts):
    sem = asyncio.Semaphore(5)
    async def _l(a):
        async with sem:
            return a if await ensure_loaded(a[0]) else None
    res = await asyncio.gather(*[_l(a) for a in accounts], return_exceptions=True)
    return [r for r in res if r and not isinstance(r, Exception)]

async def load_all_accounts(owner_id=None):
    with db_lock:
        if owner_id:
            rows = cur.execute("SELECT id FROM accounts WHERE is_active=1 AND owner_id=?", (owner_id,)).fetchall()
        else:
            rows = cur.execute("SELECT id FROM accounts WHERE is_active=1").fetchall()
    total = len(rows)
    done = [0]
    sem = asyncio.Semaphore(5)
    async def _l(aid):
        async with sem:
            r = await ensure_loaded(aid)
            done[0] += 1
            if done[0] % 5 == 0 or done[0] == total:
                log.info(f"⏳ loading accounts {done[0]}/{total}")
            return r
    await asyncio.gather(*[_l(r[0]) for r in rows], return_exceptions=True)
    log.info(f"✅ Loaded {len(clients)}/{total} accounts")

def cooldown(aid, secs, owner=None):
    with db_lock:
        cur.execute("UPDATE accounts SET cooldown_until=?, flood_count=flood_count+1 WHERE id=?",
                    (time.time() + min(secs, 6 * 3600), aid))
        conn.commit()
    log.info(f"⏸ acc#{aid} cooldown {int(secs)}s")

def deactivate_account(aid):
    with db_lock:
        cur.execute("UPDATE accounts SET is_active=0 WHERE id=?", (aid,))
        conn.commit()
    clients.pop(aid, None)

def get_accounts(owner_id, order="added_today ASC", limit=200):
    with db_lock:
        return cur.execute(
            f"SELECT id, phone, name, added_today FROM accounts "
            f"WHERE owner_id=? AND is_active=1 ORDER BY {order} LIMIT ?",
            (owner_id, limit)).fetchall()

def get_available_accounts(owner_id):
    with db_lock:
        return cur.execute(
            "SELECT id, phone, name, added_today FROM accounts "
            "WHERE owner_id=? AND is_active=1 AND cooldown_until<? ORDER BY added_today ASC",
            (owner_id, time.time())).fetchall()

# ==================== REACTION ====================
FATAL_REACT = ("BANNED", "FORBIDDEN", "PEER_ID_INVALID", "CHANNEL_PRIVATE", "USER_DEACTIVATED", "AUTH_KEY")

async def _try_send_reaction(c, peer, msg_id, emoji):
    from pyrogram.raw.functions.messages import SendReaction
    from pyrogram.raw.types import ReactionEmoji
    try:
        await c.invoke(SendReaction(
            peer=peer, msg_id=msg_id,
            reaction=[ReactionEmoji(emoticon=emoji)]))
        return True, None
    except ReactionInvalid:
        return False, "invalid"
    except FloodWait as e:
        return False, ("flood", e.value)
    except Exception as e:
        err = repr(e)
        up = err.upper()
        if "REACTION_SAME" in up:
            return True, "same"
        if "REACTION_INVALID" in up:
            return False, "invalid"
        if "MESSAGE_ID_INVALID" in up:
            return False, ("skipmsg", err[:60])
        if any(f in up for f in FATAL_REACT):
            return False, ("fatal", err[:80])
        return False, ("error", err[:80])

async def send_reaction_retry(c, peer, msg_id, emoji):
    s, info = await _try_send_reaction(c, peer, msg_id, emoji)
    if not s and isinstance(info, tuple) and info[0] == "flood" and info[1] <= 90:
        await asyncio.sleep(info[1] + 1)
        s, info = await _try_send_reaction(c, peer, msg_id, emoji)
    return s, info

def _log_react(owner, chat_id, title, msg_id, emoji, phone, status, error=None):
    with db_lock:
        cur.execute(
            "INSERT INTO reacted_log(owner_id, chat_id, chat_title, msg_id, emoji, account_phone, status, error) "
            "VALUES(?,?,?,?,?,?,?,?)",
            (owner, chat_id, title, msg_id, emoji, phone, status, error))
        conn.commit()

async def react_account(owner, aid, phone, ref, chat_id, title, msg_ids, job_key, st, status_msg):
    c = clients.get(aid)
    if not c: return
    entity, peer, err = await resolve_chat(c, ref, allow_join=True)
    if err or entity is None or peer is None:
        st["errors"].append(f"{phone}: {err}")
        return
    real_chat_id = entity.id
    consecutive_fail = 0

    for mid in msg_ids:
        if job_key not in running_jobs: return
        with db_lock:
            seen = cur.execute(
                "SELECT 1 FROM reaction_marks WHERE account_id=? AND chat_id=? AND msg_id=?",
                (aid, real_chat_id, mid)).fetchone()
        if seen:
            st["skip"] += 1
            continue

        done = False
        for emoji in random.sample(REACTIONS, len(REACTIONS)):
            s, info = await send_reaction_retry(c, peer, mid, emoji)
            if s:
                with db_lock:
                    cur.execute(
                        "INSERT OR IGNORE INTO reaction_marks(owner_id, account_id, chat_id, msg_id, emoji) "
                        "VALUES(?,?,?,?,?)", (owner, aid, real_chat_id, mid, emoji))
                    conn.commit()
                _log_react(owner, real_chat_id, title, mid, emoji, phone, "success")
                st["ok"] += 1
                consecutive_fail = 0
                done = True
                break
            if isinstance(info, tuple):
                if info[0] == "flood":
                    _log_react(owner, real_chat_id, title, mid, emoji, phone, "flood", f"wait={info[1]}")
                    cooldown(aid, info[1], owner)
                    st["floods"] += 1
                    return
                if info[0] == "fatal":
                    _log_react(owner, real_chat_id, title, mid, emoji, phone, "fail", info[1])
                    st["bad"] += 1
                    st["errors"].append(f"{phone}: {info[1][:50]}")
                    return
                if info[0] == "skipmsg":
                    break
        if not done:
            st["bad"] += 1
            consecutive_fail += 1
            _log_react(owner, real_chat_id, title, mid, REACTIONS[0], phone, "fail", "all_emojis_failed")
            if consecutive_fail >= 10:
                st["errors"].append(f"{phone}: ۱۰ شکست پشت‌هم")
                return

        await throttled_edit(status_msg,
            f"⚡️ در حال ری‌اکشن...\n{SEP}✅ {st['ok']}\n❌ {st['bad']}\n⏭ {st['skip']}\n🌊 {st['floods']}", st, 3)
        await asyncio.sleep(random.uniform(REACT_DELAY_MIN, REACT_DELAY_MAX))

async def react_job(owner_id, target, limit, status_msg):
    job_key = f"react_{owner_id}"
    running_jobs.add(job_key)
    try:
        reset_daily()
        accounts = get_available_accounts(owner_id)
        if not accounts:
            await safe_edit(status_msg, "❌ اکانت آزادی نیست (کولداون یا غیرفعال).", reply_markup=back_kb())
            return
        active = await ensure_accounts_loaded(accounts)
        if not active:
            await safe_edit(status_msg, "❌ اکانتی لود نشد!", reply_markup=back_kb())
            return

        ref = normalize_ref(target)
        entity = peer = None
        first_acc = None
        last_err = None
        for a in active:
            entity, peer, last_err = await resolve_chat(clients[a[0]], ref, allow_join=True)
            if entity is not None and peer is not None:
                first_acc = a
                break
        if first_acc is None:
            await safe_edit(status_msg, f"❌ پیدا نشد: {last_err}", reply_markup=back_kb())
            return

        real_chat_id = entity.id
        chat_title = entity.title or str(real_chat_id)

        msg_ids = []
        try:
            async for m in clients[first_acc[0]].get_chat_history(real_chat_id, limit=limit * 2):
                if m.id and not m.service:
                    msg_ids.append(m.id)
                if len(msg_ids) >= limit:
                    break
        except Exception as e:
            await safe_edit(status_msg, f"❌ خواندن پیام‌ها: {repr(e)[:100]}", reply_markup=back_kb())
            return
        if not msg_ids:
            await safe_edit(status_msg, "❌ پیامی پیدا نشد.", reply_markup=back_kb())
            return

        await safe_edit(status_msg,
            f"⚡️ ری‌اکشن انبوه\n{SEP}🎯 {chat_title}\n📨 {len(msg_ids)} پیام\n📱 {len(active)} اکانت\n\n⏳ شروع...")

        st = {"ok": 0, "bad": 0, "skip": 0, "floods": 0, "errors": [], "last": 0}
        sem = asyncio.Semaphore(REACT_CONCURRENCY)

        async def run(a):
            async with sem:
                try:
                    await react_account(owner_id, a[0], a[1], ref, real_chat_id, chat_title,
                                        msg_ids, job_key, st, status_msg)
                except Exception as e:
                    st["errors"].append(f"{a[1]}: {repr(e)[:50]}")
                    log.error(f"react worker: {repr(e)[:100]}")

        await asyncio.gather(*[run(a) for a in active], return_exceptions=True)

        stopped = job_key not in running_jobs
        text = (f"{'🛑 متوقف شد' if stopped else '🎉 ری‌اکشن تموم شد!'}\n{SEP}"
                f"✅ موفق: {st['ok']}\n❌ ناموفق: {st['bad']}\n⏭ رد: {st['skip']}\n🌊 فلود: {st['floods']}")
        if st["errors"]:
            text += "\n\n⚠️ مشکل اکانت‌ها:\n" + "\n".join(f"• {e}" for e in st["errors"][:5])
        await safe_edit(status_msg, text, reply_markup=InlineKeyboardMarkup([
            [InlineKeyboardButton("📋 گزارش ری‌اکشن", callback_data=f"report_react_{real_chat_id}")],
            [InlineKeyboardButton("🔙 منو", callback_data="main")]]))
    except Exception as e:
        log.error(f"react_job: {repr(e)[:150]}")
        await safe_edit(status_msg, f"❌ خطا: {repr(e)[:120]}", reply_markup=back_kb())
    finally:
        running_jobs.discard(job_key)

# ==================== ADD MEMBER ====================
async def add_member_real(client, target_chat_id, user_id, username=""):
    u = None
    if username:
        try:
            u = await client.get_users(username)
            if u and u.id != user_id:
                u = None
        except Exception:
            u = None
    if u is None:
        try:
            u = await client.get_users(user_id)
        except Exception as e:
            return {"success": False, "error": f"resolve:{str(e)[:40]}"}
    if not u: return {"success": False, "error": "user_not_found"}
    if getattr(u, "is_bot", False): return {"success": False, "error": "is_bot"}
    if getattr(u, "is_deleted", False): return {"success": False, "error": "deleted"}
    real_uid = u.id

    try:
        await client.add_chat_members(target_chat_id, real_uid)
    except UserAlreadyParticipant:
        return {"success": False, "error": "already_member"}
    except UserPrivacyRestricted:
        return {"success": False, "error": "privacy_restricted"}
    except UserNotMutualContact:
        return {"success": False, "error": "not_mutual"}
    except UserChannelsTooMuch:
        return {"success": False, "error": "too_many_channels"}
    except ChatAdminRequired:
        return {"success": False, "error": "not_admin"}
    except FloodWait as e:
        return {"success": False, "error": "flood", "wait": e.value}
    except PeerIdInvalid:
        return {"success": False, "error": "invalid_peer"}
    except UserNotParticipant:
        return {"success": False, "error": "not_participant"}
    except RPCError as e:
        err = str(e).upper()
        if "PEER_FLOOD" in err: return {"success": False, "error": "flood", "wait": 6 * 3600}
        if "USER_BANNED_IN_CHANNEL" in err: return {"success": False, "error": "flood", "wait": 6 * 3600}
        if "AUTH_KEY" in err or "USER_DEACTIVATED" in err: return {"success": False, "error": "account_dead"}
        if "USER_NOT_MUTUAL_CONTACT" in err: return {"success": False, "error": "not_mutual"}
        if "USER_PRIVACY_RESTRICTED" in err: return {"success": False, "error": "privacy_restricted"}
        if "PEER_ID_INVALID" in err: return {"success": False, "error": "invalid_peer"}
        if "USER_ALREADY_PARTICIPANT" in err: return {"success": False, "error": "already_member"}
        if "CHAT_ADMIN_REQUIRED" in err: return {"success": False, "error": "not_admin"}
        if "USER_CHANNELS_TOO_MUCH" in err: return {"success": False, "error": "too_many_channels"}
        if "USER_KICKED" in err: return {"success": False, "error": "user_kicked"}
        return {"success": False, "error": f"rpc:{str(e)[:40]}"}
    except Exception as e:
        return {"success": False, "error": str(e)[:60]}

    await asyncio.sleep(2)
    try:
        m = await client.get_chat_member(target_chat_id, real_uid)
        st = str(getattr(m, "status", "")).lower()
        if "left" in st or "kicked" in st or "banned" in st:
            return {"success": False, "error": "not_joined_after_add"}
        return {"success": True, "error": None}
    except UserNotParticipant:
        return {"success": False, "error": "not_joined_after_add"}
    except Exception as e:
        return {"success": False, "error": f"verify_fail:{str(e)[:40]}"}

async def check_admin(aid, c, chat_id):
    try:
        me_id = _me_ids.get(aid)
        if not me_id:
            me_id = (await c.get_me()).id
            _me_ids[aid] = me_id
        m = await c.get_chat_member(chat_id, me_id)
        if m.status not in (ChatMemberStatus.ADMINISTRATOR, ChatMemberStatus.OWNER):
            return False, "ادمین نیست"
        priv = getattr(m, "privileges", None)
        if priv is not None and getattr(priv, "can_invite_users", True) is False:
            return False, "دسترسی Add Users نداره"
        return True, "ok"
    except UserNotParticipant:
        return False, "عضو گروه نیست"
    except Exception as e:
        return False, repr(e)[:50]

# ==================== LOG HELPERS ====================
def log_add(owner_id, target_id, title, uid, uname, fname, phone, status, error=None):
    with db_lock:
        cur.execute(
            "INSERT INTO added_log(owner_id, target_id, target_title, user_id, username, "
            "first_name, account_phone, status, error) VALUES(?,?,?,?,?,?,?,?,?)",
            (owner_id, target_id, title, uid, uname, fname, phone, status, error))
        conn.commit()

def mark_added(aid, owner_id, target_id):
    with db_lock:
        cur.execute("UPDATE accounts SET added_today=added_today+1, total_added=total_added+1 WHERE id=?", (aid,))
        cur.execute("UPDATE targets SET total_added=total_added+1 WHERE id=? AND owner_id=?", (target_id, owner_id))
        conn.commit()

def set_used(owner_id, uid, value):
    with db_lock:
        cur.execute("UPDATE harvested SET used=? WHERE owner_id=? AND user_id=?", (value, owner_id, uid))
        conn.commit()

def get_members_to_add(owner_id, limit=100):
    with db_lock:
        return cur.execute(
            """SELECT user_id, username, first_name FROM harvested
               WHERE owner_id=? AND used=0 AND is_channel=0
               ORDER BY (COALESCE(username,'')!='') DESC, is_premium DESC, msg_count DESC LIMIT ?""",
            (owner_id, limit)).fetchall()

# ==================== ADD MEMBERS JOB ====================
def _add_text(title, c, limit, n_acc, head="🚀 در حال افزودن..."):
    return (f"{head}\n{SEP}🎯 {title}\n📱 {n_acc} اکانت\n"
            f"✅ {c['added']}/{limit}\n❌ {c['failed']}\n⏭ {c['skipped']}\n🌊 {c['floods']}")

async def add_members_job(owner_id, target_id, limit, status_msg):
    job_key = f"add_{owner_id}"
    running_jobs.add(job_key)
    try:
        await _add_members_inner(owner_id, target_id, limit, status_msg, job_key)
    except Exception as e:
        log.error(f"add_job: {repr(e)[:150]}")
        await safe_edit(status_msg, f"❌ خطا: {repr(e)[:120]}", reply_markup=back_kb())
    finally:
        running_jobs.discard(job_key)

async def _add_members_inner(owner_id, target_id, limit, status_msg, job_key):
    with db_lock:
        target = cur.execute("SELECT chat_id, title FROM targets WHERE id=? AND owner_id=?",
                             (target_id, owner_id)).fetchone()
    if not target:
        await safe_edit(status_msg, "❌ گروه پیدا نشد!", reply_markup=back_kb()); return
    target_chat_id, target_title = target

    reset_daily()
    members = get_members_to_add(owner_id, limit * 3)
    if not members:
        await safe_edit(status_msg, "❌ عضوی نیست! اول اسکرپ کن.", reply_markup=back_kb()); return

    dlim = daily_limit(owner_id)
    accounts = [a for a in get_available_accounts(owner_id) if (a[3] or 0) < dlim]
    if not accounts:
        await safe_edit(status_msg, "❌ اکانت آزادی نیست (سقف روزانه / کولداون / غیرفعال).",
                        reply_markup=back_kb()); return

    loaded = await ensure_accounts_loaded(accounts)
    if not loaded:
        await safe_edit(status_msg, "❌ اکانتی لود نشد!", reply_markup=back_kb()); return

    usable, notes = [], []
    for a in loaded:
        ok, why = await check_admin(a[0], clients[a[0]], target_chat_id)
        if ok: usable.append(a)
        else: notes.append(f"{a[1]}: {why}")
    if not usable:
        await safe_edit(status_msg,
            f"❌ هیچ اکانتی ادمین گروه {target_title} نیست!\n\n" + "\n".join(f"• {n}" for n in notes[:8]) +
            "\n\n💡 اکانت‌ها باید ادمین با دسترسی Add Users باشن.", reply_markup=back_kb())
        return

    note_txt = ("\n⚠️ کنار گذاشته شد:\n" + "\n".join(f"• {n}" for n in notes[:5])) if notes else ""
    await safe_edit(status_msg,
        f"🚀 شروع افزودن...\n{SEP}🎯 {target_title}\n👥 هدف: {limit}\n📱 اکانت: {len(usable)}{note_txt}")

    queue = asyncio.Queue()
    for m in members:
        queue.put_nowait(m)

    counters = {"added": 0, "failed": 0, "skipped": 0, "floods": 0, "inflight": 0}
    lock = asyncio.Lock()
    ui = {"last": 0}

    async def worker(acc):
        aid, phone, name, added0 = acc
        client = clients.get(aid)
        if not client: return
        quota = dlim - (added0 or 0)
        done_here = 0

        while job_key in running_jobs and done_here < quota:
            wait, m = False, None
            async with lock:
                if counters["added"] >= limit:
                    return
                if counters["added"] + counters["inflight"] >= limit:
                    wait = True
                else:
                    try:
                        m = queue.get_nowait()
                        counters["inflight"] += 1
                    except asyncio.QueueEmpty:
                        if counters["inflight"] == 0:
                            return
                        wait = True
            if wait:
                await asyncio.sleep(1)
                continue

            uid_, uname, fname = m
            requeue, quit_worker = False, False
            try:
                await asyncio.sleep(random.uniform(ADD_DELAY_MIN, ADD_DELAY_MAX))
                if job_key not in running_jobs:
                    requeue = quit_worker = True
                else:
                    r = await add_member_real(client, target_chat_id, uid_, uname or "")
                    err = r.get("error")
                    if r["success"]:
                        done_here += 1
                        counters["added"] += 1
                        mark_added(aid, owner_id, target_id)
                        set_used(owner_id, uid_, 1)
                        log_add(owner_id, target_id, target_title, uid_, uname, fname, phone, "success")
                    elif err == "flood":
                        wait_s = r.get("wait", 60)
                        cooldown(aid, wait_s, owner_id)
                        counters["floods"] += 1
                        log_add(owner_id, target_id, target_title, uid_, uname, fname, phone, "flood", f"wait={wait_s}")
                        requeue = quit_worker = True
                    elif err == "not_admin":
                        log_add(owner_id, target_id, target_title, uid_, uname, fname, phone, "fail", "not_admin")
                        requeue = quit_worker = True
                    elif err == "account_dead":
                        deactivate_account(aid)
                        log_add(owner_id, target_id, target_title, uid_, uname, fname, phone, "fail", "account_dead")
                        requeue = quit_worker = True
                    elif err == "already_member":
                        counters["skipped"] += 1
                        set_used(owner_id, uid_, 1)
                        log_add(owner_id, target_id, target_title, uid_, uname, fname, phone, "skip", "already_member")
                    else:
                        counters["failed"] += 1
                        if err in PERMANENT_ERRORS:
                            set_used(owner_id, uid_, 2)
                        log_add(owner_id, target_id, target_title, uid_, uname, fname, phone, "fail", err)
            except Exception as e:
                counters["failed"] += 1
                log.error(f"worker: {repr(e)[:100]}")
                log_add(owner_id, target_id, target_title, uid_, uname, fname, phone, "fail", repr(e)[:60])
            finally:
                async with lock:
                    counters["inflight"] -= 1
                    if requeue:
                        queue.put_nowait(m)

            await throttled_edit(status_msg, _add_text(target_title, counters, limit, len(usable)), ui, 3)
            if quit_worker:
                return

    sem = asyncio.Semaphore(ADD_CONCURRENCY)
    async def limited(a):
        try:
            async with sem:
                await worker(a)
        except Exception as e:
            log.error(f"worker: {repr(e)[:80]}")

    await asyncio.gather(*[limited(a) for a in usable], return_exceptions=True)

    stopped = job_key not in running_jobs
    with db_lock:
        remaining = cur.execute("SELECT COUNT(*) FROM harvested WHERE owner_id=? AND used=0", (owner_id,)).fetchone()[0]
    head = "🛑 متوقف شد" if stopped else "🎉 تموم شد!"
    text = (f"{head}\n{SEP}"
            f"✅ موفق (تأیید شده): {counters['added']}\n"
            f"❌ ناموفق: {counters['failed']}\n"
            f"⏭ رد: {counters['skipped']}\n"
            f"🌊 فلود: {counters['floods']}\n"
            f"📥 باقی‌مانده در مخزن: {remaining}")
    if counters["added"] < limit and not stopped:
        text += "\n\nℹ️ به هدف نرسید: سقف روزانه/فلود/کمبود عضو."
    await safe_edit(status_msg, text, reply_markup=InlineKeyboardMarkup([
        [InlineKeyboardButton("📋 گزارش افزودن", callback_data=f"report_add_{target_id}")],
        [InlineKeyboardButton("🔙 منو", callback_data="main")]]))

# ==================== SCRAPE ====================
async def scrape_job(owner_id, source, limit, status_msg, job_key):
    accounts = get_available_accounts(owner_id) or get_accounts(owner_id)
    if not accounts:
        await safe_edit(status_msg, "❌ اکانت نداری"); return 0
    aid = None
    for a in accounts:
        if await ensure_loaded(a[0]):
            aid = a[0]; break
    if aid is None:
        await safe_edit(status_msg, "❌ اکانت لود نشد"); return 0
    c = clients[aid]

    entity, peer, err = await resolve_chat(c, source, allow_join=True)
    if err or entity is None:
        await safe_edit(status_msg, f"❌ پیدا نشد: {err}"); return 0

    src_title = entity.title or getattr(entity, "username", None) or str(entity.id)
    counts = defaultdict(int)
    cache = {}
    fetched = 0

    try:
        async for msg in c.get_chat_history(entity.id, limit=limit):
            if job_key not in running_jobs:
                break
            fetched += 1
            u = msg.from_user
            if not u or u.is_bot or u.is_deleted:
                continue
            counts[u.id] += 1
            cache[u.id] = u
            if fetched % 300 == 0:
                await safe_edit(status_msg, f"🔎 اسکن...\n🎯 {src_title}\n📨 {fetched} | 👥 {len(counts)}")
            if fetched % 100 == 0:
                await asyncio.sleep(SCRAPE_DELAY)
    except FloodWait as e:
        cooldown(aid, e.value, owner_id)
        log.error(f"scrape flood {e.value}")
    except Exception as e:
        log.error(f"scrape: {e}")

    new_cnt = 0
    with db_lock:
        for uid_, cnt in counts.items():
            u = cache[uid_]
            is_p = 1 if getattr(u, "is_premium", False) else 0
            is_a = 1 if cnt >= ACTIVE_THRESHOLD else 0
            uname = getattr(u, "username", None) or ""
            fname = getattr(u, "first_name", None) or ""
            try:
                ex = cur.execute("SELECT id FROM harvested WHERE owner_id=? AND user_id=?",
                                 (owner_id, uid_)).fetchone()
                if ex:
                    cur.execute(
                        "UPDATE harvested SET msg_count=msg_count+?, is_premium=MAX(is_premium,?), "
                        "is_active=MAX(is_active,?), username=?, first_name=?, source=? WHERE id=?",
                        (cnt, is_p, is_a, uname, fname, src_title, ex[0]))
                else:
                    cur.execute(
                        "INSERT INTO harvested(owner_id, user_id, username, first_name, "
                        "is_premium, msg_count, is_active, source, is_channel) VALUES(?,?,?,?,?,?,?,?,0)",
                        (owner_id, uid_, uname, fname, is_p, cnt, is_a, src_title))
                    new_cnt += 1
            except Exception as e:
                log.warning(f"save: {e}")
        conn.commit()
    return new_cnt

# ==================== KEYBOARDS ====================
def main_menu():
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("➕ افزودن اکانت", callback_data="flow_addacc"),
         InlineKeyboardButton("🎯 افزودن گروه", callback_data="flow_addtarget")],
        [InlineKeyboardButton("🔎 اسکرپ", callback_data="flow_scrape"),
         InlineKeyboardButton("👥 افزودن اعضا", callback_data="flow_addmembers")],
        [InlineKeyboardButton("⚡️ ری‌اکشن", callback_data="flow_react"),
         InlineKeyboardButton("🤖 ری‌اکشن خودکار", callback_data="watch_menu")],
        [InlineKeyboardButton("📋 گزارش افزودن", callback_data="report_add_list"),
         InlineKeyboardButton("📊 آمار", callback_data="stats")],
        [InlineKeyboardButton("👤 اکانت‌ها", callback_data="acc_list"),
         InlineKeyboardButton("🎯 گروه‌ها", callback_data="tgt_list")],
        [InlineKeyboardButton("🛑 توقف کارها", callback_data="stop_jobs")],
    ])

def cancel_kb():
    return InlineKeyboardMarkup([[InlineKeyboardButton("❌ لغو", callback_data="cancel_flow")]])

def back_kb():
    return InlineKeyboardMarkup([[InlineKeyboardButton("🔙 منو", callback_data="main")]])

# ==================== FLOW ====================
async def clear_flow(uid):
    st = user_states.pop(uid, None)
    if st:
        c = st["data"].pop("client", None)
        if c is not None:
            await _safe_disconnect(c, 5)

async def start_flow(uid, flow, step):
    await clear_flow(uid)
    user_states[uid] = {"flow": flow, "step": step, "data": {}}
    await prompt_flow(uid)

async def prompt_flow(uid):
    st = user_states.get(uid)
    if not st: return
    flow, step, d = st["flow"], st["step"], st["data"]

    if flow == "addacc":
        if step == "phone":
            await safe_send(uid, "📱 شماره با کد کشور:\nمثال: `+989123456789`", reply_markup=cancel_kb())
        elif step == "code":
            await safe_send(uid, "🔢 کد تأیید:", reply_markup=cancel_kb())
        elif step == "password":
            await safe_send(uid, "🔐 رمز دوم (2FA):", reply_markup=cancel_kb())

    elif flow == "addtarget":
        await safe_send(uid,
            "🎯 آیدی/یوزرنیم/لینک گروه:\n`@mygroup`\n`https://t.me/mygroup`\n`-1001234567890`\n\n"
            "⚠️ اکانت باید قبلاً توی گروه ادمین باشه.",
            reply_markup=cancel_kb())

    elif flow == "scrape":
        if step == "source":
            await safe_send(uid, "🔎 منبع (آیدی/یوزرنیم/لینک):", reply_markup=cancel_kb())
        elif step == "count":
            await safe_send(uid, "📨 چند پیام؟ (مثلاً `5000`)", reply_markup=cancel_kb())

    elif flow == "addmembers":
        if step == "target":
            with db_lock:
                rows = cur.execute("SELECT id, title FROM targets WHERE owner_id=? AND is_active=1",
                                   (uid,)).fetchall()
            if not rows:
                await safe_send(uid, "❌ اول گروه هدف اضافه کن.", reply_markup=back_kb())
                user_states.pop(uid, None); return
            lines = ["🎯 کدوم گروه؟ شماره بفرست:\n"]
            for tid, title in rows:
                lines.append(f"`{tid}` — {title}")
            d["targets_list"] = [r[0] for r in rows]
            await safe_send(uid, "\n".join(lines), reply_markup=cancel_kb())
        elif step == "count":
            await safe_send(uid, "👥 چند نفر؟ (مثلاً `500`)", reply_markup=cancel_kb())

    elif flow == "react":
        if step == "target":
            await safe_send(uid, "⚡️ گروه/کانال هدف:\n`@mygroup` یا `-100...` یا لینک", reply_markup=cancel_kb())
        elif step == "count":
            await safe_send(uid,
                f"📨 چند پیام آخر؟ (عدد بفرست، `0` = پیش‌فرض {REACT_DEFAULT})",
                reply_markup=cancel_kb())

    elif flow == "addwatch":
        await safe_send(uid,
            "🤖 گروه برای ری‌اکشن خودکار:\n`@mygroup` یا `-100...` یا لینک دعوت\n\n"
            "از لحظه‌ی ثبت، به هر پیام جدید همه‌ی اکانت‌ها ری‌اکشن می‌زنن.",
            reply_markup=cancel_kb())

# ==================== TEXT ROUTER ====================
@bot.on_message(filters.private & filters.text & ~filters.command(COMMANDS))
async def flow_router(client, message):
    uid = message.from_user.id
    if not is_authorized(uid): return
    if is_banned(uid): return
    st = user_states.get(uid)
    if not st: return

    flow, step, d = st["flow"], st["step"], st["data"]
    text = message.text.strip()

    try:
        if flow == "addacc":
            if step == "phone":
                phone = text.replace(" ", "")
                try:
                    acc = Client(name=f"login_{uid}_{int(time.time())}",
                                 api_id=API_ID, api_hash=API_HASH,
                                 in_memory=True, no_updates=True)
                    await acc.connect()
                    d["client"] = acc
                    sent = await acc.send_code(phone)
                    d.update({"phone": phone, "hash": sent.phone_code_hash})
                    st["step"] = "code"
                    await prompt_flow(uid)
                except Exception as e:
                    await safe_send(uid, f"❌ {repr(e)[:150]}", reply_markup=back_kb()); await clear_flow(uid)
            elif step == "code":
                code = text.replace(" ", "").replace("-", "")
                try:
                    await d["client"].sign_in(phone_number=d["phone"], phone_code_hash=d["hash"], phone_code=code)
                except SessionPasswordNeeded:
                    st["step"] = "password"; await prompt_flow(uid); return
                except PhoneCodeInvalid:
                    await safe_send(uid, "❌ کد اشتباه. دوباره:"); return
                except PhoneCodeExpired:
                    await safe_send(uid, "❌ منقضی شد.", reply_markup=back_kb()); await clear_flow(uid); return
                await _finish_login(uid)
            elif step == "password":
                try:
                    await d["client"].check_password(password=text)
                except PasswordHashInvalid:
                    await safe_send(uid, "❌ رمز اشتباه. دوباره:"); return
                await _finish_login(uid)

        elif flow == "addtarget":
            accounts = get_accounts(uid)
            if not accounts:
                await safe_send(uid, "❌ اول اکانت اضافه کن.", reply_markup=back_kb()); await clear_flow(uid); return
            aid = accounts[0][0]
            if not await ensure_loaded(aid):
                await safe_send(uid, "❌ اکانت لود نشد", reply_markup=back_kb()); await clear_flow(uid); return
            entity, peer, err = await resolve_chat(clients[aid], text)
            if err or entity is None:
                await safe_send(uid, f"❌ {err}\nدوباره بفرست:"); return
            title = entity.title or str(entity.id)
            with db_lock:
                ex = cur.execute("SELECT id FROM targets WHERE owner_id=? AND chat_id=?", (uid, entity.id)).fetchone()
                if ex:
                    cur.execute("UPDATE targets SET title=?, is_active=1 WHERE id=?", (title, ex[0]))
                else:
                    n = cur.execute("SELECT COUNT(*) FROM targets WHERE owner_id=? AND is_active=1", (uid,)).fetchone()[0]
                    if n >= get_user_limits(uid)["max_targets"]:
                        await safe_send(uid, f"🚫 سقف گروه‌ها ({get_user_limits(uid)['max_targets']}) پر شده.",
                                        reply_markup=back_kb())
                        await clear_flow(uid); return
                    cur.execute("INSERT INTO targets(owner_id, chat_id, title) VALUES(?,?,?)", (uid, entity.id, title))
                conn.commit()
            await safe_send(uid, f"✅ اضافه شد: {title}\n`{entity.id}`", reply_markup=back_kb())
            await clear_flow(uid)

        elif flow == "scrape":
            if step == "source":
                d["source"] = text; st["step"] = "count"; await prompt_flow(uid)
            elif step == "count":
                try:
                    cnt = int(text); assert 0 < cnt <= 200000
                except Exception:
                    await safe_send(uid, "❌ عدد مثبت (حداکثر ۲۰۰۰۰۰):"); return
                if user_jobs(uid):
                    await safe_send(uid, "⏳ یک کار در حال اجراست. /stop بزن یا صبر کن."); return
                source = d["source"]
                await clear_flow(uid)
                jk = f"scrape_{uid}"
                running_jobs.add(jk)
                sm = await safe_send(uid, "🔎 شروع اسکن...")

                async def _run():
                    try:
                        n = await scrape_job(uid, source, cnt, sm, jk)
                        await safe_edit(sm, f"✅ اسکن تموم!\n🆕 جدید: {n}", reply_markup=back_kb())
                    except Exception as e:
                        await safe_edit(sm, f"❌ {repr(e)[:150]}", reply_markup=back_kb())
                    finally:
                        running_jobs.discard(jk)
                spawn(_run())

        elif flow == "addmembers":
            if step == "target":
                try:
                    tid = int(text)
                    if tid not in d.get("targets_list", []): raise ValueError
                except Exception:
                    await safe_send(uid, "❌ شماره از لیست:"); return
                with db_lock:
                    row = cur.execute("SELECT title FROM targets WHERE id=? AND owner_id=?", (tid, uid)).fetchone()
                if not row: await safe_send(uid, "❌ پیدا نشد"); return
                d["target_id"] = tid; d["target_title"] = row[0]
                st["step"] = "count"; await prompt_flow(uid)
            elif step == "count":
                try:
                    cnt = int(text); assert 0 < cnt <= 5000
                except Exception:
                    await safe_send(uid, "❌ عدد مثبت (حداکثر ۵۰۰۰):"); return
                if user_jobs(uid):
                    await safe_send(uid, "⏳ یک کار در حال اجراست. /stop بزن یا صبر کن."); return
                tid = d["target_id"]
                await clear_flow(uid)
                running_jobs.add(f"add_{uid}")
                sm = await safe_send(uid, "🚀 آماده‌سازی...")
                spawn(add_members_job(uid, tid, cnt, sm))

        elif flow == "react":
            if step == "target":
                d["target"] = text; st["step"] = "count"; await prompt_flow(uid)
            elif step == "count":
                try:
                    cnt = int(text); assert 0 <= cnt <= 1000
                except Exception:
                    await safe_send(uid, "❌ عدد بین 0 تا 1000:"); return
                cnt = cnt or REACT_DEFAULT
                if user_jobs(uid):
                    await safe_send(uid, "⏳ یک کار در حال اجراست. /stop بزن یا صبر کن."); return
                target = d["target"]
                await clear_flow(uid)
                running_jobs.add(f"react_{uid}")
                sm = await safe_send(uid, "⚡️ آماده‌سازی ری‌اکشن...")
                spawn(react_job(uid, target, cnt, sm))

        elif flow == "addwatch":
            accounts = get_available_accounts(uid) or get_accounts(uid)
            if not accounts:
                await safe_send(uid, "❌ اول اکانت اضافه کن.", reply_markup=back_kb()); await clear_flow(uid); return
            loaded = await ensure_accounts_loaded(accounts)
            if not loaded:
                await safe_send(uid, "❌ اکانتی لود نشد.", reply_markup=back_kb()); await clear_flow(uid); return
            entity = peer = None
            err = None
            used_c = None
            for a in loaded[:3]:
                entity, peer, err = await resolve_chat(clients[a[0]], text, allow_join=True)
                if entity is not None and peer is not None:
                    used_c = clients[a[0]]
                    break
            if used_c is None:
                await safe_send(uid, f"❌ {err}\nدوباره بفرست:"); return
            title = entity.title or str(entity.id)
            last_id = -1
            try:
                last_id = 0
                async for m in used_c.get_chat_history(entity.id, limit=1):
                    last_id = m.id
            except Exception:
                last_id = -1
            ref = str(normalize_ref(text))
            with db_lock:
                ex = cur.execute("SELECT id FROM watches WHERE owner_id=? AND chat_id=?", (uid, entity.id)).fetchone()
                if ex:
                    cur.execute("UPDATE watches SET title=?, ref=?, is_active=1, last_id=? WHERE id=?",
                                (title, ref, last_id, ex[0]))
                else:
                    n = cur.execute("SELECT COUNT(*) FROM watches WHERE owner_id=?", (uid,)).fetchone()[0]
                    if n >= get_user_limits(uid)["max_targets"]:
                        await safe_send(uid, f"🚫 سقف گروه‌های خودکار ({get_user_limits(uid)['max_targets']}) پر شده.",
                                        reply_markup=back_kb())
                        await clear_flow(uid); return
                    cur.execute("INSERT INTO watches(owner_id, chat_id, title, ref, last_id) VALUES(?,?,?,?,?)",
                                (uid, entity.id, title, ref, last_id))
                conn.commit()
            spawn(prejoin_watch(uid, entity.id, ref))
            await safe_send(uid,
                f"✅ ری‌اکشن خودکار فعال شد\n{SEP}🎯 {title}\n"
                f"📱 {len(loaded)} اکانت\n\nاز همین الان به پیام‌های جدید ری‌اکشن می‌زنن.",
                reply_markup=InlineKeyboardMarkup([
                    [InlineKeyboardButton("🤖 مدیریت", callback_data="watch_menu")],
                    [InlineKeyboardButton("🔙 منو", callback_data="main")]]))
            await clear_flow(uid)

    except Exception as e:
        log.error(f"flow err: {repr(e)[:200]}")
        await safe_send(uid, f"❌ {repr(e)[:150]}", reply_markup=back_kb())
        await clear_flow(uid)

async def _finish_login(uid):
    st = user_states.get(uid)
    if not st: return
    d = st["data"]
    acc = d["client"]
    try:
        me = await acc.get_me()
        ss = await acc.export_session_string()
        phone = me.phone_number or d["phone"]
        if not phone.startswith("+"): phone = "+" + phone
        name = f"{me.first_name or ''} {me.last_name or ''}".strip() or "Unknown"
        with db_lock:
            ex = cur.execute("SELECT id FROM accounts WHERE owner_id=? AND phone IN (?,?)",
                             (uid, phone, phone.lstrip("+"))).fetchone()
            if ex:
                cur.execute("UPDATE accounts SET session=?, name=?, phone=?, is_active=1, cooldown_until=0 WHERE id=?",
                            (ss, name, phone, ex[0]))
                aid = ex[0]
            else:
                n = cur.execute("SELECT COUNT(*) FROM accounts WHERE owner_id=? AND is_active=1", (uid,)).fetchone()[0]
                if n >= get_user_limits(uid)["max_accounts"]:
                    await clear_flow(uid)
                    await safe_send(uid, f"🚫 سقف اکانت‌ها ({get_user_limits(uid)['max_accounts']}) پر شده.",
                                    reply_markup=back_kb())
                    return
                cur.execute("INSERT INTO accounts(owner_id, phone, name, session, is_active, day) VALUES(?,?,?,?,1,?)",
                            (uid, phone, name, ss, _today_utc()))
                aid = cur.lastrowid
            conn.commit()
        await clear_flow(uid)
        old = clients.pop(aid, None)
        if old: await _safe_stop(old)
        ok = await load_account(aid)
        await safe_send(uid, f"✅ اکانت `{phone}` اضافه شد" + (" و لود شد!" if ok else " (لود نشد)"),
                        reply_markup=back_kb())
    except Exception as e:
        await safe_send(uid, f"❌ {repr(e)[:150]}", reply_markup=back_kb())
        await clear_flow(uid)

# ==================== LIST VIEWS ====================
async def show_accounts(msg, uid):
    with db_lock:
        rows = cur.execute(
            "SELECT id, phone, added_today, cooldown_until FROM accounts WHERE owner_id=? AND is_active=1 "
            "ORDER BY id", (uid,)).fetchall()
    if not rows:
        await safe_edit(msg, "📭 خالی", reply_markup=back_kb()); return
    lines = [f"👤 اکانت‌ها ({len(rows)})\n{SEP}"]
    kb = []
    now = time.time()
    for aid, phone, added, cd in rows[:40]:
        st = "🟢" if aid in clients else "⚪️"
        if cd and cd > now: st = "⏸"
        lines.append(f"{st} `{phone}` — امروز: {added}/{daily_limit(uid)}")
        kb.append([InlineKeyboardButton(f"🗑 حذف {phone}", callback_data=f"del_acc_{aid}")])
    lines.append("\n🟢 لود  ⚪️ آفلاین  ⏸ کولداون")
    kb.append([InlineKeyboardButton("🔙 منو", callback_data="main")])
    await safe_edit(msg, "\n".join(lines), reply_markup=InlineKeyboardMarkup(kb))

async def show_targets(msg, uid):
    with db_lock:
        rows = cur.execute("SELECT id, chat_id, title, total_added FROM targets WHERE owner_id=? AND is_active=1",
                           (uid,)).fetchall()
    if not rows:
        await safe_edit(msg, "📭 خالی", reply_markup=back_kb()); return
    lines = [f"🎯 گروه‌های هدف\n{SEP}"]
    kb = []
    for tid, cid, title, ta in rows:
        lines.append(f"#{tid} | {title}\n`{cid}` — ✅ {ta}")
        kb.append([InlineKeyboardButton(f"🗑 حذف {title[:25]}", callback_data=f"del_tgt_{tid}")])
    kb.append([InlineKeyboardButton("🔙 منو", callback_data="main")])
    await safe_edit(msg, "\n".join(lines), reply_markup=InlineKeyboardMarkup(kb))

# ==================== CALLBACKS ====================
@bot.on_callback_query()
async def cb_handler(client, cb):
    uid = cb.from_user.id
    data = cb.data or ""

    if data.startswith("apr_"):
        if not is_owner(uid): await cb.answer("🚫", show_alert=True); return
        t = int(data.split("_", 1)[1])
        with db_lock:
            r = cur.execute("SELECT username, first_name FROM access_requests WHERE user_id=?", (t,)).fetchone()
            cur.execute("INSERT OR REPLACE INTO authorized_users(user_id, username, first_name, approved_by, is_active) "
                        "VALUES(?,?,?,?,1)", (t, r[0] if r else "", r[1] if r else "", uid))
            cur.execute("UPDATE access_requests SET status='approved' WHERE user_id=?", (t,))
            conn.commit()
        await cb.answer("✅ تأیید شد", show_alert=True)
        try: await safe_send(t, "✅ دسترسی شما تأیید شد! /start را بزن.")
        except Exception: pass
        return

    if data.startswith("rej_"):
        if not is_owner(uid): await cb.answer("🚫", show_alert=True); return
        t = int(data.split("_", 1)[1])
        with db_lock:
            cur.execute("UPDATE access_requests SET status='rejected' WHERE user_id=?", (t,))
            conn.commit()
        await cb.answer("❌ رد شد", show_alert=True); return

    if not is_authorized(uid) or is_banned(uid):
        await cb.answer("🚫 دسترسی نداری", show_alert=True); return

    try: await cb.answer()
    except Exception: pass

    try:
        if data == "main":
            await clear_flow(uid)
            await safe_edit(cb.message, f"🌟 منوی اصلی\n{SEP}🤖 {BOT_NAME}", reply_markup=main_menu())
        elif data == "cancel_flow":
            await clear_flow(uid)
            await safe_edit(cb.message, "❌ لغو شد.", reply_markup=back_kb())
        elif data == "stop_jobs":
            n = stop_user_jobs(uid)
            await safe_edit(cb.message, f"🛑 {n} کار متوقف شد.", reply_markup=back_kb())
        elif data == "flow_addacc":
            with db_lock:
                n = cur.execute("SELECT COUNT(*) FROM accounts WHERE owner_id=? AND is_active=1", (uid,)).fetchone()[0]
            if n >= get_user_limits(uid)["max_accounts"]:
                await safe_send(uid, f"🚫 سقف اکانت‌ها ({get_user_limits(uid)['max_accounts']}) پر شده.",
                                reply_markup=back_kb()); return
            await start_flow(uid, "addacc", "phone")
        elif data == "flow_addtarget":
            with db_lock:
                n = cur.execute("SELECT COUNT(*) FROM targets WHERE owner_id=? AND is_active=1", (uid,)).fetchone()[0]
            if n >= get_user_limits(uid)["max_targets"]:
                await safe_send(uid, f"🚫 سقف گروه‌ها ({get_user_limits(uid)['max_targets']}) پر شده.",
                                reply_markup=back_kb()); return
            await start_flow(uid, "addtarget", "identifier")
        elif data == "flow_scrape":
            await start_flow(uid, "scrape", "source")
        elif data == "flow_addmembers":
            await start_flow(uid, "addmembers", "target")
        elif data == "flow_react":
            await start_flow(uid, "react", "target")
        elif data == "stats":
            with db_lock:
                tot = cur.execute("SELECT COUNT(*) FROM harvested WHERE owner_id=?", (uid,)).fetchone()[0]
                used = cur.execute("SELECT COUNT(*) FROM harvested WHERE owner_id=? AND used=1", (uid,)).fetchone()[0]
                bad = cur.execute("SELECT COUNT(*) FROM harvested WHERE owner_id=? AND used=2", (uid,)).fetchone()[0]
                rem = cur.execute("SELECT COUNT(*) FROM harvested WHERE owner_id=? AND used=0", (uid,)).fetchone()[0]
                accs = cur.execute("SELECT COUNT(*) FROM accounts WHERE owner_id=? AND is_active=1", (uid,)).fetchone()[0]
                tgts = cur.execute("SELECT COUNT(*) FROM targets WHERE owner_id=? AND is_active=1", (uid,)).fetchone()[0]
                added_today = cur.execute(
                    "SELECT COUNT(*) FROM added_log WHERE owner_id=? AND status='success' AND DATE(added_at)=DATE('now')",
                    (uid,)).fetchone()[0]
                react_today = cur.execute(
                    "SELECT COUNT(*) FROM reacted_log WHERE owner_id=? AND status='success' AND DATE(sent_at)=DATE('now')",
                    (uid,)).fetchone()[0]
            text = (
                f"📊 آمار امروز\n{SEP}"
                f"✅ افزوده شده: {added_today}\n"
                f"⚡️ ری‌اکشن: {react_today}\n{SEP}"
                f"👥 مخزن: {tot}\n"
                f"📤 افزوده‌شده: {used}\n"
                f"🚫 غیرقابل‌افزودن: {bad}\n"
                f"📥 باقی‌مانده: {rem}\n"
                f"📱 اکانت: {accs}\n"
                f"🎯 گروه: {tgts}\n"
                f"🔌 لود شده: {len(clients)}"
            )
            await safe_edit(cb.message, text, reply_markup=InlineKeyboardMarkup([
                [InlineKeyboardButton("♻️ ریست غیرقابل‌افزودن‌ها", callback_data="pool_reset")],
                [InlineKeyboardButton("🗑 خالی کردن مخزن", callback_data="pool_clear")],
                [InlineKeyboardButton("🔙 منو", callback_data="main")]]))
        elif data == "pool_reset":
            with db_lock:
                cur.execute("UPDATE harvested SET used=0 WHERE owner_id=? AND used=2", (uid,))
                n = cur.rowcount; conn.commit()
            await safe_edit(cb.message, f"♻️ {n} نفر دوباره وارد صف شدن.", reply_markup=back_kb())
        elif data == "pool_clear":
            await safe_edit(cb.message, "⚠️ مطمئنی کل مخزن پاک بشه؟",
                reply_markup=InlineKeyboardMarkup([[
                    InlineKeyboardButton("✅ آره پاک کن", callback_data="pool_clear_yes"),
                    InlineKeyboardButton("❌ نه", callback_data="stats")]]))
        elif data == "pool_clear_yes":
            with db_lock:
                cur.execute("DELETE FROM harvested WHERE owner_id=?", (uid,))
                n = cur.rowcount; conn.commit()
            await safe_edit(cb.message, f"🗑 {n} رکورد پاک شد.", reply_markup=back_kb())
        elif data == "acc_list":
            await show_accounts(cb.message, uid)
        elif data.startswith("del_acc_"):
            aid = int(data.split("del_acc_", 1)[1])
            with db_lock:
                r = cur.execute("SELECT id FROM accounts WHERE id=? AND owner_id=?", (aid, uid)).fetchone()
                if r:
                    cur.execute("DELETE FROM accounts WHERE id=?", (aid,))
                    conn.commit()
            if r:
                c = clients.pop(aid, None)
                if c: await _safe_stop(c)
            await show_accounts(cb.message, uid)
        elif data == "tgt_list":
            await show_targets(cb.message, uid)
        elif data.startswith("del_tgt_"):
            tid = int(data.split("del_tgt_", 1)[1])
            with db_lock:
                cur.execute("DELETE FROM targets WHERE id=? AND owner_id=?", (tid, uid))
                conn.commit()
            await show_targets(cb.message, uid)
        elif data == "report_add_list":
            with db_lock:
                rows = cur.execute(
                    "SELECT target_id, target_title FROM added_log WHERE owner_id=? AND target_id IS NOT NULL "
                    "GROUP BY target_id ORDER BY MAX(id) DESC LIMIT 20", (uid,)).fetchall()
            if not rows:
                await safe_edit(cb.message, "📭 گزارشی نیست.", reply_markup=back_kb()); return
            kb = [[InlineKeyboardButton(f"🎯 {t}", callback_data=f"report_add_{tid}")] for tid, t in rows]
            kb.append([InlineKeyboardButton("🔙 منو", callback_data="main")])
            await safe_edit(cb.message, "📋 انتخاب گروه برای گزارش:", reply_markup=InlineKeyboardMarkup(kb))
        elif data.startswith("report_add_"):
            await show_add_report(cb.message, uid, int(data.split("report_add_", 1)[1]))
        elif data.startswith("report_react_"):
            await show_react_report(cb.message, uid, int(data.split("report_react_", 1)[1]))
        elif data == "watch_menu":
            await show_watches(cb.message, uid)
        elif data == "flow_addwatch":
            with db_lock:
                n = cur.execute("SELECT COUNT(*) FROM watches WHERE owner_id=?", (uid,)).fetchone()[0]
            if n >= get_user_limits(uid)["max_targets"]:
                await safe_send(uid, f"🚫 سقف گروه‌های خودکار ({get_user_limits(uid)['max_targets']}) پر شده.",
                                reply_markup=back_kb()); return
            await start_flow(uid, "addwatch", "target")
        elif data.startswith("watch_toggle_"):
            wid = int(data.split("watch_toggle_", 1)[1])
            with db_lock:
                r = cur.execute("SELECT is_active FROM watches WHERE id=? AND owner_id=?", (wid, uid)).fetchone()
                if r:
                    if r[0]:
                        cur.execute("UPDATE watches SET is_active=0 WHERE id=?", (wid,))
                    else:
                        cur.execute("UPDATE watches SET is_active=1, last_id=-1 WHERE id=?", (wid,))
                    conn.commit()
            await show_watches(cb.message, uid)
        elif data.startswith("watch_del_"):
            wid = int(data.split("watch_del_", 1)[1])
            with db_lock:
                cur.execute("DELETE FROM watches WHERE id=? AND owner_id=?", (wid, uid))
                conn.commit()
            await show_watches(cb.message, uid)
    except Exception as e:
        log.error(f"cb: {repr(e)[:150]}")
        try: await cb.answer("خطا", show_alert=True)
        except Exception: pass

# ==================== REPORTS ====================
async def show_add_report(msg, owner_id, target_id):
    with db_lock:
        counts = dict(cur.execute(
            "SELECT status, COUNT(*) FROM added_log WHERE owner_id=? AND target_id=? GROUP BY status",
            (owner_id, target_id)).fetchall())
        errs = cur.execute(
            "SELECT COALESCE(error,'unknown'), COUNT(*) FROM added_log WHERE owner_id=? AND target_id=? "
            "AND status='fail' GROUP BY error ORDER BY 2 DESC LIMIT 8", (owner_id, target_id)).fetchall()
        success = cur.execute(
            "SELECT user_id, username, first_name FROM added_log WHERE owner_id=? AND target_id=? "
            "AND status='success' ORDER BY id DESC LIMIT 30", (owner_id, target_id)).fetchall()
        fails = cur.execute(
            "SELECT user_id, error FROM added_log WHERE owner_id=? AND target_id=? "
            "AND status='fail' ORDER BY id DESC LIMIT 10", (owner_id, target_id)).fetchall()
        trow = cur.execute("SELECT title FROM targets WHERE id=?", (target_id,)).fetchone()
        if not trow:
            trow = cur.execute("SELECT target_title FROM added_log WHERE target_id=? LIMIT 1", (target_id,)).fetchone()
    ttitle = trow[0] if trow else str(target_id)

    if not counts:
        await safe_edit(msg, f"📭 گزارشی برای {ttitle} نیست.", reply_markup=back_kb()); return

    text = (f"📋 گزارش — {ttitle}\n{SEP}"
            f"✅ موفق: {counts.get('success', 0)}\n"
            f"⏭ رد: {counts.get('skip', 0)}\n"
            f"❌ ناموفق: {counts.get('fail', 0)}\n"
            f"🌊 فلود: {counts.get('flood', 0)}\n\n")
    if errs:
        text += "🔍 دلایل خطا:\n" + "".join(f"  • {e}: {n}\n" for e, n in errs) + "\n"
    if success:
        text += "━━━ ✅ ۳۰ موفق آخر ━━━\n"
        for uid_, uname, fname in success:
            text += f"`{uid_}`"
            if uname: text += f" @{uname}"
            if fname: text += f" | {fname[:15]}"
            text += "\n"
    if fails:
        text += "\n━━━ ❌ ۱۰ خطای آخر ━━━\n" + "".join(f"`{u}` — {e}\n" for u, e in fails)
    await safe_edit(msg, text, reply_markup=back_kb())

async def show_react_report(msg, owner_id, chat_id):
    with db_lock:
        counts = dict(cur.execute(
            "SELECT status, COUNT(*) FROM reacted_log WHERE owner_id=? AND chat_id=? GROUP BY status",
            (owner_id, chat_id)).fetchall())
        errs = cur.execute(
            "SELECT COALESCE(error,'unknown'), COUNT(*) FROM reacted_log WHERE owner_id=? AND chat_id=? "
            "AND status='fail' GROUP BY error ORDER BY 2 DESC LIMIT 5", (owner_id, chat_id)).fetchall()
        rows = cur.execute(
            "SELECT msg_id, emoji, account_phone, status FROM reacted_log WHERE owner_id=? AND chat_id=? "
            "ORDER BY id DESC LIMIT 15", (owner_id, chat_id)).fetchall()
    if not counts:
        await safe_edit(msg, "📭 گزارشی نیست.", reply_markup=back_kb()); return

    text = (f"📋 گزارش ری‌اکشن\n{SEP}"
            f"✅ موفق: {counts.get('success', 0)}\n"
            f"❌ ناموفق: {counts.get('fail', 0)}\n"
            f"🌊 فلود: {counts.get('flood', 0)}\n\n")
    if errs:
        text += "🔍 دلایل:\n" + "".join(f"  • {e}: {n}\n" for e, n in errs)
    text += "\n━━━ ۱۵ ری‌اکشن آخر ━━━\n"
    for mid, emoji, phone, st in rows:
        text += f"{'✅' if st == 'success' else '❌'} msg `{mid}` {emoji} | {phone}\n"
    await safe_edit(msg, text, reply_markup=back_kb())

# ==================== COMMANDS ====================
@bot.on_message(filters.command("start") & filters.private)
async def cmd_start(_, m: Message):
    uid = m.from_user.id
    get_or_create_user(uid, m.from_user.username or "", m.from_user.first_name or "")
    if is_banned(uid):
        return await safe_send(m, "🚫 شما بن شده‌اید.")
    if not is_authorized(uid):
        with db_lock:
            cur.execute("INSERT OR IGNORE INTO access_requests(user_id, username, first_name) VALUES(?,?,?)",
                        (uid, m.from_user.username or "", m.from_user.first_name or ""))
            new_req = cur.rowcount > 0
            conn.commit()
        await safe_send(uid, "🚫 دسترسی نداری. درخواست ارسال شد.")
        if new_req:
            try:
                await safe_send(OWNER_ID,
                    f"🔔 درخواست:\n👤 {m.from_user.first_name or ''}\n🆔 `{uid}`",
                    reply_markup=InlineKeyboardMarkup([[
                        InlineKeyboardButton("✅", callback_data=f"apr_{uid}"),
                        InlineKeyboardButton("❌", callback_data=f"rej_{uid}")]]))
            except Exception: pass
        return
    await clear_flow(uid)
    await safe_send(uid,
        f"🌟 {BOT_NAME}\n{SEP}👑 @{OWNER_USERNAME}\n\nاز منو انتخاب کن — همه چیز خودکاره! 🚀",
        reply_markup=main_menu())

@bot.on_message(filters.command("stop") & filters.private)
async def cmd_stop(_, m: Message):
    uid = m.from_user.id
    if not is_authorized(uid): return
    if is_owner(uid) and len(m.command) > 1 and m.command[1] == "all":
        n = len(running_jobs); running_jobs.clear()
    else:
        n = stop_user_jobs(uid)
    await clear_flow(uid)
    await safe_send(m.chat.id, f"🛑 {n} کار متوقف شد.")

@bot.on_message(filters.command("status") & filters.private)
async def cmd_status(_, m: Message):
    uid = m.from_user.id
    if not is_authorized(uid): return
    jobs = user_jobs(uid)
    with db_lock:
        accs = cur.execute("SELECT phone, added_today, cooldown_until FROM accounts WHERE owner_id=? AND is_active=1",
                           (uid,)).fetchall()
    now = time.time()
    lines = [f"📡 وضعیت\n{SEP}", f"🔧 کار در حال اجرا: {', '.join(k.rsplit('_', 1)[0] for k in jobs) or 'هیچ'}"]
    for phone, added, cd in accs:
        extra = f" ⏸ {int(cd - now)}s" if cd and cd > now else ""
        lines.append(f"📱 `{phone}` — {added}/{daily_limit(uid)}{extra}")
    await safe_send(m, "\n".join(lines))

@bot.on_message(filters.command("users") & filters.private)
async def cmd_users(_, m: Message):
    if not is_owner(m.from_user.id): return
    with db_lock:
        rows = cur.execute("SELECT user_id, username, first_name, is_active FROM authorized_users").fetchall()
    if not rows:
        await safe_send(m, "📭 کاربری مجاز نیست."); return
    lines = [f"👥 کاربران مجاز ({len(rows)})\n{SEP}"]
    for uid_, un, fn, act in rows:
        lines.append(f"{'🟢' if act else '⚪️'} `{uid_}` {('@' + un) if un else ''} {fn or ''}")
    lines.append("\n/revoke <id> | /ban <id> [دلیل] | /unban <id>")
    await safe_send(m, "\n".join(lines))

@bot.on_message(filters.command("revoke") & filters.private)
async def cmd_revoke(_, m: Message):
    if not is_owner(m.from_user.id): return
    try: t = int(m.command[1])
    except Exception: await safe_send(m, "استفاده: /revoke <id>"); return
    with db_lock:
        cur.execute("UPDATE authorized_users SET is_active=0 WHERE user_id=?", (t,)); conn.commit()
    stop_user_jobs(t)
    await safe_send(m, f"✅ دسترسی `{t}` لغو شد.")

@bot.on_message(filters.command("ban") & filters.private)
async def cmd_ban(_, m: Message):
    if not is_owner(m.from_user.id): return
    try: t = int(m.command[1])
    except Exception: await safe_send(m, "استفاده: /ban <id> [دلیل]"); return
    reason = " ".join(m.command[2:])[:100]
    if is_owner(t): await safe_send(m, "😅 نمی‌شه خودت رو بن کنی."); return
    with db_lock:
        cur.execute("INSERT OR IGNORE INTO users(user_id) VALUES(?)", (t,))
        cur.execute("UPDATE users SET is_banned=1, ban_reason=? WHERE user_id=?", (reason, t)); conn.commit()
    stop_user_jobs(t)
    await safe_send(m, f"🚫 `{t}` بن شد.")

@bot.on_message(filters.command("unban") & filters.private)
async def cmd_unban(_, m: Message):
    if not is_owner(m.from_user.id): return
    try: t = int(m.command[1])
    except Exception: await safe_send(m, "استفاده: /unban <id>"); return
    with db_lock:
        cur.execute("UPDATE users SET is_banned=0, ban_reason=NULL WHERE user_id=?", (t,)); conn.commit()
    await safe_send(m, f"✅ `{t}` آزاد شد.")

# ==================== AUTO REACT (WATCH) ====================
async def get_peer_for(aid, c, chat_id, ref):
    key = (aid, chat_id)
    if key in _peer_cache:
        return _peer_cache[key], None
    t = _peer_fail.get(key)
    if t and time.time() - t < 600:
        return None, "cached_fail"
    try:
        entity, peer, err = await resolve_chat(c, ref, allow_join=True)
        if entity is None or peer is None:
            entity, peer, err2 = await resolve_chat(c, chat_id)
            if entity is None or peer is None:
                raise RuntimeError(err or err2 or "resolve")
        me_id = _me_ids.get(aid)
        if me_id:
            try:
                await c.get_chat_member(entity.id, me_id)
            except UserNotParticipant:
                target = getattr(entity, "username", None) or normalize_ref(ref)
                try:
                    await c.join_chat(target)
                except UserAlreadyParticipant:
                    pass
                except Exception as e:
                    log.warning(f"join acc#{aid}: {repr(e)[:80]}")
                await asyncio.sleep(1)
            except Exception:
                pass
        _peer_cache[key] = peer
        return peer, None
    except Exception as e:
        _peer_fail[key] = time.time()
        return None, str(e)[:60]

def _acc_cooling(aid):
    with db_lock:
        r = cur.execute("SELECT cooldown_until, is_active FROM accounts WHERE id=?", (aid,)).fetchone()
    return (not r) or (not r[1]) or (r[0] or 0) > time.time()

async def react_to_message(w, msg_id):
    wid, owner, chat_id, title, ref = w
    accs = get_available_accounts(owner)
    if not accs: return
    loaded = await ensure_accounts_loaded(accs)
    sem = asyncio.Semaphore(WATCH_CONCURRENCY)

    async def one(a):
        aid, phone = a[0], a[1]
        c = clients.get(aid)
        if not c: return
        await asyncio.sleep(random.uniform(0.5, 5))
        lock = _react_locks.setdefault(aid, asyncio.Lock())
        async with lock:
            async with sem:
                if _acc_cooling(aid): return
                with db_lock:
                    seen = cur.execute(
                        "SELECT 1 FROM reaction_marks WHERE account_id=? AND chat_id=? AND msg_id=?",
                        (aid, chat_id, msg_id)).fetchone()
                if seen: return
                peer, err = await get_peer_for(aid, c, chat_id, ref)
                if peer is None: return
                done = False
                for emoji in random.sample(REACTIONS, len(REACTIONS)):
                    s, info = await send_reaction_retry(c, peer, msg_id, emoji)
                    if s:
                        with db_lock:
                            cur.execute(
                                "INSERT OR IGNORE INTO reaction_marks(owner_id, account_id, chat_id, msg_id, emoji) "
                                "VALUES(?,?,?,?,?)", (owner, aid, chat_id, msg_id, emoji))
                            cur.execute("UPDATE watches SET total_reacted=total_reacted+1 WHERE id=?", (wid,))
                            conn.commit()
                        _log_react(owner, chat_id, title, msg_id, emoji, phone, "success")
                        done = True
                        break
                    if isinstance(info, tuple):
                        if info[0] == "flood":
                            _log_react(owner, chat_id, title, msg_id, emoji, phone, "flood", f"wait={info[1]}")
                            cooldown(aid, info[1], owner)
                            return
                        if info[0] == "fatal":
                            _log_react(owner, chat_id, title, msg_id, emoji, phone, "fail", info[1])
                            _peer_cache.pop((aid, chat_id), None)
                            _peer_fail[(aid, chat_id)] = time.time()
                            return
                        if info[0] == "skipmsg":
                            break
                if not done:
                    _log_react(owner, chat_id, title, msg_id, REACTIONS[0], phone, "fail", "all_emojis_failed")
                await asyncio.sleep(random.uniform(REACT_DELAY_MIN, REACT_DELAY_MAX))

    await asyncio.gather(*[one(a) for a in loaded], return_exceptions=True)

async def poll_watch(w):
    wid, owner, chat_id, title, ref, last_id = w
    try:
        accs = get_available_accounts(owner)
        loaded = [a for a in accs if a[0] in clients] or await ensure_accounts_loaded(accs[:3])
        c = None
        for a in loaded[:3]:
            cc = clients.get(a[0])
            if not cc: continue
            peer, err = await get_peer_for(a[0], cc, chat_id, ref)
            if peer is not None:
                c = cc
                break
        if c is None: return

        msgs = []
        async for m in c.get_chat_history(chat_id, limit=30):
            msgs.append(m)
        if not msgs:
            if last_id < 0:
                with db_lock:
                    cur.execute("UPDATE watches SET last_id=0 WHERE id=?", (wid,)); conn.commit()
            return
        newest = max(m.id for m in msgs)
        if last_id < 0:
            with db_lock:
                cur.execute("UPDATE watches SET last_id=? WHERE id=?", (newest, wid)); conn.commit()
            return
        if newest > last_id:
            with db_lock:
                cur.execute("UPDATE watches SET last_id=? WHERE id=?", (newest, wid)); conn.commit()
        new = sorted([m for m in msgs if m.id > last_id and not m.service], key=lambda m: m.id)
        mine = set(_me_ids.values())
        for m in new[-20:]:
            if m.from_user and m.from_user.id in mine:
                continue
            spawn(react_to_message((wid, owner, chat_id, title, ref), m.id))
    except FloodWait as e:
        await asyncio.sleep(min(e.value, 30))
    except Exception as e:
        log.error(f"poll_watch: {repr(e)[:120]}")
    finally:
        _watch_busy.discard(wid)

async def watch_loop():
    while True:
        try:
            with db_lock:
                rows = cur.execute(
                    "SELECT id, owner_id, chat_id, title, ref, last_id FROM watches WHERE is_active=1").fetchall()
            for r in rows:
                if r[0] in _watch_busy: continue
                if is_banned(r[1]) or not is_authorized(r[1]): continue
                _watch_busy.add(r[0])
                spawn(poll_watch(r))
        except Exception as e:
            log.error(f"watch_loop: {repr(e)[:100]}")
        await asyncio.sleep(WATCH_INTERVAL)

async def prejoin_watch(owner, chat_id, ref):
    for a in get_available_accounts(owner):
        try:
            if not await ensure_loaded(a[0]): continue
            c = clients.get(a[0])
            if c: await get_peer_for(a[0], c, chat_id, ref)
        except Exception as e:
            log.warning(f"prejoin: {repr(e)[:80]}")
        await asyncio.sleep(random.uniform(3, 8))

async def show_watches(msg, uid):
    with db_lock:
        rows = cur.execute("SELECT id, chat_id, title, is_active, total_reacted FROM watches WHERE owner_id=?",
                           (uid,)).fetchall()
    lines = [f"🤖 ری‌اکشن خودکار\n{SEP}"]
    kb = []
    if not rows:
        lines.append("📭 هنوز گروهی ثبت نشده.")
    for wid, cid, title, act, tot in rows:
        lines.append(f"{'🟢' if act else '⏸'} {title}\n`{cid}` — ⚡️ {tot}")
        kb.append([
            InlineKeyboardButton(f"{'⏸ توقف' if act else '▶️ شروع'} {title[:14]}", callback_data=f"watch_toggle_{wid}"),
            InlineKeyboardButton("🗑", callback_data=f"watch_del_{wid}"),
            InlineKeyboardButton("📋", callback_data=f"report_react_{cid}")])
    kb.append([InlineKeyboardButton("➕ ثبت گروه جدید", callback_data="flow_addwatch")])
    kb.append([InlineKeyboardButton("🔙 منو", callback_data="main")])
    await safe_edit(msg, "\n".join(lines), reply_markup=InlineKeyboardMarkup(kb))

# ==================== MAIN ====================
async def shutdown():
    global _daily_task, _watch_task
    running_jobs.clear()
    if _daily_task: _daily_task.cancel()
    if _watch_task: _watch_task.cancel()
    for t in list(bg_tasks): t.cancel()
    try:
        await asyncio.wait_for(
            asyncio.gather(*[_safe_stop(c, 5) for c in list(clients.values())], return_exceptions=True), timeout=20)
    except Exception:
        pass
    clients.clear()
    await _safe_stop(bot, 5)
    try:
        conn.commit(); conn.close()
    except Exception:
        pass

async def main():
    global _daily_task, _watch_task
    if not isinstance(OWNER_ID, int) or not REACTIONS:
        raise SystemExit("❌ OWNER_ID باید عدد باشه و REACTIONS خالی نباشه")
    print(f"\n🚀 {BOT_NAME} starting...")
    await bot.start()
    me = await bot.get_me()
    print(f"✅ @{me.username} online")
    print(f"💘 Reactions: {' '.join(REACTIONS)}")
    reset_daily()
    _daily_task = asyncio.create_task(daily_reset_loop())
    try:
        await load_all_accounts()
        print(f"✅ {len(clients)} accounts loaded")
        _watch_task = asyncio.create_task(watch_loop())
        with db_lock:
            nw = cur.execute("SELECT COUNT(*) FROM watches WHERE is_active=1").fetchone()[0]
        print(f"🤖 {nw} auto-react groups active")
        with db_lock:
            tm = cur.execute("SELECT COUNT(*) FROM harvested").fetchone()[0]
        warn = "" if clients else "\n⚠️ هیچ اکانتی لود نشد!"
        await safe_send(OWNER_ID,
            f"🌟 ربات روشن شد!\n{SEP}🤖 {BOT_NAME}\n📱 اکانت: {len(clients)}\n"
            f"👥 اعضا: {tm}\n💘 {' '.join(REACTIONS)}{warn}")
        await idle()
    finally:
        await shutdown()

if __name__ == "__main__":
    try:
        asyncio.get_event_loop().run_until_complete(main())
    except KeyboardInterrupt:
        print("\n🛑 متوقف شد")
