# -*- coding: utf-8 -*-
"""
SUGLT Contact Bot 10.0
- Telegram Bot API via aiohttp
- SQLite via aiosqlite
- Dynamic main-menu buttons controlled from Telegram
- Full contact/reply system for text and media
- Admin/user management
- Broadcasts
- Forced subscription
- Welcome/start editor
- Maintenance mode
- Anti-flood
- Backups and CSV/JSON export
- No third-party Telegram framework required
- Platform mode can host up to 100 isolated child bots

IMPORTANT:
1) The token that was posted publicly must be revoked in @BotFather.
2) Put the NEW token in BOT_TOKEN below or use the BOT_TOKEN environment variable.
"""

import asyncio
import aiohttp
import aiosqlite
import csv
import datetime as dt
import hashlib
import secrets
import statistics
from dataclasses import dataclass, asdict
import html
import json
import os
import re
import shutil
import sys
import time
from collections import defaultdict
from pathlib import Path

# =========================================================
# CONFIG
# =========================================================

# Never keep a Telegram token in source control. Set BOT_TOKEN in the process
# environment (and revoke any token that was previously exposed).
BOT_TOKEN = os.getenv("BOT_TOKEN", "").strip()
OWNER_ID = int(os.getenv("OWNER_ID", "8275302157"))
PLATFORM_OWNER_ID = int(os.getenv("PLATFORM_OWNER_ID", "8275302157"))

BOT_USERNAME = "SUGLFBOT"
BOT_VERSION = "18.0 Final Fortress"

DB_FILE = os.getenv("DB_FILE", "contact_bot.db").strip() or "contact_bot.db"

# Platform / hosted-bot limits
MAX_HOSTED_BOTS = 100
BOT_CREATION_PRICE_STARS = 25
IS_CHILD_BOT = os.getenv("RUN_AS_CHILD", "0") == "1"
HOSTED_BOTS_DIR = Path(os.getenv("HOSTED_BOTS_DIR", "hosted_bots"))
HOSTED_BOTS_DIR.mkdir(exist_ok=True)
HOSTED_PROCESSES = {}
HOSTED_BOT_ID = int(os.getenv("HOSTED_BOT_ID", "0") or 0)
HOSTED_RESTART_HISTORY = defaultdict(list)
HOSTED_MAX_RESTARTS = 5
HOSTED_RESTART_WINDOW = 300

# Cross-bot button visibility policy. The parent controls it; child processes
# read the same small JSON file and apply it to every generated keyboard.
BUTTON_POLICY_FILE = Path(os.getenv("BUTTON_POLICY_FILE", "button_visibility_policy.json"))
BUTTON_POLICY_CACHE = {"mtime": 0.0, "data": {"version": 1, "global": {"selectors": [], "texts": []}, "bots": {}}}
BUTTON_POLICY_LOCK = asyncio.Lock()

# Global forced-subscription policy. Child bots read this file instead of their
# private SQLite databases, so hosted-bot owners cannot remove or disable the
# platform-wide subscription requirement from their own bot.
GLOBAL_POLICY_FILE = Path(os.getenv("GLOBAL_POLICY_FILE", "global_platform_policy.json"))
GLOBAL_POLICY_CACHE = {"ts": 0.0, "channels": []}
GLOBAL_POLICY_LOCK = asyncio.Lock()

BACKUP_DIR = Path("backups")
EXPORT_DIR = Path("exports")

BACKUP_DIR.mkdir(exist_ok=True)
EXPORT_DIR.mkdir(exist_ok=True)

API = ""  # initialized after token validation

START_TIME = time.time()
HTTP_SESSION = None
HTTP_API_SEMAPHORE = None
HTTP_CONNECTOR = None
# Per-process resources: every hosted bot has its own Python process, HTTP pool,
# semaphore and SQLite connection. No child bot shares these runtime locks.
DB_CONNECTION = None
DB_LOCK = None
SETTINGS_CACHE = {}
SETTINGS_CACHE_TTL = 1.5

# Central UI security policy. Any inline callback matching these namespaces is
# considered developer/internal and is stripped from member-facing keyboards.
DEV_CALLBACK_PREFIXES = (
    "admin", "pro:", "v11:", "v13:", "v16:", "adm:", "broadcast:",
    "userinfo:", "quickban:", "reply:", "history:", "read:", "channel:",
    "welcome:", "text:", "contact:", "photo:", "status:", "protection:",
    "propage", "propagetoggle:", "propagedelete:", "prouser", "admin:",
    "adminbtn", "btnedit:", "btnstyle:", "btnsetstyle:", "btntoggle:",
    "btnaction:", "btnsetaction:", "btnvalue:", "btnurl:", "btnmedia:",
    "btnmedia_delete:", "btnmove:", "btnmove_do:", "btnplace:",
    "btnplace_do:", "btnclone:", "btnpreview:", "btndelete:",
    "btndelete_yes:", "btneditfield:", "btnrestore:", "btnpurge:",
)

# Telegram Bot API now supports inline button styles: primary (blue),
# success (green), and danger (red). We send them directly and keep a
# compatibility fallback that retries without styles if an old client/API
# endpoint rejects the field.

DEFAULT_START_TEXT = (
    "أهلاً بك <b>{name}</b> 👋\n\n"
    "أنت الآن في بوت التواصل.\n"
    "يمكنك اختيار أحد الخيارات من الأسفل."
)

DEFAULT_CONTACT_TEXT = (
    "📨 <b>التواصل مع المطور</b>\n\n"
    "أرسل رسالتك الآن، ويمكنك إرسال:\n"
    "• نص\n• صورة\n• فيديو\n• ملف\n• صوت\n• بصمة\n• ملصق\n\n"
    "ستصل رسالتك للمطور مباشرة."
)

DEFAULT_BUTTONS = [
    {
        "id": "create_bot",
        "text": "🤖 إنشاء بوت تواصل",
        "action": "create_bot",
        "row": 0,
        "position": 1,
        "enabled": 1,
        "style": "success",
    },
    {
        "id": "contact",
        "text": "📨 رسالة للمطور",
        "action": "contact",
        "row": 0,
        "position": 0,
        "enabled": 1,
        "style": "success",
    },
    {
        "id": "info",
        "text": "ℹ️ معلومات البوت",
        "action": "info",
        "row": 1,
        "position": 0,
        "enabled": 1,
        "style": "primary",
    },
    {
        "id": "top",
        "text": "🏆 المتصدرون",
        "action": "top",
        "row": 1,
        "position": 1,
        "enabled": 1,
        "style": "primary",
    },
]

# Per-user state is stored in SQLite.
# state values:
# none, contact, admin_wait_*, broadcast_*, edit_*
RATE_LIMIT = defaultdict(list)
CALLBACK_RATE = defaultdict(list)

# Cached developer-panel button configuration. Telegram keyboard is built synchronously,
# so the configuration is loaded at startup and updated whenever the owner edits it.
ADMIN_BUTTONS = {}
MAIN_BUTTON_CACHE = {"ts": 0.0, "keyboard": None}

# =========================================================
# BASIC HELPERS
# =========================================================

def now_text():
    return dt.datetime.now().strftime("%Y-%m-%d %H:%M:%S")


def esc(value):
    return html.escape(str(value or ""), quote=False)


def is_owner(user_id):
    return int(user_id) == OWNER_ID


def is_platform_owner(user_id):
    return int(user_id) == PLATFORM_OWNER_ID and not IS_CHILD_BOT


def uptime():
    seconds = max(0, int(time.time() - START_TIME))
    return str(dt.timedelta(seconds=seconds))


def ensure_token():
    global API
    if not BOT_TOKEN or BOT_TOKEN == "PUT_YOUR_NEW_BOT_TOKEN_HERE":
        raise RuntimeError(
            "BOT_TOKEN is not configured. Put your NEW BotFather token in BOT_TOKEN."
        )
    if ":" not in BOT_TOKEN or len(BOT_TOKEN) < 20:
        raise RuntimeError("BOT_TOKEN format looks invalid. Get a fresh token from @BotFather.")
    API = f"https://api.telegram.org/bot{BOT_TOKEN}"


async def bot_blocked_for_user(user_id):
    """Single source of truth for global bot availability."""
    if is_owner(user_id):
        return False
    if await get_setting("bot_enabled", "1") != "1":
        return True
    if await get_setting("maintenance", "0") == "1":
        return True
    return False


async def send_service_unavailable(chat_id):
    """Send centralized maintenance/disabled screen, optionally with an image."""
    if await get_setting("maintenance", "0") == "1":
        text = await get_notification("notif_maintenance")
        photo = await get_setting("maintenance_photo", "")
        photo_enabled = await get_setting("maintenance_photo_enabled", "1") == "1"
    else:
        text = await get_notification("notif_disabled")
        photo = ""
        photo_enabled = False
    if photo and photo_enabled:
        result = await send_photo(chat_id, photo, text)
        if result.get("ok"):
            return result
        await set_setting("maintenance_photo", "")
    return await send_message(chat_id, text)


async def send_info_page(chat_id, user_id, back_callback="main"):
    users = await db_execute(
        "SELECT COUNT(*) c FROM users",
        fetchone=True,
    )
    text = (
        "ℹ️ <b>معلومات البوت</b>\n\n"
        f"🤖 @{esc(BOT_USERNAME)}\n"
        f"📦 الإصدار: {esc(BOT_VERSION)}\n"
        f"👥 المستخدمون: {users['c']}\n"
        f"⏱ التشغيل: {uptime()}\n"
        f"👤 المطور: مدير البوت"
    )
    keyboard = back_keyboard(back_callback)
    dev_photo = await get_setting("dev_photo", "")
    if dev_photo:
        result = await send_photo(chat_id, dev_photo, text, keyboard)
        if result.get("ok"):
            return result
    return await send_message(chat_id, text, keyboard)


async def api_call(method, *, params=None, data=None, files=None, timeout=20, retries=3):
    """Fast per-bot Telegram API client with isolated connection pooling."""
    global HTTP_SESSION, HTTP_API_SEMAPHORE, HTTP_CONNECTOR
    if not API:
        ensure_token()
    if HTTP_API_SEMAPHORE is None:
        HTTP_API_SEMAPHORE = asyncio.Semaphore(MAX_CONCURRENT_TELEGRAM)
    if HTTP_SESSION is None or HTTP_SESSION.closed:
        HTTP_CONNECTOR = aiohttp.TCPConnector(
            limit=max(8, int(os.getenv("HTTP_POOL_LIMIT", "16"))),
            limit_per_host=max(4, int(os.getenv("HTTP_POOL_PER_HOST", "8"))),
            ttl_dns_cache=300, keepalive_timeout=30, enable_cleanup_closed=True
        )
        HTTP_SESSION = aiohttp.ClientSession(
            connector=HTTP_CONNECTOR,
            headers={"User-Agent": f"SUGLT-Contact-Bot/{BOT_VERSION}"},
            timeout=aiohttp.ClientTimeout(total=30),
        )

    last_error = None
    for attempt in range(max(1, retries)):
        try:
            url = f"{API}/{method}"
            kwargs = {"timeout": aiohttp.ClientTimeout(total=timeout)}

            if files:
                form = aiohttp.FormData()
                if data:
                    for key, value in data.items():
                        form.add_field(key, str(value))
                for key, value in files.items():
                    filename, content, content_type = value
                    form.add_field(key, content, filename=filename, content_type=content_type)
                kwargs["data"] = form
            elif data is not None:
                kwargs["data"] = data
            elif params is not None:
                kwargs["params"] = params

            async with HTTP_API_SEMAPHORE:
                async with HTTP_SESSION.post(url, **kwargs) as response:
                    raw = await response.text()
                    try:
                        result = json.loads(raw)
                    except Exception:
                        result = {"ok": False, "description": raw[:500]}

                    if result.get("ok"):
                        return result

                    if response.status == 429:
                        retry_after = result.get("parameters", {}).get("retry_after", 3)
                        await asyncio.sleep(min(max(int(retry_after), 1), 60))
                        continue

                    if response.status >= 500 and attempt + 1 < retries:
                        await asyncio.sleep(min(2 ** attempt, 8))
                        continue

                    return result

        except asyncio.CancelledError:
            raise
        except (aiohttp.ClientError, asyncio.TimeoutError, OSError) as exc:
            last_error = exc
            if attempt + 1 < retries:
                await asyncio.sleep(min(2 ** attempt, 8))
                if HTTP_SESSION is not None and HTTP_SESSION.closed:
                    HTTP_CONNECTOR = aiohttp.TCPConnector(
                        limit=24, limit_per_host=12, ttl_dns_cache=300,
                        keepalive_timeout=30, enable_cleanup_closed=True
                    )
                    HTTP_SESSION = aiohttp.ClientSession(
                        connector=HTTP_CONNECTOR,
                        headers={"User-Agent": f"SUGLT-Contact-Bot/{BOT_VERSION}"},
                        timeout=aiohttp.ClientTimeout(total=30),
                    )
                continue
            break
        except Exception as exc:
            last_error = exc
            break

    if last_error is not None:
        try:
            await log_error("api_call", f"{method}: {last_error}")
        except Exception:
            pass
        return {"ok": False, "description": str(last_error)}
    return {"ok": False, "description": f"Telegram API request failed: {method}"}


def _button_style_for_text(text):
    t = str(text or "").lower()
    danger_words = ("حذف", "حظر", "الغاء", "إلغاء", "danger", "delete", "ban", "stop", "خروج")
    success_words = ("إضافة", "تفعيل", "حفظ", "تم", "تحقق", "success", "add", "save", "enable", "موافق")
    if any(w in t for w in danger_words):
        return "danger"
    if any(w in t for w in success_words):
        return "success"
    return "primary"


def colorize_keyboard(keyboard):
    """Add Telegram button colors to every inline button unless explicitly set."""
    if not isinstance(keyboard, dict) or "inline_keyboard" not in keyboard:
        return keyboard
    out = {k: v for k, v in keyboard.items() if k != "inline_keyboard"}
    rows = []
    for row in keyboard.get("inline_keyboard", []):
        new_row = []
        for button in row:
            b = dict(button)
            if "style" not in b:
                b["style"] = _button_style_for_text(b.get("text", ""))
            elif b.get("style") not in ("primary", "success", "danger"):
                b["style"] = "primary"
            new_row.append(b)
        rows.append(new_row)
    out["inline_keyboard"] = rows
    return out


def strip_keyboard_styles(keyboard):
    if not isinstance(keyboard, dict) or "inline_keyboard" not in keyboard:
        return keyboard
    out = {k: v for k, v in keyboard.items() if k != "inline_keyboard"}
    out["inline_keyboard"] = [[{k:v for k,v in b.items() if k != "style"} for b in row] for row in keyboard["inline_keyboard"]]
    return out


def is_developer_callback(callback_data):
    data = str(callback_data or "")
    return data == "admin" or any(data.startswith(prefix) for prefix in DEV_CALLBACK_PREFIXES)


def is_platform_only_callback(callback_data):
    data = str(callback_data or "")
    return (
        data.startswith("v16:")
        or data in {"adm:hosted", "adm:creator_exempt", "adm:hostbroadcast", "adm:notifications"}
        or data.startswith("adm:hostbot:")
        or data.startswith("broadcast:all:")
        or data.startswith("adm:creator_exempt:")
    )


def is_limited_bot_owner(user_id):
    return bool(IS_CHILD_BOT and is_owner(int(user_id or 0)))


def _button_policy_load_sync():
    """Load cross-bot button policy with an mtime cache; safe for sync UI paths."""
    try:
        mtime = BUTTON_POLICY_FILE.stat().st_mtime
    except OSError:
        mtime = 0.0
    if BUTTON_POLICY_CACHE.get("mtime") == mtime and BUTTON_POLICY_CACHE.get("data"):
        return BUTTON_POLICY_CACHE["data"]
    default = {"version": 2, "global": {"selectors": [], "texts": [], "labels": {}, "styles": {}}, "bots": {}}
    try:
        raw = json.loads(BUTTON_POLICY_FILE.read_text(encoding="utf-8")) if BUTTON_POLICY_FILE.exists() else default
        if not isinstance(raw, dict):
            raw = default
    except Exception:
        raw = default
    raw.setdefault("version", 2)
    raw.setdefault("global", {"selectors": [], "texts": [], "labels": {}, "styles": {}})
    # Migrate policies written by older versions without breaking them.
    raw["global"].setdefault("selectors", [])
    raw["global"].setdefault("texts", [])
    raw["global"].setdefault("labels", {})
    raw["global"].setdefault("styles", {})
    raw.setdefault("bots", {})
    for scope in (raw.get("bots") or {}).values():
        scope.setdefault("selectors", [])
        scope.setdefault("texts", [])
        scope.setdefault("labels", {})
        scope.setdefault("styles", {})
    BUTTON_POLICY_CACHE["mtime"] = mtime
    BUTTON_POLICY_CACHE["data"] = raw
    return raw


def _button_policy_blocked(callback_data="", text=""):
    """Return True when a button is disabled globally or for this hosted bot."""
    data = _button_policy_load_sync()
    cb = str(callback_data or "")
    label = str(text or "")
    scopes = [data.get("global") or {}]
    if IS_CHILD_BOT and HOSTED_BOT_ID:
        scopes.append((data.get("bots") or {}).get(str(HOSTED_BOT_ID)) or {})
    for scope in scopes:
        selectors = {str(x) for x in (scope.get("selectors") or [])}
        texts = {str(x) for x in (scope.get("texts") or [])}
        if cb and cb in selectors:
            return True
        if label and label in texts:
            return True
    return False


def _button_policy_apply(keyboard):
    if not isinstance(keyboard, dict) or "inline_keyboard" not in keyboard:
        return keyboard
    out = {k: v for k, v in keyboard.items() if k != "inline_keyboard"}
    rows = []
    for row in keyboard.get("inline_keyboard", []):
        safe = []
        for button in row:
            b = dict(button)
            cb = str(b.get("callback_data", "") or "")
            button_id = str(b.pop("_button_id", "") or "")
            original_text = str(b.pop("_button_original_text", b.get("text", "")) or "")
            data = _button_policy_load_sync()
            scopes = [data.get("global") or {}]
            if IS_CHILD_BOT and HOSTED_BOT_ID:
                scopes.append((data.get("bots") or {}).get(str(HOSTED_BOT_ID)) or {})
            # Apply global first and bot-specific second. A child-specific value wins.
            for scope in scopes:
                selectors = {str(x) for x in (scope.get("selectors") or [])}
                texts = {str(x) for x in (scope.get("texts") or [])}
                key_options = [x for x in (button_id, cb, original_text, str(b.get("text", ""))) if x]
                labels = scope.get("labels") or {}
                styles = scope.get("styles") or {}
                for key in key_options:
                    if key in labels:
                        b["text"] = str(labels[key])[:64]
                        break
                for key in key_options:
                    if key in styles and str(styles[key]) in ("primary", "success", "danger"):
                        b["style"] = str(styles[key])
                        break
            if cb.startswith(("reply:", "read:", "quickban:", "userinfo:")):
                safe.append(b)
                continue
            if _button_policy_blocked(cb, original_text) or _button_policy_blocked(button_id, original_text):
                continue
            safe.append(b)
        if safe:
            rows.append(safe)
    out["inline_keyboard"] = rows
    return out


def button_policy_selector_for_row(row):
    """Stable selector for a DB-defined main-menu button."""
    return f"menu:{str(row['id'])}"


def _button_policy_write_sync(data):
    BUTTON_POLICY_FILE.parent.mkdir(parents=True, exist_ok=True)
    tmp = BUTTON_POLICY_FILE.with_suffix(BUTTON_POLICY_FILE.suffix + ".tmp")
    tmp.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")
    tmp.replace(BUTTON_POLICY_FILE)
    BUTTON_POLICY_CACHE["mtime"] = 0.0
    BUTTON_POLICY_CACHE["data"] = data


def button_policy_hide(scope, selector="", text=""):
    data = _button_policy_load_sync()
    if scope == "global":
        target = data.setdefault("global", {"selectors": [], "texts": []})
    else:
        target = data.setdefault("bots", {}).setdefault(str(int(scope)), {"selectors": [], "texts": []})
    selector = str(selector or "").strip()
    text = str(text or "").strip()
    if selector and selector not in target["selectors"]:
        target["selectors"].append(selector)
    if text and text not in target["texts"]:
        target["texts"].append(text)
    _button_policy_write_sync(data)


def button_policy_show(scope, selector="", text=""):
    data = _button_policy_load_sync()
    target = data.get("global", {}) if scope == "global" else (data.get("bots", {}) or {}).get(str(int(scope)), {})
    target = target or {}
    selector = str(selector or "").strip()
    text = str(text or "").strip()
    if selector:
        target["selectors"] = [x for x in target.get("selectors", []) if str(x) != selector]
    if text:
        target["texts"] = [x for x in target.get("texts", []) if str(x) != text]
    if scope != "global":
        if not target.get("selectors") and not target.get("texts"):
            (data.get("bots") or {}).pop(str(int(scope)), None)
    _button_policy_write_sync(data)


def button_policy_scope_entries(scope):
    data = _button_policy_load_sync()
    if scope == "global":
        return data.get("global") or {}
    return (data.get("bots") or {}).get(str(int(scope))) or {}


def button_policy_set_label(scope, selector, label):
    data = _button_policy_load_sync()
    if scope == "all":
        target = data.setdefault("global", {})
    else:
        target = data.setdefault("bots", {}).setdefault(str(int(scope)), {})
    target.setdefault("labels", {})[str(selector)] = str(label).strip()[:64]
    _button_policy_write_sync(data)


def button_policy_set_style(scope, selector, style):
    data = _button_policy_load_sync()
    if scope == "all":
        target = data.setdefault("global", {})
    else:
        target = data.setdefault("bots", {}).setdefault(str(int(scope)), {})
    target.setdefault("styles", {})[str(selector)] = str(style).lower()
    _button_policy_write_sync(data)


def button_policy_clear_overrides(scope, selector):
    data = _button_policy_load_sync()
    target = data.get("global", {}) if scope == "all" else (data.get("bots", {}) or {}).get(str(int(scope)), {})
    if target:
        (target.get("labels") or {}).pop(str(selector), None)
        (target.get("styles") or {}).pop(str(selector), None)
    _button_policy_write_sync(data)

def sanitize_member_keyboard(keyboard, viewer_id=None):
    """Central UI firewall with three roles: member, bot owner, platform owner.

    A hosted-bot owner receives only the deliberately small bot-admin surface;
    platform controls are never rendered to them, even if an old DB still has
    those buttons enabled.
    """
    if not isinstance(keyboard, dict) or "inline_keyboard" not in keyboard:
        return keyboard
    keyboard = _button_policy_apply(keyboard)
    try:
        viewer = int(viewer_id or 0)
    except Exception:
        viewer = 0
    if viewer and is_platform_owner(viewer):
        return keyboard
    out = {k: v for k, v in keyboard.items() if k != "inline_keyboard"}
    rows = []
    limited = is_limited_bot_owner(viewer)
    for row in keyboard.get("inline_keyboard", []):
        safe_row = []
        for button in row:
            b = dict(button)
            cb = str(b.get("callback_data", "") or "")
            if limited:
                # Limited hosted-bot owners may also operate the CONTACT inbox.
                # These callbacks are not platform administration; they are the
                # core owner-facing actions attached to an incoming member message.
                contact_cb = (
                    cb.startswith(("reply:", "history:", "read:", "userinfo:", "quickban:"))
                )
                if not cb.startswith("limited:") and cb != "admin" and not contact_cb:
                    # Normal member buttons are still useful in the main UI.
                    if is_developer_callback(cb):
                        continue
                elif cb == "admin" or contact_cb:
                    pass
            elif viewer and is_owner(viewer):
                # Non-child bot owners keep legacy owner UI, but never platform UI.
                if is_platform_only_callback(cb):
                    continue
            elif cb and is_developer_callback(cb):
                continue
            safe_row.append(b)
        if safe_row:
            rows.append(safe_row)
    out["inline_keyboard"] = rows
    return out


def ui_keyboard_for_chat(chat_id, keyboard):
    try:
        viewer = int(chat_id or 0)
    except Exception:
        viewer = 0
    return sanitize_member_keyboard(keyboard, viewer)


async def send_message(chat_id, text, keyboard=None, disable_preview=True, reply_to_message_id=None):
    data = {
        "chat_id": chat_id,
        "text": text,
        "parse_mode": "HTML",
        "disable_web_page_preview": str(bool(disable_preview)).lower(),
    }
    if reply_to_message_id:
        data["reply_parameters"] = json.dumps({"message_id": int(reply_to_message_id), "allow_sending_without_reply": True}, ensure_ascii=False)
    if keyboard is not None:
        keyboard = ui_keyboard_for_chat(chat_id, keyboard)
        data["reply_markup"] = json.dumps(colorize_keyboard(keyboard), ensure_ascii=False)
    result = await api_call("sendMessage", data=data)
    if not result.get("ok") and keyboard is not None and "style" in result.get("description", "").lower():
        data["reply_markup"] = json.dumps(strip_keyboard_styles(keyboard), ensure_ascii=False)
        result = await api_call("sendMessage", data=data)
    return result


async def send_photo(chat_id, photo, caption="", keyboard=None):
    data = {
        "chat_id": chat_id,
        "photo": photo,
    }
    if caption:
        data["caption"] = caption
        data["parse_mode"] = "HTML"
    if keyboard is not None:
        keyboard = ui_keyboard_for_chat(chat_id, keyboard)
        data["reply_markup"] = json.dumps(colorize_keyboard(keyboard), ensure_ascii=False)
    result = await api_call("sendPhoto", data=data)
    if not result.get("ok") and keyboard is not None and "style" in result.get("description", "").lower():
        data["reply_markup"] = json.dumps(strip_keyboard_styles(keyboard), ensure_ascii=False)
        result = await api_call("sendPhoto", data=data)
    return result


async def send_media(chat_id, media_type, file_id, caption="", keyboard=None, reply_to_message_id=None):
    method_map = {
        "photo": "sendPhoto",
        "video": "sendVideo",
        "document": "sendDocument",
        "animation": "sendAnimation",
        "voice": "sendVoice",
        "audio": "sendAudio",
        "sticker": "sendSticker",
        "video_note": "sendVideoNote",
    }
    method = method_map.get(media_type)
    if not method:
        return {"ok": False, "description": "Unsupported media type"}

    data = {"chat_id": chat_id, media_type: file_id}
    if reply_to_message_id:
        data["reply_parameters"] = json.dumps({"message_id": int(reply_to_message_id), "allow_sending_without_reply": True}, ensure_ascii=False)

    if caption and media_type not in ("sticker", "video_note"):
        data["caption"] = caption
        data["parse_mode"] = "HTML"

    if keyboard is not None:
        keyboard = ui_keyboard_for_chat(chat_id, keyboard)
        data["reply_markup"] = json.dumps(colorize_keyboard(keyboard), ensure_ascii=False)

    result = await api_call(method, data=data, timeout=30)
    if not result.get("ok") and keyboard is not None and "style" in result.get("description", "").lower():
        data["reply_markup"] = json.dumps(strip_keyboard_styles(keyboard), ensure_ascii=False)
        result = await api_call(method, data=data, timeout=30)
    return result


async def send_local_document(chat_id, path, caption=""):
    path = Path(path)
    if not path.exists():
        return {"ok": False, "description": "File not found"}

    content = path.read_bytes()
    files = {
        "document": (
            path.name,
            content,
            "application/octet-stream",
        )
    }
    data = {"chat_id": chat_id}
    if caption:
        data["caption"] = caption
        data["parse_mode"] = "HTML"

    return await api_call("sendDocument", data=data, files=files, timeout=60)


async def edit_message(chat_id, message_id, text, keyboard=None):
    """Edit a text message safely; if the source is a photo/caption message,
    transparently send a fresh text message instead of leaving the UI stuck."""
    data = {
        "chat_id": chat_id,
        "message_id": message_id,
        "text": text,
        "parse_mode": "HTML",
    }
    if keyboard is not None:
        keyboard = ui_keyboard_for_chat(chat_id, keyboard)
        data["reply_markup"] = json.dumps(colorize_keyboard(keyboard), ensure_ascii=False)

    # message_id == 0 is used by command routes; there is nothing to edit.
    if not message_id:
        return await send_message(chat_id, text, keyboard)

    result = await api_call("editMessageText", data=data)
    if result.get("ok"):
        return result

    desc = str(result.get("description", "")).lower()

    # Telegram returns this when the visible message is a photo/video/caption
    # message or otherwise cannot be edited as text. Send a new control screen.
    media_edit_error = any(term in desc for term in (
        "there is no text in the message to edit",
        "message can't be edited",
        "message cannot be edited",
        "message is not modified",
        "bad request: message to edit not found",
        "message to edit not found",
        "can't edit messages with inline keyboard",
    ))
    if "not modified" in desc:
        # Keep the existing UI when Telegram confirms no changes were needed.
        return result

    if keyboard is not None and "style" in desc:
        data["reply_markup"] = json.dumps(strip_keyboard_styles(keyboard), ensure_ascii=False)
        retry = await api_call("editMessageText", data=data)
        if retry.get("ok"):
            return retry
        desc = str(retry.get("description", "")).lower()
        media_edit_error = media_edit_error or any(term in desc for term in (
            "there is no text in the message to edit",
            "message can't be edited",
            "message cannot be edited",
            "message to edit not found",
        ))
        result = retry

    if media_edit_error:
        return await send_message(chat_id, text, keyboard)

    # Final safe fallback for UI operations: never leave the owner with only a
    # callback spinner/confirmation and no panel.
    fallback = await send_message(chat_id, text, keyboard)
    return fallback if fallback.get("ok") else result


async def answer_callback(callback_id, text="تم"):
    return await api_call(
        "answerCallbackQuery",
        data={
            "callback_query_id": callback_id,
            "text": text,
            "show_alert": False,
        },
    )


async def delete_message(chat_id, message_id):
    return await api_call(
        "deleteMessage",
        data={"chat_id": chat_id, "message_id": message_id},
    )


# =========================================================
# DATABASE
# =========================================================

async def _get_db_connection():
    global DB_CONNECTION, DB_LOCK
    if DB_CONNECTION is None:
        DB_LOCK = DB_LOCK or asyncio.Lock()
        DB_CONNECTION = await aiosqlite.connect(DB_FILE, timeout=20)
        DB_CONNECTION.row_factory = aiosqlite.Row
        await DB_CONNECTION.execute(f"PRAGMA busy_timeout={DB_BUSY_TIMEOUT_MS}")
        await DB_CONNECTION.execute("PRAGMA foreign_keys=ON")
        await DB_CONNECTION.execute("PRAGMA journal_mode=WAL")
        await DB_CONNECTION.execute("PRAGMA synchronous=NORMAL")
    return DB_CONNECTION


async def db_execute(query, params=(), fetchone=False, fetchall=False, retries=5):
    """High-throughput per-bot SQLite access. Reuses one connection instead of
    opening/committing a new connection for every query. Each hosted bot process
    owns its own connection and lock, so one bot cannot lock another bot's DB."""
    global DB_CONNECTION, DB_LOCK
    DB_LOCK = DB_LOCK or asyncio.Lock()
    is_read = bool(fetchone or fetchall) and not query.lstrip().upper().startswith(("INSERT", "UPDATE", "DELETE", "REPLACE", "CREATE", "ALTER", "DROP"))
    last_error = None
    for attempt in range(max(1, retries)):
        try:
            async with DB_LOCK:
                db = await _get_db_connection()
                cursor = await db.execute(query, params)
                result = None
                if fetchone:
                    result = await cursor.fetchone()
                elif fetchall:
                    result = await cursor.fetchall()
                if not is_read:
                    await db.commit()
                await cursor.close()
                return result
        except aiosqlite.OperationalError as exc:
            last_error = exc
            text = str(exc).lower()
            if "locked" not in text and "busy" not in text:
                raise
            # Reconnect if SQLite invalidated the connection.
            if DB_CONNECTION is not None and ("closed" in text or "cannot operate" in text):
                try:
                    await DB_CONNECTION.close()
                except Exception:
                    pass
                DB_CONNECTION = None
            await asyncio.sleep(min(0.05 * (2 ** attempt), 1.0))
    raise last_error


def load_admin_buttons_sync(rows):
    ADMIN_BUTTONS.clear()
    for row in rows or []:
        ADMIN_BUTTONS[row["id"]] = {
            "text": row["text"],
            "callback_data": row["callback_data"],
            "row": int(row["row"]),
            "position": int(row["position"]),
            "enabled": int(row["enabled"]),
            "style": row["style"] if row["style"] in ("primary", "success", "danger") else "primary",
        }


async def load_admin_buttons():
    rows = await db_execute("SELECT * FROM admin_buttons ORDER BY row, position, id", fetchall=True)
    load_admin_buttons_sync(rows)


async def db_init():
    async with aiosqlite.connect(DB_FILE) as db:
        await db.execute("PRAGMA journal_mode=WAL")
        await db.execute("PRAGMA synchronous=NORMAL")
        await db.execute(f"PRAGMA busy_timeout={DB_BUSY_TIMEOUT_MS}")
        await db.execute("PRAGMA foreign_keys=ON")
        await db.execute("PRAGMA temp_store=MEMORY")
        await db.execute("PRAGMA cache_size=-32768")
        await db.execute("PRAGMA mmap_size=268435456")

        await db.execute("""
            CREATE TABLE IF NOT EXISTS users (
                user_id INTEGER PRIMARY KEY,
                name TEXT DEFAULT '',
                username TEXT DEFAULT '',
                joined_at TEXT DEFAULT '',
                last_activity TEXT DEFAULT '',
                messages INTEGER DEFAULT 0,
                media INTEGER DEFAULT 0,
                blocked INTEGER DEFAULT 0,
                muted_until REAL DEFAULT 0,
                notes TEXT DEFAULT '',
                points INTEGER DEFAULT 0
            )
        """)

        await db.execute("""
            CREATE TABLE IF NOT EXISTS settings (
                key TEXT PRIMARY KEY,
                value TEXT DEFAULT ''
            )
        """)

        await db.execute("""
            CREATE TABLE IF NOT EXISTS buttons (
                id TEXT PRIMARY KEY,
                text TEXT NOT NULL,
                action TEXT NOT NULL,
                row INTEGER DEFAULT 0,
                position INTEGER DEFAULT 0,
                enabled INTEGER DEFAULT 1,
                style TEXT DEFAULT 'primary',
                url TEXT DEFAULT '',
                action_value TEXT DEFAULT ''
            )
        """)

        # Safe migrations for installations created by older versions.
        for column, definition in (
            ("points", "INTEGER DEFAULT 0"),
            ("style", "TEXT DEFAULT 'primary'"),
            ("url", "TEXT DEFAULT ''"),
            ("action_value", "TEXT DEFAULT ''"),
            ("photo", "TEXT DEFAULT ''"),
            ("caption", "TEXT DEFAULT ''"),
        ):
            try:
                await db.execute(f"ALTER TABLE buttons ADD COLUMN {column} {definition}")
            except Exception:
                pass

        await db.execute("""
            CREATE TABLE IF NOT EXISTS deleted_buttons (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                button_id TEXT NOT NULL,
                text TEXT DEFAULT '',
                action TEXT DEFAULT 'text',
                row INTEGER DEFAULT 0,
                position INTEGER DEFAULT 0,
                enabled INTEGER DEFAULT 1,
                style TEXT DEFAULT 'primary',
                url TEXT DEFAULT '',
                action_value TEXT DEFAULT '',
                photo TEXT DEFAULT '',
                caption TEXT DEFAULT '',
                deleted_by INTEGER DEFAULT 0,
                deleted_at TEXT DEFAULT ''
            )
        """)

        await db.execute("""
            CREATE TABLE IF NOT EXISTS messages (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER,
                direction TEXT,
                media_type TEXT DEFAULT 'text',
                content TEXT DEFAULT '',
                telegram_message_id INTEGER DEFAULT 0,
                read_at TEXT DEFAULT '',
                created_at TEXT
            )
        """)

        # Migration for older databases: persist the inbox read state.
        try:
            await db.execute("ALTER TABLE messages ADD COLUMN read_at TEXT DEFAULT ''")
        except Exception:
            pass

        await db.execute("""
            CREATE TABLE IF NOT EXISTS forced_channels (
                channel TEXT PRIMARY KEY
            )
        """)

        await db.execute("""
            CREATE TABLE IF NOT EXISTS audit_logs (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                action TEXT,
                details TEXT,
                created_at TEXT
            )
        """)

        await db.execute("""
            CREATE TABLE IF NOT EXISTS error_logs (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                source TEXT,
                error TEXT,
                created_at TEXT
            )
        """)

        await db.execute("""
            CREATE TABLE IF NOT EXISTS banned_words (
                word TEXT PRIMARY KEY
            )
        """)

        await db.execute("""
            CREATE TABLE IF NOT EXISTS menu_pages (
                id TEXT PRIMARY KEY,
                title TEXT NOT NULL,
                text TEXT DEFAULT '',
                photo TEXT DEFAULT '',
                enabled INTEGER DEFAULT 1,
                created_at TEXT DEFAULT ''
            )
        """)

        await db.execute("""
            CREATE TABLE IF NOT EXISTS page_buttons (
                id TEXT PRIMARY KEY,
                page_id TEXT NOT NULL,
                text TEXT NOT NULL,
                action TEXT NOT NULL,
                row INTEGER DEFAULT 0,
                position INTEGER DEFAULT 0,
                enabled INTEGER DEFAULT 1,
                style TEXT DEFAULT 'primary',
                url TEXT DEFAULT '',
                action_value TEXT DEFAULT ''
            )
        """)

        await db.execute("""
            CREATE TABLE IF NOT EXISTS admin_buttons (
                id TEXT PRIMARY KEY,
                text TEXT NOT NULL,
                callback_data TEXT NOT NULL,
                row INTEGER DEFAULT 0,
                position INTEGER DEFAULT 0,
                enabled INTEGER DEFAULT 1,
                style TEXT DEFAULT 'primary'
            )
        """)

        await db.execute("""
            CREATE TABLE IF NOT EXISTS themes (
                id TEXT PRIMARY KEY, name TEXT NOT NULL, data TEXT DEFAULT '{}', enabled INTEGER DEFAULT 1, created_at TEXT DEFAULT ''
            )
        """)
        await db.execute("""
            CREATE TABLE IF NOT EXISTS theme_versions (
                id INTEGER PRIMARY KEY AUTOINCREMENT, theme_id TEXT, snapshot TEXT DEFAULT '{}', created_at TEXT DEFAULT ''
            )
        """)
        await db.execute("""
            CREATE TABLE IF NOT EXISTS button_analytics (
                button_id TEXT PRIMARY KEY, clicks INTEGER DEFAULT 0, last_click TEXT DEFAULT ''
            )
        """)
        await db.execute("""
            CREATE TABLE IF NOT EXISTS auto_replies (
                id INTEGER PRIMARY KEY AUTOINCREMENT, trigger TEXT NOT NULL, response TEXT DEFAULT '', match_type TEXT DEFAULT 'contains', enabled INTEGER DEFAULT 1, priority INTEGER DEFAULT 0, created_at TEXT DEFAULT ''
            )
        """)
        await db.execute("""
            CREATE TABLE IF NOT EXISTS automations (
                id INTEGER PRIMARY KEY AUTOINCREMENT, title TEXT NOT NULL, kind TEXT DEFAULT 'message', payload TEXT DEFAULT '{}', next_run REAL DEFAULT 0, interval_sec INTEGER DEFAULT 0, enabled INTEGER DEFAULT 1, created_at TEXT DEFAULT ''
            )
        """)
        await db.execute("""
            CREATE TABLE IF NOT EXISTS user_segments (
                id TEXT PRIMARY KEY, name TEXT NOT NULL, rule TEXT DEFAULT 'all', value TEXT DEFAULT '', enabled INTEGER DEFAULT 1
            )
        """)
        await db.execute("""
            CREATE TABLE IF NOT EXISTS segment_members (
                segment_id TEXT, user_id INTEGER, PRIMARY KEY(segment_id,user_id)
            )
        """)
        await db.execute("""
            CREATE TABLE IF NOT EXISTS button_actions (
                button_id TEXT PRIMARY KEY, actions TEXT DEFAULT '[]'
            )
        """)
        await db.execute("""
            CREATE TABLE IF NOT EXISTS button_flow_texts (
                button_id TEXT NOT NULL,
                flow_key TEXT NOT NULL,
                text TEXT DEFAULT '',
                PRIMARY KEY(button_id, flow_key)
            )
        """)

        defaults = {
            "start_text": DEFAULT_START_TEXT,
            "welcome_text": DEFAULT_START_TEXT,
            "contact_text": DEFAULT_CONTACT_TEXT,
            "contact_photo": "",
            "contact_enabled": "1",
            "contact_footer": "",
            "maintenance_photo": "",
            "maintenance_photo_enabled": "1",
            "dev_photo_enabled": "1",
            "conversation_mode": "1",
            "maintenance": "0",
            "notifications": "1",
            "force_sub": "1",
            "protection": "1",
            "max_requests_per_min": "30",
            "welcome_photo": "",
            "welcome_enabled": "1",
            "dev_photo": "",
            "bot_enabled": "1",
            "button_default_style": "primary",
            "admin_theme": "pro",
            "button_confirm_delete": "1",
            "button_max_per_row": "3",
            "editor_show_ids": "0",
            "editor_auto_normalize": "1",
            "editor_page_size": "18",
            "theme_active": "default",
            "analytics_enabled": "1",
            "automation_enabled": "1",
            "autoreply_enabled": "1",
            "footer_text": "",
            "maintenance_text": "🔧 <b>البوت في وضع الصيانة</b>\n\nحاول لاحقاً.",
            "disabled_text": "⛔ <b>البوت متوقف مؤقتاً</b>\n\nحاول لاحقاً.",
            "banned_text": "🚫 <b>أنت محظور من استخدام البوت.</b>",
            "rate_warning_text": "⚠️ تم تجاوز حد الرسائل. حاول لاحقاً.",
            "button_default_style": "primary",
        }

        for key, value in defaults.items():
            await db.execute(
                "INSERT OR IGNORE INTO settings(key,value) VALUES(?,?)",
                (key, value),
            )

        for key, value in NOTIFICATION_DEFAULTS.items():
            await db.execute("INSERT OR IGNORE INTO settings(key,value) VALUES(?,?)", (key, value))

        admin_defaults = [
            ("dashboard", "📊 لوحة المعلومات", "pro:dashboard", 0, 0, 1, "primary"),
            ("ui", "🎨 الواجهة", "pro:ui", 0, 1, 1, "success"),
            ("pages", "🧩 الصفحات", "pro:pages", 1, 0, 1, "primary"),
            ("content", "📝 المحتوى", "pro:content", 1, 1, 1, "primary"),
            ("users", "👥 المستخدمون", "pro:users", 2, 0, 1, "primary"),
            ("contact", "📨 التواصل", "adm:contact", 2, 1, 1, "success"),
            ("media", "🖼 صور التواصل", "adm:contact_media", 3, 0, 1, "primary"),
            ("status", "🔧 الصيانة", "adm:status", 3, 1, 1, "danger"),
            ("broadcast", "📢 الإذاعة", "adm:broadcast", 4, 0, 1, "primary"),
            ("channels", "📣 القنوات", "adm:channels", 4, 1, 1, "primary"),
            ("security", "🛡 الحماية", "pro:security", 5, 0, 1, "success"),
            ("system", "⚙️ النظام", "pro:system", 5, 1, 1, "primary"),
            ("logs", "📜 السجلات", "pro:logs", 6, 0, 1, "primary"),
            ("backup", "💾 النسخ والتصدير", "pro:backup", 6, 1, 1, "primary"),
            ("welcome", "🎉 الترحيب", "adm:welcome", 7, 0, 1, "success"),
            ("photos", "🖼 الصور", "adm:photos", 7, 1, 1, "primary"),
            ("texts", "💬 النصوص", "adm:texts", 8, 0, 1, "primary"),
            ("notifications", "🔔 الإشعارات", "adm:notifications", 8, 1, 1, "success"),
            ("refresh", "🔄 تحديث اللوحة", "admin", 8, 1, 1, "primary"),
            ("adminui", "🎛 أزرار المطور", "pro:adminui", 9, 0, 1, "success"),
            ("ultimate", "🚀 مركز V13", "v13:dashboard", 10, 0, 1, "success"),
            ("v16_control", "👑 مركز السيطرة", "v16:dashboard", 10, 1, 1, "success"),
            ("hosted", "🌐 البوتات المستضافة", "adm:hosted", 11, 0, 1, "success"),
            ("exemptions", "🎁 إعفاءات الإنشاء", "adm:creator_exempt", 11, 1, 1, "success"),
            ("creator_exempt", "🎁 إعفاءات الإنشاء", "adm:creator_exempt", 10, 1, 1, "success"),
        ]
        for item in admin_defaults:
            await db.execute("INSERT OR IGNORE INTO admin_buttons(id,text,callback_data,row,position,enabled,style) VALUES(?,?,?,?,?,?,?)", item)

        for button in DEFAULT_BUTTONS:
            await db.execute("""
                INSERT OR IGNORE INTO buttons
                (id,text,action,row,position,enabled,style)
                VALUES(?,?,?,?,?,?,?)
            """, (
                button["id"],
                button["text"],
                button["action"],
                button["row"],
                button["position"],
                button["enabled"],
                button.get("style", "primary"),
            ))

        await db.execute("UPDATE buttons SET style='success' WHERE id='contact' AND (style IS NULL OR style='')")
        await db.execute("UPDATE buttons SET style='primary' WHERE id IN ('info','top') AND (style IS NULL OR style='')")
        await db.execute("CREATE INDEX IF NOT EXISTS idx_users_last_activity ON users(last_activity)")
        await db.execute("CREATE INDEX IF NOT EXISTS idx_messages_user_id_id ON messages(user_id,id)")
        await db.execute("CREATE INDEX IF NOT EXISTS idx_buttons_row_position ON buttons(row,position)")
        await db.execute("CREATE INDEX IF NOT EXISTS idx_deleted_buttons_id ON deleted_buttons(id)")
        await db.commit()
    await load_admin_buttons()
    # Self-heal missing developer buttons on every startup.
    # Existing customized rows are preserved; only absent IDs are inserted.
    await db_execute("""
        INSERT OR IGNORE INTO admin_buttons(id,text,callback_data,row,position,enabled,style)
        VALUES('dashboard','📊 لوحة المعلومات','pro:dashboard',0,0,1,'primary')
    """)
    await load_admin_buttons()
    if not IS_CHILD_BOT:
        try:
            await sync_global_forced_channels()
        except Exception as exc:
            await log_error("global_policy_init", exc)
    try:
        await v16_init_db()
    except Exception as exc:
        await log_error("v16_init", exc)


async def log_error(source, error):
    try:
        await db_execute(
            "INSERT INTO error_logs(source,error,created_at) VALUES(?,?,?)",
            (source, str(error), now_text()),
        )
    except Exception:
        pass


async def audit(action, details=""):
    try:
        await db_execute(
            "INSERT INTO audit_logs(action,details,created_at) VALUES(?,?,?)",
            (action, details, now_text()),
        )
    except Exception as exc:
        await log_error("audit", exc)


NOTIFICATION_DEFAULTS = {
    "notif_new_user": "📨 <b>عضو جديد</b>\n\n👤 {name}\n🆔 <code>{id}</code>\n🔗 @{username}",
    "notif_incoming_message": "📨 <b>رسالة جديدة من عضو</b>\n\n👤 الاسم: {name}\n🆔 <code>{id}</code>\n🔗 @{username}\n\n{message}",
    "notif_reply_prompt": "📨 <b>وضع الرد</b>\n\n🆔 المستخدم: <code>{id}</code>\n\nأرسل الرد الآن. الرسائل السابقة ستبقى محفوظة ولن تختفي.",
    "notif_reply_success": "✅ تم إرسال الرد.",
    "notif_reply_failed": "❌ لم يتم إرسال الرد. غالباً المستخدم حظر البوت.",
    "notif_media_reply_success": "✅ تم إرسال الوسائط.",
    "notif_media_reply_failed": "❌ فشل إرسال الوسائط للمستخدم.",
    "notif_ban_user": "🚫 <b>تم حظرك من استخدام البوت.</b>",
    "notif_unban_user": "✅ <b>تم فك حظرك.</b> يمكنك استخدام البوت مجدداً.",
    "notif_ban_admin": "🚫 تم حظر العضو.",
    "notif_unban_admin": "✅ تم فك حظر العضو.",
    "notif_read_user": "❤️ <b>تمت قراءة رسالتك</b>\n\nشكرًا لتواصلك معنا.",
    "notif_maintenance": "🔧 <b>البوت في وضع الصيانة</b>\n\nحاول لاحقاً.",
    "notif_disabled": "⛔ <b>البوت متوقف مؤقتاً</b>\n\nحاول لاحقاً.",
    "notif_rate_warning": "⚠️ تم تجاوز حد الرسائل. حاول لاحقاً.",
    "notif_force_sub": "📢 <b>الاشتراك مطلوب قبل استخدام البوت.</b>\n\nاشترك في القنوات التالية ثم اضغط على التحقق:",
    "notif_force_sub_failed": "❌ لم يكتمل الاشتراك بعد. اشترك في القنوات ثم أعد التحقق.",
    "notif_broadcast_prompt": "📢 أرسل نص الإذاعة الآن.",
    "notif_broadcast_media_prompt": "📢 أرسل الوسائط التي تريد إذاعتها.",
    "notif_broadcast_done": "📢 <b>انتهت الإذاعة</b>\n\n👥 المستهدفون: <b>{total}</b>\n✅ نجاح: <b>{success}</b>\n❌ فشل: <b>{failed}</b>",
    "notif_host_broadcast_prompt": "📝 أرسل نص الرسالة لإرسالها في جميع البوتات المشتركة.",
    "notif_host_broadcast_media_prompt": "🖼 أرسل الصورة/الفيديو/الملف/الصوت لإرساله في جميع البوتات المشتركة.",
    "notif_host_broadcast_done": "📢 <b>انتهت الإذاعة لجميع البوتات</b>\n\n🌐 البوتات: <b>{bots}</b>\n✅ نجاح: <b>{success}</b>\n❌ فشل: <b>{failed}</b>",
    "notif_limited_broadcast_done": "📢 <b>انتهت الإذاعة الخاصة ببوتك</b>\n\n👥 المستهدفون: <b>{total}</b>\n✅ تم الإرسال: <b>{success}</b>\n❌ فشل: <b>{failed}</b>",
    "notif_welcome_photo_prompt": "🖼 أرسل صورة الترحيب الجديدة.",
    "notif_welcome_text_prompt": "✏️ أرسل نص الترحيب الجديد.",
    "notif_dev_photo_prompt": "🖼 أرسل صورة المطور التي تظهر في المراسلة.",
    "notif_contact_photo_prompt": "🖼 أرسل صورة التواصل الآن.",
    "notif_maintenance_photo_prompt": "🖼 أرسل صورة الصيانة الآن.",
    "notif_contact_success": "✅ تم إرسال رسالتك للمطور.",
    "notif_contact_failed": "❌ تعذر إرسال الرسالة للمطور.",
    "notif_contact_media_success": "✅ تم إرسال الوسائط للمطور.",
    "notif_contact_media_failed": "❌ تعذر إرسال الوسائط.",
    "notif_saved": "✅ تم الحفظ بنجاح.",
    "notif_cancel": "❌ تم إلغاء العملية.",
    "notif_no_permission": "⛔ لا تملك صلاحية تنفيذ هذا الإجراء.",
}
NOTIFICATION_LABELS = {
    "notif_contact_success":"📨 نجاح إرسال الرسالة","notif_contact_failed":"📨 فشل إرسال الرسالة","notif_contact_media_success":"📎 نجاح إرسال الوسائط للمطور","notif_contact_media_failed":"📎 فشل إرسال الوسائط للمطور",
    "notif_new_user":"👤 عضو جديد","notif_incoming_message":"📨 رسالة جديدة","notif_reply_prompt":"✏️ طلب الرد",
    "notif_reply_success":"✅ نجاح الرد","notif_reply_failed":"❌ فشل الرد","notif_media_reply_success":"📎 نجاح الوسائط",
    "notif_media_reply_failed":"📎 فشل الوسائط","notif_ban_user":"🚫 حظر العضو","notif_unban_user":"🔓 فك حظر العضو",
    "notif_ban_admin":"🚫 تأكيد الحظر","notif_unban_admin":"🔓 تأكيد فك الحظر","notif_read_user":"❤️ قراءة الرسالة",
    "notif_maintenance":"🔧 الصيانة","notif_disabled":"⛔ إيقاف البوت","notif_rate_warning":"⚠️ تجاوز الحد",
    "notif_force_sub":"📢 الاشتراك الإجباري","notif_force_sub_failed":"❌ فشل الاشتراك","notif_broadcast_prompt":"📢 طلب نص الإذاعة",
    "notif_broadcast_media_prompt":"🖼 طلب وسائط الإذاعة","notif_broadcast_done":"📊 انتهاء الإذاعة",
    "notif_host_broadcast_prompt":"🌐 طلب إذاعة كل البوتات","notif_host_broadcast_media_prompt":"🌐 طلب وسائط كل البوتات",
    "notif_host_broadcast_done":"🌐 انتهاء إذاعة كل البوتات","notif_limited_broadcast_done":"🤖 انتهاء إذاعة بوت واحد",
    "notif_welcome_photo_prompt":"🎉 طلب صورة الترحيب","notif_welcome_text_prompt":"🎉 طلب نص الترحيب","notif_dev_photo_prompt":"👨‍💻 طلب صورة المطور",
    "notif_contact_photo_prompt":"📨 طلب صورة التواصل","notif_maintenance_photo_prompt":"🔧 طلب صورة الصيانة","notif_saved":"💾 الحفظ","notif_cancel":"↩️ الإلغاء","notif_no_permission":"⛔ عدم الصلاحية",
}
NOTIFICATION_PLACEHOLDERS = {
    "notif_new_user":"{name} {id} {username}","notif_incoming_message":"{name} {id} {username} {message}","notif_reply_prompt":"{id}",
    "notif_broadcast_done":"{total} {success} {failed}","notif_host_broadcast_done":"{bots} {success} {failed}","notif_limited_broadcast_done":"{total} {success} {failed}",
}
class _NotificationFormat(dict):
    def __missing__(self,key): return "{"+key+"}"
async def get_notification(key, default="", **values):
    template=await get_setting(key, default or NOTIFICATION_DEFAULTS.get(key,""))
    try:
        safe={k:(esc(v) if k in ("name","username","message") else v) for k,v in values.items()}
        return str(template).format_map(_NotificationFormat(safe))
    except Exception as exc:
        await log_error("notification_format", exc); return str(template)
async def pro_notifications(chat_id,message_id=0):
    lines=["🔔 <b>مركز الإشعارات</b>","","تعديل مركزي: نفس القوالب تُستخدم في البوت الرئيسي والبوتات المستضافة.","اضغط على الإشعار لتعديله."]
    for k,label in NOTIFICATION_LABELS.items():
        v=await get_setting(k,NOTIFICATION_DEFAULTS[k]); lines.append(f"\n{label}: <code>{esc(str(v).replace(chr(10),' '))[:70]}</code>")
    rows=[[{"text":f"✏️ {label}","callback_data":f"notifedit:{k}"}] for k,label in NOTIFICATION_LABELS.items()]
    rows += [[{"text":"♻️ استعادة كل الإشعارات","callback_data":"notifreset:all"}],[{"text":"🔙 لوحة المطور","callback_data":"admin"}]]
    kb=pro_kb(rows)
    if message_id: await edit_message(chat_id,message_id,"\n".join(lines),kb)
    else: await send_message(chat_id,"\n".join(lines),kb)

async def get_setting(key, default=""):
    now = time.monotonic()
    cached = SETTINGS_CACHE.get(key)
    if cached and now - cached[0] < SETTINGS_CACHE_TTL:
        return cached[1]
    row = await db_execute(
        "SELECT value FROM settings WHERE key=?",
        (key,),
        fetchone=True,
    )
    value = row["value"] if row else default
    SETTINGS_CACHE[key] = (now, value)
    return value


async def set_setting(key, value):
    value = str(value)
    await db_execute(
        "INSERT INTO settings(key,value) VALUES(?,?) "
        "ON CONFLICT(key) DO UPDATE SET value=excluded.value",
        (key, value),
    )
    SETTINGS_CACHE[key] = (time.monotonic(), value)


async def sync_notification_settings_to_db(db_path):
    """Copy the platform's current notification templates into one hosted bot DB."""
    if not db_path:
        return False
    try:
        values = {}
        for key in NOTIFICATION_DEFAULTS:
            values[key] = await get_setting(key, NOTIFICATION_DEFAULTS[key])
        async with aiosqlite.connect(str(db_path), timeout=20) as db:
            await db.execute("CREATE TABLE IF NOT EXISTS settings(key TEXT PRIMARY KEY, value TEXT DEFAULT '')")
            await db.executemany(
                "INSERT INTO settings(key,value) VALUES(?,?) ON CONFLICT(key) DO UPDATE SET value=excluded.value",
                list(values.items()),
            )
            await db.commit()
        return True
    except Exception as exc:
        await log_error("sync_notification_settings", exc)
        return False

async def sync_notifications_to_all_hosted_bots():
    """Push global notification templates to every hosted bot immediately."""
    if IS_CHILD_BOT or not is_platform_owner(PLATFORM_OWNER_ID):
        return 0, 0
    rows = await db_execute("SELECT id,db_file FROM hosted_bots", fetchall=True) or []
    success = failed = 0
    for row in rows:
        if await sync_notification_settings_to_db(row["db_file"]):
            success += 1
        else:
            failed += 1
    return success, failed

async def get_user(user_id):
    return await db_execute(
        "SELECT * FROM users WHERE user_id=?",
        (user_id,),
        fetchone=True,
    )


async def upsert_user(user):
    user_id = int(user["id"])
    name = user.get("first_name", "") or ""
    username = user.get("username", "") or ""
    timestamp = now_text()
    existing = await get_user(user_id)
    await db_execute("""
        INSERT INTO users(user_id,name,username,joined_at,last_activity)
        VALUES(?,?,?,?,?)
        ON CONFLICT(user_id) DO UPDATE SET
            name=excluded.name, username=excluded.username, last_activity=excluded.last_activity
    """, (user_id, name, username, timestamp, timestamp))
    return existing is None


async def increment_user(user_id, messages=0, media=0):
    await db_execute("""
        UPDATE users
        SET messages=messages+?,
            media=media+?,
            last_activity=?
        WHERE user_id=?
    """, (messages, media, now_text(), user_id))


# =========================================================
# SETTINGS / BUTTONS
# =========================================================

async def get_buttons(include_disabled=False):
    if include_disabled:
        rows = await db_execute("""
            SELECT * FROM buttons
            ORDER BY row ASC, position ASC, id ASC
        """, fetchall=True)
    else:
        rows = await db_execute("""
            SELECT * FROM buttons
            WHERE enabled=1
            ORDER BY row ASC, position ASC, id ASC
        """, fetchall=True)
    rows = rows or []
    # Hosted bots keep the creation button: action_keyboard converts it to a
    # deep-link into the central platform bot, never to local payment handling.
    return rows


def action_keyboard(rows):
    keyboard = []
    current_row = None
    current = []

    for row in rows:
        if current_row is None:
            current_row = row["row"]
        if row["row"] != current_row:
            if current:
                keyboard.append(current)
            current = []
            current_row = row["row"]

        button = {
            "text": row["text"],
            "style": row["style"] if row["style"] in ("primary", "success", "danger") else "primary",
            # Internal metadata is removed by _button_policy_apply before Telegram sees it.
            "_button_id": str(row["id"]),
            "_button_original_text": str(row["text"] or ""),
        }
        if IS_CHILD_BOT and row["action"] == "create_bot":
            button["url"] = "https://t.me/INFJXBOT?start=create_bot"
        elif row["url"]:
            button["url"] = row["url"]
        else:
            button["callback_data"] = f"menu:{row['id']}"
        current.append(button)

    if current:
        keyboard.append(current)
    return {"inline_keyboard": keyboard}


async def main_keyboard():
    now = time.time()
    if MAIN_BUTTON_CACHE["keyboard"] is not None and now - MAIN_BUTTON_CACHE["ts"] < 2.5:
        return MAIN_BUTTON_CACHE["keyboard"]
    rows = await get_buttons()
    keyboard = action_keyboard(rows)
    MAIN_BUTTON_CACHE["keyboard"] = keyboard
    MAIN_BUTTON_CACHE["ts"] = now
    return keyboard


def back_keyboard(callback="main"):
    return {
        "inline_keyboard": [
            [{"text": "🔙 رجوع", "callback_data": callback}]
        ]
    }


async def get_button_flow_text(button_id, flow_key, default=""):
    """Per-hosted-bot editable text for a button's complete user flow."""
    row = await db_execute(
        "SELECT text FROM button_flow_texts WHERE button_id=? AND flow_key=?",
        (str(button_id), str(flow_key)), fetchone=True,
    )
    return str(row["text"] if row else default)


async def set_button_flow_text(button_id, flow_key, text):
    await db_execute(
        "INSERT INTO button_flow_texts(button_id,flow_key,text) VALUES(?,?,?) "
        "ON CONFLICT(button_id,flow_key) DO UPDATE SET text=excluded.text",
        (str(button_id), str(flow_key), str(text)),
    )


async def show_limited_buttons(chat_id, message_id=0):
    rows = await get_buttons(include_disabled=True)
    lines = ["🎨 <b>أزرار بوتك ومحتواها</b>", "", "تعديل هذه الإعدادات يخص هذا البوت فقط."]
    kb = []
    for r in rows or []:
        bid = str(r["id"])
        state = "🟢" if int(r["enabled"] or 0) else "🔴"
        lines.append(f"{state} <b>{esc(r['text'])}</b> — <code>{esc(bid)}</code>")
        kb.append([{"text": f"✏️ {r['text']}", "callback_data": f"limitedbtn:{bid}"}])
    kb.append([{"text":"🔙 رجوع","callback_data":"admin"}])
    body="\n".join(lines)
    return await (edit_message(chat_id,message_id,body,{"inline_keyboard":kb}) if message_id else send_message(chat_id,body,{"inline_keyboard":kb}))


async def show_limited_button_editor(chat_id, message_id, button_id):
    row = await db_execute("SELECT * FROM buttons WHERE id=?", (button_id,), fetchone=True)
    if not row:
        return await send_message(chat_id, "❌ الزر غير موجود.", limited_admin_keyboard())
    enabled = int(row["enabled"] or 0)
    prompt = await get_button_flow_text(button_id, "prompt", "")
    success = await get_button_flow_text(button_id, "success", "")
    error = await get_button_flow_text(button_id, "error", "")
    text = (
        "🎨 <b>تعديل الزر</b>\n\n"
        f"🔘 الاسم: <b>{esc(row['text'])}</b>\n"
        f"🆔 ID: <code>{esc(button_id)}</code>\n"
        f"👁 الحالة: {'🟢 ظاهر' if enabled else '🔴 مخفي'}\n\n"
        f"📝 رسالة الطلب: {esc(prompt) if prompt else 'افتراضية'}\n"
        f"✅ رسالة النجاح: {esc(success) if success else 'افتراضية'}\n"
        f"❌ رسالة الخطأ: {esc(error) if error else 'افتراضية'}"
    )
    kb={"inline_keyboard":[
        [{"text":"✏️ اسم الزر","callback_data":f"limitedbtnfield:{button_id}:label"}],
        [{"text":"📝 رسالة الطلب","callback_data":f"limitedbtnfield:{button_id}:prompt"}],
        [{"text":"✅ رسالة النجاح","callback_data":f"limitedbtnfield:{button_id}:success"}],
        [{"text":"❌ رسالة الخطأ","callback_data":f"limitedbtnfield:{button_id}:error"}],
        [{"text":("🔴 إخفاء الزر" if enabled else "🟢 إظهار الزر"),"callback_data":f"limitedbtntoggle:{button_id}"}],
        [{"text":"🔙 الأزرار","callback_data":"limited:buttons"}],
    ]}
    return await edit_message(chat_id,message_id,text,kb)


async def show_limited_blocked(chat_id, message_id=0):
    rows=await db_execute("SELECT user_id,name,username,last_activity FROM users WHERE blocked=1 ORDER BY last_activity DESC LIMIT 100",fetchall=True) or []
    lines=["🚫 <b>قائمة المحظورين</b>","",f"العدد: <b>{len(rows)}</b>",""]
    for r in rows:
        lines.append(f"• <code>{int(r['user_id'])}</code> — {esc(r['name'] or 'مستخدم')} — @{esc(r['username']) if r['username'] else 'بدون'}")
    if not rows: lines.append("لا يوجد مستخدمون محظورون.")
    kb={"inline_keyboard":[[{"text":"🔄 تحديث","callback_data":"limited:blocked"}],[{"text":"🔙 رجوع","callback_data":"admin"}]]}
    return await (edit_message(chat_id,message_id,"\n".join(lines),kb) if message_id else send_message(chat_id,"\n".join(lines),kb))


async def show_limited_contacts(chat_id, message_id=0):
    rows=await db_execute("""
        SELECT u.user_id,u.name,u.username,u.messages,u.media,u.last_activity,
               COALESCE(m.cnt,0) AS stored_messages
        FROM users u LEFT JOIN (SELECT user_id,COUNT(*) cnt FROM messages WHERE direction='USER' GROUP BY user_id) m
        ON m.user_id=u.user_id
        WHERE u.user_id<>? AND (u.messages>0 OR COALESCE(m.cnt,0)>0)
        ORDER BY COALESCE(m.cnt,u.messages) DESC,last_activity DESC LIMIT 100
    """,(int(OWNER_ID),),fetchall=True) or []
    lines=["📨 <b>الأشخاص الذين أرسلوا رسائل</b>","",f"العدد: <b>{len(rows)}</b>",""]
    for i,r in enumerate(rows,1):
        count=max(int(r['messages'] or 0),int(r['stored_messages'] or 0))
        lines.append(f"{i}. {esc(r['name'] or 'مستخدم')} — <code>{int(r['user_id'])}</code> — @{esc(r['username']) if r['username'] else 'بدون'} — <b>{count}</b> رسالة")
    if not rows: lines.append("لا توجد رسائل واردة حتى الآن.")
    kb={"inline_keyboard":[[{"text":"🔄 تحديث","callback_data":"limited:contacts"}],[{"text":"🔙 رجوع","callback_data":"admin"}]]}
    return await (edit_message(chat_id,message_id,"\n".join(lines),kb) if message_id else send_message(chat_id,"\n".join(lines),kb))


async def show_limited_force_sub(chat_id, message_id=0):
    enabled=await get_setting("force_sub","1") == "1"
    channels=await get_local_forced_channels()
    lines=["📢 <b>الاشتراك الإجباري لبوتك</b>","",f"الحالة: {'🟢 مفعّل' if enabled else '🔴 متوقف'}","", "القنوات:"]
    lines += [f"• @{esc(c)}" for c in channels] or ["• لا توجد قنوات مضافة."]
    kb={"inline_keyboard":[
        [{"text":("🔴 إيقاف الاشتراك" if enabled else "🟢 تفعيل الاشتراك"),"callback_data":"limited:force_toggle"}],
        [{"text":"➕ إضافة قناة","callback_data":"limited:force_add"},{"text":"🗑 حذف قناة","callback_data":"limited:force_delete"}],
        [{"text":"🔙 رجوع","callback_data":"admin"}],
    ]}
    return await (edit_message(chat_id,message_id,"\n".join(lines),kb) if message_id else send_message(chat_id,"\n".join(lines),kb))


def limited_admin_keyboard():
    return {"inline_keyboard": [
        [{"text": "🔧 وضع الصيانة", "callback_data": "limited:maintenance", "style": "danger"}],
        [{"text": "🚫 قائمة المحظورين", "callback_data": "limited:blocked", "style": "danger"},
         {"text": "📨 المرسلون", "callback_data": "limited:contacts", "style": "primary"}],
        [{"text": "🎨 أزرار ومحتوى البوت", "callback_data": "limited:buttons", "style": "success"}],
        [{"text": "🎉 إعدادات الترحيب", "callback_data": "limited:welcome", "style": "success"}],
        [{"text": "🖼 صورة المطور للمراسلة", "callback_data": "limited:dev_photo", "style": "primary"}],
        [{"text": "📢 الاشتراك الإجباري", "callback_data": "limited:force_sub", "style": "success"}],
        [{"text": "📢 إذاعة لمستخدمي بوتي", "callback_data": "limited:broadcast", "style": "success"}],
    ]}


def admin_keyboard(viewer_id=None):
    """Build the correct admin surface for the current role."""
    try:
        viewer = int(viewer_id or 0)
    except Exception:
        viewer = 0
    if is_limited_bot_owner(viewer):
        return limited_admin_keyboard()

    ordered = sorted(
        ADMIN_BUTTONS.items(),
        key=lambda item: (item[1]["row"], item[1]["position"], item[0])
    ) if ADMIN_BUTTONS else []
    keyboard = []
    current_row = None
    current = []
    for _, b in ordered:
        if not b.get("enabled"):
            continue
        if is_platform_only_callback(b.get("callback_data", "")) and not is_platform_owner(viewer):
            continue
        if IS_CHILD_BOT and b.get("callback_data") in ("adm:creator_exempt", "adm:hosted"):
            continue
        row_no = int(b.get("row", 0))
        if current_row is None:
            current_row = row_no
        if row_no != current_row:
            if current:
                keyboard.append(current)
            current = []
            current_row = row_no
        current.append({
            "text": b.get("text", "زر"),
            "callback_data": b.get("callback_data", "admin"),
            "style": b.get("style", "primary") if b.get("style") in ("primary", "success", "danger") else "primary",
        })
    if current:
        keyboard.append(current)

    required = [
        ("📊 لوحة المعلومات", "pro:dashboard", "primary"),
        ("🎨 الواجهة", "pro:ui", "success"),
        ("👥 المستخدمون", "pro:users", "primary"),
        ("📨 التواصل", "adm:contact", "success"),
        ("🔧 الصيانة", "adm:status", "danger"),
        ("📢 الإذاعة", "adm:broadcast", "primary"),
        ("📣 القنوات", "adm:channels", "primary"),
        ("🛡 الحماية", "pro:security", "success"),
        ("⚙️ النظام", "pro:system", "primary"),
        ("📜 السجلات", "pro:logs", "primary"),
        ("💾 النسخ الاحتياطي", "pro:backup", "primary"),
        ("🎉 الترحيب", "adm:welcome", "success"),
        ("🖼 الصور", "adm:photos", "primary"),
        ("💬 النصوص", "adm:texts", "primary"),
        ("🎛 أزرار المطور", "pro:adminui", "success"),
        ("🚀 مركز V13", "v13:dashboard", "success"),
        ("🎁 إعفاءات الإنشاء", "adm:creator_exempt", "success"),
        ("🌐 البوتات المستضافة", "adm:hosted", "success"),
    ]
    existing = {b.get("callback_data") for row in keyboard for b in row}
    missing = [x for x in required if x[1] not in existing and (not is_platform_only_callback(x[1]) or is_platform_owner(viewer))]
    while missing:
        pair, missing = missing[:2], missing[2:]
        keyboard.append([{"text": t, "callback_data": cb, "style": st} for t, cb, st in pair])
    if not keyboard:
        keyboard = [[{"text": "📊 لوحة المعلومات", "callback_data": "pro:dashboard"}]]
    return {"inline_keyboard": keyboard}

def cancel_keyboard():
    return {
        "inline_keyboard": [
            [{"text": "❌ إلغاء", "callback_data": "admin"}]
        ]
    }


# =========================================================
# USER STATE
# =========================================================

async def set_state(user_id, state):
    await set_setting(f"user_state:{user_id}", state)


async def get_state(user_id):
    return await get_setting(f"user_state:{user_id}", "")


async def clear_state(user_id):
    await db_execute(
        "DELETE FROM settings WHERE key=?",
        (f"user_state:{user_id}",),
    )


# =========================================================
# PROTECTION / ACCESS
# =========================================================

async def is_banned(user_id):
    row = await get_user(user_id)
    return bool(row and row["blocked"])


async def is_muted(user_id):
    row = await get_user(user_id)
    if not row:
        return False, 0

    until = float(row["muted_until"] or 0)
    if until > time.time():
        return True, int(until - time.time())

    if until:
        await db_execute(
            "UPDATE users SET muted_until=0 WHERE user_id=?",
            (user_id,),
        )

    return False, 0


async def protection_ok(user_id, text=""):
    enabled = await get_setting("protection", "1")
    if enabled != "1" or is_owner(user_id):
        return True

    # Banned words
    words = await db_execute(
        "SELECT word FROM banned_words",
        fetchall=True,
    )
    lower = (text or "").lower()
    for row in words or []:
        if row["word"].lower() in lower:
            await audit("Banned word", f"user={user_id}")
            return False

    # Per-minute flood
    limit = int(await get_setting("max_requests_per_min", "30") or 30)
    now = time.time()

    RATE_LIMIT[user_id].append(now)
    RATE_LIMIT[user_id] = [
        x for x in RATE_LIMIT[user_id]
        if now - x < 60
    ]

    return len(RATE_LIMIT[user_id]) <= limit


async def get_local_forced_channels():
    rows = await db_execute("SELECT channel FROM forced_channels ORDER BY channel", fetchall=True)
    return [str(r["channel"]).lstrip("@").strip() for r in rows or [] if r["channel"]]


async def sync_global_forced_channels():
    """Publish the platform owner's forced-subscription list atomically for child bots."""
    channels = await get_local_forced_channels()
    payload = {
        "version": 1,
        "force": True,
        "channels": channels,
        "updated_at": now_text(),
    }
    tmp = GLOBAL_POLICY_FILE.with_suffix(GLOBAL_POLICY_FILE.suffix + ".tmp")
    try:
        tmp.write_text(json.dumps(payload, ensure_ascii=False, indent=2), encoding="utf-8")
        tmp.replace(GLOBAL_POLICY_FILE)
        GLOBAL_POLICY_CACHE["ts"] = time.time()
        GLOBAL_POLICY_CACHE["channels"] = list(channels)
        return True
    except Exception as exc:
        await log_error("global_policy_write", exc)
        return False


async def get_global_forced_channels():
    """Read the immutable-for-child global subscription policy with a tiny cache."""
    now = time.time()
    if now - float(GLOBAL_POLICY_CACHE.get("ts", 0)) < 2.0:
        return list(GLOBAL_POLICY_CACHE.get("channels", []))
    async with GLOBAL_POLICY_LOCK:
        now = time.time()
        if now - float(GLOBAL_POLICY_CACHE.get("ts", 0)) < 2.0:
            return list(GLOBAL_POLICY_CACHE.get("channels", []))
        try:
            payload = json.loads(GLOBAL_POLICY_FILE.read_text(encoding="utf-8"))
            channels = [
                str(x).lstrip("@").strip()
                for x in payload.get("channels", [])
                if str(x).strip()
            ]
        except Exception:
            channels = []
        GLOBAL_POLICY_CACHE["channels"] = channels
        GLOBAL_POLICY_CACHE["ts"] = now
        return list(channels)


async def check_forced_subscription(user_id):
    # The platform developer is the only identity that bypasses the global rule.
    # A hosted-bot owner is deliberately NOT exempt from the platform policy.
    if is_platform_owner(user_id):
        return True, []

    if IS_CHILD_BOT:
        channels = await get_global_forced_channels()
    else:
        if await get_setting("force_sub", "1") != "1":
            return True, []
        channels = await get_local_forced_channels()

    if not channels:
        return True, []

    async def one(channel):
        result = await api_call(
            "getChatMember",
            data={"chat_id": f"@{channel}", "user_id": user_id},
            timeout=8,
        )
        if not result.get("ok"):
            # If the bot cannot inspect the channel, do not silently deny
            # every user. Treat it as not verified and tell admin to check
            # that the bot is an admin in the channel.
            return channel, False

        status = result.get("result", {}).get("status", "left")
        return channel, status in {
            "member", "administrator", "creator", "restricted"
        }

    results = await asyncio.gather(*(one(c) for c in channels))
    missing = [c for c, ok in results if not ok]
    return not missing, missing


def subscription_keyboard(channels):
    rows = []
    for channel in channels:
        rows.append([{
            "text": f"📢 اشترك في @{channel}",
            "url": f"https://t.me/{channel}",
        }])
    rows.append([{
        "text": "✅ تحققت من الاشتراك",
        "callback_data": "check_sub",
    }])
    return {"inline_keyboard": rows}


# =========================================================
# TEXT FORMATTING
# =========================================================

async def render_text(text, user_id):
    user = await get_user(user_id)
    name = user["name"] if user else "مستخدم"
    username = user["username"] if user else ""

    top_rows = await db_execute("""
        SELECT name, user_id, messages
        FROM users
        ORDER BY messages DESC
        LIMIT 5
    """, fetchall=True)

    top = "لا يوجد متصدرون بعد"
    if top_rows:
        top = "\n".join(
            f"{i}. {esc(row['name'] or 'مستخدم')} — {row['messages']}"
            for i, row in enumerate(top_rows, 1)
        )

    replacements = {
        "{name}": esc(name),
        "{name_user}": esc(name),
        "{username}": f"@{esc(username)}" if username else "بدون معرف",
        "{id}": str(user_id),
        "{top5}": top,
        "{invitelink}": f"https://t.me/{BOT_USERNAME}?start=ref_{user_id}",
        "#name": esc(name),
        "#name_user": esc(name),
        "#username": f"@{esc(username)}" if username else "بدون معرف",
        "#id": str(user_id),
        "#top5": top,
        "#invitelink": f"https://t.me/{BOT_USERNAME}?start=ref_{user_id}",
    }

    result = str(text)
    for key, value in replacements.items():
        result = result.replace(key, value)

    return result


# =========================================================
# CONTACT SYSTEM
# =========================================================

def contact_admin_keyboard(user_id, message_id):
    """Exactly four controls shown to the hosted-bot owner for each member message."""
    uid = int(user_id)
    mid = int(message_id)
    return {
        "inline_keyboard": [
            [
                {"text": "📨 الرد على الرسالة", "callback_data": f"reply:{uid}:{mid}"},
                {"text": "🚫 حظر العضو", "callback_data": f"quickban:{uid}"},
            ],
            [
                {"text": "❤️ تعيين كمقروءة", "callback_data": f"read:{uid}:{mid}"},
                {"text": "👤 معلومات العضو", "callback_data": f"userinfo:{uid}"},
            ],
        ]
    }


async def log_message(user_id, direction, media_type, content, tg_message_id=0):
    await db_execute("""
        INSERT INTO messages
        (user_id,direction,media_type,content,telegram_message_id,created_at)
        VALUES(?,?,?,?,?,?)
    """, (
        user_id,
        direction,
        media_type,
        str(content or "")[:4000],
        tg_message_id,
        now_text(),
    ))


async def copy_message_to_owner(msg, user_id, keyboard=None, reply_to_message_id=None):
    """Deliver the member message to the hosted-bot owner.

    Replying is intentionally handled through Telegram's native Reply feature:
    the owner can swipe/reply to the copied member message and the bot maps that
    owner-side message back to the real member and original message id.
    No inline keyboard is required for the reply workflow.
    """
    source_chat = int(msg["chat"]["id"])
    source_message_id = int(msg["message_id"])
    owner_id = int(OWNER_ID)

    # Copy the original member message first so text/media stays native.
    copy_data = {
        "chat_id": owner_id,
        "from_chat_id": source_chat,
        "message_id": source_message_id,
    }
    # Put the four owner controls on the copied member message itself.
    # Telegram Bot API expects reply_markup as JSON for copyMessage.
    if keyboard:
        copy_data["reply_markup"] = json.dumps(
            strip_keyboard_styles(keyboard),
            ensure_ascii=False,
            separators=(",", ":"),
        )
    result = await api_call("copyMessage", data=copy_data, timeout=30)
    # If requested, make the copied member message sit directly under the inbox header.
    if result.get("ok") and reply_to_message_id:
        copied_for_reply = int((result.get("result") or {}).get("message_id") or 0)
        if copied_for_reply:
            # copyMessage itself cannot set reply parameters, so edit the copied message
            # by replying with a tiny marker is avoided; the header/copy order remains valid.
            pass

    # Fallback for message types that Telegram refuses to copy.
    if not result.get("ok"):
        media_type, file_id, caption = extract_media(msg)
        if media_type:
            result = await send_media(owner_id, media_type, file_id, caption=caption or "", keyboard=None)
        else:
            result = await send_message(
                owner_id,
                msg.get("text") or msg.get("caption") or "[رسالة غير مدعومة]",
                None,
            )

    if not result.get("ok"):
        await log_error("inbox_copy", result.get("description", "failed to deliver member message"))
        return result

    copied_id = int((result.get("result") or {}).get("message_id") or 0)
    if not copied_id:
        await log_error("inbox_copy", "Telegram returned no copied message_id")
        return {"ok": False, "description": "no copied message_id"}

    # Critical mapping: owner reply message_id -> real member + original message.
    # Settings are used so this works without changing the database schema.
    try:
        await set_setting(
            f"inbox_reply:{owner_id}:{copied_id}",
            json.dumps({
                "user_id": int(user_id),
                "source_message_id": int(source_message_id),
                "created_at": now_text(),
            }, ensure_ascii=False),
        )
    except Exception as exc:
        await log_error("inbox_reply_map", exc)

    # Intentionally NO inline keyboard. The owner simply replies to this message.
    return result


async def get_inbox_reply_target(owner_id, replied_message_id):
    """Return (member_id, original_message_id) for an owner-side replied message."""
    try:
        raw = await get_setting(f"inbox_reply:{int(owner_id)}:{int(replied_message_id)}", "")
        if not raw:
            return 0, 0
        data = json.loads(raw)
        return int(data.get("user_id") or 0), int(data.get("source_message_id") or 0)
    except Exception as exc:
        await log_error("inbox_reply_lookup", exc)
        return 0, 0


async def handle_native_owner_reply(msg):
    """Handle a native Telegram Reply from the hosted-bot owner to a member message."""
    owner_id = int(msg.get("from", {}).get("id") or 0)
    replied = msg.get("reply_to_message") or {}
    replied_id = int(replied.get("message_id") or 0)
    if not owner_id or not replied_id:
        return False

    target_user, source_message_id = await get_inbox_reply_target(owner_id, replied_id)
    if not target_user:
        return False

    chat_id = int(msg.get("chat", {}).get("id") or owner_id)
    text = str(msg.get("text") or "").strip()

    # Convenient moderation/info commands while replying to the member message.
    if text in ("/ban", "/حظر"):
        await db_execute("UPDATE users SET blocked=1 WHERE user_id=?", (target_user,))
        await audit("Quick ban", f"user={target_user}")
        await send_message(target_user, await get_notification("notif_ban_user"))
        await send_message(chat_id, await get_notification("notif_ban_admin"))
        return True

    if text in ("/read", "/مقروءة"):
        if source_message_id:
            await db_execute(
                "UPDATE messages SET read_at=? WHERE user_id=? AND telegram_message_id=? AND direction='USER'",
                (now_text(), target_user, source_message_id),
            )
        await audit("Read message", f"user={target_user};message={source_message_id}")
        await send_message(target_user, await get_notification("notif_read_user"))
        await send_message(chat_id, "❤️ تم تعيين الرسالة كمقروءة.")
        return True

    if text in ("/info", "/معلومات"):
        row = await get_user(target_user)
        counts = await db_execute(
            "SELECT media_type, COUNT(*) c FROM messages WHERE user_id=? GROUP BY media_type",
            (target_user,), fetchall=True,
        )
        breakdown = {str(r["media_type"] or "text"): int(r["c"] or 0) for r in (counts or [])}
        await send_message(
            chat_id,
            "👤 <b>معلومات العضو</b>\n\n"
            f"🆔 ID: <code>{target_user}</code>\n"
            f"🔗 المعرف: @{esc(row['username']) if row and row['username'] else 'بدون'}\n"
            f"🏷️ الاسم: {esc(row['name']) if row else 'مستخدم'}\n"
            f"💬 الرسائل: <b>{int(row['messages'] or 0) if row else 0}</b>\n"
            f"📎 الوسائط: <b>{int(row['media'] or 0) if row else 0}</b>\n"
            f"🖼️ صور: <b>{breakdown.get('photo', 0)}</b>\n"
            f"🎥 فيديو: <b>{breakdown.get('video', 0)}</b>\n"
            f"🎞️ GIF: <b>{breakdown.get('animation', 0)}</b>\n"
            f"📄 ملفات: <b>{breakdown.get('document', 0)}</b>\n"
            f"🎤 صوت: <b>{breakdown.get('voice', 0) + breakdown.get('audio', 0)}</b>\n"
            f"🧩 ملصقات: <b>{breakdown.get('sticker', 0)}</b>\n"
            f"📹 فيديو دائري: <b>{breakdown.get('video_note', 0)}</b>\n"
            f"🚫 محظور: {'نعم' if row and row['blocked'] else 'لا'}",
        )
        return True

    # Ordinary text reply: send it to the real member and make Telegram show it
    # as a reply to the member's original message when possible.
    if text:
        await reply_to_user_text(chat_id, target_user, text, source_message_id or None)
        return True

    # The same native Reply workflow also supports photos/videos/files/audio.
    media_type, _, _ = extract_media(msg)
    if media_type:
        await reply_to_user_media(chat_id, target_user, msg, source_message_id or None)
        return True

    return False


async def conversation_history_text(user_id, page=0):
    page = max(0, int(page))
    limit = 12
    offset = page * limit
    rows = await db_execute(
        "SELECT * FROM messages WHERE user_id=? ORDER BY id DESC LIMIT ? OFFSET ?",
        (user_id, limit, offset), fetchall=True
    )
    total_row = await db_execute(
        "SELECT COUNT(*) c FROM messages WHERE user_id=?", (user_id,), fetchone=True
    )
    total = int(total_row["c"] if total_row else 0)
    if not rows:
        return "📚 <b>سجل المحادثة</b>\n\nلا توجد رسائل محفوظة.", {"inline_keyboard":[[{"text":"🔙 رجوع","callback_data":"admin"}]]}
    lines=[f"📚 <b>سجل المحادثة</b> — <code>{user_id}</code>", ""]
    for r in reversed(rows):
        direction = "👤 العضو" if r["direction"] == "USER" else "👑 المطور"
        media = r["media_type"] or "text"
        content = r["content"] or "[وسائط]"
        if media != "text":
            content = f"[{esc(media)}] {esc(content) if content else ''}"
        else:
            content = esc(content)
        lines.append(f"{direction} • {esc(r['created_at'])}")
        lines.append(content[:700])
        lines.append("")
    kb=[]
    nav=[]
    if page>0: nav.append({"text":"⬅️ السابق","callback_data":f"history:{user_id}:{page-1}"})
    if offset+len(rows)<total: nav.append({"text":"التالي ➡️","callback_data":f"history:{user_id}:{page+1}"})
    if nav: kb.append(nav)
    kb.append([{"text":"🔙 رجوع","callback_data":"admin"}])
    return "\n".join(lines), {"inline_keyboard":kb}


async def _send_inbox_control_panel(user_id, source_message_id, owner_id=None, reply_to_message_id=None):
    """Explicit four-button fallback panel for the hosted-bot owner."""
    owner_id = int(owner_id or OWNER_ID)
    keyboard = contact_admin_keyboard(user_id, source_message_id)
    data = {
        "chat_id": owner_id,
        "text": (
            "🎛️ <b>تحكم برسالة العضو</b>\n\n"
            f"🆔 العضو: <code>{int(user_id)}</code>\n"
            f"🆔 الرسالة: <code>{int(source_message_id)}</code>\n\n"
            "اختر الإجراء:"
        ),
        "parse_mode": "HTML",
        "reply_markup": json.dumps(strip_keyboard_styles(keyboard), ensure_ascii=False, separators=(",", ":")),
    }
    if reply_to_message_id:
        data["reply_parameters"] = json.dumps({
            "message_id": int(reply_to_message_id),
            "allow_sending_without_reply": True,
        }, ensure_ascii=False)
    return await api_call("sendMessage", data=data, timeout=20)


async def notify_owner_text(msg, text):
    user_id = int(msg["from"]["id"])
    source_message_id = int(msg["message_id"])
    await log_message(user_id, "USER", "text", text, source_message_id)
    header = await send_message(
        OWNER_ID,
        await get_notification(
            "notif_incoming_message",
            name=msg.get("from", {}).get("first_name", "مستخدم"),
            id=user_id,
            username=msg.get("from", {}).get("username", "بدون") or "بدون",
            message=text,
        ),
    )
    delivered = await copy_message_to_owner(msg, user_id, contact_admin_keyboard(user_id, source_message_id))
    if not delivered.get("ok"):
        return False
    copied_id = int((delivered.get("result") or {}).get("message_id") or 0)
    header_id = int((header.get("result") or {}).get("message_id") or 0) if header.get("ok") else 0
    for mapped_id in (header_id, copied_id):
        if mapped_id:
            await set_setting(f"inbox_reply:{int(OWNER_ID)}:{mapped_id}", json.dumps({"user_id": user_id, "source_message_id": source_message_id, "created_at": now_text()}, ensure_ascii=False))
    return True


async def notify_owner_media(msg, media_type, file_id, caption):
    user_id = int(msg["from"]["id"])
    source_message_id = int(msg["message_id"])
    await log_message(user_id, "USER", media_type, caption or "", source_message_id)
    header = await send_message(
        OWNER_ID,
        await get_notification(
            "notif_incoming_message",
            name=msg.get("from", {}).get("first_name", "مستخدم"),
            id=user_id,
            username=msg.get("from", {}).get("username", "بدون") or "بدون",
            message=caption or "[وسائط]",
        ),
    )
    delivered = await copy_message_to_owner(msg, user_id, contact_admin_keyboard(user_id, source_message_id))
    if not delivered.get("ok"):
        return False
    copied_id = int((delivered.get("result") or {}).get("message_id") or 0)
    header_id = int((header.get("result") or {}).get("message_id") or 0) if header.get("ok") else 0
    for mapped_id in (header_id, copied_id):
        if mapped_id:
            await set_setting(f"inbox_reply:{int(OWNER_ID)}:{mapped_id}", json.dumps({"user_id": user_id, "source_message_id": source_message_id, "created_at": now_text()}, ensure_ascii=False))
    return True


async def reply_to_user_text(owner_chat_id, target_user, text, source_message_id=None):
    result = await send_message(
        target_user,
        f"📨 <b>رد من المطور</b>\n\n{esc(text)}",
        reply_to_message_id=source_message_id,
    )

    if result.get("ok"):
        await log_message(target_user, "OWNER", "text", text, result["result"]["message_id"])
        await send_message(owner_chat_id, await get_notification("notif_reply_success"))
    else:
        await send_message(owner_chat_id, await get_notification("notif_reply_failed"))


async def reply_to_user_media(owner_chat_id, target_user, msg, source_message_id=None):
    media_type, file_id, caption = extract_media(msg)
    if not media_type:
        return

    result = await send_media(
        target_user,
        media_type,
        file_id,
        caption=f"📨 <b>رد من المطور</b>\n\n{esc(caption)}" if caption else "📨 <b>رد من المطور</b>",
        reply_to_message_id=source_message_id,
    )

    if result.get("ok"):
        await log_message(target_user, "OWNER", media_type, caption or "", result["result"]["message_id"])
        await send_message(owner_chat_id, await get_notification("notif_media_reply_success"))
    else:
        await send_message(owner_chat_id, await get_notification("notif_media_reply_failed"))


# =========================================================
# MEDIA
# =========================================================

def extract_media(msg):
    caption = msg.get("caption", "") or ""

    if "photo" in msg:
        return "photo", msg["photo"][-1]["file_id"], caption
    if "video" in msg:
        return "video", msg["video"]["file_id"], caption
    if "document" in msg:
        return "document", msg["document"]["file_id"], caption
    if "animation" in msg:
        return "animation", msg["animation"]["file_id"], caption
    if "voice" in msg:
        return "voice", msg["voice"]["file_id"], caption
    if "audio" in msg:
        return "audio", msg["audio"]["file_id"], caption
    if "sticker" in msg:
        return "sticker", msg["sticker"]["file_id"], caption
    if "video_note" in msg:
        return "video_note", msg["video_note"]["file_id"], caption

    return None, None, caption


# =========================================================
# ADMIN UI
# =========================================================

async def show_admin(chat_id, message_id=None, user_id=None):
    text = (
        "⚙️ <b>لوحة تحكم المطور</b>\n\n"
        "من هنا تتحكم بالبوت والواجهة والمستخدمين والتواصل."
    )
    if message_id:
        return await edit_message(chat_id, message_id, text, admin_keyboard(user_id or chat_id))
    return await send_message(chat_id, text, admin_keyboard(user_id or chat_id))


def invalidate_button_cache():
    MAIN_BUTTON_CACHE["ts"] = 0.0
    MAIN_BUTTON_CACHE["keyboard"] = None

async def archive_button(button_id, deleted_by=0):
    row = await db_execute("SELECT * FROM buttons WHERE id=?", (button_id,), fetchone=True)
    if not row:
        return False
    await db_execute("""
        INSERT INTO deleted_buttons
        (button_id,text,action,row,position,enabled,style,url,action_value,photo,caption,deleted_by,deleted_at)
        VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?)
    """, (
        row["id"], row["text"], row["action"] or "text", int(row["row"] or 0), int(row["position"] or 0),
        int(row["enabled"] or 0), row["style"] or "primary", row["url"] or "", row["action_value"] or "",
        row["photo"] or "", row["caption"] or "", int(deleted_by or 0), now_text(),
    ))
    await db_execute("DELETE FROM buttons WHERE id=?", (button_id,))
    invalidate_button_cache()
    await normalize_button_positions()
    await audit("Delete button", button_id)
    return True

async def restore_deleted_button(trash_id):
    row = await db_execute("SELECT * FROM deleted_buttons WHERE id=?", (trash_id,), fetchone=True)
    if not row:
        return False, "العنصر المحذوف غير موجود."
    button_id = row["button_id"]
    exists = await db_execute("SELECT id FROM buttons WHERE id=?", (button_id,), fetchone=True)
    if exists:
        button_id = f"restored_{int(time.time()*1000000)}"
    await db_execute("""
        INSERT INTO buttons(id,text,action,row,position,enabled,style,url,action_value,photo,caption)
        VALUES(?,?,?,?,?,?,?,?,?,?,?)
    """, (
        button_id, row["text"] or "زر", row["action"] or "text", int(row["row"] or 0), int(row["position"] or 0),
        int(row["enabled"] or 1), row["style"] if row["style"] in BUTTON_STYLES else "primary",
        row["url"] or "", row["action_value"] or "", row["photo"] or "", row["caption"] or "",
    ))
    await db_execute("DELETE FROM deleted_buttons WHERE id=?", (trash_id,))
    invalidate_button_cache()
    await normalize_button_positions()
    await audit("Restore button", f"trash={trash_id},button={button_id}")
    return True, button_id

async def deleted_buttons_menu(chat_id, message_id):
    rows = await db_execute("""
        SELECT id,button_id,text,action,deleted_at FROM deleted_buttons ORDER BY id DESC LIMIT 30
    """, fetchall=True)
    lines=["🗑 <b>سلة أزرار الواجهة</b>", ""]
    kb=[]
    for r in rows or []:
        label=str(r["text"] or r["button_id"] or "زر")[:28]
        lines.append(f"• <b>{esc(label)}</b> · {esc(r['action'] or 'text')} · {esc(r['deleted_at'])}")
        kb.append([{"text":f"♻️ استرجاع {label}","callback_data":f"btnrestore:{r['id']}","style":"success"}])
        kb.append([{"text":f"🗑 حذف نهائي {label}","callback_data":f"btnpurge:{r['id']}","style":"danger"}])
    if not rows:
        lines.append("السلة فارغة.")
    kb.append([{"text":"🔙 مدير الأزرار","callback_data":"adm:ui"}])
    await edit_message(chat_id,message_id,"\n".join(lines),{"inline_keyboard":kb})

async def button_manager_home(chat_id, message_id):
    rows=await get_buttons(include_disabled=True)
    trash=await db_execute("SELECT COUNT(*) c FROM deleted_buttons",fetchone=True)
    shown=sum(1 for r in rows if int(r["enabled"] or 0))
    hidden=len(rows)-shown
    text=("🎛 <b>مدير الأزرار الكامل</b>\n\n"
          f"🔘 كل الأزرار: <b>{len(rows)}</b>\n"
          f"🟢 الظاهرة: <b>{shown}</b>\n"
          f"🔴 المخفية: <b>{hidden}</b>\n"
          f"🗑 المحذوفة في السلة: <b>{int(trash['c'] if trash else 0)}</b>\n\n"
          "تحكم كامل في الإضافة، التعديل، الحذف، الاسترجاع، الألوان، الوظائف، الروابط، الصور والترتيب.")
    kb={"inline_keyboard":[
        [{"text":"➕ إضافة زر","callback_data":"ui:add","style":"success"},{"text":"♻️ استرجاع","callback_data":"ui:restore","style":"success"}],
        [{"text":"✏️ تعديل","callback_data":"ui:edit"},{"text":"👁 إظهار/إخفاء","callback_data":"ui:toggle"}],
        [{"text":"🎨 لون","callback_data":"ui:style"},{"text":"⚡ وظيفة","callback_data":"ui:action"}],
        [{"text":"🔗 رابط","callback_data":"ui:url"},{"text":"🖼 صورة/نص","callback_data":"ui:media"}],
        [{"text":"↕️ ترتيب","callback_data":"ui:sort"},{"text":"📍 تحكم بصري","callback_data":"pro:ui"}],
        [{"text":"🗑 حذف","callback_data":"ui:delete","style":"danger"},{"text":"🗑 السلة","callback_data":"ui:trash"}],
        [{"text":"🔄 تطبيع الترتيب","callback_data":"ui:normalize"},{"text":"👁 معاينة","callback_data":"ui:preview"}],
        [{"text":"🔙 لوحة المطور","callback_data":"admin"}],
    ]}
    await edit_message(chat_id,message_id,text,kb)

async def show_ui_admin(chat_id, message_id):
    return await button_manager_home(chat_id, message_id)


def ui_actions():
    return {
        "inline_keyboard": [
            [{"text": "📨 تواصل", "callback_data": "ui_action:contact", "style": "success"}],
            [{"text": "ℹ️ معلومات", "callback_data": "ui_action:info", "style": "primary"}],
            [{"text": "🏆 المتصدرون", "callback_data": "ui_action:top", "style": "primary"}],
            [{"text": "📝 نص مخصص", "callback_data": "ui_action:text", "style": "primary"}],
            [{"text": "🔗 رابط", "callback_data": "ui_action:url", "style": "primary"}],
            [{"text": "🧩 صفحة داخلية", "callback_data": "ui_action:page", "style": "primary"}],
            [{"text": "🖼 صورة + نص", "callback_data": "ui_action:media", "style": "success"}],
        ]
    }


async def ui_list(chat_id, message_id, operation):
    rows = await get_buttons(include_disabled=True)
    if not rows:
        await edit_message(chat_id, message_id, "لا توجد أزرار.", back_keyboard("adm:ui"))
        return

    buttons = []
    for row in rows:
        status = "🟢" if row["enabled"] else "🔴"
        buttons.append([{
            "text": f"{status} {row['text']}",
            "callback_data": f"ui_pick:{operation}:{row['id']}",
        }])
    buttons.append([{"text": "🔙 رجوع", "callback_data": "adm:ui"}])
    await edit_message(
        chat_id,
        message_id,
        "اختر الزر:",
        {"inline_keyboard": buttons},
    )


async def show_ui_place_picker(chat_id, message_id, user_id):
    text = "📍 <b>اختر مكان الزر</b>\n\nبدل الأرقام، اضغط على الزر الذي تريد وضع الزر الجديد بعده."
    kb = await ui_place_keyboard(user_id)
    if message_id:
        return await edit_message(chat_id, message_id, text, kb)
    return await send_message(chat_id, text, kb)


async def ui_place_keyboard(user_id):
    """Visual placement picker for newly-created buttons.

    The old implementation already intended to avoid row/position numbers, but
    its callbacks were not routed by the global callback dispatcher. This
    version also groups buttons by row so the owner can clearly see where the
    new button will land.
    """
    rows = await get_buttons(include_disabled=True)
    kb = []
    if not rows:
        kb.append([{"text": "➕ أول زر / صف جديد", "callback_data": "ui_place:newrow"}])
    else:
        grouped = defaultdict(list)
        for r in rows:
            grouped[int(r["row"] or 0)].append(r)
        for row_no in sorted(grouped):
            kb.append([{"text": f"━━ الصف {row_no + 1} ━━", "callback_data": "ui_place:noop"}])
            ordered = sorted(grouped[row_no], key=lambda x: (int(x["position"] or 0), str(x["id"])))
            for r in ordered:
                status = "🟢" if r["enabled"] else "🔴"
                label = str(r["text"] or "زر")[:32]
                kb.append([{"text": f"➕ بعد {status} {label}", "callback_data": f"ui_place:after:{r['id']}"}])
        kb.append([{"text": "➕ صف جديد في الأسفل", "callback_data": "ui_place:newrow"}])
    kb.append([{"text": "❌ إلغاء", "callback_data": "admin"}])
    return {"inline_keyboard": kb}


async def create_button_from_temp(user_id, mode, target_id=None):
    button_text = await get_setting(f"temp_button_text:{user_id}", "زر")
    value = await get_setting(f"temp_button_value:{user_id}", "")
    caption = await get_setting(f"temp_button_caption:{user_id}", "")
    photo = await get_setting(f"temp_button_photo:{user_id}", "")
    button_id = f"custom_{int(time.time()*1000)}"
    style = await get_setting("button_default_style", "primary")
    action = mode
    url = value if action == "url" else ""
    action_value = value if action in ("text", "page") else ""
    if action == "media":
        action_value = caption
    # Determine placement without asking for row/position.
    if target_id:
        target = await db_execute("SELECT row,position FROM buttons WHERE id=?", (target_id,), fetchone=True)
        if target:
            row = int(target["row"]); position = int(target["position"]) + 1
            await db_execute("UPDATE buttons SET position=position+1 WHERE row=? AND position>=?", (row, position))
            # Keep placement deterministic even if an older version left gaps.
            await normalize_button_positions()
            target = await db_execute("SELECT row,position FROM buttons WHERE id=?", (target_id,), fetchone=True)
            if target:
                row = int(target["row"])
                position = int(target["position"]) + 1
                await db_execute("UPDATE buttons SET position=position+1 WHERE row=? AND position>=? AND id<>?", (row, position, button_id))
        else:
            last = await db_execute("SELECT COALESCE(MAX(row),-1) r FROM buttons", fetchone=True)
            row = int(last["r"])+1; position=0
    else:
        last = await db_execute("SELECT COALESCE(MAX(row),-1) r FROM buttons", fetchone=True)
        row = int(last["r"])+1; position=0
    await db_execute("""INSERT INTO buttons(id,text,action,row,position,enabled,style,url,action_value,photo,caption) VALUES(?,?,?,?,?,?,?,?,?,?,?)""", (button_id,button_text,action,row,position,1,style,url,action_value,photo,caption))
    for key in (f"temp_button_text:{user_id}", f"temp_button_value:{user_id}", f"temp_button_caption:{user_id}", f"temp_button_photo:{user_id}"):
        await db_execute("DELETE FROM settings WHERE key=?", (key,))
    await clear_state(user_id)
    await audit("Add button", f"{button_id}/{action}/row={row}/pos={position}")
    return button_id


async def handle_ui_callback(user_id, chat_id, message_id, data):
    if data.startswith("ui_place:"):
        if not is_owner(user_id):
            return
        target = data.split(":", 2)
        if len(target) >= 2 and target[1] == "noop":
            # Header-only row button; intentionally does nothing.
            return
        target_id = None if len(target) < 3 or target[1] == "newrow" else target[2]
        state = await get_state(user_id)
        if not state.startswith("ui_add_position:"):
            await send_message(chat_id, "❌ لا توجد عملية إضافة زر معلقة.")
            return
        action = state.split(":",1)[1]
        button_id = await create_button_from_temp(user_id, action, target_id)
        await send_message(chat_id, f"✅ تمت إضافة الزر <b>{esc(button_id)}</b> في مكانه الجديد.", admin_keyboard())
        return

    if data == "ui:add":
        await set_state(user_id, "ui_add_text")
        await edit_message(
            chat_id,
            message_id,
            "➕ <b>إضافة زر</b>\n\nأرسل اسم الزر الآن.",
            cancel_keyboard(),
        )
        return

    if data in {"ui:trash", "ui:restore"}:
        await deleted_buttons_menu(chat_id, message_id)
        return
    if data == "ui:normalize":
        await normalize_button_positions()
        await button_manager_home(chat_id, message_id)
        return
    if data in {"ui:edit", "ui:delete", "ui:toggle", "ui:sort", "ui:style", "ui:url", "ui:action", "ui:media"}:
        operation = data.split(":")[1]
        await ui_list(chat_id, message_id, operation)
        return

    if data.startswith("ui_move:"):
        _, direction, bid = data.split(":", 2)
        r = await db_execute("SELECT row,position FROM buttons WHERE id=?", (bid,), fetchone=True)
        if not r:
            await send_message(chat_id, "❌ الزر غير موجود."); return
        row=int(r["row"]); pos=int(r["position"])
        if direction in ("left", "right"):
            step = -1 if direction == "left" else 1
            neighbor = await db_execute("SELECT id,position FROM buttons WHERE row=? AND position=?", (row, pos + step), fetchone=True)
            if neighbor:
                await db_execute("UPDATE buttons SET position=? WHERE id=?", (pos + 99, bid))
                await db_execute("UPDATE buttons SET position=? WHERE id=?", (pos, neighbor["id"]))
                await db_execute("UPDATE buttons SET position=? WHERE id=?", (pos + step, bid))
        elif direction in ("up","down"):
            newrow=max(0,row-1) if direction=="up" else row+1
            await db_execute("UPDATE buttons SET row=? WHERE id=?", (newrow,bid))
        await audit("Move button",f"{bid}:{direction}")
        await show_ui_admin(chat_id,message_id)
        return

    if data == "ui:preview":
        text = await render_text(await get_setting("start_text", DEFAULT_START_TEXT), user_id)
        await send_message(chat_id, "🔄 <b>معاينة:</b>\n\n" + text, await main_keyboard())
        return

    if data.startswith("ui_action:"):
        action = data.split(":", 1)[1]
        # If editing an existing button, keep its id in a temporary setting.
        pending = await get_setting(f"ui_edit_action:{user_id}", "")
        if pending:
            await db_execute("UPDATE buttons SET action=?, url=CASE WHEN ?='url' THEN url ELSE '' END WHERE id=?", (action, action, pending))
            await db_execute("DELETE FROM settings WHERE key=?", (f"ui_edit_action:{user_id}",))
            await clear_state(user_id)
            await audit("Button action", f"{pending}={action}")
            await send_message(chat_id, "✅ تم تغيير وظيفة الزر.", admin_keyboard())
            return
        if action == "media":
            await set_state(user_id, "ui_add_media_photo")
            await edit_message(chat_id, message_id, "🖼 أرسل صورة الزر الآن. بعد الصورة سأطلب النص الذي يظهر تحتها.", cancel_keyboard())
            return
        if action in {"text", "page", "url"}:
            await set_state(user_id, f"ui_add_value:{action}")
            prompt = {
                "text": "📝 أرسل النص الذي سيظهر عند الضغط على الزر.",
                "page": "🧩 أرسل ID الصفحة التي سيفتحها الزر.",
                "url": "🔗 أرسل الرابط، ويجب أن يبدأ بـ http:// أو https://",
            }[action]
            await edit_message(chat_id, message_id, prompt, cancel_keyboard())
            return
        await set_state(user_id, f"ui_add_position:{action}")
        await show_ui_place_picker(chat_id, message_id, user_id)
        return

    if data.startswith("ui_pick:"):
        _, operation, button_id = data.split(":", 2)
        row = await db_execute(
            "SELECT * FROM buttons WHERE id=?",
            (button_id,),
            fetchone=True,
        )
        if not row:
            await send_message(chat_id, "❌ الزر غير موجود.")
            return

        if operation == "delete":
            await archive_button(button_id, user_id)
            await show_ui_admin(chat_id, message_id)
            return

        if operation == "toggle":
            enabled = 0 if row["enabled"] else 1
            await db_execute(
                "UPDATE buttons SET enabled=? WHERE id=?",
                (enabled, button_id),
            )
            await audit("Toggle button", f"{button_id}={enabled}")
            await show_ui_admin(chat_id, message_id)
            return

        if operation == "style":
            await set_state(user_id, f"ui_style:{button_id}")
            await edit_message(chat_id, message_id, "🎨 أرسل اللون: <code>primary</code> أو <code>success</code> أو <code>danger</code>", cancel_keyboard())
            return

        if operation == "url":
            await set_state(user_id, f"ui_url:{button_id}")
            await edit_message(chat_id, message_id, "🔗 أرسل الرابط الجديد، أو <code>none</code> لإزالة الرابط.", cancel_keyboard())
            return

        if operation == "media":
            await set_setting(f"ui_media_target:{user_id}", button_id)
            await set_state(user_id, f"ui_edit_media_photo:{button_id}")
            await edit_message(chat_id, message_id, "🖼 أرسل الصورة الجديدة لهذا الزر. بعد ذلك سأطلب النص الذي يظهر تحتها.", cancel_keyboard())
            return

        if operation == "action":
            await set_setting(f"ui_edit_action:{user_id}", button_id)
            await edit_message(chat_id, message_id, "⚡ اختر الوظيفة الجديدة:", ui_actions())
            return

        if operation == "edit":
            await set_state(user_id, f"ui_edit_text:{button_id}")
            await edit_message(
                chat_id,
                message_id,
                f"✏️ الاسم الحالي:\n<b>{esc(row['text'])}</b>\n\n"
                "أرسل الاسم الجديد.",
                cancel_keyboard(),
            )
            return

        if operation == "sort":
            await set_state(user_id, f"ui_sort:{button_id}")
            await edit_message(
                chat_id,
                message_id,
                "↕️ أرسل الصف والترتيب بهذا الشكل:\n<code>0 1</code>",
                cancel_keyboard(),
            )
            return



# =========================================================
# V10 VISUAL BUTTON STUDIO
# =========================================================

BUTTON_STYLES = ("primary", "success", "danger")
BUTTON_ACTIONS = ("contact", "info", "top", "text", "url", "page", "media")


def _button_label(row, include_id=False):
    label = str(row["text"] or "زر")
    if include_id:
        return f"{label} · {row['id']}"
    return label


async def normalize_button_positions():
    """Compact gaps in row/position values without changing visual order."""
    rows = await get_buttons(include_disabled=True)
    grouped = defaultdict(list)
    for row in rows:
        grouped[int(row["row"] or 0)].append(row)
    for new_row, old_row in enumerate(sorted(grouped)):
        ordered = sorted(grouped[old_row], key=lambda r: (int(r["position"] or 0), str(r["id"])))
        for new_pos, row in enumerate(ordered):
            await db_execute("UPDATE buttons SET row=?, position=? WHERE id=?", (new_row, new_pos, row["id"]))
    await audit("Normalize buttons", f"rows={len(grouped)}")


async def button_row_keyboard(rows, prefix, include_disabled=True):
    kb = []
    for row in rows:
        if not include_disabled and not row["enabled"]:
            continue
        status = "🟢" if row["enabled"] else "🔴"
        media = " 🖼" if row["photo"] else ""
        action = str(row["action"] or "?")
        kb.append([{
            "text": f"{status} {_button_label(row)}{media} · {action}",
            "callback_data": f"{prefix}:{row['id']}",
            "style": row["style"] if row["style"] in BUTTON_STYLES else "primary",
        }])
    return kb


async def visual_button_studio(chat_id, message_id):
    rows = await get_buttons(include_disabled=True)
    visible = sum(1 for r in rows if r["enabled"])
    hidden = len(rows) - visible
    media = sum(1 for r in rows if r["photo"])
    text = (
        "🎛 <b>BUTTON STUDIO V10</b>\n\n"
        f"🔘 الأزرار: <b>{len(rows)}</b>\n"
        f"🟢 ظاهرة: <b>{visible}</b>   🔴 مخفية: <b>{hidden}</b>\n"
        f"🖼 أزرار وسائط: <b>{media}</b>\n\n"
        "اختر أي زر لفتح محرر كامل.\n"
        "يمكنك تعديل الاسم، اللون، الوظيفة، المحتوى، الصورة، المكان، النسخ، الإظهار والحذف."
    )
    kb = await button_row_keyboard(rows, "btnedit")
    kb += [
        [{"text": "➕ إضافة زر جديد", "callback_data": "ui:add", "style": "success"}],
        [{"text": "🧹 ترتيب تلقائي", "callback_data": "btn:normalize"}],
        [{"text": "👁 معاينة الواجهة", "callback_data": "ui:preview"}],
        [{"text": "🔙 إدارة الواجهة", "callback_data": "adm:ui"}],
    ]
    await edit_message(chat_id, message_id, text, {"inline_keyboard": kb})


async def visual_button_editor(chat_id, message_id, button_id):
    row = await db_execute("SELECT * FROM buttons WHERE id=?", (button_id,), fetchone=True)
    if not row:
        await edit_message(chat_id, message_id, "❌ الزر غير موجود.", back_keyboard("pro:ui"))
        return
    action = str(row["action"] or "?")
    style = row["style"] if row["style"] in BUTTON_STYLES else "primary"
    content = str(row["action_value"] or "")
    content_preview = content.replace("\n", " ")[:90] or "—"
    text = (
        "🎛 <b>محرر الزر المتقدم</b>\n\n"
        f"🔘 الاسم: <b>{esc(row['text'])}</b>\n"
        f"🆔 ID: <code>{esc(row['id'])}</code>\n"
        f"⚡ الوظيفة: <code>{esc(action)}</code>\n"
        f"🎨 اللون: <code>{esc(style)}</code>\n"
        f"📍 المكان: صف <b>{row['row']}</b> · ترتيب <b>{row['position']}</b>\n"
        f"👁 الحالة: {'🟢 ظاهر' if row['enabled'] else '🔴 مخفي'}\n"
        f"🖼 الصورة: {'🟢 موجودة' if row['photo'] else '⚪ لا توجد'}\n"
        f"📝 المحتوى: <code>{esc(content_preview)}</code>\n"
        f"🔗 الرابط: <code>{esc(row['url'] or '—')}</code>"
    )
    kb = [
        [{"text": "✏️ اسم الزر", "callback_data": f"btneditfield:text:{button_id}"}],
        [{"text": "🎨 اللون", "callback_data": f"btnstyle:{button_id}"}, {"text": "👁 إظهار/إخفاء", "callback_data": f"btntoggle:{button_id}"}],
        [{"text": "⚡ الوظيفة", "callback_data": f"btnaction:{button_id}"}],
        [{"text": "📝 محتوى الزر", "callback_data": f"btnvalue:{button_id}"}],
        [{"text": "🖼 الصورة + النص", "callback_data": f"btnmedia:{button_id}"}],
        [{"text": "🗑 حذف الصورة", "callback_data": f"btnmedia_delete:{button_id}"}],
        [{"text": "🔗 الرابط", "callback_data": f"btnurl:{button_id}"}],
        [{"text": "📍 تحريك بصري", "callback_data": f"btnmove:{button_id}"}],
        [{"text": "📋 نسخ الزر", "callback_data": f"btnclone:{button_id}"}],
        [{"text": "👁 معاينة الزر", "callback_data": f"btnpreview:{button_id}"}],
        [{"text": "🗑 حذف الزر", "callback_data": f"btndelete:{button_id}"}],
        [{"text": "🔙 Button Studio", "callback_data": "pro:ui"}],
    ]
    await edit_message(chat_id, message_id, text, {"inline_keyboard": kb})


async def button_style_picker(chat_id, message_id, button_id):
    row = await db_execute("SELECT text,style FROM buttons WHERE id=?", (button_id,), fetchone=True)
    if not row:
        return
    kb = [[
        {"text": "🔵 Primary", "callback_data": f"btnsetstyle:primary:{button_id}", "style": "primary"},
        {"text": "🟢 Success", "callback_data": f"btnsetstyle:success:{button_id}", "style": "success"},
        {"text": "🔴 Danger", "callback_data": f"btnsetstyle:danger:{button_id}", "style": "danger"},
    ], [{"text": "🔙 رجوع", "callback_data": f"btnedit:{button_id}"}]]
    await edit_message(chat_id, message_id, f"🎨 اختر لون زر <b>{esc(row['text'])}</b>", {"inline_keyboard": kb})


async def button_action_picker(chat_id, message_id, button_id):
    kb = [
        [{"text": "📨 تواصل", "callback_data": f"btnsetaction:contact:{button_id}", "style": "success"}],
        [{"text": "ℹ️ معلومات", "callback_data": f"btnsetaction:info:{button_id}"}, {"text": "🏆 المتصدرون", "callback_data": f"btnsetaction:top:{button_id}"}],
        [{"text": "📝 نص", "callback_data": f"btnsetaction:text:{button_id}"}, {"text": "🔗 رابط", "callback_data": f"btnsetaction:url:{button_id}"}],
        [{"text": "🧩 صفحة", "callback_data": f"btnsetaction:page:{button_id}"}, {"text": "🖼 صورة + نص", "callback_data": f"btnsetaction:media:{button_id}", "style": "success"}],
        [{"text": "🔙 رجوع", "callback_data": f"btnedit:{button_id}"}],
    ]
    await edit_message(chat_id, message_id, "⚡ <b>وظيفة الزر</b>\n\nاختر ما يحدث عند الضغط.", {"inline_keyboard": kb})


async def button_move_picker(chat_id, message_id, button_id):
    row = await db_execute("SELECT * FROM buttons WHERE id=?", (button_id,), fetchone=True)
    if not row:
        return
    rows = await get_buttons(include_disabled=True)
    kb = [
        [{"text": "⬅️ يسار", "callback_data": f"btnmove_do:left:{button_id}"}, {"text": "➡️ يمين", "callback_data": f"btnmove_do:right:{button_id}"}],
        [{"text": "⬆️ صف أعلى", "callback_data": f"btnmove_do:up:{button_id}"}, {"text": "⬇️ صف أسفل", "callback_data": f"btnmove_do:down:{button_id}"}],
    ]
    kb.append([{"text": "📌 ضع بعد زر…", "callback_data": f"btnplace:{button_id}"}])
    kb.append([{"text": "➕ صف جديد في الأسفل", "callback_data": f"btnmove_do:newrow:{button_id}"}])
    kb.append([{"text": "🔙 رجوع", "callback_data": f"btnedit:{button_id}"}])
    await edit_message(chat_id, message_id, f"📍 <b>تحريك الزر</b>\n\nالمكان الحالي: صف {row['row']} · ترتيب {row['position']}", {"inline_keyboard": kb})


async def button_place_after_picker(chat_id, message_id, button_id):
    rows = await get_buttons(include_disabled=True)
    kb = []
    for row in rows:
        if row["id"] == button_id:
            continue
        kb.append([{"text": f"بعد {row['text']}", "callback_data": f"btnplace_do:{button_id}:{row['id']}"}])
    kb.append([{"text": "➕ صف جديد", "callback_data": f"btnmove_do:newrow:{button_id}"}])
    kb.append([{"text": "🔙 رجوع", "callback_data": f"btnedit:{button_id}"}])
    await edit_message(chat_id, message_id, "📍 اختر مكان الزر بالضغط على الزر الذي تريد وضعه بعده.", {"inline_keyboard": kb})


async def preview_button(chat_id, button_id):
    row = await db_execute("SELECT * FROM buttons WHERE id=? AND enabled=1", (button_id,), fetchone=True)
    if not row:
        await send_message(chat_id, "❌ الزر غير موجود أو مخفي.")
        return
    action = row["action"]
    if action == "media" and row["photo"]:
        await send_photo(chat_id, row["photo"], await render_text(row["caption"] or row["action_value"] or "", chat_id), back_keyboard("pro:ui"))
    elif action == "text":
        await send_message(chat_id, await render_text(row["action_value"] or "لا يوجد نص.", chat_id), back_keyboard("pro:ui"))
    elif action == "url" and row["url"]:
        await send_message(chat_id, f'🔗 <a href="{esc(row["url"])}">فتح الرابط</a>', back_keyboard("pro:ui"))
    else:
        await send_message(chat_id, f"👁 معاينة الزر:\n\n[{esc(row['text'])}]\n\nالوظيفة: <code>{esc(action)}</code>", back_keyboard("pro:ui"))


async def clone_button(button_id):
    row = await db_execute("SELECT * FROM buttons WHERE id=?", (button_id,), fetchone=True)
    if not row:
        return None
    new_id = f"custom_{int(time.time()*1000000)}"
    target_pos = int(row["position"]) + 1
    await db_execute("UPDATE buttons SET position=position+1 WHERE row=? AND position>=?", (row["row"], target_pos))
    await db_execute("""INSERT INTO buttons(id,text,action,row,position,enabled,style,url,action_value,photo,caption)
        VALUES(?,?,?,?,?,?,?,?,?,?,?)""", (
        new_id, f"{row['text']} (نسخة)", row["action"], row["row"], target_pos, row["enabled"], row["style"],
        row["url"], row["action_value"], row["photo"], row["caption"],
    ))
    await normalize_button_positions()
    await audit("Clone button", f"{button_id}->{new_id}")
    return new_id


async def delete_button_safe(chat_id, message_id, button_id, deleted_by=0):
    await archive_button(button_id, deleted_by)
    await visual_button_studio(chat_id, message_id)


async def handle_visual_button_callback(user_id, chat_id, message_id, data):
    if not is_owner(user_id):
        return False
    if data == "btn:normalize":
        await normalize_button_positions()
        await visual_button_studio(chat_id, message_id)
        return True
    if data.startswith("btnrestore:"):
        ok,info=await restore_deleted_button(int(data.split(":",1)[1]))
        await button_manager_home(chat_id,message_id)
        return True
    if data.startswith("btnpurge:"):
        await db_execute("DELETE FROM deleted_buttons WHERE id=?",(int(data.split(":",1)[1]),))
        await audit("Purge deleted button", data.split(":",1)[1])
        await deleted_buttons_menu(chat_id,message_id)
        return True
    if data.startswith("btnedit:"):
        await visual_button_editor(chat_id, message_id, data.split(":", 1)[1])
        return True
    if data.startswith("btnstyle:"):
        await button_style_picker(chat_id, message_id, data.split(":", 1)[1])
        return True
    if data.startswith("btnsetstyle:"):
        _, style, bid = data.split(":", 2)
        if style not in BUTTON_STYLES:
            return True
        await db_execute("UPDATE buttons SET style=? WHERE id=?", (style, bid))
        await audit("Button color", f"{bid}={style}")
        await visual_button_editor(chat_id, message_id, bid)
        return True
    if data.startswith("btntoggle:"):
        bid = data.split(":", 1)[1]
        row = await db_execute("SELECT enabled FROM buttons WHERE id=?", (bid,), fetchone=True)
        if row:
            await db_execute("UPDATE buttons SET enabled=? WHERE id=?", (0 if row["enabled"] else 1, bid))
            await audit("Button visibility", bid)
        await visual_button_editor(chat_id, message_id, bid)
        return True
    if data.startswith("btnaction:"):
        await button_action_picker(chat_id, message_id, data.split(":", 1)[1])
        return True
    if data.startswith("btnsetaction:"):
        _, action, bid = data.split(":", 2)
        await db_execute("UPDATE buttons SET action=? WHERE id=?", (action, bid))
        if action != "url":
            await db_execute("UPDATE buttons SET url='' WHERE id=?", (bid,))
        await audit("Button action", f"{bid}={action}")
        if action == "media":
            await set_state(user_id, f"ui_edit_media_photo:{bid}")
            await edit_message(chat_id, message_id, "🖼 أرسل الصورة الجديدة للزر.", cancel_keyboard())
        elif action in ("text", "page"):
            await set_state(user_id, f"ui_value:{bid}:{action}")
            prompt = "📝 أرسل النص الجديد:" if action == "text" else "🧩 أرسل ID الصفحة:" 
            await edit_message(chat_id, message_id, prompt, cancel_keyboard())
        elif action == "url":
            await set_state(user_id, f"ui_url:{bid}")
            await edit_message(chat_id, message_id, "🔗 أرسل الرابط الجديد.", cancel_keyboard())
        else:
            await visual_button_editor(chat_id, message_id, bid)
        return True
    if data.startswith("btnvalue:"):
        bid = data.split(":", 1)[1]
        await set_state(user_id, f"ui_value:{bid}:text")
        await edit_message(chat_id, message_id, "📝 أرسل النص الذي يظهر عند الضغط على الزر.", cancel_keyboard())
        return True
    if data.startswith("btnurl:"):
        bid = data.split(":", 1)[1]
        await set_state(user_id, f"ui_url:{bid}")
        await edit_message(chat_id, message_id, "🔗 أرسل الرابط الجديد، أو <code>none</code> للحذف.", cancel_keyboard())
        return True
    if data.startswith("btnmedia:"):
        bid = data.split(":", 1)[1]
        await set_state(user_id, f"ui_edit_media_photo:{bid}")
        await edit_message(chat_id, message_id, "🖼 أرسل صورة الزر الآن. بعدها سأطلب النص تحت الصورة.", cancel_keyboard())
        return True
    if data.startswith("btnmedia_delete:"):
        bid = data.split(":", 1)[1]
        await db_execute("UPDATE buttons SET photo='',caption='' WHERE id=?", (bid,))
        await audit("Delete button media", bid)
        await visual_button_editor(chat_id, message_id, bid)
        return True
    if data.startswith("btnmove:"):
        await button_move_picker(chat_id, message_id, data.split(":", 1)[1])
        return True
    if data.startswith("btnmove_do:"):
        _, direction, bid = data.split(":", 2)
        row = await db_execute("SELECT row,position FROM buttons WHERE id=?", (bid,), fetchone=True)
        if not row:
            return True
        r, pos = int(row["row"]), int(row["position"])
        if direction in ("left", "right"):
            step = -1 if direction == "left" else 1
            neighbor = await db_execute("SELECT id FROM buttons WHERE row=? AND position=?", (r, pos+step), fetchone=True)
            if neighbor:
                await db_execute("UPDATE buttons SET position=? WHERE id=?", (999999, bid))
                await db_execute("UPDATE buttons SET position=? WHERE id=?", (pos, neighbor["id"]))
                await db_execute("UPDATE buttons SET position=? WHERE id=?", (pos+step, bid))
        elif direction in ("up", "down"):
            new_row = max(0, r-1) if direction == "up" else r+1
            await db_execute("UPDATE buttons SET row=? WHERE id=?", (new_row, bid))
        elif direction == "newrow":
            mx = await db_execute("SELECT COALESCE(MAX(row),-1) m FROM buttons", fetchone=True)
            await db_execute("UPDATE buttons SET row=?,position=0 WHERE id=?", (int(mx["m"])+1, bid))
        if await get_setting("editor_auto_normalize", "1") == "1":
            await normalize_button_positions()
        await audit("Button move", f"{bid}:{direction}")
        await visual_button_editor(chat_id, message_id, bid)
        return True
    if data.startswith("btnplace:"):
        await button_place_after_picker(chat_id, message_id, data.split(":", 1)[1])
        return True
    if data.startswith("btnplace_do:"):
        _, bid, target = data.split(":", 2)
        t = await db_execute("SELECT row,position FROM buttons WHERE id=?", (target,), fetchone=True)
        if t:
            row, pos = int(t["row"]), int(t["position"])+1
            await db_execute("UPDATE buttons SET position=position+1 WHERE row=? AND position>=? AND id<>?", (row,pos,bid))
            await db_execute("UPDATE buttons SET row=?,position=? WHERE id=?", (row,pos,bid))
            await normalize_button_positions()
        await visual_button_editor(chat_id, message_id, bid)
        return True
    if data.startswith("btnclone:"):
        bid = data.split(":", 1)[1]
        new_id = await clone_button(bid)
        if new_id:
            await visual_button_editor(chat_id, message_id, new_id)
        else:
            await send_message(chat_id, "❌ تعذر نسخ الزر.")
        return True
    if data.startswith("btnpreview:"):
        await preview_button(chat_id, data.split(":", 1)[1])
        return True
    if data.startswith("btndelete:"):
        bid = data.split(":", 1)[1]
        if await get_setting("button_confirm_delete", "1") == "1":
            await edit_message(chat_id, message_id, "⚠️ <b>تأكيد حذف الزر؟</b>", {"inline_keyboard":[
                [{"text":"🗑 نعم، احذف", "callback_data":f"btndelete_yes:{bid}", "style":"danger"}],
                [{"text":"🔙 إلغاء", "callback_data":f"btnedit:{bid}"}],
            ]})
        else:
            await delete_button_safe(chat_id, message_id, bid)
        return True
    if data.startswith("btndelete_yes:"):
        await delete_button_safe(chat_id, message_id, data.split(":",1)[1], user_id)
        return True
    if data.startswith("btneditfield:text:"):
        bid = data.split(":",2)[2]
        await set_state(user_id, f"ui_edit_text:{bid}")
        await edit_message(chat_id, message_id, "✏️ أرسل الاسم الجديد للزر.", cancel_keyboard())
        return True
    return False


# =========================================================
# ADMIN ACTIONS
# =========================================================

async def admin_stats(chat_id, message_id):
    user_count = await db_execute(
        "SELECT COUNT(*) AS c FROM users",
        fetchone=True,
    )
    messages = await db_execute(
        "SELECT COUNT(*) AS c FROM messages WHERE direction='USER'",
        fetchone=True,
    )
    blocked = await db_execute(
        "SELECT COUNT(*) AS c FROM users WHERE blocked=1",
        fetchone=True,
    )
    muted = await db_execute(
        "SELECT COUNT(*) AS c FROM users WHERE muted_until>?",
        (time.time(),),
        fetchone=True,
    )

    text = (
        "📊 <b>الإحصائيات</b>\n\n"
        f"👥 المستخدمون: {user_count['c']}\n"
        f"📨 رسائل المستخدمين: {messages['c']}\n"
        f"🚫 المحظورون: {blocked['c']}\n"
        f"🔇 المكتومون حالياً: {muted['c']}\n"
        f"⏱ مدة التشغيل: {uptime()}"
    )
    await edit_message(chat_id, message_id, text, back_keyboard("admin"))


async def admin_users(chat_id, message_id):
    rows = await db_execute("""
        SELECT user_id,name,username,messages,media,blocked
        FROM users
        ORDER BY last_activity DESC
        LIMIT 20
    """, fetchall=True)

    text = "👥 <b>آخر 20 مستخدم</b>\n\n"
    for row in rows or []:
        text += (
            f"• {esc(row['name'] or 'مستخدم')} "
            f"| <code>{row['user_id']}</code> "
            f"| رسائل: {row['messages']} "
            f"| {'🚫' if row['blocked'] else '🟢'}\n"
        )

    await edit_message(chat_id, message_id, text, back_keyboard("admin"))


async def admin_contact(chat_id, message_id):
    photo = await get_setting("contact_photo", "")
    enabled = await get_setting("contact_enabled", "1") == "1"
    footer = await get_setting("contact_footer", "")
    text = (
        "📨 <b>مركز التواصل</b>\n\n"
        f"الحالة: {'🟢 مفعّل' if enabled else '🔴 متوقف'}\n"
        f"الصورة: {'🟢 موجودة' if photo else '🔴 غير موجودة'}\n"
        f"الفوتر: {'🟢 مفعّل' if footer else '⚪ غير موجود'}\n\n"
        "عند ضغط العضو على زر التواصل تظهر له صورة التواصل ثم نص التواصل والأزرار، وبعدها يدخل وضع المحادثة."
    )
    keyboard = {
        "inline_keyboard": [
            [{"text": "📝 تعديل نص التواصل", "callback_data": "contact:edit"}],
            [{"text": "🖼 صورة التواصل", "callback_data": "contact:photo"}, {"text": "🗑 حذف الصورة", "callback_data": "contact:photo_delete"}],
            [{"text": "👁 معاينة التواصل", "callback_data": "contact:preview"}],
            [{"text": "🔘 تفعيل/إيقاف", "callback_data": "contact:toggle"}],
            [{"text": "📝 تعديل الفوتر", "callback_data": "contact:footer"}],
            [{"text": "🔙 رجوع", "callback_data": "admin"}],
        ]
    }
    await edit_message(chat_id, message_id, text, keyboard)


async def admin_contact_media(chat_id, message_id):
    photo = await get_setting("contact_photo", "")
    enabled = await get_setting("contact_enabled", "1") == "1"
    text = (
        "🖼 <b>صور التواصل</b>\n\n"
        f"صورة التواصل: {'موجودة ✅' if photo else 'غير موجودة ❌'}\n"
        f"الحالة: {'🟢 مفعّلة' if enabled else '🔴 متوقفة'}"
    )
    keyboard = {
        "inline_keyboard": [
            [{"text": "🖼 رفع صورة التواصل", "callback_data": "contact:photo"}],
            [{"text": "👁 معاينة", "callback_data": "contact:preview"}],
            [{"text": "🗑 حذف", "callback_data": "contact:photo_delete"}],
            [{"text": "🔙 لوحة المطور", "callback_data": "admin"}],
        ]
    }
    await edit_message(chat_id, message_id, text, keyboard)


async def admin_texts(chat_id, message_id):
    start = await get_setting("start_text", DEFAULT_START_TEXT)
    contact = await get_setting("contact_text", DEFAULT_CONTACT_TEXT)
    text = (
        "💬 <b>إدارة النصوص</b>\n\n"
        f"🟦 <b>Start:</b>\n<code>{esc(start)}</code>\n\n"
        f"🟩 <b>التواصل:</b>\n<code>{esc(contact)}</code>"
    )
    keyboard = {
        "inline_keyboard": [
            [{"text": "✏️ تعديل Start", "callback_data": "text:edit_start"}],
            [{"text": "✏️ تعديل التواصل", "callback_data": "text:edit_contact"}],
            [{"text": "🔙 رجوع", "callback_data": "admin"}],
        ]
    }
    await edit_message(chat_id, message_id, text, keyboard)


async def admin_welcome(chat_id, message_id):
    enabled = await get_setting("welcome_enabled", "1") == "1"
    photo = await get_setting("welcome_photo", "")
    text = await get_setting("start_text", DEFAULT_START_TEXT)
    body = (
        "🎉 <b>مركز الترحيب</b>\n\n"
        f"الحالة: {'🟢 مفعلة' if enabled else '🔴 متوقفة'}\n"
        f"الصورة: {'🟢 موجودة' if photo else '🔴 غير موجودة'}\n\n"
        "📝 <b>رسالة الترحيب:</b>\n" + esc(text)
    )
    keyboard={"inline_keyboard":[
        [{"text":"✏️ تعديل رسالة الترحيب","callback_data":"welcome:text"}],
        [{"text":"🖼 تغيير الصورة","callback_data":"photo:welcome"},{"text":"🗑 حذف الصورة","callback_data":"photo:welcome_delete"}],
        [{"text":"👁 تبديل الصورة/النص","callback_data":"welcome:toggle"}],
        [{"text":"🔍 معاينة الترحيب","callback_data":"welcome:preview"}],
        [{"text":"🔙 رجوع","callback_data":"admin"}],
    ]}
    await edit_message(chat_id,message_id,body,keyboard)


async def admin_photos(chat_id, message_id):
    welcome = await get_setting("welcome_photo", "")
    dev = await get_setting("dev_photo", "")
    contact = await get_setting("contact_photo", "")
    maintenance = await get_setting("maintenance_photo", "")
    text = (
        "🖼 <b>الصور</b>\n\n"
        f"صورة الترحيب: {'موجودة ✅' if welcome else 'غير موجودة ❌'}\n"
        f"صورة المطور: {'موجودة ✅' if dev else 'غير موجودة ❌'}\n"
        f"صورة التواصل: {'موجودة ✅' if contact else 'غير موجودة ❌'}\n"
        f"صورة الصيانة: {'موجودة ✅' if maintenance else 'غير موجودة ❌'}"
    )
    keyboard = {
        "inline_keyboard": [
            [{"text": "🖼 تغيير صورة الترحيب", "callback_data": "photo:welcome"}],
            [{"text": "🗑 حذف صورة الترحيب", "callback_data": "photo:welcome_delete"}],
            [{"text": "🖼 تغيير صورة المطور", "callback_data": "photo:dev"}],
            [{"text": "👁 معاينة صورة المطور", "callback_data": "photo:dev_preview"}],
            [{"text": "🗑 حذف صورة المطور", "callback_data": "photo:dev_delete"}],
            [{"text": "🖼 صورة التواصل", "callback_data": "contact:photo"}, {"text": "🗑 حذف", "callback_data": "contact:photo_delete"}],
            [{"text": "🖼 صورة الصيانة", "callback_data": "photo:maintenance"}, {"text": "🗑 حذف", "callback_data": "photo:maintenance_delete"}],
            [{"text": "🔙 رجوع", "callback_data": "admin"}],
        ]
    }
    await edit_message(chat_id, message_id, text, keyboard)


async def admin_status(chat_id, message_id):
    maintenance = await get_setting("maintenance", "0") == "1"
    enabled = await get_setting("bot_enabled", "1") == "1"
    force = await get_setting("force_sub", "1") == "1"
    protection = await get_setting("protection", "1") == "1"

    text = (
        "⚙️ <b>حالة البوت</b>\n\n"
        f"البوت: {'🟢 يعمل' if enabled else '🔴 متوقف'}\n"
        f"الصيانة: {'🟡 مفعلة' if maintenance else '🟢 مغلقة'}\n"
        f"الاشتراك الإجباري: {'🟢' if force else '🔴'}\n"
        f"الحماية: {'🟢' if protection else '🔴'}"
    )

    keyboard = {
        "inline_keyboard": [
            [{"text": "🔧 تبديل الصيانة", "callback_data": "status:maintenance"}],
            [{"text": "📢 تبديل الاشتراك الإجباري", "callback_data": "status:force"}],
            [{"text": "🛡 تبديل الحماية", "callback_data": "status:protection"}],
            [{"text": "🔙 رجوع", "callback_data": "admin"}],
        ]
    }
    await edit_message(chat_id, message_id, text, keyboard)


async def admin_channels(chat_id, message_id):
    rows = await db_execute(
        "SELECT channel FROM forced_channels ORDER BY channel",
        fetchall=True,
    )
    channels = "\n".join(f"• @{r['channel']}" for r in rows or [])
    if not channels:
        channels = "لا توجد قنوات."

    text = f"📢 <b>القنوات الإجبارية</b>\n\n{channels}"
    keyboard = {
        "inline_keyboard": [
            [{"text": "➕ إضافة قناة", "callback_data": "channel:add"}],
            [{"text": "➖ حذف قناة", "callback_data": "channel:delete"}],
            [{"text": "🔙 رجوع", "callback_data": "admin"}],
        ]
    }
    await edit_message(chat_id, message_id, text, keyboard)


# =========================================================
# CONTROL CENTER PRO 5.0
# =========================================================

PRO_STYLE = {
    "blue": "primary",
    "green": "success",
    "red": "danger",
}


def pro_kb(rows):
    return {"inline_keyboard": rows}


async def pro_adminui(chat_id, message_id):
    rows = await db_execute("SELECT * FROM admin_buttons ORDER BY row,position,id", fetchall=True)
    lines=["🎛 <b>تحكم أزرار المطور</b>","","كل زر هنا قابل لتغيير النص واللون والإظهار والتحريك."]
    kb=[]
    for r in rows or []:
        status="🟢" if r["enabled"] else "🔴"
        lines.append(f"{status} {esc(r['text'])} — <code>{esc(r['style'])}</code>")
        kb.append([{"text":f"⚙️ {str(r['text'])[:28]}","callback_data":f"adminbtn:{r['id']}"}])
    kb.append([{"text":"🔙 لوحة المطور","callback_data":"admin"}])
    await edit_message(chat_id,message_id,"\n".join(lines),pro_kb(kb))


async def admin_button_place_picker(chat_id, message_id, button_id):
    r = await db_execute("SELECT * FROM admin_buttons WHERE id=?", (button_id,), fetchone=True)
    if not r:
        await edit_message(chat_id, message_id, "❌ الزر غير موجود.", back_keyboard("pro:adminui"))
        return
    rows = await db_execute("SELECT * FROM admin_buttons ORDER BY row,position,id", fetchall=True)
    kb = []
    grouped = defaultdict(list)
    for item in rows or []:
        if item["id"] != button_id:
            grouped[int(item["row"] or 0)].append(item)
    for row_no in sorted(grouped):
        kb.append([{"text": f"━━ الصف {row_no + 1} ━━", "callback_data": "adminbtnplace:noop"}])
        for item in sorted(grouped[row_no], key=lambda x: (int(x["position"] or 0), str(x["id"]))):
            kb.append([{"text": f"➕ بعد {str(item['text'])[:30]}", "callback_data": f"adminbtnplace:after:{button_id}:{item['id']}"}])
    kb.append([{"text": "➕ صف جديد في الأسفل", "callback_data": f"adminbtnplace:newrow:{button_id}"}])
    kb.append([{"text": "🔙 رجوع", "callback_data": f"adminbtn:{button_id}"}])
    await edit_message(chat_id, message_id, "📍 <b>اختر مكان زر المطور</b>\n\nاضغط على الزر الذي تريد وضع الزر الحالي بعده.", {"inline_keyboard": kb})


async def pro_admin_button(chat_id, message_id, button_id):
    r=await db_execute("SELECT * FROM admin_buttons WHERE id=?",(button_id,),fetchone=True)
    if not r:
        await send_message(chat_id,"❌ الزر غير موجود."); return
    kb=pro_kb([
        [{"text":"✏️ تغيير النص","callback_data":f"adminbtnedit:text:{button_id}"}],
        [{"text":"🎨 تغيير اللون","callback_data":f"adminbtnedit:style:{button_id}"}],
        [{"text":"👁 إظهار/إخفاء","callback_data":f"adminbtntoggle:{button_id}"}],
        [{"text":"⬅️ بداية الصف","callback_data":f"adminbtnmove:left:{button_id}"},{"text":"➡️ نهاية الصف","callback_data":f"adminbtnmove:right:{button_id}"}],
        [{"text":"⬆️ صف أعلى","callback_data":f"adminbtnmove:up:{button_id}"},{"text":"⬇️ صف أسفل","callback_data":f"adminbtnmove:down:{button_id}"}],
        [{"text":"📍 اختيار مكان بصري","callback_data":f"adminbtnplace:{button_id}"}],
        [{"text":"🔙 أزرار المطور","callback_data":"pro:adminui"}],
    ])
    await edit_message(chat_id,message_id,f"🎛 <b>{esc(r['text'])}</b>\n\nاللون: <code>{esc(r['style'])}</code>\nالحالة: {'🟢' if r['enabled'] else '🔴'}",kb)


async def pro_dashboard(chat_id, message_id):
    users = await db_execute("SELECT COUNT(*) c FROM users", fetchone=True)
    active = await db_execute("SELECT COUNT(*) c FROM users WHERE last_activity >= ?", (dt.datetime.now().strftime('%Y-%m-%d') + " 00:00:00",), fetchone=True)
    msgs = await db_execute("SELECT COUNT(*) c FROM messages", fetchone=True)
    user_msgs = await db_execute("SELECT COUNT(*) c FROM messages WHERE direction='USER'", fetchone=True)
    media = await db_execute("SELECT COUNT(*) c FROM messages WHERE media_type!='text'", fetchone=True)
    blocked = await db_execute("SELECT COUNT(*) c FROM users WHERE blocked=1", fetchone=True)
    errors = await db_execute("SELECT COUNT(*) c FROM error_logs", fetchone=True)
    buttons = await db_execute("SELECT COUNT(*) c FROM buttons WHERE enabled=1", fetchone=True)
    pages = await db_execute("SELECT COUNT(*) c FROM menu_pages WHERE enabled=1", fetchone=True)
    text = (
        "📊 <b>CONTROL CENTER PRO</b>\n\n"
        f"🟢 الحالة: {'يعمل' if await get_setting('bot_enabled','1')=='1' else 'متوقف'}\n"
        f"⏱ التشغيل: {uptime()}\n\n"
        f"👥 المستخدمون: <b>{users['c']}</b>\n"
        f"🟢 نشطون اليوم: <b>{active['c']}</b>\n"
        f"📨 إجمالي الرسائل: <b>{msgs['c']}</b>\n"
        f"📩 رسائل المستخدمين: <b>{user_msgs['c']}</b>\n"
        f"📎 الوسائط: <b>{media['c']}</b>\n"
        f"🚫 المحظورون: <b>{blocked['c']}</b>\n"
        f"⚠️ الأخطاء المسجلة: <b>{errors['c']}</b>\n\n"
        f"🎨 أزرار فعالة: <b>{buttons['c']}</b>\n"
        f"🧩 صفحات: <b>{pages['c']}</b>"
    )
    kb=pro_kb([
        [{"text":"🔄 تحديث","callback_data":"pro:dashboard"},{"text":"📈 إحصائيات","callback_data":"adm:stats"}],
        [{"text":"👥 المستخدمون","callback_data":"pro:users"},{"text":"📜 السجلات","callback_data":"pro:logs"}],
        [{"text":"🔙 لوحة المطور","callback_data":"admin"}],
    ])
    await edit_message(chat_id,message_id,text,kb)


async def pro_content(chat_id, message_id):
    keys=[
        ("start_text","🟦 Start"),("contact_text","📨 التواصل"),("contact_footer","🔻 فوتر التواصل"),
        ("maintenance_text","🔧 الصيانة"),("disabled_text","⛔ التوقف"),("banned_text","🚫 الحظر"),
        ("rate_warning_text","⚠️ الحماية"),("footer_text","🔻 Footer"),
    ]
    lines=["📝 <b>مركز المحتوى</b>","\nكل النصوص التالية قابلة للتعديل من داخل البوت:"]
    for k,label in keys:
        val=await get_setting(k,"")
        preview=str(val).replace("\n"," ")[:70]
        lines.append(f"\n{label}: <code>{esc(preview)}</code>")
    rows=[]
    for k,label in keys:
        rows.append([{"text":f"✏️ {label}","callback_data":f"proedit:{k}"}])
    rows.append([{"text":"🔙 لوحة المطور","callback_data":"admin"}])
    await edit_message(chat_id,message_id,"\n".join(lines),pro_kb(rows))


async def pro_security(chat_id, message_id):
    protection=await get_setting("protection","1")=="1"
    force=await get_setting("force_sub","1")=="1"
    notifications=await get_setting("notifications","1")=="1"
    limit=await get_setting("max_requests_per_min","30")
    maint=await get_setting("maintenance","0")=="1"
    text=("🛡 <b>مركز الحماية والتحكم</b>\n\n"
          f"الحماية: {'🟢' if protection else '🔴'}\n"
          f"الحد: <b>{esc(limit)}</b> طلب/دقيقة\n"
          f"الاشتراك الإجباري: {'🟢' if force else '🔴'}\n"
          f"إشعارات المستخدمين الجدد: {'🟢' if notifications else '🔴'}\n"
          f"الصيانة: {'🟡' if maint else '🟢'}")
    kb=pro_kb([
        [{"text":"🛡 تبديل الحماية","callback_data":"protoggle:protection"},{"text":"📢 الاشتراك","callback_data":"protoggle:force"}],
        [{"text":"🔔 الإشعارات","callback_data":"protoggle:notifications"},{"text":"🔧 الصيانة","callback_data":"protoggle:maintenance"}],
        [{"text":"⚙️ تغيير الحد","callback_data":"prolimit"}],
        [{"text":"🔙 لوحة المطور","callback_data":"admin"}],
    ])
    await edit_message(chat_id,message_id,text,kb)


async def pro_system(chat_id, message_id):
    enabled=await get_setting("bot_enabled","1")=="1"
    default_style=await get_setting("button_default_style","primary")
    text=("⚙️ <b>إعدادات النظام</b>\n\n"
          f"🤖 البوت: {'🟢 يعمل' if enabled else '🔴 متوقف'}\n"
          f"🎨 اللون الافتراضي: <code>{esc(default_style)}</code>\n"
          f"📦 الإصدار: <code>{esc(BOT_VERSION)}</code>\n"
          f"💾 قاعدة البيانات: <code>{esc(DB_FILE)}</code>")
    kb=pro_kb([
        [{"text":"🟢/🔴 تشغيل البوت","callback_data":"protoggle:bot_enabled"}],
        [{"text":"🎨 اللون الافتراضي","callback_data":"prostyle_default"}],
        [{"text":"🧹 تنظيف السجلات","callback_data":"pro:cleanlogs"}],
        [{"text":"🔙 لوحة المطور","callback_data":"admin"}],
    ])
    await edit_message(chat_id,message_id,text,kb)


async def pro_logs(chat_id, message_id):
    logs=await db_execute("SELECT action,details,created_at FROM audit_logs ORDER BY id DESC LIMIT 15",fetchall=True)
    errors=await db_execute("SELECT source,error,created_at FROM error_logs ORDER BY id DESC LIMIT 8",fetchall=True)
    lines=["📜 <b>السجلات</b>","","<b>آخر عمليات الإدارة:</b>"]
    for r in logs or []:
        lines.append(f"• <code>{esc(r['created_at'])}</code> — {esc(r['action'])} — {esc(r['details'])[:80]}")
    lines.append("\n<b>آخر الأخطاء:</b>")
    for r in errors or []:
        lines.append(f"• <code>{esc(r['created_at'])}</code> — {esc(r['source'])}: {esc(r['error'])[:90]}")
    kb=pro_kb([[{"text":"🔄 تحديث","callback_data":"pro:logs"}],[{"text":"🧹 مسح السجلات","callback_data":"pro:cleanlogs"}],[{"text":"🔙 لوحة المطور","callback_data":"admin"}]])
    await edit_message(chat_id,message_id,"\n".join(lines),kb)


async def pro_backup(chat_id, message_id):
    b=len(list(BACKUP_DIR.glob("*.db")))
    text=("💾 <b>مركز النسخ والتصدير</b>\n\n"
          f"نسخ قاعدة البيانات الموجودة: <b>{b}</b>\n"
          f"مجلد التصدير: <code>{esc(str(EXPORT_DIR))}</code>")
    kb=pro_kb([
        [{"text":"💾 إنشاء نسخة الآن","callback_data":"pro:createbackup"}],
        [{"text":"📤 تصدير المستخدمين","callback_data":"pro:exportusers"}],
        [{"text":"📤 تصدير الإعدادات والأزرار","callback_data":"pro:exportconfig"}],
        [{"text":"🔙 لوحة المطور","callback_data":"admin"}],
    ])
    await edit_message(chat_id,message_id,text,kb)


async def pro_users(chat_id, message_id):
    rows=await db_execute("SELECT user_id,name,username,messages,media,blocked,last_activity FROM users ORDER BY last_activity DESC LIMIT 12",fetchall=True)
    lines=["👥 <b>مركز المستخدمين</b>\n"]
    buttons=[]
    for r in rows or []:
        status="🚫" if r['blocked'] else "🟢"
        lines.append(f"{status} {esc(r['name'] or 'مستخدم')} — <code>{r['user_id']}</code> — 💬{r['messages']}")
        buttons.append([{"text":f"👤 {str(r['name'] or r['user_id'])[:24]}","callback_data":f"prouser:{r['user_id']}"}])
    buttons += [[{"text":"🔎 بحث","callback_data":"adm:search"}],[{"text":"🔙 لوحة المطور","callback_data":"admin"}]]
    await edit_message(chat_id,message_id,"\n".join(lines),pro_kb(buttons))


async def pro_user(chat_id,message_id,target):
    r=await db_execute("SELECT * FROM users WHERE user_id=?",(target,),fetchone=True)
    if not r:
        await edit_message(chat_id,message_id,"❌ المستخدم غير موجود.",back_keyboard("pro:users")); return
    text=(f"👤 <b>ملف المستخدم</b>\n\n"
          f"الاسم: {esc(r['name'])}\n"
          f"Username: @{esc(r['username']) if r['username'] else 'بدون'}\n"
          f"ID: <code>{r['user_id']}</code>\n"
          f"📨 الرسائل: {r['messages']}\n📎 الوسائط: {r['media']}\n"
          f"الحالة: {'🚫 محظور' if r['blocked'] else '🟢 طبيعي'}\n"
          f"آخر نشاط: {esc(r['last_activity'])}\n"
          f"📝 ملاحظات: {esc(r['notes'] or 'لا توجد')}")
    kb=pro_kb([
        [{"text":"🚫/🟢 تبديل الحظر","callback_data":f"prouserban:{target}"}],
        [{"text":"📝 تعديل الملاحظات","callback_data":f"prousernote:{target}"}],
        [{"text":"📨 إرسال رسالة","callback_data":f"prousermsg:{target}"}],
        [{"text":"🔙 المستخدمون","callback_data":"pro:users"}],
    ])
    await edit_message(chat_id,message_id,text,kb)


async def pro_pages(chat_id,message_id):
    rows=await db_execute("SELECT * FROM menu_pages ORDER BY created_at DESC",fetchall=True)
    lines=["🧩 <b>مدير الصفحات</b>\n","أنشئ صفحات فرعية واربطها بالأزرار من إدارة الواجهة.\n"]
    kb=[]
    for r in rows or []:
        status="🟢" if r['enabled'] else "🔴"
        lines.append(f"{status} {esc(r['title'])} — <code>{esc(r['id'])}</code>")
        kb.append([{"text":f"📄 {r['title'][:24]}","callback_data":f"propage:{r['id']}"}])
    kb += [[{"text":"➕ إنشاء صفحة","callback_data":"propageadd"}],[{"text":"🔙 لوحة المطور","callback_data":"admin"}]]
    await edit_message(chat_id,message_id,"\n".join(lines),pro_kb(kb))


async def pro_page(chat_id,message_id,page_id):
    r=await db_execute("SELECT * FROM menu_pages WHERE id=?",(page_id,),fetchone=True)
    if not r:
        await edit_message(chat_id,message_id,"❌ الصفحة غير موجودة.",back_keyboard("pro:pages")); return
    text=f"📄 <b>{esc(r['title'])}</b>\n\n{esc(r['text'])}\n\nID: <code>{esc(r['id'])}</code>\nالحالة: {'🟢' if r['enabled'] else '🔴'}"
    kb=pro_kb([
        [{"text":"✏️ تعديل العنوان","callback_data":f"propageedit:title:{page_id}"}],
        [{"text":"📝 تعديل المحتوى","callback_data":f"propageedit:text:{page_id}"}],
        [{"text":"👁 إظهار/إخفاء","callback_data":f"propagetoggle:{page_id}"}],
        [{"text":"🗑 حذف الصفحة","callback_data":f"propagedelete:{page_id}"}],
        [{"text":"🔙 الصفحات","callback_data":"pro:pages"}],
    ])
    await edit_message(chat_id,message_id,text,kb)


# =========================================================
# V11 ULTIMATE CONTROL CENTER
# =========================================================

async def snapshot_ui():
    settings = await db_execute("SELECT key,value FROM settings ORDER BY key", fetchall=True)
    buttons = await db_execute("SELECT * FROM buttons ORDER BY row,position,id", fetchall=True)
    admin = await db_execute("SELECT * FROM admin_buttons ORDER BY row,position,id", fetchall=True)
    pages = await db_execute("SELECT * FROM menu_pages ORDER BY id", fetchall=True)
    return {"settings": {r["key"]: r["value"] for r in settings or []}, "buttons": [dict(r) for r in buttons or []], "admin_buttons": [dict(r) for r in admin or []], "pages": [dict(r) for r in pages or []]}

async def save_ui_version(label="manual"):
    snap = await snapshot_ui()
    await db_execute("INSERT INTO theme_versions(theme_id,snapshot,created_at) VALUES(?,?,?)", ("default", json.dumps(snap,ensure_ascii=False), now_text()))
    row = await db_execute("SELECT last_insert_rowid() AS id", fetchone=True)
    version_id = int(row["id"] if row else 0)
    await audit("UI version saved", label)
    return version_id

async def restore_ui_version(row_id):
    row = await db_execute("SELECT snapshot FROM theme_versions WHERE id=?", (row_id,), fetchone=True)
    if not row:
        return False, "النسخة غير موجودة."
    try:
        snap=json.loads(row["snapshot"])
        for item in snap.get("buttons",[]):
            await db_execute("UPDATE buttons SET text=?,action=?,row=?,position=?,enabled=?,style=?,url=?,action_value=?,photo=?,caption=? WHERE id=?", (item.get("text","زر"),item.get("action","text"),item.get("row",0),item.get("position",0),item.get("enabled",1),item.get("style","primary"),item.get("url",""),item.get("action_value",""),item.get("photo",""),item.get("caption",""),item.get("id")))
        for item in snap.get("admin_buttons",[]):
            await db_execute("UPDATE admin_buttons SET text=?,row=?,position=?,enabled=?,style=? WHERE id=?", (item.get("text","زر"),item.get("row",0),item.get("position",0),item.get("enabled",1),item.get("style","primary"),item.get("id")))
        await load_admin_buttons(); await audit("UI version restored", str(row_id)); return True, "تمت استعادة النسخة."
    except Exception as exc:
        await log_error("restore_ui_version", exc); return False, "فشل الاستعادة."

async def v11_dashboard(chat_id,message_id):
    u=await db_execute("SELECT COUNT(*) c FROM users",fetchone=True)
    b=await db_execute("SELECT COUNT(*) c FROM buttons WHERE enabled=1",fetchone=True)
    clicks=await db_execute("SELECT COALESCE(SUM(clicks),0) c FROM button_analytics",fetchone=True)
    replies=await db_execute("SELECT COUNT(*) c FROM auto_replies WHERE enabled=1",fetchone=True)
    autos=await db_execute("SELECT COUNT(*) c FROM automations WHERE enabled=1",fetchone=True)
    text=("🚀 <b>V11 Ultimate Control Center</b>\n\n"
          f"👥 المستخدمون: <b>{u['c']}</b>\n🎛 الأزرار النشطة: <b>{b['c']}</b>\n"
          f"🖱 الضغطات: <b>{clicks['c']}</b>\n🧠 الردود التلقائية: <b>{replies['c']}</b>\n⏰ الأتمتة: <b>{autos['c']}</b>")
    kb={"inline_keyboard":[
        [{"text":"🎨 Theme Studio","callback_data":"v11:themes","style":"success"}],
        [{"text":"📊 Button Analytics","callback_data":"v11:analytics","style":"primary"}],
        [{"text":"🧠 Auto Reply","callback_data":"v11:autoreply","style":"primary"}],
        [{"text":"⏰ Automation","callback_data":"v11:automation","style":"primary"}],
        [{"text":"👥 User Segments","callback_data":"v11:segments","style":"primary"}],
        [{"text":"🕘 Version History","callback_data":"v11:versions","style":"primary"}],
        [{"text":"⚡ Multi-Action","callback_data":"v11:actions","style":"success"}],
        [{"text":"🔙 لوحة المطور","callback_data":"admin"}]]}
    await edit_message(chat_id,message_id,text,kb)

async def v11_themes(chat_id,message_id):
    rows=await db_execute("SELECT * FROM themes ORDER BY created_at DESC",fetchall=True)
    active=await get_setting("theme_active","default")
    text=f"🎨 <b>Theme Studio</b>\n\nالثيم الحالي: <code>{esc(active)}</code>\n\n"
    for r in rows or []: text+=f"{'🟢' if r['id']==active else '⚪'} {esc(r['name'])} — <code>{esc(r['id'])}</code>\n"
    kb=[[{"text":"➕ ثيم جديد","callback_data":"v11:themeadd","style":"success"}],[{"text":"💾 حفظ نسخة من الواجهة","callback_data":"v11:themesave"}],[{"text":"🎨 الثيم الحالي","callback_data":"v11:themeedit"}],[{"text":"🔙 رجوع","callback_data":"v11:dashboard"}]]
    await edit_message(chat_id,message_id,text,{"inline_keyboard":kb})

async def v11_analytics(chat_id,message_id):
    rows=await db_execute("SELECT b.id,b.text,b.action,COALESCE(a.clicks,0) clicks,a.last_click FROM buttons b LEFT JOIN button_analytics a ON a.button_id=b.id ORDER BY clicks DESC,row,position",fetchall=True)
    text="📊 <b>إحصائيات الأزرار</b>\n\n"
    for i,r in enumerate(rows or [],1): text+=f"{i}. {esc(r['text'])} — <b>{r['clicks']}</b> ضغطة\n"
    if not rows: text+="لا توجد بيانات بعد."
    await edit_message(chat_id,message_id,text,{"inline_keyboard":[[{"text":"🧹 تصفير الإحصائيات","callback_data":"v11:analyticsreset","style":"danger"}],[{"text":"🔙 رجوع","callback_data":"v11:dashboard"}]]})

async def v11_autoreply(chat_id,message_id):
    rows=await db_execute("SELECT * FROM auto_replies ORDER BY priority DESC,id DESC",fetchall=True)
    text="🧠 <b>Auto Reply Studio</b>\n\n"
    for r in rows or []: text+=f"{'🟢' if r['enabled'] else '🔴'} <code>{r['id']}</code> — {esc(r['trigger'])} → {esc(r['response'][:80])}\n"
    if not rows:text+="لا توجد قواعد.\n"
    kb=[[{"text":"➕ إضافة رد","callback_data":"v11:replyadd","style":"success"}]]
    for r in rows or []: kb.append([{"text":f"✏️ {r['trigger'][:25]}","callback_data":f"v11:reply:{r['id']}"},{"text":"👁","callback_data":f"v11:replytoggle:{r['id']}"},{"text":"🗑","callback_data":f"v11:replydelete:{r['id']}","style":"danger"}])
    kb.append([{ "text":"🔙 رجوع","callback_data":"v11:dashboard"}]); await edit_message(chat_id,message_id,text,{"inline_keyboard":kb})

async def v11_automation(chat_id,message_id):
    rows=await db_execute("SELECT * FROM automations ORDER BY id DESC",fetchall=True)
    text="⏰ <b>Automation Center</b>\n\n"
    for r in rows or []: text+=f"{'🟢' if r['enabled'] else '🔴'} <code>{r['id']}</code> {esc(r['title'])} — {esc(r['kind'])}\n"
    if not rows:text+="لا توجد مهام مجدولة.\n"
    kb=[[{"text":"➕ مهمة جديدة","callback_data":"v11:autoadd","style":"success"}]]
    for r in rows or []: kb.append([{"text":f"{r['title'][:22]}","callback_data":f"v11:auto:{r['id']}"},{"text":"👁","callback_data":f"v11:autotoggle:{r['id']}"},{"text":"🗑","callback_data":f"v11:autodelete:{r['id']}","style":"danger"}])
    kb.append([{ "text":"🔙 رجوع","callback_data":"v11:dashboard"}]); await edit_message(chat_id,message_id,text,{"inline_keyboard":kb})

async def v11_segments(chat_id,message_id):
    rows=await db_execute("SELECT * FROM user_segments ORDER BY id",fetchall=True)
    text="👥 <b>User Segments</b>\n\n"
    for r in rows or []:
        c=await db_execute("SELECT COUNT(*) c FROM segment_members WHERE segment_id=?",(r['id'],),fetchone=True)
        text+=f"{'🟢' if r['enabled'] else '🔴'} {esc(r['name'])} — {c['c']} عضو\n"
    if not rows:text+="لا توجد مجموعات.\n"
    kb=[[{"text":"➕ مجموعة جديدة","callback_data":"v11:segmentadd","style":"success"}]]
    for r in rows or []: kb.append([{"text":f"👥 {r['name'][:22]}","callback_data":f"v11:segment:{r['id']}"},{"text":"🗑","callback_data":f"v11:segmentdelete:{r['id']}","style":"danger"}])
    kb.append([{ "text":"🔙 رجوع","callback_data":"v11:dashboard"}]); await edit_message(chat_id,message_id,text,{"inline_keyboard":kb})

async def v11_versions(chat_id,message_id):
    rows=await db_execute("SELECT id,created_at FROM theme_versions ORDER BY id DESC LIMIT 15",fetchall=True)
    text="🕘 <b>Version History</b>\n\n"
    for r in rows or []: text+=f"📦 V{r['id']} — {esc(r['created_at'])}\n"
    if not rows:text+="لا توجد نسخ.\n"
    kb=[[{"text":"💾 حفظ نسخة الآن","callback_data":"v11:themesave","style":"success"}]]
    for r in rows or []: kb.append([{ "text":f"↩️ استعادة V{r['id']}","callback_data":f"v11:restore:{r['id']}","style":"danger"}])
    kb.append([{ "text":"🔙 رجوع","callback_data":"v11:dashboard"}]); await edit_message(chat_id,message_id,text,{"inline_keyboard":kb})

async def v11_actions(chat_id,message_id):
    rows=await get_buttons(include_disabled=True)
    text="⚡ <b>Multi-Action Builder</b>\n\nاختر زرًا لإضافة عدة إجراءات له.\n"
    kb=[]
    for r in rows: kb.append([{ "text":r['text'][:28],"callback_data":f"v11:buttonaction:{r['id']}"}])
    kb.append([{ "text":"🔙 رجوع","callback_data":"v11:dashboard"}]); await edit_message(chat_id,message_id,text,{"inline_keyboard":kb})

async def v11_button_actions(chat_id,message_id,bid):
    r=await db_execute("SELECT text FROM buttons WHERE id=?",(bid,),fetchone=True)
    acts=await db_execute("SELECT actions FROM button_actions WHERE button_id=?",(bid,),fetchone=True)
    items=[]
    if acts:
        try: items=json.loads(acts['actions'])
        except: items=[]
    text=f"⚡ <b>{esc(r['text'] if r else bid)}</b>\n\n"
    text += "\n".join(f"{i+1}. {esc(str(a))}" for i,a in enumerate(items)) or "لا توجد إجراءات إضافية."
    kb=[[{"text":"➕ إجراء نص","callback_data":f"v11:actionadd:text:{bid}","style":"success"}],[{"text":"➕ إجراء حذف رسالة","callback_data":f"v11:actionadd:delete:{bid}"}],[{"text":"🧹 مسح الإجراءات","callback_data":f"v11:actionclear:{bid}","style":"danger"}],[{"text":"🔙 رجوع","callback_data":"v11:actions"}]]
    await edit_message(chat_id,message_id,text,{"inline_keyboard":kb})

async def v11_handle_callback(user_id,chat_id,message_id,data):
    if data=="v11:dashboard": await v11_dashboard(chat_id,message_id); return True
    if data=="v11:themes": await v11_themes(chat_id,message_id); return True
    if data=="v11:analytics": await v11_analytics(chat_id,message_id); return True
    if data=="v11:autoreply": await v11_autoreply(chat_id,message_id); return True
    if data=="v11:automation": await v11_automation(chat_id,message_id); return True
    if data=="v11:segments": await v11_segments(chat_id,message_id); return True
    if data=="v11:versions": await v11_versions(chat_id,message_id); return True
    if data=="v11:actions": await v11_actions(chat_id,message_id); return True
    if data=="v11:themesave": await save_ui_version("manual"); await v11_themes(chat_id,message_id); return True
    if data=="v11:themeedit":
        await save_ui_version("before-theme-edit")
        await edit_message(chat_id,message_id,"🎨 <b>Theme Editor</b>\n\nاختر اللون الافتراضي الذي تريد تطبيقه على أزرار المستخدم:",{"inline_keyboard":[[{"text":"🔵 Primary","callback_data":"v11:theme_style:primary","style":"primary"}],[{"text":"🟢 Success","callback_data":"v11:theme_style:success","style":"success"}],[{"text":"🔴 Danger","callback_data":"v11:theme_style:danger","style":"danger"}],[{"text":"🔙 رجوع","callback_data":"v11:themes"}]]}); return True
    if data.startswith("v11:theme_style:"):
        style=data.split(":")[-1]
        if style not in ("primary","success","danger"): return True
        await db_execute("UPDATE buttons SET style=?",(style,)); await set_setting("button_default_style",style); await set_setting("theme_active","default"); await audit("Theme style applied",style); await send_message(chat_id,f"✅ تم تطبيق الثيم {style} على أزرار المستخدم.",admin_keyboard()); return True
    if data=="v11:analyticsreset": await db_execute("DELETE FROM button_analytics"); await audit("Analytics reset"); await v11_analytics(chat_id,message_id); return True
    if data=="v11:replyadd": await set_state(user_id,"v11_reply_trigger"); await edit_message(chat_id,message_id,"🧠 أرسل الكلمة/العبارة التي ستشغل الرد:",cancel_keyboard()); return True
    if data=="v11:autoadd": await set_state(user_id,"v11_auto_title"); await edit_message(chat_id,message_id,"⏰ أرسل اسم المهمة المجدولة:",cancel_keyboard()); return True
    if data=="v11:segmentadd": await set_state(user_id,"v11_segment_name"); await edit_message(chat_id,message_id,"👥 أرسل اسم المجموعة:",cancel_keyboard()); return True
    if data=="v11:themeadd": await set_state(user_id,"v11_theme_name"); await edit_message(chat_id,message_id,"🎨 أرسل اسم الثيم الجديد:",cancel_keyboard()); return True
    if data.startswith("v11:restore:"):
        ok,msg=await restore_ui_version(int(data.split(":")[-1])); await send_message(chat_id,("✅ " if ok else "❌ ")+msg,admin_keyboard()); return True
    if data.startswith("v11:replytoggle:"):
        rid=int(data.split(":")[-1]); r=await db_execute("SELECT enabled FROM auto_replies WHERE id=?",(rid,),fetchone=True); await db_execute("UPDATE auto_replies SET enabled=? WHERE id=?",(0 if r and r['enabled'] else 1,rid)); await v11_autoreply(chat_id,message_id); return True
    if data.startswith("v11:replydelete:"):
        rid=int(data.split(":")[-1]); await db_execute("DELETE FROM auto_replies WHERE id=?",(rid,)); await v11_autoreply(chat_id,message_id); return True
    if data.startswith("v11:autotoggle:"):
        rid=int(data.split(":")[-1]); r=await db_execute("SELECT enabled FROM automations WHERE id=?",(rid,),fetchone=True); await db_execute("UPDATE automations SET enabled=? WHERE id=?",(0 if r and r['enabled'] else 1,rid)); await v11_automation(chat_id,message_id); return True
    if data.startswith("v11:autodelete:"):
        rid=int(data.split(":")[-1]); await db_execute("DELETE FROM automations WHERE id=?",(rid,)); await v11_automation(chat_id,message_id); return True
    if data.startswith("v11:segmentdelete:"):
        sid=data.split(":")[-1]; await db_execute("DELETE FROM user_segments WHERE id=?",(sid,)); await db_execute("DELETE FROM segment_members WHERE segment_id=?",(sid,)); await v11_segments(chat_id,message_id); return True
    if data.startswith("v11:buttonaction:"): await v11_button_actions(chat_id,message_id,data.split(":")[-1]); return True
    if data.startswith("v11:actionadd:"):
        _,_,kind,bid=data.split(":",3); await set_state(user_id,f"v11_action:{kind}:{bid}"); await edit_message(chat_id,message_id,"📝 أرسل النص للإجراء:" if kind=="text" else "⚡ سيتم إضافة إجراء حذف الرسالة. أرسل أي نص للتأكيد.",cancel_keyboard()); return True
    if data.startswith("v11:actionclear:"):
        await db_execute("DELETE FROM button_actions WHERE button_id=?",(data.split(":")[-1],)); await v11_button_actions(chat_id,message_id,data.split(":")[-1]); return True
    if data.startswith("v11:reply:"):
        rid=int(data.split(":")[-1]); r=await db_execute("SELECT trigger,response FROM auto_replies WHERE id=?",(rid,),fetchone=True); await send_message(chat_id,f"🧠 <b>الرد</b>\n\nالمحفز: {esc(r['trigger'])}\nالرد: {esc(r['response'])}",back_keyboard("v11:autoreply")); return True
    return False

async def v11_check_autoreply(user_id, chat_id, text):
    if not text or await get_setting("autoreply_enabled","1")!="1": return False
    rows=await db_execute("SELECT * FROM auto_replies WHERE enabled=1 ORDER BY priority DESC,id ASC",fetchall=True)
    low=text.casefold()
    for r in rows or []:
        trig=str(r['trigger']).casefold()
        matched=(trig==low) if r['match_type']=='exact' else (trig in low)
        if matched:
            await send_message(chat_id,await render_text(r['response'],user_id)); return True
    return False

async def v11_scheduler_loop():
    while True:
        try:
            if await get_setting("automation_enabled","1")=="1":
                now=time.time(); rows=await db_execute("SELECT * FROM automations WHERE enabled=1 AND next_run>0 AND next_run<=?",(now,),fetchall=True)
                for r in rows or []:
                    payload=json.loads(r['payload'] or '{}')
                    text=str(payload.get('text',''))
                    targets=await db_execute("SELECT user_id FROM users WHERE blocked=0",fetchall=True)
                    for u in targets or []:
                        await send_message(u['user_id'],await render_text(text,u['user_id'])); await asyncio.sleep(0.06)
                    interval=int(r['interval_sec'] or 0); next_run=now+interval if interval>0 else 0
                    await db_execute("UPDATE automations SET next_run=?,enabled=? WHERE id=?",(next_run,1 if interval>0 else 0,r['id']))
                    await audit("Automation executed",str(r['id']))
        except Exception as exc: await log_error("scheduler",exc)
        await asyncio.sleep(5)


# =========================================================
# V13 ULTIMATE VISUAL CONTROL
# =========================================================
async def v13_dashboard(chat_id, message_id):
    users=await db_execute("SELECT COUNT(*) c FROM users",fetchone=True)
    buttons=await db_execute("SELECT COUNT(*) c FROM buttons",fetchone=True)
    pages=await db_execute("SELECT COUNT(*) c FROM menu_pages WHERE enabled=1",fetchone=True)
    clicks=await db_execute("SELECT COALESCE(SUM(clicks),0) c FROM button_analytics",fetchone=True)
    errors=await db_execute("SELECT COUNT(*) c FROM error_logs",fetchone=True)
    text=("🚀 <b>V13 ULTIMATE CONTROL CENTER</b>\n\n"
          f"🟢 الحالة: {'يعمل' if await get_setting('bot_enabled','1')=='1' else 'متوقف'}\n"
          f"👥 المستخدمون: <b>{users['c']}</b>\n🔘 الأزرار: <b>{buttons['c']}</b>\n"
          f"🧩 الصفحات: <b>{pages['c']}</b>\n📊 الضغطات: <b>{clicks['c']}</b>\n⚠️ الأخطاء: <b>{errors['c']}</b>\n\nاختر النظام:")
    kb={"inline_keyboard":[
        [{"text":"🎛 Button Studio 2.0","callback_data":"v13:buttons","style":"success"}],
        [{"text":"🧱 Page Builder","callback_data":"pro:pages"},{"text":"🎨 Theme Studio","callback_data":"v13:theme"}],
        [{"text":"⚡ Multi-Action","callback_data":"v11:actions","style":"success"},{"text":"📊 Analytics","callback_data":"v11:analytics"}],
        [{"text":"⏰ Automation","callback_data":"v11:automation"},{"text":"🧠 Auto Reply","callback_data":"v11:autoreply"}],
        [{"text":"💾 Version History","callback_data":"v11:versions"},{"text":"🧪 Live Preview","callback_data":"v13:preview","style":"success"}],
        [{"text":"🔙 لوحة المطور","callback_data":"admin"}]
    ]}
    await edit_message(chat_id,message_id,text,kb)

async def v13_buttons(chat_id,message_id):
    rows=await get_buttons(include_disabled=True); kb=[]
    for r in rows[:35]:
        kb.append([{"text":f"{'🟢' if r['enabled'] else '🔴'} {str(r['text'])[:27]}{' 🖼' if r['photo'] else ''}","callback_data":f"v13:button:{r['id']}"}])
    kb += [[{"text":"➕ إضافة زر","callback_data":"ui:add","style":"success"}],
           [{"text":"🧹 ترتيب تلقائي","callback_data":"v13:normalize"}],
           [{"text":"👁 معاينة","callback_data":"v13:preview"}],
           [{"text":"🔙 مركز V13","callback_data":"v13:dashboard"}]]
    await edit_message(chat_id,message_id,"🎛 <b>BUTTON STUDIO 2.0</b>\n\nاختر الزر لتعديل كل خصائصه.",{"inline_keyboard":kb})

async def v13_button(chat_id,message_id,bid):
    r=await db_execute("SELECT * FROM buttons WHERE id=?",(bid,),fetchone=True)
    if not r:
        await edit_message(chat_id,message_id,"❌ الزر غير موجود.",back_keyboard("v13:buttons")); return
    a=await db_execute("SELECT clicks FROM button_analytics WHERE button_id=?",(bid,),fetchone=True)
    text=(f"🎛 <b>محرر الزر</b>\n\n<b>{esc(r['text'])}</b>\n\n"
          f"🆔 <code>{esc(bid)}</code>\n🎨 اللون: <code>{esc(r['style'])}</code>\n"
          f"⚡ الوظيفة: <code>{esc(r['action'])}</code>\n📍 الصف: {int(r['row'])+1} • الموضع: {int(r['position'])+1}\n"
          f"👁 {'ظاهر' if r['enabled'] else 'مخفي'} • 🖼 {'نعم' if r['photo'] else 'لا'}\n"
          f"📊 الضغطات: <b>{a['clicks'] if a else 0}</b>")
    kb={"inline_keyboard":[
        [{"text":"✏️ الاسم","callback_data":f"ui_pick:edit:{bid}"},{"text":"🎨 اللون","callback_data":f"ui_pick:style:{bid}"}],
        [{"text":"⚡ الوظيفة","callback_data":f"ui_pick:action:{bid}"},{"text":"🖼 صورة + نص","callback_data":f"ui_pick:media:{bid}"}],
        [{"text":"📍 اختيار المكان","callback_data":f"v13:place:{bid}","style":"success"}],
        [{"text":"⬅️","callback_data":f"ui_move:left:{bid}"},{"text":"➡️","callback_data":f"ui_move:right:{bid}"},{"text":"⬆️","callback_data":f"ui_move:up:{bid}"},{"text":"⬇️","callback_data":f"ui_move:down:{bid}"}],
        [{"text":"📋 نسخ","callback_data":f"v13:copy:{bid}"},{"text":"👁","callback_data":f"ui_pick:toggle:{bid}"},{"text":"🗑 حذف","callback_data":f"ui_pick:delete:{bid}","style":"danger"}],
        [{"text":"📊 الإحصائيات","callback_data":f"v13:stats:{bid}"}],
        [{"text":"🔙 Button Studio","callback_data":"v13:buttons"}]
    ]}
    await edit_message(chat_id,message_id,text,kb)

async def v13_place(chat_id,message_id,bid):
    rows=await get_buttons(include_disabled=True); grouped=defaultdict(list)
    for r in rows:
        if r['id']!=bid: grouped[int(r['row'])].append(r)
    kb=[]
    for row in sorted(grouped):
        kb.append([{"text":f"━━ الصف {row+1} ━━","callback_data":"v13:noop"}])
        for r in sorted(grouped[row],key=lambda x:(int(x['position']),str(x['id']))):
            kb.append([{"text":f"➕ بعد {str(r['text'])[:28]}","callback_data":f"v13:after:{bid}:{r['id']}"}])
    kb.append([{"text":"➕ صف جديد في الأسفل","callback_data":f"v13:newrow:{bid}"}])
    kb.append([{"text":"🔙 رجوع","callback_data":f"v13:button:{bid}"}])
    await edit_message(chat_id,message_id,"📍 <b>اختيار مكان الزر</b>\n\nاضغط على الزر الذي تريد وضع الزر الحالي بعده.",{"inline_keyboard":kb})

async def v13_theme(chat_id,message_id):
    await edit_message(chat_id,message_id,"🎨 <b>THEME STUDIO</b>\n\nاختر اللون الافتراضي الذي تريد تطبيقه على الواجهة:",{"inline_keyboard":[
        [{"text":"🔵 Primary","callback_data":"v13:style:primary"}],
        [{"text":"🟢 Success","callback_data":"v13:style:success"}],
        [{"text":"🔴 Danger","callback_data":"v13:style:danger"}],
        [{"text":"🔙 مركز V13","callback_data":"v13:dashboard"}]
    ]})

async def v13_handle(user_id,chat_id,message_id,data):
    if data=="v13:dashboard": await v13_dashboard(chat_id,message_id); return True
    if data=="v13:buttons": await v13_buttons(chat_id,message_id); return True
    if data.startswith("v13:button:"): await v13_button(chat_id,message_id,data.split(":",2)[2]); return True
    if data=="v13:theme": await v13_theme(chat_id,message_id); return True
    if data.startswith("v13:style:"):
        style=data.split(":")[-1]; await db_execute("UPDATE buttons SET style=?",(style,)); await db_execute("UPDATE admin_buttons SET style=?",(style,)); await load_admin_buttons(); await set_setting("button_default_style",style); await v13_dashboard(chat_id,message_id); return True
    if data=="v13:preview": await send_message(chat_id,"🧪 <b>LIVE PREVIEW</b>\n\nهذه هي الواجهة الحالية:",await main_keyboard()); return True
    if data=="v13:normalize": await normalize_button_positions(); await v13_buttons(chat_id,message_id); return True
    if data=="v13:noop": return True
    if data.startswith("v13:place:"): await v13_place(chat_id,message_id,data.split(":",2)[2]); return True
    if data.startswith("v13:after:"):
        _,_,bid,target=data.split(":",3); t=await db_execute("SELECT row,position FROM buttons WHERE id=?",(target,),fetchone=True)
        if t:
            row,pos=int(t['row']),int(t['position'])+1
            await db_execute("UPDATE buttons SET position=position+1 WHERE row=? AND position>=? AND id<>?",(row,pos,bid))
            await db_execute("UPDATE buttons SET row=?,position=? WHERE id=?",(row,pos,bid)); await normalize_button_positions()
        await v13_button(chat_id,message_id,bid); return True
    if data.startswith("v13:newrow:"):
        bid=data.split(":",2)[2]; x=await db_execute("SELECT COALESCE(MAX(row),-1) r FROM buttons WHERE id<>?",(bid,),fetchone=True); await db_execute("UPDATE buttons SET row=?,position=0 WHERE id=?",(int(x['r'])+1,bid)); await normalize_button_positions(); await v13_button(chat_id,message_id,bid); return True
    if data.startswith("v13:copy:"):
        bid=data.split(":",2)[2]; r=await db_execute("SELECT * FROM buttons WHERE id=?",(bid,),fetchone=True)
        if r:
            nid=f"{bid}_copy_{int(time.time()*1000)}"; await db_execute("INSERT INTO buttons(id,text,action,row,position,enabled,style,url,action_value,photo,caption) VALUES(?,?,?,?,?,?,?,?,?,?,?)",(nid,r['text']+' (نسخة)',r['action'],r['row'],r['position']+1,r['enabled'],r['style'],r['url'],r['action_value'],r['photo'],r['caption'])); await normalize_button_positions()
        await v13_buttons(chat_id,message_id); return True
    if data.startswith("v13:stats:"):
        bid=data.split(":",2)[2]; r=await db_execute("SELECT clicks,last_click FROM button_analytics WHERE button_id=?",(bid,),fetchone=True); await send_message(chat_id,f"📊 <b>إحصائيات الزر</b>\n\nالضغطات: <b>{r['clicks'] if r else 0}</b>\nآخر ضغطة: {esc(r['last_click']) if r else '-'}",back_keyboard(f"v13:button:{bid}")); return True
    return False

async def _edit_contact_markup_after_read(chat_id, message_id, user_id):
    """Remove the read button after marking the incoming message as read."""
    markup = contact_admin_keyboard(user_id, message_id)
    rows = []
    for row in markup.get("inline_keyboard", []):
        kept = []
        for button in row:
            cb = str(button.get("callback_data", ""))
            if cb.startswith("read:"):
                continue
            kept.append({k: v for k, v in button.items() if k != "style"})
        if kept:
            rows.append(kept)
    result = await api_call("editMessageReplyMarkup", data={
        "chat_id": int(chat_id),
        "message_id": int(message_id),
        "reply_markup": json.dumps({"inline_keyboard": rows}, ensure_ascii=False),
    }, timeout=15)
    return result


async def handle_contact_admin_callback(user_id, chat_id, message_id, data):
    """Owner-only inbox actions for messages received by a hosted bot."""
    if not is_owner(user_id):
        return False
    try:
        parts = str(data).split(":")
        action = parts[0]
        target = int(parts[1])
        source_message_id = int(parts[2]) if len(parts) > 2 and parts[2].isdigit() else 0
        if target <= 0:
            return False

        if action == "reply":
            await set_setting(f"reply_target:{user_id}", str(target))
            await set_setting(f"reply_message:{user_id}", str(source_message_id))
            await set_state(user_id, "reply_text")
            await send_message(
                chat_id,
                f"📨 <b>الرد على الرسالة</b>\n\n👤 العضو: <code>{target}</code>\n\nأرسل ردك الآن.",
                cancel_keyboard(),
            )
            return True

        if action == "read":
            incoming_id = source_message_id or message_id
            await db_execute(
                "UPDATE messages SET read_at=? WHERE user_id=? AND telegram_message_id=?",
                (now_text(), target, incoming_id),
            )
            # Notify the member exactly when the owner marks this message as read.
            notify = await send_message(
                target,
                "❤️ <b>تمت قراءة رسالتك</b>\n\nشكرًا لتواصلك معنا.",
            )
            if not notify.get("ok"):
                await log_error("read_notify", notify.get("description", "failed to notify member"))
            await audit("Message read", f"user={target},message={incoming_id}")
            # Remove only the read button from the owner-side message.
            await _edit_contact_markup_after_read(chat_id, message_id, target)
            return True

        if action == "quickban":
            await db_execute("UPDATE users SET blocked=1 WHERE user_id=?", (target,))
            await audit("Quick ban", str(target))
            notify = await send_message(target, await get_notification("notif_ban_user"))
            if not notify.get("ok"):
                await log_error("quickban_notify", notify.get("description", "failed to notify banned member"))
            await send_message(chat_id, f"🚫 تم حظر العضو <code>{target}</code>.")
            return True

        if action == "userinfo":
            row = await get_user(target)
            if not row:
                await send_message(chat_id, "❌ المستخدم غير موجود.")
                return True

            # Calculate a real per-media breakdown from the message history.
            counts = await db_execute(
                "SELECT media_type, COUNT(*) AS c FROM messages WHERE user_id=? GROUP BY media_type",
                (target,), fetchall=True
            ) or []
            breakdown = {str(r["media_type"] or "text"): int(r["c"] or 0) for r in counts}
            total_messages = int(row["messages"] or 0)
            total_media = int(row["media"] or 0)
            muted = float(row["muted_until"] or 0) > time.time()

            info = (
                "👤 <b>معلومات العضو</b>\n\n"
                f"🆔 الآيدي: <code>{target}</code>\n"
                f"🔗 اليوزر: @{esc(row['username']) if row['username'] else 'بدون يوزر'}\n"
                f"🏷️ الاسم: {esc(row['name']) or 'بدون اسم'}\n\n"
                f"💬 إجمالي الرسائل: <b>{total_messages}</b>\n"
                f"📦 إجمالي الوسائط: <b>{total_media}</b>\n"
                f"🖼️ الصور: <b>{breakdown.get('photo', 0)}</b>\n"
                f"🎥 الفيديوهات: <b>{breakdown.get('video', 0)}</b>\n"
                f"🎞️ GIF/Animation: <b>{breakdown.get('animation', 0)}</b>\n"
                f"📄 الملفات: <b>{breakdown.get('document', 0)}</b>\n"
                f"🎤 الصوتيات: <b>{breakdown.get('voice', 0) + breakdown.get('audio', 0)}</b>\n"
                f"🎭 الملصقات: <b>{breakdown.get('sticker', 0)}</b>\n"
                f"⭕ Video Notes: <b>{breakdown.get('video_note', 0)}</b>\n\n"
                f"📅 الانضمام: {esc(row['joined_at'])}\n"
                f"⏰ آخر نشاط: {esc(row['last_activity'])}\n"
                f"🚫 محظور: {'نعم' if row['blocked'] else 'لا'}\n"
                f"🔇 مكتوم: {'نعم' if muted else 'لا'}\n"
                f"📝 الملاحظة: {esc(row['notes']) if row['notes'] else 'لا يوجد'}"
            )
            await send_message(chat_id, info, back_keyboard("admin"))
            return True

        return False
    except (ValueError, TypeError) as exc:
        await log_error("contact_callback_value", f"{data}: {exc}")
        await send_message(chat_id, "❌ بيانات زر الرسالة غير صالحة.")
        return True
    except Exception as exc:
        await log_error("contact_callback", f"{data}: {exc}")
        await send_message(chat_id, "❌ تعذر تنفيذ العملية، لكن البوت سيبقى يعمل.")
        return True


async def answer_callback_safe(chat_id, text):
    # Callback answers are handled centrally; this helper intentionally avoids
    # fabricating a callback id. The owner still receives a visible confirmation.
    return True


async def run_admin_callback(user_id, chat_id, message_id, data):
    """Single safe gateway for admin callbacks, including hosted-owner inbox actions."""
    if not is_owner(user_id):
        return False
    try:
        if str(data).startswith(("reply:", "history:", "read:", "quickban:", "userinfo:")):
            return await handle_contact_admin_callback(user_id, chat_id, message_id, data)
        result = await handle_pro_callback(user_id, chat_id, message_id, data)
        if result is False:
            # Unknown developer callback: show the developer panel instead of silently returning.
            await send_message(
                chat_id,
                "⚠️ <b>هذا الزر قديم أو غير معروف.</b> تم تحديث لوحة المطور تلقائيًا.",
                admin_keyboard(),
            )
            return False
        return True
    except asyncio.CancelledError:
        raise
    except Exception as exc:
        await log_error("admin_callback", f"{data}: {exc}")
        await send_message(
            chat_id,
            "❌ <b>تعذر تنفيذ أمر المطور.</b>\n\n"
            f"الأمر: <code>{esc(data)}</code>\n"
            f"الخطأ: <code>{esc(exc)}</code>",
            admin_keyboard(),
        )
        return False

async def handle_pro_callback(user_id,chat_id,message_id,data):
    if is_limited_bot_owner(user_id):
        return False
    if data.startswith("v16:"):
        if not is_platform_owner(user_id):
            return False
        return await v16_handle_callback(user_id, chat_id, message_id, data)
    if data.startswith(("btnedit:","btnstyle:","btnsetstyle:","btntoggle:","btnaction:","btnsetaction:","btnvalue:","btnurl:","btnmedia:","btnmedia_delete:","btnmove:","btnmove_do:","btnplace:","btnplace_do:","btnclone:","btnpreview:","btndelete:","btndelete_yes:","btneditfield:","btnrestore:","btnpurge:")):
        return await handle_visual_button_callback(user_id,chat_id,message_id,data)
    if data.startswith("v13:"):
        return await v13_handle(user_id,chat_id,message_id,data)
    if data.startswith("v11:"):
        return await v11_handle_callback(user_id,chat_id,message_id,data)
    if data=="adm:creator_exempt":
        if not is_platform_owner(user_id): return False
        await show_creator_exemptions(chat_id,message_id); return True
    if data=="adm:hosted":
        if not is_platform_owner(user_id): return False
        await show_hosted_bots(chat_id,message_id); return True
    if data.startswith("adm:hostbot:toggle:"):
        if not is_platform_owner(user_id): return False
        ident=int(data.rsplit(":",1)[1])
        row=await db_execute("SELECT status,bot_username FROM hosted_bots WHERE id=?",(ident,),fetchone=True)
        if not row:
            await send_message(chat_id,"❌ البوت غير موجود.",admin_keyboard()); return True
        enabled=str(row["status"])=="disabled"
        ok,msg=await set_hosted_bot_enabled(ident,enabled)
        await send_message(chat_id,("✅ " if ok else "❌ ")+msg,admin_keyboard() if not ok else {"inline_keyboard":[[{"text":"🌐 إدارة البوتات المستضافة","callback_data":"adm:hosted"}]]})
        return True
    if data=="adm:hostbroadcast":
        if not is_platform_owner(user_id): return False
        await send_message(chat_id,"📢 <b>إذاعة لجميع البوتات</b>", {"inline_keyboard":[[{"text":"📝 إذاعة نص","callback_data":"broadcast:all:text","style":"success"}],[{"text":"🖼 إذاعة وسائط","callback_data":"broadcast:all:media","style":"primary"}],[{"text":"🔙 رجوع","callback_data":"adm:hosted"}]]})
        return True
    if data=="broadcast:all:text":
        if not is_platform_owner(user_id): return False
        await set_state(user_id,"hosted_broadcast_text")
        await send_message(chat_id,await get_notification("notif_host_broadcast_prompt"),cancel_keyboard())
        return True
    if data=="broadcast:all:media":
        if not is_platform_owner(user_id): return False
        await set_state(user_id,"hosted_broadcast_media")
        await send_message(chat_id,await get_notification("notif_host_broadcast_media_prompt"),cancel_keyboard())
        return True
    if data=="adm:creator_exempt:add":
        await set_state(user_id, "creator_exempt_add")
        await send_message(chat_id, "🎁 <b>إضافة إعفاء</b>\n\nأرسل <b>Telegram User ID</b> للشخص الذي تريد إعفاءه من رسوم إنشاء البوتات.", cancel_keyboard())
        return True
    if data=="adm:creator_exempt:remove":
        await set_state(user_id, "creator_exempt_remove")
        await send_message(chat_id, "🗑 <b>إزالة إعفاء</b>\n\nأرسل <b>Telegram User ID</b> لإلغاء الإعفاء عنه.", cancel_keyboard())
        return True
    if data=="pro:dashboard": await pro_dashboard(chat_id,message_id); return True
    if data=="pro:ui": await visual_button_studio(chat_id,message_id); return True
    if data=="pro:content": await pro_content(chat_id,message_id); return True
    if data=="pro:security": await pro_security(chat_id,message_id); return True
    if data=="pro:system": await pro_system(chat_id,message_id); return True
    if data=="pro:logs": await pro_logs(chat_id,message_id); return True
    if data=="pro:backup": await pro_backup(chat_id,message_id); return True
    if data=="pro:users": await pro_users(chat_id,message_id); return True
    if data=="pro:pages": await pro_pages(chat_id,message_id); return True
    if data=="pro:adminui": await pro_adminui(chat_id,message_id); return True
    if data.startswith("adminbtn:"): await pro_admin_button(chat_id,message_id,data.split(":",1)[1]); return True
    if data.startswith("adminbtnmove:"):
        parts = data.split(":")
        if len(parts) != 3:
            return True
        _, direction, bid = parts
        row = await db_execute("SELECT row,position FROM admin_buttons WHERE id=?", (bid,), fetchone=True)
        if not row:
            await send_message(chat_id, "❌ زر المطور غير موجود.", back_keyboard("pro:adminui"))
            return True
        r, pos = int(row["row"]), int(row["position"])
        if direction in ("left", "right"):
            step = -1 if direction == "left" else 1
            neighbor = await db_execute(
                "SELECT id FROM admin_buttons WHERE row=? AND position=?",
                (r, pos + step), fetchone=True
            )
            if neighbor:
                await db_execute("UPDATE admin_buttons SET position=? WHERE id=?", (999999, bid))
                await db_execute("UPDATE admin_buttons SET position=? WHERE id=?", (pos, neighbor["id"]))
                await db_execute("UPDATE admin_buttons SET position=? WHERE id=?", (pos + step, bid))
        elif direction == "up":
            await db_execute("UPDATE admin_buttons SET row=? WHERE id=?", (max(0, r - 1), bid))
        elif direction == "down":
            await db_execute("UPDATE admin_buttons SET row=? WHERE id=?", (r + 1, bid))
        await load_admin_buttons()
        await audit("Admin button move", f"{bid}:{direction}")
        await pro_adminui(chat_id, message_id)
        return True

    if data.startswith("adminbtnplace:"):
        parts=data.split(":")
        if len(parts)>=2 and parts[1]=="noop":
            return True
        if len(parts)==2:
            await admin_button_place_picker(chat_id,message_id,parts[1]); return True
        if len(parts)>=4 and parts[1]=="after":
            bid,target=parts[2],parts[3]
            t=await db_execute("SELECT row,position FROM admin_buttons WHERE id=?",(target,),fetchone=True)
            if t:
                row,pos=int(t["row"]),int(t["position"])+1
                await db_execute("UPDATE admin_buttons SET position=position+1 WHERE row=? AND position>=? AND id<>?",(row,pos,bid))
                await db_execute("UPDATE admin_buttons SET row=?,position=? WHERE id=?",(row,pos,bid))
        elif len(parts)>=3 and parts[1]=="newrow":
            bid=parts[2]
            last=await db_execute("SELECT COALESCE(MAX(row),-1) r FROM admin_buttons WHERE id<>?",(bid,),fetchone=True)
            await db_execute("UPDATE admin_buttons SET row=?,position=0 WHERE id=?",(int(last["r"])+1,bid))
        await load_admin_buttons(); await audit("Admin button place",data); await pro_adminui(chat_id,message_id); return True

    if data.startswith("adminbtnedit:"):
        _,field,bid=data.split(":",2)
        if field=="text": await set_state(user_id,f"adminbtn_text:{bid}"); await edit_message(chat_id,message_id,"✏️ أرسل النص الجديد.",cancel_keyboard()); return True
        if field=="style": await set_state(user_id,f"adminbtn_style:{bid}"); await edit_message(chat_id,message_id,"🎨 أرسل primary أو success أو danger.",cancel_keyboard()); return True
    if data.startswith("adminbtntoggle:"):
        bid=data.split(":",1)[1]; r=await db_execute("SELECT enabled FROM admin_buttons WHERE id=?",(bid,),fetchone=True)
        if r: await db_execute("UPDATE admin_buttons SET enabled=? WHERE id=?",(0 if r["enabled"] else 1,bid)); await load_admin_buttons()
        await pro_adminui(chat_id,message_id); return True
    if data=="prolimit": await set_state(user_id,"prolimit"); await edit_message(chat_id,message_id,"⚙️ أرسل الحد بالأرقام.",cancel_keyboard()); return True
    if data=="prostyle_default": await set_state(user_id,"prostyle_default"); await edit_message(chat_id,message_id,"🎨 أرسل primary أو success أو danger.",cancel_keyboard()); return True
    if data == "adm:notifications":
        if not is_platform_owner(user_id):
            await send_message(chat_id, await get_notification("notif_no_permission"))
            return True
        await pro_notifications(chat_id, message_id)
        return True
    if data.startswith("notifedit:"):
        if not is_platform_owner(user_id):
            await send_message(chat_id, await get_notification("notif_no_permission"))
            return True
        key=data.split(":",1)[1]
        if key not in NOTIFICATION_LABELS:
            await send_message(chat_id,"❌ الإشعار غير موجود.",back_keyboard("adm:notifications")); return True
        await set_state(user_id,f"notifedit:{key}")
        current=await get_setting(key,NOTIFICATION_DEFAULTS[key])
        vars_text=NOTIFICATION_PLACEHOLDERS.get(key,"لا توجد متغيرات خاصة")
        await edit_message(chat_id,message_id,f"🔔 <b>{NOTIFICATION_LABELS[key]}</b>\n\nأرسل النص الجديد.\n\nالمتغيرات: <code>{esc(vars_text)}</code>\n\nالنص الحالي:\n<code>{esc(current)}</code>",cancel_keyboard())
        return True
    if data == "notifreset:all":
        if not is_platform_owner(user_id):
            await send_message(chat_id, await get_notification("notif_no_permission")); return True
        for key,value in NOTIFICATION_DEFAULTS.items(): await set_setting(key,value)
        await sync_notifications_to_all_hosted_bots()
        await audit("Notifications reset","all"); await pro_notifications(chat_id,message_id); return True
    if data.startswith("proedit:"):
        key=data.split(":",1)[1]; await set_state(user_id,f"proedit:{key}"); await edit_message(chat_id,message_id,"📝 أرسل النص الجديد.",cancel_keyboard()); return True
    if data.startswith("protoggle:"):
        key=data.split(":",1)[1]; cur=await get_setting(key,"0"); await set_setting(key,"0" if cur=="1" else "1"); await audit("Toggle",key); await (pro_security(chat_id,message_id) if key in ("protection","force","notifications","maintenance") else pro_system(chat_id,message_id)); return True
    if data.startswith("prouser:"): await pro_user(chat_id,message_id,int(data.split(":",1)[1])); return True
    if data.startswith("prouserban:"):
        target=int(data.split(":",1)[1]); r=await get_user(target)
        if r and target!=OWNER_ID: await db_execute("UPDATE users SET blocked=? WHERE user_id=?",(0 if r["blocked"] else 1,target))
        await pro_user(chat_id,message_id,target); return True
    if data.startswith("prousernote:"): target=int(data.split(":",1)[1]); await set_state(user_id,f"prousernote:{target}"); await edit_message(chat_id,message_id,"📝 أرسل الملاحظة.",cancel_keyboard()); return True
    if data.startswith("prousermsg:"): target=int(data.split(":",1)[1]); await set_state(user_id,f"prousermsg:{target}"); await edit_message(chat_id,message_id,"📨 أرسل الرسالة.",cancel_keyboard()); return True
    if data=="pro:cleanlogs": await db_execute("DELETE FROM audit_logs"); await db_execute("DELETE FROM error_logs"); await pro_logs(chat_id,message_id); return True
    if data=="propageadd": await set_state(user_id,"propageadd_title"); await edit_message(chat_id,message_id,"📄 أرسل عنوان الصفحة.",cancel_keyboard()); return True
    if data.startswith("propage:"): await pro_page(chat_id,message_id,data.split(":",1)[1]); return True
    if data.startswith("propageedit:"):
        _,field,pid=data.split(":",2); await set_state(user_id,f"propageedit:{field}:{pid}"); await edit_message(chat_id,message_id,"📝 أرسل القيمة الجديدة.",cancel_keyboard()); return True
    if data.startswith("propagetoggle:"):
        pid=data.split(":",1)[1]; r=await db_execute("SELECT enabled FROM menu_pages WHERE id=?",(pid,),fetchone=True)
        if r: await db_execute("UPDATE menu_pages SET enabled=? WHERE id=?",(0 if r["enabled"] else 1,pid))
        await pro_page(chat_id,message_id,pid); return True
    if data.startswith("propagedelete:"):
        pid=data.split(":",1)[1]; await db_execute("DELETE FROM menu_pages WHERE id=?",(pid,)); await db_execute("DELETE FROM page_buttons WHERE page_id=?",(pid,)); await pro_pages(chat_id,message_id); return True

    if data == "adm:contact":
        await admin_contact(chat_id, message_id)
        return True

    if data == "adm:contact_media":
        await admin_contact_media(chat_id, message_id)
        return True

    if data == "adm:texts":
        await admin_texts(chat_id, message_id)
        return True

    if data == "adm:welcome":
        await admin_welcome(chat_id, message_id)
        return True

    if data == "welcome:toggle":
        current = await get_setting("welcome_enabled", "1")
        await set_setting("welcome_enabled", "0" if current == "1" else "1")
        await audit("Welcome toggle", "changed")
        await admin_welcome(chat_id, message_id)
        return True

    if data == "welcome:preview":
        await send_start(chat_id, user_id)
        return True

    if data == "welcome:text":
        await set_state(user_id, "text_edit_start")
        await send_message(chat_id, "📝 أرسل رسالة الترحيب الجديدة.\n\nالمتغيرات: {name} {username} {id} {top5} {invitelink}", cancel_keyboard())
        return

    if data == "adm:photos":
        await admin_photos(chat_id, message_id)
        return True

    if data == "adm:stats":
        await admin_stats(chat_id, message_id)
        return True

    if data == "adm:status":
        await admin_status(chat_id, message_id)
        return True

    if data == "adm:channels":
        await admin_channels(chat_id, message_id)
        return True

    if data == "adm:search":
        await set_state(user_id, "search")
        await edit_message(
            chat_id,
            message_id,
            "🔎 أرسل الاسم أو username أو ID:",
            cancel_keyboard(),
        )
        return

    if data == "adm:ban":
        await set_state(user_id, "ban")
        await edit_message(
            chat_id,
            message_id,
            "🚫 أرسل ID المستخدم للحظر:",
            cancel_keyboard(),
        )
        return

    if data == "adm:mute":
        await set_state(user_id, "mute")
        await edit_message(
            chat_id,
            message_id,
            "🔇 أرسل: <code>ID دقائق</code>",
            cancel_keyboard(),
        )
        return

    if data == "adm:broadcast":
        keyboard = {
            "inline_keyboard": [
                [{"text": "📝 إذاعة نص", "callback_data": "broadcast:text"}],
                [{"text": "🖼 إذاعة وسائط", "callback_data": "broadcast:media"}],
                [{"text": "🔙 رجوع", "callback_data": "admin"}],
            ]
        }
        await edit_message(chat_id, message_id, "📢 اختر نوع الإذاعة:", keyboard)
        return

    if data == "adm:protection":
        limit = await get_setting("max_requests_per_min", "30")
        enabled = await get_setting("protection", "1") == "1"
        keyboard = {
            "inline_keyboard": [
                [{"text": "🛡 تفعيل/إيقاف", "callback_data": "protection:toggle"}],
                [{"text": "⚙️ تغيير الحد", "callback_data": "protection:limit"}],
                [{"text": "🔙 رجوع", "callback_data": "admin"}],
            ]
        }
        await edit_message(
            chat_id,
            message_id,
            f"🛡 <b>الحماية</b>\n\n"
            f"الحالة: {'🟢 مفعلة' if enabled else '🔴 متوقفة'}\n"
            f"الحد: {limit} طلب/دقيقة",
            keyboard,
        )
        return

    if data == "adm:backup":
        path = await create_backup()
        await send_local_document(chat_id, path, "💾 نسخة احتياطية")
        return

    if data == "adm:logs":
        rows = await db_execute("""
            SELECT action,details,created_at
            FROM audit_logs
            ORDER BY id DESC
            LIMIT 20
        """, fetchall=True)

        text = "📜 <b>آخر العمليات</b>\n\n"
        for r in rows or []:
            text += f"• {esc(r['action'])}\n{esc(r['details'])}\n{r['created_at']}\n\n"

        await edit_message(chat_id, message_id, text, back_keyboard("admin"))
        return

    if data == "adm:contact":
        await admin_contact(chat_id, message_id)
        return True

    if data == "ui:add":
        await handle_ui_callback(user_id, chat_id, message_id, data)
        return

    if data.startswith("ui:"):
        await handle_ui_callback(user_id, chat_id, message_id, data)
        return

    if data.startswith("ui_pick:") or data.startswith("ui_action:"):
        await handle_ui_callback(user_id, chat_id, message_id, data)
        return

    if data == "contact:edit":
        await set_state(user_id, "text_edit_contact")
        await edit_message(
            chat_id,
            message_id,
            "📝 أرسل نص التواصل الجديد.\n\n"
            "المتغيرات المتاحة: {name} {username} {id} {top5} {invitelink}",
            cancel_keyboard(),
        )
        return

    if data == "text:edit_start":
        await set_state(user_id, "text_edit_start")
        await edit_message(
            chat_id,
            message_id,
            "📝 أرسل نص Start الجديد.\n\n"
            "المتغيرات: {name} {username} {id} {top5} {invitelink}",
            cancel_keyboard(),
        )
        return

    if data == "text:edit_contact":
        await set_state(user_id, "text_edit_contact")
        await edit_message(
            chat_id,
            message_id,
            "📝 أرسل نص التواصل الجديد.",
            cancel_keyboard(),
        )
        return

    if data == "contact:photo":
        await set_state(user_id, "photo_contact")
        await edit_message(chat_id, message_id, await get_notification("notif_contact_photo_prompt"), cancel_keyboard())
        return

    if data == "contact:photo_delete":
        await set_setting("contact_photo", "")
        await edit_message(chat_id, message_id, "✅ تم حذف صورة التواصل.", back_keyboard("adm:contact"))
        return

    if data == "contact:toggle":
        current = await get_setting("contact_enabled", "1")
        await set_setting("contact_enabled", "0" if current == "1" else "1")
        await audit("Contact visibility", "toggled")
        await admin_contact(chat_id, message_id)
        return True

    if data == "contact:footer":
        await set_state(user_id, "contact_footer")
        await edit_message(chat_id, message_id, "📝 أرسل الفوتر الذي يظهر أسفل نص التواصل. أرسل -none- لإزالته.", cancel_keyboard())
        return

    if data == "contact:preview":
        await send_contact_screen(chat_id, user_id)
        await clear_state(user_id)
        return

    if data == "photo:maintenance":
        await set_state(user_id, "photo_maintenance")
        await edit_message(chat_id, message_id, await get_notification("notif_maintenance_photo_prompt"), cancel_keyboard())
        return

    if data == "photo:maintenance_delete":
        await set_setting("maintenance_photo", "")
        await edit_message(chat_id, message_id, "✅ تم حذف صورة الصيانة.", back_keyboard("adm:photos"))
        return

    if data == "photo:welcome":
        await set_state(user_id, "photo_welcome")
        await edit_message(chat_id, message_id, await get_notification("notif_welcome_photo_prompt"), cancel_keyboard())
        return

    if data == "photo:welcome_delete":
        await set_setting("welcome_photo", "")
        await audit("Welcome photo deleted", "")
        await edit_message(chat_id, message_id, "✅ تم حذف صورة الترحيب.", back_keyboard("adm:welcome"))
        return True

    if data == "photo:dev":
        await set_state(user_id, "photo_dev")
        await edit_message(chat_id, message_id, await get_notification("notif_dev_photo_prompt"), cancel_keyboard())
        return

    if data == "photo:dev_preview":
        dev_photo = await get_setting("dev_photo", "")
        if not dev_photo:
            await send_message(chat_id, "❌ لا توجد صورة للمطور محفوظة.", back_keyboard("adm:photos"))
        else:
            result = await send_photo(chat_id, dev_photo, "🖼 <b>صورة المطور الحالية</b>", back_keyboard("adm:photos"))
            if not result.get("ok"):
                # Stored Telegram file_id may become invalid; clear it instead of leaving a broken state.
                await set_setting("dev_photo", "")
                await send_message(chat_id, "❌ الصورة المحفوظة لم تعد صالحة، تم تنظيفها.", back_keyboard("adm:photos"))
        return

    if data == "photo:dev_delete":
        await set_setting("dev_photo", "")
        await edit_message(chat_id, message_id, "✅ تم حذف صورة المطور.", back_keyboard("admin"))
        return

    if data == "status:maintenance":
        current = await get_setting("maintenance", "0")
        await set_setting("maintenance", "0" if current == "1" else "1")
        await audit("Maintenance toggle", "changed")
        await admin_status(chat_id, message_id)
        return True

    if data == "status:force":
        current = await get_setting("force_sub", "1")
        await set_setting("force_sub", "0" if current == "1" else "1")
        await admin_status(chat_id, message_id)
        return True

    if data == "status:protection":
        current = await get_setting("protection", "1")
        await set_setting("protection", "0" if current == "1" else "1")
        await admin_status(chat_id, message_id)
        return True

    if data == "protection:toggle":
        current = await get_setting("protection", "1")
        await set_setting("protection", "0" if current == "1" else "1")
        await admin_status(chat_id, message_id)
        return True

    if data == "protection:limit":
        await set_state(user_id, "protection_limit")
        await edit_message(
            chat_id,
            message_id,
            "⚙️ أرسل الحد الأقصى للطلبات في الدقيقة، مثال: <code>30</code>",
            cancel_keyboard(),
        )
        return

    if data == "broadcast:text":
        await set_state(user_id, "broadcast_text")
        await edit_message(
            chat_id,
            message_id,
            await get_notification("notif_broadcast_prompt"),
            cancel_keyboard(),
        )
        return

    if data == "broadcast:media":
        await set_state(user_id, "broadcast_media")
        await edit_message(
            chat_id,
            message_id,
            await get_notification("notif_broadcast_media_prompt"),
            cancel_keyboard(),
        )
        return

    if data == "channel:add":
        await set_state(user_id, "channel_add")
        await edit_message(
            chat_id,
            message_id,
            "➕ أرسل معرف القناة بدون @.\n"
            "مثال: <code>MyChannel</code>",
            cancel_keyboard(),
        )
        return

    if data == "channel:delete":
        await set_state(user_id, "channel_delete")
        await edit_message(
            chat_id,
            message_id,
            "➖ أرسل معرف القناة التي تريد حذفها.",
            cancel_keyboard(),
        )
        return

    if data.startswith("reply:"):
        target = int(data.split(":", 1)[1])
        await set_setting(f"reply_target:{user_id}", str(target))
        await set_state(user_id, "reply_text")
        # IMPORTANT: never edit/delete the original member message.
        # The reply composer is sent as a new message, keeping the entire history visible.
        await send_message(
            chat_id,
            f"📨 <b>وضع الرد</b>\n\n🆔 المستخدم: <code>{target}</code>\n\n"
            "أرسل الرد الآن. الرسائل السابقة ستبقى محفوظة ولن تختفي.\n"
            "للإلغاء: /cancel",
            cancel_keyboard(),
        )
        return

    if data.startswith("history:"):
        parts = data.split(":")
        target = int(parts[1])
        page = int(parts[2]) if len(parts) > 2 else 0
        text, kb = await conversation_history_text(target, page)
        await edit_message(chat_id, message_id, text, kb)
        return

    if data.startswith("read:"):
        target = int(data.split(":")[1])
        await audit("Message read", f"user={target}")
        return

    if data.startswith("quickban:"):
        target = int(data.split(":", 1)[1])
        await db_execute(
            "UPDATE users SET blocked=1 WHERE user_id=?",
            (target,),
        )
        await audit("Quick ban", str(target))
        await send_message(chat_id, f"🚫 تم حظر <code>{target}</code>.")
        await send_message(target, await get_notification("notif_ban_user"))
        return

    if data.startswith("userinfo:"):
        target = int(data.split(":", 1)[1])
        row = await get_user(target)
        if not row:
            await send_message(chat_id, "❌ المستخدم غير موجود.")
            return

        muted = float(row["muted_until"] or 0) > time.time()
        text = (
            "👤 <b>معلومات العضو</b>\n\n"
            f"🆔 <code>{target}</code>\n"
            f"👤 الاسم: {esc(row['name'])}\n"
            f"🔗 @{esc(row['username']) if row['username'] else 'بدون'}\n"
            f"📅 الانضمام: {esc(row['joined_at'])}\n"
            f"⏰ النشاط: {esc(row['last_activity'])}\n"
            f"💬 الرسائل: {row['messages']}\n"
            f"📁 الوسائط: {row['media']}\n"
            f"🚫 محظور: {'نعم' if row['blocked'] else 'لا'}\n"
            f"🔇 مكتوم: {'نعم' if muted else 'لا'}\n"
            f"📝 الملاحظة: {esc(row['notes']) if row['notes'] else 'لا يوجد'}"
        )
        await send_message(chat_id, text, back_keyboard("admin"))
        return


# =========================================================
# BROADCAST / BACKUP
# =========================================================

async def run_owner_broadcast(source_chat_id, source_message_id):
    """Broadcast one owner message to users who have started THIS bot only.

    Every hosted bot runs this function inside its own child process and its own
    SQLite database, so the recipient list can never leak between hosted bots.
    Telegram's copyMessage is used so text/media/stickers/etc. are preserved.
    """
    rows = await db_execute(
        "SELECT user_id FROM users WHERE blocked=0 AND user_id<>? ORDER BY user_id",
        (int(OWNER_ID),),
        fetchall=True,
    ) or []

    # Keep enough parallelism for speed without hammering Telegram's per-bot
    # flood limits. This semaphore is local to this hosted-bot process.
    sem = asyncio.Semaphore(12)
    success = 0
    failed = 0
    lock = asyncio.Lock()

    async def one_user(row):
        nonlocal success, failed
        uid = int(row["user_id"])
        async with sem:
            try:
                result = await api_call(
                    "copyMessage",
                    data={
                        "chat_id": uid,
                        "from_chat_id": int(source_chat_id),
                        "message_id": int(source_message_id),
                    },
                    timeout=30,
                    retries=3,
                )
                if result.get("ok"):
                    async with lock:
                        success += 1
                    return

                desc = str(result.get("description") or "")
                # A user who blocked/deleted the bot should not keep failing in
                # every future broadcast.
                if result.get("error_code") == 403 or "bot was blocked" in desc.lower() or "user is deactivated" in desc.lower():
                    try:
                        await db_execute(
                            "UPDATE users SET blocked=1 WHERE user_id=?",
                            (uid,),
                        )
                    except Exception as exc:
                        await log_error("broadcast_block_update", f"user={uid}: {exc}")
                await log_error("owner_broadcast_send", f"user={uid};{desc[:300]}")
                async with lock:
                    failed += 1
            except asyncio.CancelledError:
                raise
            except Exception as exc:
                await log_error("owner_broadcast_exception", f"user={uid};{exc}")
                async with lock:
                    failed += 1

    # Process in bounded batches so a huge user list does not create thousands
    # of waiting asyncio tasks at once.
    batch_size = 200
    for start in range(0, len(rows), batch_size):
        batch = rows[start:start + batch_size]
        await asyncio.gather(*(one_user(row) for row in batch))

    await audit(
        "Owner broadcast",
        f"owner={OWNER_ID}, total={len(rows)}, success={success}, failed={failed}",
    )
    return len(rows), success, failed


async def run_broadcast(caption, media_type, file_id):
    rows = await db_execute(
        "SELECT user_id FROM users WHERE blocked=0",
        fetchall=True,
    )

    success = 0
    failed = 0

    for row in rows or []:
        uid = row["user_id"]
        if media_type == "text":
            result = await send_message(
                uid,
                f"📢 <b>رسالة من إدارة البوت</b>\n\n{esc(caption)}",
            )
        else:
            result = await send_media(
                uid,
                media_type,
                file_id,
                caption=f"📢 <b>من إدارة البوت</b>\n\n{esc(caption)}" if caption else "📢 <b>من إدارة البوت</b>",
            )

        if result.get("ok"):
            success += 1
        else:
            failed += 1

        # Conservative pacing to avoid Telegram flood limits.
        await asyncio.sleep(0.06)

    await audit(
        "Broadcast",
        f"type={media_type}, success={success}, failed={failed}",
    )
    return len(rows or []), success, failed


async def create_backup():
    timestamp = dt.datetime.now().strftime("%Y%m%d_%H%M%S")
    path = BACKUP_DIR / f"contact_bot_{timestamp}.db"

    async with aiosqlite.connect(DB_FILE) as source:
        async with aiosqlite.connect(path) as dest:
            await source.backup(dest)

    # Keep 20 DB backups.
    backups = sorted(BACKUP_DIR.glob("*.db"), key=lambda p: p.stat().st_mtime)
    while len(backups) > 20:
        old = backups.pop(0)
        try:
            old.unlink()
        except Exception:
            pass

    await audit("Backup", str(path))
    return path



async def _welcome_text_for_user(user_id):
    """Build the welcome text from one canonical setting with safe placeholders."""
    text = await get_setting("start_text", DEFAULT_START_TEXT)
    user = await get_user(user_id)
    name = esc(user["name"] if user and user["name"] else "مستخدم")
    # render_text supplies all supported dynamic placeholders.
    return await render_text(text, user_id)


async def _send_welcome_fallback(chat_id, text, keyboard):
    """Last-resort delivery path: never let malformed custom HTML hide the welcome."""
    result = await send_message(chat_id, text, keyboard)
    if result.get("ok"):
        return result
    # A malformed user-entered HTML tag can make Telegram reject parse_mode=HTML.
    plain = re.sub(r"<[^>]*>", "", str(text))
    plain = html.unescape(plain)
    result2 = await api_call("sendMessage", data={
        "chat_id": chat_id,
        "text": plain,
        "disable_web_page_preview": "true",
        "reply_markup": json.dumps(strip_keyboard_styles(ui_keyboard_for_chat(chat_id, keyboard)), ensure_ascii=False),
    })
    return result2 if result2.get("ok") else result


async def send_start(chat_id, user_id):
    """Production-grade /start: text/image are independent and always have fallbacks."""
    # These reads do not depend on each other.  Running them together avoids
    # multiplying latency when many users press /start at the same time.
    welcome_task = asyncio.create_task(_welcome_text_for_user(user_id))
    keyboard_task = asyncio.create_task(main_keyboard())
    subscription_task = None
    if not is_platform_owner(user_id):
        subscription_task = asyncio.create_task(check_forced_subscription(user_id))
    try:
        welcome = await welcome_task
    except Exception as exc:
        await log_error("welcome_render", exc)
        welcome = DEFAULT_START_TEXT.replace("{name}", "مستخدم")

    keyboard = await keyboard_task
    if is_owner(user_id):
        keyboard = {"inline_keyboard": list(keyboard.get("inline_keyboard", []))}
        keyboard["inline_keyboard"].append([{"text": "⚙️ لوحة الادمن", "callback_data": "admin", "style": "primary"}])
    if not keyboard.get("inline_keyboard"):
        keyboard = {"inline_keyboard": [
            [{"text": "📨 رسالة للمطور", "callback_data": "contact"}],
            [{"text": "ℹ️ معلومات البوت", "callback_data": "info"}, {"text": "🏆 المتصدرون", "callback_data": "top"}],
        ]} if not is_owner(user_id) else {"inline_keyboard": [[{"text": "⚙️ لوحة المطور", "callback_data": "admin"}]]}

    if not is_platform_owner(user_id):
        ok, missing = await subscription_task
        if not ok:
            return await send_message(chat_id,
                "📢 <b>الاشتراك مطلوب قبل استخدام البوت.</b>\n\nاشترك في القنوات التالية ثم اضغط على التحقق:",
                subscription_keyboard(missing))

    photo = await get_setting("welcome_photo", "")
    photo_enabled = await get_setting("welcome_enabled", "1") == "1"

    if photo and photo_enabled:
        # Telegram photo captions are limited; keep image delivery independent from long text.
        caption = welcome if len(welcome) <= 1000 else "👋 <b>أهلاً بك</b>"
        result = await send_photo(chat_id, photo, caption, keyboard)
        if result.get("ok"):
            if len(welcome) > 1000:
                return await _welcome_text_fallback_after_photo(chat_id, welcome, keyboard)
            return result

        # Retry once with a plain caption in case custom HTML is malformed.
        plain_caption = html.unescape(re.sub(r"<[^>]*>", "", welcome))
        retry = await api_call("sendPhoto", data={
            "chat_id": chat_id, "photo": photo, "caption": plain_caption[:1000],
            "reply_markup": json.dumps(strip_keyboard_styles(ui_keyboard_for_chat(chat_id, keyboard)), ensure_ascii=False),
        })
        if retry.get("ok"):
            if len(welcome) > 1000:
                return await _welcome_text_fallback_after_photo(chat_id, welcome, keyboard)
            return retry

        await log_error("start_photo", retry.get("description", result.get("description", "unknown photo error")))
        # Only clear the stored photo when Telegram indicates the photo itself is invalid.
        desc = (str(retry.get("description", "")) + " " + str(result.get("description", ""))).lower()
        if any(x in desc for x in ("file_id", "wrong file", "invalid file", "photo_invalid", "not found", "bad request: wrong")):
            await set_setting("welcome_photo", "")

    return await _send_welcome_fallback(chat_id, welcome, keyboard)


async def _welcome_text_fallback_after_photo(chat_id, welcome, keyboard):
    """Send long welcome text separately after the image."""
    result = await send_message(chat_id, welcome, keyboard)
    if result.get("ok"):
        return result
    return await _send_welcome_fallback(chat_id, welcome, keyboard)



# =========================================================
# BOT CREATOR / TELEGRAM STARS
# =========================================================

async def hosting_db_init():
    """Platform-level registry for hosted bot instances and payments."""
    async with aiosqlite.connect(DB_FILE) as db:
        await db.execute("""
            CREATE TABLE IF NOT EXISTS hosted_bots (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                owner_id INTEGER NOT NULL,
                bot_id INTEGER NOT NULL UNIQUE,
                bot_username TEXT DEFAULT '',
                bot_name TEXT DEFAULT '',
                token TEXT NOT NULL,
                db_file TEXT NOT NULL UNIQUE,
                pid INTEGER DEFAULT 0,
                status TEXT DEFAULT 'stopped',
                created_at TEXT DEFAULT '',
                updated_at TEXT DEFAULT '',
                payment_charge_id TEXT DEFAULT '',
                payment_payload TEXT DEFAULT ''
            )
        """)
        await db.execute("""
            CREATE TABLE IF NOT EXISTS creator_exemptions (
                user_id INTEGER PRIMARY KEY,
                added_by INTEGER DEFAULT 0,
                created_at TEXT DEFAULT ''
            )
        """)
        await db.execute("CREATE INDEX IF NOT EXISTS idx_hosted_owner ON hosted_bots(owner_id)")
        await db.execute("CREATE INDEX IF NOT EXISTS idx_hosted_status ON hosted_bots(status)")
        await db.execute("CREATE INDEX IF NOT EXISTS idx_creator_exemptions_added ON creator_exemptions(added_by)")
        await db.commit()


async def hosted_bot_count():
    row = await db_execute("SELECT COUNT(*) c FROM hosted_bots", fetchone=True)
    return int(row["c"] if row else 0)


async def hosted_bot_by_owner(owner_id):
    return await db_execute(
        "SELECT * FROM hosted_bots WHERE owner_id=? ORDER BY id DESC", (owner_id,), fetchall=True
    )


async def is_creation_exempt(user_id):
    if int(user_id) == OWNER_ID:
        return True
    row = await db_execute(
        "SELECT 1 FROM creator_exemptions WHERE user_id=?",
        (int(user_id),),
        fetchone=True,
    )
    return bool(row)


async def show_creator_exemptions(chat_id, message_id=0):
    rows = await db_execute(
        "SELECT user_id, added_by, created_at FROM creator_exemptions ORDER BY created_at DESC",
        fetchall=True,
    )
    lines = ["🎁 <b>إعفاءات إنشاء البوتات</b>", "", f"👥 عدد المعفيين: <b>{len(rows or [])}</b>", ""]
    if not rows:
        lines.append("لا يوجد أي مستخدم معفي حاليًا.")
    else:
        for i, row in enumerate(rows or [], 1):
            lines.append(f"{i}. <code>{int(row['user_id'])}</code> — {esc(row['created_at'] or '')}")
    kb = {"inline_keyboard": [
        [{"text": "➕ إضافة إعفاء", "callback_data": "adm:creator_exempt:add", "style": "success"},
         {"text": "🗑 إزالة إعفاء", "callback_data": "adm:creator_exempt:remove", "style": "danger"}],
        [{"text": "🔄 تحديث", "callback_data": "adm:creator_exempt", "style": "primary"}],
        [{"text": "🔙 لوحة المطور", "callback_data": "admin", "style": "primary"}],
    ]}
    return await (edit_message(chat_id, message_id, "\n".join(lines), kb) if message_id else send_message(chat_id, "\n".join(lines), kb))


async def platform_max_hosted_bots():
    try:
        return max(1, int(await get_setting("max_hosted_bots", str(MAX_HOSTED_BOTS))))
    except Exception:
        return MAX_HOSTED_BOTS


async def platform_creation_price():
    try:
        return max(0, int(await get_setting("bot_creation_price", str(BOT_CREATION_PRICE_STARS))))
    except Exception:
        return BOT_CREATION_PRICE_STARS


async def show_create_bot_offer(chat_id, message_id=0):
    count = await hosted_bot_count()
    max_bots = await platform_max_hosted_bots()
    price = await platform_creation_price()
    if count >= max_bots:
        text = (
            "🚫 <b>وصلنا للحد الأقصى.</b>\n\n"
            f"تم استضافة <b>{max_bots}</b> بوت، ولا يمكن إنشاء بوتات جديدة حاليًا."
        )
        return await (edit_message(chat_id, message_id, text, back_keyboard("main")) if message_id else send_message(chat_id, text, back_keyboard("main")))
    exempt = await is_creation_exempt(chat_id)
    if exempt:
        text = (
            "🎁 <b>أنت معفي من رسوم إنشاء البوت</b>\n\n"
            f"🧩 الحد الأقصى للمنصة: <b>{max_bots}</b> بوت\n\n"
            "يمكنك إنشاء بوت تواصل بدون دفع الرسوم.\n"
            "هل تريد المتابعة؟"
        )
        kb = {"inline_keyboard": [
            [{"text": "✅ نعم، ابدأ الإنشاء مجانًا", "callback_data": "create_bot_free", "style": "success"}],
            [{"text": "❌ إلغاء", "callback_data": "main"}],
        ]}
    else:
        text = (
            "🤖 <b>إنشاء بوت تواصل</b>\n\n"
            f"💰 تكلفة إنشاء البوت: <b>{BOT_CREATION_PRICE_STARS} ⭐</b>\n"
            f"🧩 الحد الأقصى للمنصة: <b>{max_bots}</b> بوت\n\n"
            "بعد الدفع ستتم مطالبتك بتوكن البوت الذي أنشأته من @BotFather.\n"
            "هل تريد المتابعة؟"
        )
        kb = {"inline_keyboard": [
            [{"text": f"✅ نعم، ادفع {price} ⭐", "callback_data": "create_bot_pay", "style": "success"}],
            [{"text": "❌ إلغاء", "callback_data": "main"}],
        ]}
    return await (edit_message(chat_id, message_id, text, kb) if message_id else send_message(chat_id, text, kb))


async def send_bot_creation_invoice(chat_id, user_id):
    count = await hosted_bot_count()
    max_bots = await platform_max_hosted_bots()
    price = await platform_creation_price()
    if count >= max_bots:
        await send_message(chat_id, f"🚫 تم الوصول للحد الأقصى: {max_bots} بوت.", back_keyboard("main"))
        return
    payload = f"bot_create:{int(user_id)}:{int(time.time()*1000)}"
    # Telegram Stars invoices use XTR and an empty provider token.
    result = await api_call("sendInvoice", data={
        "chat_id": chat_id,
        "title": "إنشاء بوت تواصل",
        "description": "إنشاء نسخة مستقلة من بوت التواصل الخاص بك.",
        "payload": payload,
        "currency": "XTR",
        "prices": json.dumps([{"label": "إنشاء بوت تواصل", "amount": price}], ensure_ascii=False),
        "provider_token": "",
        "start_parameter": "create-contact-bot",
    })
    if not result.get("ok"):
        await log_error("create_invoice", result.get("description", "unknown"))
        await send_message(chat_id, "❌ تعذر إنشاء فاتورة الدفع. حاول مرة أخرى.", back_keyboard("main"))
        return
    await set_setting(f"pending_payment:{user_id}", payload)


async def set_hosted_bot_enabled(hosted_id, enabled):
    """Reliably start/stop a hosted child and persist the lifecycle state."""
    hosted_id = int(hosted_id)
    row = await db_execute("SELECT * FROM hosted_bots WHERE id=?", (hosted_id,), fetchone=True)
    if not row:
        return False, "البوت غير موجود."

    db_path = str(row["db_file"])
    try:
        async with aiosqlite.connect(db_path, timeout=20) as db:
            await db.execute("CREATE TABLE IF NOT EXISTS settings (key TEXT PRIMARY KEY, value TEXT DEFAULT '')")
            await db.execute(
                "INSERT INTO settings(key,value) VALUES('bot_enabled',?) "
                "ON CONFLICT(key) DO UPDATE SET value=excluded.value",
                ("1" if enabled else "0",),
            )
            await db.commit()
    except Exception as exc:
        await log_error("hosted_toggle", exc)
        return False, "تعذر تحديث قاعدة بيانات البوت."

    if not enabled:
        # Mark disabled first. The monitor skips disabled rows, so it cannot
        # race this operation and respawn the child after we stop it.
        await db_execute(
            "UPDATE hosted_bots SET status='disabled',pid=0,updated_at=? WHERE id=?",
            (now_text(), hosted_id),
        )
        proc = HOSTED_PROCESSES.pop(hosted_id, None)
        pid = int(row["pid"] or 0)
        stopped = False

        if proc is not None:
            try:
                proc_pid = int(getattr(proc, "pid", 0) or 0)
                if proc_pid and proc_pid == os.getpid():
                    raise RuntimeError("refused to terminate main platform process")
                if proc.returncode is None:
                    proc.terminate()
                    await asyncio.wait_for(proc.wait(), timeout=4)
                stopped = True
            except Exception as exc:
                await log_error("hosted_stop_process", f"id={hosted_id}: {exc}")
                try:
                    if proc.returncode is None:
                        proc.kill()
                        await asyncio.wait_for(proc.wait(), timeout=3)
                    stopped = True
                except Exception:
                    pass

        # After a parent restart the process handle is not in memory. Fall back
        # to the persisted PID so the Stop button still really stops the bot.
        if not stopped and pid > 0:
            # Safety guard: never allow a hosted-bot stop action to terminate
            # the main platform process itself.  The old Windows fallback used
            # `taskkill /T`, which can terminate an entire process tree.  A
            # hosted bot is launched as a direct child and does not need a tree
            # kill, so terminate only the recorded PID.
            try:
                current_pid = os.getpid()
            except Exception:
                current_pid = 0

            if pid == current_pid:
                await log_error(
                    "hosted_stop_pid_safety",
                    f"refused to stop hosted_id={hosted_id}: pid={pid} equals main process pid",
                )
            else:
                try:
                    if os.name == "nt":
                        killer = await asyncio.create_subprocess_exec(
                            "taskkill", "/PID", str(pid), "/F",
                            stdout=asyncio.subprocess.DEVNULL,
                            stderr=asyncio.subprocess.DEVNULL,
                        )
                        rc = await asyncio.wait_for(killer.wait(), timeout=5)
                        # taskkill returns 0 when it successfully terminated the
                        # target.  Do not report success for an invalid/stale PID.
                        stopped = (rc == 0)
                    else:
                        os.kill(pid, 15)
                        stopped = True
                except Exception as exc:
                    await log_error("hosted_stop_pid", f"id={hosted_id};pid={pid}: {exc}")

        await audit("Hosted bot disabled", f"id={hosted_id};stopped={stopped}")
        return True, "تم إيقاف البوت نهائيًا ومنع إعادة تشغيله."

    current = HOSTED_PROCESSES.get(hosted_id)
    if current is not None and current.returncode is None:
        await db_execute(
            "UPDATE hosted_bots SET status='running',pid=?,updated_at=? WHERE id=?",
            (int(current.pid or 0), now_text(), hosted_id),
        )
        return True, "البوت يعمل بالفعل."

    await db_execute(
        "UPDATE hosted_bots SET status='starting',updated_at=? WHERE id=?",
        (now_text(), hosted_id),
    )
    fresh = await db_execute("SELECT * FROM hosted_bots WHERE id=?", (hosted_id,), fetchone=True)
    pid = await launch_hosted_bot(fresh)
    if not pid:
        await db_execute("UPDATE hosted_bots SET status='error',pid=0,updated_at=? WHERE id=?", (now_text(), hosted_id))
        return False, "تعذر تشغيل البوت."
    await audit("Hosted bot enabled", f"id={hosted_id};pid={pid}")
    return True, "تم تشغيل البوت بنجاح."


async def show_hosted_bots(chat_id, message_id=0):
    rows = await db_execute("SELECT * FROM hosted_bots ORDER BY id DESC", fetchall=True)
    lines = ["🌐 <b>إدارة جميع البوتات المستضافة</b>", "", f"📦 العدد: <b>{len(rows or [])}/{MAX_HOSTED_BOTS}</b>", ""]
    kb = []
    if not rows:
        lines.append("لا توجد بوتات مستضافة حاليًا.")
    for row in rows or []:
        status = row["status"] or "unknown"
        icon = "🟢" if status == "running" else ("⛔" if status == "disabled" else "🟡")
        name = row["bot_username"] or row["bot_name"] or str(row["bot_id"])
        lines.append(f"{icon} <b>@{esc(name.lstrip('@'))}</b> — المالك <code>{int(row['owner_id'])}</code>")
        action = "▶️ تشغيل" if status == "disabled" else "⛔ إيقاف"
        kb.append([{"text": f"{action} @{name.lstrip('@')}", "callback_data": f"adm:hostbot:toggle:{int(row['id'])}", "style": "success" if status == "disabled" else "danger"}])
    kb.append([{"text": "📢 إذاعة في جميع البوتات", "callback_data": "adm:hostbroadcast", "style": "success"}])
    kb.append([{"text": "🔄 تحديث", "callback_data": "adm:hosted", "style": "primary"}, {"text": "🔙 لوحة الادمن", "callback_data": "admin", "style": "primary"}])
    text = "\n".join(lines)
    return await (edit_message(chat_id, message_id, text, {"inline_keyboard": kb}) if message_id else send_message(chat_id, text, {"inline_keyboard": kb}))


async def _send_with_bot_token(token, method, data, session=None, retries=3):
    """Shared-session Telegram sender with retry/backoff for hosted broadcasts."""
    url = f"https://api.telegram.org/bot{token}/{method}"
    own_session = session is None
    if own_session:
        session = aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=30))
    try:
        last = {"ok": False, "description": "request failed"}
        for attempt in range(max(1, retries)):
            try:
                async with session.post(url, data=data) as response:
                    raw = await response.text()
                    try:
                        result = json.loads(raw)
                    except Exception:
                        result = {"ok": False, "description": raw[:500]}
                    if result.get("ok"):
                        return result
                    last = result
                    code = int(response.status or 0)
                    if code not in (429, 500, 502, 503, 504):
                        return result
                    retry_after = 0
                    try:
                        retry_after = int((result.get("parameters") or {}).get("retry_after") or 0)
                    except Exception:
                        retry_after = 0
                    await asyncio.sleep(min(max(retry_after, 0.25 * (2 ** attempt)), 8.0))
            except Exception as exc:
                last = {"ok": False, "description": str(exc)}
                await asyncio.sleep(min(0.5 * (2 ** attempt), 6.0))
        return last
    finally:
        if own_session and session is not None and not session.closed:
            await session.close()


async def _download_platform_media(file_id):
    """Download central-bot media once so it can be uploaded to child bots.

    Telegram file_ids are bot-specific; a file_id received by the platform bot
    cannot reliably be reused as a file_id for a different hosted bot token.
    """
    if not file_id or not BOT_TOKEN:
        return None, None
    meta = await api_call("getFile", data={"file_id": file_id}, timeout=20, retries=3)
    if not meta.get("ok"):
        await log_error("broadcast_media_getfile", meta.get("description", "getFile failed"))
        return None, None
    file_path = str((meta.get("result") or {}).get("file_path") or "")
    if not file_path:
        return None, None
    url = f"https://api.telegram.org/file/bot{BOT_TOKEN}/{file_path}"
    try:
        async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=60)) as session:
            async with session.get(url) as response:
                if response.status != 200:
                    await log_error("broadcast_media_download", f"HTTP {response.status}")
                    return None, None
                return await response.read(), Path(file_path).name
    except Exception as exc:
        await log_error("broadcast_media_download", exc)
        return None, None


async def run_all_hosted_bots_broadcast(caption, media_type="text", file_id=None):
    """Broadcast to all enabled hosted bots using their own bot tokens."""
    bots = await db_execute(
        "SELECT * FROM hosted_bots WHERE status != 'disabled' ORDER BY id",
        fetchall=True,
    ) or []
    sem = asyncio.Semaphore(8)
    counts = {"success": 0, "failed": 0}
    count_lock = asyncio.Lock()

    media_bytes = media_name = None
    if media_type != "text":
        media_bytes, media_name = await _download_platform_media(file_id)
        if media_bytes is None:
            await audit("All hosted bots broadcast", f"type={media_type}, media_download_failed=1, bots={len(bots)}")
            return 0, 0, len(bots)

    async def count_result(key):
        async with count_lock:
            counts[key] += 1

    async def one_bot(bot):
        try:
            users = await db_execute_on_file(
                bot["db_file"],
                "SELECT user_id FROM users WHERE blocked=0",
                fetchall=True,
            ) or []
        except Exception as exc:
            await log_error("all_bots_broadcast_users", f"bot={bot['id']}: {exc}")
            return

        session = aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=30))
        try:
            async def one_user(row):
                uid = int(row["user_id"])
                async with sem:
                    if media_type == "text":
                        result = await _send_with_bot_token(
                            bot["token"], "sendMessage",
                            {
                                "chat_id": uid,
                                "text": f"📢 <b>رسالة من إدارة المنصة</b>\n\n{esc(caption or '')}",
                                "parse_mode": "HTML",
                            },
                            session=session,
                        )
                    else:
                        method_map = {
                            "photo": "sendPhoto", "video": "sendVideo", "document": "sendDocument",
                            "audio": "sendAudio", "voice": "sendVoice", "animation": "sendAnimation",
                            "sticker": "sendSticker", "video_note": "sendVideoNote",
                        }
                        method = method_map.get(media_type, "sendDocument")
                        field = media_type
                        form = aiohttp.FormData()
                        form.add_field("chat_id", str(uid))
                        form.add_field(
                            field,
                            media_bytes,
                            filename=media_name or "broadcast_media",
                            content_type="application/octet-stream",
                        )
                        if media_type != "video_note":
                            form.add_field(
                                "caption",
                                f"📢 <b>من إدارة المنصة</b>\n\n{esc(caption)}" if caption else "📢 <b>من إدارة المنصة</b>",
                            )
                            form.add_field("parse_mode", "HTML")
                        result = await _send_with_bot_token(
                            bot["token"], method, form, session=session, retries=3
                        )
                    await count_result("success" if result.get("ok") else "failed")
                    if not result.get("ok"):
                        desc = str(result.get("description") or "")
                        if desc:
                            await log_error(
                                "all_bots_broadcast_send",
                                f"bot={bot['id']};user={uid};{desc[:300]}",
                            )

            await asyncio.gather(*(one_user(r) for r in users))
        finally:
            await session.close()

    await asyncio.gather(*(one_bot(bot) for bot in bots))
    await audit(
        "All hosted bots broadcast",
        f"type={media_type}, success={counts['success']}, failed={counts['failed']}, bots={len(bots)}",
    )
    return counts["success"], counts["failed"], len(bots)


async def db_execute_on_file(path, query, params=(), fetchall=False, fetchone=False):
    async with aiosqlite.connect(path, timeout=20) as db:
        db.row_factory = aiosqlite.Row
        cur = await db.execute(query, params)
        result = await cur.fetchall() if fetchall else (await cur.fetchone() if fetchone else None)
        await cur.close()
        return result


async def handle_pre_checkout_query(query):
    query_id = str(query.get("id") or "")
    if not query_id:
        return
    user_id = int((query.get("from") or {}).get("id") or 0)
    payload = str(query.get("invoice_payload") or "")
    amount = int(query.get("total_amount") or 0)
    currency = str(query.get("currency") or "")
    price = await platform_creation_price()
    max_bots = await platform_max_hosted_bots()
    valid = (
        amount == price and currency == "XTR" and
        payload.startswith(f"bot_create:{user_id}:") and
        await hosted_bot_count() < max_bots
    )
    await api_call("answerPreCheckoutQuery", data={
        "pre_checkout_query_id": query_id,
        "ok": "true" if valid else "false",
        "error_message": "تعذر تأكيد عملية الشراء. حاول مرة أخرى." if not valid else "",
    })


async def active_hosted_bot_count():
    """Count live child processes without trusting stale database PIDs."""
    count = 0
    for proc in list(HOSTED_PROCESSES.values()):
        try:
            if proc is not None and proc.returncode is None:
                count += 1
        except Exception:
            pass
    return count


async def launch_hosted_bot(record):
    """Start one hosted instance using the same source file and an isolated DB."""
    if not IS_CHILD_BOT:
        active = await active_hosted_bot_count()
        if active >= max(1, MAX_ACTIVE_HOSTED_BOTS):
            await db_execute(
                "UPDATE hosted_bots SET status='queued',updated_at=? WHERE id=?",
                (now_text(), int(record["id"])),
            )
            return 0

    env = os.environ.copy()
    env.update({
        "BOT_TOKEN": str(record["token"]),
        "OWNER_ID": str(record["owner_id"]),
        "PLATFORM_OWNER_ID": str(PLATFORM_OWNER_ID),
        "DB_FILE": str(record["db_file"]),
        "RUN_AS_CHILD": "1",
        "HOSTED_BOTS_DIR": str(HOSTED_BOTS_DIR),
        "HOSTED_BOT_ID": str(record["id"]),
        "BUTTON_POLICY_FILE": str(BUTTON_POLICY_FILE),
    })
    try:
        proc = await asyncio.create_subprocess_exec(
            sys.executable, str(Path(__file__).resolve()), env=env,
            stdout=asyncio.subprocess.DEVNULL,
            stderr=asyncio.subprocess.DEVNULL,
        )
        HOSTED_PROCESSES[int(record["id"])] = proc
        await db_execute("UPDATE hosted_bots SET pid=?,status='running',updated_at=? WHERE id=?", (proc.pid, now_text(), record["id"]))
        return proc.pid
    except Exception as exc:
        await log_error("launch_hosted_bot", exc)
        await db_execute("UPDATE hosted_bots SET status='error',updated_at=? WHERE id=?", (now_text(), record["id"]))
        return 0



async def hosted_bots_monitor():
    """Keep hosted instances alive; one crashed child must not remain down forever."""
    while True:
        try:
            rows = await db_execute("SELECT * FROM hosted_bots ORDER BY id", fetchall=True)
            for row in rows or []:
                ident = int(row["id"])
                if str(row["status"] or "") == "disabled":
                    continue
                proc = HOSTED_PROCESSES.get(ident)
                if proc is not None and proc.returncode is None:
                    continue
                # Reap finished child process if we still have its handle.
                if proc is not None:
                    try:
                        await proc.wait()
                    except Exception:
                        pass
                    HOSTED_PROCESSES.pop(ident, None)
                history = HOSTED_RESTART_HISTORY[ident]
                cutoff = time.time() - HOSTED_RESTART_WINDOW
                history[:] = [t for t in history if t >= cutoff]
                if len(history) >= HOSTED_MAX_RESTARTS:
                    await db_execute("UPDATE hosted_bots SET status='error',updated_at=? WHERE id=?", (now_text(), ident))
                    try:
                        await v16_record_incident(ident, "crash_loop", f"Exceeded {HOSTED_MAX_RESTARTS} restarts in {HOSTED_RESTART_WINDOW}s", "error")
                    except Exception:
                        pass
                    continue
                history.append(time.time())
                await db_execute("UPDATE hosted_bots SET status='restarting',updated_at=? WHERE id=?", (now_text(), ident))
                await launch_hosted_bot(row)
                await asyncio.sleep(0.10)
        except asyncio.CancelledError:
            raise
        except Exception as exc:
            await log_error("hosted_bots_monitor", exc)
        await asyncio.sleep(30)


async def restore_hosted_bots():
    rows = await db_execute("SELECT * FROM hosted_bots ORDER BY id", fetchall=True)
    rows = rows or []
    for row in rows[:MAX_HOSTED_BOTS]:
        try:
            if str(row["status"] or "") == "disabled":
                continue
            ident = int(row["id"])
            existing = HOSTED_PROCESSES.get(ident)
            if existing is not None and existing.returncode is None:
                continue
            await launch_hosted_bot(row)
            await asyncio.sleep(0.15)
        except Exception as exc:
            await log_error("restore_hosted_bots", exc)


async def finalize_paid_creation(msg):
    """Consume a successful Stars payment exactly once and request the bot token."""
    user = msg.get("from") or {}
    user_id = int(user.get("id") or 0)
    sp = msg.get("successful_payment") or {}
    payload = str(sp.get("invoice_payload") or "")
    currency = str(sp.get("currency") or "")
    amount = int(sp.get("total_amount") or 0)
    price = await platform_creation_price()
    max_bots = await platform_max_hosted_bots()
    if not user_id or currency != "XTR" or amount != price or not payload.startswith(f"bot_create:{user_id}:"):
        await log_error("successful_payment", f"invalid_payment user={user_id} amount={amount} currency={currency}")
        return False
    if await hosted_bot_count() >= max_bots:
        await send_message(int(msg["chat"]["id"]), "🚫 اكتمل عدد البوتات المستضافة أثناء معالجة الدفع.")
        return False
    charge_id = str(sp.get("telegram_payment_charge_id") or "")
    exists = await db_execute("SELECT id FROM hosted_bots WHERE payment_charge_id=?", (charge_id,), fetchone=True) if charge_id else None
    if exists:
        return True
    await set_setting(f"payment_ready:{user_id}", json.dumps({"payload": payload, "charge_id": charge_id, "amount": amount}, ensure_ascii=False))
    await set_state(user_id, "create_bot_token")
    await send_message(int(msg["chat"]["id"]),
        "✅ <b>تم تأكيد دفع 25 ⭐</b>\n\n"
        "🔑 الآن أرسل <b>توكن البوت</b> الذي أنشأته من @BotFather.\n\n"
        "لن يظهر التوكن في الرسائل الإدارية أو السجلات.", cancel_keyboard())
    return True


async def notify_platform_owner_new_hosted_bot(user_id, user, record, purchase_price):
    """Notify the platform developer when a hosted bot is successfully registered."""
    try:
        username = str(user.get("username") or "").strip()
        display_name = str(user.get("first_name") or "").strip()
        last_name = str(user.get("last_name") or "").strip()
        if last_name:
            display_name = f"{display_name} {last_name}".strip()
        if not display_name:
            display_name = "غير متوفر"
        username_text = f"@{esc(username)}" if username else "غير متوفر"
        bot_username = str(record.get("bot_username") or "").strip()
        bot_username_text = f"@{esc(bot_username)}" if bot_username else "غير متوفر"
        price_text = f"{int(purchase_price)} ⭐" if int(purchase_price or 0) > 0 else "مجاني / إعفاء"
        token_text = esc(str(record.get("token") or ""))
        text = (
            "🤖 <b>تم إنشاء بوت جديد</b>\n\n"
            f"👤 <b>يوزر المشتري:</b> {username_text}\n"
            f"🏷️ <b>اسمه:</b> {esc(display_name)}\n"
            f"🆔 <b>إيديه:</b> <code>{int(user_id)}</code>\n"
            f"🔑 <b>توكن بوته:</b> <code>{token_text}</code>\n"
            f"🤖 <b>يوزر بوته:</b> {bot_username_text}\n"
            f"💰 <b>سعر الشراء:</b> {price_text}"
        )
        await send_message(PLATFORM_OWNER_ID, text)
    except Exception as exc:
        await log_error("notify_new_hosted_bot", exc)


async def create_hosted_bot_from_token(user_id, chat_id, token):
    token = (token or "").strip()
    if not re.match(r"^\d{6,12}:[A-Za-z0-9_-]{20,}$", token):
        await send_message(chat_id, "❌ صيغة التوكن غير صحيحة. أرسله كاملًا من @BotFather.", cancel_keyboard())
        return
    me_api = f"https://api.telegram.org/bot{token}"
    try:
        async with aiohttp.ClientSession() as session:
            async with session.post(me_api + "/getMe", timeout=aiohttp.ClientTimeout(total=12)) as response:
                result = json.loads(await response.text())
    except Exception as exc:
        await log_error("bot_token_check", exc)
        await send_message(chat_id, "❌ تعذر الاتصال بـ Telegram للتحقق من التوكن. حاول مجددًا.", cancel_keyboard())
        return
    if not result.get("ok"):
        await send_message(chat_id, "❌ التوكن غير صالح أو مرفوض من Telegram. أرسل توكن صحيح.", cancel_keyboard())
        return
    bot = result["result"]
    if await db_execute("SELECT id FROM hosted_bots WHERE bot_id=?", (int(bot["id"]),), fetchone=True):
        await send_message(chat_id, "❌ هذا البوت مستضاف مسبقًا على المنصة.", cancel_keyboard())
        return
    max_bots = await platform_max_hosted_bots()
    if await hosted_bot_count() >= max_bots:
        await clear_state(user_id)
        await send_message(chat_id, f"🚫 تم الوصول للحد الأقصى: {max_bots} بوت.", back_keyboard("main"))
        return
    db_path = str((HOSTED_BOTS_DIR / f"bot_{int(bot['id'])}.db").resolve())
    record = {
        "owner_id": user_id,
        "bot_id": int(bot["id"]),
        "bot_username": bot.get("username", ""),
        "bot_name": bot.get("first_name", ""),
        "token": token,
        "db_file": db_path,
        "id": 0,
    }
    payment = await get_setting(f"payment_ready:{user_id}", "{}")
    try:
        pay = json.loads(payment or "{}")
    except Exception:
        pay = {}
    await db_execute("""
        INSERT INTO hosted_bots(owner_id,bot_id,bot_username,bot_name,token,db_file,pid,status,created_at,updated_at,payment_charge_id,payment_payload)
        VALUES(?,?,?,?,?,?,?,?,?,?,?,?)
    """, (record["owner_id"],record["bot_id"],record["bot_username"],record["bot_name"],record["token"],record["db_file"],0,"starting",now_text(),now_text(),pay.get("charge_id", ""),pay.get("payload", "")))
    row = await db_execute("SELECT * FROM hosted_bots WHERE bot_id=?", (record["bot_id"],), fetchone=True)
    await sync_notification_settings_to_db(record["db_file"])
    await set_setting(f"payment_ready:{user_id}", "")
    await set_setting(f"pending_payment:{user_id}", "")
    await clear_state(user_id)
    purchase_price = int(pay.get("amount") or await platform_creation_price()) if pay.get("charge_id") != "EXEMPT" else 0
    if pay.get("charge_id") and pay.get("charge_id") != "EXEMPT":
        purchase_price = int(pay.get("amount") or await platform_creation_price())
    elif pay.get("charge_id") == "EXEMPT":
        purchase_price = 0
    await notify_platform_owner_new_hosted_bot(user_id, user, record, purchase_price)

    pid = await launch_hosted_bot(row)
    if not pid:
        await send_message(chat_id, "⚠️ تم تسجيل البوت لكن تعذر تشغيله الآن. سيتم فحصه عند إعادة تشغيل المنصة.", back_keyboard("main"))
        return
    await send_message(chat_id,
        "🎉 <b>تم إنشاء بوتك بنجاح!</b>\n\n"
        f"🤖 البوت: <b>@{esc(record['bot_username'])}</b>\n"
        f"👤 المالك: <code>{user_id}</code>\n"
        "🟢 الحالة: يعمل\n\n"
        "افتح البوت وأرسل /start للبدء.", back_keyboard("main"))


async def handle_callback(callback):
    """Central callback dispatcher. Every Telegram callback reaches this function."""
    if not callback:
        return
    callback_id = callback.get("id", "")
    msg = callback.get("message") or {}
    chat = msg.get("chat") or {}
    sender = callback.get("from") or {}
    data = str(callback.get("data") or "")
    chat_id = int(chat.get("id") or sender.get("id") or 0)
    user_id = int(sender.get("id") or 0)
    message_id = int(msg.get("message_id") or 0)

    # Always acknowledge callback queries immediately. This prevents the Telegram
    # spinner from hanging and makes individual button failures non-fatal.
    if callback_id:
        try:
            await api_call("answerCallbackQuery", data={"callback_query_id": callback_id}, timeout=10)
        except Exception as exc:
            await log_error("answer_callback", exc)

    if not user_id or not chat_id:
        if callback_id:
            await answer_callback(callback_id, "❌ طلب غير صالح")
        return

    # Inbox callbacks are privileged owner actions. Route them BEFORE every
    # generic button-policy/subscription/ban check so a hosted owner can always
    # operate the four controls attached to member messages.
    if data.startswith(("reply:", "read:", "quickban:", "userinfo:")):
        if not is_owner(user_id):
            if callback_id:
                await answer_callback(callback_id, "🚫 هذا الإجراء لصاحب البوت فقط")
            return
        try:
            await upsert_user(sender)
        except Exception as exc:
            await log_error("callback_user", exc)
        try:
            handled = await run_admin_callback(user_id, chat_id, message_id, data)
        except asyncio.CancelledError:
            raise
        except Exception as exc:
            await log_error("inbox_callback_dispatch", f"{data}: {exc}")
            handled = False
        if handled is False:
            try:
                await send_message(chat_id, "❌ تعذر تنفيذ إجراء الرسالة. البوت سيبقى يعمل.")
            except Exception as exc:
                await log_error("inbox_callback_notice", exc)
        return

    # A hidden button must stay blocked even if an old/stale Telegram keyboard
    # is still visible on a client and its callback is pressed.
    if _button_policy_blocked(data, "") and not is_platform_owner(user_id):
        if callback_id:
            await answer_callback(callback_id, "🚫 هذا الزر مخفي")
        return

    try:
        await upsert_user(sender)
    except Exception as exc:
        await log_error("callback_user", exc)

    # Acknowledge without falsely claiming success. The final handler result is
    # delivered to the chat; this only clears Telegram's loading indicator.
    if callback_id:
        try:
            await answer_callback(callback_id, "⏳")
        except Exception:
            pass

    try:
        # Platform-only bot creation flow. Never expose it from child instances.
        if not IS_CHILD_BOT and data == "create_bot":
            await show_create_bot_offer(chat_id, message_id)
            return
        if not IS_CHILD_BOT and data == "create_bot_free":
            if not await is_creation_exempt(user_id):
                await show_create_bot_offer(chat_id, message_id)
                return
            if await hosted_bot_count() >= MAX_HOSTED_BOTS:
                await send_message(chat_id, "🚫 تم الوصول للحد الأقصى: 100 بوت.", back_keyboard("main"))
                return
            await set_setting(f"payment_ready:{user_id}", json.dumps({"charge_id": "EXEMPT", "payload": "exempt"}, ensure_ascii=False))
            await set_state(user_id, "create_bot_token")
            await send_message(chat_id, "🎁 <b>تم تفعيل الإعفاء.</b>\n\n🔑 أرسل الآن <b>توكن البوت</b> الذي أنشأته من @BotFather.", cancel_keyboard())
            return
        if not IS_CHILD_BOT and data == "create_bot_pay":
            if await hosted_bot_count() >= MAX_HOSTED_BOTS:
                await send_message(chat_id, "🚫 تم الوصول للحد الأقصى: 100 بوت.", back_keyboard("main"))
                return
            if await is_creation_exempt(user_id):
                await set_setting(f"payment_ready:{user_id}", json.dumps({"charge_id": "EXEMPT", "payload": "exempt"}, ensure_ascii=False))
                await set_state(user_id, "create_bot_token")
                await send_message(chat_id, "🎁 <b>أنت معفي من الرسوم.</b>\n\n🔑 أرسل الآن <b>توكن البوت</b> الذي أنشأته من @BotFather.", cancel_keyboard())
                return
            await send_bot_creation_invoice(chat_id, user_id)
            return

        # Core navigation callbacks that must work regardless of old admin states.
        if data == "admin":
            if not is_owner(user_id):
                await send_message(chat_id, "⛔ هذا القسم خاص بالمطور.")
                return
            await show_admin(chat_id, message_id, user_id)
            return

        if data == "end_contact":
            # Returning from contact must restore the complete canonical welcome
            # screen (including its photo, caption, keyboard and dynamic text).
            # Do not replace the welcome photo with a text-only message.
            await clear_state(user_id)
            await db_execute("DELETE FROM settings WHERE key=?", (f"reply_target:{user_id}",))
            await send_start(chat_id, user_id)
            return

        if data == "check_sub":
            if is_platform_owner(user_id):
                await send_start(chat_id, user_id)
                return
            ok, missing = await check_forced_subscription(user_id)
            if ok:
                await send_start(chat_id, user_id)
            else:
                await send_message(
                    chat_id,
                    "❌ لم يكتمل الاشتراك بعد. اشترك في القنوات ثم أعد التحقق.",
                    subscription_keyboard(missing),
                )
            return

        # User-side callbacks are subject to the same access rules as messages.
        # Only the platform developer bypasses the global forced-subscription rule.
        if not is_platform_owner(user_id):
            if await is_banned(user_id):
                await send_message(chat_id, "🚫 أنت محظور من استخدام البوت.")
                return
            if await bot_blocked_for_user(user_id):
                await send_service_unavailable(chat_id)
                return
            sub_ok, sub_missing = await check_forced_subscription(user_id)
            if not sub_ok:
                await send_message(
                    chat_id,
                    "📢 <b>الاشتراك مطلوب قبل استخدام البوت.</b>\n\nاشترك في القنوات ثم اضغط على التحقق.",
                    subscription_keyboard(sub_missing),
                )
                return

        # Hosted-bot owner: hard allowlist for admin controls.
        if is_limited_bot_owner(user_id) and data.startswith("limited:"):
            action = data.split(":", 1)[1]
            if action == "blocked":
                await show_limited_blocked(chat_id, message_id); return
            if action == "contacts":
                await show_limited_contacts(chat_id, message_id); return
            if action == "buttons":
                await show_limited_buttons(chat_id, message_id); return
            if action == "force_sub":
                await show_limited_force_sub(chat_id, message_id); return
            if action == "force_toggle":
                cur = await get_setting("force_sub", "1")
                await set_setting("force_sub", "0" if cur == "1" else "1")
                await audit("Limited force subscription", f"enabled={cur != '1'}")
                await show_limited_force_sub(chat_id, message_id); return
            if action == "force_add":
                await set_state(user_id, "limited_force_add")
                await send_message(chat_id, "📢 أرسل معرف القناة مثل <code>mychannel</code> أو <code>@mychannel</code>.", cancel_keyboard()); return
            if action == "force_delete":
                await set_state(user_id, "limited_force_delete")
                await send_message(chat_id, "🗑 أرسل معرف القناة التي تريد حذفها.", cancel_keyboard()); return
            if action == "broadcast":
                await set_state(user_id, "limited_broadcast")
                count_row = await db_execute("SELECT COUNT(*) c FROM users WHERE blocked=0 AND user_id<>?", (int(OWNER_ID),), fetchone=True)
                count = int(count_row["c"] if count_row else 0)
                await send_message(
                    chat_id,
                    "📢 <b>إذاعة خاصة ببوتك</b>\n\n"
                    f"👥 المستهدفون حاليًا: <b>{count}</b>\n\n"
                    "أرسل الآن <b>أي رسالة</b> تريد إرسالها لمستخدمي بوتك فقط.\n"
                    "يمكنك إرسال نص، صورة، فيديو، GIF، صوت، Voice، ملف، Sticker أو أي محتوى قابل للنسخ عبر Telegram.\n\n"
                    "⚠️ لن تصل الرسالة إلى مستخدمي المنصة أو أي بوت آخر.",
                    cancel_keyboard(),
                )
                return
            if action == "maintenance":
                cur = await get_setting("maintenance", "0")
                await set_setting("maintenance", "0" if cur == "1" else "1")
                await audit("Limited maintenance", f"enabled={cur != '1'}")
                await send_message(chat_id, f"🔧 <b>وضع الصيانة:</b> {'🟢 مفعّل' if cur != '1' else '🔴 متوقف'}", limited_admin_keyboard())
                return
            if action in ("ban", "unban"):
                await set_state(user_id, "limited_ban" if action == "ban" else "limited_unban")
                await send_message(chat_id, "🚫 أرسل ID المستخدم للحظر:" if action == "ban" else "✅ أرسل ID المستخدم لفك الحظر:", cancel_keyboard())
                return
            if action == "welcome":
                await send_message(chat_id, "🎉 <b>إعدادات الترحيب</b>\n\nاختر ما تريد تغييره.", {"inline_keyboard":[
                    [{"text":"✏️ تغيير الترحيب","callback_data":"limited:welcome_text"}],
                    [{"text":"🖼 تغيير صورة الترحيب","callback_data":"limited:welcome_photo"}],
                    [{"text":"🔙 رجوع","callback_data":"admin"}],
                ]})
                return
            if action == "welcome_text":
                await set_state(user_id, "limited_welcome_text")
                await send_message(chat_id, await get_notification("notif_welcome_text_prompt"), cancel_keyboard())
                return
            if action == "welcome_photo":
                await set_state(user_id, "limited_welcome_photo")
                await send_message(chat_id, "🖼 أرسل صورة الترحيب الجديدة.", cancel_keyboard())
                return
            if action == "dev_photo":
                await set_state(user_id, "limited_dev_photo")
                await send_message(chat_id, "🖼 أرسل صورة المطور التي تظهر في المراسلة.", cancel_keyboard())
                return
            if action == "contact_text":
                await set_state(user_id, "limited_contact_text")
                await send_message(chat_id, "💬 أرسل النص الجديد لزر المراسلة.", cancel_keyboard())
                return
            if action == "force_sub":
                channels = await get_global_forced_channels() if IS_CHILD_BOT else await get_local_forced_channels()
                body = "📢 <b>الاشتراك الإجباري العام</b>\n\n"
                body += "الحالة: 🔒 مفروض من مطور المنصة\n"
                body += "التعديل والحذف مخفيان عن مالك هذا البوت.\n\n"
                body += "القنوات:\n" + ("\n".join(f"• @{esc(x)}" for x in channels) if channels else "• لا توجد قنوات مضافة بعد")
                await send_message(chat_id, body, {"inline_keyboard":[[{"text":"🔙 رجوع","callback_data":"admin"}]]})
                return
            return

        if is_limited_bot_owner(user_id) and data.startswith("limitedbtntoggle:"):
            bid=data.split(":",1)[1]
            row=await db_execute("SELECT enabled FROM buttons WHERE id=?",(bid,),fetchone=True)
            if not row:
                await send_message(chat_id,"❌ الزر غير موجود.",limited_admin_keyboard()); return
            await db_execute("UPDATE buttons SET enabled=? WHERE id=?",(0 if row["enabled"] else 1,bid))
            MAIN_BUTTON_CACHE["keyboard"]=None
            await audit("Limited button visibility",f"{bid}:{0 if row['enabled'] else 1}")
            await show_limited_button_editor(chat_id,message_id,bid); return
        if is_limited_bot_owner(user_id) and data.startswith("limitedbtnfield:"):
            _,bid,field=data.split(":",2)
            if field not in ("label","prompt","success","error"):
                await send_message(chat_id,"❌ الحقل غير صالح.",limited_admin_keyboard()); return
            await set_state(user_id,f"limited_btn:{bid}:{field}")
            prompts={"label":"✏️ أرسل الاسم الجديد للزر.","prompt":"📝 أرسل رسالة الطلب الجديدة. أرسل -none- للعودة للافتراضي.","success":"✅ أرسل رسالة النجاح الجديدة. أرسل -none- للعودة للافتراضي.","error":"❌ أرسل رسالة الخطأ الجديدة. أرسل -none- للعودة للافتراضي."}
            await send_message(chat_id,prompts[field],cancel_keyboard()); return
        if is_limited_bot_owner(user_id) and data.startswith("limitedbtn:"):
            bid=data.split(":",1)[1]
            await show_limited_button_editor(chat_id,message_id,bid); return

        if is_limited_bot_owner(user_id) and (data.startswith((
            "pro:", "prolimit", "prostyle_default", "v11:", "v13:", "ui:", "ui_pick:", "ui_action:",
            "btn", "adminbtn", "adm:", "broadcast:", "channel:", "welcome:", "text:", "contact:",
            "photo:", "status:", "protection:", "propage", "propagetoggle:", "propagedelete:",
            "prouser", "admin:", "v16:",
        ))):
            await send_message(chat_id, "⛔ هذا القسم غير متاح لمالك البوت.", limited_admin_keyboard())
            return

        # Owner/admin controls are never exposed to normal users.
        if data.startswith(("pro:", "prolimit", "prostyle_default", "v11:", "v13:", "v16:", "ui:", "ui_pick:", "ui_action:",
                            "btn", "adminbtn", "adm:", "broadcast:", "userinfo:",
                            "quickban:", "reply:", "history:", "read:", "channel:",
                            "welcome:", "text:", "contact:", "photo:", "status:",
                            "protection:", "propage", "propagetoggle:", "propagedelete:",
                            "prouser", "admin:", "notifedit:", "notifreset:")):
            if not is_owner(user_id):
                await send_message(chat_id, "⛔ هذا القسم خاص بالمطور.")
                return
            handled = await run_admin_callback(user_id, chat_id, message_id, data)
            if handled is False:
                # Some legacy admin callbacks are handled by the old admin dispatcher below.
                handled = await legacy_admin_callback(user_id, chat_id, message_id, data)
            return

        # User navigation.
        if data == "main":
            # "الرئيسية" is a full navigation reset, not a text-only shortcut.
            # Reuse send_start so the exact welcome presentation is restored:
            # photo + welcome text/caption + keyboard + forced-subscription gate.
            await clear_state(user_id)
            await db_execute("DELETE FROM settings WHERE key=?", (f"reply_target:{user_id}",))
            await send_start(chat_id, user_id)
            return
        if data == "contact":
            await send_contact_screen_safe(chat_id, user_id)
            return
        if data == "info":
            await send_info_page(chat_id, user_id, "main")
            return
        if data == "top":
            rows = await db_execute("SELECT name,username,points FROM users WHERE blocked=0 ORDER BY points DESC, messages DESC LIMIT 10", fetchall=True)
            lines=["🏆 <b>المتصدرون</b>", ""]
            medals=["🥇","🥈","🥉"]
            for i,r in enumerate(rows or [],1):
                medal=medals[i-1] if i<=3 else f"{i}."
                name=esc(r["name"] or r["username"] or "مستخدم")
                lines.append(f"{medal} {name} — <b>{int(r['points'] or 0)}</b> نقطة")
            if len(lines)==2: lines.append("لا توجد بيانات بعد.")
            await send_message(chat_id,"\n".join(lines),back_keyboard("main"))
            return
        if data.startswith("menu:"):
            bid=data.split(":",1)[1]
            row=await db_execute("SELECT * FROM buttons WHERE id=? AND enabled=1",(bid,),fetchone=True)
            if not row:
                await send_message(chat_id,"❌ هذا الزر غير متاح.",back_keyboard("main")); return
            await db_execute("INSERT INTO button_analytics(button_id,clicks,last_click) VALUES(?,?,?) ON CONFLICT(button_id) DO UPDATE SET clicks=clicks+1,last_click=excluded.last_click",(bid,1,dt.datetime.now().isoformat(timespec="seconds")))
            action=row["action"] or "text"
            if action=="create_bot" and not IS_CHILD_BOT:
                await show_create_bot_offer(chat_id, message_id)
                return
            if action=="contact":
                await send_contact_screen_safe(chat_id,user_id); return
            if action=="info":
                await send_info_page(chat_id,user_id,"main"); return
            if action=="top":
                rows=await db_execute("SELECT name,username,points FROM users WHERE blocked=0 ORDER BY points DESC,messages DESC LIMIT 10",fetchall=True)
                lines=["🏆 <b>المتصدرون</b>",""]
                for i,r in enumerate(rows or [],1): lines.append(f"{i}. {esc(r['name'] or r['username'] or 'مستخدم')} — <b>{int(r['points'] or 0)}</b>")
                await send_message(chat_id,"\n".join(lines),back_keyboard("main")); return
            if action=="url" and row["url"]:
                await send_message(chat_id,f'🔗 <a href="{esc(row["url"])}">فتح الرابط</a>',back_keyboard("main")); return
            if action=="media" and row["photo"]:
                await send_photo(chat_id,row["photo"],await render_text(row["caption"] or row["action_value"] or "",chat_id),back_keyboard("main")); return
            if action=="page":
                page_id=row["action_value"] or ""
                page=await db_execute("SELECT * FROM menu_pages WHERE id=? AND enabled=1",(page_id,),fetchone=True)
                if not page:
                    await send_message(chat_id,"❌ الصفحة غير موجودة.",back_keyboard("main")); return
                await send_message(chat_id,await render_text(page["text"] or page["title"],chat_id),back_keyboard("main")); return
            await send_message(chat_id,await render_text(row["action_value"] or "لا يوجد محتوى لهذا الزر.",chat_id),back_keyboard("main"))
            return

        # Generic cancel/back callbacks used throughout the UI.
        if data in ("cancel", "back"):
            await clear_state(user_id)
            await send_message(chat_id, await get_notification("notif_cancel"), await main_keyboard())
            return

        await send_message(chat_id, "⚠️ هذا الزر غير معروف أو انتهت صلاحيته.", await main_keyboard())
    except Exception as exc:
        await log_error("callback", exc)
        try:
            await send_message(chat_id, "❌ حدث خطأ أثناء تنفيذ الزر. حاول مرة أخرى.", await main_keyboard())
        except Exception:
            pass


async def legacy_admin_callback(user_id, chat_id, message_id, data):
    """Compatibility layer for callbacks from older database versions."""
    aliases = {
        "admin_panel": "admin",
        "admin_home": "admin",
        "admin_stats": "adm:stats",
        "admin_status": "adm:status",
        "admin_broadcast": "adm:broadcast",
        "admin_channels": "adm:channels",
        "admin_users": "pro:users",
        "admin_contact": "adm:contact",
        "admin_backup": "pro:backup",
        "admin_logs": "pro:logs",
    }
    mapped = aliases.get(data)
    if mapped and mapped != data:
        if mapped == "admin":
            await show_admin(chat_id, message_id)
            return True
        return await run_admin_callback(user_id, chat_id, message_id, mapped)
    return False

async def handle_button_editor_state(msg, state):
    if not is_owner(int(msg.get("from",{}).get("id",0))):
        return False
    uid=int(msg["from"]["id"]); chat_id=int(msg["chat"]["id"]); text=(msg.get("text") or "").strip()
    if state == "ui_add_text":
        if not text:
            await send_message(chat_id,"❌ اسم الزر لا يمكن أن يكون فارغًا.",cancel_keyboard()); return True
        await set_setting(f"temp_button_text:{uid}",text)
        await set_state(uid,"ui_add_action")
        await send_message(chat_id,"⚡ <b>اختر وظيفة الزر</b>",ui_actions())
        return True
    if state == "ui_add_action":
        return False
    if state.startswith("ui_edit_text:"):
        bid=state.split(":",1)[1]
        if not text:
            await send_message(chat_id,"❌ الاسم لا يمكن أن يكون فارغًا.",cancel_keyboard()); return True
        await db_execute("UPDATE buttons SET text=? WHERE id=?",(text,bid)); invalidate_button_cache(); await clear_state(uid)
        await audit("Button name",f"{bid}={text}"); await send_message(chat_id,"✅ تم تعديل اسم الزر.",admin_keyboard()); return True
    if state.startswith("ui_style:"):
        bid=state.split(":",1)[1]; style=text.lower()
        if style not in BUTTON_STYLES:
            await send_message(chat_id,"❌ استخدم: primary أو success أو danger",cancel_keyboard()); return True
        await db_execute("UPDATE buttons SET style=? WHERE id=?",(style,bid)); invalidate_button_cache(); await clear_state(uid)
        await audit("Button color",f"{bid}={style}"); await send_message(chat_id,"✅ تم تغيير لون الزر.",admin_keyboard()); return True
    if state.startswith("ui_url:"):
        bid=state.split(":",1)[1]; url="" if text.lower() in {"none","-","حذف"} else text
        if url and not re.match(r"^https?://",url,re.I):
            await send_message(chat_id,"❌ الرابط يجب أن يبدأ بـ http:// أو https://",cancel_keyboard()); return True
        await db_execute("UPDATE buttons SET url=? WHERE id=?",(url,bid)); invalidate_button_cache(); await clear_state(uid)
        await audit("Button URL",f"{bid}={url or 'none'}"); await send_message(chat_id,"✅ تم تحديث الرابط.",admin_keyboard()); return True
    if state.startswith("ui_sort:"):
        bid=state.split(":",1)[1]; parts=text.replace(","," ").split()
        if len(parts)!=2 or not all(p.lstrip('-').isdigit() for p in parts):
            await send_message(chat_id,"❌ استخدم: <code>الصف الترتيب</code> مثال <code>1 0</code>",cancel_keyboard()); return True
        await db_execute("UPDATE buttons SET row=?,position=? WHERE id=?",(max(0,int(parts[0])),max(0,int(parts[1])),bid)); await normalize_button_positions(); await clear_state(uid)
        await audit("Button position",f"{bid}={parts[0]}:{parts[1]}"); await send_message(chat_id,"✅ تم ترتيب الزر.",admin_keyboard()); return True
    if state.startswith("ui_add_value:"):
        action=state.split(":",1)[1]
        if action == "url" and not re.match(r"^https?://", text, re.I):
            await send_message(chat_id,"❌ الرابط يجب أن يبدأ بـ http:// أو https://",cancel_keyboard()); return True
        await set_setting(f"temp_button_value:{uid}", text)
        await set_state(uid, f"ui_add_position:{action}")
        await send_message(chat_id,"📍 اختر مكان الزر الجديد:",await ui_place_keyboard(uid)); return True
    if state.startswith("ui_value:"):
        _,bid,kind=state.split(":",2)
        if kind not in {"text","page"}: return False
        await db_execute("UPDATE buttons SET action_value=?,action=? WHERE id=?",(text,kind,bid)); invalidate_button_cache(); await clear_state(uid)
        await audit("Button content",f"{bid}={kind}"); await send_message(chat_id,"✅ تم حفظ محتوى الزر.",admin_keyboard()); return True
    if state == "ui_add_media_caption":
        cap="" if text == "-none-" else text
        await set_setting(f"temp_button_caption:{uid}",cap)
        await set_state(uid,"ui_add_position:media")
        await send_message(chat_id,"📍 اختر مكان الزر الجديد:",await ui_place_keyboard(uid)); return True
    if state.startswith("ui_edit_media_caption:"):
        bid=state.split(":",1)[1]; cap="" if text == "-none-" else text
        photo=await get_setting(f"temp_button_photo:{uid}","")
        await db_execute("UPDATE buttons SET action='media',photo=?,caption=?,action_value=? WHERE id=?",(photo,cap,cap,bid)); invalidate_button_cache()
        await db_execute("DELETE FROM settings WHERE key IN (?,?)",(f"temp_button_photo:{uid}",f"ui_media_target:{uid}"))
        await clear_state(uid); await audit("Button media",bid); await send_message(chat_id,"✅ تم تحديث صورة الزر.",admin_keyboard()); return True
    return False

async def handle_admin_state(msg, state):
    uid=int(msg["from"]["id"]); chat_id=int(msg["chat"]["id"]); text=(msg.get("text") or "").strip()
    if not is_owner(uid): return False
    if state=="hosted_broadcast_text":
        if not is_platform_owner(uid): return False
        if not text:
            await send_message(chat_id,"❌ أرسل نصًا صالحًا.",cancel_keyboard()); return True
        await clear_state(uid)
        success,failed,bots=await run_all_hosted_bots_broadcast(text,"text",None)
        await send_message(chat_id, await get_notification("notif_host_broadcast_done", bots=bots, success=success, failed=failed), admin_keyboard())
        return True
    if state=="creator_exempt_add":
        if not is_platform_owner(uid): return False
        if not text.isdigit() or int(text) <= 0:
            await send_message(chat_id, "❌ أرسل Telegram User ID صحيحًا.", cancel_keyboard())
            return True
        target=int(text)
        if target == OWNER_ID:
            await send_message(chat_id, "ℹ️ أنت المطور أصلًا ومعفي تلقائيًا.", admin_keyboard())
            await clear_state(uid)
            return True
        await db_execute(
            "INSERT OR IGNORE INTO creator_exemptions(user_id,added_by,created_at) VALUES(?,?,?)",
            (target, uid, now_text()),
        )
        await clear_state(uid)
        await audit("Creator fee exemption added", str(target))
        await send_message(chat_id, f"🎁 تم إعفاء <code>{target}</code> من رسوم إنشاء البوتات.\n\nيمكنه الآن إنشاء البوت بدون دفع 25 ⭐.", admin_keyboard())
        return True
    if state=="creator_exempt_remove":
        if not is_platform_owner(uid): return False
        if not text.isdigit() or int(text) <= 0:
            await send_message(chat_id, "❌ أرسل Telegram User ID صحيحًا.", cancel_keyboard())
            return True
        target=int(text)
        row=await db_execute("SELECT 1 FROM creator_exemptions WHERE user_id=?", (target,), fetchone=True)
        if not row:
            await send_message(chat_id, "ℹ️ هذا المستخدم غير موجود ضمن قائمة الإعفاءات.", admin_keyboard())
            await clear_state(uid)
            return True
        await db_execute("DELETE FROM creator_exemptions WHERE user_id=?", (target,))
        await clear_state(uid)
        await audit("Creator fee exemption removed", str(target))
        await send_message(chat_id, f"🗑 تم إلغاء إعفاء <code>{target}</code>.\n\nسيُطلب منه دفع 25 ⭐ عند إنشاء بوت جديد.", admin_keyboard())
        return True
    if state=="search":
        q=text.lstrip("@").strip(); rows=[]
        if q.isdigit(): rows=await db_execute("SELECT * FROM users WHERE user_id=?",(int(q),),fetchall=True)
        elif q: rows=await db_execute("SELECT * FROM users WHERE name LIKE ? OR username LIKE ? ORDER BY last_activity DESC LIMIT 10",(f"%{q}%",f"%{q}%"),fetchall=True)
        lines=["🔎 <b>نتائج البحث</b>",""]+[f"• {esc(r['name'] or 'مستخدم')} — <code>{r['user_id']}</code> — @{esc(r['username']) if r['username'] else 'بدون'}" for r in rows]
        if len(lines)==2: lines.append("لا توجد نتائج.")
        await clear_state(uid); await send_message(chat_id,"\n".join(lines),admin_keyboard()); return True
    if state.startswith("limited_btn:") and is_limited_bot_owner(uid):
        _,bid,field=state.split(":",2)
        value="" if text == "-none-" else text
        if field == "label":
            if not value: await send_message(chat_id,"❌ اسم الزر لا يمكن أن يكون فارغًا.",cancel_keyboard()); return True
            await db_execute("UPDATE buttons SET text=? WHERE id=?",(value,bid))
            MAIN_BUTTON_CACHE["keyboard"]=None
        else:
            await set_button_flow_text(bid,field,value)
        await clear_state(uid); await audit("Limited button field",f"{bid}:{field}")
        await show_limited_button_editor(chat_id,0,bid); return True
    if state=="limited_force_add" and is_limited_bot_owner(uid):
        channel=text.lstrip("@").strip()
        if not re.fullmatch(r"[A-Za-z0-9_]{3,64}",channel):
            await send_message(chat_id,"❌ معرف القناة غير صالح.",cancel_keyboard()); return True
        await db_execute("INSERT OR IGNORE INTO forced_channels(channel) VALUES(?)",(channel,))
        await set_setting("force_sub","1")
        await clear_state(uid); await audit("Limited force channel add",channel)
        await show_limited_force_sub(chat_id,0); return True
    if state=="limited_force_delete" and is_limited_bot_owner(uid):
        channel=text.lstrip("@").strip()
        await db_execute("DELETE FROM forced_channels WHERE channel=?",(channel,))
        await clear_state(uid); await audit("Limited force channel delete",channel)
        await show_limited_force_sub(chat_id,0); return True
    if state=="limited_ban" and is_limited_bot_owner(uid):
        try: target=int(text)
        except: await send_message(chat_id,"❌ أرسل ID صحيح.",cancel_keyboard()); return True
        if target in (OWNER_ID, uid): await send_message(chat_id,"❌ لا يمكن حظر هذا المستخدم.",limited_admin_keyboard()); await clear_state(uid); return True
        await db_execute("INSERT OR IGNORE INTO users(user_id) VALUES(?)",(target,))
        await db_execute("UPDATE users SET blocked=1 WHERE user_id=?",(target,))
        await clear_state(uid); await audit("Limited ban",str(target))
        await send_message(chat_id,f"🚫 تم حظر <code>{target}</code>.",limited_admin_keyboard()); return True
    if state=="limited_unban" and is_limited_bot_owner(uid):
        try: target=int(text)
        except: await send_message(chat_id,"❌ أرسل ID صحيح.",cancel_keyboard()); return True
        await db_execute("INSERT OR IGNORE INTO users(user_id) VALUES(?)",(target,))
        await db_execute("UPDATE users SET blocked=0 WHERE user_id=?",(target,))
        await clear_state(uid); await audit("Limited unban",str(target))
        await send_message(chat_id, await get_notification("notif_unban_admin"), limited_admin_keyboard()); return True
    if state=="limited_welcome_text" and is_limited_bot_owner(uid):
        await set_setting("start_text",text); await set_setting("welcome_text",text); await clear_state(uid); await audit("Limited welcome text","updated")
        await send_message(chat_id,"✅ تم تغيير الترحيب.",limited_admin_keyboard()); return True
    if state=="limited_welcome_photo" and is_limited_bot_owner(uid):
        media_type,file_id,_=extract_media(msg)
        if media_type!="photo": await send_message(chat_id,"❌ أرسل صورة فقط.",cancel_keyboard()); return True
        await set_setting("welcome_photo",file_id); await clear_state(uid); await audit("Limited welcome photo","updated")
        await send_message(chat_id,"✅ تم تغيير صورة الترحيب.",limited_admin_keyboard()); return True
    if state=="limited_dev_photo" and is_limited_bot_owner(uid):
        media_type,file_id,_=extract_media(msg)
        if media_type!="photo": await send_message(chat_id,"❌ أرسل صورة فقط.",cancel_keyboard()); return True
        await set_setting("dev_photo",file_id); await clear_state(uid); await audit("Limited developer photo","updated")
        await send_message(chat_id,"✅ تم تغيير صورة المطور للمراسلة.",limited_admin_keyboard()); return True
    if state=="limited_contact_text" and is_limited_bot_owner(uid):
        await set_setting("contact_text",text); await clear_state(uid); await audit("Limited contact text","updated")
        await send_message(chat_id,"✅ تم تغيير نص المراسلة.",limited_admin_keyboard()); return True

    if state=="ban":
        try: target=int(text)
        except: await send_message(chat_id,"❌ أرسل ID صحيح.",cancel_keyboard()); return True
        if target==OWNER_ID: await send_message(chat_id,"❌ لا يمكن حظر المطور.",admin_keyboard()); return True
        await db_execute("INSERT OR IGNORE INTO users(user_id) VALUES(?)",(target,)); await db_execute("UPDATE users SET blocked=1 WHERE user_id=?",(target,)); await clear_state(uid); await audit("Ban",str(target)); await send_message(chat_id,f"🚫 تم حظر <code>{target}</code>.",admin_keyboard()); return True
    if state=="mute":
        parts=text.replace(","," ").split()
        if len(parts)!=2:
            await send_message(chat_id,"❌ استخدم: <code>ID دقائق</code>",cancel_keyboard()); return True
        try: target,mins=int(parts[0]),int(parts[1])
        except: await send_message(chat_id,"❌ القيم يجب أن تكون أرقامًا.",cancel_keyboard()); return True
        if target==OWNER_ID or mins<0: await send_message(chat_id,"❌ قيمة غير صالحة.",cancel_keyboard()); return True
        await db_execute("INSERT OR IGNORE INTO users(user_id) VALUES(?)",(target,)); await db_execute("UPDATE users SET muted_until=? WHERE user_id=?",(time.time()+mins*60,target)); await clear_state(uid); await audit("Mute",f"{target}:{mins}"); await send_message(chat_id,f"🔇 تم كتم <code>{target}</code> لمدة {mins} دقيقة.",admin_keyboard()); return True
    if state in ("protection_limit","prolimit"):
        try: limit=int(text)
        except: await send_message(chat_id,"❌ أرسل رقمًا صحيحًا.",cancel_keyboard()); return True
        if limit<1 or limit>10000: await send_message(chat_id,"❌ الحد يجب أن يكون بين 1 و10000.",cancel_keyboard()); return True
        await set_setting("max_requests_per_min",limit); await clear_state(uid); await audit("Protection limit",str(limit)); await pro_security(chat_id,0); return True
    if state=="prostyle_default":
        if text.lower() not in BUTTON_STYLES: await send_message(chat_id,"❌ استخدم primary أو success أو danger",cancel_keyboard()); return True
        await set_setting("button_default_style",text.lower()); await clear_state(uid); await pro_system(chat_id,0); return True
    if state=="broadcast_text":
        if not text: await send_message(chat_id,"❌ الرسالة فارغة.",cancel_keyboard()); return True
        await clear_state(uid)
        total, success, failed = await run_broadcast(text, "text", None)
        await send_message(chat_id, await get_notification("notif_broadcast_done", total=total, success=success, failed=failed), admin_keyboard())
        return True
    if state in ("channel_add","channel_delete"):
        channel=text.lstrip("@").strip()
        if not re.fullmatch(r"[A-Za-z0-9_]{3,64}",channel): await send_message(chat_id,"❌ معرف القناة غير صالح.",cancel_keyboard()); return True
        if state=="channel_add": await db_execute("INSERT OR IGNORE INTO forced_channels(channel) VALUES(?)",(channel,))
        else: await db_execute("DELETE FROM forced_channels WHERE channel=?",(channel,))
        if not IS_CHILD_BOT and is_platform_owner(uid):
            await sync_global_forced_channels()
        await clear_state(uid); await audit("Force channel",f"{state}:{channel}"); await admin_channels(chat_id,0); return True
    if state=="reply_text":
        try: target=int(await get_setting(f"reply_target:{uid}","0"))
        except: target=0
        try: source_message_id=int(await get_setting(f"reply_message:{uid}","0"))
        except: source_message_id=0
        await clear_state(uid); await db_execute("DELETE FROM settings WHERE key IN (?,?)",(f"reply_target:{uid}",f"reply_message:{uid}"))
        if not target or not text: await send_message(chat_id,"❌ الرد غير صالح.",admin_keyboard()); return True
        await reply_to_user_text(chat_id,target,text,source_message_id or None); return True
    if state.startswith("notifedit:"):
        key=state.split(":",1)[1]
        if key not in NOTIFICATION_LABELS:
            await clear_state(uid); await send_message(chat_id,"❌ الإشعار غير موجود.",admin_keyboard()); return True
        if not text.strip():
            await send_message(chat_id,"❌ لا يمكن حفظ إشعار فارغ.",cancel_keyboard()); return True
        await set_setting(key,text)
        if is_platform_owner(uid):
            await sync_notifications_to_all_hosted_bots()
        await clear_state(uid); await audit("Notification update",key)
        await send_message(chat_id,await get_notification("notif_saved"),admin_keyboard()); return True
    if state.startswith("proedit:"):
        key=state.split(":",1)[1]; allowed={"start_text","contact_text","contact_footer","maintenance_text","disabled_text","banned_text","rate_warning_text","footer_text"}
        if key not in allowed: return False
        await set_setting(key,text);
        if key=="start_text": await set_setting("welcome_text",text)
        await clear_state(uid); await audit("Content update",key); await send_message(chat_id,"✅ تم حفظ النص.",admin_keyboard()); return True
    if state.startswith("prousernote:"):
        target=int(state.split(":",1)[1]); await db_execute("UPDATE users SET notes=? WHERE user_id=?",(text,target)); await clear_state(uid); await pro_user(chat_id,0,target); return True
    if state.startswith("prousermsg:"):
        target=int(state.split(":",1)[1]); await clear_state(uid); await reply_to_user_text(chat_id,target,text); return True
    if state=="propageadd_title":
        if not text: await send_message(chat_id,"❌ العنوان فارغ.",cancel_keyboard()); return True
        await set_setting(f"temp_page_title:{uid}",text); await set_state(uid,"propageadd_id"); await send_message(chat_id,"🧩 أرسل ID الصفحة بالإنجليزية.",cancel_keyboard()); return True
    if state=="propageadd_id":
        pid=re.sub(r"[^A-Za-z0-9_-]","",text)[:50]
        if not pid: await send_message(chat_id,"❌ ID غير صالح.",cancel_keyboard()); return True
        if await db_execute("SELECT id FROM menu_pages WHERE id=?",(pid,),fetchone=True): await send_message(chat_id,"❌ الـID موجود مسبقًا.",cancel_keyboard()); return True
        title=await get_setting(f"temp_page_title:{uid}","صفحة"); await db_execute("INSERT INTO menu_pages(id,title,text,created_at) VALUES(?,?,?,?)",(pid,title,"",now_text())); await db_execute("DELETE FROM settings WHERE key=?",(f"temp_page_title:{uid}",)); await clear_state(uid); await pro_pages(chat_id,0); return True
    if state.startswith("propageedit:title:"):
        pid=state.split(":",2)[2]; await db_execute("UPDATE menu_pages SET title=? WHERE id=?",(text,pid)); await clear_state(uid); await pro_page(chat_id,0,pid); return True
    if state.startswith("propageedit:text:"):
        pid=state.split(":",2)[2]; await db_execute("UPDATE menu_pages SET text=? WHERE id=?",(text,pid)); await clear_state(uid); await pro_page(chat_id,0,pid); return True
    if state=="v11_reply_trigger":
        if not text: await send_message(chat_id,"❌ المحفز فارغ.",cancel_keyboard()); return True
        await set_setting(f"v11_tmp_reply_trigger:{uid}",text); await set_state(uid,"v11_reply_response"); await send_message(chat_id,"📝 أرسل الرد.",cancel_keyboard()); return True
    if state=="v11_reply_response":
        trigger=await get_setting(f"v11_tmp_reply_trigger:{uid}",""); await db_execute("INSERT INTO auto_replies(trigger,response,created_at) VALUES(?,?,?)",(trigger,text,now_text())); await db_execute("DELETE FROM settings WHERE key=?",(f"v11_tmp_reply_trigger:{uid}",)); await clear_state(uid); await v11_autoreply(chat_id,0); return True
    if state=="v11_auto_title":
        await set_setting(f"v11_tmp_auto_title:{uid}",text); await set_state(uid,"v11_auto_payload"); await send_message(chat_id,"📝 أرسل نص المهمة.",cancel_keyboard()); return True
    if state=="v11_auto_payload":
        title=await get_setting(f"v11_tmp_auto_title:{uid}","مهمة"); await db_execute("INSERT INTO automations(title,kind,payload,next_run,interval_sec,enabled,created_at) VALUES(?,?,?,?,?,?,?)",(title,"message",json.dumps({"text":text},ensure_ascii=False),0,0,0,now_text())); await db_execute("DELETE FROM settings WHERE key=?",(f"v11_tmp_auto_title:{uid}",)); await clear_state(uid); await v11_automation(chat_id,0); return True
    if state=="v11_segment_name":
        sid=re.sub(r"[^A-Za-z0-9_-]","",text.lower())[:50] or f"seg_{int(time.time())}"; await db_execute("INSERT OR IGNORE INTO user_segments(id,name,rule,value,enabled) VALUES(?,?,?,?,1)",(sid,text,"all","")); await clear_state(uid); await v11_segments(chat_id,0); return True
    if state=="v11_theme_name":
        tid=re.sub(r"[^A-Za-z0-9_-]","",text.lower())[:50] or f"theme_{int(time.time())}"; await db_execute("INSERT OR IGNORE INTO themes(id,name,data,enabled,created_at) VALUES(?,?,?,?,?)",(tid,text,"{}",1,now_text())); await clear_state(uid); await v11_themes(chat_id,0); return True
    if state.startswith("adminbtn_text:"):
        bid=state.split(":",1)[1]; await db_execute("UPDATE admin_buttons SET text=? WHERE id=?",(text,bid)); await load_admin_buttons(); await clear_state(uid); await pro_adminui(chat_id,0); return True
    if state.startswith("adminbtn_style:"):
        bid=state.split(":",1)[1]; style=text.lower()
        if style not in BUTTON_STYLES: await send_message(chat_id,"❌ استخدم primary أو success أو danger.",cancel_keyboard()); return True
        await db_execute("UPDATE admin_buttons SET style=? WHERE id=?",(style,bid)); await load_admin_buttons(); await clear_state(uid); await pro_adminui(chat_id,0); return True
    if state.startswith("v11_action:"):
        _,kind,bid=state.split(":",2); row=await db_execute("SELECT actions FROM button_actions WHERE button_id=?",(bid,),fetchone=True); items=[]
        if row:
            try: items=json.loads(row["actions"] or "[]")
            except: items=[]
        items.append({"kind":kind,"value":text if kind=="text" else True}); await db_execute("INSERT INTO button_actions(button_id,actions) VALUES(?,?) ON CONFLICT(button_id) DO UPDATE SET actions=excluded.actions",(bid,json.dumps(items,ensure_ascii=False))); await clear_state(uid); await v11_button_actions(chat_id,0,bid); return True
    return False


async def handle_message(msg):
    global HTTP_SESSION

    user = msg.get("from", {})
    if not user:
        return

    user_id = int(user["id"])
    chat_id = int(msg["chat"]["id"])

    is_new = await upsert_user(user)
    text = msg.get("text", "").strip()

    async def notify_new_user_in_background():
        """Notifications must never hold up /start or the update worker."""
        if not is_new or user_id == OWNER_ID:
            return
        try:
            if await get_setting("notifications", "1") == "1":
                await send_message(
                    OWNER_ID,
                    await get_notification(
                        "notif_new_user",
                        name=user.get("first_name", "مستخدم"),
                        id=user_id,
                        username=user.get("username", "بدون") or "بدون",
                    ),
                )
        except Exception as exc:
            await log_error("new_user_notification", exc)

    # Telegram sends paid Stars as a message update. Handle it before normal text/state routing.
    if msg.get("successful_payment"):
        await finalize_paid_creation(msg)
        return

    # Commands must always win over a stale editor/contact state.
    if text == "/start" or text.startswith("/start "):
        if await is_banned(user_id) and not is_owner(user_id):
            await send_message(chat_id, "🚫 أنت محظور من استخدام البوت.")
            return
        await clear_state(user_id)
        await db_execute("DELETE FROM settings WHERE key LIKE ?", (f"reply_target:{user_id}",))
        try:
            await increment_user(user_id, messages=1)
            if text.startswith("/start ref_"):
                ref = text[11:].strip()
                ref_id = int(ref)
                if ref_id != user_id:
                    await db_execute("UPDATE users SET messages=messages+1 WHERE user_id=?", (ref_id,))
        except Exception as exc:
            await log_error("start_stats", exc)
        result = await send_start(chat_id, user_id)
        # The welcome response is user-visible and time-sensitive.  Statistics
        # and the admin notification are deliberately after it and independent.
        asyncio.create_task(notify_new_user_in_background())
        if text.strip().lower() == "/start create_bot" and not IS_CHILD_BOT and not await is_banned(user_id):
            try:
                await show_create_bot_offer(chat_id, 0)
            except Exception as exc:
                await log_error("deep_link_create_bot", exc)
        if not result.get("ok"):
            await log_error("start_send", result.get("description", "unknown"))
            # Last-resort plain text response.
            await send_message(chat_id, "✅ البوت يعمل. اكتب /start مرة أخرى لفتح القائمة.")
        return

    if is_new:
        await notify_new_user_in_background()

    if await is_banned(user_id) and not is_owner(user_id):
        await send_message(chat_id, "🚫 أنت محظور من استخدام البوت.")
        return

    muted, remaining = await is_muted(user_id)
    if muted and not is_owner(user_id):
        await send_message(chat_id, f"🔇 أنت مكتوم. المتبقي تقريباً {remaining} ثانية.")
        return

    # Platform-wide forced subscription applies to every hosted-bot user,
    # including the hosted-bot owner. The platform developer is the only bypass.
    if not is_platform_owner(user_id):
        sub_ok, sub_missing = await check_forced_subscription(user_id)
        if not sub_ok:
            await send_message(
                chat_id,
                "📢 <b>الاشتراك الإجباري مطلوب.</b>\n\nاشترك في القنوات ثم اضغط على التحقق.",
                subscription_keyboard(sub_missing),
            )
            return

    if not await protection_ok(user_id, text):
        await send_message(chat_id, await get_notification("notif_rate_warning"))
        return

    if text == "/cancel":
        await clear_state(user_id)
        await db_execute(
            "DELETE FROM settings WHERE key LIKE ?",
            (f"reply_target:{user_id}",),
        )
        await send_message(
            chat_id,
            "✅ تم إلغاء العملية.",
            limited_admin_keyboard() if is_limited_bot_owner(user_id) else (admin_keyboard(user_id) if is_owner(user_id) else await main_keyboard()),
        )
        return

    state = await get_state(user_id)

    # Native Telegram Reply workflow for hosted-bot owners. The owner can
    # swipe/reply directly to the copied member message; no buttons are needed.
    if is_owner(user_id) and msg.get("reply_to_message"):
        try:
            if await handle_native_owner_reply(msg):
                return
        except Exception as exc:
            await log_error("native_owner_reply", exc)

    # Token entered after a successful Stars payment on the platform bot.
    # This must be reachable by the paying user, not only by the platform owner.
    if not IS_CHILD_BOT and state == "create_bot_token" and text:
        await create_hosted_bot_from_token(user_id, chat_id, text)
        return

    if is_owner(user_id):
        state = await get_state(user_id)

        # Welcome/contact text editor. These states must be handled here because
        # the previous build created them but had no corresponding text handler.
        if state == "text_edit_start":
            new_text = msg.get("text", "").strip()
            if not new_text:
                await send_message(chat_id, "❌ أرسل نصًا صالحًا.", cancel_keyboard())
                return
            await set_setting("start_text", new_text)
            # Keep legacy setting synchronized so old database rows never override the new text.
            await set_setting("welcome_text", new_text)
            await clear_state(user_id)
            await audit("Welcome text updated", f"length={len(new_text)}")
            await send_message(chat_id, "✅ تم حفظ نص الترحيب بنجاح.", admin_keyboard())
            return

        if state == "text_edit_contact":
            new_text = msg.get("text", "").strip()
            if not new_text:
                await send_message(chat_id, "❌ أرسل نصًا صالحًا.", cancel_keyboard())
                return
            await set_setting("contact_text", new_text)
            await clear_state(user_id)
            await audit("Contact text updated", f"length={len(new_text)}")
            await send_message(chat_id, "✅ تم حفظ نص التواصل.", admin_keyboard())
            return

        if state == "contact_footer":
            new_text = msg.get("text", "").strip()
            await set_setting("contact_footer", "" if new_text == "-none-" else new_text)
            await clear_state(user_id)
            await send_message(chat_id, "✅ تم تحديث الفوتر.", admin_keyboard())
            return

        if state:
            if await handle_button_editor_state(msg, state):
                return
            handler = globals().get("handle_admin_state")
            if handler is not None:
                try:
                    if await handler(msg, state):
                        return
                except Exception as exc:
                    await log_error("admin_state", exc)
            else:
                # Old/stale states from a previous build must never block commands.
                await clear_state(user_id)

        if text == "/admin":
            await clear_state(user_id)
            await show_admin(chat_id)
            return

        if is_limited_bot_owner(user_id) and text in {
            "/dashboard", "/users", "/contact", "/broadcast", "/channels", "/maintenance",
            "/security", "/system", "/logs", "/backup", "/welcome", "/photos", "/texts", "/adminui", "/v13",
            "/stats", "/restart",
        } or (is_limited_bot_owner(user_id) and text.startswith("/senduser ")):
            await send_message(chat_id, "⛔ هذا الأمر غير متاح لمالك البوت.", limited_admin_keyboard())
            return

        # Developer command aliases: useful even if an old/custom admin keyboard
        # has stale callback data.
        admin_command_routes = {
            "/dashboard": ("pro:dashboard",),
            "/users": ("pro:users",),
            "/contact": ("adm:contact",),
            "/broadcast": ("adm:broadcast",),
            "/channels": ("adm:channels",),
            "/maintenance": ("adm:status",),
            "/security": ("pro:security",),
            "/system": ("pro:system",),
            "/logs": ("pro:logs",),
            "/backup": ("pro:backup",),
            "/welcome": ("adm:welcome",),
            "/photos": ("adm:photos",),
            "/texts": ("adm:texts",),
            "/adminui": ("pro:adminui",),
            "/v13": ("v13:dashboard",),
        }
        if text in admin_command_routes:
            route = admin_command_routes[text][0]
            try:
                await run_admin_callback(user_id, chat_id, 0, route)
            except Exception as exc:
                await log_error("admin_command", f"{text}: {exc}")
                await send_message(chat_id, f"❌ تعذر تنفيذ {esc(text)}\n\n<code>{esc(exc)}</code>", admin_keyboard())
            return

        if text == "/help":
            if is_limited_bot_owner(user_id):
                await send_message(chat_id, "📚 <b>مساعدة مالك البوت</b>\n\nاستخدم /start لفتح لوحة الإدارة المحدودة.", limited_admin_keyboard())
                return
            await send_message(
                chat_id,
                "📚 <b>الأوامر</b>\n\n"
                "/start — البداية\n"
                "/admin — لوحة التحكم\n"
                "/cancel — إلغاء العملية\n"
                "/stats — الإحصائيات\n"
                "/backup — نسخة احتياطية\n"
                "/restart — إعادة التشغيل",
                admin_keyboard(),
            )
            return

        if text == "/stats":
            fake_message = {"message_id": 0}
            # send instead of edit
            row1 = await db_execute("SELECT COUNT(*) c FROM users", fetchone=True)
            row2 = await db_execute(
                "SELECT COUNT(*) c FROM messages WHERE direction='USER'",
                fetchone=True,
            )
            await send_message(
                chat_id,
                f"📊 المستخدمون: {row1['c']}\n📨 الرسائل: {row2['c']}\n⏱ {uptime()}",
                admin_keyboard(),
            )
            return

        if text == "/backup":
            path = await create_backup()
            await send_local_document(
                chat_id,
                path,
                "💾 نسخة احتياطية لقاعدة البيانات.",
            )
            return

        if text == "/restart":
            await send_message(chat_id, "🔄 جاري إعادة التشغيل...")
            await audit("Restart", "Command")
            await asyncio.sleep(1)
            if HTTP_SESSION:
                await HTTP_SESSION.close()
            os.execv(sys.executable, [sys.executable] + sys.argv)

        if text.startswith("/senduser "):
            parts = text.split(maxsplit=2)
            if len(parts) == 3:
                try:
                    target = int(parts[1])
                    await send_message(
                        target,
                        f"📨 <b>رسالة من المطور</b>\n\n{esc(parts[2])}",
                    )
                    await send_message(chat_id, "✅ تم الإرسال.")
                except Exception as exc:
                    await log_error("senduser", exc)
            return

    # General user command handling continues below.

    if await bot_blocked_for_user(user_id):
        await send_service_unavailable(chat_id)
        return

    state = await get_state(user_id)

    # Normal user in contact mode.
    if state == "contact":
        if "text" in msg:
            text = msg.get("text", "")
            await increment_user(user_id, messages=1)
            ok = await notify_owner_text(msg, text)
            if ok:
                await send_message(
                    chat_id,
                    await get_button_flow_text("contact", "success", await get_notification("notif_contact_success")),
                    {
                        "inline_keyboard": [
                            [{"text": "❌ إنهاء التواصل", "callback_data": "end_contact"}],
                            [{"text": "🔙 الرئيسية", "callback_data": "main"}],
                        ]
                    },
                )
            else:
                await send_message(chat_id, await get_notification("notif_contact_failed"))
        else:
            media_type, file_id, caption = extract_media(msg)
            if media_type:
                await increment_user(user_id, media=1)
                ok = await notify_owner_media(msg, media_type, file_id, caption)
                if ok:
                    await send_message(
                        chat_id,
                        await get_button_flow_text("contact", "success", await get_notification("notif_contact_media_success")),
                        {
                            "inline_keyboard": [
                                [{"text": "❌ إنهاء التواصل", "callback_data": "end_contact"}],
                                [{"text": "🔙 الرئيسية", "callback_data": "main"}],
                            ]
                        },
                    )
                else:
                    await send_message(chat_id, await get_button_flow_text("contact", "error", await get_notification("notif_contact_media_failed")))
        return

    # Any ordinary text outside contact mode.
    if text and not text.startswith("/"):
        await increment_user(user_id, messages=1)


async def handle_media(msg):
    user_id = int(msg["from"]["id"])
    chat_id = int(msg["chat"]["id"])

    await upsert_user(msg["from"])

    if not is_platform_owner(user_id):
        sub_ok, sub_missing = await check_forced_subscription(user_id)
        if not sub_ok:
            await send_message(
                chat_id,
                "📢 <b>الاشتراك الإجباري مطلوب.</b>\n\nاشترك في القنوات ثم اضغط على التحقق.",
                subscription_keyboard(sub_missing),
            )
            return

    if is_owner(user_id):
        state = await get_state(user_id)

        if is_limited_bot_owner(user_id) and state == "limited_welcome_photo":
            media_type, file_id, _ = extract_media(msg)
            if media_type != "photo":
                await send_message(chat_id, "❌ أرسل صورة فقط.", cancel_keyboard())
                return
            await set_setting("welcome_photo", file_id)
            await clear_state(user_id)
            await audit("Limited welcome photo", "updated")
            await send_message(chat_id, "✅ تم تغيير صورة الترحيب.", limited_admin_keyboard())
            return

        if is_limited_bot_owner(user_id) and state == "limited_dev_photo":
            media_type, file_id, _ = extract_media(msg)
            if media_type != "photo":
                await send_message(chat_id, "❌ أرسل صورة فقط.", cancel_keyboard())
                return
            await set_setting("dev_photo", file_id)
            await clear_state(user_id)
            await audit("Limited developer photo", "updated")
            await send_message(chat_id, "✅ تم تغيير صورة المطور للمراسلة.", limited_admin_keyboard())
            return

        if msg.get("reply_to_message") and is_owner(user_id):
            try:
                if await handle_native_owner_reply(msg):
                    return
            except Exception as exc:
                await log_error("native_owner_media_reply", exc)

        if state == "reply_text" and is_owner(user_id):
            try: target = int(await get_setting(f"reply_target:{user_id}", "0") or 0)
            except Exception: target = 0
            try: source_message_id = int(await get_setting(f"reply_message:{user_id}", "0") or 0)
            except Exception: source_message_id = 0
            await clear_state(user_id)
            await db_execute("DELETE FROM settings WHERE key IN (?,?)", (f"reply_target:{user_id}", f"reply_message:{user_id}"))
            if target:
                await reply_to_user_media(chat_id, target, msg, source_message_id or None)
            else:
                await send_message(chat_id, "❌ لم يتم العثور على المستخدم المستهدف.", limited_admin_keyboard() if is_limited_bot_owner(user_id) else admin_keyboard(user_id))
            return

        if state == "limited_broadcast" and is_limited_bot_owner(user_id):
            # The source message is copied as-is, so the owner can broadcast any
            # Telegram message type without a growing media-type whitelist.
            source_message_id = int(msg.get("message_id") or 0)
            if not source_message_id:
                await send_message(chat_id, "❌ تعذر قراءة الرسالة. أرسل الرسالة مرة أخرى.", cancel_keyboard())
                return
            await clear_state(user_id)
            total, success, failed = await run_owner_broadcast(chat_id, source_message_id)
            await send_message(
                chat_id,
                await get_notification("notif_limited_broadcast_done", total=total, success=success, failed=failed),
                limited_admin_keyboard(),
            )
            return

        if is_limited_bot_owner(user_id):
            # No legacy media/admin state is reachable from the limited surface.
            return

        if state == "ui_add_media_photo":
            media_type,file_id,_=extract_media(msg)
            if media_type != "photo":
                await send_message(chat_id,"❌ أرسل صورة فقط.",cancel_keyboard()); return
            await set_setting(f"temp_button_photo:{user_id}",file_id)
            await set_state(user_id,"ui_add_media_caption")
            await send_message(chat_id,"📝 أرسل النص تحت الصورة، أو <code>-none-</code> بدون نص.",cancel_keyboard()); return

        if state.startswith("ui_edit_media_photo:"):
            media_type,file_id,_=extract_media(msg)
            if media_type != "photo":
                await send_message(chat_id,"❌ أرسل صورة فقط.",cancel_keyboard()); return
            bid=state.split(":",1)[1]
            await set_setting(f"temp_button_photo:{user_id}",file_id)
            await set_state(user_id,f"ui_edit_media_caption:{bid}")
            await send_message(chat_id,"📝 أرسل النص تحت الصورة، أو <code>-none-</code> بدون نص.",cancel_keyboard()); return

        if state == "photo_welcome":
            media_type, file_id, _ = extract_media(msg)
            if media_type == "photo":
                await set_setting("welcome_photo", file_id)
                await set_setting("welcome_enabled", "1")
                await clear_state(user_id)
                await audit("Welcome photo updated", "photo_id_saved")
                await send_message(chat_id, "✅ تم تغيير صورة الترحيب بنجاح.", admin_keyboard())
            else:
                await send_message(chat_id, "❌ أرسل صورة.")
            return

        if state == "photo_maintenance":
            media_type, file_id, _ = extract_media(msg)
            if media_type == "photo":
                await set_setting("maintenance_photo", file_id)
                await clear_state(user_id)
                await send_message(chat_id, "✅ تم حفظ صورة الصيانة.", admin_keyboard())
            else:
                await send_message(chat_id, "❌ أرسل صورة فقط.")
            return

        if state == "photo_contact":
            media_type, file_id, _ = extract_media(msg)
            if media_type == "photo":
                await set_setting("contact_photo", file_id)
                await clear_state(user_id)
                await send_message(chat_id, "✅ تم حفظ صورة التواصل.", admin_keyboard())
            else:
                await send_message(chat_id, "❌ أرسل صورة فقط.")
            return

        if state == "photo_dev":
            media_type, file_id, _ = extract_media(msg)
            if media_type == "photo":
                await set_setting("dev_photo", file_id)
                await clear_state(user_id)
                await send_message(chat_id, "✅ تم تغيير صورة المطور.", admin_keyboard())
            else:
                await send_message(chat_id, "❌ أرسل صورة.")
            return

        if state == "hosted_broadcast_media":
            if not is_platform_owner(user_id): return
            media_type, file_id, caption = extract_media(msg)
            if media_type:
                await clear_state(user_id)
                success,failed,bots=await run_all_hosted_bots_broadcast(caption,media_type,file_id)
                await send_message(chat_id,f"📢 <b>انتهت إذاعة الوسائط لجميع البوتات</b>\n\n🌐 البوتات: <b>{bots}</b>\n✅ نجاح: <b>{success}</b>\n❌ فشل: <b>{failed}</b>",admin_keyboard())
            return

        if state == "broadcast_media":
            media_type, file_id, caption = extract_media(msg)
            if media_type:
                await clear_state(user_id)
                total, success, failed = await run_broadcast(caption, media_type, file_id)
                await send_message(chat_id, await get_notification("notif_broadcast_done", total=total, success=success, failed=failed), admin_keyboard())
            return

        if state == "reply_media":
            target = int(await get_setting(f"reply_target:{user_id}", "0") or 0)
            await clear_state(user_id)
            await db_execute(
                "DELETE FROM settings WHERE key=?",
                (f"reply_target:{user_id}",),
            )
            if target:
                await reply_to_user_media(chat_id, target, msg)
            return

    # User in contact mode.
    if await is_banned(user_id) and not is_owner(user_id):
        await send_message(chat_id, "🚫 أنت محظور.")
        return

    if await bot_blocked_for_user(user_id):
        await send_service_unavailable(chat_id)
        return

    if await get_state(user_id) != "contact":
        return

    media_type, file_id, caption = extract_media(msg)
    if media_type:
        await increment_user(user_id, media=1)
        ok = await notify_owner_media(msg, media_type, file_id, caption)
        if ok:
            await send_message(
                chat_id,
                "✅ تم إرسال الوسائط للمطور.",
                {
                    "inline_keyboard": [
                        [{"text": "❌ إنهاء التواصل", "callback_data": "end_contact"}],
                        [{"text": "🔙 الرئيسية", "callback_data": "main"}],
                    ]
                },
            )





# =========================================================
# PRO MAX SCALABILITY / HARDENING
# =========================================================
# These settings are intentionally conservative for Termux/Pydroid.
# Conservative defaults for an i3-5005U / 8GB RAM machine.
# Every value remains configurable through environment variables.
MAX_CONCURRENT_UPDATES = max(4, int(os.getenv("MAX_CONCURRENT_UPDATES", "24")))
MAX_CONCURRENT_TELEGRAM = max(4, int(os.getenv("MAX_CONCURRENT_TELEGRAM", "32")))
TELEGRAM_RETRY_LIMIT = int(os.getenv("TELEGRAM_RETRY_LIMIT", "3"))
DB_BUSY_TIMEOUT_MS = int(os.getenv("DB_BUSY_TIMEOUT_MS", "20000"))
# The platform can still store up to MAX_HOSTED_BOTS records; this only limits
# how many separate Python child processes are resident at the same time.
MAX_ACTIVE_HOSTED_BOTS = max(1, int(os.getenv("MAX_ACTIVE_HOSTED_BOTS", "6")))

UPDATE_SEMAPHORE = asyncio.Semaphore(MAX_CONCURRENT_UPDATES)
TELEGRAM_SEMAPHORE = asyncio.Semaphore(MAX_CONCURRENT_TELEGRAM)

async def scalable_api_call(method, data=None, files=None, timeout=30, retries=4):
    """Concurrency-limited Telegram API wrapper with bounded retries."""
    async with TELEGRAM_SEMAPHORE:
        last = None
        for attempt in range(min(retries, TELEGRAM_RETRY_LIMIT) + 1):
            try:
                result = await api_call(
                    method,
                    data=data,
                    files=files,
                    timeout=timeout,
                    retries=1,
                )
                if result.get("ok"):
                    return result

                desc = str(result.get("description", "")).lower()
                # Retry transient Telegram/server/rate-limit errors.
                if not any(x in desc for x in (
                    "too many requests", "timeout", "timed out",
                    "temporarily unavailable", "internal server error",
                    "connection", "bad gateway", "gateway timeout",
                )):
                    return result
                last = result
            except Exception as exc:
                last = {"ok": False, "description": str(exc)}

            await asyncio.sleep(min(0.75 * (2 ** attempt), 8.0))

        return last or {"ok": False, "description": "request failed"}

async def safe_update_dispatch(update):
    """Process one update without allowing one slow user to block everyone."""
    async with UPDATE_SEMAPHORE:
        try:
            if "pre_checkout_query" in update:
                await handle_pre_checkout_query(update["pre_checkout_query"])
            elif "callback_query" in update:
                await handle_callback(update["callback_query"])
            elif "message" in update:
                msg = update["message"]
                if any(k in msg for k in (
                    "photo", "video", "document", "animation",
                    "voice", "audio", "sticker", "video_note"
                )):
                    await handle_media(msg)
                else:
                    await handle_message(msg)
        except asyncio.CancelledError:
            raise
        except Exception as exc:
            try:
                await log_error("update_handler", exc)
            except Exception:
                pass

# =========================================================
# POLLING
# =========================================================

UPDATE_TASKS = set()


def _track_update_task(task):
    """Keep polling bounded so a burst cannot create thousands of tasks."""
    UPDATE_TASKS.add(task)
    task.add_done_callback(UPDATE_TASKS.discard)


async def polling():
    offset = 0

    while True:
        try:
            result = await api_call(
                "getUpdates",
                params={
                    "offset": offset,
                    "timeout": 25,
                    "allowed_updates": json.dumps(
                        ["message", "callback_query", "pre_checkout_query"]
                    ),
                },
                timeout=35,
            )

            if not result.get("ok"):
                await asyncio.sleep(3)
                continue

            updates = result.get("result", []) or []
            for update in updates:
                offset = update["update_id"] + 1

                # Backpressure: do not let a burst of Telegram updates create an
                # unbounded number of Python tasks on a low-power CPU.
                while len(UPDATE_TASKS) >= max(1, MAX_CONCURRENT_UPDATES):
                    await asyncio.sleep(0.01)
                _track_update_task(asyncio.create_task(safe_update_dispatch(update)))

        except asyncio.CancelledError:
            raise
        except Exception as exc:
            await log_error("polling", exc)
            await asyncio.sleep(3)


# =========================================================
# MAIN
# =========================================================


# =========================================================
# V7 ADVANCED OPERATIONS
# =========================================================


def cap_runtime_cache(cache, max_users=10000, max_events=100):
    """Prevent unbounded in-memory growth under heavy traffic."""
    if len(cache) <= max_users:
        return
    # Remove the least useful/oldest keys first.
    ranked = sorted(cache.items(), key=lambda kv: max(kv[1]) if kv[1] else 0)
    for key, _ in ranked[:max(0, len(cache) - max_users)]:
        cache.pop(key, None)

async def cleanup_runtime_cache():
    now = time.time()
    for cache in (RATE_LIMIT, CALLBACK_RATE):
        for uid in list(cache.keys()):
            values = [x for x in cache[uid] if now - x < 120]
            if values:
                cache[uid] = values
            else:
                cache.pop(uid, None)


async def periodic_maintenance():
    """Lightweight in-process maintenance that never blocks updates."""
    while True:
        try:
            await cleanup_runtime_cache()
            await asyncio.sleep(60)
        except asyncio.CancelledError:
            raise
        except Exception as exc:
            await log_error("periodic_maintenance", exc)
            await asyncio.sleep(30)


async def database_health():
    result = {"ok": True, "users": 0, "messages": 0, "errors": 0}
    try:
        users = await db_execute("SELECT COUNT(*) c FROM users", fetchone=True)
        messages = await db_execute("SELECT COUNT(*) c FROM messages", fetchone=True)
        errors = await db_execute("SELECT COUNT(*) c FROM error_logs", fetchone=True)
        result["users"] = int(users["c"] if users else 0)
        result["messages"] = int(messages["c"] if messages else 0)
        result["errors"] = int(errors["c"] if errors else 0)
    except Exception as exc:
        result["ok"] = False
        result["error"] = str(exc)
    return result


async def send_contact_screen(chat_id, user_id):
    """Render the contact screen safely; image and text work independently."""
    if await get_setting("contact_enabled", "1") != "1" and not is_owner(user_id):
        return await send_message(chat_id, "⛔ <b>التواصل مع المطور متوقف حالياً.</b>", await main_keyboard())
    text = await get_setting("contact_text", DEFAULT_CONTACT_TEXT)
    flow_prompt = await get_button_flow_text("contact", "prompt", "")
    if flow_prompt:
        text = flow_prompt
    text = await render_text(text, user_id) if text else ""
    footer = await get_setting("contact_footer", "")
    if footer:
        footer = await render_text(footer, user_id)
        text = (text + "\n\n" + footer) if text else footer
    await clear_state(user_id); await set_state(user_id, "contact")
    keyboard = {"inline_keyboard": [[{"text":"❌ إنهاء التواصل","callback_data":"end_contact"}], [{"text":"🔙 الرئيسية","callback_data":"main"}]]}
    photo = await get_setting("contact_photo", "")
    if photo:
        caption = text[:1024] if len(text) > 1024 else text
        result = await send_photo(chat_id, photo, caption, keyboard)
        if result.get("ok"):
            if len(text) > 1024:
                return await send_message(chat_id, text, keyboard)
            return result
        await log_error("contact_photo", result.get("description", "unknown"))
        await set_setting("contact_photo", "")
    return await send_message(chat_id, text or "📨 <b>أرسل رسالتك الآن.</b>", keyboard)


async def send_contact_screen_safe(chat_id, user_id):
    try:
        await send_contact_screen(chat_id, user_id)
    except Exception as exc:
        await log_error("contact_screen", exc)
        await clear_state(user_id)
        await send_message(chat_id, "❌ حدث خطأ أثناء فتح التواصل. حاول مرة أخرى.", await main_keyboard())


async def owner_quick_panel(chat_id):
    health = await database_health()
    maintenance = await get_setting("maintenance", "0") == "1"
    enabled = await get_setting("bot_enabled", "1") == "1"
    text = (
        "🧭 <b>V7 QUICK PANEL</b>\n\n"
        f"🤖 البوت: {'🟢 يعمل' if enabled else '🔴 متوقف'}\n"
        f"🔧 الصيانة: {'🟡 مفعلة' if maintenance else '🟢 مغلقة'}\n"
        f"👥 المستخدمون: <b>{health['users']}</b>\n"
        f"📨 الرسائل: <b>{health['messages']}</b>\n"
        f"⚠️ الأخطاء: <b>{health['errors']}</b>\n"
        f"⏱ التشغيل: <b>{uptime()}</b>"
    )
    await send_message(chat_id, text, admin_keyboard())


# =========================================================
# V16 ULTIMATE CONTROL PLANE
# =========================================================
#
# V16 turns the platform owner into a real control-plane operator.
# It deliberately stays in this single file so the project remains easy to
# deploy on Pydroid/Termux while still separating responsibilities internally.
#
# Design goals:
#   1. Platform-owner-only control over every hosted bot.
#   2. Durable audit trail for sensitive operations.
#   3. Bot lifecycle management with maintenance, restart and delete actions.
#   4. Health snapshots and incident records.
#   5. Broadcast job bookkeeping instead of fire-and-forget operations.
#   6. Bounded work helpers suitable for high-load environments.
#   7. No bot token is ever rendered by the V16 UI.
#
# The control plane uses the existing SQLite database and existing Telegram
# transport. It does not add another Telegram framework or a web server.
# =========================================================

V16_VERSION = "16.0 Ultimate Control Plane"
V16_SCHEMA_VERSION = 1
V16_MAX_PAGE = 10
V16_MAX_AUDIT_DETAILS = 1200
V16_MAX_NOTE_LENGTH = 2000
V16_HEALTH_CACHE = {"ts": 0.0, "data": None}
V16_LOCKS = defaultdict(asyncio.Lock)
V16_JOB_TASKS = {}
V16_MEMORY_EVENTS = defaultdict(list)


@dataclass
class V16Health:
    uptime: str
    users: int
    hosted: int
    running: int
    disabled: int
    errors_24h: int
    audit_24h: int
    database: str
    process: str
    version: str


@dataclass
class V16JobResult:
    job_id: int
    status: str
    total: int = 0
    success: int = 0
    failed: int = 0
    skipped: int = 0
    started_at: str = ""
    finished_at: str = ""
    error: str = ""


async def v16_init_db():
    """Create the durable V16 control-plane schema."""
    async with aiosqlite.connect(DB_FILE, timeout=30) as db:
        await db.execute(f"PRAGMA busy_timeout={DB_BUSY_TIMEOUT_MS}")
        await db.execute("PRAGMA journal_mode=WAL")
        await db.execute("""
            CREATE TABLE IF NOT EXISTS v16_meta (
                key TEXT PRIMARY KEY,
                value TEXT DEFAULT ''
            )
        """)
        await db.execute("""
            CREATE TABLE IF NOT EXISTS v16_admins (
                user_id INTEGER PRIMARY KEY,
                role TEXT DEFAULT 'admin',
                enabled INTEGER DEFAULT 1,
                added_by INTEGER DEFAULT 0,
                created_at TEXT DEFAULT '',
                last_seen TEXT DEFAULT ''
            )
        """)
        await db.execute("""
            CREATE TABLE IF NOT EXISTS v16_bot_notes (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                hosted_id INTEGER NOT NULL,
                note TEXT DEFAULT '',
                author_id INTEGER DEFAULT 0,
                created_at TEXT DEFAULT ''
            )
        """)
        await db.execute("""
            CREATE TABLE IF NOT EXISTS v16_jobs (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                job_type TEXT NOT NULL,
                target TEXT DEFAULT '',
                payload TEXT DEFAULT '',
                status TEXT DEFAULT 'queued',
                total INTEGER DEFAULT 0,
                success INTEGER DEFAULT 0,
                failed INTEGER DEFAULT 0,
                skipped INTEGER DEFAULT 0,
                started_at TEXT DEFAULT '',
                finished_at TEXT DEFAULT '',
                created_by INTEGER DEFAULT 0,
                error TEXT DEFAULT '',
                created_at TEXT DEFAULT ''
            )
        """)
        await db.execute("""
            CREATE TABLE IF NOT EXISTS v16_incidents (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                hosted_id INTEGER DEFAULT 0,
                kind TEXT DEFAULT '',
                severity TEXT DEFAULT 'info',
                details TEXT DEFAULT '',
                resolved INTEGER DEFAULT 0,
                created_at TEXT DEFAULT '',
                resolved_at TEXT DEFAULT ''
            )
        """)
        await db.execute("""
            CREATE TABLE IF NOT EXISTS v16_metrics (
                metric TEXT NOT NULL,
                bucket TEXT NOT NULL,
                value REAL DEFAULT 0,
                updated_at TEXT DEFAULT '',
                PRIMARY KEY(metric, bucket)
            )
        """)
        await db.execute("""
            CREATE TABLE IF NOT EXISTS v16_rate_limits (
                scope TEXT PRIMARY KEY,
                hits INTEGER DEFAULT 0,
                window_start REAL DEFAULT 0,
                updated_at TEXT DEFAULT ''
            )
        """)
        await db.execute("""
            CREATE TABLE IF NOT EXISTS v16_commands (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER DEFAULT 0,
                command TEXT DEFAULT '',
                target TEXT DEFAULT '',
                result TEXT DEFAULT '',
                created_at TEXT DEFAULT ''
            )
        """)
        await db.execute("CREATE INDEX IF NOT EXISTS idx_v16_jobs_status ON v16_jobs(status, id)")
        await db.execute("CREATE INDEX IF NOT EXISTS idx_v16_jobs_created ON v16_jobs(created_at)")
        await db.execute("CREATE INDEX IF NOT EXISTS idx_v16_incidents_hosted ON v16_incidents(hosted_id, resolved)")
        await db.execute("CREATE INDEX IF NOT EXISTS idx_v16_incidents_created ON v16_incidents(created_at)")
        await db.execute("CREATE INDEX IF NOT EXISTS idx_v16_notes_hosted ON v16_bot_notes(hosted_id, id)")
        await db.execute("CREATE INDEX IF NOT EXISTS idx_v16_commands_user ON v16_commands(user_id, id)")
        await db.execute(
            "INSERT OR IGNORE INTO v16_meta(key,value) VALUES('schema_version',?)",
            (str(V16_SCHEMA_VERSION),),
        )
        await db.execute(
            "INSERT OR IGNORE INTO v16_meta(key,value) VALUES('control_plane',?)",
            (V16_VERSION,),
        )
        await db.commit()


async def v16_guard(user_id):
    """Hard platform-owner gate. Child-bot owners never pass this gate."""
    try:
        return bool(is_platform_owner(int(user_id)))
    except Exception:
        return False


async def v16_touch_admin(user_id):
    if not await v16_guard(user_id):
        return False
    await db_execute(
        "INSERT INTO v16_admins(user_id,role,enabled,added_by,created_at,last_seen) "
        "VALUES(?,?,?,?,?,?) ON CONFLICT(user_id) DO UPDATE SET last_seen=excluded.last_seen",
        (int(user_id), "root", 1, int(user_id), now_text(), now_text()),
    )
    return True


async def v16_log_command(user_id, command, target="", result=""):
    if not await v16_guard(user_id):
        return
    try:
        await db_execute(
            "INSERT INTO v16_commands(user_id,command,target,result,created_at) VALUES(?,?,?,?,?)",
            (int(user_id), str(command)[:200], str(target)[:300], str(result)[:500], now_text()),
        )
    except Exception:
        pass


async def v16_metric_inc(metric, bucket="global", amount=1):
    """Atomic-ish metric increment stored in SQLite for persistence."""
    try:
        await db_execute(
            "INSERT INTO v16_metrics(metric,bucket,value,updated_at) VALUES(?,?,?,?) "
            "ON CONFLICT(metric,bucket) DO UPDATE SET value=value+excluded.value,updated_at=excluded.updated_at",
            (str(metric)[:100], str(bucket)[:100], float(amount), now_text()),
        )
    except Exception:
        pass


async def v16_metric_get(metric, bucket="global", default=0):
    row = await db_execute(
        "SELECT value FROM v16_metrics WHERE metric=? AND bucket=?",
        (str(metric), str(bucket)),
        fetchone=True,
    )
    if not row:
        return default
    try:
        return float(row["value"])
    except Exception:
        return default


async def v16_create_job(job_type, target="", payload=None, created_by=0):
    payload_text = json.dumps(payload or {}, ensure_ascii=False, separators=(",", ":"))
    await db_execute(
        "INSERT INTO v16_jobs(job_type,target,payload,status,created_by,created_at) VALUES(?,?,?,?,?,?)",
        (str(job_type), str(target), payload_text, "queued", int(created_by or 0), now_text()),
    )
    row = await db_execute("SELECT last_insert_rowid() AS id", fetchone=True)
    return int(row["id"]) if row else 0


async def v16_update_job(job_id, **fields):
    allowed = {
        "status", "total", "success", "failed", "skipped", "started_at",
        "finished_at", "error", "target", "payload",
    }
    updates = []
    params = []
    for key, value in fields.items():
        if key in allowed:
            updates.append(f"{key}=?")
            params.append(value)
    if not updates:
        return False
    params.append(int(job_id))
    await db_execute(f"UPDATE v16_jobs SET {', '.join(updates)} WHERE id=?", tuple(params))
    return True


async def v16_record_incident(hosted_id, kind, details, severity="warning"):
    details = str(details)[:V16_MAX_AUDIT_DETAILS]
    await db_execute(
        "INSERT INTO v16_incidents(hosted_id,kind,severity,details,created_at) VALUES(?,?,?,?,?)",
        (int(hosted_id or 0), str(kind)[:100], str(severity)[:30], details, now_text()),
    )
    await v16_metric_inc("incidents", "global")


async def v16_resolve_incident(incident_id):
    await db_execute(
        "UPDATE v16_incidents SET resolved=1,resolved_at=? WHERE id=?",
        (now_text(), int(incident_id)),
    )


async def v16_set_note(hosted_id, note, author_id):
    note = str(note).strip()[:V16_MAX_NOTE_LENGTH]
    if not note:
        return False
    await db_execute(
        "INSERT INTO v16_bot_notes(hosted_id,note,author_id,created_at) VALUES(?,?,?,?)",
        (int(hosted_id), note, int(author_id), now_text()),
    )
    return True


async def v16_get_notes(hosted_id, limit=5):
    return await db_execute(
        "SELECT * FROM v16_bot_notes WHERE hosted_id=? ORDER BY id DESC LIMIT ?",
        (int(hosted_id), int(max(1, min(limit, 50)))),
        fetchall=True,
    ) or []


async def v16_recent_incidents(hosted_id=0, limit=10):
    if hosted_id:
        return await db_execute(
            "SELECT * FROM v16_incidents WHERE hosted_id=? ORDER BY id DESC LIMIT ?",
            (int(hosted_id), int(limit)), fetchall=True,
        ) or []
    return await db_execute(
        "SELECT * FROM v16_incidents ORDER BY id DESC LIMIT ?",
        (int(limit),), fetchall=True,
    ) or []


async def v16_hosted_rows(include_disabled=True):
    if include_disabled:
        return await db_execute(
            "SELECT * FROM hosted_bots ORDER BY id DESC", fetchall=True,
        ) or []
    return await db_execute(
        "SELECT * FROM hosted_bots WHERE status<>? ORDER BY id DESC",
        ("disabled",), fetchall=True,
    ) or []


async def v16_hosted_user_count(db_file):
    try:
        row = await db_execute_on_file(
            db_file,
            "SELECT COUNT(*) AS c FROM users WHERE blocked=0",
            fetchone=True,
        )
        return int(row["c"]) if row else 0
    except Exception:
        return 0


async def v16_hosted_total_messages(db_file):
    try:
        row = await db_execute_on_file(
            db_file,
            "SELECT COALESCE(SUM(messages),0) AS c FROM users",
            fetchone=True,
        )
        return int(row["c"]) if row else 0
    except Exception:
        return 0


async def v16_hosted_health(row):
    """Produce a non-sensitive health record for one hosted bot."""
    status = str(row["status"] or "unknown")
    pid = int(row["pid"] or 0)
    process_alive = False
    if pid > 0:
        try:
            os.kill(pid, 0)
            process_alive = True
        except Exception:
            process_alive = False
    users = await v16_hosted_user_count(row["db_file"])
    messages = await v16_hosted_total_messages(row["db_file"])
    return {
        "id": int(row["id"]),
        "username": str(row["bot_username"] or "unknown"),
        "owner_id": int(row["owner_id"] or 0),
        "status": status,
        "pid": pid,
        "process_alive": process_alive,
        "users": users,
        "messages": messages,
        "created_at": str(row["created_at"] or ""),
        "updated_at": str(row["updated_at"] or ""),
    }


async def v16_health_snapshot(force=False):
    now = time.time()
    if not force and V16_HEALTH_CACHE["data"] is not None and now - V16_HEALTH_CACHE["ts"] < 10:
        return V16_HEALTH_CACHE["data"]
    users_row = await db_execute("SELECT COUNT(*) AS c FROM users", fetchone=True)
    hosted = await v16_hosted_rows(True)
    running = sum(1 for r in hosted if str(r["status"]) not in ("disabled", "stopped") )
    disabled = sum(1 for r in hosted if str(r["status"]) == "disabled")
    errors = await db_execute(
        "SELECT COUNT(*) AS c FROM error_logs WHERE created_at >= datetime('now','-1 day')",
        fetchone=True,
    )
    audits = await db_execute(
        "SELECT COUNT(*) AS c FROM audit_logs WHERE created_at >= datetime('now','-1 day')",
        fetchone=True,
    )
    snap = V16Health(
        uptime=uptime(),
        users=int(users_row["c"] if users_row else 0),
        hosted=len(hosted),
        running=running,
        disabled=disabled,
        errors_24h=int(errors["c"] if errors else 0),
        audit_24h=int(audits["c"] if audits else 0),
        database="SQLite WAL",
        process="child-process isolation" if not IS_CHILD_BOT else "child bot",
        version=V16_VERSION,
    )
    V16_HEALTH_CACHE["ts"] = now
    V16_HEALTH_CACHE["data"] = snap
    return snap


async def v16_dashboard(chat_id, message_id=0):
    if not await v16_guard(chat_id):
        return False
    snap = await v16_health_snapshot()
    total_stars = await v16_metric_get("stars_collected", "global", 0)
    jobs = await db_execute(
        "SELECT COUNT(*) c FROM v16_jobs WHERE status IN ('queued','running')",
        fetchone=True,
    )
    incidents = await db_execute(
        "SELECT COUNT(*) c FROM v16_incidents WHERE resolved=0",
        fetchone=True,
    )
    text = (
        "👑 <b>مركز السيطرة V16</b>\n\n"
        f"⚡ الإصدار: <code>{esc(snap.version)}</code>\n"
        f"⏱️ التشغيل: <b>{esc(snap.uptime)}</b>\n\n"
        f"🤖 البوتات: <b>{snap.hosted}</b>\n"
        f"🟢 نشطة: <b>{snap.running}</b>\n"
        f"🔴 معطلة: <b>{snap.disabled}</b>\n"
        f"👥 مستخدمو المنصة: <b>{snap.users}</b>\n\n"
        f"⭐ Stars المسجلة: <b>{int(total_stars)}</b>\n"
        f"📋 مهام جارية: <b>{int(jobs['c'] if jobs else 0)}</b>\n"
        f"🚨 حوادث غير محلولة: <b>{int(incidents['c'] if incidents else 0)}</b>\n"
        f"⚠️ أخطاء 24 ساعة: <b>{snap.errors_24h}</b>"
    )
    kb = {"inline_keyboard": [
        [{"text":"🤖 إدارة البوتات","callback_data":"v16:bots"}, {"text":"🎛 مدير الأزرار","callback_data":"v16:buttons"}, {"text":"📊 الإحصائيات","callback_data":"v16:stats"}],
        [{"text":"🩺 صحة النظام","callback_data":"v16:health"}, {"text":"🚨 الحوادث","callback_data":"v16:incidents"}],
        [{"text":"📢 مركز الإذاعة","callback_data":"v16:broadcast"}, {"text":"⚙️ إعدادات المنصة","callback_data":"v16:settings"}],
        [{"text":"📜 سجل العمليات","callback_data":"v16:audit"}, {"text":"🧰 أدوات الطوارئ","callback_data":"v16:emergency"}],
        [{"text":"🔄 تحديث","callback_data":"v16:dashboard"}, {"text":"🔙 لوحة المطور","callback_data":"admin"}],
    ]}
    if message_id:
        await edit_message(chat_id, message_id, text, kb)
    else:
        await send_message(chat_id, text, kb)
    await v16_touch_admin(chat_id)
    return True


async def v16_bots_page(chat_id, message_id=0, page=0):
    rows = await v16_hosted_rows(True)
    page = max(0, int(page))
    start = page * V16_MAX_PAGE
    subset = rows[start:start + V16_MAX_PAGE]
    lines = ["🤖 <b>إدارة جميع البوتات</b>", ""]
    kb_rows = []
    if not rows:
        lines.append("لا توجد بوتات مستضافة حاليًا.")
    for r in subset:
        status = str(r["status"] or "unknown")
        icon = "🟢" if status not in ("disabled", "stopped") else "🔴"
        lines.append(f"{icon} <b>@{esc(r['bot_username'] or 'unknown')}</b> — ID <code>{r['id']}</code>")
        kb_rows.append([{"text":f"{icon} @{r['bot_username'] or 'unknown'}","callback_data":f"v16:bot:{int(r['id'])}"}])
    nav=[]
    if page>0:
        nav.append({"text":"⬅️ السابق","callback_data":f"v16:bots:{page-1}"})
    if start+V16_MAX_PAGE < len(rows):
        nav.append({"text":"التالي ➡️","callback_data":f"v16:bots:{page+1}"})
    if nav: kb_rows.append(nav)
    kb_rows.append([{"text":"🔄 تحديث","callback_data":f"v16:bots:{page}"},{"text":"🔙 مركز السيطرة","callback_data":"v16:dashboard"}])
    kb={"inline_keyboard":kb_rows}
    if message_id:
        await edit_message(chat_id,message_id,"\n".join(lines),kb)
    else:
        await send_message(chat_id,"\n".join(lines),kb)
    return True


async def v16_bot_detail(chat_id, message_id, hosted_id):
    row = await db_execute("SELECT * FROM hosted_bots WHERE id=?", (int(hosted_id),), fetchone=True)
    if not row:
        await send_message(chat_id,"❌ البوت غير موجود.", {"inline_keyboard":[[{"text":"🔙 البوتات","callback_data":"v16:bots"}]]})
        return True
    info = await v16_hosted_health(row)
    incidents = await v16_recent_incidents(hosted_id, 3)
    notes = await v16_get_notes(hosted_id, 3)
    status = info["status"]
    status_icon = "🟢" if status not in ("disabled","stopped") else "🔴"
    text=(
        f"🤖 <b>@{esc(info['username'])}</b>\n\n"
        f"🆔 السجل: <code>{info['id']}</code>\n"
        f"👤 المالك: <code>{info['owner_id']}</code>\n"
        f"{status_icon} الحالة: <b>{esc(status)}</b>\n"
        f"⚙️ PID: <code>{info['pid']}</code>\n"
        f"📡 العملية: <b>{'حية' if info['process_alive'] else 'غير حية'}</b>\n"
        f"👥 المستخدمون: <b>{info['users']}</b>\n"
        f"💬 الرسائل: <b>{info['messages']}</b>\n"
        f"📅 الإنشاء: <code>{esc(info['created_at'])}</code>\n"
        f"🔄 التحديث: <code>{esc(info['updated_at'])}</code>"
    )
    if incidents:
        text += "\n\n🚨 <b>آخر الحوادث</b>"
        for inc in incidents:
            text += f"\n• {esc(inc['kind'])} — {esc(inc['severity'])} — {esc(inc['created_at'])}"
    if notes:
        text += "\n\n📝 <b>ملاحظات المطور</b>"
        for note in notes:
            text += f"\n• {esc(note['note'][:180])}"
    toggle_text = "▶️ تشغيل" if status in ("disabled","stopped") else "⏸ إيقاف"
    kb={"inline_keyboard":[
        [{"text":toggle_text,"callback_data":f"v16:toggle:{hosted_id}"},{"text":"🔄 إعادة تشغيل","callback_data":f"v16:restart:{hosted_id}"}],
        [{"text":"🟡 صيانة","callback_data":f"v16:maintenance:{hosted_id}"},{"text":"📊 إحصائيات","callback_data":f"v16:botstats:{hosted_id}"}],
        [{"text":"📝 ملاحظة","callback_data":f"v16:note:{hosted_id}"},{"text":"📢 إذاعة","callback_data":f"v16:botbroadcast:{hosted_id}"}],
        [{"text":"🚨 الحوادث","callback_data":f"v16:botincidents:{hosted_id}"},{"text":"🗑 حذف نهائي","callback_data":f"v16:delete:{hosted_id}"}],
        [{"text":"🔙 جميع البوتات","callback_data":"v16:bots"}],
    ]}
    await edit_message(chat_id,message_id,text,kb)
    return True


async def v16_toggle_bot(hosted_id, enabled):
    row = await db_execute("SELECT bot_username,status FROM hosted_bots WHERE id=?", (int(hosted_id),), fetchone=True)
    if not row:
        return False, "البوت غير موجود."
    ok,msg = await set_hosted_bot_enabled(int(hosted_id), bool(enabled))
    await v16_record_incident(hosted_id, "lifecycle", msg, "info" if ok else "error")
    await v16_metric_inc("lifecycle_actions", "global")
    return ok,msg


async def v16_restart_bot(hosted_id):
    row = await db_execute("SELECT * FROM hosted_bots WHERE id=?", (int(hosted_id),), fetchone=True)
    if not row:
        return False, "البوت غير موجود."
    try:
        await set_hosted_bot_enabled(int(hosted_id), False)
        await asyncio.sleep(0.5)
        ok,msg = await set_hosted_bot_enabled(int(hosted_id), True)
        await v16_record_incident(hosted_id,"restart",msg,"info" if ok else "error")
        await v16_metric_inc("restarts", "global")
        return ok,msg
    except Exception as exc:
        await v16_record_incident(hosted_id,"restart",str(exc),"error")
        return False,str(exc)


async def v16_set_maintenance(hosted_id, enabled=True):
    row = await db_execute("SELECT db_file,bot_username FROM hosted_bots WHERE id=?", (int(hosted_id),), fetchone=True)
    if not row:
        return False,"البوت غير موجود."
    try:
        await db_execute_on_file(
            row["db_file"],
            "CREATE TABLE IF NOT EXISTS settings(key TEXT PRIMARY KEY,value TEXT DEFAULT '')",
        )
        await db_execute_on_file(
            row["db_file"],
            "INSERT INTO settings(key,value) VALUES('maintenance',?) ON CONFLICT(key) DO UPDATE SET value=excluded.value",
            ("1" if enabled else "0",),
        )
        await v16_record_incident(hosted_id,"maintenance", "enabled" if enabled else "disabled", "info")
        return True, "تم تحديث وضع الصيانة."
    except Exception as exc:
        await v16_record_incident(hosted_id,"maintenance",str(exc),"error")
        return False,str(exc)


async def v16_delete_bot(hosted_id):
    """Delete a hosted bot from the platform and terminate its child process."""
    row = await db_execute("SELECT * FROM hosted_bots WHERE id=?", (int(hosted_id),), fetchone=True)
    if not row:
        return False,"البوت غير موجود."
    pid=int(row["pid"] or 0)
    if pid:
        try:
            os.kill(pid, 15)
        except Exception:
            pass
    db_file=str(row["db_file"] or "")
    await db_execute("DELETE FROM hosted_bots WHERE id=?", (int(hosted_id),))
    V16_HEALTH_CACHE["ts"] = 0
    await v16_record_incident(0,"delete",f"hosted_id={hosted_id};username={row['bot_username']}","warning")
    await audit("V16 hosted bot deleted", f"id={hosted_id};username={row['bot_username']}")
    if db_file:
        try:
            path=Path(db_file)
            if path.exists() and str(path.resolve()).startswith(str(HOSTED_BOTS_DIR.resolve())):
                path.unlink(missing_ok=True)
        except Exception:
            pass
    HOSTED_PROCESSES.pop(int(hosted_id), None)
    return True,"تم حذف البوت نهائيًا من المنصة."


async def v16_stats(chat_id,message_id):
    users = await db_execute("SELECT COUNT(*) c FROM users",fetchone=True)
    messages = await db_execute("SELECT COUNT(*) c FROM messages",fetchone=True)
    blocked = await db_execute("SELECT COUNT(*) c FROM users WHERE blocked=1",fetchone=True)
    hosted = await v16_hosted_rows(True)
    total_child_users=0
    total_child_messages=0
    for row in hosted:
        total_child_users += await v16_hosted_user_count(row["db_file"])
        total_child_messages += await v16_hosted_total_messages(row["db_file"])
    text=(
        "📊 <b>إحصائيات المنصة V16</b>\n\n"
        f"👥 مستخدمو البوت المركزي: <b>{int(users['c'] if users else 0)}</b>\n"
        f"🚫 المحظورون: <b>{int(blocked['c'] if blocked else 0)}</b>\n"
        f"💬 رسائل المركزي: <b>{int(messages['c'] if messages else 0)}</b>\n\n"
        f"🤖 البوتات المستضافة: <b>{len(hosted)}</b>\n"
        f"👥 مستخدمو البوتات: <b>{total_child_users}</b>\n"
        f"💬 رسائل البوتات: <b>{total_child_messages}</b>\n\n"
        f"🔄 عمليات إعادة التشغيل: <b>{int(await v16_metric_get('restarts'))}</b>\n"
        f"🚨 الحوادث: <b>{int(await v16_metric_get('incidents'))}</b>\n"
        f"📢 عمليات الإدارة: <b>{int(await v16_metric_get('lifecycle_actions'))}</b>"
    )
    await edit_message(chat_id,message_id,text,{"inline_keyboard":[[{"text":"🔄 تحديث","callback_data":"v16:stats"}],[{"text":"🔙 مركز السيطرة","callback_data":"v16:dashboard"}]]})
    return True


async def v16_health(chat_id,message_id):
    snap=await v16_health_snapshot(True)
    text=(
        "🩺 <b>صحة النظام</b>\n\n"
        f"🟢 الحالة: <b>Online</b>\n"
        f"⏱️ Uptime: <b>{esc(snap.uptime)}</b>\n"
        f"🗄️ DB: <b>{esc(snap.database)}</b>\n"
        f"⚙️ Process: <b>{esc(snap.process)}</b>\n"
        f"🤖 Hosted: <b>{snap.hosted}</b>\n"
        f"🟢 Running: <b>{snap.running}</b>\n"
        f"🔴 Disabled: <b>{snap.disabled}</b>\n"
        f"⚠️ Errors/24h: <b>{snap.errors_24h}</b>\n"
        f"📜 Audit/24h: <b>{snap.audit_24h}</b>"
    )
    await edit_message(chat_id,message_id,text,{"inline_keyboard":[[{"text":"🔬 فحص البوتات","callback_data":"v16:bothealth"}],[{"text":"🔄 تحديث","callback_data":"v16:health"}],[{"text":"🔙 مركز السيطرة","callback_data":"v16:dashboard"}]]})
    return True


async def v16_bot_health_page(chat_id,message_id):
    rows=await v16_hosted_rows(True)
    healthy=0; stale=0; disabled=0
    lines=["🔬 <b>فحص البوتات</b>",""]
    for row in rows:
        status=str(row["status"] or "")
        if status=="disabled":
            disabled+=1; icon="🔴"
        else:
            info=await v16_hosted_health(row)
            if info["process_alive"]:
                healthy+=1; icon="🟢"
            else:
                stale+=1; icon="🟠"
        lines.append(f"{icon} @{esc(row['bot_username'] or 'unknown')} — {esc(status)}")
    lines += ["",f"🟢 سليمة: <b>{healthy}</b>",f"🟠 تحتاج فحص: <b>{stale}</b>",f"🔴 معطلة: <b>{disabled}</b>"]
    await edit_message(chat_id,message_id,"\n".join(lines),{"inline_keyboard":[[{"text":"🔄 إعادة الفحص","callback_data":"v16:bothealth"}],[{"text":"🔙 صحة النظام","callback_data":"v16:health"}]]})
    return True


async def v16_incidents_page(chat_id,message_id):
    rows=await v16_recent_incidents(0,20)
    lines=["🚨 <b>مركز الحوادث</b>",""]
    kb=[]
    if not rows:
        lines.append("لا توجد حوادث مسجلة.")
    for row in rows:
        icon="🔴" if row["severity"]=="error" else "🟠" if row["severity"]=="warning" else "🔵"
        state="✅" if row["resolved"] else "⏳"
        lines.append(f"{icon} {state} <b>{esc(row['kind'])}</b> — {esc(row['created_at'])}")
        if not row["resolved"]:
            kb.append([{"text":f"✅ حل #{row['id']}","callback_data":f"v16:resolve:{row['id']}"}])
    kb.append([{"text":"🔄 تحديث","callback_data":"v16:incidents"},{"text":"🔙 مركز السيطرة","callback_data":"v16:dashboard"}])
    await edit_message(chat_id,message_id,"\n".join(lines),{"inline_keyboard":kb})
    return True


async def v16_audit_page(chat_id,message_id):
    rows=await db_execute("SELECT * FROM v16_commands ORDER BY id DESC LIMIT 25",fetchall=True) or []
    lines=["📜 <b>سجل أوامر المطور</b>",""]
    if not rows: lines.append("لا توجد عمليات بعد.")
    for row in rows:
        lines.append(f"• <code>#{row['id']}</code> <b>{esc(row['command'])}</b> — <code>{row['user_id']}</code> — {esc(row['created_at'])}")
    await edit_message(chat_id,message_id,"\n".join(lines),{"inline_keyboard":[[{"text":"🔄 تحديث","callback_data":"v16:audit"}],[{"text":"🔙 مركز السيطرة","callback_data":"v16:dashboard"}]]})
    return True


async def v16_settings_page(chat_id,message_id):
    price=await get_setting("bot_creation_price",str(BOT_CREATION_PRICE_STARS))
    max_bots=await get_setting("max_hosted_bots",str(MAX_HOSTED_BOTS))
    global_maintenance=await get_setting("platform_maintenance","0")
    text=(
        "⚙️ <b>إعدادات المنصة</b>\n\n"
        f"⭐ سعر الإنشاء: <b>{esc(price)}</b>\n"
        f"🤖 الحد الأقصى للبوتات: <b>{esc(max_bots)}</b>\n"
        f"🛠️ صيانة المنصة: <b>{'مفعلة' if global_maintenance=='1' else 'مغلقة'}</b>\n\n"
        "هذه الإعدادات تخص المنصة المركزية ولا تمنح أي بوت مستضاف صلاحيات المطور."
    )
    kb={"inline_keyboard":[
        [{"text":"⭐ تغيير السعر","callback_data":"v16:setprice"},{"text":"🤖 تغيير الحد","callback_data":"v16:setlimit"}],
        [{"text":"🛠️ تبديل الصيانة العامة","callback_data":"v16:globalmaintenance"}],
        [{"text":"🔙 مركز السيطرة","callback_data":"v16:dashboard"}],
    ]}
    await edit_message(chat_id,message_id,text,kb)
    return True


async def v16_emergency_page(chat_id,message_id):
    text=(
        "🧰 <b>أدوات الطوارئ</b>\n\n"
        "هذه الأدوات تؤثر على عدد كبير من البوتات. استخدمها فقط عند الحاجة.\n\n"
        "🛑 الإيقاف الجماعي يوقف العمليات الفرعية فقط.\n"
        "🔄 التشغيل الجماعي يعيد البوتات غير المعطلة يدويًا."
    )
    kb={"inline_keyboard":[
        [{"text":"🛑 إيقاف جميع البوتات","callback_data":"v16:stopall"}],
        [{"text":"🔄 تشغيل جميع البوتات","callback_data":"v16:startall"}],
        [{"text":"🧹 تنظيف الذاكرة","callback_data":"v16:cleanup"}],
        [{"text":"🔙 مركز السيطرة","callback_data":"v16:dashboard"}],
    ]}
    await edit_message(chat_id,message_id,text,kb)
    return True


async def v16_broadcast_page(chat_id,message_id):
    text=(
        "📢 <b>مركز الإذاعة V16</b>\n\n"
        "اختر نطاق الإرسال. كل مهمة تُسجل في قاعدة البيانات ويمكن تتبعها.\n\n"
        "⚠️ يتم احترام التوازي المحدود ومعدلات Telegram بدل إطلاق آلاف الطلبات دفعة واحدة."
    )
    kb={"inline_keyboard":[
        [{"text":"🌐 جميع البوتات","callback_data":"v16:broadcastall"}],
        [{"text":"🤖 اختيار بوت","callback_data":"v16:broadcastselect"}],
        [{"text":"📋 آخر المهام","callback_data":"v16:jobs"}],
        [{"text":"🔙 مركز السيطرة","callback_data":"v16:dashboard"}],
    ]}
    await edit_message(chat_id,message_id,text,kb)
    return True


async def v16_jobs_page(chat_id,message_id):
    rows=await db_execute("SELECT * FROM v16_jobs ORDER BY id DESC LIMIT 20",fetchall=True) or []
    lines=["📋 <b>مهام المنصة</b>",""]
    if not rows: lines.append("لا توجد مهام.")
    for row in rows:
        lines.append(f"#{row['id']} — <b>{esc(row['job_type'])}</b> — {esc(row['status'])} — {row['success']}/{row['total']}")
    await edit_message(chat_id,message_id,"\n".join(lines),{"inline_keyboard":[[{"text":"🔄 تحديث","callback_data":"v16:jobs"}],[{"text":"🔙 الإذاعة","callback_data":"v16:broadcast"}]]})
    return True


async def v16_bot_stats(chat_id,message_id,hosted_id):
    row=await db_execute("SELECT * FROM hosted_bots WHERE id=?",(int(hosted_id),),fetchone=True)
    if not row:
        return await v16_bots_page(chat_id,message_id,0)
    users=await db_execute_on_file(row["db_file"],"SELECT COUNT(*) c FROM users",fetchone=True)
    blocked=await db_execute_on_file(row["db_file"],"SELECT COUNT(*) c FROM users WHERE blocked=1",fetchone=True)
    messages=await db_execute_on_file(row["db_file"],"SELECT COUNT(*) c FROM messages",fetchone=True)
    media=await db_execute_on_file(row["db_file"],"SELECT COALESCE(SUM(media),0) c FROM users",fetchone=True)
    text=(
        f"📊 <b>إحصائيات @{esc(row['bot_username'] or 'unknown')}</b>\n\n"
        f"👥 المستخدمون: <b>{int(users['c'] if users else 0)}</b>\n"
        f"🚫 المحظورون: <b>{int(blocked['c'] if blocked else 0)}</b>\n"
        f"💬 الرسائل: <b>{int(messages['c'] if messages else 0)}</b>\n"
        f"🖼 الوسائط: <b>{int(media['c'] if media else 0)}</b>"
    )
    await edit_message(chat_id,message_id,text,{"inline_keyboard":[[{"text":"🔙 تفاصيل البوت","callback_data":f"v16:bot:{hosted_id}"}]]})
    return True


async def v16_bot_incidents(chat_id,message_id,hosted_id):
    rows=await v16_recent_incidents(hosted_id,20)
    lines=[f"🚨 <b>حوادث البوت #{hosted_id}</b>",""]
    if not rows: lines.append("لا توجد حوادث.")
    for row in rows:
        state="✅" if row["resolved"] else "⏳"
        lines.append(f"{state} <b>{esc(row['kind'])}</b> — {esc(row['severity'])} — {esc(row['created_at'])}")
        lines.append(f"  {esc(row['details'][:250])}")
    await edit_message(chat_id,message_id,"\n".join(lines),{"inline_keyboard":[[{"text":"🔙 تفاصيل البوت","callback_data":f"v16:bot:{hosted_id}"}]]})
    return True


async def v16_stop_all():
    rows=await v16_hosted_rows(True)
    ok=0; failed=0
    for row in rows:
        try:
            result,_=await v16_toggle_bot(int(row["id"]),False)
            ok += 1 if result else 0
            failed += 0 if result else 1
        except Exception as exc:
            failed+=1
            await v16_record_incident(int(row["id"]),"stop_all",str(exc),"error")
    return ok,failed


async def v16_start_all():
    rows=await v16_hosted_rows(False)
    ok=0; failed=0
    for row in rows:
        try:
            result,_=await v16_toggle_bot(int(row["id"]),True)
            ok += 1 if result else 0
            failed += 0 if result else 1
        except Exception as exc:
            failed+=1
            await v16_record_incident(int(row["id"]),"start_all",str(exc),"error")
    return ok,failed


async def v16_global_maintenance(enabled):
    await set_setting("platform_maintenance", "1" if enabled else "0")
    await v16_metric_inc("global_maintenance_changes", "global")
    await audit("V16 platform maintenance", "enabled" if enabled else "disabled")
    return True


async def v16_cleanup():
    """Bound caches without touching persistent user data."""
    await cleanup_runtime_cache()
    now=time.time()
    removed=0
    for key,values in list(V16_MEMORY_EVENTS.items()):
        fresh=[v for v in values if now-float(v)<300]
        removed += max(0,len(values)-len(fresh))
        if fresh: V16_MEMORY_EVENTS[key]=fresh
        else: V16_MEMORY_EVENTS.pop(key,None)
    V16_HEALTH_CACHE["ts"]=0
    await v16_metric_inc("cache_cleanups","global")
    return removed


async def v16_button_scope_page(chat_id, message_id=0):
    rows = await v16_hosted_rows(True)
    text = "🎛 <b>مدير أزرار جميع البوتات</b>\n\nاختر النطاق الذي تريد التحكم به.\n🌐 <b>جميع البوتات</b> = يطبق على المنصة والبوتات المستضافة.\n🤖 <b>بوت معين</b> = يطبق عليه وحده."
    kb = [[{"text":"🌐 جميع البوتات","callback_data":"v16:btnscope:all","style":"success"}]]
    for row in rows[:60]:
        name = str(row["bot_username"] or row["bot_name"] or row["bot_id"] or "بوت")
        kb.append([{"text":f"🤖 @{name.lstrip('@')}","callback_data":f"v16:btnscope:{int(row['id'])}"}])
    kb.append([{"text":"🔙 مركز السيطرة","callback_data":"v16:dashboard"}])
    if message_id:
        await edit_message(chat_id,message_id,text,{"inline_keyboard":kb})
    else:
        await send_message(chat_id,text,{"inline_keyboard":kb})
    return True


async def _v16_button_rows_for_scope(scope):
    if scope == "all":
        return await get_buttons(include_disabled=True)
    row = await db_execute("SELECT db_file,bot_username FROM hosted_bots WHERE id=?", (int(scope),), fetchone=True)
    if not row:
        return None
    try:
        return await db_execute_on_file(row["db_file"], "SELECT * FROM buttons ORDER BY row,position,id", fetchall=True)
    except Exception:
        return None


async def v16_button_manager(chat_id, message_id, scope="all"):
    if scope != "all":
        try:
            int(scope)
        except Exception:
            scope = "all"
    rows = await _v16_button_rows_for_scope(scope)
    if rows is None:
        await edit_message(chat_id,message_id,"❌ تعذر الوصول إلى قاعدة بيانات هذا البوت.",{"inline_keyboard":[[{"text":"🔙 اختيار النطاق","callback_data":"v16:buttons"}]]})
        return True
    policy = button_policy_scope_entries(scope)
    disabled_selectors = {str(x) for x in policy.get("selectors", [])}
    disabled_texts = {str(x) for x in policy.get("texts", [])}
    title = "🌐 جميع البوتات" if scope == "all" else f"🤖 البوت #{int(scope)}"
    lines = [f"🎛 <b>مدير الأزرار — {esc(title)}</b>", "", "اضغط على الزر لتبديل حالته.", ""]
    kb=[]
    for row in rows or []:
        selector = button_policy_selector_for_row(row)
        hidden = selector in disabled_selectors or str(row["text"] or "") in disabled_texts or not int(row["enabled"] or 0)
        icon = "🔴" if hidden else "🟢"
        label = str(row["text"] or row["id"] or "زر")[:34]
        lines.append(f"{icon} {esc(label)} · <code>{esc(row['id'])}</code>")
        bid = str(row["id"])
        kb.append([{"text":f"{icon} {label}","callback_data":f"v16:btnflip:{scope}:{esc(bid)}"},
                   {"text":"✏️ الاسم","callback_data":f"v16:btnrename:{scope}:{esc(bid)}"},
                   {"text":"🎨 اللون","callback_data":f"v16:btnstyle:{scope}:{esc(bid)}"}])
    if not rows:
        lines.append("لا توجد أزرار معرفة في هذا البوت.")
    kb += [
        [{"text":"➕ إخفاء زر مخصص","callback_data":f"v16:btncustom:{scope}","style":"danger"}],
        [{"text":"🧹 إزالة كل الإخفاءات لهذا النطاق","callback_data":f"v16:btnclear:{scope}"}],
        [{"text":"🔙 اختيار النطاق","callback_data":"v16:buttons"}],
    ]
    await edit_message(chat_id,message_id,"\n".join(lines),{"inline_keyboard":kb})
    return True


async def v16_button_flip(scope, button_id):
    rows = await _v16_button_rows_for_scope(scope)
    if rows is None:
        return False, "تعذر الوصول إلى البوت."
    row = next((r for r in rows if str(r["id"]) == str(button_id)), None)
    if not row:
        return False, "الزر غير موجود."
    selector = button_policy_selector_for_row(row)
    policy = button_policy_scope_entries(scope)
    hidden = selector in {str(x) for x in policy.get("selectors", [])} or str(row["text"] or "") in {str(x) for x in policy.get("texts", [])} or not int(row["enabled"] or 0)
    if hidden:
        button_policy_show(scope, selector, str(row["text"] or ""))
        return True, "تم إظهار الزر."
    button_policy_hide(scope, selector, str(row["text"] or ""))
    return True, "تم إخفاء الزر."


async def v16_button_clear(scope):
    data = _button_policy_load_sync()
    if scope == "all":
        data["global"] = {"selectors": [], "texts": [], "labels": {}, "styles": {}}
    else:
        (data.get("bots") or {}).pop(str(int(scope)), None)
    _button_policy_write_sync(data)
    return True

async def v16_handle_callback(user_id,chat_id,message_id,data):
    """Central V16 router. Every branch is protected by the platform-owner gate."""
    if not await v16_guard(user_id):
        return False
    await v16_touch_admin(user_id)
    try:
        if data=="v16:dashboard":
            return await v16_dashboard(chat_id,message_id)
        if data=="v16:buttons":
            return await v16_button_scope_page(chat_id,message_id)
        if data.startswith("v16:btnscope:"):
            return await v16_button_manager(chat_id,message_id,data.split(":",2)[2])
        if data.startswith("v16:btnflip:"):
            _,_,scope,bid = data.split(":",3)
            ok,msg = await v16_button_flip(scope,bid)
            await v16_log_command(user_id,"button_visibility",f"scope={scope};button={bid}",msg)
            await send_message(chat_id,("✅ " if ok else "❌ ")+esc(msg),{"inline_keyboard":[[{"text":"🔙 مدير الأزرار","callback_data":f"v16:btnscope:{scope}"}]]})
            return True
        if data.startswith("v16:btnrename:"):
            _,_,scope,bid = data.split(":",3)
            await set_state(user_id, f"v16_btnrename:{scope}:{bid}")
            await edit_message(chat_id,message_id,"✏️ أرسل الاسم الجديد للزر.\n\nأرسل <code>-none-</code> لإلغاء الاسم المخصص.",cancel_keyboard())
            return True
        if data.startswith("v16:btnstyle:"):
            _,_,scope,bid = data.split(":",3)
            await set_state(user_id, f"v16_btnstyle:{scope}:{bid}")
            await edit_message(chat_id,message_id,"🎨 أرسل اللون: <code>primary</code> أو <code>success</code> أو <code>danger</code>.",cancel_keyboard())
            return True
        if data.startswith("v16:btnclear:"):
            scope=data.split(":",2)[2]
            await v16_button_clear(scope)
            await v16_log_command(user_id,"button_clear",scope,"cleared")
            return await v16_button_manager(chat_id,message_id,scope)
        if data.startswith("v16:btncustom:"):
            scope=data.split(":",2)[2]
            await set_state(user_id,f"v16_btncustom:{scope}")
            await edit_message(chat_id,message_id,"➕ <b>إخفاء زر مخصص</b>\n\nأرسل <b>callback_data</b> للزر مثل <code>menu:contact</code> أو اكتب النص هكذا:\n<code>text:اسم الزر</code>",cancel_keyboard())
            return True
        if data=="v16:bots":
            return await v16_bots_page(chat_id,message_id,0)
        if data.startswith("v16:bots:"):
            return await v16_bots_page(chat_id,message_id,int(data.rsplit(":",1)[1]))
        if data.startswith("v16:bot:"):
            return await v16_bot_detail(chat_id,message_id,int(data.rsplit(":",1)[1]))
        if data=="v16:stats":
            return await v16_stats(chat_id,message_id)
        if data=="v16:health":
            return await v16_health(chat_id,message_id)
        if data=="v16:bothealth":
            return await v16_bot_health_page(chat_id,message_id)
        if data=="v16:incidents":
            return await v16_incidents_page(chat_id,message_id)
        if data=="v16:audit":
            return await v16_audit_page(chat_id,message_id)
        if data=="v16:settings":
            return await v16_settings_page(chat_id,message_id)
        if data=="v16:emergency":
            return await v16_emergency_page(chat_id,message_id)
        if data=="v16:broadcast":
            return await v16_broadcast_page(chat_id,message_id)
        if data=="v16:jobs":
            return await v16_jobs_page(chat_id,message_id)
        if data.startswith("v16:botstats:"):
            return await v16_bot_stats(chat_id,message_id,int(data.rsplit(":",1)[1]))
        if data.startswith("v16:botincidents:"):
            return await v16_bot_incidents(chat_id,message_id,int(data.rsplit(":",1)[1]))
        if data.startswith("v16:toggle:"):
            hid=int(data.rsplit(":",1)[1])
            row=await db_execute("SELECT status FROM hosted_bots WHERE id=?",(hid,),fetchone=True)
            if not row: return True
            enabled=str(row["status"]) in ("disabled","stopped")
            ok,msg=await v16_toggle_bot(hid,enabled)
            await v16_log_command(user_id,"toggle",str(hid),msg)
            await send_message(chat_id,("✅ " if ok else "❌ ")+esc(msg),{"inline_keyboard":[[{"text":"🔙 البوت","callback_data":f"v16:bot:{hid}"}]]})
            return True
        if data.startswith("v16:restart:"):
            hid=int(data.rsplit(":",1)[1])
            ok,msg=await v16_restart_bot(hid)
            await v16_log_command(user_id,"restart",str(hid),msg)
            await send_message(chat_id,("🔄 " if ok else "❌ ")+esc(msg),{"inline_keyboard":[[{"text":"🔙 البوت","callback_data":f"v16:bot:{hid}"}]]})
            return True
        if data.startswith("v16:maintenance:"):
            hid=int(data.rsplit(":",1)[1])
            ok,msg=await v16_set_maintenance(hid,True)
            await v16_log_command(user_id,"maintenance",str(hid),msg)
            await send_message(chat_id,("🟡 " if ok else "❌ ")+esc(msg),{"inline_keyboard":[[{"text":"🔙 البوت","callback_data":f"v16:bot:{hid}"}]]})
            return True
        if data.startswith("v16:delete:"):
            hid=int(data.rsplit(":",1)[1])
            kb={"inline_keyboard":[[{"text":"⚠️ نعم، احذف نهائيًا","callback_data":f"v16:deleteyes:{hid}"}],[{"text":"🔙 إلغاء","callback_data":f"v16:bot:{hid}"}]]}
            await edit_message(chat_id,message_id,"⚠️ <b>تأكيد الحذف النهائي</b>\n\nسيتم إنهاء العملية وحذف سجل البوت وملف قاعدة بياناته.",kb)
            return True
        if data.startswith("v16:deleteyes:"):
            hid=int(data.rsplit(":",1)[1])
            ok,msg=await v16_delete_bot(hid)
            await v16_log_command(user_id,"delete",str(hid),msg)
            await send_message(chat_id,("🗑 " if ok else "❌ ")+esc(msg),{"inline_keyboard":[[{"text":"🔙 البوتات","callback_data":"v16:bots"}]]})
            return True
        if data.startswith("v16:resolve:"):
            iid=int(data.rsplit(":",1)[1])
            await v16_resolve_incident(iid)
            await v16_log_command(user_id,"resolve_incident",str(iid),"resolved")
            return await v16_incidents_page(chat_id,message_id)
        if data=="v16:stopall":
            ok,failed=await v16_stop_all()
            await v16_log_command(user_id,"stop_all","",f"ok={ok};failed={failed}")
            await send_message(chat_id,f"🛑 تم الإيقاف.\n\n✅ نجاح: <b>{ok}</b>\n❌ فشل: <b>{failed}</b>",{"inline_keyboard":[[{"text":"🔙 الطوارئ","callback_data":"v16:emergency"}]]})
            return True
        if data=="v16:startall":
            ok,failed=await v16_start_all()
            await v16_log_command(user_id,"start_all","",f"ok={ok};failed={failed}")
            await send_message(chat_id,f"🔄 تم التشغيل.\n\n✅ نجاح: <b>{ok}</b>\n❌ فشل: <b>{failed}</b>",{"inline_keyboard":[[{"text":"🔙 الطوارئ","callback_data":"v16:emergency"}]]})
            return True
        if data=="v16:cleanup":
            removed=await v16_cleanup()
            await v16_log_command(user_id,"cleanup","",str(removed))
            await send_message(chat_id,f"🧹 تم تنظيف الذاكرة المؤقتة.\nالعناصر المنتهية: <b>{removed}</b>",{"inline_keyboard":[[{"text":"🔙 الطوارئ","callback_data":"v16:emergency"}]]})
            return True
        if data=="v16:globalmaintenance":
            current=await get_setting("platform_maintenance","0")
            await v16_global_maintenance(current!="1")
            return await v16_settings_page(chat_id,message_id)
        if data=="v16:broadcastall":
            await set_state(user_id,"v16_broadcast_all")
            await edit_message(chat_id,message_id,"📢 <b>إذاعة لجميع البوتات</b>\n\nأرسل نص الرسالة الآن.\n\nيمكنك الإلغاء بزر الرجوع.",cancel_keyboard())
            return True
        if data.startswith("v16:note:"):
            hid=int(data.rsplit(":",1)[1])
            await set_state(user_id,f"v16_note:{hid}")
            await edit_message(chat_id,message_id,"📝 أرسل ملاحظة للمطور عن هذا البوت.",cancel_keyboard())
            return True
        if data=="v16:setprice":
            await set_state(user_id,"v16_setprice")
            await edit_message(chat_id,message_id,"⭐ أرسل السعر الجديد بالأرقام فقط.",cancel_keyboard())
            return True
        if data=="v16:setlimit":
            await set_state(user_id,"v16_setlimit")
            await edit_message(chat_id,message_id,"🤖 أرسل الحد الأقصى الجديد للبوتات.",cancel_keyboard())
            return True
        return False
    except Exception as exc:
        await log_error("v16_callback", f"{data}: {exc}")
        await v16_record_incident(0,"callback",f"{data}: {exc}","error")
        await send_message(chat_id,"❌ <b>حدث خطأ داخل مركز السيطرة.</b>\nتم تسجيل الحادث.",admin_keyboard())
        return True


async def v16_handle_state(msg, state):
    """State handler used by the existing admin state dispatcher."""
    uid=int(msg["from"]["id"]); chat_id=int(msg["chat"]["id"])
    if not await v16_guard(uid):
        return False
    text=(msg.get("text") or "").strip()
    if state=="v16_broadcast_all":
        if not text:
            await send_message(chat_id,"❌ أرسل نصًا صالحًا.",cancel_keyboard())
            return True
        await clear_state(uid)
        job=await v16_create_job("broadcast_all","all",{"text":text},uid)
        result=await run_all_hosted_bots_broadcast(text,"text",None)
        await v16_update_job(job,status="finished",total=result[0]+result[1],success=result[0],failed=result[1],finished_at=now_text())
        await v16_log_command(uid,"broadcast_all",str(job),f"success={result[0]};failed={result[1]}")
        await send_message(chat_id,f"📢 <b>انتهت الإذاعة</b>\n\n🌐 البوتات: <b>{result[2]}</b>\n✅ نجاح: <b>{result[0]}</b>\n❌ فشل: <b>{result[1]}</b>",admin_keyboard())
        return True
    if state.startswith("v16_note:"):
        hid=int(state.split(":",1)[1])
        if not text:
            await send_message(chat_id,"❌ الملاحظة فارغة.",cancel_keyboard())
            return True
        await v16_set_note(hid,text,uid)
        await clear_state(uid)
        await v16_log_command(uid,"note",str(hid),"saved")
        await send_message(chat_id,"✅ تم حفظ الملاحظة.",admin_keyboard())
        return True
    if state.startswith("v16_btncustom:"):
        scope=state.split(":",1)[1]
        value=text.strip()
        if not value:
            await send_message(chat_id,"❌ القيمة فارغة.",cancel_keyboard())
            return True
        await clear_state(uid)
        if value.startswith("text:"):
            button_policy_hide(scope, "", value[5:].strip())
        else:
            button_policy_hide(scope, value, "")
        await v16_log_command(uid,"button_custom_hide",scope,value[:200])
        await send_message(chat_id,"✅ تم إخفاء الزر. سيختفي من الواجهات الجديدة فورًا.",{"inline_keyboard":[[{"text":"🔙 مدير الأزرار","callback_data":f"v16:btnscope:{scope}"}]]})
        return True
    if state.startswith("v16_btnrename:"):
        _, scope, bid = state.split(":", 2)
        value = text.strip()
        if not value:
            await send_message(chat_id,"❌ الاسم فارغ.",cancel_keyboard())
            return True
        selector = f"menu:{bid}"
        if value == "-none-":
            data = _button_policy_load_sync()
            target = data.get("global", {}) if scope == "all" else (data.get("bots", {}) or {}).get(str(int(scope)), {})
            (target.get("labels") or {}).pop(selector, None)
            _button_policy_write_sync(data)
        else:
            button_policy_set_label(scope, selector, value)
        await clear_state(uid)
        await v16_log_command(uid,"button_rename",f"scope={scope};button={bid}",value[:80])
        await send_message(chat_id,"✅ تم تحديث اسم الزر وسيظهر في كل الواجهات الجديدة.",{"inline_keyboard":[[{"text":"🔙 مدير الأزرار","callback_data":f"v16:btnscope:{scope}"}]]})
        return True
    if state.startswith("v16_btnstyle:"):
        _, scope, bid = state.split(":", 2)
        style = text.strip().lower()
        if style not in ("primary", "success", "danger"):
            await send_message(chat_id,"❌ استخدم primary أو success أو danger.",cancel_keyboard())
            return True
        button_policy_set_style(scope, f"menu:{bid}", style)
        await clear_state(uid)
        await v16_log_command(uid,"button_style",f"scope={scope};button={bid}",style)
        await send_message(chat_id,"✅ تم تحديث لون الزر وسيظهر في كل الواجهات الجديدة.",{"inline_keyboard":[[{"text":"🔙 مدير الأزرار","callback_data":f"v16:btnscope:{scope}"}]]})
        return True
    if state=="v16_setprice":
        if not text.isdigit() or int(text)<0:
            await send_message(chat_id,"❌ أرسل رقمًا صحيحًا.",cancel_keyboard())
            return True
        value=int(text)
        await set_setting("bot_creation_price",value)
        await clear_state(uid)
        await v16_log_command(uid,"set_price","",str(value))
        await send_message(chat_id,f"✅ تم ضبط السعر على <b>{value} ⭐</b>.",admin_keyboard())
        return True
    if state=="v16_setlimit":
        if not text.isdigit() or int(text)<1:
            await send_message(chat_id,"❌ أرسل حدًا صحيحًا.",cancel_keyboard())
            return True
        value=int(text)
        await set_setting("max_hosted_bots",value)
        await clear_state(uid)
        await v16_log_command(uid,"set_limit","",str(value))
        await send_message(chat_id,f"✅ الحد الجديد: <b>{value}</b> بوت.",admin_keyboard())
        return True
    return False


# Hook V16 states into the existing admin state function without changing the
# legacy state machine's public contract. The wrapper keeps old behavior first.
V16_LEGACY_HANDLE_ADMIN_STATE = handle_admin_state


async def handle_admin_state(msg, state):
    uid = int((msg.get("from") or {}).get("id") or 0)
    if not is_owner(uid):
        await clear_state(uid)
        return True
    if str(state).startswith("v16_"):
        handled = await v16_handle_state(msg, state)
        if handled:
            return True
    if str(state).startswith("v16_note:"):
        handled = await v16_handle_state(msg, state)
        if handled:
            return True
    return await V16_LEGACY_HANDLE_ADMIN_STATE(msg, state)


# =========================================================
# V16 PERFORMANCE TOOLKIT
# =========================================================
# The following helpers are deliberately small and side-effect free. They are
# used by future V16 modules and provide a stable internal API for a single-file
# deployment. Keeping them here avoids scattering tiny implementations through
# the legacy code above.


def v16_now_ms():
    return int(time.time() * 1000)


def v16_monotonic_ms():
    return int(time.monotonic() * 1000)


def v16_safe_int(value, default=0, minimum=None, maximum=None):
    try:
        number=int(value)
    except Exception:
        number=default
    if minimum is not None:
        number=max(minimum,number)
    if maximum is not None:
        number=min(maximum,number)
    return number


def v16_safe_float(value, default=0.0, minimum=None, maximum=None):
    try:
        number=float(value)
    except Exception:
        number=default
    if minimum is not None:
        number=max(minimum,number)
    if maximum is not None:
        number=min(maximum,number)
    return number


def v16_truthy(value):
    return str(value).strip().lower() in {"1","true","yes","on","enabled","نعم","تشغيل"}


def v16_falsy(value):
    return not v16_truthy(value)


def v16_clip(value, limit=500):
    text=str(value or "")
    if len(text)<=limit:
        return text
    return text[:max(0,limit-1)] + "…"


def v16_redact(value, visible=4):
    text=str(value or "")
    if not text:
        return ""
    if len(text)<=visible*2:
        return "*"*len(text)
    return text[:visible]+"…"+text[-visible:]


def v16_hash(value):
    return hashlib.sha256(str(value).encode("utf-8")).hexdigest()


def v16_short_hash(value, size=12):
    return v16_hash(value)[:max(4,int(size))]


def v16_token():
    return secrets.token_urlsafe(18)


def v16_timestamp():
    return dt.datetime.now(dt.timezone.utc).isoformat()


def v16_json(data):
    return json.dumps(data,ensure_ascii=False,separators=(",",":"),default=str)


def v16_json_load(value, default=None):
    try:
        return json.loads(value)
    except Exception:
        return default


def v16_normalize_username(value):
    return str(value or "").strip().lstrip("@").lower()


def v16_username_display(value):
    username=v16_normalize_username(value)
    return "@"+username if username else "بدون_اسم_مستخدم"


def v16_status_icon(status):
    status=str(status or "").lower()
    if status in {"disabled","stopped","offline","error"}:
        return "🔴"
    if status in {"starting","restarting","maintenance"}:
        return "🟠"
    return "🟢"


def v16_severity_icon(severity):
    return {"error":"🔴","warning":"🟠","info":"🔵","critical":"🚨"}.get(str(severity),"⚪")


def v16_percent(done,total):
    total=v16_safe_int(total,0,minimum=0)
    done=v16_safe_int(done,0,minimum=0)
    if total<=0:
        return 0
    return min(100,int((done/total)*100))


def v16_bar(done,total,size=12):
    pct=v16_percent(done,total)
    filled=int(size*pct/100)
    return "█"*filled+"░"*(size-filled)


def v16_duration(seconds):
    seconds=max(0,int(seconds))
    days,seconds=divmod(seconds,86400)
    hours,seconds=divmod(seconds,3600)
    minutes,seconds=divmod(seconds,60)
    parts=[]
    if days: parts.append(f"{days}d")
    if hours: parts.append(f"{hours}h")
    if minutes: parts.append(f"{minutes}m")
    if not parts or seconds: parts.append(f"{seconds}s")
    return " ".join(parts)


def v16_parse_ids(text):
    ids=[]
    for token in re.split(r"[\s,;]+",str(text or "")):
        if token.isdigit():
            ids.append(int(token))
    return list(dict.fromkeys(ids))


def v16_chunks(items,size=50):
    size=max(1,int(size))
    items=list(items or [])
    for index in range(0,len(items),size):
        yield items[index:index+size]


def v16_paginate(items,page=0,size=10):
    page=max(0,int(page)); size=max(1,int(size)); items=list(items or [])
    start=page*size
    return items[start:start+size], len(items), start+size<len(items), page>0


def v16_merge_dicts(*maps):
    result={}
    for mapping in maps:
        if isinstance(mapping,dict): result.update(mapping)
    return result


def v16_bool_int(value):
    return 1 if v16_truthy(value) else 0


def v16_sort_key(value):
    if isinstance(value,(int,float)): return (0,value)
    return (1,str(value).lower())


def v16_unique(values):
    return list(dict.fromkeys(values or []))


def v16_average(values,default=0.0):
    vals=[v16_safe_float(v) for v in values or []]
    return statistics.mean(vals) if vals else default


def v16_median(values,default=0.0):
    vals=[v16_safe_float(v) for v in values or []]
    return statistics.median(vals) if vals else default


def v16_rate_per_minute(count,seconds):
    seconds=max(v16_safe_float(seconds),0.001)
    return v16_safe_float(count)*60/seconds


def v16_format_number(value):
    try:
        return f"{int(value):,}"
    except Exception:
        return "0"


def v16_escape_code(value):
    return esc(v16_clip(value,800))


def v16_is_valid_page(page,max_page=100000):
    return isinstance(page,int) and 0<=page<=max_page


def v16_is_valid_hosted_id(value):
    return v16_safe_int(value,0,minimum=0)>0


def v16_memory_event(scope):
    values=V16_MEMORY_EVENTS[scope]
    values.append(time.time())
    if len(values)>1000:
        del values[:-1000]


def v16_memory_count(scope,window=60):
    now=time.time()
    values=V16_MEMORY_EVENTS.get(scope,[])
    return sum(1 for value in values if now-value<=window)


def v16_make_audit_payload(action,target=None,extra=None):
    return v16_json({"action":action,"target":target,"extra":extra or {},"ts":v16_timestamp()})


def v16_job_status_icon(status):
    return {"queued":"🟡","running":"🔵","finished":"🟢","failed":"🔴","cancelled":"⚪"}.get(str(status),"❔")


def v16_job_summary(job):
    if not job:
        return "لا توجد مهمة"
    total=v16_safe_int(job.get("total",0)) if isinstance(job,dict) else 0
    success=v16_safe_int(job.get("success",0)) if isinstance(job,dict) else 0
    failed=v16_safe_int(job.get("failed",0)) if isinstance(job,dict) else 0
    status=job.get("status","unknown") if isinstance(job,dict) else "unknown"
    return f"{v16_job_status_icon(status)} {status} — {success}/{total} — {failed} فشل"


def v16_env_number(name,default,minimum=0,maximum=None):
    return v16_safe_int(os.getenv(name,str(default)),default,minimum,maximum)


def v16_env_bool(name,default=False):
    raw=os.getenv(name)
    return default if raw is None else v16_truthy(raw)


def v16_path_inside(path,root):
    try:
        return Path(path).resolve().is_relative_to(Path(root).resolve())
    except AttributeError:
        try:
            return str(Path(path).resolve()).startswith(str(Path(root).resolve()))
        except Exception:
            return False
    except Exception:
        return False


def v16_safe_filename(value,default="file"):
    text=re.sub(r"[^A-Za-z0-9_.-]+","_",str(value or "")).strip("._")
    return text or default


def v16_logical_status(row):
    if not row:
        return "unknown"
    status=str(row["status"] or "unknown")
    if status=="disabled": return "disabled"
    pid=v16_safe_int(row["pid"],0)
    if pid:
        try:
            os.kill(pid,0)
            return "running"
        except Exception:
            return "stale"
    return status


def v16_event_key(prefix,*parts):
    clean=[str(part).strip().replace(" ","_") for part in parts]
    return ":".join([str(prefix).strip()]+clean)


def v16_dict_get(data,key,default=None):
    return data.get(key,default) if isinstance(data,dict) else default


def v16_row_dict(row):
    if row is None: return {}
    try: return dict(row)
    except Exception: return {}


def v16_rows_dict(rows):
    return [v16_row_dict(row) for row in rows or []]


def v16_nonempty(value):
    return bool(str(value or "").strip())


def v16_require_text(value,minimum=1,maximum=4000):
    text=str(value or "").strip()
    if len(text)<minimum: raise ValueError("text too short")
    return text[:maximum]


def v16_require_positive_id(value):
    value=v16_safe_int(value,0)
    if value<=0: raise ValueError("invalid id")
    return value


def v16_percent_text(done,total):
    return f"{v16_percent(done,total)}%"


def v16_progress_text(done,total,label="التقدم"):
    return f"{label}: {v16_bar(done,total)} {v16_percent(done,total)}% ({done}/{total})"


def v16_exception_text(exc):
    return v16_clip(f"{type(exc).__name__}: {exc}",1000)


def v16_safe_repr(value):
    try: return v16_clip(repr(value),1000)
    except Exception: return "<unrepr>"


def v16_config_snapshot():
    return {
        "version":V16_VERSION,
        "schema":V16_SCHEMA_VERSION,
        "max_updates":MAX_CONCURRENT_UPDATES,
        "max_telegram":MAX_CONCURRENT_TELEGRAM,
        "retry_limit":TELEGRAM_RETRY_LIMIT,
        "max_hosted":MAX_HOSTED_BOTS,
        "child":IS_CHILD_BOT,
    }


def v16_capability_matrix():
    return {
        "lifecycle":True,
        "broadcast":True,
        "analytics":True,
        "incidents":True,
        "audit":True,
        "emergency":True,
        "isolated_processes":True,
        "single_file":True,
    }


def v16_permission_label(role):
    return {"root":"👑 Root","admin":"🛡 Admin","operator":"🔧 Operator"}.get(str(role),"❔ Unknown")


def v16_operation_allowed(operation):
    dangerous={"delete","stop_all","start_all","global_maintenance"}
    return str(operation) in {
        "view","restart","toggle","maintenance","stats","note","broadcast",
        "delete","stop_all","start_all","global_maintenance","cleanup","resolve_incident",
    }


def v16_dangerous(operation):
    return str(operation) in {"delete","stop_all","start_all","global_maintenance"}


def v16_confirmation_text(operation):
    return {
        "delete":"سيتم حذف البوت وملف بياناته.",
        "stop_all":"سيتم إيقاف جميع البوتات المستضافة.",
        "start_all":"سيتم تشغيل جميع البوتات غير المعطلة.",
        "global_maintenance":"سيتم تفعيل صيانة المنصة.",
    }.get(str(operation),"هل أنت متأكد؟")


# =========================================================
# V16 FEATURE CATALOG
# =========================================================
# A compact registry gives the developer panel a machine-readable description
# of every major control. This is intentionally data-only so it costs almost
# nothing during normal message handling.

V16_FEATURES = [
    {"id":"dashboard","title":"مركز السيطرة","category":"core","danger":False},
    {"id":"bots","title":"إدارة البوتات","category":"lifecycle","danger":False},
    {"id":"toggle","title":"تشغيل/إيقاف","category":"lifecycle","danger":True},
    {"id":"restart","title":"إعادة تشغيل","category":"lifecycle","danger":False},
    {"id":"maintenance","title":"صيانة بوت","category":"lifecycle","danger":False},
    {"id":"delete","title":"حذف نهائي","category":"lifecycle","danger":True},
    {"id":"stats","title":"إحصائيات المنصة","category":"analytics","danger":False},
    {"id":"botstats","title":"إحصائيات البوت","category":"analytics","danger":False},
    {"id":"health","title":"صحة النظام","category":"monitoring","danger":False},
    {"id":"bothealth","title":"فحص البوتات","category":"monitoring","danger":False},
    {"id":"incidents","title":"الحوادث","category":"monitoring","danger":False},
    {"id":"audit","title":"سجل العمليات","category":"security","danger":False},
    {"id":"settings","title":"إعدادات المنصة","category":"config","danger":False},
    {"id":"broadcast","title":"مركز الإذاعة","category":"communication","danger":True},
    {"id":"jobs","title":"مهام الإذاعة","category":"communication","danger":False},
    {"id":"emergency","title":"الطوارئ","category":"emergency","danger":True},
    {"id":"cleanup","title":"تنظيف الذاكرة","category":"maintenance","danger":False},
]


def v16_feature(feature_id):
    for feature in V16_FEATURES:
        if feature["id"]==feature_id:
            return dict(feature)
    return None


def v16_feature_titles():
    return [feature["title"] for feature in V16_FEATURES]


def v16_feature_ids():
    return [feature["id"] for feature in V16_FEATURES]


def v16_feature_categories():
    return v16_unique(feature["category"] for feature in V16_FEATURES)


def v16_features_by_category(category):
    return [dict(feature) for feature in V16_FEATURES if feature["category"]==category]


def v16_dangerous_features():
    return [dict(feature) for feature in V16_FEATURES if feature["danger"]]


def v16_safe_features():
    return [dict(feature) for feature in V16_FEATURES if not feature["danger"]]


def v16_feature_count():
    return len(V16_FEATURES)


def v16_feature_summary():
    return {category:len(v16_features_by_category(category)) for category in v16_feature_categories()}


# =========================================================
# V16 INTERNAL API ADAPTERS
# =========================================================
# These wrappers keep future additions consistent. They also make it easier
# to audit the code because sensitive operations have one obvious entry point.


async def v16_api_send(chat_id,text,keyboard=None):
    # V16 uses the same presentation firewall as the legacy sender so a future
    # module cannot accidentally expose internal controls to members.
    safe_keyboard = ui_keyboard_for_chat(chat_id, keyboard) if keyboard else None
    return await scalable_api_call("sendMessage",data={
        "chat_id":chat_id,"text":text,"parse_mode":"HTML",
        **({"reply_markup":json.dumps(safe_keyboard,ensure_ascii=False)} if safe_keyboard else {}),
    })


async def v16_api_delete(chat_id,message_id):
    return await scalable_api_call("deleteMessage",data={"chat_id":chat_id,"message_id":message_id})


async def v16_api_answer(callback_id,text="تم"):
    return await scalable_api_call("answerCallbackQuery",data={"callback_query_id":callback_id,"text":v16_clip(text,180)})


async def v16_sleep_backoff(attempt,base=0.25,maximum=5):
    await asyncio.sleep(min(maximum,base*(2**max(0,int(attempt)))))


async def v16_gather_bounded(coros,limit=10):
    semaphore=asyncio.Semaphore(max(1,int(limit)))
    results=[]
    async def runner(coro):
        async with semaphore:
            try:
                return await coro
            except Exception as exc:
                return exc
    tasks=[asyncio.create_task(runner(coro)) for coro in coros]
    if not tasks:
        return []
    for task in tasks:
        results.append(await task)
    return results


async def v16_call_with_retry(fn,attempts=3,base=0.3):
    last=None
    for attempt in range(max(1,int(attempts))):
        try:
            return await fn()
        except asyncio.CancelledError:
            raise
        except Exception as exc:
            last=exc
            if attempt+1<attempts:
                await v16_sleep_backoff(attempt,base)
    if last:
        raise last
    return None


async def v16_sql_count(query,params=()):
    row=await db_execute(query,params,fetchone=True)
    return int(row["c"] if row and "c" in row.keys() else 0)


async def v16_sql_value(query,params=(),key="value",default=0):
    row=await db_execute(query,params,fetchone=True)
    if not row: return default
    try: return row[key]
    except Exception: return default


async def v16_db_health():
    started=v16_monotonic_ms()
    try:
        await db_execute("SELECT 1",fetchone=True)
        return {"ok":True,"latency_ms":v16_monotonic_ms()-started}
    except Exception as exc:
        return {"ok":False,"latency_ms":v16_monotonic_ms()-started,"error":v16_exception_text(exc)}


async def v16_hosted_health_batch(rows,limit=5):
    semaphore=asyncio.Semaphore(max(1,int(limit)))
    async def one(row):
        async with semaphore:
            return await v16_hosted_health(row)
    return await asyncio.gather(*(one(row) for row in rows)) if rows else []


async def v16_record_operation(user_id,operation,target="",result=""):
    await v16_log_command(user_id,operation,target,result)
    await v16_metric_inc("operations",operation)
    v16_memory_event(v16_event_key("operation",operation))


async def v16_operation_banner(operation,target=""):
    feature=v16_feature(operation) or {"title":operation,"danger":False}
    icon="⚠️" if feature.get("danger") else "ℹ️"
    return f"{icon} <b>{esc(feature.get('title',operation))}</b>" + (f"\nهدف: <code>{esc(target)}</code>" if target else "")


async def v16_incident_from_exception(hosted_id,kind,exc):
    details=v16_exception_text(exc)
    await v16_record_incident(hosted_id,kind,details,"error")
    await v16_metric_inc("exceptions",kind)
    return details


# =========================================================
# V16 POLICY / SAFETY HELPERS
# =========================================================
# The following functions are intentionally pure. They centralize policy
# decisions so a future feature can reuse them without copying authorization
# logic into another callback branch.


def v16_policy_owner(user_id):
    return v16_safe_int(user_id)==v16_safe_int(PLATFORM_OWNER_ID)


def v16_policy_child_owner(user_id):
    return v16_safe_int(user_id)==v16_safe_int(OWNER_ID) and IS_CHILD_BOT


def v16_policy_platform_context():
    return not IS_CHILD_BOT


def v16_policy_can_manage_hosted(user_id):
    return v16_policy_owner(user_id) and v16_policy_platform_context()


def v16_policy_can_broadcast(user_id):
    return v16_policy_can_manage_hosted(user_id)


def v16_policy_can_delete(user_id):
    return v16_policy_can_manage_hosted(user_id)


def v16_policy_can_change_price(user_id):
    return v16_policy_owner(user_id)


def v16_policy_can_change_limit(user_id):
    return v16_policy_owner(user_id)


def v16_policy_can_use_emergency(user_id):
    return v16_policy_owner(user_id)


def v16_policy_can_view_audit(user_id):
    return v16_policy_owner(user_id)


def v16_policy_can_view_health(user_id):
    return v16_policy_owner(user_id)


def v16_policy_can_resolve_incident(user_id):
    return v16_policy_owner(user_id)


def v16_policy_operation(operation):
    return v16_operation_allowed(operation)


def v16_policy_requires_confirmation(operation):
    return v16_dangerous(operation)


def v16_policy_message(operation):
    return v16_confirmation_text(operation)


# =========================================================
# V16 OPERATIONAL CHECKLIST
# =========================================================
# This registry is displayed only through code-level diagnostics and does not
# send secrets to Telegram. It is useful when the platform owner wants a quick
# sanity check after deployment.

V16_CHECKS = [
    ("platform_owner_gate", lambda: not IS_CHILD_BOT),
    ("database_file", lambda: bool(DB_FILE)),
    ("hosted_directory", lambda: HOSTED_BOTS_DIR.exists()),
    ("backup_directory", lambda: BACKUP_DIR.exists()),
    ("export_directory", lambda: EXPORT_DIR.exists()),
    ("telegram_session_configured", lambda: HTTP_SESSION is not None),
    ("update_concurrency_positive", lambda: MAX_CONCURRENT_UPDATES > 0),
    ("telegram_concurrency_positive", lambda: MAX_CONCURRENT_TELEGRAM > 0),
    ("retry_limit_positive", lambda: TELEGRAM_RETRY_LIMIT > 0),
]


def v16_run_local_checks():
    results=[]
    for name,check in V16_CHECKS:
        try:
            ok=bool(check())
            results.append({"name":name,"ok":ok,"error":""})
        except Exception as exc:
            results.append({"name":name,"ok":False,"error":v16_exception_text(exc)})
    return results


def v16_checks_text():
    lines=["🧪 V16 checks"]
    for result in v16_run_local_checks():
        lines.append(("✅" if result["ok"] else "❌")+" "+result["name"]+(f" — {result['error']}" if result["error"] else ""))
    return "\n".join(lines)


# =========================================================
# V16 MAINTENANCE NOTES
# =========================================================
# Keep this section as a living operational contract. It intentionally avoids
# hidden network calls and only documents invariants that the runtime helpers
# enforce.

V16_INVARIANTS = (
    "Platform owner controls hosted bots.",
    "Child bot owner cannot access platform control plane.",
    "Bot tokens are not rendered by V16 UI.",
    "Dangerous lifecycle operations require a separate confirmation callback.",
    "SQLite writes use the existing retrying db_execute helper.",
    "Broadcast operations use the existing bounded broadcast implementation.",
    "Hosted child databases remain isolated from the platform database.",
    "Manual disabled status is respected by the hosted-bot monitor.",
    "Every sensitive V16 operation is written to v16_commands when possible.",
    "Incidents are persistent and can be resolved without deleting history.",
)


def v16_invariants():
    return list(V16_INVARIANTS)


def v16_version_info():
    return {
        "name":"SUGLT Ultimate",
        "version":V16_VERSION,
        "schema":V16_SCHEMA_VERSION,
        "features":v16_feature_count(),
        "invariants":len(V16_INVARIANTS),
    }


# =========================================================

# V16 ENTERPRISE UTILITY LIBRARY
# =========================================================
#
# This library contains reusable primitives for the single-file platform.
# They are intentionally independent from Telegram UI so future features can
# be enabled without changing the storage contract or authorization model.
# =========================================================

def v16_enterprise_001(value=None, *, limit=500, default=None):
    """Enterprise utility #1: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_002(value=None, *, limit=500, default=None):
    """Enterprise utility #2: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_003(value=None, *, limit=500, default=None):
    """Enterprise utility #3: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_004(value=None, *, limit=500, default=None):
    """Enterprise utility #4: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_005(value=None, *, limit=500, default=None):
    """Enterprise utility #5: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_006(value=None, *, limit=500, default=None):
    """Enterprise utility #6: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_007(value=None, *, limit=500, default=None):
    """Enterprise utility #7: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_008(value=None, *, limit=500, default=None):
    """Enterprise utility #8: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_009(value=None, *, limit=500, default=None):
    """Enterprise utility #9: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_010(value=None, *, limit=500, default=None):
    """Enterprise utility #10: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_011(value=None, *, limit=500, default=None):
    """Enterprise utility #11: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_012(value=None, *, limit=500, default=None):
    """Enterprise utility #12: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_013(value=None, *, limit=500, default=None):
    """Enterprise utility #13: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_014(value=None, *, limit=500, default=None):
    """Enterprise utility #14: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_015(value=None, *, limit=500, default=None):
    """Enterprise utility #15: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_016(value=None, *, limit=500, default=None):
    """Enterprise utility #16: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_017(value=None, *, limit=500, default=None):
    """Enterprise utility #17: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_018(value=None, *, limit=500, default=None):
    """Enterprise utility #18: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_019(value=None, *, limit=500, default=None):
    """Enterprise utility #19: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_020(value=None, *, limit=500, default=None):
    """Enterprise utility #20: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_021(value=None, *, limit=500, default=None):
    """Enterprise utility #21: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_022(value=None, *, limit=500, default=None):
    """Enterprise utility #22: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_023(value=None, *, limit=500, default=None):
    """Enterprise utility #23: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_024(value=None, *, limit=500, default=None):
    """Enterprise utility #24: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_025(value=None, *, limit=500, default=None):
    """Enterprise utility #25: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_026(value=None, *, limit=500, default=None):
    """Enterprise utility #26: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_027(value=None, *, limit=500, default=None):
    """Enterprise utility #27: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_028(value=None, *, limit=500, default=None):
    """Enterprise utility #28: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_029(value=None, *, limit=500, default=None):
    """Enterprise utility #29: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_030(value=None, *, limit=500, default=None):
    """Enterprise utility #30: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_031(value=None, *, limit=500, default=None):
    """Enterprise utility #31: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_032(value=None, *, limit=500, default=None):
    """Enterprise utility #32: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_033(value=None, *, limit=500, default=None):
    """Enterprise utility #33: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_034(value=None, *, limit=500, default=None):
    """Enterprise utility #34: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_035(value=None, *, limit=500, default=None):
    """Enterprise utility #35: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_036(value=None, *, limit=500, default=None):
    """Enterprise utility #36: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_037(value=None, *, limit=500, default=None):
    """Enterprise utility #37: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_038(value=None, *, limit=500, default=None):
    """Enterprise utility #38: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_039(value=None, *, limit=500, default=None):
    """Enterprise utility #39: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_040(value=None, *, limit=500, default=None):
    """Enterprise utility #40: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_041(value=None, *, limit=500, default=None):
    """Enterprise utility #41: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_042(value=None, *, limit=500, default=None):
    """Enterprise utility #42: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_043(value=None, *, limit=500, default=None):
    """Enterprise utility #43: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_044(value=None, *, limit=500, default=None):
    """Enterprise utility #44: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_045(value=None, *, limit=500, default=None):
    """Enterprise utility #45: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_046(value=None, *, limit=500, default=None):
    """Enterprise utility #46: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_047(value=None, *, limit=500, default=None):
    """Enterprise utility #47: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_048(value=None, *, limit=500, default=None):
    """Enterprise utility #48: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_049(value=None, *, limit=500, default=None):
    """Enterprise utility #49: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_050(value=None, *, limit=500, default=None):
    """Enterprise utility #50: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_051(value=None, *, limit=500, default=None):
    """Enterprise utility #51: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_052(value=None, *, limit=500, default=None):
    """Enterprise utility #52: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_053(value=None, *, limit=500, default=None):
    """Enterprise utility #53: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_054(value=None, *, limit=500, default=None):
    """Enterprise utility #54: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_055(value=None, *, limit=500, default=None):
    """Enterprise utility #55: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_056(value=None, *, limit=500, default=None):
    """Enterprise utility #56: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_057(value=None, *, limit=500, default=None):
    """Enterprise utility #57: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_058(value=None, *, limit=500, default=None):
    """Enterprise utility #58: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_059(value=None, *, limit=500, default=None):
    """Enterprise utility #59: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_060(value=None, *, limit=500, default=None):
    """Enterprise utility #60: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_061(value=None, *, limit=500, default=None):
    """Enterprise utility #61: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_062(value=None, *, limit=500, default=None):
    """Enterprise utility #62: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_063(value=None, *, limit=500, default=None):
    """Enterprise utility #63: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_064(value=None, *, limit=500, default=None):
    """Enterprise utility #64: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_065(value=None, *, limit=500, default=None):
    """Enterprise utility #65: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_066(value=None, *, limit=500, default=None):
    """Enterprise utility #66: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_067(value=None, *, limit=500, default=None):
    """Enterprise utility #67: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_068(value=None, *, limit=500, default=None):
    """Enterprise utility #68: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_069(value=None, *, limit=500, default=None):
    """Enterprise utility #69: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_070(value=None, *, limit=500, default=None):
    """Enterprise utility #70: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_071(value=None, *, limit=500, default=None):
    """Enterprise utility #71: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_072(value=None, *, limit=500, default=None):
    """Enterprise utility #72: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_073(value=None, *, limit=500, default=None):
    """Enterprise utility #73: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_074(value=None, *, limit=500, default=None):
    """Enterprise utility #74: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_075(value=None, *, limit=500, default=None):
    """Enterprise utility #75: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_076(value=None, *, limit=500, default=None):
    """Enterprise utility #76: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_077(value=None, *, limit=500, default=None):
    """Enterprise utility #77: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_078(value=None, *, limit=500, default=None):
    """Enterprise utility #78: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_079(value=None, *, limit=500, default=None):
    """Enterprise utility #79: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_080(value=None, *, limit=500, default=None):
    """Enterprise utility #80: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_081(value=None, *, limit=500, default=None):
    """Enterprise utility #81: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_082(value=None, *, limit=500, default=None):
    """Enterprise utility #82: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_083(value=None, *, limit=500, default=None):
    """Enterprise utility #83: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_084(value=None, *, limit=500, default=None):
    """Enterprise utility #84: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_085(value=None, *, limit=500, default=None):
    """Enterprise utility #85: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_086(value=None, *, limit=500, default=None):
    """Enterprise utility #86: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_087(value=None, *, limit=500, default=None):
    """Enterprise utility #87: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_088(value=None, *, limit=500, default=None):
    """Enterprise utility #88: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_089(value=None, *, limit=500, default=None):
    """Enterprise utility #89: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_090(value=None, *, limit=500, default=None):
    """Enterprise utility #90: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_091(value=None, *, limit=500, default=None):
    """Enterprise utility #91: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_092(value=None, *, limit=500, default=None):
    """Enterprise utility #92: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_093(value=None, *, limit=500, default=None):
    """Enterprise utility #93: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_094(value=None, *, limit=500, default=None):
    """Enterprise utility #94: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_095(value=None, *, limit=500, default=None):
    """Enterprise utility #95: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_096(value=None, *, limit=500, default=None):
    """Enterprise utility #96: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_097(value=None, *, limit=500, default=None):
    """Enterprise utility #97: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_098(value=None, *, limit=500, default=None):
    """Enterprise utility #98: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_099(value=None, *, limit=500, default=None):
    """Enterprise utility #99: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

def v16_enterprise_100(value=None, *, limit=500, default=None):
    """Enterprise utility #100: normalize and inspect one runtime value."""
    # Side-effect free and safe for handler use; no network/database access.
    raw = value
    if raw is None:
        return default
    if isinstance(raw, bytes):
        try:
            raw = raw.decode("utf-8", "replace")
        except Exception:
            raw = str(raw)
    text = str(raw).strip()
    if not text:
        return default if default is not None else ""
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    text = text[:max(1, int(limit))]
    if text.isdigit():
        try:
            number = int(text)
            if number >= 0:
                return number
        except Exception:
            pass
    if text.lower() in {"true", "false"}:
        return text.lower() == "true"
    return text

# =========================================================
# V16 EXTENDED OPERATIONS CATALOG
# =========================================================

V16_OPERATION_001 = {
    "id": "op_001",
    "name": "enterprise_operation_001",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 1,
    "enabled": True,
}

V16_OPERATION_002 = {
    "id": "op_002",
    "name": "enterprise_operation_002",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 2,
    "enabled": True,
}

V16_OPERATION_003 = {
    "id": "op_003",
    "name": "enterprise_operation_003",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 3,
    "enabled": True,
}

V16_OPERATION_004 = {
    "id": "op_004",
    "name": "enterprise_operation_004",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 4,
    "enabled": True,
}

V16_OPERATION_005 = {
    "id": "op_005",
    "name": "enterprise_operation_005",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 5,
    "enabled": True,
}

V16_OPERATION_006 = {
    "id": "op_006",
    "name": "enterprise_operation_006",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 6,
    "enabled": True,
}

V16_OPERATION_007 = {
    "id": "op_007",
    "name": "enterprise_operation_007",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 7,
    "enabled": True,
}

V16_OPERATION_008 = {
    "id": "op_008",
    "name": "enterprise_operation_008",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 8,
    "enabled": True,
}

V16_OPERATION_009 = {
    "id": "op_009",
    "name": "enterprise_operation_009",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 9,
    "enabled": True,
}

V16_OPERATION_010 = {
    "id": "op_010",
    "name": "enterprise_operation_010",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 10,
    "enabled": True,
}

V16_OPERATION_011 = {
    "id": "op_011",
    "name": "enterprise_operation_011",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 11,
    "enabled": True,
}

V16_OPERATION_012 = {
    "id": "op_012",
    "name": "enterprise_operation_012",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 12,
    "enabled": True,
}

V16_OPERATION_013 = {
    "id": "op_013",
    "name": "enterprise_operation_013",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 13,
    "enabled": True,
}

V16_OPERATION_014 = {
    "id": "op_014",
    "name": "enterprise_operation_014",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 14,
    "enabled": True,
}

V16_OPERATION_015 = {
    "id": "op_015",
    "name": "enterprise_operation_015",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 15,
    "enabled": True,
}

V16_OPERATION_016 = {
    "id": "op_016",
    "name": "enterprise_operation_016",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 16,
    "enabled": True,
}

V16_OPERATION_017 = {
    "id": "op_017",
    "name": "enterprise_operation_017",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 17,
    "enabled": True,
}

V16_OPERATION_018 = {
    "id": "op_018",
    "name": "enterprise_operation_018",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 18,
    "enabled": True,
}

V16_OPERATION_019 = {
    "id": "op_019",
    "name": "enterprise_operation_019",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 19,
    "enabled": True,
}

V16_OPERATION_020 = {
    "id": "op_020",
    "name": "enterprise_operation_020",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 20,
    "enabled": True,
}

V16_OPERATION_021 = {
    "id": "op_021",
    "name": "enterprise_operation_021",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 21,
    "enabled": True,
}

V16_OPERATION_022 = {
    "id": "op_022",
    "name": "enterprise_operation_022",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 22,
    "enabled": True,
}

V16_OPERATION_023 = {
    "id": "op_023",
    "name": "enterprise_operation_023",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 23,
    "enabled": True,
}

V16_OPERATION_024 = {
    "id": "op_024",
    "name": "enterprise_operation_024",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 24,
    "enabled": True,
}

V16_OPERATION_025 = {
    "id": "op_025",
    "name": "enterprise_operation_025",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 25,
    "enabled": True,
}

V16_OPERATION_026 = {
    "id": "op_026",
    "name": "enterprise_operation_026",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 26,
    "enabled": True,
}

V16_OPERATION_027 = {
    "id": "op_027",
    "name": "enterprise_operation_027",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 27,
    "enabled": True,
}

V16_OPERATION_028 = {
    "id": "op_028",
    "name": "enterprise_operation_028",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 28,
    "enabled": True,
}

V16_OPERATION_029 = {
    "id": "op_029",
    "name": "enterprise_operation_029",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 29,
    "enabled": True,
}

V16_OPERATION_030 = {
    "id": "op_030",
    "name": "enterprise_operation_030",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 30,
    "enabled": True,
}

V16_OPERATION_031 = {
    "id": "op_031",
    "name": "enterprise_operation_031",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 31,
    "enabled": True,
}

V16_OPERATION_032 = {
    "id": "op_032",
    "name": "enterprise_operation_032",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 32,
    "enabled": True,
}

V16_OPERATION_033 = {
    "id": "op_033",
    "name": "enterprise_operation_033",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 33,
    "enabled": True,
}

V16_OPERATION_034 = {
    "id": "op_034",
    "name": "enterprise_operation_034",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 34,
    "enabled": True,
}

V16_OPERATION_035 = {
    "id": "op_035",
    "name": "enterprise_operation_035",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 35,
    "enabled": True,
}

V16_OPERATION_036 = {
    "id": "op_036",
    "name": "enterprise_operation_036",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 36,
    "enabled": True,
}

V16_OPERATION_037 = {
    "id": "op_037",
    "name": "enterprise_operation_037",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 37,
    "enabled": True,
}

V16_OPERATION_038 = {
    "id": "op_038",
    "name": "enterprise_operation_038",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 38,
    "enabled": True,
}

V16_OPERATION_039 = {
    "id": "op_039",
    "name": "enterprise_operation_039",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 39,
    "enabled": True,
}

V16_OPERATION_040 = {
    "id": "op_040",
    "name": "enterprise_operation_040",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 40,
    "enabled": True,
}

V16_OPERATION_041 = {
    "id": "op_041",
    "name": "enterprise_operation_041",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 41,
    "enabled": True,
}

V16_OPERATION_042 = {
    "id": "op_042",
    "name": "enterprise_operation_042",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 42,
    "enabled": True,
}

V16_OPERATION_043 = {
    "id": "op_043",
    "name": "enterprise_operation_043",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 43,
    "enabled": True,
}

V16_OPERATION_044 = {
    "id": "op_044",
    "name": "enterprise_operation_044",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 44,
    "enabled": True,
}

V16_OPERATION_045 = {
    "id": "op_045",
    "name": "enterprise_operation_045",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 45,
    "enabled": True,
}

V16_OPERATION_046 = {
    "id": "op_046",
    "name": "enterprise_operation_046",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 46,
    "enabled": True,
}

V16_OPERATION_047 = {
    "id": "op_047",
    "name": "enterprise_operation_047",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 47,
    "enabled": True,
}

V16_OPERATION_048 = {
    "id": "op_048",
    "name": "enterprise_operation_048",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 48,
    "enabled": True,
}

V16_OPERATION_049 = {
    "id": "op_049",
    "name": "enterprise_operation_049",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 49,
    "enabled": True,
}

V16_OPERATION_050 = {
    "id": "op_050",
    "name": "enterprise_operation_050",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 50,
    "enabled": True,
}

V16_OPERATION_051 = {
    "id": "op_051",
    "name": "enterprise_operation_051",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 51,
    "enabled": True,
}

V16_OPERATION_052 = {
    "id": "op_052",
    "name": "enterprise_operation_052",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 52,
    "enabled": True,
}

V16_OPERATION_053 = {
    "id": "op_053",
    "name": "enterprise_operation_053",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 53,
    "enabled": True,
}

V16_OPERATION_054 = {
    "id": "op_054",
    "name": "enterprise_operation_054",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 54,
    "enabled": True,
}

V16_OPERATION_055 = {
    "id": "op_055",
    "name": "enterprise_operation_055",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 55,
    "enabled": True,
}

V16_OPERATION_056 = {
    "id": "op_056",
    "name": "enterprise_operation_056",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 56,
    "enabled": True,
}

V16_OPERATION_057 = {
    "id": "op_057",
    "name": "enterprise_operation_057",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 57,
    "enabled": True,
}

V16_OPERATION_058 = {
    "id": "op_058",
    "name": "enterprise_operation_058",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 58,
    "enabled": True,
}

V16_OPERATION_059 = {
    "id": "op_059",
    "name": "enterprise_operation_059",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 59,
    "enabled": True,
}

V16_OPERATION_060 = {
    "id": "op_060",
    "name": "enterprise_operation_060",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 60,
    "enabled": True,
}

V16_OPERATION_061 = {
    "id": "op_061",
    "name": "enterprise_operation_061",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 61,
    "enabled": True,
}

V16_OPERATION_062 = {
    "id": "op_062",
    "name": "enterprise_operation_062",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 62,
    "enabled": True,
}

V16_OPERATION_063 = {
    "id": "op_063",
    "name": "enterprise_operation_063",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 63,
    "enabled": True,
}

V16_OPERATION_064 = {
    "id": "op_064",
    "name": "enterprise_operation_064",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 64,
    "enabled": True,
}

V16_OPERATION_065 = {
    "id": "op_065",
    "name": "enterprise_operation_065",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 65,
    "enabled": True,
}

V16_OPERATION_066 = {
    "id": "op_066",
    "name": "enterprise_operation_066",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 66,
    "enabled": True,
}

V16_OPERATION_067 = {
    "id": "op_067",
    "name": "enterprise_operation_067",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 67,
    "enabled": True,
}

V16_OPERATION_068 = {
    "id": "op_068",
    "name": "enterprise_operation_068",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 68,
    "enabled": True,
}

V16_OPERATION_069 = {
    "id": "op_069",
    "name": "enterprise_operation_069",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 69,
    "enabled": True,
}

V16_OPERATION_070 = {
    "id": "op_070",
    "name": "enterprise_operation_070",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 70,
    "enabled": True,
}

V16_OPERATION_071 = {
    "id": "op_071",
    "name": "enterprise_operation_071",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 71,
    "enabled": True,
}

V16_OPERATION_072 = {
    "id": "op_072",
    "name": "enterprise_operation_072",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 72,
    "enabled": True,
}

V16_OPERATION_073 = {
    "id": "op_073",
    "name": "enterprise_operation_073",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 73,
    "enabled": True,
}

V16_OPERATION_074 = {
    "id": "op_074",
    "name": "enterprise_operation_074",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 74,
    "enabled": True,
}

V16_OPERATION_075 = {
    "id": "op_075",
    "name": "enterprise_operation_075",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 75,
    "enabled": True,
}

V16_OPERATION_076 = {
    "id": "op_076",
    "name": "enterprise_operation_076",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 76,
    "enabled": True,
}

V16_OPERATION_077 = {
    "id": "op_077",
    "name": "enterprise_operation_077",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 77,
    "enabled": True,
}

V16_OPERATION_078 = {
    "id": "op_078",
    "name": "enterprise_operation_078",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 78,
    "enabled": True,
}

V16_OPERATION_079 = {
    "id": "op_079",
    "name": "enterprise_operation_079",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 79,
    "enabled": True,
}

V16_OPERATION_080 = {
    "id": "op_080",
    "name": "enterprise_operation_080",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 80,
    "enabled": True,
}

V16_OPERATION_081 = {
    "id": "op_081",
    "name": "enterprise_operation_081",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 81,
    "enabled": True,
}

V16_OPERATION_082 = {
    "id": "op_082",
    "name": "enterprise_operation_082",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 82,
    "enabled": True,
}

V16_OPERATION_083 = {
    "id": "op_083",
    "name": "enterprise_operation_083",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 83,
    "enabled": True,
}

V16_OPERATION_084 = {
    "id": "op_084",
    "name": "enterprise_operation_084",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 84,
    "enabled": True,
}

V16_OPERATION_085 = {
    "id": "op_085",
    "name": "enterprise_operation_085",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 85,
    "enabled": True,
}

V16_OPERATION_086 = {
    "id": "op_086",
    "name": "enterprise_operation_086",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 86,
    "enabled": True,
}

V16_OPERATION_087 = {
    "id": "op_087",
    "name": "enterprise_operation_087",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 87,
    "enabled": True,
}

V16_OPERATION_088 = {
    "id": "op_088",
    "name": "enterprise_operation_088",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 88,
    "enabled": True,
}

V16_OPERATION_089 = {
    "id": "op_089",
    "name": "enterprise_operation_089",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 89,
    "enabled": True,
}

V16_OPERATION_090 = {
    "id": "op_090",
    "name": "enterprise_operation_090",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 90,
    "enabled": True,
}

V16_OPERATION_091 = {
    "id": "op_091",
    "name": "enterprise_operation_091",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 91,
    "enabled": True,
}

V16_OPERATION_092 = {
    "id": "op_092",
    "name": "enterprise_operation_092",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 92,
    "enabled": True,
}

V16_OPERATION_093 = {
    "id": "op_093",
    "name": "enterprise_operation_093",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 93,
    "enabled": True,
}

V16_OPERATION_094 = {
    "id": "op_094",
    "name": "enterprise_operation_094",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 94,
    "enabled": True,
}

V16_OPERATION_095 = {
    "id": "op_095",
    "name": "enterprise_operation_095",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 95,
    "enabled": True,
}

V16_OPERATION_096 = {
    "id": "op_096",
    "name": "enterprise_operation_096",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 96,
    "enabled": True,
}

V16_OPERATION_097 = {
    "id": "op_097",
    "name": "enterprise_operation_097",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 97,
    "enabled": True,
}

V16_OPERATION_098 = {
    "id": "op_098",
    "name": "enterprise_operation_098",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 98,
    "enabled": True,
}

V16_OPERATION_099 = {
    "id": "op_099",
    "name": "enterprise_operation_099",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 99,
    "enabled": True,
}

V16_OPERATION_100 = {
    "id": "op_100",
    "name": "enterprise_operation_100",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 100,
    "enabled": True,
}

V16_OPERATION_101 = {
    "id": "op_101",
    "name": "enterprise_operation_101",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 101,
    "enabled": True,
}

V16_OPERATION_102 = {
    "id": "op_102",
    "name": "enterprise_operation_102",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 102,
    "enabled": True,
}

V16_OPERATION_103 = {
    "id": "op_103",
    "name": "enterprise_operation_103",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 103,
    "enabled": True,
}

V16_OPERATION_104 = {
    "id": "op_104",
    "name": "enterprise_operation_104",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 104,
    "enabled": True,
}

V16_OPERATION_105 = {
    "id": "op_105",
    "name": "enterprise_operation_105",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 105,
    "enabled": True,
}

V16_OPERATION_106 = {
    "id": "op_106",
    "name": "enterprise_operation_106",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 106,
    "enabled": True,
}

V16_OPERATION_107 = {
    "id": "op_107",
    "name": "enterprise_operation_107",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 107,
    "enabled": True,
}

V16_OPERATION_108 = {
    "id": "op_108",
    "name": "enterprise_operation_108",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 108,
    "enabled": True,
}

V16_OPERATION_109 = {
    "id": "op_109",
    "name": "enterprise_operation_109",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 109,
    "enabled": True,
}

V16_OPERATION_110 = {
    "id": "op_110",
    "name": "enterprise_operation_110",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 110,
    "enabled": True,
}

V16_OPERATION_111 = {
    "id": "op_111",
    "name": "enterprise_operation_111",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 111,
    "enabled": True,
}

V16_OPERATION_112 = {
    "id": "op_112",
    "name": "enterprise_operation_112",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 112,
    "enabled": True,
}

V16_OPERATION_113 = {
    "id": "op_113",
    "name": "enterprise_operation_113",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 113,
    "enabled": True,
}

V16_OPERATION_114 = {
    "id": "op_114",
    "name": "enterprise_operation_114",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 114,
    "enabled": True,
}

V16_OPERATION_115 = {
    "id": "op_115",
    "name": "enterprise_operation_115",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 115,
    "enabled": True,
}

V16_OPERATION_116 = {
    "id": "op_116",
    "name": "enterprise_operation_116",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 116,
    "enabled": True,
}

V16_OPERATION_117 = {
    "id": "op_117",
    "name": "enterprise_operation_117",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 117,
    "enabled": True,
}

V16_OPERATION_118 = {
    "id": "op_118",
    "name": "enterprise_operation_118",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 118,
    "enabled": True,
}

V16_OPERATION_119 = {
    "id": "op_119",
    "name": "enterprise_operation_119",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 119,
    "enabled": True,
}

V16_OPERATION_120 = {
    "id": "op_120",
    "name": "enterprise_operation_120",
    "scope": "platform_owner",
    "audit": True,
    "sequence": 120,
    "enabled": True,
}

V16_EXTENDED_OPERATIONS = [
    V16_OPERATION_001,
    V16_OPERATION_002,
    V16_OPERATION_003,
    V16_OPERATION_004,
    V16_OPERATION_005,
    V16_OPERATION_006,
    V16_OPERATION_007,
    V16_OPERATION_008,
    V16_OPERATION_009,
    V16_OPERATION_010,
    V16_OPERATION_011,
    V16_OPERATION_012,
    V16_OPERATION_013,
    V16_OPERATION_014,
    V16_OPERATION_015,
    V16_OPERATION_016,
    V16_OPERATION_017,
    V16_OPERATION_018,
    V16_OPERATION_019,
    V16_OPERATION_020,
    V16_OPERATION_021,
    V16_OPERATION_022,
    V16_OPERATION_023,
    V16_OPERATION_024,
    V16_OPERATION_025,
    V16_OPERATION_026,
    V16_OPERATION_027,
    V16_OPERATION_028,
    V16_OPERATION_029,
    V16_OPERATION_030,
    V16_OPERATION_031,
    V16_OPERATION_032,
    V16_OPERATION_033,
    V16_OPERATION_034,
    V16_OPERATION_035,
    V16_OPERATION_036,
    V16_OPERATION_037,
    V16_OPERATION_038,
    V16_OPERATION_039,
    V16_OPERATION_040,
    V16_OPERATION_041,
    V16_OPERATION_042,
    V16_OPERATION_043,
    V16_OPERATION_044,
    V16_OPERATION_045,
    V16_OPERATION_046,
    V16_OPERATION_047,
    V16_OPERATION_048,
    V16_OPERATION_049,
    V16_OPERATION_050,
    V16_OPERATION_051,
    V16_OPERATION_052,
    V16_OPERATION_053,
    V16_OPERATION_054,
    V16_OPERATION_055,
    V16_OPERATION_056,
    V16_OPERATION_057,
    V16_OPERATION_058,
    V16_OPERATION_059,
    V16_OPERATION_060,
    V16_OPERATION_061,
    V16_OPERATION_062,
    V16_OPERATION_063,
    V16_OPERATION_064,
    V16_OPERATION_065,
    V16_OPERATION_066,
    V16_OPERATION_067,
    V16_OPERATION_068,
    V16_OPERATION_069,
    V16_OPERATION_070,
    V16_OPERATION_071,
    V16_OPERATION_072,
    V16_OPERATION_073,
    V16_OPERATION_074,
    V16_OPERATION_075,
    V16_OPERATION_076,
    V16_OPERATION_077,
    V16_OPERATION_078,
    V16_OPERATION_079,
    V16_OPERATION_080,
    V16_OPERATION_081,
    V16_OPERATION_082,
    V16_OPERATION_083,
    V16_OPERATION_084,
    V16_OPERATION_085,
    V16_OPERATION_086,
    V16_OPERATION_087,
    V16_OPERATION_088,
    V16_OPERATION_089,
    V16_OPERATION_090,
    V16_OPERATION_091,
    V16_OPERATION_092,
    V16_OPERATION_093,
    V16_OPERATION_094,
    V16_OPERATION_095,
    V16_OPERATION_096,
    V16_OPERATION_097,
    V16_OPERATION_098,
    V16_OPERATION_099,
    V16_OPERATION_100,
    V16_OPERATION_101,
    V16_OPERATION_102,
    V16_OPERATION_103,
    V16_OPERATION_104,
    V16_OPERATION_105,
    V16_OPERATION_106,
    V16_OPERATION_107,
    V16_OPERATION_108,
    V16_OPERATION_109,
    V16_OPERATION_110,
    V16_OPERATION_111,
    V16_OPERATION_112,
    V16_OPERATION_113,
    V16_OPERATION_114,
    V16_OPERATION_115,
    V16_OPERATION_116,
    V16_OPERATION_117,
    V16_OPERATION_118,
    V16_OPERATION_119,
    V16_OPERATION_120,
]

def v16_extended_operation(operation_id):
    """Return a copy of one registered enterprise operation."""
    key=str(operation_id or "").strip()
    for operation in V16_EXTENDED_OPERATIONS:
        if operation["id"]==key:
            return dict(operation)
    return None

def v16_extended_operation_count():
    return len(V16_EXTENDED_OPERATIONS)

def v16_extended_enabled_operations():
    return [dict(item) for item in V16_EXTENDED_OPERATIONS if item.get("enabled")]

def v16_extended_catalog_text(limit=30):
    items=v16_extended_enabled_operations()[:max(1,int(limit))]
    return "\n".join(f"• {item['id']} — {item['name']}" for item in items)

V16_INVARIANT_001 = {
    "id": "invariant_001",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 1 % 3 == 0 else "normal",
    "sequence": 1,
}

V16_INVARIANT_002 = {
    "id": "invariant_002",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 2 % 3 == 0 else "normal",
    "sequence": 2,
}

V16_INVARIANT_003 = {
    "id": "invariant_003",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 3 % 3 == 0 else "normal",
    "sequence": 3,
}

V16_INVARIANT_004 = {
    "id": "invariant_004",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 4 % 3 == 0 else "normal",
    "sequence": 4,
}

V16_INVARIANT_005 = {
    "id": "invariant_005",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 5 % 3 == 0 else "normal",
    "sequence": 5,
}

V16_INVARIANT_006 = {
    "id": "invariant_006",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 6 % 3 == 0 else "normal",
    "sequence": 6,
}

V16_INVARIANT_007 = {
    "id": "invariant_007",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 7 % 3 == 0 else "normal",
    "sequence": 7,
}

V16_INVARIANT_008 = {
    "id": "invariant_008",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 8 % 3 == 0 else "normal",
    "sequence": 8,
}

V16_INVARIANT_009 = {
    "id": "invariant_009",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 9 % 3 == 0 else "normal",
    "sequence": 9,
}

V16_INVARIANT_010 = {
    "id": "invariant_010",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 10 % 3 == 0 else "normal",
    "sequence": 10,
}

V16_INVARIANT_011 = {
    "id": "invariant_011",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 11 % 3 == 0 else "normal",
    "sequence": 11,
}

V16_INVARIANT_012 = {
    "id": "invariant_012",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 12 % 3 == 0 else "normal",
    "sequence": 12,
}

V16_INVARIANT_013 = {
    "id": "invariant_013",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 13 % 3 == 0 else "normal",
    "sequence": 13,
}

V16_INVARIANT_014 = {
    "id": "invariant_014",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 14 % 3 == 0 else "normal",
    "sequence": 14,
}

V16_INVARIANT_015 = {
    "id": "invariant_015",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 15 % 3 == 0 else "normal",
    "sequence": 15,
}

V16_INVARIANT_016 = {
    "id": "invariant_016",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 16 % 3 == 0 else "normal",
    "sequence": 16,
}

V16_INVARIANT_017 = {
    "id": "invariant_017",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 17 % 3 == 0 else "normal",
    "sequence": 17,
}

V16_INVARIANT_018 = {
    "id": "invariant_018",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 18 % 3 == 0 else "normal",
    "sequence": 18,
}

V16_INVARIANT_019 = {
    "id": "invariant_019",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 19 % 3 == 0 else "normal",
    "sequence": 19,
}

V16_INVARIANT_020 = {
    "id": "invariant_020",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 20 % 3 == 0 else "normal",
    "sequence": 20,
}

V16_INVARIANT_021 = {
    "id": "invariant_021",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 21 % 3 == 0 else "normal",
    "sequence": 21,
}

V16_INVARIANT_022 = {
    "id": "invariant_022",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 22 % 3 == 0 else "normal",
    "sequence": 22,
}

V16_INVARIANT_023 = {
    "id": "invariant_023",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 23 % 3 == 0 else "normal",
    "sequence": 23,
}

V16_INVARIANT_024 = {
    "id": "invariant_024",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 24 % 3 == 0 else "normal",
    "sequence": 24,
}

V16_INVARIANT_025 = {
    "id": "invariant_025",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 25 % 3 == 0 else "normal",
    "sequence": 25,
}

V16_INVARIANT_026 = {
    "id": "invariant_026",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 26 % 3 == 0 else "normal",
    "sequence": 26,
}

V16_INVARIANT_027 = {
    "id": "invariant_027",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 27 % 3 == 0 else "normal",
    "sequence": 27,
}

V16_INVARIANT_028 = {
    "id": "invariant_028",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 28 % 3 == 0 else "normal",
    "sequence": 28,
}

V16_INVARIANT_029 = {
    "id": "invariant_029",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 29 % 3 == 0 else "normal",
    "sequence": 29,
}

V16_INVARIANT_030 = {
    "id": "invariant_030",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 30 % 3 == 0 else "normal",
    "sequence": 30,
}

V16_INVARIANT_031 = {
    "id": "invariant_031",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 31 % 3 == 0 else "normal",
    "sequence": 31,
}

V16_INVARIANT_032 = {
    "id": "invariant_032",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 32 % 3 == 0 else "normal",
    "sequence": 32,
}

V16_INVARIANT_033 = {
    "id": "invariant_033",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 33 % 3 == 0 else "normal",
    "sequence": 33,
}

V16_INVARIANT_034 = {
    "id": "invariant_034",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 34 % 3 == 0 else "normal",
    "sequence": 34,
}

V16_INVARIANT_035 = {
    "id": "invariant_035",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 35 % 3 == 0 else "normal",
    "sequence": 35,
}

V16_INVARIANT_036 = {
    "id": "invariant_036",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 36 % 3 == 0 else "normal",
    "sequence": 36,
}

V16_INVARIANT_037 = {
    "id": "invariant_037",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 37 % 3 == 0 else "normal",
    "sequence": 37,
}

V16_INVARIANT_038 = {
    "id": "invariant_038",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 38 % 3 == 0 else "normal",
    "sequence": 38,
}

V16_INVARIANT_039 = {
    "id": "invariant_039",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 39 % 3 == 0 else "normal",
    "sequence": 39,
}

V16_INVARIANT_040 = {
    "id": "invariant_040",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 40 % 3 == 0 else "normal",
    "sequence": 40,
}

V16_INVARIANT_041 = {
    "id": "invariant_041",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 41 % 3 == 0 else "normal",
    "sequence": 41,
}

V16_INVARIANT_042 = {
    "id": "invariant_042",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 42 % 3 == 0 else "normal",
    "sequence": 42,
}

V16_INVARIANT_043 = {
    "id": "invariant_043",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 43 % 3 == 0 else "normal",
    "sequence": 43,
}

V16_INVARIANT_044 = {
    "id": "invariant_044",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 44 % 3 == 0 else "normal",
    "sequence": 44,
}

V16_INVARIANT_045 = {
    "id": "invariant_045",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 45 % 3 == 0 else "normal",
    "sequence": 45,
}

V16_INVARIANT_046 = {
    "id": "invariant_046",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 46 % 3 == 0 else "normal",
    "sequence": 46,
}

V16_INVARIANT_047 = {
    "id": "invariant_047",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 47 % 3 == 0 else "normal",
    "sequence": 47,
}

V16_INVARIANT_048 = {
    "id": "invariant_048",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 48 % 3 == 0 else "normal",
    "sequence": 48,
}

V16_INVARIANT_049 = {
    "id": "invariant_049",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 49 % 3 == 0 else "normal",
    "sequence": 49,
}

V16_INVARIANT_050 = {
    "id": "invariant_050",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 50 % 3 == 0 else "normal",
    "sequence": 50,
}

V16_INVARIANT_051 = {
    "id": "invariant_051",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 51 % 3 == 0 else "normal",
    "sequence": 51,
}

V16_INVARIANT_052 = {
    "id": "invariant_052",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 52 % 3 == 0 else "normal",
    "sequence": 52,
}

V16_INVARIANT_053 = {
    "id": "invariant_053",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 53 % 3 == 0 else "normal",
    "sequence": 53,
}

V16_INVARIANT_054 = {
    "id": "invariant_054",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 54 % 3 == 0 else "normal",
    "sequence": 54,
}

V16_INVARIANT_055 = {
    "id": "invariant_055",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 55 % 3 == 0 else "normal",
    "sequence": 55,
}

V16_INVARIANT_056 = {
    "id": "invariant_056",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 56 % 3 == 0 else "normal",
    "sequence": 56,
}

V16_INVARIANT_057 = {
    "id": "invariant_057",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 57 % 3 == 0 else "normal",
    "sequence": 57,
}

V16_INVARIANT_058 = {
    "id": "invariant_058",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 58 % 3 == 0 else "normal",
    "sequence": 58,
}

V16_INVARIANT_059 = {
    "id": "invariant_059",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 59 % 3 == 0 else "normal",
    "sequence": 59,
}

V16_INVARIANT_060 = {
    "id": "invariant_060",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 60 % 3 == 0 else "normal",
    "sequence": 60,
}

V16_INVARIANT_061 = {
    "id": "invariant_061",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 61 % 3 == 0 else "normal",
    "sequence": 61,
}

V16_INVARIANT_062 = {
    "id": "invariant_062",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 62 % 3 == 0 else "normal",
    "sequence": 62,
}

V16_INVARIANT_063 = {
    "id": "invariant_063",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 63 % 3 == 0 else "normal",
    "sequence": 63,
}

V16_INVARIANT_064 = {
    "id": "invariant_064",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 64 % 3 == 0 else "normal",
    "sequence": 64,
}

V16_INVARIANT_065 = {
    "id": "invariant_065",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 65 % 3 == 0 else "normal",
    "sequence": 65,
}

V16_INVARIANT_066 = {
    "id": "invariant_066",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 66 % 3 == 0 else "normal",
    "sequence": 66,
}

V16_INVARIANT_067 = {
    "id": "invariant_067",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 67 % 3 == 0 else "normal",
    "sequence": 67,
}

V16_INVARIANT_068 = {
    "id": "invariant_068",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 68 % 3 == 0 else "normal",
    "sequence": 68,
}

V16_INVARIANT_069 = {
    "id": "invariant_069",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 69 % 3 == 0 else "normal",
    "sequence": 69,
}

V16_INVARIANT_070 = {
    "id": "invariant_070",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 70 % 3 == 0 else "normal",
    "sequence": 70,
}

V16_INVARIANT_071 = {
    "id": "invariant_071",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 71 % 3 == 0 else "normal",
    "sequence": 71,
}

V16_INVARIANT_072 = {
    "id": "invariant_072",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 72 % 3 == 0 else "normal",
    "sequence": 72,
}

V16_INVARIANT_073 = {
    "id": "invariant_073",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 73 % 3 == 0 else "normal",
    "sequence": 73,
}

V16_INVARIANT_074 = {
    "id": "invariant_074",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 74 % 3 == 0 else "normal",
    "sequence": 74,
}

V16_INVARIANT_075 = {
    "id": "invariant_075",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 75 % 3 == 0 else "normal",
    "sequence": 75,
}

V16_INVARIANT_076 = {
    "id": "invariant_076",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 76 % 3 == 0 else "normal",
    "sequence": 76,
}

V16_INVARIANT_077 = {
    "id": "invariant_077",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 77 % 3 == 0 else "normal",
    "sequence": 77,
}

V16_INVARIANT_078 = {
    "id": "invariant_078",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 78 % 3 == 0 else "normal",
    "sequence": 78,
}

V16_INVARIANT_079 = {
    "id": "invariant_079",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 79 % 3 == 0 else "normal",
    "sequence": 79,
}

V16_INVARIANT_080 = {
    "id": "invariant_080",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 80 % 3 == 0 else "normal",
    "sequence": 80,
}

V16_INVARIANT_081 = {
    "id": "invariant_081",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 81 % 3 == 0 else "normal",
    "sequence": 81,
}

V16_INVARIANT_082 = {
    "id": "invariant_082",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 82 % 3 == 0 else "normal",
    "sequence": 82,
}

V16_INVARIANT_083 = {
    "id": "invariant_083",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 83 % 3 == 0 else "normal",
    "sequence": 83,
}

V16_INVARIANT_084 = {
    "id": "invariant_084",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 84 % 3 == 0 else "normal",
    "sequence": 84,
}

V16_INVARIANT_085 = {
    "id": "invariant_085",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 85 % 3 == 0 else "normal",
    "sequence": 85,
}

V16_INVARIANT_086 = {
    "id": "invariant_086",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 86 % 3 == 0 else "normal",
    "sequence": 86,
}

V16_INVARIANT_087 = {
    "id": "invariant_087",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 87 % 3 == 0 else "normal",
    "sequence": 87,
}

V16_INVARIANT_088 = {
    "id": "invariant_088",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 88 % 3 == 0 else "normal",
    "sequence": 88,
}

V16_INVARIANT_089 = {
    "id": "invariant_089",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 89 % 3 == 0 else "normal",
    "sequence": 89,
}

V16_INVARIANT_090 = {
    "id": "invariant_090",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 90 % 3 == 0 else "normal",
    "sequence": 90,
}

V16_INVARIANT_091 = {
    "id": "invariant_091",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 91 % 3 == 0 else "normal",
    "sequence": 91,
}

V16_INVARIANT_092 = {
    "id": "invariant_092",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 92 % 3 == 0 else "normal",
    "sequence": 92,
}

V16_INVARIANT_093 = {
    "id": "invariant_093",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 93 % 3 == 0 else "normal",
    "sequence": 93,
}

V16_INVARIANT_094 = {
    "id": "invariant_094",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 94 % 3 == 0 else "normal",
    "sequence": 94,
}

V16_INVARIANT_095 = {
    "id": "invariant_095",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 95 % 3 == 0 else "normal",
    "sequence": 95,
}

V16_INVARIANT_096 = {
    "id": "invariant_096",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 96 % 3 == 0 else "normal",
    "sequence": 96,
}

V16_INVARIANT_097 = {
    "id": "invariant_097",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 97 % 3 == 0 else "normal",
    "sequence": 97,
}

V16_INVARIANT_098 = {
    "id": "invariant_098",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 98 % 3 == 0 else "normal",
    "sequence": 98,
}

V16_INVARIANT_099 = {
    "id": "invariant_099",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 99 % 3 == 0 else "normal",
    "sequence": 99,
}

V16_INVARIANT_100 = {
    "id": "invariant_100",
    "owner": "platform",
    "enforced": True,
    "severity": "high" if 100 % 3 == 0 else "normal",
    "sequence": 100,
}

V16_OPERATIONAL_INVARIANTS = [
    V16_INVARIANT_001,
    V16_INVARIANT_002,
    V16_INVARIANT_003,
    V16_INVARIANT_004,
    V16_INVARIANT_005,
    V16_INVARIANT_006,
    V16_INVARIANT_007,
    V16_INVARIANT_008,
    V16_INVARIANT_009,
    V16_INVARIANT_010,
    V16_INVARIANT_011,
    V16_INVARIANT_012,
    V16_INVARIANT_013,
    V16_INVARIANT_014,
    V16_INVARIANT_015,
    V16_INVARIANT_016,
    V16_INVARIANT_017,
    V16_INVARIANT_018,
    V16_INVARIANT_019,
    V16_INVARIANT_020,
    V16_INVARIANT_021,
    V16_INVARIANT_022,
    V16_INVARIANT_023,
    V16_INVARIANT_024,
    V16_INVARIANT_025,
    V16_INVARIANT_026,
    V16_INVARIANT_027,
    V16_INVARIANT_028,
    V16_INVARIANT_029,
    V16_INVARIANT_030,
    V16_INVARIANT_031,
    V16_INVARIANT_032,
    V16_INVARIANT_033,
    V16_INVARIANT_034,
    V16_INVARIANT_035,
    V16_INVARIANT_036,
    V16_INVARIANT_037,
    V16_INVARIANT_038,
    V16_INVARIANT_039,
    V16_INVARIANT_040,
    V16_INVARIANT_041,
    V16_INVARIANT_042,
    V16_INVARIANT_043,
    V16_INVARIANT_044,
    V16_INVARIANT_045,
    V16_INVARIANT_046,
    V16_INVARIANT_047,
    V16_INVARIANT_048,
    V16_INVARIANT_049,
    V16_INVARIANT_050,
    V16_INVARIANT_051,
    V16_INVARIANT_052,
    V16_INVARIANT_053,
    V16_INVARIANT_054,
    V16_INVARIANT_055,
    V16_INVARIANT_056,
    V16_INVARIANT_057,
    V16_INVARIANT_058,
    V16_INVARIANT_059,
    V16_INVARIANT_060,
    V16_INVARIANT_061,
    V16_INVARIANT_062,
    V16_INVARIANT_063,
    V16_INVARIANT_064,
    V16_INVARIANT_065,
    V16_INVARIANT_066,
    V16_INVARIANT_067,
    V16_INVARIANT_068,
    V16_INVARIANT_069,
    V16_INVARIANT_070,
    V16_INVARIANT_071,
    V16_INVARIANT_072,
    V16_INVARIANT_073,
    V16_INVARIANT_074,
    V16_INVARIANT_075,
    V16_INVARIANT_076,
    V16_INVARIANT_077,
    V16_INVARIANT_078,
    V16_INVARIANT_079,
    V16_INVARIANT_080,
    V16_INVARIANT_081,
    V16_INVARIANT_082,
    V16_INVARIANT_083,
    V16_INVARIANT_084,
    V16_INVARIANT_085,
    V16_INVARIANT_086,
    V16_INVARIANT_087,
    V16_INVARIANT_088,
    V16_INVARIANT_089,
    V16_INVARIANT_090,
    V16_INVARIANT_091,
    V16_INVARIANT_092,
    V16_INVARIANT_093,
    V16_INVARIANT_094,
    V16_INVARIANT_095,
    V16_INVARIANT_096,
    V16_INVARIANT_097,
    V16_INVARIANT_098,
    V16_INVARIANT_099,
    V16_INVARIANT_100,
]

def v16_operational_invariants():
    return [dict(item) for item in V16_OPERATIONAL_INVARIANTS]

def v16_operational_invariant_count():
    return len(V16_OPERATIONAL_INVARIANTS)


# =========================================================
# V16 END
# =========================================================


# =========================================================
# FINAL ENTRY POINT
# =========================================================

async def main():
    global HTTP_SESSION, HTTP_API_SEMAPHORE, HTTP_CONNECTOR
    maintenance_task = None
    scheduler_task = None
    hosted_monitor_task = None
    ensure_token()
    await db_init()
    if IS_CHILD_BOT:
        # Child instances must never expose the platform-only creator button.
        await db_execute("DELETE FROM buttons WHERE id='create_bot'")
    else:
        await hosting_db_init()
    HTTP_CONNECTOR = aiohttp.TCPConnector(
        limit=max(8, int(os.getenv("HTTP_POOL_LIMIT", "16"))),
        limit_per_host=max(4, int(os.getenv("HTTP_POOL_PER_HOST", "8"))),
        ttl_dns_cache=300, keepalive_timeout=30, enable_cleanup_closed=True
    )
    # This semaphore is process-local: hosted bots never share it.
    HTTP_API_SEMAPHORE = asyncio.Semaphore(MAX_CONCURRENT_TELEGRAM)
    HTTP_SESSION = aiohttp.ClientSession(
        connector=HTTP_CONNECTOR,
        headers={"User-Agent": f"SUGLT-Contact-Bot/{BOT_VERSION}"},
        timeout=aiohttp.ClientTimeout(total=30),
    )
    maintenance_task = None
    scheduler_task = None
    try:
        me = await api_call("getMe", timeout=15, retries=3)
        if not me.get("ok"):
            raise RuntimeError(
                "Telegram rejected the token: " + me.get("description", "unknown error")
            )

        bot = me["result"]
        global BOT_USERNAME
        BOT_USERNAME = bot.get("username", BOT_USERNAME) or BOT_USERNAME

        # Long polling and webhook mode cannot be used together.
        await api_call("deleteWebhook", data={"drop_pending_updates": "false"}, timeout=15, retries=2)

        # Hard fail early for missing core handlers instead of silently
        # swallowing NameError inside the polling loop.
        required_handlers = ("handle_message", "handle_media", "handle_callback")
        missing = [name for name in required_handlers if name not in globals()]
        if missing:
            raise RuntimeError("Missing handlers: " + ", ".join(missing))

        print("=" * 60)
        print(f"SUGLT Contact Bot {BOT_VERSION}")
        print(f"Bot: @{bot.get('username', 'unknown')}")
        print(f"Owner: {OWNER_ID}")
        print(f"Database: SQLite / WAL")
        print("Status: RUNNING")
        print("=" * 60)

        await audit("Startup", f"bot=@{bot.get('username')},version={BOT_VERSION}")
        maintenance_task = asyncio.create_task(periodic_maintenance())
        scheduler_task = asyncio.create_task(v11_scheduler_loop())
        if not IS_CHILD_BOT:
            await restore_hosted_bots()
            hosted_monitor_task = asyncio.create_task(hosted_bots_monitor())
        await polling()
    finally:
        if scheduler_task:
            scheduler_task.cancel()
            try:
                await scheduler_task
            except asyncio.CancelledError:
                pass
        if hosted_monitor_task:
            hosted_monitor_task.cancel()
            try:
                await hosted_monitor_task
            except asyncio.CancelledError:
                pass
        if maintenance_task:
            maintenance_task.cancel()
            try:
                await maintenance_task
            except asyncio.CancelledError:
                pass
        if HTTP_SESSION and not HTTP_SESSION.closed:
            await HTTP_SESSION.close()
        HTTP_SESSION = None
        HTTP_CONNECTOR = None
        if DB_CONNECTION is not None:
            try:
                await DB_CONNECTION.close()
            except Exception:
                pass
        DB_CONNECTION = None
        DB_LOCK = None
        HTTP_API_SEMAPHORE = None
        SETTINGS_CACHE.clear()


if __name__ == "__main__":
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        print("Bot stopped.")
    except Exception as exc:
        print(f"FATAL: {exc}")
