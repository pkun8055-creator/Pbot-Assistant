from __future__ import annotations

import asyncio
import base64
import io
import json
import os
import sqlite3
import time
from contextlib import closing
from datetime import datetime, timedelta, timezone
from functools import lru_cache
from pathlib import Path
from typing import Any, Optional
from urllib.parse import quote

import aiohttp
import discord
from discord import app_commands
from discord.ext import commands
from PIL import Image, ImageDraw, ImageFilter, ImageFont

HIVE_API = "https://api.playhive.com/v0"
PATH_ALL = "/game/all/all/{name}"
PATH_MAIN = "/game/all/main/{name}"
PATH_MONTHLY_PLAYER = "/game/monthly/player/{game}/{name}"
PATH_MONTHLY_PLAYER_YM = "/game/monthly/player/{game}/{name}/{year}/{month}"
PATH_META = "/game/meta/{game}"
PATH_LB_ALL = "/game/all/{game}"
PATH_LB_MONTHLY = "/game/monthly/{game}"
PATH_MAPS = "/game/map/{game}"
PATH_GLOBAL = "/global/statistics"
PATH_SEARCH = "/player/search/{query}"

JST = timezone(timedelta(hours=9))
CACHE_SEC = 1800
META_CACHE_SEC = 86400
SEARCH_CACHE_SEC = 300
DB_PATH = "hive_cache.db"
USER_AGENT = "HiveStatsBot/3.0 (Discord bot; discord.py)"

# ---------- フォント（PixelMplus: 日本語も英数字も1つのドットフォント） ----------
# fonts/ に PixelMplus12-Bold.ttf と PixelMplus12-Regular.ttf を置く（配布zipに入っているもの）
FONT_DIR = Path("fonts")
PIXEL_FONT_FILE = FONT_DIR / "PixelMplus12-Bold.ttf"
PIXEL_FONT_REGULAR = FONT_DIR / "PixelMplus12-Regular.ttf"  # Wだけ通常版で補う
# 12pxフォントの整数倍（12 / 24 / 36）だけを使うと、ドットがにじまず綺麗に出る
PIXEL_SIZES = (12, 24, 36)
# PixelMplus が無いときの代替（自動ダウンロード）
FONT_FALLBACK_PATH = FONT_DIR / "DotGothic16-Regular.ttf"
FONT_FALLBACK_URL = "https://raw.githubusercontent.com/google/fonts/main/ofl/dotgothic16/DotGothic16-Regular.ttf"

_blocked: dict[str, float] = {}
_last_use: dict[int, float] = {}
_DEFAULT_MAP: Optional[bytes] = None  # 通知カードなど、マップ画像が手元にないカード用の共通背景
_assets_task: Optional[asyncio.Task] = None


# ---------- プレステージアイコン（コインI〜V / 22x20 ドット絵を埋め込み） ----------
PRESTIGE_ICONS_B64 = [
    "iVBORw0KGgoAAAANSUhEUgAAABYAAAAUCAYAAACJfM0wAAAAkElEQVR42mNkwAT/GcgDjMgcJgYaAUZ0l15+8JiBgYGBQVtOmiSDmJiYUMykmYtZYC5dtuMIikuvPnpKlAEw9f/+/YO5/D/NXYwCcLl0557zDAwMDAzuLoZY1aPHCc1cPGrwqMFEpOPLNx4yMDAwMOhqyKOIo6df9JyHnv7pV7rBygxSQZSHDX1KN8YhV4MAABnkJAcTvOdlAAAAAElFTkSuQmCC",
    "iVBORw0KGgoAAAANSUhEUgAAABYAAAAUCAYAAACJfM0wAAAAfUlEQVR42mNkwAT/GcgDjMgcJgYaAUZ0l/75DLWR+x9JBjExMaGYSTMXs8Bc+mMFqkv/fSXOTrj6f/9gLv9PcxejAHSXvumG0CKl2Pkw9ehxQjMXjxo8ajD2sgIl58ETuDcDaTnvC8SNLHz0Lt3QXU4s4IhgoE/pxjjkahAAxrMixUKbc5MAAAAASUVORK5CYII=",
    "iVBORw0KGgoAAAANSUhEUgAAABYAAAAUCAYAAACJfM0wAAAAo0lEQVR42mOUWfyRARk8ieX/z0AG+P//PyMyn4mBRoAF3aWBjRsYGBgYGNbW+pFkECMj439kl9PMxYwMDAxYXZq15QxRBkzzMUHhMzEx0SmMYQDm0lN7HjMwMDAwmLnI4uVn4XI5rVw8avCowUSk45fnn6GkVxjAxYelX/ScSruy4jGUIYtWZpAK1tcHMDAwMDA8hpQ/dHAxA5rLSQUwl9I8jAGvlTNsGwcRiAAAAABJRU5ErkJggg==",
    "iVBORw0KGgoAAAANSUhEUgAAABYAAAAUCAYAAACJfM0wAAAAsUlEQVR42mOUWfyRARk8ieX/z0AG+P//PyMyn4mBRoAF3aXl/+UYGBgYGFr/rSbJIEZGxv/ILqeZixkZGBj+MzAwMKgfNWFgYGBguGoxlYGBgYGhmimUKAPQfcbCbE6nMIYBmEu7ZooxMDAwMJSlv8LLZ0gPxepymrl41GA65jxCAFfqoLuLMXIeDARYvSIp58HSfyfjI9q7GF6kYnM5seCm9RkUM+niYhSXU2oWzVwMAOiYNPKIp3IvAAAAAElFTkSuQmCC",
    "iVBORw0KGgoAAAANSUhEUgAAABYAAAAUCAYAAACJfM0wAAAAsklEQVR42u2VQQrCMBBF31RrRXDTK7kSL+BeT9AzuPYEuvcG3qobQbSFjpsEmthCFBI3/t2E8Hlk5meEdylfSFWlX2dE0tQnvZUNAEWVt+Z8EgIhItonj0qsAJfyakkfAM9jOw8xKKocgOagDnmSN2aI9Lw4dQC7+z4zNaa29x3y6FPxN06bvEGNTcPPiMVPntWGFZ8kz87zsp7FJ3Z+N588VNt67XgmIR7bIF1go9NskBcWFjVbJTJBGgAAAABJRU5ErkJggg=="
]


# ---------- 永続データベース ----------
class HiveRateLimited(Exception):
    def __init__(self, wait: int):
        super().__init__(f"rate limited: {wait}s")
        self.wait = wait


def _db_init():
    with closing(sqlite3.connect(DB_PATH)) as con:
        con.execute(
            "CREATE TABLE IF NOT EXISTS cache "
            "(path TEXT PRIMARY KEY, ts REAL, body TEXT)"
        )
        con.execute(
            "CREATE TABLE IF NOT EXISTS user_links "
            "(discord_id INTEGER PRIMARY KEY, gamertag TEXT, updated_at REAL)"
        )
        con.execute(
            "CREATE TABLE IF NOT EXISTS snapshots "
            "(snap_key TEXT PRIMARY KEY, ts REAL, body TEXT)"
        )
        con.commit()


def db_load(key: str) -> Optional[tuple[float, Any]]:
    _db_init()
    with closing(sqlite3.connect(DB_PATH)) as con:
        row = con.execute(
            "SELECT ts, body FROM cache WHERE path=?", (key,)
        ).fetchone()
    return (row[0], json.loads(row[1])) if row else None


def db_save(key: str, ts: float, data: Any):
    _db_init()
    with closing(sqlite3.connect(DB_PATH)) as con:
        con.execute(
            "INSERT OR REPLACE INTO cache VALUES (?,?,?)",
            (key, ts, json.dumps(data)),
        )
        con.commit()


def link_get(discord_id: int) -> Optional[str]:
    _db_init()
    with closing(sqlite3.connect(DB_PATH)) as con:
        row = con.execute(
            "SELECT gamertag FROM user_links WHERE discord_id=?", (discord_id,)
        ).fetchone()
    return row[0] if row else None


def link_set(discord_id: int, gamertag: str):
    _db_init()
    with closing(sqlite3.connect(DB_PATH)) as con:
        con.execute(
            "INSERT OR REPLACE INTO user_links VALUES (?,?,?)",
            (discord_id, gamertag, time.time()),
        )
        con.commit()


def link_delete(discord_id: int):
    _db_init()
    with closing(sqlite3.connect(DB_PATH)) as con:
        con.execute("DELETE FROM user_links WHERE discord_id=?", (discord_id,))
        con.commit()


def update_snapshot_diff(
    gamertag: str, game_id: str, period: str, current: dict[str, Any]
) -> Optional[dict[str, int]]:
    if period != "all":
        return None
    _db_init()
    key = f"{gamertag.lower()}::{game_id}"
    with closing(sqlite3.connect(DB_PATH)) as con:
        row = con.execute(
            "SELECT ts, body FROM snapshots WHERE snap_key=?", (key,)
        ).fetchone()
        prev = json.loads(row[1]) if row else None
        con.execute(
            "INSERT OR REPLACE INTO snapshots VALUES (?,?,?)",
            (key, time.time(), json.dumps(current)),
        )
        con.commit()
    if not prev:
        return None
    diff: dict[str, int] = {}
    for k in ("played", "victories", "kills", "deaths", "final_kills", "beds_destroyed", "xp"):
        cur_v = current.get(k)
        prev_v = prev.get(k)
        if isinstance(cur_v, int) and isinstance(prev_v, int) and cur_v > prev_v:
            diff[k] = cur_v - prev_v
    return diff or None


async def hive_get(
    session: aiohttp.ClientSession, path: str, ttl: int = CACHE_SEC
) -> Any:
    key = path.lower()
    now = time.time()
    saved = db_load(key)
    if saved and now - saved[0] < ttl:
        return saved[1]
    until = _blocked.get(key, 0)
    if now < until:
        if saved:
            return saved[1]
        raise HiveRateLimited(int(until - now))
    async with session.get(
        HIVE_API + path, timeout=aiohttp.ClientTimeout(total=12)
    ) as r:
        if r.status == 429:
            wait = int(r.headers.get("Retry-After", "60"))
            reset = r.headers.get("x-ratelimit-reset")
            _blocked[key] = float(reset) if reset else now + wait
            if saved:
                return saved[1]
            raise HiveRateLimited(wait)
        if r.status in (404, 422):
            return None
        r.raise_for_status()
        data = await r.json()
    db_save(key, now, data)
    return data


async def fetch_image_bytes(session: aiohttp.ClientSession, url: Optional[str]) -> Optional[bytes]:
    if not url:
        return None
    cache_key = f"img::{url}"
    saved = db_load(cache_key)
    if saved and time.time() - saved[0] < META_CACHE_SEC:
        return bytes.fromhex(saved[1])
    try:
        async with session.get(url, timeout=aiohttp.ClientTimeout(total=6)) as r:
            if r.status == 200:
                raw = await r.read()
                db_save(cache_key, time.time(), raw.hex())
                return raw
    except Exception:
        pass
    return None


async def _download_font(session: aiohttp.ClientSession, path: Path, url: str):
    if path.exists() and path.stat().st_size > 10_000:
        return
    try:
        async with session.get(url, timeout=aiohttp.ClientTimeout(total=30)) as r:
            if r.status == 200:
                path.write_bytes(await r.read())
    except Exception:
        pass


async def ensure_fonts():
    FONT_DIR.mkdir(parents=True, exist_ok=True)
    if not PIXEL_FONT_FILE.exists():
        print("[hive] fonts/PixelMplus12-Bold.ttf が見つからないため、代替フォントを使います")
        async with aiohttp.ClientSession(headers={"User-Agent": USER_AGENT}) as session:
            await _download_font(session, FONT_FALLBACK_PATH, FONT_FALLBACK_URL)
    _load_font.cache_clear()


async def ensure_default_map():
    """通知カードなど、マップ画像を持たないカードの背景用にSkyWarsのマップを1枚確保する。"""
    global _DEFAULT_MAP
    try:
        async with aiohttp.ClientSession(headers={"User-Agent": USER_AGENT}) as session:
            maps = await hive_get(session, PATH_MAPS.format(game="sky"), ttl=META_CACHE_SEC)
            url = maps[0].get("image") if isinstance(maps, list) and maps else None
            _DEFAULT_MAP = await fetch_image_bytes(session, url)
    except Exception:
        pass


async def _prepare_assets():
    await ensure_fonts()
    await ensure_default_map()


async def wait_assets():
    if _assets_task is not None:
        try:
            await asyncio.shield(_assets_task)
        except Exception:
            pass


async def get_bg_map_bytes(session: aiohttp.ClientSession, meta_key: Optional[str]) -> Optional[bytes]:
    """ゲームのマップ画像を背景用に取得（失敗してもNoneを返すだけ）。"""
    try:
        maps_list = await hive_get(
            session, PATH_MAPS.format(game=quote(meta_key or "sky", safe="")), ttl=META_CACHE_SEC
        )
        url = maps_list[0].get("image") if isinstance(maps_list, list) and maps_list else None
        return await fetch_image_bytes(session, url)
    except Exception:
        return None


# ---------- ゲーム定義 & ラベル ----------
GAMES: dict[str, dict[str, Any]] = {
    "sky": {"name": "SkyWars", "en": "SkyWars", "accent": (56, 189, 248), "meta": "sky"},
    "bed": {"name": "BedWars", "en": "BedWars", "accent": (244, 63, 94), "meta": "bed"},
    "wars": {"name": "Treasure Wars", "en": "Treasure Wars", "accent": (245, 158, 11), "meta": "wars"},
    "murder": {"name": "Murder Mystery", "en": "Murder Mystery", "accent": (239, 68, 68), "meta": "murder"},
    "hide": {"name": "Hide and Seek", "en": "Hide and Seek", "accent": (168, 85, 247), "meta": "hide"},
    "sg": {"name": "Survival Games", "en": "Survival Games", "accent": (34, 197, 94), "meta": "sg"},
    "dr": {"name": "DeathRun", "en": "DeathRun", "accent": (234, 179, 8), "meta": "dr"},
    "ctf": {"name": "Capture the Flag", "en": "Capture the Flag", "accent": (59, 130, 246), "meta": "ctf"},
    "bridge": {"name": "The Bridge", "en": "The Bridge", "accent": (249, 115, 22), "meta": "bridge"},
    "drop": {"name": "Block Drop", "en": "Block Drop", "accent": (14, 165, 233), "meta": "drop"},
    "ground": {"name": "Ground Wars", "en": "Ground Wars", "accent": (132, 204, 22), "meta": "ground"},
    "build": {"name": "Just Build", "en": "Just Build", "accent": (236, 72, 153), "meta": "build"},
    "party": {"name": "Block Party", "en": "Block Party", "accent": (217, 70, 239), "meta": "party"},
    "grav": {"name": "Gravity", "en": "Gravity", "accent": (99, 102, 241), "meta": "grav"},
    "sky-classic": {"name": "SkyWars Classic", "en": "SkyWars Classic", "accent": (56, 189, 248), "meta": "sky"},
    "sky-kits": {"name": "SkyWars Kits", "en": "SkyWars Kits", "accent": (56, 189, 248), "meta": "sky"},
    "parkour": {"name": "Parkour", "en": "Parkour", "accent": (20, 184, 166), "meta": None},
}

STAT_LABELS: dict[str, str] = {
    "xp": "XP",
    "uncapped_xp": "Uncapped XP",
    "prestige": "Prestige",
    "played": "Games Played",
    "victories": "Wins",
    "kills": "Kills",
    "deaths": "Deaths",
    "assists": "Assists",
    "final_kills": "Final Kills",
    "final_deaths": "Final Deaths",
    "mystery_chests_destroyed": "Mystery Chests",
    "ores_mined": "Ores Mined",
    "spells_used": "Spells Used",
    "selected_kit": "Selected Kit",
    "beds_destroyed": "Beds Destroyed",
    "treasure_destroyed": "Treasures Destroyed",
    "flags_captured": "Flags Captured",
    "flags_returned": "Flags Returned",
    "teams_eliminated": "Teams Eliminated",
    "coins": "Coins",
    "murders": "Murders",
    "murderer_eliminations": "Murderer Eliminations",
    "bux": "Bux",
    "hider_kills": "Hider Kills",
    "seeker_kills": "Seeker Kills",
    "taunts": "Taunts",
    "crates": "Crates",
    "deathmatches": "Deathmatches",
    "cows": "Cows",
    "teleporters_used": "Teleporters Used",
    "launchpads_used": "Launchpads Used",
    "flares_used": "Flares Used",
    "checkpoints": "Checkpoints",
    "activated": "Traps Activated",
    "blocks_destroyed": "Blocks Destroyed",
    "blocks_placed": "Blocks Placed",
    "powerups_collected": "Powerups Collected",
    "vaults_used": "Vaults Used",
    "projectiles_fired": "Projectiles Fired",
    "goals": "Goals",
    "rounds_survived": "Rounds Survived",
    "maps_completed": "Maps Completed",
    "maps_completed_without_dying": "Flawless Maps",
    "rating_love_received": "Love Ratings",
    "rating_great_received": "Great Ratings",
    "rating_good_received": "Good Ratings",
    "rating_okay_received": "Okay Ratings",
    "rating_meh_received": "Meh Ratings",
}

RANK_TAGS: dict[str, tuple[str, tuple[int, int, int]]] = {
    "OWNER": ("OWNER", (239, 68, 68)),
    "STAFF": ("STAFF", (239, 68, 68)),
    "MODERATOR": ("MOD", (249, 115, 22)),
    "HELPER": ("HELPER", (59, 130, 246)),
    "PARTNER": ("PARTNER", (168, 85, 247)),
    "YOUTUBER": ("YT", (239, 68, 68)),
    "HIVE": ("HIVE", (245, 158, 11)),
    "ULTIMATE": ("U", (216, 180, 254)),
    "PLUS": ("+", (56, 189, 248)),
}
RANK_HIDDEN = {"REGULAR", "DEFAULT", "PLAYER", "MEMBER", ""}

SKIP_KEYS = {"UUID", "first_played", "index", "human_index", "username"}
GREEN, RED, AMBER = (74, 222, 128), (248, 113, 113), (251, 191, 36)
SKY = (96, 165, 250)
PRESTIGE_COL = (232, 121, 249)
GOLD = (250, 204, 21)


def pick(d: Any, *names: str, default: Any = 0) -> Any:
    if isinstance(d, dict):
        for n in names:
            if d.get(n) is not None:
                return d[n]
    return default


def rank_tag(raw: Any) -> Optional[tuple[str, tuple[int, int, int]]]:
    if isinstance(raw, dict):
        raw = pick(raw, "name", "rank", "id", default="")
    text = str(raw or "").strip()
    if not text:
        return None
    key = text.upper().replace(" ", "_")
    if key in RANK_HIDDEN:
        return None
    return RANK_TAGS.get(key, (text.upper(), (148, 163, 184)))


def ratio(a: float, b: float) -> float:
    return a / b if b else float(a)


def fmt_num(v: Any) -> str:
    if isinstance(v, bool):
        return str(v)
    if isinstance(v, float):
        return f"{v:,.2f}".rstrip("0").rstrip(".")
    if isinstance(v, int):
        return f"{v:,}"
    return str(v)


def fmt_date(ts: Any) -> str:
    if not ts:
        return "記録なし"
    dt = datetime.fromtimestamp(int(ts), tz=timezone.utc).astimezone(JST)
    return dt.strftime("%Y年%m月%d日 %H:%M")


def prev_year_month() -> tuple[int, int, str]:
    now = datetime.now(JST)
    first_of_this_month = now.replace(day=1)
    last_month = first_of_this_month - timedelta(days=1)
    return last_month.year, last_month.month, f"{last_month.year}/{last_month.month:02d}"


def compute_level(
    xp: int, meta: Optional[dict[str, Any]], prestige: Optional[int] = None
) -> Optional[dict[str, Any]]:
    if not meta or "experienceToLevel" not in meta:
        return None
    table = sorted((int(req_xp), int(lv)) for req_xp, lv in meta["experienceToLevel"].items())
    if not table:
        return None
    max_lv = int(meta.get("maxLevel", table[-1][1]))
    max_req_xp = table[-1][0]
    allow_prestige = bool(meta.get("allowPrestiging")) and prestige is not None
    max_prestige = int(meta.get("maxPrestige", 0)) if allow_prestige else 0
    cur_prestige = int(prestige) if prestige is not None else 0

    cur_lv = 1
    cur_floor = 0
    next_floor = table[1][0] if len(table) > 1 else 150
    for i, (req_xp, lv) in enumerate(table):
        if xp >= req_xp:
            cur_lv = lv
            cur_floor = req_xp
            next_floor = table[i + 1][0] if i + 1 < len(table) else req_xp
        else:
            break
    is_max_lv = cur_lv >= max_lv
    in_lv = max(0, xp - cur_floor)
    need = max(1, next_floor - cur_floor) if not is_max_lv else 1
    can_prestige = allow_prestige and is_max_lv and cur_prestige < max_prestige
    is_true_max = (is_max_lv and cur_prestige >= max_prestige) if allow_prestige else is_max_lv
    total_xp = (cur_prestige * max_req_xp + xp) if allow_prestige else xp
    return {
        "level": cur_lv,
        "in_lv": in_lv,
        "need": need,
        "max_lv": max_lv,
        "is_max_lv": is_max_lv,
        "allow_prestige": allow_prestige,
        "prestige": cur_prestige,
        "max_prestige": max_prestige,
        "can_prestige": can_prestige,
        "is_true_max": is_true_max,
        "total_xp": total_xp,
    }


def _num(v: Any) -> bool:
    return isinstance(v, (int, float)) and not isinstance(v, bool)


def build_stat_items(
    s: dict[str, Any], meta: Optional[dict[str, Any]] = None
) -> list[tuple[str, str, tuple[int, int, int], str]]:
    out: list[tuple[str, str, tuple[int, int, int], str]] = []
    played = s.get("played")
    wins = s.get("victories")
    kills = s.get("kills")
    deaths = s.get("deaths")
    fkills = s.get("final_kills")
    fdeaths = s.get("final_deaths")

    if _num(wins):
        out.append(("Wins", fmt_num(wins), GREEN, "trophy"))
    if _num(wins) and _num(played):
        losses = max(played - wins, 0)
        out.append(("Losses", fmt_num(losses), RED, "none"))
        if played > 0:
            out.append(("Win Rate", f"{wins / played * 100:.2f}%", AMBER, "none"))
    if _num(played):
        out.append(("Games Played", fmt_num(played), SKY, "none"))

    if _num(kills):
        out.append(("Kills", fmt_num(kills), GREEN, "sword"))
    if _num(deaths):
        out.append(("Deaths", fmt_num(deaths), RED, "skull"))
    if _num(kills) and _num(deaths):
        out.append(("KDR", fmt_num(round(ratio(kills, deaths), 2)), AMBER, "none"))
    if _num(fkills):
        out.append(("Final Kills", fmt_num(fkills), (167, 243, 208), "none"))
    if _num(fkills) and (_num(fdeaths) or (_num(wins) and _num(played))):
        denom = fdeaths if _num(fdeaths) else max(played - wins, 0)
        out.append(("FKLR", fmt_num(round(ratio(fkills, denom), 2)), (125, 211, 252), "none"))

    done = {
        "played", "victories", "kills", "deaths",
        "final_kills", "final_deaths", "xp", "prestige",
    } | SKIP_KEYS

    extra_palette = [
        (244, 180, 120), (125, 211, 252), (216, 180, 254),
        (163, 230, 53), (249, 168, 212), (94, 234, 212),
    ]
    idx = 0
    for k, v in s.items():
        if k in done:
            continue
        if not (_num(v) or isinstance(v, str)):
            continue
        label = STAT_LABELS.get(k, k.replace("_", " ").title())
        val = fmt_num(v) if _num(v) else str(v)
        icon = "none"
        out.append((label, val, extra_palette[idx % len(extra_palette)], icon))
        idx += 1

    return out[:14]


def build_analysis_text(s: dict[str, Any], diff: Optional[dict[str, int]]) -> Optional[str]:
    parts: list[str] = []
    played = s.get("played", 0)
    wins = s.get("victories", 0)
    kills = s.get("kills")
    if isinstance(played, int) and played > 0:
        avg_kills = f"・{kills / played:.2f}キル" if isinstance(kills, int) else ""
        cur_wr = wins / played * 100
        next_target = (int(cur_wr // 5) + 1) * 5
        advice = ""
        if 0 < next_target < 100:
            p_dec = next_target / 100.0
            needed = int(-(-((p_dec * played) - wins) // (1 - p_dec)))
            if 0 < needed <= 200:
                advice = f" ・ あと{needed}連勝で{next_target}%"
        parts.append(f"1戦平均 {s.get('xp', 0) / played:.1f}XP{avg_kills}{advice}")

    if diff:
        d_items = []
        if "victories" in diff:
            d_items.append(f"+{diff['victories']}勝")
        if "played" in diff:
            d_items.append(f"+{diff['played']}戦")
        if "kills" in diff:
            d_items.append(f"+{diff['kills']}キル")
        if "xp" in diff:
            d_items.append(f"+{diff['xp']:,}XP")
        if d_items:
            parts.append(f"前回から {' '.join(d_items)}")

    return "  |  ".join(parts) if parts else None


# ---------- フォント描画（英数字=Jersey 10 / 日本語=DotGothic16） ----------
class PixelFont:
    """ドットフォント。太字版の「W」は「M」とほぼ同じ形で読みにくいので、W/w だけ通常版の字形で描く。"""

    def __init__(self, font: Any, alt: Any = None, dot: int = 1):
        self.font = font
        self.latin = font  # getmetrics 用
        self.alt = alt
        self.dot = dot

    def segments(self, text: str):
        """(文字列, Wの特別描画かどうか) の並びにして返す。"""
        buf = ""
        for ch in text:
            if self.alt is not None and ch in "Ww":
                if buf:
                    yield buf, False
                    buf = ""
                yield ch, True
            else:
                buf += ch
        if buf:
            yield buf, False

    def seg_font(self, special: bool):
        return self.alt if special else self.font


class MixedDraw(ImageDraw.ImageDraw):
    """PixelFont を渡したときだけ専用の描き方をする ImageDraw。既存の d.text / d.textlength はそのまま使える。"""

    def textlength(self, text, font=None, *args, **kwargs):
        if isinstance(font, PixelFont):
            return sum(
                super(MixedDraw, self).textlength(seg, font=font.seg_font(sp))
                for seg, sp in font.segments(str(text))
            )
        return super().textlength(text, font=font, *args, **kwargs)

    def text(self, xy, text, fill=None, font=None, anchor=None, *args, **kwargs):
        if not isinstance(font, PixelFont):
            return super().text(xy, text, fill=fill, font=font, anchor=anchor, *args, **kwargs)
        text = str(text)
        x, y = xy
        anc = anchor or "la"
        total = self.textlength(text, font=font)
        if anc[0] == "m":
            x -= total / 2
        elif anc[0] == "r":
            x -= total
        try:
            asc, desc = font.latin.getmetrics()
        except Exception:
            asc, desc = 0, 0
        baseline = y + (asc - desc) / 2 if anc[1] == "m" else y + asc
        cx = x
        for seg, sp in font.segments(text):
            f = font.seg_font(sp)
            super().text((round(cx), round(baseline)), seg, fill=fill, font=f, anchor="ls")
            cx += super().textlength(seg, font=f)


def _snap_size(size: int) -> int:
    """希望サイズを、ドットがそろうサイズ(12/24/36)に丸める。"""
    if size <= 13:
        return 12
    for px in PIXEL_SIZES:
        if px >= size - 2:
            return px
    return PIXEL_SIZES[-1]


@lru_cache(maxsize=64)
def _load_font(size: int) -> PixelFont | ImageFont.ImageFont:
    if PIXEL_FONT_FILE.exists():
        try:
            px = _snap_size(size)
            f = ImageFont.truetype(str(PIXEL_FONT_FILE), px)
            alt = None
            if PIXEL_FONT_REGULAR.exists():
                try:
                    alt = ImageFont.truetype(str(PIXEL_FONT_REGULAR), px)
                except OSError:
                    alt = None
            return PixelFont(f, alt, max(1, px // 12))
        except OSError:
            pass
    if FONT_FALLBACK_PATH.exists():
        try:
            return PixelFont(ImageFont.truetype(str(FONT_FALLBACK_PATH), size))
        except OSError:
            pass
    return ImageFont.load_default()


# ---------- プレステージアイコン ----------
@lru_cache(maxsize=1)
def _prestige_sources() -> list[Image.Image]:
    return [
        Image.open(io.BytesIO(base64.b64decode(b))).convert("RGBA")
        for b in PRESTIGE_ICONS_B64
    ]


@lru_cache(maxsize=64)
def prestige_icon(p: int, height: int) -> Optional[Image.Image]:
    """プレステージ段階 p (1〜) のコイン画像。P0はNone。6以上は最上位(V)のコインを使う。"""
    if p <= 0:
        return None
    src = _prestige_sources()
    base = src[min(p, len(src)) - 1]
    w = max(1, round(base.width * height / base.height))
    return base.resize((w, height), Image.Resampling.NEAREST)


def prestige_width(d: ImageDraw.ImageDraw, p: int, ih: int, font: Any) -> int:
    ic = prestige_icon(p, ih)
    if not ic:
        return 0
    w = ic.width + 8
    if p > len(PRESTIGE_ICONS_B64):
        w += int(d.textlength(f"P{p}", font=font)) + 8
    return w


def draw_prestige(
    img: Image.Image, d: ImageDraw.ImageDraw, p: int, x: float, cy: float, ih: int, font: Any,
    col: tuple[int, int, int] = PRESTIGE_COL,
) -> int:
    """コインを描いて使った横幅を返す。6以上のときは "P6" のような数字を右に添える。"""
    ic = prestige_icon(p, ih)
    if not ic:
        return 0
    img.alpha_composite(ic, (int(x), int(cy - ic.height / 2)))
    w = ic.width + 8
    if p > len(PRESTIGE_ICONS_B64):
        txt = f"P{p}"
        d.text((x + w, cy), txt, font=font, fill=col, anchor="lm")
        w += int(d.textlength(txt, font=font)) + 8
    return w


def draw_icon_text(
    img: Image.Image, d: ImageDraw.ImageDraw, p: int, text: str, font: Any,
    fill: tuple[int, int, int], x: float, cy: float, align: str = "m", ih: int = 26,
):
    """[コイン] + テキスト をまとめて配置する。align: l / m / r。pが0ならテキストのみ。"""
    iw = prestige_width(d, p, ih, font)
    tw = int(d.textlength(text, font=font))
    total = iw + tw
    start = x - total / 2 if align == "m" else (x - total if align == "r" else x)
    if iw:
        draw_prestige(img, d, p, start, cy, ih, font)
    d.text((start + iw, cy), text, font=font, fill=fill, anchor="lm")


# ---------- 共通画像ユーティリティ ----------
PANEL_FILL = (22, 25, 33, 220)
PANEL_BORDER = (65, 72, 88, 180)
TXT_MAIN = (248, 250, 252)
TXT_MUTED = (186, 194, 208)


def _make_canvas_bg(w: int, h: int, map_bytes: Optional[bytes] = None) -> Image.Image:
    """マップ画像を拡大→ぼかし→暗幕。マップが無ければ共通背景、それも無ければ無地の暗色。"""
    global _DEFAULT_MAP
    if map_bytes and _DEFAULT_MAP is None:
        _DEFAULT_MAP = map_bytes
    src = map_bytes or _DEFAULT_MAP
    if src:
        try:
            bg = Image.open(io.BytesIO(src)).convert("RGB")
            scale = max(w / bg.width, h / bg.height)
            nw, nh = int(bg.width * scale) + 2, int(bg.height * scale) + 2
            bg = bg.resize((nw, nh), Image.Resampling.LANCZOS)
            left, top = (nw - w) // 2, (nh - h) // 2
            bg = bg.crop((left, top, left + w, top + h)).filter(ImageFilter.GaussianBlur(radius=7)).convert("RGBA")
            scrim = Image.new("RGBA", (w, h), (16, 18, 24, 150))
            return Image.alpha_composite(bg, scrim)
        except Exception:
            pass
    return Image.new("RGBA", (w, h), (26, 29, 36, 255))


def _fit_text(d: ImageDraw.ImageDraw, text: str, base_size: int, max_w: int, min_size: int = 12) -> tuple[str, Any]:
    sz = base_size
    f = _load_font(sz)
    while sz > min_size and d.textlength(text, font=f) > max_w:
        sz -= 1
        f = _load_font(sz)
    while len(text) > 1 and d.textlength(text, font=f) > max_w:
        text = text[:-2] + "…"
    return text, f


# ---------- ドット絵アイコン（20x20を2倍拡大。トロフィーと同じ「茶縁＋3段陰影」の画風） ----------
ICON_N = 20
ICON_PX = 40
_OUT = (134, 63, 5)  # 縁取りの茶色

_TROPHY_GRID = [
    "....................",
    "....kkkkkkkkkkkk....",
    "....koyccccyyyok....",
    "....koyccccyyyok....",
    "....koccccyyyyok....",
    ".kkkkooooooooookkkk.",
    ".kyyykddddddddkyykk.",
    ".kyydkooooooookdykk.",
    ".kyydkooooooookdykk.",
    ".koodkoyyyccookdokk.",
    "..kkokoyycccookok...",
    "....kkoccccyookk....",
    ".....kkcccyykkk.....",
    ".....kkcccyykkk.....",
    "......kkkookkk......",
    ".....nnnnnnnnnn.....",
    ".....nssswwsssn.....",
    ".....nnnnbbnnnn.....",
    ".....nnnnbbnnnn.....",
    "....................",
]
_TROPHY_PAL = {
    "k": _OUT, "o": (238, 157, 16), "y": (255, 229, 33), "n": (31, 41, 56),
    "c": (255, 247, 199), "d": (182, 96, 0), "s": (70, 91, 99), "b": (130, 157, 181), "w": (222, 240, 255),
}


def _draw_fit(d, xy, text: str, base: int, max_w: int, fill, anchor: str = "lm", min_size: int = 12):
    """はみ出す場合だけ文字サイズを下げて描く。"""
    t, f = _fit_text(d, text, base, max_w, min_size)
    d.text(xy, t, font=f, fill=fill, anchor=anchor)


_SWORD_B64 = "iVBORw0KGgoAAAANSUhEUgAAABAAAAAQCAYAAAAf8/9hAAABD0lEQVR42mNkIAPw2Zv9ZyAX8Nmb/V/y98P/JX8//OdQVfjPRKrmaft2MbSf2kO+zdrH18BtJ0uz8evTNNLMZ2/2Hz10+ezN/hu/Po1XM0ogsqvIw6OIz97sv+qaqQw/7jxk4FCRZ7hqFcrw4/YDRoLOlesq/8+hqvDf+PXp/3Jd5QT9zIhugIC3IwMDAwPD95v3GOQ6ygjazIjNFewq8gw/7zxk+PXsFUFno4SBp5no/yj+FwyfD51mYGBgYGCTEmMgFGUsyJodDIUY5m9/wvDj0VdGBgaG/zBDGBgY/uNyCQss1OX5XzDM3/6E4QZEM7LTCbuAXUWeYcGhVzCbUQChMGD59ewVw69nr8jOnQAPcZ16N2XJuwAAAABJRU5ErkJggg=="   # Kills: ダイヤの剣（16x16）
_SKULL_B64 = "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"   # Deaths: スケルトンの頭（40x40）


def _b64_image(b64: str) -> Image.Image:
    return Image.open(io.BytesIO(base64.b64decode(b64))).convert("RGBA")


def _build_sprites() -> dict[str, Image.Image]:
    sp: dict[str, Image.Image] = {}
    # Wins: トロフィー（20x20）
    im = Image.new("RGBA", (ICON_N, ICON_N), (0, 0, 0, 0))
    for y, row in enumerate(_TROPHY_GRID):
        for x, ch in enumerate(row):
            if ch in _TROPHY_PAL:
                im.putpixel((x, y), (*_TROPHY_PAL[ch], 255))
    sp["trophy"] = im.resize((ICON_N * 2, ICON_N * 2), Image.Resampling.NEAREST)   # 40x40（1ドット=2px）
    sp["sword"] = _b64_image(_SWORD_B64).resize((48, 48), Image.Resampling.NEAREST)  # 48x48（1ドット=3px）
    sp["skull"] = _b64_image(_SKULL_B64)                                              # 40x40
    return sp


_SPRITES = _build_sprites()


def _icon_w(kind: str) -> int:
    sp = _SPRITES.get(kind)
    return sp.width if sp is not None else 0


def _draw_mini_icon(img: Image.Image, kind: str, cx: int, cy: int):
    sp = _SPRITES.get(kind)
    if sp is None:
        return
    img.alpha_composite(sp, (int(cx - sp.width // 2), int(cy - sp.height // 2)))


def _paste_rounded(img: Image.Image, raw_bytes: Optional[bytes], x: int, y: int, w: int, h: int, radius: int = 10) -> bool:
    if not raw_bytes:
        return False
    try:
        sub = Image.open(io.BytesIO(raw_bytes)).convert("RGBA")
        scale = max(w / sub.width, h / sub.height)
        nw, nh = int(sub.width * scale) + 1, int(sub.height * scale) + 1
        sub = sub.resize((nw, nh), Image.Resampling.LANCZOS)
        left, top = max(0, (nw - w) // 2), max(0, (nh - h) // 2)
        sub = sub.crop((left, top, left + w, top + h))
        mask = Image.new("L", (w, h), 0)
        ImageDraw.Draw(mask).rounded_rectangle([0, 0, w, h], radius, fill=255)
        img.paste(sub, (x, y), mask)
        return True
    except Exception:
        return False


def _to_png(img: Image.Image) -> bytes:
    buf = io.BytesIO()
    img.convert("RGB").save(buf, "PNG", optimize=True)
    return buf.getvalue()


def _panel_drawer(layer: Image.Image):
    ld = ImageDraw.Draw(layer)

    def draw_panel(x: int, y: int, w: int, h: int, r: int = 12):
        ld.rounded_rectangle([x, y, x + w, y + h], radius=r, fill=PANEL_FILL, outline=PANEL_BORDER, width=1)

    return draw_panel



# ---------- マイクラ風 XPバー ----------
XP_BAR_W, XP_BAR_H = 182, 5  # マイクラ本家と同じドット数


@lru_cache(maxsize=256)
def _xp_bar_native(filled_px: int, magenta: bool) -> Image.Image:
    """182x5 のXPバー(+黒縁=184x7)をドット単位で作る。拡大はNEAREST。"""
    W, H = XP_BAR_W + 2, XP_BAR_H + 2
    im = Image.new("RGBA", (W, H), (0, 0, 0, 255))
    px = im.load()
    if magenta:
        fill_rows = [(245, 190, 255), (226, 110, 255), (226, 110, 255), (178, 70, 214), (120, 40, 150)]
    else:
        fill_rows = [(190, 255, 120), (128, 255, 32), (128, 255, 32), (96, 205, 26), (56, 140, 20)]
    empty_rows = [(74, 90, 76), (52, 66, 54), (46, 58, 48), (40, 51, 42), (32, 42, 34)]
    gap = (22, 30, 24)
    for x in range(XP_BAR_W):
        is_gap = x > 0 and (x * 18) % XP_BAR_W < 18  # 18分割の境目
        for y in range(XP_BAR_H):
            if x < filled_px:
                col = fill_rows[y] if not is_gap else tuple(int(c * 0.78) for c in fill_rows[y])
            else:
                col = gap if is_gap else empty_rows[y]
            px[x + 1, y + 1] = col + (255,)
    return im


def draw_xp_bar(img: Image.Image, cx: int, y: int, pct: float, scale: int = 4, magenta: bool = False) -> tuple[int, int, int]:
    """バーを中央cxに貼り、(左端x, 右端x, 高さ)を返す。pctは0〜1。"""
    filled = max(0, min(XP_BAR_W, int(pct * XP_BAR_W)))
    nat = _xp_bar_native(filled, magenta)
    big = nat.resize((nat.width * scale, nat.height * scale), Image.Resampling.NEAREST)
    x = cx - big.width // 2
    img.alpha_composite(big, (x, y))
    return x, x + big.width, big.height


# ---------- 1. ゲーム戦績カード ----------
def build_card(
    game_id: str,
    name: str,
    main: Optional[dict[str, Any]],
    s: dict[str, Any],
    meta: Optional[dict[str, Any]],
    period_label: str,
    avatar_bytes: Optional[bytes] = None,
    map_bytes: Optional[bytes] = None,
    monthly_rank: Optional[int] = None,
    analysis_note: Optional[str] = None,
) -> bytes:
    game_info = GAMES.get(game_id, {"name": game_id})
    stats = build_stat_items(s, meta)
    xp = int(pick(s, "xp", default=0))
    raw_prestige = s.get("prestige")
    prestige_opt = int(raw_prestige) if isinstance(raw_prestige, int) else None
    level_info = compute_level(xp, meta, prestige_opt)
    first_played = pick(s, "first_played", default=0) or pick(main, "first_played", default=0)
    rank = pick(main, "rank", default="")
    streak = pick(main, "daily_login_streak", default=None)

    rows_data: list[list[tuple[str, str, tuple[int, int, int], str]]] = []
    for i in range(0, len(stats), 4):
        rows_data.append(stats[i : i + 4])
    if len(rows_data) >= 2 and len(rows_data[-1]) == 1 and len(rows_data[-2]) == 4:
        moved = rows_data[-2].pop()
        rows_data[-1].insert(0, moved)

    W, M, G = 1040, 28, 12
    ch = 104
    top_y, top_h = 24, 62
    banner_y, banner_h = top_y + top_h + G, 68
    grid_y = banner_y + banner_h + G
    fp_y, fp_h = grid_y + len(rows_data) * (ch + G), 48
    pg_y = fp_y + fp_h + G
    pg_h = 118 if level_info else 0
    note_y = pg_y + (pg_h + G if pg_h else 0)
    note_h = 42 if analysis_note else 0
    ft_y = note_y + (note_h + G if note_h else 0)
    H = ft_y + 42

    img = _make_canvas_bg(W, H, map_bytes)
    layer = Image.new("RGBA", (W, H), (0, 0, 0, 0))
    draw_panel = _panel_drawer(layer)

    period_w = 240
    draw_panel(M, top_y, period_w, top_h)
    draw_panel(M + period_w + G, top_y, W - 2 * M - period_w - G, top_h)
    draw_panel(M, banner_y, W - 2 * M, banner_h)

    for r_idx, row_items in enumerate(rows_data):
        cnt = len(row_items)
        cell_w = (W - 2 * M - (cnt - 1) * G) // cnt
        py = grid_y + r_idx * (ch + G)
        for c_idx in range(cnt):
            px = M + c_idx * (cell_w + G)
            w_adj = (W - M - px) if c_idx == cnt - 1 else cell_w
            draw_panel(px, py, w_adj, ch)

    draw_panel(M, fp_y, W - 2 * M, fp_h)
    if level_info:
        draw_panel(M, pg_y, W - 2 * M, pg_h)
    if analysis_note:
        draw_panel(M, note_y, W - 2 * M, note_h, r=10)
    draw_panel(M, ft_y, W - 2 * M, 34, r=10)

    img = Image.alpha_composite(img, layer)
    d = MixedDraw(img)

    f_period = _load_font(24)
    f_title = _load_font(28)
    f_banner = _load_font(28)
    f_label = _load_font(19)
    f_fp = _load_font(20)
    f_pg = _load_font(21)
    f_sm = _load_font(16)

    d.text((M + period_w // 2, top_y + top_h // 2), period_label, font=f_period, fill=(56, 189, 248), anchor="mm")
    title_cx = M + period_w + G + (W - 2 * M - period_w - G) // 2
    d.text((title_cx, top_y + top_h // 2), f"{game_info['name']}  Statistics", font=f_title, fill=TXT_MAIN, anchor="mm")

    # --- バナー: [コイン] Level N  名前 [RANK] [#月間順位] ---
    display_name = pick(main, "username_cc", default=name)
    banner_segs: list[tuple[str, Any, Optional[tuple[int, int, int]]]] = []  # ("t", 文字, 色) / ("i", 段階, None)
    if level_info:
        if level_info["allow_prestige"] and level_info["prestige"] > 0:
            banner_segs.append(("i", level_info["prestige"], None))
        banner_segs.append(("t", f"Level {level_info['level']}  ", GOLD))
    banner_segs.append(("t", display_name, TXT_MAIN))
    tag = rank_tag(rank)
    if tag:
        banner_segs.append(("t", f" [{tag[0]}]", tag[1]))
    if monthly_rank:
        banner_segs.append(("t", f"  [#{monthly_rank:,}]", RED))

    icon_h = 34

    def seg_width(kind: str, val: Any) -> int:
        if kind == "i":
            return prestige_width(d, val, icon_h, f_banner)
        return int(d.textlength(val, font=f_banner))

    total_text_w = sum(seg_width(k, v) for k, v, _ in banner_segs)
    av_sz = 42 if avatar_bytes else 0
    total_w = total_text_w + (av_sz + 14 if av_sz else 0)
    cur_x = int(W // 2 - total_w // 2)
    cy_banner = banner_y + banner_h // 2

    if avatar_bytes and _paste_rounded(img, avatar_bytes, cur_x, cy_banner - av_sz // 2, av_sz, av_sz, 8):
        cur_x += av_sz + 14

    for kind, val, col in banner_segs:
        if kind == "i":
            cur_x += draw_prestige(img, d, val, cur_x, cy_banner, icon_h, f_banner)
        else:
            d.text((cur_x, cy_banner), val, font=f_banner, fill=col, anchor="lm")
            cur_x += int(d.textlength(val, font=f_banner))

    # --- 統計セル ---
    for r_idx, row_items in enumerate(rows_data):
        cnt = len(row_items)
        cell_w = (W - 2 * M - (cnt - 1) * G) // cnt
        py = grid_y + r_idx * (ch + G)
        for c_idx, (lbl, val, col, icon) in enumerate(row_items):
            px = M + c_idx * (cell_w + G)
            w_adj = (W - M - px) if c_idx == cnt - 1 else cell_w
            cx = px + w_adj // 2
            lbl_fit, fl = _fit_text(d, lbl, 19, w_adj - 24, 13)
            d.text((cx, py + 30), lbl_fit, font=fl, fill=TXT_MUTED, anchor="mm")

            slot = _icon_w(icon) + 8 if icon in _SPRITES else 0
            val_fit, fv = _fit_text(d, val, 32, w_adj - 24 - slot, 15)
            if slot:
                vw = int(d.textlength(val_fit, font=fv))
                sx = cx - (vw + slot) // 2
                _draw_mini_icon(img, icon, sx + _icon_w(icon) // 2, py + 72)
                d.text((sx + slot, py + 72), val_fit, font=fv, fill=col, anchor="lm")
            else:
                d.text((cx, py + 72), val_fit, font=fv, fill=col, anchor="mm")

    d.text((W // 2, fp_y + fp_h // 2), f"初プレイ日: {fmt_date(first_played)}", font=f_fp, fill=(125, 211, 252), anchor="mm")

    # --- レベル / プレステージ進捗 ---
    if level_info:
        lv = level_info["level"]
        cur_xp = level_info["in_lv"]
        need_xp = level_info["need"]
        is_max_lv = level_info["is_max_lv"]
        allow_p = level_info["allow_prestige"]
        p_cur = level_info["prestige"]
        p_max = level_info["max_prestige"]
        can_p = level_info["can_prestige"]
        is_true_max = level_info["is_true_max"]

        pg_title = (
            f"レベル＆プレステージ進捗  ・  プレステージ {p_cur} / {p_max}"
            if allow_p else "レベル進捗"
        )
        draw_icon_text(img, d, p_cur if allow_p else 0, pg_title, f_pg, TXT_MAIN, W // 2, pg_y + 22, "m", 26)

        if can_p:
            xp_txt = f"プレステージ {p_cur + 1} へ昇格可能！"
            xp_col = PRESTIGE_COL
        elif is_true_max:
            xp_txt = "プレステージ・レベルとも最大！" if allow_p else "最大レベル！"
            xp_col = GOLD
        else:
            xp_txt = f"{int(cur_xp / need_xp * 100)}%"
            xp_col = GREEN
        xp_fit, f_xp = _fit_text(d, xp_txt, 19, W - 2 * M - 40, 13)
        d.text((W // 2, pg_y + 52), xp_fit, font=f_xp, fill=xp_col, anchor="mm")

        pct = 1.0 if is_max_lv else cur_xp / need_xp
        bar_scale = 4
        bar_h = (XP_BAR_H + 2) * bar_scale
        by = pg_y + 76
        bx, bx_end, _ = draw_xp_bar(img, W // 2, by, pct, bar_scale, magenta=can_p)
        blocks_w = bx_end - bx
        bh = bar_h

        lv_col = (216, 180, 254)
        by_c = by + bh // 2
        if allow_p:
            draw_icon_text(img, d, p_cur, f"Lv.{lv}", f_label, lv_col, bx - 16, by_c, "r", 24)
        else:
            d.text((bx - 16, by_c), f"Level {lv}", font=f_label, fill=lv_col, anchor="rm")
        if can_p:
            draw_icon_text(img, d, p_cur + 1, "昇格！", f_label, lv_col, bx_end + 16, by_c, "l", 24)
        elif is_true_max:
            d.text((bx_end + 16, by_c), "最大", font=f_label, fill=lv_col, anchor="lm")
        else:
            nxt = f"Lv.{lv + 1}" if allow_p else f"Level {lv + 1}"
            d.text((bx_end + 16, by_c), nxt, font=f_label, fill=lv_col, anchor="lm")

    if analysis_note:
        note_fit, f_note = _fit_text(d, analysis_note, 17, W - 2 * M - 32, 13)
        d.text((W // 2, note_y + note_h // 2), note_fit, font=f_note, fill=GOLD, anchor="mm")

    ft_parts = ["ぴーBOT"]
    if streak is not None:
        ft_parts.append(f"Login Streak: {streak}d")
    d.text((W // 2, ft_y + 17), "  ・  ".join(ft_parts), font=f_sm, fill=TXT_MUTED, anchor="mm")

    return _to_png(img)


# ---------- 2. 総合プロフィール画像 ----------
def build_overview_card(
    gamertag: str,
    allstats: dict[str, Any],
    main: dict[str, Any],
    avatar_bytes: Optional[bytes] = None,
    map_bytes: Optional[bytes] = None,
) -> bytes:
    display_name = pick(main, "username_cc", default=gamertag)
    rank_info = rank_tag(pick(main, "rank", default=""))
    paid_ranks = "、".join(main.get("paid_ranks") or []) or "なし"
    first_played = fmt_date(pick(main, "first_played", default=0))
    player_no = fmt_num(pick(main, "player_number", default=0))

    played_games: list[tuple[str, int, int, int, int, tuple[int, int, int]]] = []
    for gid, ginfo in GAMES.items():
        gs = allstats.get(gid)
        if isinstance(gs, dict) and (gs.get("played", 0) > 0 or gs.get("xp", 0) > 0):
            played_games.append((
                ginfo["name"],
                int(gs.get("victories", 0)),
                int(gs.get("played", 0)),
                int(gs.get("xp", 0)),
                int(gs.get("prestige") or 0),
                ginfo["accent"],
            ))
    played_games.sort(key=lambda x: x[2], reverse=True)
    shown_games = played_games[:12]

    W, M, G = 1040, 28, 12
    top_y, top_h = 24, 96
    info_y, info_h = top_y + top_h + G, 124
    games_rows = max(1, -(-len(shown_games) // 3))
    games_y = info_y + info_h + G
    game_ch = 78
    ft_y = games_y + 38 + games_rows * (game_ch + 10) + G
    H = ft_y + 42

    img = _make_canvas_bg(W, H, map_bytes)
    layer = Image.new("RGBA", (W, H), (0, 0, 0, 0))
    draw_panel = _panel_drawer(layer)

    draw_panel(M, top_y, W - 2 * M, top_h)
    half_w = (W - 2 * M - G) // 2
    draw_panel(M, info_y, half_w, info_h)
    draw_panel(M + half_w + G, info_y, W - 2 * M - half_w - G, info_h)
    draw_panel(M, games_y, W - 2 * M, 38 + games_rows * (game_ch + 10))
    draw_panel(M, ft_y, W - 2 * M, 34, r=10)

    img = Image.alpha_composite(img, layer)
    d = MixedDraw(img)

    f_name = _load_font(30)
    f_sub = _load_font(17)
    f_sec = _load_font(18)
    f_sm = _load_font(16)

    av_x, av_y, av_sz = M + 18, top_y + 14, 68
    if not _paste_rounded(img, avatar_bytes, av_x, av_y, av_sz, av_sz, 12):
        d.rounded_rectangle([av_x, av_y, av_x + av_sz, av_y + av_sz], 12, fill=(45, 52, 68))
        d.text((av_x + av_sz // 2, av_y + av_sz // 2), display_name[:2].upper(), font=f_name, fill=AMBER, anchor="mm")

    tx = av_x + av_sz + 18
    title_str = f"{display_name} - Overview"
    if rank_info:
        title_str += f"  [{rank_info[0]}]"
    t_fit, ft_f = _fit_text(d, title_str, 28, W - M - tx - 20, 18)
    d.text((tx, top_y + 32), t_fit, font=ft_f, fill=TXT_MAIN, anchor="lm")
    _draw_fit(d, (tx, top_y + 68), f"Player #{player_no}  ・  初プレイ日: {first_played}  ・  Paid Ranks: {paid_ranks}", 20, W - M - tx - 20, TXT_MUTED)

    d.text((M + 18, info_y + 24), "Login & Friends", font=f_sec, fill=AMBER, anchor="lm")
    _draw_fit(
        d, (M + 18, info_y + 62),
        f"Streak: {main.get('daily_login_streak', 0)}d (Best: {main.get('longest_daily_login_streak', 0)}d)",
        24, half_w - 36, TXT_MAIN,
    )
    _draw_fit(d, (M + 18, info_y + 94), f"Friends: {fmt_num(main.get('friend_count', 0))}", 24, half_w - 36, TXT_MAIN)

    rx = M + half_w + G + 18
    d.text((rx, info_y + 24), "Cosmetics", font=f_sec, fill=(56, 189, 248), anchor="lm")
    _draw_fit(
        d, (rx, info_y + 62),
        f"Titles {main.get('hub_title_count', 0)} ・ Avatars {main.get('avatar_count', 0)} ・ Costumes {main.get('costume_count', 0)}",
        24, half_w - 36, TXT_MAIN,
    )
    _draw_fit(
        d, (rx, info_y + 94),
        f"Hats {main.get('hat_count', 0)} ・ Pets {len(main.get('pets') or [])}",
        24, half_w - 36, TXT_MAIN,
    )

    d.text((M + 18, games_y + 22), f"Games Summary ({len(played_games)} games played)", font=f_sec, fill=TXT_MAIN, anchor="lm")
    if not shown_games:
        d.text((W // 2, games_y + 75), "まだプレイ記録がありません", font=f_sec, fill=TXT_MUTED, anchor="mm")
    else:
        gw = (W - 2 * M - 36 - 2 * 10) // 3
        for idx, (gname, wins, played, xp, prest, acc) in enumerate(shown_games):
            r, c = divmod(idx, 3)
            gx = M + 18 + c * (gw + 10)
            gy = games_y + 42 + r * (game_ch + 10)
            d.rounded_rectangle([gx, gy, gx + gw, gy + game_ch], 10, fill=(32, 36, 46, 220), outline=PANEL_BORDER, width=1)
            d.rectangle([gx, gy + 12, gx + 4, gy + game_ch - 12], fill=acc)

            # プレステージコインはカード右上に表示（6以上は下に P数字）
            pic = prestige_icon(prest, 28)
            ptxt = f"P{prest}" if prest > len(PRESTIGE_ICONS_B64) else ""
            ptxt_w = (int(d.textlength(ptxt, font=f_sm)) + 8) if ptxt else 0
            name_max = gw - 28 - ((pic.width + 12 + ptxt_w) if pic else 0)
            gn_fit, fg = _fit_text(d, gname, 19, name_max, 13)
            d.text((gx + 16, gy + 24), gn_fit, font=fg, fill=TXT_MAIN, anchor="lm")
            if pic:
                img.alpha_composite(pic, (gx + gw - 12 - pic.width, gy + 24 - pic.height // 2))
                if ptxt:
                    d.text((gx + gw - 12 - pic.width - 8, gy + 24), ptxt, font=f_sm, fill=PRESTIGE_COL, anchor="rm")

            wr = f" ({wins / played * 100:.1f}%)" if played else ""
            _draw_fit(d, (gx + 16, gy + 54), f"{wins:,} W / {played:,} P{wr}", 24, gw - 28, GREEN)

    d.text((W // 2, ft_y + 17), "ぴーBOT  ・  下のメニューから各ゲームの詳細カードを開けます", font=f_sm, fill=TXT_MUTED, anchor="mm")
    return _to_png(img)


# ---------- 3. 持ち物・コスメティック画像 ----------
def build_cosmetics_card(
    gamertag: str,
    main: dict[str, Any],
    avatar_bytes: Optional[bytes] = None,
    map_bytes: Optional[bytes] = None,
) -> bytes:
    display_name = pick(main, "username_cc", default=gamertag)
    av_name = pick(main, "equipped_avatar", default={}).get("name", "未設定") if isinstance(main.get("equipped_avatar"), dict) else "未設定"

    hats = [f"{h.get('name')} ({h.get('rarity', '-')})" for h in (main.get("hat_unlocked") or [])]
    backs = [f"{b.get('name')} ({b.get('rarity', '-')})" for b in (main.get("cosmetics.backbling") or [])]
    costumes = main.get("costume_unlocked") or []
    titles = main.get("hub_title_unlocked") or []
    pets = main.get("pets") or []
    mounts = main.get("mounts") or []

    sections = [
        (f"Hats ({len(hats)})", ", ".join(hats[:8]) + (" ..." if len(hats) > 8 else "") or "None"),
        (f"Backbling ({len(backs)})", ", ".join(backs[:8]) + (" ..." if len(backs) > 8 else "") or "None"),
        (f"Costumes ({len(costumes)})", ", ".join(costumes[:12]) + (" ..." if len(costumes) > 12 else "") or "None"),
        (f"Pets & Mounts (Pets: {len(pets)} / Mounts: {len(mounts)})", f"Pets: {', '.join(pets[:8]) or 'None'}  /  Mounts: {', '.join(mounts[:8]) or 'None'}"),
        (f"Hub Titles ({main.get('hub_title_count', len(titles))})", ", ".join(titles[:12]) + (" ..." if len(titles) > 12 else "") or "None"),
    ]

    W, M, G = 1040, 28, 12
    top_y, top_h = 24, 92
    sec_y = top_y + top_h + G
    sec_h = 84
    ft_y = sec_y + len(sections) * (sec_h + 10) + 4
    H = ft_y + 42

    img = _make_canvas_bg(W, H, map_bytes)
    layer = Image.new("RGBA", (W, H), (0, 0, 0, 0))
    draw_panel = _panel_drawer(layer)

    draw_panel(M, top_y, W - 2 * M, top_h)
    for i in range(len(sections)):
        draw_panel(M, sec_y + i * (sec_h + 10), W - 2 * M, sec_h)
    draw_panel(M, ft_y, W - 2 * M, 34, r=10)

    img = Image.alpha_composite(img, layer)
    d = MixedDraw(img)

    f_title = _load_font(28)
    f_sec = _load_font(19)
    f_sm = _load_font(16)

    av_x, av_y, av_sz = M + 18, top_y + 14, 64
    if not _paste_rounded(img, avatar_bytes, av_x, av_y, av_sz, av_sz, 10):
        d.rounded_rectangle([av_x, av_y, av_x + av_sz, av_y + av_sz], 10, fill=(45, 52, 68))

    tx = av_x + av_sz + 18
    d.text((tx, top_y + 32), f"{display_name} - Cosmetics", font=f_title, fill=TXT_MAIN, anchor="lm")
    _draw_fit(d, (tx, top_y + 66), f"Equipped Avatar: {av_name}  ・  Unlocked Avatars: {main.get('avatar_count', 0)}", 24, W - M - tx - 20, TXT_MUTED)

    for i, (heading, body) in enumerate(sections):
        sy = sec_y + i * (sec_h + 10)
        d.text((M + 20, sy + 24), heading, font=f_sec, fill=AMBER, anchor="lm")
        body_fit, fb = _fit_text(d, body, 17, W - 2 * M - 40, 12)
        d.text((M + 20, sy + 56), body_fit, font=fb, fill=TXT_MAIN, anchor="lm")

    d.text((W // 2, ft_y + 17), "ぴーBOT  ・  The Hive Cosmetics", font=f_sm, fill=TXT_MUTED, anchor="mm")
    return _to_png(img)


# ---------- 4. マップ一覧画像（マップサムネイル付き） ----------
def build_maps_card(
    game_id: str,
    maps: list[dict[str, Any]],
    thumb_bytes_list: list[Optional[bytes]],
) -> bytes:
    ginfo = GAMES.get(game_id, {"name": game_id})
    shown = maps[:12]
    cols = 3
    rows = max(1, -(-len(shown) // cols))

    W, M, G = 1040, 28, 12
    top_y, top_h = 24, 66
    grid_y = top_y + top_h + G
    cw = (W - 2 * M - (cols - 1) * G) // cols
    ch = 166
    ft_y = grid_y + (rows * (ch + G) if shown else 120)
    H = ft_y + 42

    bg_map = next((b for b in thumb_bytes_list if b), None)
    img = _make_canvas_bg(W, H, bg_map)
    layer = Image.new("RGBA", (W, H), (0, 0, 0, 0))
    draw_panel = _panel_drawer(layer)

    draw_panel(M, top_y, W - 2 * M, top_h)
    for i in range(len(shown)):
        r, c = divmod(i, cols)
        draw_panel(M + c * (cw + G), grid_y + r * (ch + G), cw, ch)
    if not shown:
        draw_panel(M, grid_y, W - 2 * M, 108)
    draw_panel(M, ft_y, W - 2 * M, 34, r=10)

    img = Image.alpha_composite(img, layer)
    d = MixedDraw(img)

    f_title = _load_font(26)
    f_sm = _load_font(15)
    d.text((W // 2, top_y + top_h // 2), f"{ginfo['name']}  Maps ({len(maps)})", font=f_title, fill=TXT_MAIN, anchor="mm")

    if not shown:
        d.text((W // 2, grid_y + 54), "公開されているマップ情報がありません", font=_load_font(20), fill=TXT_MUTED, anchor="mm")
    else:
        for i, m in enumerate(shown):
            r, c = divmod(i, cols)
            px = M + c * (cw + G)
            py = grid_y + r * (ch + G)
            tb = thumb_bytes_list[i] if i < len(thumb_bytes_list) else None
            if not _paste_rounded(img, tb, px + 8, py + 8, cw - 16, 104, 8):
                d.rounded_rectangle([px + 8, py + 8, px + cw - 8, py + 112], 8, fill=(40, 46, 58))
            mname, fn = _fit_text(d, str(m.get("name", "Unknown")), 18, cw - 20, 13)
            d.text((px + 12, py + 126), mname, font=fn, fill=TXT_MAIN, anchor="lm")
            meta_txt = f"{m.get('variant', 'Standard')} ・ {m.get('season', '-')}"
            mmeta, fm = _fit_text(d, meta_txt, 14, cw - 20, 11)
            d.text((px + 12, py + 149), mmeta, font=fm, fill=TXT_MUTED, anchor="lm")

    d.text((W // 2, ft_y + 17), "ぴーBOT  ・  Showing top 12 maps", font=f_sm, fill=TXT_MUTED, anchor="mm")
    return _to_png(img)


# ---------- 5. ランキング画像 ----------
def build_leaderboard_card(
    game_id: str,
    period: str,
    entries: list[dict[str, Any]],
    page: int,
    per_page: int = 10,
    map_bytes: Optional[bytes] = None,
) -> bytes:
    ginfo = GAMES.get(game_id, {"name": game_id})
    total_pages = max(1, -(-len(entries) // per_page))
    chunk = entries[page * per_page : (page + 1) * per_page]

    W, M, G = 1040, 28, 12
    top_y, top_h = 24, 66
    list_y = top_y + top_h + G
    row_h = 52
    ft_y = list_y + max(1, len(chunk)) * row_h + G
    H = ft_y + 42

    img = _make_canvas_bg(W, H, map_bytes)
    layer = Image.new("RGBA", (W, H), (0, 0, 0, 0))
    ld = ImageDraw.Draw(layer)

    ld.rounded_rectangle([M, top_y, W - M, top_y + top_h], 12, fill=PANEL_FILL, outline=PANEL_BORDER, width=1)
    for i in range(max(1, len(chunk))):
        ry = list_y + i * row_h
        ld.rounded_rectangle([M, ry, W - M, ry + row_h - 6], 10, fill=PANEL_FILL, outline=PANEL_BORDER, width=1)
    ld.rounded_rectangle([M, ft_y, W - M, ft_y + 34], 10, fill=PANEL_FILL, outline=PANEL_BORDER, width=1)

    img = Image.alpha_composite(img, layer)
    d = MixedDraw(img)

    f_title = _load_font(26)
    f_row = _load_font(20)
    f_sm = _load_font(16)

    p_label = "All-Time Top 100" if period == "all" else "Monthly Top 100"
    d.text((W // 2, top_y + top_h // 2), f"{ginfo['name']}  {p_label}", font=f_title, fill=TXT_MAIN, anchor="mm")

    if not chunk:
        d.text((W // 2, list_y + 22), "ランキングデータがありません", font=f_row, fill=TXT_MUTED, anchor="mm")
    else:
        for i, e in enumerate(chunk):
            ry = list_y + i * row_h + (row_h - 6) // 2
            rank = int(e.get("human_index", e.get("index", 0) + 1))
            r_col = (250, 204, 21) if rank == 1 else ((226, 232, 240) if rank == 2 else ((251, 146, 60) if rank == 3 else (96, 165, 250)))
            d.text((M + 26, ry), f"#{rank}", font=f_row, fill=r_col, anchor="lm")

            uname, fn = _fit_text(d, str(e.get("username", "Unknown")), 21, 320, 14)
            d.text((M + 110, ry), uname, font=fn, fill=TXT_MAIN, anchor="lm")

            wins = int(e.get("victories", 0))
            played = int(e.get("played", 0))
            xp = int(e.get("xp", 0))
            wr = f"({wins / played * 100:.1f}%)" if played else ""
            d.text((W - M - 260, ry), f"{wins:,} W / {played:,} P {wr}", font=f_sm, fill=GREEN, anchor="rm")
            d.text((W - M - 24, ry), f"{xp:,} XP", font=f_row, fill=AMBER, anchor="rm")

    d.text((W // 2, ft_y + 17), f"ぴーBOT  ・  Page {page + 1} / {total_pages}", font=f_sm, fill=TXT_MUTED, anchor="mm")
    return _to_png(img)


# ---------- 6. 全体統計画像 ----------
def build_global_card(up: dict[str, int]) -> bytes:
    total = up.get("global", up.get("main", 0))
    rows = sorted(
        [(gid, cnt) for gid, cnt in up.items() if gid not in ("global", "main")],
        key=lambda kv: kv[1],
        reverse=True,
    )

    W, M, G = 1040, 28, 12
    top_y, top_h = 24, 92
    list_y = top_y + top_h + G
    row_h = 46
    list_h = len(rows) * row_h + 12
    ft_y = list_y + list_h + G
    H = ft_y + 42

    img = _make_canvas_bg(W, H)
    layer = Image.new("RGBA", (W, H), (0, 0, 0, 0))
    draw_panel = _panel_drawer(layer)

    draw_panel(M, top_y, W - 2 * M, top_h)
    draw_panel(M, list_y, W - 2 * M, list_h)
    draw_panel(M, ft_y, W - 2 * M, 34, r=10)

    img = Image.alpha_composite(img, layer)
    d = MixedDraw(img)

    f_title = _load_font(26)
    f_big = _load_font(32)
    f_row = _load_font(17)
    f_sm = _load_font(15)

    d.text((W // 2, top_y + 28), "The Hive - Global Unique Players", font=f_title, fill=TXT_MUTED, anchor="mm")
    d.text((W // 2, top_y + 66), f"{total:,}", font=f_big, fill=AMBER, anchor="mm")

    bar_x = M + 280
    bar_w = W - M - 220 - bar_x
    for i, (gid, cnt) in enumerate(rows):
        ry = list_y + 24 + i * row_h
        info = GAMES.get(gid, {"name": gid, "accent": (245, 158, 11)})
        pct = (cnt / total * 100) if total else 0
        gname, fg = _fit_text(d, info["name"], 17, 240, 12)
        d.text((M + 20, ry), gname, font=fg, fill=TXT_MAIN, anchor="lm")

        d.rounded_rectangle([bar_x, ry - 7, bar_x + bar_w, ry + 7], 7, fill=(45, 52, 68))
        fw = max(12, int(bar_w * (cnt / total))) if total else 12
        d.rounded_rectangle([bar_x, ry - 7, bar_x + fw, ry + 7], 7, fill=info["accent"])

        d.text((W - M - 20, ry), f"{cnt:,} ({pct:.1f}%)", font=f_row, fill=TXT_MAIN, anchor="rm")

    d.text((W // 2, ft_y + 17), "ぴーBOT  ・  Unique Players by Game", font=f_sm, fill=TXT_MUTED, anchor="mm")
    return _to_png(img)


# ---------- 7. 2人比較画像 ----------
def build_compare_card(
    game_id: str,
    p1_name: str,
    p1_s: dict[str, Any],
    p2_name: str,
    p2_s: dict[str, Any],
) -> bytes:
    game_info = GAMES.get(game_id, {"name": game_id})
    metrics = [
        ("Wins", "victories"),
        ("Games Played", "played"),
        ("Win Rate", "_winrate"),
        ("Kills", "kills"),
        ("Deaths", "deaths"),
        ("KDR", "_kd"),
        ("Final Kills", "final_kills"),
        ("Prestige", "prestige"),
        ("XP", "xp"),
    ]

    def get_val(s: dict[str, Any], key: str) -> Optional[float]:
        if key == "_winrate":
            p, w = s.get("played", 0), s.get("victories", 0)
            return round(w / p * 100, 2) if p else 0.0
        if key == "_kd":
            k, d_ = s.get("kills", 0), s.get("deaths", 0)
            return round(ratio(k, d_), 2)
        v = s.get(key)
        return float(v) if _num(v) else None

    rows = []
    for lbl, key in metrics:
        v1, v2 = get_val(p1_s, key), get_val(p2_s, key)
        if v1 is not None or v2 is not None:
            rows.append((lbl, key, v1 or 0.0, v2 or 0.0))

    W, M, G = 980, 28, 12
    top_y, top_h = 24, 100
    list_y = top_y + top_h + G
    row_h = 54
    ft_y = list_y + len(rows) * row_h + G
    H = ft_y + 42

    img = _make_canvas_bg(W, H)
    layer = Image.new("RGBA", (W, H), (0, 0, 0, 0))
    draw_panel = _panel_drawer(layer)
    draw_panel(M, top_y, W - 2 * M, top_h)
    for i in range(len(rows)):
        draw_panel(M, list_y + i * row_h, W - 2 * M, row_h - 6, r=10)
    draw_panel(M, ft_y, W - 2 * M, 34, r=10)

    img = Image.alpha_composite(img, layer)
    d = MixedDraw(img)

    f_title = _load_font(25)
    f_player = _load_font(28)
    f_row = _load_font(22)
    f_sm = _load_font(17)

    d.text((W // 2, top_y + 26), f"{game_info['name']}  Compare", font=f_title, fill=TXT_MAIN, anchor="mm")
    p1_fit, fp1 = _fit_text(d, p1_name, 28, W // 2 - M - 90, 16)
    p2_fit, fp2 = _fit_text(d, p2_name, 28, W // 2 - M - 90, 16)
    d.text((M + 20, top_y + 68), p1_fit, font=fp1, fill=(96, 165, 250), anchor="lm")
    d.text((W // 2, top_y + 68), "VS", font=f_row, fill=(148, 163, 184), anchor="mm")
    d.text((W - M - 20, top_y + 68), p2_fit, font=fp2, fill=(251, 146, 60), anchor="rm")

    for idx, (lbl, key, v1, v2) in enumerate(rows):
        cy = list_y + idx * row_h + (row_h - 6) // 2
        s1 = f"{v1:.2f}%" if key == "_winrate" else fmt_num(int(v1) if float(v1).is_integer() else v1)
        s2 = f"{v2:.2f}%" if key == "_winrate" else fmt_num(int(v2) if float(v2).is_integer() else v2)
        c1 = GREEN if (v1 > v2 and key != "deaths") or (v1 < v2 and key == "deaths") else TXT_MAIN
        c2 = GREEN if (v2 > v1 and key != "deaths") or (v2 < v1 and key == "deaths") else TXT_MAIN
        d.text((M + 24, cy), s1, font=f_row, fill=c1, anchor="lm")
        d.text((W // 2, cy), lbl, font=f_sm, fill=TXT_MUTED, anchor="mm")
        d.text((W - M - 24, cy), s2, font=f_row, fill=c2, anchor="rm")

    d.text((W // 2, ft_y + 17), "ぴーBOT", font=f_sm, fill=TXT_MUTED, anchor="mm")
    return _to_png(img)


# ---------- 8. お知らせ・データなし画像 ----------
def build_notice_card(title: str, message: str, is_error: bool = False) -> bytes:
    W, H = 880, 220
    img = _make_canvas_bg(W, H)
    layer = Image.new("RGBA", (W, H), (0, 0, 0, 0))
    ImageDraw.Draw(layer).rounded_rectangle([24, 24, W - 24, H - 24], 14, fill=PANEL_FILL, outline=PANEL_BORDER, width=1)
    img = Image.alpha_composite(img, layer)
    d = MixedDraw(img)

    t_fit, ft = _fit_text(d, title, 26, W - 96, 16)
    m_fit, fm = _fit_text(d, message, 20, W - 96, 13)
    d.text((W // 2, 76), t_fit, font=ft, fill=RED if is_error else AMBER, anchor="mm")
    d.text((W // 2, 128), m_fit, font=fm, fill=TXT_MAIN, anchor="mm")
    d.text((W // 2, 174), "ぴーBOT", font=_load_font(15), fill=TXT_MUTED, anchor="mm")
    return _to_png(img)


# ---------- 対話型 Discord UI View（すべて画像出力・誰でも操作可能） ----------
class HiveDashboardView(discord.ui.View):
    def __init__(
        self,
        gamertag: str,
        game_id: str,
        period: str,
        view_mode: str,
        allstats: dict[str, Any],
        main: dict[str, Any],
    ):
        super().__init__(timeout=300)
        self.gamertag = gamertag
        self.game_id = game_id
        self.period = period
        self.view_mode = view_mode  # "card" | "cosmetics" | "maps"
        self.allstats = allstats
        self.main = main

        options = [
            discord.SelectOption(
                label="Overview（総合プロフィール）",
                value="overview",
                description="Rank・ログイン日数・各ゲームの戦績一覧",
                default=(self.game_id == "overview"),
            )
        ]
        for gid, ginfo in GAMES.items():
            gs = allstats.get(gid)
            has_data = isinstance(gs, dict) and (gs.get("played", 0) > 0 or gs.get("xp", 0) > 0)
            p_tag = f"[P{gs.get('prestige')}] " if isinstance(gs, dict) and (gs.get("prestige") or 0) > 0 else ""
            desc = (
                f"{p_tag}{fmt_num(gs.get('victories', 0))} W / {fmt_num(gs.get('played', 0))} P"
                if has_data else "プレイ記録なし"
            )
            options.append(
                discord.SelectOption(
                    label=ginfo["name"],
                    value=gid,
                    description=desc[:90],
                    default=(self.game_id == gid),
                )
            )
        select = discord.ui.Select(
            placeholder="見たいゲームやプロフィールを選ぶ...",
            options=options[:25],
            row=0,
        )
        select.callback = self.on_game_select
        self.add_item(select)

    async def _render_png(self) -> tuple[bytes, str]:
        await wait_assets()
        av_url = pick(self.main, "equipped_avatar", default={}).get("url") if isinstance(self.main.get("equipped_avatar"), dict) else None
        meta_key = GAMES.get(self.game_id, {}).get("meta") if self.game_id != "overview" else "sky"
        q_name = quote(self.gamertag, safe="")
        py, pm, prev_lbl = prev_year_month()

        async with aiohttp.ClientSession(headers={"User-Agent": USER_AGENT}) as session:
            if self.view_mode == "maps":
                m_key = meta_key or self.game_id
                maps = await hive_get(session, PATH_MAPS.format(game=quote(m_key, safe="")), ttl=META_CACHE_SEC) or []
                thumbs = await asyncio.gather(*(fetch_image_bytes(session, m.get("image")) for m in maps[:12]))
                png = await asyncio.to_thread(build_maps_card, self.game_id, maps, list(thumbs))
                return png, "hive_maps.png"

            if self.view_mode == "cosmetics":
                av_bytes, map_bytes = await asyncio.gather(
                    fetch_image_bytes(session, av_url), get_bg_map_bytes(session, "sky")
                )
                png = await asyncio.to_thread(build_cosmetics_card, self.gamertag, self.main, av_bytes, map_bytes)
                return png, "hive_cosmetics.png"

            if self.game_id == "overview":
                av_bytes, map_bytes = await asyncio.gather(
                    fetch_image_bytes(session, av_url), get_bg_map_bytes(session, "sky")
                )
                png = await asyncio.to_thread(build_overview_card, self.gamertag, self.allstats, self.main, av_bytes, map_bytes)
                return png, "hive_overview.png"

            meta = await hive_get(session, PATH_META.format(game=quote(meta_key, safe="")), ttl=META_CACHE_SEC) if meta_key else None
            monthly_data = None
            if self.period == "monthly":
                monthly_data = await hive_get(session, PATH_MONTHLY_PLAYER.format(game=quote(self.game_id, safe=""), name=q_name))
            elif self.period == "prev_month":
                monthly_data = await hive_get(session, PATH_MONTHLY_PLAYER_YM.format(game=quote(self.game_id, safe=""), name=q_name, year=py, month=pm))
            av_bytes, map_bytes = await asyncio.gather(
                fetch_image_bytes(session, av_url), get_bg_map_bytes(session, meta_key)
            )

        s = monthly_data if self.period in ("monthly", "prev_month") else self.allstats.get(self.game_id)
        if not s:
            gname = GAMES.get(self.game_id, {}).get("name", self.game_id)
            p_lbl = "今月" if self.period == "monthly" else (prev_lbl if self.period == "prev_month" else "全期間")
            png = await asyncio.to_thread(
                build_notice_card,
                f"{self.gamertag} さん - {gname}（{p_lbl}）",
                f"{p_lbl}のプレイ記録がまだ見つかりませんでした。",
            )
            return png, "hive_notice.png"

        diff = update_snapshot_diff(self.gamertag, self.game_id, self.period, s)
        analysis = build_analysis_text(s, diff)
        monthly_rank = s.get("human_index") if self.period in ("monthly", "prev_month") else None
        p_lbl = "今月" if self.period == "monthly" else (f"先月 {prev_lbl}" if self.period == "prev_month" else "全期間")
        png = await asyncio.to_thread(
            build_card, self.game_id, self.gamertag, self.main, s, meta, p_lbl, av_bytes, map_bytes, monthly_rank, analysis
        )
        return png, "hive_stats.png"

    async def _render_and_update(self, interaction: discord.Interaction):
        await interaction.response.defer()
        try:
            png, fname = await self._render_png()
        except HiveRateLimited as e:
            png = await asyncio.to_thread(
                build_notice_card,
                "ただいまアクセスが集中しています",
                f"約{max(1, e.wait // 60)}分後にもう一度お試しください。",
                True,
            )
            fname = "hive_notice.png"
        await interaction.edit_original_response(
            content=None,
            embed=None,
            attachments=[discord.File(io.BytesIO(png), filename=fname)],
            view=self,
        )

    async def on_game_select(self, interaction: discord.Interaction):
        self.game_id = interaction.data["values"][0]
        if self.view_mode == "cosmetics":
            self.view_mode = "card"
        for child in self.children:
            if isinstance(child, discord.ui.Select):
                for opt in child.options:
                    opt.default = (opt.value == self.game_id)
        await self._render_and_update(interaction)

    @discord.ui.button(label="All-Time / Monthly / 先月", style=discord.ButtonStyle.primary, row=1)
    async def cycle_period(self, interaction: discord.Interaction, button: discord.ui.Button):
        order = ["all", "monthly", "prev_month"]
        self.period = order[(order.index(self.period) + 1) % len(order)]
        self.view_mode = "card"
        if self.game_id == "overview":
            self.game_id = "sky"
        await self._render_and_update(interaction)

    @discord.ui.button(label="Cosmetics", style=discord.ButtonStyle.secondary, row=1)
    async def show_cosmetics(self, interaction: discord.Interaction, button: discord.ui.Button):
        self.view_mode = "cosmetics"
        await self._render_and_update(interaction)

    @discord.ui.button(label="Maps", style=discord.ButtonStyle.secondary, row=1)
    async def show_maps(self, interaction: discord.Interaction, button: discord.ui.Button):
        if self.game_id == "overview":
            self.game_id = "sky"
        self.view_mode = "maps"
        await self._render_and_update(interaction)


class LeaderboardPaginator(discord.ui.View):
    def __init__(self, game_id: str, period: str, entries: list[dict[str, Any]], map_bytes: Optional[bytes] = None):
        super().__init__(timeout=180)
        self.game_id = game_id
        self.period = period
        self.entries = entries
        self.map_bytes = map_bytes
        self.page = 0
        self.per_page = 10

    async def make_file(self) -> discord.File:
        png = await asyncio.to_thread(
            build_leaderboard_card, self.game_id, self.period, self.entries, self.page, self.per_page, self.map_bytes
        )
        return discord.File(io.BytesIO(png), filename="hive_leaderboard.png")

    @discord.ui.button(label="◀ 前の10件", style=discord.ButtonStyle.secondary)
    async def prev_page(self, interaction: discord.Interaction, button: discord.ui.Button):
        await interaction.response.defer()
        self.page = max(0, self.page - 1)
        await interaction.edit_original_response(content=None, embed=None, attachments=[await self.make_file()], view=self)

    @discord.ui.button(label="次の10件 ▶", style=discord.ButtonStyle.secondary)
    async def next_page(self, interaction: discord.Interaction, button: discord.ui.Button):
        await interaction.response.defer()
        max_page = max(0, -(-len(self.entries) // self.per_page) - 1)
        self.page = min(max_page, self.page + 1)
        await interaction.edit_original_response(content=None, embed=None, attachments=[await self.make_file()], view=self)


# ---------- ゲーマータグ自動補完 ----------
async def gamertag_autocomplete(
    interaction: discord.Interaction, current: str
) -> list[app_commands.Choice[str]]:
    q = current.strip()
    if len(q) < 4:
        return []
    try:
        async with aiohttp.ClientSession(headers={"User-Agent": USER_AGENT}) as session:
            res = await hive_get(session, PATH_SEARCH.format(query=quote(q, safe="")), ttl=SEARCH_CACHE_SEC)
        if isinstance(res, list):
            return [
                app_commands.Choice(
                    name=str(item.get("username_cc") or item.get("username"))[:100],
                    value=str(item.get("username"))[:100],
                )
                for item in res[:15]
                if item.get("username")
            ]
    except Exception:
        pass
    return []


# ---------- コマンド登録（すべて画像出力・誰でも利用可能） ----------
def setup_hive(bot: commands.Bot):
    global _assets_task
    # フォントとマップ背景の準備をバックグラウンドで開始（setup_hook内など、イベントループ上で呼ぶこと）
    _assets_task = asyncio.create_task(_prepare_assets())

    game_choices = [
        app_commands.Choice(name=v["name"], value=k)
        for k, v in GAMES.items()
    ][:25]

    def _file(png: bytes, name: str = "hive_notice.png") -> discord.File:
        return discord.File(io.BytesIO(png), filename=name)

    @bot.tree.command(name="hive_link", description="自分のMinecraftゲーマータグを登録します（次回から /hive で入力を省略できます）")
    @app_commands.describe(gamertag="普段使っているMinecraftのゲーマータグ")
    @app_commands.autocomplete(gamertag=gamertag_autocomplete)
    async def hive_link(interaction: discord.Interaction, gamertag: str):
        await wait_assets()
        clean = gamertag.strip()
        link_set(interaction.user.id, clean)
        png = await asyncio.to_thread(
            build_notice_card,
            "ゲーマータグを登録しました",
            f"「{clean}」を登録しました。次回から /hive だけで確認できます！",
        )
        await interaction.response.send_message(file=_file(png, "hive_link.png"), ephemeral=True)

    @bot.tree.command(name="hive_unlink", description="登録したゲーマータグを解除します")
    async def hive_unlink(interaction: discord.Interaction):
        await wait_assets()
        link_delete(interaction.user.id)
        png = await asyncio.to_thread(build_notice_card, "登録を解除しました", "ゲーマータグの登録を解除しました。")
        await interaction.response.send_message(file=_file(png, "hive_unlink.png"), ephemeral=True)

    @bot.tree.command(name="hive", description="Hiveの戦績やCosmeticsを画像で表示します")
    @app_commands.describe(
        gamertag="Minecraftのゲーマータグ（/hive_link 済みなら省略できます）",
        game="最初に見るゲーム（省略時はOverview）",
        period="集計する期間（All-Time / Monthly / 先月）",
    )
    @app_commands.autocomplete(gamertag=gamertag_autocomplete)
    @app_commands.choices(
        game=[app_commands.Choice(name="Overview（すべて）", value="overview")] + game_choices[:24],
        period=[
            app_commands.Choice(name="All-Time（全期間）", value="all"),
            app_commands.Choice(name="Monthly（今月）", value="monthly"),
            app_commands.Choice(name="Previous Month（先月）", value="prev_month"),
        ],
    )
    async def hive(
        interaction: discord.Interaction,
        gamertag: Optional[str] = None,
        game: Optional[app_commands.Choice[str]] = None,
        period: Optional[app_commands.Choice[str]] = None,
    ):
        target_tag = (gamertag or "").strip() or link_get(interaction.user.id)
        if not target_tag:
            await wait_assets()
            png = await asyncio.to_thread(
                build_notice_card,
                "ゲーマータグを指定してください",
                "ゲーマータグを入力するか、先に /hive_link で自分のタグを登録してください。",
            )
            await interaction.response.send_message(file=_file(png), ephemeral=True)
            return

        now = time.time()
        if now - _last_use.get(interaction.user.id, 0) < 4:
            await wait_assets()
            png = await asyncio.to_thread(build_notice_card, "少しお待ちください", "連続での実行を防ぐため、数秒空けてからお試しください。")
            await interaction.response.send_message(file=_file(png), ephemeral=True)
            return
        _last_use[interaction.user.id] = now
        await interaction.response.defer()
        await wait_assets()

        game_id = game.value if game else "overview"
        period_val = period.value if period else "all"
        q_name = quote(target_tag, safe="")

        try:
            async with aiohttp.ClientSession(headers={"User-Agent": USER_AGENT}) as session:
                allstats = await hive_get(session, PATH_ALL.format(name=q_name))
                main = allstats.get("main") if isinstance(allstats, dict) else None
                if allstats and not (isinstance(main, dict) and "player_number" in main):
                    mr = await hive_get(session, PATH_MAIN.format(name=q_name))
                    if isinstance(mr, dict):
                        main = mr.get("main", mr)
        except HiveRateLimited as e:
            png = await asyncio.to_thread(
                build_notice_card,
                "アクセスが集中しています",
                f"約{max(1, e.wait // 60)}分後にもう一度お試しください。",
                True,
            )
            await interaction.followup.send(file=_file(png))
            return
        except Exception as e:
            print(f"[hive] error: {e!r}")
            png = await asyncio.to_thread(
                build_notice_card,
                "データを読み込めませんでした",
                "しばらく時間を置いてからもう一度お試しください。",
                True,
            )
            await interaction.followup.send(file=_file(png))
            return

        if not allstats or not isinstance(allstats, dict):
            png = await asyncio.to_thread(
                build_notice_card,
                "プレイヤーが見つかりません",
                f"「{target_tag}」の戦績データは見つかりませんでした。",
                True,
            )
            await interaction.followup.send(file=_file(png))
            return

        view = HiveDashboardView(target_tag, game_id, period_val, "card", allstats, main or {})
        try:
            png, fname = await view._render_png()
        except HiveRateLimited as e:
            png = await asyncio.to_thread(
                build_notice_card,
                "アクセスが集中しています",
                f"約{max(1, e.wait // 60)}分後にもう一度お試しください。",
                True,
            )
            await interaction.followup.send(file=_file(png))
            return
        await interaction.followup.send(file=_file(png, fname), view=view)

    @bot.tree.command(name="hive_compare", description="2人のプレイヤーの戦績を画像でくらべます")
    @app_commands.describe(
        player1="1人目のゲーマータグ",
        player2="2人目のゲーマータグ",
        game="くらべるゲーム",
    )
    @app_commands.autocomplete(player1=gamertag_autocomplete, player2=gamertag_autocomplete)
    @app_commands.choices(game=game_choices)
    async def hive_compare(
        interaction: discord.Interaction,
        player1: str,
        player2: str,
        game: app_commands.Choice[str],
    ):
        await interaction.response.defer()
        await wait_assets()
        try:
            async with aiohttp.ClientSession(headers={"User-Agent": USER_AGENT}) as session:
                d1, d2 = await asyncio.gather(
                    hive_get(session, PATH_ALL.format(name=quote(player1.strip(), safe=""))),
                    hive_get(session, PATH_ALL.format(name=quote(player2.strip(), safe=""))),
                )
        except HiveRateLimited as e:
            png = await asyncio.to_thread(build_notice_card, "アクセスが集中しています", f"約{max(1, e.wait // 60)}分後に再度お試しください。", True)
            await interaction.followup.send(file=_file(png))
            return

        if not d1 or not d2:
            png = await asyncio.to_thread(build_notice_card, "プレイヤーが見つかりません", "指定されたプレイヤーのどちらかが見つかりませんでした。", True)
            await interaction.followup.send(file=_file(png))
            return
        s1, s2 = d1.get(game.value), d2.get(game.value)
        if not s1 or not s2:
            png = await asyncio.to_thread(build_notice_card, "比較できる記録がありません", f"{game.name} の比較に必要なプレイ記録が足りません。")
            await interaction.followup.send(file=_file(png))
            return
        png = await asyncio.to_thread(build_compare_card, game.value, player1.strip(), s1, player2.strip(), s2)
        await interaction.followup.send(file=_file(png, "hive_compare.png"))

    @bot.tree.command(name="hive_leaderboard", description="ゲームごとのトップ100ランキングを画像で表示します")
    @app_commands.describe(game="ゲーム", period="全期間 / 今月")
    @app_commands.choices(
        game=game_choices,
        period=[
            app_commands.Choice(name="全期間トップ100", value="all"),
            app_commands.Choice(name="今月トップ100", value="monthly"),
        ],
    )
    async def hive_leaderboard(
        interaction: discord.Interaction,
        game: app_commands.Choice[str],
        period: Optional[app_commands.Choice[str]] = None,
    ):
        await interaction.response.defer()
        await wait_assets()
        p_val = period.value if period else "all"
        path = PATH_LB_MONTHLY.format(game=quote(game.value, safe="")) if p_val == "monthly" else PATH_LB_ALL.format(game=quote(game.value, safe=""))
        meta_key = GAMES.get(game.value, {}).get("meta") or game.value
        try:
            async with aiohttp.ClientSession(headers={"User-Agent": USER_AGENT}) as session:
                entries, map_bytes = await asyncio.gather(
                    hive_get(session, path, ttl=CACHE_SEC),
                    get_bg_map_bytes(session, meta_key),
                )
        except HiveRateLimited as e:
            png = await asyncio.to_thread(build_notice_card, "アクセスが集中しています", f"約{max(1, e.wait // 60)}分後に再度お試しください。", True)
            await interaction.followup.send(file=_file(png))
            return
        if not isinstance(entries, list) or not entries:
            png = await asyncio.to_thread(build_notice_card, "ランキングを取得できません", f"{game.name} のランキングデータが見つかりませんでした。", True)
            await interaction.followup.send(file=_file(png))
            return
        paginator = LeaderboardPaginator(game.value, p_val, entries, map_bytes)
        await interaction.followup.send(file=await paginator.make_file(), view=paginator)

    @bot.tree.command(name="hive_global", description="Hive全体で遊んでいる累計プレイヤー数を画像で表示します")
    async def hive_global(interaction: discord.Interaction):
        await interaction.response.defer()
        await wait_assets()
        try:
            async with aiohttp.ClientSession(headers={"User-Agent": USER_AGENT}) as session:
                data = await hive_get(session, PATH_GLOBAL, ttl=META_CACHE_SEC)
        except HiveRateLimited as e:
            png = await asyncio.to_thread(build_notice_card, "アクセスが集中しています", f"約{max(1, e.wait // 60)}分後に再度お試しください。", True)
            await interaction.followup.send(file=_file(png))
            return
        up = data.get("unique_players", {}) if isinstance(data, dict) else {}
        if not up:
            png = await asyncio.to_thread(build_notice_card, "全体統計を取得できません", "しばらくしてからもう一度お試しください。", True)
            await interaction.followup.send(file=_file(png))
            return
        png = await asyncio.to_thread(build_global_card, up)
        await interaction.followup.send(file=_file(png, "hive_global.png"))

    @bot.tree.command(name="hive_maps", description="ゲームごとのマップ一覧を画像で表示します")
    @app_commands.describe(game="マップを見たいゲーム")
    @app_commands.choices(game=game_choices)
    async def hive_maps(interaction: discord.Interaction, game: app_commands.Choice[str]):
        await interaction.response.defer()
        await wait_assets()
        meta_key = GAMES.get(game.value, {}).get("meta") or game.value
        try:
            async with aiohttp.ClientSession(headers={"User-Agent": USER_AGENT}) as session:
                maps = await hive_get(session, PATH_MAPS.format(game=quote(meta_key, safe="")), ttl=META_CACHE_SEC) or []
                thumbs = await asyncio.gather(*(fetch_image_bytes(session, m.get("image")) for m in maps[:12]))
        except HiveRateLimited as e:
            png = await asyncio.to_thread(build_notice_card, "アクセスが集中しています", f"約{max(1, e.wait // 60)}分後に再度お試しください。", True)
            await interaction.followup.send(file=_file(png))
            return
        png = await asyncio.to_thread(build_maps_card, game.value, maps, list(thumbs))
        await interaction.followup.send(file=_file(png, "hive_maps.png"))


# ---------- bot本体 ----------
class HiveBot(commands.Bot):
    async def setup_hook(self):
        setup_hive(self)
        await self.tree.sync()


bot = HiveBot(command_prefix="!", intents=discord.Intents.default())


@bot.event
async def on_ready():
    print(f"起動完了: {bot.user} / サーバー数: {len(bot.guilds)}")


if __name__ == "__main__":
    token = os.getenv("DISCORD_TOKEN")
    if not token:
        raise SystemExit("環境変数 DISCORD_TOKEN を設定してください")
    bot.run(token)
