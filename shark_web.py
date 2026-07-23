"""
Shark IQ Controller — Web App
Accesible desde el navegador del celular en la red WiFi local.

Uso:
    python shark_web.py
    Luego abrir en el celu: http://<IP_DEL_PC>:8080
"""

import asyncio
import base64
import codecs
import hashlib
import io
import json
import os
import random
import re
import sqlite3
import subprocess
import sys
import threading
import time
import urllib.parse
import uuid
from contextlib import contextmanager
from datetime import datetime, timedelta, timezone
from zoneinfo import ZoneInfo
from zoneinfo import ZoneInfoNotFoundError

from flask import Flask, Response, jsonify, make_response, redirect, render_template_string, request, session, url_for

# ── Importar sharkiq ─────────────────────────────────────────────────────────
try:
    from sharkiq import get_ayla_api, OperatingModes, PowerModes, Properties
    from sharkiq.exc import SharkIqAuthError
    from sharkiq.const import (
        AUTH0_URL, AUTH0_CLIENT_ID, AUTH0_SCOPES, AUTH0_REDIRECT_URI,
        AUTH0_TOKEN_URL, LOGIN_URL, SHARK_APP_ID, SHARK_APP_SECRET,
    )
    SHARKIQ_OK = True
except ImportError:
    SHARKIQ_OK = False

# ── Configuración ─────────────────────────────────────────────────────────────
PORT        = int(os.environ.get("PORT", 8080))
CLOUD       = os.environ.get("RAILWAY_ENVIRONMENT") or os.environ.get("RENDER") or os.environ.get("CLOUD", "")
TOKEN_FILE  = os.path.join(os.path.dirname(os.path.abspath(__file__)), "shark_web_tokens.json")
BASE_DIR    = os.path.dirname(os.path.abspath(__file__))
DATA_DIR    = (os.environ.get("SHARK_DATA_DIR")
               or os.environ.get("RAILWAY_VOLUME_MOUNT_PATH")
               or BASE_DIR)
SCHEDULE_DB = os.path.join(DATA_DIR, "shark_schedules.db")
SCHEDULE_TZ_NAME = os.environ.get("SHARK_TIMEZONE", "America/Argentina/Buenos_Aires")
try:
    SCHEDULE_TZ = ZoneInfo(SCHEDULE_TZ_NAME)
except ZoneInfoNotFoundError:
    # Argentina usa UTC-3 sin horario de verano; permite ejecutar también en Windows.
    SCHEDULE_TZ = timezone(timedelta(hours=-3), name=SCHEDULE_TZ_NAME)

app = Flask(__name__)
app.secret_key = os.environ.get("SECRET_KEY") or os.urandom(24)

# ── Estado global del servidor ────────────────────────────────────────────────
_state = {
    "api":     None,
    "vacuum":  None,
    "vacuums": [],
    "session": None,
    "authed":  False,
    "mode":    "UNKNOWN",
    "battery": None,
    "rooms":   {},           # {robot_name: display_name}
    "carpet_rooms": set(),
    "map_png": None,         # bytes del PNG del mapa
    "map_ts":  None,         # timestamp de la última carga
    "login_status": "",      # mensaje para la pantalla de login
    "login_in_progress": False,
    "pkce_verifier": None,   # para OAuth web
    "pkce_redirect_uri": None,  # redirect URI usado en el último /auth/launch
    "mop_attached": None,    # GET_MopPlateAttached
    "power_mode": None,      # PowerModes: 1=Eco, 0=Normal, 2=Máxima
    "mission_complete": None,
    "docked": None,
}
_state_lock = threading.Lock()
_schedule_lock = threading.Lock()

# ── Bucle asyncio en hilo secundario ─────────────────────────────────────────
_loop = asyncio.new_event_loop()
_loop_thread = threading.Thread(target=lambda: _loop.run_forever(), daemon=True)
_loop_thread.start()


def _run_async(coro):
    """Ejecuta una coroutine en el loop secundario y espera el resultado."""
    future = asyncio.run_coroutine_threadsafe(coro, _loop)
    return future.result(timeout=60)


# ── Programación persistente ─────────────────────────────────────────────────
def _schedule_connect():
    os.makedirs(DATA_DIR, exist_ok=True)
    conn = sqlite3.connect(SCHEDULE_DB, timeout=10)
    conn.row_factory = sqlite3.Row
    return conn


@contextmanager
def _schedule_db():
    conn = _schedule_connect()
    try:
        yield conn
        conn.commit()
    except Exception:
        conn.rollback()
        raise
    finally:
        conn.close()


def _init_schedule_db():
    with _schedule_lock, _schedule_db() as conn:
        conn.execute("""
            CREATE TABLE IF NOT EXISTS schedules (
                id TEXT PRIMARY KEY,
                name TEXT NOT NULL,
                time_hm TEXT NOT NULL,
                days_json TEXT NOT NULL,
                rooms_json TEXT NOT NULL,
                enabled INTEGER NOT NULL DEFAULT 1,
                created_at TEXT NOT NULL,
                updated_at TEXT NOT NULL,
                last_run_at TEXT,
                last_run_key TEXT,
                last_status TEXT,
                last_message TEXT
            )
        """)
        conn.execute("""
            CREATE TABLE IF NOT EXISTS cleaning_missions (
                id TEXT PRIMARY KEY,
                source TEXT NOT NULL,
                title TEXT NOT NULL,
                rooms_json TEXT NOT NULL,
                schedule_ids_json TEXT NOT NULL,
                started_at TEXT NOT NULL,
                status TEXT NOT NULL,
                seen_running INTEGER NOT NULL DEFAULT 0,
                last_mode TEXT,
                completed_at TEXT
            )
        """)
        conn.execute("""
            CREATE TABLE IF NOT EXISTS notifications (
                id TEXT PRIMARY KEY,
                mission_id TEXT,
                kind TEXT NOT NULL,
                title TEXT NOT NULL,
                message TEXT NOT NULL,
                created_at TEXT NOT NULL,
                read_at TEXT
            )
        """)
        conn.execute("""
            CREATE INDEX IF NOT EXISTS idx_notifications_created
            ON notifications(created_at DESC)
        """)
        conn.execute("""
            CREATE TABLE IF NOT EXISTS robot_monitor_state (
                id INTEGER PRIMARY KEY CHECK (id = 1),
                mode TEXT,
                mission_complete INTEGER,
                docked INTEGER,
                observed_at TEXT NOT NULL
            )
        """)


def _create_cleaning_mission(source, title, rooms=None, schedule_ids=None):
    """Registra una limpieza y devuelve su id para seguirla hasta el final."""
    mission_id = uuid.uuid4().hex
    now_iso = datetime.now(SCHEDULE_TZ).isoformat()
    if _active_cleaning_mission() is not None:
        _finish_active_mission("interrupted", "REPLACED")
    with _schedule_lock, _schedule_db() as conn:
        conn.execute("""
            INSERT INTO cleaning_missions
                (id, source, title, rooms_json, schedule_ids_json, started_at, status)
            VALUES (?, ?, ?, ?, ?, ?, 'pending')
        """, (
            mission_id, source, title,
            json.dumps(list(rooms or []), ensure_ascii=False),
            json.dumps(list(schedule_ids or [])), now_iso,
        ))
    return mission_id


def _active_cleaning_mission():
    with _schedule_lock, _schedule_db() as conn:
        return conn.execute("""
            SELECT * FROM cleaning_missions
             WHERE status IN ('pending', 'running')
             ORDER BY started_at DESC LIMIT 1
        """).fetchone()


def _room_display_names(rooms):
    known = _state.get("rooms") or {}
    return [known.get(room, room) for room in rooms]


def _finish_active_mission(result="completed", mode=None, error_code=None):
    """Cierra la misión activa y crea una notificación persistente."""
    now_iso = datetime.now(SCHEDULE_TZ).isoformat()
    with _schedule_lock, _schedule_db() as conn:
        row = conn.execute("""
            SELECT * FROM cleaning_missions
             WHERE status IN ('pending', 'running')
             ORDER BY started_at DESC LIMIT 1
        """).fetchone()
        if row is None:
            return None

        rooms = json.loads(row["rooms_json"])
        schedule_ids = json.loads(row["schedule_ids_json"])
        room_names = _room_display_names(rooms)
        if result == "interrupted":
            title = "Limpieza interrumpida"
            detail = "La tarea se detuvo y el robot está regresando a la base."
            kind = "warning"
            schedule_status = "interrupted"
        elif result == "error":
            title = "Limpieza terminada con una alerta"
            detail = f"El robot dejó de limpiar e informó el error {error_code}."
            kind = "warning"
            schedule_status = "error"
        else:
            title = "Limpieza finalizada"
            detail = "El robot confirmó que la tarea terminó."
            kind = "success"
            schedule_status = "completed"
        scope = ", ".join(room_names) if room_names else "Toda la casa"
        message = f"{row['title']} · {scope}. {detail}"
        conn.execute("""
            UPDATE cleaning_missions
               SET status=?, last_mode=?, completed_at=?
             WHERE id=?
        """, (result, mode, now_iso, row["id"]))
        notification_id = uuid.uuid4().hex
        conn.execute("""
            INSERT INTO notifications
                (id, mission_id, kind, title, message, created_at)
            VALUES (?, ?, ?, ?, ?, ?)
        """, (notification_id, row["id"], kind, title, message, now_iso))
        for schedule_id in schedule_ids:
            conn.execute("""
                UPDATE schedules
                   SET last_status=?, last_message=?
                 WHERE id=?
            """, (schedule_status, message[:500], schedule_id))
    return notification_id


def _monitor_state():
    with _schedule_lock, _schedule_db() as conn:
        return conn.execute(
            "SELECT * FROM robot_monitor_state WHERE id=1"
        ).fetchone()


def _save_monitor_state(mode, mission_complete, docked):
    now_iso = datetime.now(SCHEDULE_TZ).isoformat()
    mission_value = None if mission_complete is None else int(bool(mission_complete))
    docked_value = None if docked is None else int(bool(docked))
    with _schedule_lock, _schedule_db() as conn:
        conn.execute("""
            INSERT INTO robot_monitor_state
                (id, mode, mission_complete, docked, observed_at)
            VALUES (1, ?, ?, ?, ?)
            ON CONFLICT(id) DO UPDATE SET
                mode=excluded.mode,
                mission_complete=excluded.mission_complete,
                docked=excluded.docked,
                observed_at=excluded.observed_at
        """, (mode, mission_value, docked_value, now_iso))


def _sync_active_mission(mode, error_code=None, mission_complete=None, docked=None):
    """Actualiza el seguimiento usando el estado real informado por el robot."""
    cleaning_modes = {"START", "CLEAN", "CLEANING", "MOP", "VACUUM", "VACUUM_AND_MOP"}
    terminal_modes = {"STOP", "RETURN", "RECHARGING"}
    previous = _monitor_state()
    row = _active_cleaning_mission()
    running_signal = (
        mode in cleaning_modes
        or (mission_complete is False and docked is not True)
    )
    completion_transition = bool(
        previous is not None
        and previous["mission_complete"] == 0
        and mission_complete is True
    )

    if row is None and (running_signal or completion_transition):
        _create_cleaning_mission(
            "external", "Limpieza iniciada desde otro dispositivo", []
        )
        row = _active_cleaning_mission()
    if row is None:
        _save_monitor_state(mode, mission_complete, docked)
        return
    if running_signal or completion_transition:
        with _schedule_lock, _schedule_db() as conn:
            conn.execute("""
                UPDATE cleaning_missions
                   SET status='running', seen_running=1, last_mode=?
                 WHERE id=?
            """, (mode, row["id"]))

    should_finish = bool(
        row["seen_running"]
        and (
            completion_transition
            or (mission_complete is True and (docked is True or mode in terminal_modes))
            or (mission_complete is None and mode in terminal_modes)
        )
    )
    # completion_transition puede haber creado la misión en esta misma lectura.
    if completion_transition:
        row = _active_cleaning_mission()
        should_finish = row is not None
    if should_finish:
        result = "error" if error_code not in (None, 0, "0", "") else "completed"
        _finish_active_mission(result, mode, error_code)
    _save_monitor_state(mode, mission_complete, docked)


def _list_notifications(limit=50):
    limit = max(1, min(int(limit), 100))
    with _schedule_lock, _schedule_db() as conn:
        rows = conn.execute("""
            SELECT * FROM notifications ORDER BY created_at DESC LIMIT ?
        """, (limit,)).fetchall()
        unread = conn.execute(
            "SELECT COUNT(*) FROM notifications WHERE read_at IS NULL"
        ).fetchone()[0]
    return [dict(row) for row in rows], unread


def _next_schedule_run(days, time_hm, now=None):
    now = now or datetime.now(SCHEDULE_TZ)
    hour, minute = (int(part) for part in time_hm.split(":"))
    for offset in range(8):
        date_value = (now + timedelta(days=offset)).date()
        if date_value.weekday() not in days:
            continue
        candidate = datetime(
            date_value.year, date_value.month, date_value.day,
            hour, minute, tzinfo=SCHEDULE_TZ,
        )
        if candidate > now:
            return candidate.isoformat()
    return None


def _schedule_row(row):
    days = json.loads(row["days_json"])
    rooms = json.loads(row["rooms_json"])
    return {
        "id": row["id"],
        "name": row["name"],
        "time": row["time_hm"],
        "days": days,
        "rooms": rooms,
        "enabled": bool(row["enabled"]),
        "created_at": row["created_at"],
        "updated_at": row["updated_at"],
        "last_run_at": row["last_run_at"],
        "last_status": row["last_status"],
        "last_message": row["last_message"],
        "next_run_at": _next_schedule_run(days, row["time_hm"]) if row["enabled"] else None,
    }


def _list_schedules():
    with _schedule_lock, _schedule_db() as conn:
        rows = conn.execute(
            "SELECT * FROM schedules ORDER BY time_hm, name COLLATE NOCASE"
        ).fetchall()
    return [_schedule_row(row) for row in rows]


def _validate_schedule(data, current=None):
    merged = dict(current or {})
    merged.update(data or {})
    name = str(merged.get("name", "")).strip()[:60]
    time_hm = str(merged.get("time", "")).strip()
    days = merged.get("days", [])
    rooms = merged.get("rooms", [])
    enabled = bool(merged.get("enabled", True))
    if not name:
        raise ValueError("Escribe un nombre para la tarea")
    if not re.fullmatch(r"(?:[01]\d|2[0-3]):[0-5]\d", time_hm):
        raise ValueError("La hora no es válida")
    if not isinstance(days, list):
        raise ValueError("Los días no son válidos")
    days = sorted({int(day) for day in days})
    if not days or any(day < 0 or day > 6 for day in days):
        raise ValueError("Selecciona al menos un día")
    if not isinstance(rooms, list):
        raise ValueError("Los ambientes no son válidos")
    rooms = list(dict.fromkeys(str(room).strip() for room in rooms if str(room).strip()))
    if not rooms:
        raise ValueError("Selecciona al menos un ambiente")
    return {"name": name, "time": time_hm, "days": days, "rooms": rooms, "enabled": enabled}


def _execute_room_cleaning(selected):
    vac = _state.get("vacuum")
    if not _state.get("authed") or vac is None:
        raise RuntimeError("La sesión de Shark no está conectada")
    clean_type = "wet" if _state.get("mop_attached") else "dry"
    if hasattr(vac, "async_clean_rooms"):
        try:
            _run_async(vac.async_clean_rooms(selected, clean_type=clean_type))
        except TypeError:
            _run_async(vac.async_clean_rooms(selected))
    else:
        _run_async(vac.async_set_operating_mode(
            OperatingModes.START, room_names=selected
        ))
    return clean_type


def _record_schedule_result(schedule_id, run_key, status, message):
    now_iso = datetime.now(SCHEDULE_TZ).isoformat()
    with _schedule_lock, _schedule_db() as conn:
        conn.execute("""
            UPDATE schedules
               SET last_run_at=?, last_run_key=?, last_status=?, last_message=?
             WHERE id=?
        """, (now_iso, run_key, status, str(message)[:500], schedule_id))


def _run_due_schedules():
    now = datetime.now(SCHEDULE_TZ)
    minute_key = now.strftime("%Y-%m-%dT%H:%M")
    with _schedule_lock, _schedule_db() as conn:
        rows = conn.execute(
            "SELECT * FROM schedules WHERE enabled=1 AND time_hm=?",
            (now.strftime("%H:%M"),),
        ).fetchall()
        due = []
        for row in rows:
            if now.weekday() not in json.loads(row["days_json"]):
                continue
            run_key = f"{row['id']}:{minute_key}"
            if row["last_run_key"] == run_key:
                continue
            conn.execute(
                "UPDATE schedules SET last_run_key=?, last_status=?, last_message=? WHERE id=?",
                (run_key, "running", "Iniciando limpieza", row["id"]),
            )
            due.append((row, run_key))

    if not due:
        return

    # Si dos tareas coinciden exactamente, combina sus ambientes en una sola misión.
    combined_rooms = []
    for row, _ in due:
        for room in json.loads(row["rooms_json"]):
            if room not in combined_rooms:
                combined_rooms.append(room)
    try:
        clean_type = _execute_room_cleaning(combined_rooms)
        task_names = [row["name"] for row, _ in due]
        mission_title = task_names[0] if len(task_names) == 1 else "Tareas: " + ", ".join(task_names)
        _create_cleaning_mission(
            "scheduled", mission_title, combined_rooms,
            schedule_ids=[row["id"] for row, _ in due],
        )
        for row, run_key in due:
            own_rooms = json.loads(row["rooms_json"])
            _record_schedule_result(
                row["id"], run_key, "running",
                f"Limpieza iniciada ({clean_type}): {', '.join(own_rooms)}",
            )
    except Exception as exc:
        for row, run_key in due:
            _record_schedule_result(row["id"], run_key, "error", exc)


def _schedule_worker():
    while True:
        try:
            _run_due_schedules()
        except Exception as exc:
            print(f"[SCHEDULE] Error: {exc}", flush=True)
        time.sleep(15)


def _mission_monitor_worker():
    """Detecta limpiezas iniciadas desde la app, Shark o asistentes de voz."""
    while True:
        try:
            if _state.get("authed"):
                _refresh_state()
        except Exception as exc:
            print(f"[MISSION] Error: {exc}", flush=True)
        time.sleep(30)


# ── PKCE ─────────────────────────────────────────────────────────────────────
def _pkce_generate():
    chars = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789"
    verifier  = "".join(random.choice(chars) for _ in range(43))
    state_val = "".join(random.choice(chars) for _ in range(43))
    digest    = hashlib.sha256(codecs.encode(verifier, "utf-8")).digest()
    challenge = (base64.b64encode(digest).decode()
                 .replace("+", "-").replace("/", "_").replace("=", "").replace("$", ""))
    return verifier, challenge, state_val


def _build_auth_url(verifier, challenge, state_val, override_redirect=None):
    params = {
        "os": "ios",
        "response_type": "code",
        "mobile_shark_app_version": "rn1.01",
        "client_id": AUTH0_CLIENT_ID,
        "state": state_val,
        "scope": AUTH0_SCOPES,
        "redirect_uri": override_redirect or AUTH0_REDIRECT_URI,
        "code_challenge": challenge,
        "screen_hint": "signin",
        "code_challenge_method": "S256",
        "ui_locales": "en",
    }
    return AUTH0_URL + "/authorize?" + urllib.parse.urlencode(params)


# ── Tokens persistentes ───────────────────────────────────────────────────────
def _save_tokens(data: dict):
    try:
        with open(TOKEN_FILE, "w") as f:
            json.dump(data, f)
    except Exception:
        pass


def _load_tokens() -> dict | None:
    if os.path.exists(TOKEN_FILE):
        try:
            with open(TOKEN_FILE) as f:
                return json.load(f)
        except Exception:
            pass
    env_tokens = os.environ.get("SHARK_TOKENS", "").strip()
    if env_tokens:
        try:
            return json.loads(env_tokens)
        except Exception:
            pass
    return None


# ── Inicializar sesión desde tokens guardados ─────────────────────────────────
async def _init_from_tokens(tokens: dict):
    import aiohttp
    sess = aiohttp.ClientSession()
    try:
        id_token   = tokens["auth0_id_token"]
        ayla_token = tokens["ayla_access_token"]
        refresh    = tokens.get("ayla_refresh_token")

        api = get_ayla_api("", "", websession=sess)
        api._auth0_id_token  = id_token
        api._access_token    = ayla_token
        api._refresh_token   = refresh
        api._auth_expiration = datetime.now() + timedelta(hours=1)
        api._is_authed       = True

        vacuums = []
        try:
            raw = await api.async_list_devices()
            vacuums = await api.async_get_devices(update=False)
            for v in vacuums:
                try:
                    await v.async_update()
                except Exception:
                    pass
        except Exception:
            pass

        if not vacuums:
            from sharkiq import SkegoxApi, SkegoxAuthManager, SkegoxDevice
            from sharkiq.const import REGION_ELSEWHERE
            from datetime import timezone
            token_store = {
                "auth0_id_token":      id_token,
                "auth0_refresh_token": tokens.get("auth0_refresh_token"),
                "auth0_access_token":  tokens.get("auth0_access_token"),
                "auth0_expiry":        tokens.get("auth0_expiry", ""),
            }
            skegox_auth = SkegoxAuthManager("", "", region=REGION_ELSEWHERE, token_store=token_store)
            skegox_api  = SkegoxApi(skegox_auth)
            await skegox_api.discover()
            device_dicts = await skegox_api.get_all_devices()
            if device_dicts:
                vacuums = [_SkegoxWrapper(SkegoxDevice(skegox_api, d), skegox_api)
                           for d in device_dicts]
                api = skegox_api

        return api, vacuums, sess
    except Exception:
        await sess.close()
        raise


# ── Wrapper Skegox → interfaz común ──────────────────────────────────────────
class _SkegoxWrapper:
    def __init__(self, dev, s_api):
        self._dev  = dev
        self._sapi = s_api

    @property
    def name(self):
        return self._dev.name

    @property
    def operating_mode(self):
        val = self._dev.get_property_value("GET_Operating_Mode")
        if val is None:
            return None
        try:
            return OperatingModes(val)
        except Exception:
            return val

    def get_property_value(self, prop):
        return self._dev.get_property_value(prop)

    async def async_update(self):
        data = await self._sapi.get_device(self._dev._snd)
        self._dev.update_from_response(data)

    async def async_set_operating_mode(self, mode):
        await self._dev.async_set_operating_mode(mode)

    async def async_set_power_mode(self, mode):
        await self._dev.async_set_property_value(Properties.POWER_MODE, mode)

    async def async_clean_rooms(self, rooms, clean_type='dry'):
        dev = self._dev
        # Respetar _has_areas_v3 de la librería — no forzar V3
        has_v3 = getattr(dev, '_has_areas_v3', False)
        if has_v3 and hasattr(self._sapi, 'clean_rooms'):
            # V3: pasar clean_type para controlar inclusión de alfombras
            await self._sapi.clean_rooms(
                snd=dev._snd,
                rooms=rooms,
                floor_id=getattr(dev, '_floor_id', ''),
                clean_type=clean_type,
                use_v3=True,
            )
        else:
            # V2 o Ayla: usar método original de la librería
            await dev.async_clean_rooms(rooms)


# ── Mapeo de modo a texto/color ───────────────────────────────────────────────
MODE_MAP = {
    "START":      ("▶ Limpiando",        "#3fb950"),
    "STOP":       ("⏹ Detenido",         "#f85149"),
    "PAUSE":      ("⏸ Pausado",          "#e3b341"),
    "RETURN":     ("🏠 Volviendo a base", "#58a6ff"),
    "RECHARGING": ("🔌 Cargando",         "#3fb950"),
    "UNKNOWN":    ("● Desconocido",       "#8b949e"),
}


def _read_bool_property(vac, *property_names):
    for property_name in property_names:
        try:
            value = vac.get_property_value(property_name)
        except Exception:
            continue
        if value is None:
            continue
        if isinstance(value, bool):
            return value
        if isinstance(value, (int, float)):
            return bool(value)
        normalized = str(value).strip().lower()
        if normalized in ("true", "1", "yes", "on"):
            return True
        if normalized in ("false", "0", "no", "off", ""):
            return False
    return None


def _resolve_mode(vac):
    """Devuelve (mode_key, mode_text, mode_color, battery)."""
    battery = None
    try:
        battery = vac.get_property_value("GET_Battery_Capacity")
        if battery is not None:
            battery = int(battery)
    except Exception:
        pass

    mode_name = "UNKNOWN"
    try:
        om = vac.operating_mode
        if om is not None:
            if hasattr(om, "name"):
                mode_name = om.name.upper()
            else:
                mode_name = str(om).upper()
    except Exception:
        pass

    # Sobrescribir con estado de carga real
    try:
        charging = _read_bool_property(vac, "GET_Charging_Status", "Charging_Status")
        docked = _read_bool_property(
            vac, "GET_DockedStatus", "GET_Docked_Status", "DockedStatus"
        )
        if (charging or docked) and mode_name in ("RETURN", "STOP", "UNKNOWN"):
            mode_name = "RECHARGING"
    except Exception:
        pass

    text, color = MODE_MAP.get(mode_name, (f"● {mode_name}", "#8b949e"))
    return mode_name, text, color, battery


# ── Actualizar estado global ──────────────────────────────────────────────────
def _refresh_state():
    vac = _state["vacuum"]
    if vac is None:
        return
    try:
        _run_async(vac.async_update())
        mode_key, mode_text, mode_color, battery = _resolve_mode(vac)
        power_mode = None
        try:
            value = vac.get_property_value(Properties.POWER_MODE)
            if value is not None:
                power_mode = int(value)
        except Exception:
            pass
        error_code = None
        try:
            error_code = getattr(vac, "error_code", None)
            if callable(error_code):
                error_code = error_code()
        except Exception:
            error_code = None
        if error_code is None:
            for property_name in ("GET_Error_Code", "Error_Code"):
                try:
                    error_code = vac.get_property_value(property_name)
                    if error_code is not None:
                        break
                except Exception:
                    pass
        mission_complete = _read_bool_property(
            vac, "GET_MissionComplete", "MissionComplete",
            "GET_CleanComplete", "CleanComplete",
        )
        docked = _read_bool_property(
            vac, "GET_DockedStatus", "GET_Docked_Status", "DockedStatus"
        )
        # Leer estado de la almohadilla
        mop_attached = None
        try:
            dev = getattr(vac, "_dev", vac)
            props = getattr(dev, "properties_full", {})
            val = props.get("GET_MopPlateAttached")
            if val is not None:
                # properties_full stores {"value": ...} dicts
                if isinstance(val, dict):
                    val = val.get("value")
                if val is not None:
                    if isinstance(val, bool):
                        mop_attached = val
                    elif isinstance(val, int):
                        mop_attached = bool(val)
                    else:
                        mop_attached = str(val).lower() in ("true", "1", "yes")
        except Exception:
            pass
        with _state_lock:
            _state["mode"]        = mode_key
            _state["mode_text"]   = mode_text
            _state["mode_color"]  = mode_color
            _state["battery"]     = battery
            _state["mop_attached"] = mop_attached
            _state["power_mode"]   = power_mode
            _state["mission_complete"] = mission_complete
            _state["docked"] = docked
        _sync_active_mission(
            mode_key, error_code,
            mission_complete=mission_complete, docked=docked,
        )
    except Exception as e:
        pass


# ── Rutas Flask ───────────────────────────────────────────────────────────────

@app.route("/")
def index():
    if not _state["authed"]:
        return redirect(url_for("login_page"))
    return redirect(url_for("dashboard"))


@app.route("/login")
def login_page():
    if _state["authed"]:
        return redirect(url_for("dashboard"))
    resp = make_response(render_template_string(LOGIN_HTML,
        status=_state["login_status"],
        in_progress=False,
        is_cloud=bool(CLOUD)))   # nunca auto-arrancar
    resp.headers["Cache-Control"] = "no-store, no-cache, must-revalidate, max-age=0"
    resp.headers["Pragma"] = "no-cache"
    return resp


@app.route("/auth/start", methods=["POST"])
def auth_start():
    """Inicia el flujo OAuth abriendo el navegador del PC."""
    if CLOUD:
        return jsonify({"ok": False, "msg": "❌ Browser auth no disponible en cloud. Usa email+contraseña."})
    if _state["login_in_progress"]:
        print("[AUTH] start ignorado — login ya en progreso", flush=True)
        return jsonify({"ok": False, "msg": "Login ya en progreso"})

    with _state_lock:
        _state["login_in_progress"] = True
        _state["login_status"] = "⏳ Abriendo el navegador del PC..."

    print("[AUTH] Iniciando login por navegador (pywebview)...", flush=True)

    def _do_login():
        verifier, challenge, state_val = _pkce_generate()
        auth_url = _build_auth_url(verifier, challenge, state_val)
        script = os.path.join(BASE_DIR, "shark_browser_auth.py")
        print(f"[AUTH] Lanzando subprocess: {script}", flush=True)
        try:
            result = subprocess.run(
                [sys.executable, script, auth_url],
                capture_output=True, text=True, timeout=300
            )
            redirect_url = result.stdout.strip()
            print(f"[AUTH] subprocess OK — stdout={repr(redirect_url[:80] if redirect_url else '')} stderr={repr(result.stderr[:120] if result.stderr else '')}", flush=True)
        except subprocess.TimeoutExpired:
            print("[AUTH] subprocess TIMEOUT", flush=True)
            with _state_lock:
                _state["login_status"] = "❌ Tiempo agotado. Intenta de nuevo."
                _state["login_in_progress"] = False
            return
        except Exception as e:
            print(f"[AUTH] subprocess EXCEPTION: {e}", flush=True)
            with _state_lock:
                _state["login_status"] = f"❌ Error: {e}"
                _state["login_in_progress"] = False
            return

        if not redirect_url or redirect_url.startswith("ERROR:"):
            print(f"[AUTH] subprocess ERROR: {repr(redirect_url)}", flush=True)
            with _state_lock:
                _state["login_status"] = f"❌ {redirect_url or 'Login cancelado'}. Intenta de nuevo."
                _state["login_in_progress"] = False
            return

        # Extraer code
        parsed = urllib.parse.urlparse(redirect_url)
        params = urllib.parse.parse_qs(parsed.query)
        code = params.get("code", [None])[0]
        if not code:
            with _state_lock:
                _state["login_status"] = "❌ No se obtuvo código. Intenta de nuevo."
                _state["login_in_progress"] = False
            return

        with _state_lock:
            _state["login_status"] = "⏳ Autenticando con Shark..."

        try:
            import aiohttp as _aiohttp
            async def _exchange():
                sess = _aiohttp.ClientSession()
                try:
                    token_payload = {
                        "grant_type": "authorization_code",
                        "client_id": AUTH0_CLIENT_ID,
                        "code": code,
                        "redirect_uri": AUTH0_REDIRECT_URI,
                        "code_verifier": verifier,
                    }
                    async with sess.post(AUTH0_TOKEN_URL, json=token_payload) as r:
                        token_data = await r.json()

                    id_token = token_data.get("id_token")
                    if not id_token:
                        raise RuntimeError(f"Sin id_token: {token_data}")

                    ayla_payload = {
                        "app_id": SHARK_APP_ID,
                        "app_secret": SHARK_APP_SECRET,
                        "token": id_token,
                    }
                    async with sess.post(f"{LOGIN_URL}/api/v1/token_sign_in",
                                         json=ayla_payload,
                                         headers={"Content-Type": "application/json",
                                                  "User-Agent": "Mozilla/5.0"}) as r:
                        ayla_data = await r.json()

                    if "access_token" not in ayla_data:
                        raise RuntimeError(f"Sin access_token: {ayla_data}")

                    return sess, id_token, token_data, ayla_data
                except Exception:
                    await sess.close()
                    raise

            sess, id_token, token_data, ayla_data = _run_async(_exchange())

            # Guardar tokens
            from datetime import timezone
            tokens = {
                "auth0_id_token":      id_token,
                "auth0_refresh_token": token_data.get("refresh_token"),
                "auth0_access_token":  token_data.get("access_token"),
                "auth0_expiry":        (
                    datetime.now(timezone.utc)
                    + timedelta(seconds=token_data.get("expires_in", 86400))
                ).isoformat(),
                "ayla_access_token":   ayla_data["access_token"],
                "ayla_refresh_token":  ayla_data.get("refresh_token"),
            }
            _save_tokens(tokens)

            # Crear API y obtener dispositivos
            api = get_ayla_api("", "", websession=sess)
            api._auth0_id_token  = id_token
            api._access_token    = ayla_data["access_token"]
            api._refresh_token   = ayla_data.get("refresh_token")
            api._auth_expiration = datetime.now() + timedelta(hours=1)
            api._is_authed       = True

            vacuums = []
            try:
                raw = _run_async(api.async_list_devices())
                vacuums = _run_async(api.async_get_devices(update=False))
                for v in vacuums:
                    try:
                        _run_async(v.async_update())
                    except Exception:
                        pass
            except Exception:
                pass

            if not vacuums:
                from sharkiq import SkegoxApi, SkegoxAuthManager, SkegoxDevice
                from sharkiq.const import REGION_ELSEWHERE
                from datetime import timezone as tz
                token_store = {
                    "auth0_id_token":      id_token,
                    "auth0_refresh_token": token_data.get("refresh_token"),
                    "auth0_access_token":  token_data.get("access_token"),
                    "auth0_expiry":        tokens["auth0_expiry"],
                }
                skegox_auth = SkegoxAuthManager("", "", region=REGION_ELSEWHERE,
                                                token_store=token_store)
                skegox_api = SkegoxApi(skegox_auth)
                _run_async(skegox_api.discover())
                device_dicts = _run_async(skegox_api.get_all_devices())
                if device_dicts:
                    from sharkiq import SkegoxDevice
                    vacuums = [_SkegoxWrapper(SkegoxDevice(skegox_api, d), skegox_api)
                               for d in device_dicts]
                    api = skegox_api

            with _state_lock:
                _state["api"]        = api
                _state["vacuums"]    = vacuums
                _state["vacuum"]     = vacuums[0] if vacuums else None
                _state["authed"]     = bool(vacuums)
                _state["login_in_progress"] = False
                _state["login_status"] = (
                    f"✓ Conectado — {vacuums[0].name}" if vacuums
                    else "❌ No se encontraron robots."
                )

            if vacuums:
                _refresh_state()

        except Exception as e:
            with _state_lock:
                _state["login_status"] = f"❌ Error: {e}"
                _state["login_in_progress"] = False

    threading.Thread(target=_do_login, daemon=True).start()
    return jsonify({"ok": True})


@app.route("/auth/status")
def auth_status():
    return jsonify({
        "authed":      _state["authed"],
        "in_progress": _state["login_in_progress"],
        "msg":         _state["login_status"],
    })


@app.route("/auth/launch")
def auth_launch():
    """Genera PKCE, guarda el verifier y redirige directo al login de Auth0."""
    verifier, challenge, state_val = _pkce_generate()
    with _state_lock:
        _state["pkce_verifier"]     = verifier
        _state["pkce_redirect_uri"] = AUTH0_REDIRECT_URI
    auth_url = _build_auth_url(verifier, challenge, state_val)
    return redirect(auth_url, code=302)


@app.route("/auth/launch-fallback")
def auth_launch_fallback():
    """Igual que /auth/launch pero usa la URI mobile original (para Firefox)."""
    verifier, challenge, state_val = _pkce_generate()
    with _state_lock:
        _state["pkce_verifier"]     = verifier
        _state["pkce_redirect_uri"] = AUTH0_REDIRECT_URI
    auth_url = _build_auth_url(verifier, challenge, state_val)
    return redirect(auth_url, code=302)


@app.route("/auth/callback")
def auth_callback():
    """Auth0 redirige aquí con el código de autorización (flujo web)."""
    error = request.args.get("error")
    code  = request.args.get("code")

    if error or not code:
        msg = request.args.get("error_description", error or "No se recibió código")
        fallback_url = request.url_root.rstrip('/') + '/auth/launch-fallback'
        return f"""<!DOCTYPE html><html><head><meta charset="UTF-8"><title>Shark IQ</title>
<style>*{{box-sizing:border-box;margin:0;padding:0}}body{{background:#070D18;color:#E8F3FF;
font-family:'Segoe UI',sans-serif;display:flex;align-items:center;justify-content:center;
min-height:100vh;padding:20px}}.c{{background:#0C1520;border:1px solid #1B2C40;border-radius:16px;
padding:32px 24px;max-width:380px;text-align:center}}a{{color:#2896FF}}code{{color:#AAD4FF;
font-size:11px}}</style></head><body><div class="c">
<p style="font-size:28px;margin-bottom:10px">&#10060;</p>
<p style="font-weight:700;margin-bottom:8px">Auth0 no aceptó la redirecci&oacute;n</p>
<p style="color:#5E7E9A;font-size:13px;margin-bottom:16px">{msg}</p>
<p style="font-size:13px;color:#5E7E9A">Cerrá esta pestaña, abrí <strong>Firefox</strong>
y andá a:<br><a href="{fallback_url}" target="_blank" style="font-size:12px">/auth/launch-fallback</a><br><br>
Después copiá la URL que aparece en la barra de Firefox<br>(empieza con <code>com.sharkninja.shark://</code>)
y pegala en la pestaña principal de Shark IQ.</p>
</div></body></html>""", 400

    with _state_lock:
        verifier     = _state.get("pkce_verifier")
        redirect_uri = _state.get("pkce_redirect_uri") or (request.url_root.rstrip('/') + '/auth/callback')
        if verifier:
            _state["pkce_verifier"] = None
        if _state["login_in_progress"]:
            return _CALLBACK_WAITING_HTML
        _state["login_in_progress"] = True
        _state["login_status"] = "\u23f3 Autenticando..."

    if not verifier:
        return "<p style='font-family:sans-serif;padding:20px'>Sesi&oacute;n expirada &mdash; cerrá esta pestaña y reintentá</p>", 400

    def _do_callback():
        try:
            import aiohttp as _aiohttp
            async def _exchange():
                sess = _aiohttp.ClientSession()
                try:
                    token_payload = {
                        "grant_type": "authorization_code",
                        "client_id": AUTH0_CLIENT_ID,
                        "code": code,
                        "redirect_uri": redirect_uri,
                        "code_verifier": verifier,
                    }
                    async with sess.post(AUTH0_TOKEN_URL, json=token_payload) as r:
                        token_data = await r.json()
                    id_token = token_data.get("id_token")
                    if not id_token:
                        raise RuntimeError(f"Sin id_token: {token_data}")
                    ayla_payload = {
                        "app_id": SHARK_APP_ID,
                        "app_secret": SHARK_APP_SECRET,
                        "token": id_token,
                    }
                    async with sess.post(f"{LOGIN_URL}/api/v1/token_sign_in",
                                         json=ayla_payload,
                                         headers={"Content-Type": "application/json",
                                                  "User-Agent": "Mozilla/5.0"}) as r:
                        ayla_data = await r.json()
                    if "access_token" not in ayla_data:
                        raise RuntimeError(f"Sin access_token: {ayla_data}")
                    return sess, id_token, token_data, ayla_data
                except Exception:
                    await sess.close()
                    raise

            sess, id_token, token_data, ayla_data = _run_async(_exchange())

            from datetime import timezone
            tokens = {
                "auth0_id_token":      id_token,
                "auth0_refresh_token": token_data.get("refresh_token"),
                "auth0_access_token":  token_data.get("access_token"),
                "auth0_expiry":        (
                    datetime.now(timezone.utc)
                    + timedelta(seconds=token_data.get("expires_in", 86400))
                ).isoformat(),
                "ayla_access_token":  ayla_data["access_token"],
                "ayla_refresh_token": ayla_data.get("refresh_token"),
            }
            _save_tokens(tokens)

            api = get_ayla_api("", "", websession=sess)
            api._auth0_id_token  = id_token
            api._access_token    = ayla_data["access_token"]
            api._refresh_token   = ayla_data.get("refresh_token")
            api._auth_expiration = datetime.now() + timedelta(hours=1)
            api._is_authed       = True

            vacuums = []
            try:
                vacuums = _run_async(api.async_get_devices(update=False))
                for v in vacuums:
                    try: _run_async(v.async_update())
                    except: pass
            except: pass

            if not vacuums:
                from sharkiq import SkegoxApi, SkegoxAuthManager, SkegoxDevice
                from sharkiq.const import REGION_ELSEWHERE
                token_store = {
                    "auth0_id_token":      id_token,
                    "auth0_refresh_token": token_data.get("refresh_token"),
                    "auth0_access_token":  token_data.get("access_token"),
                    "auth0_expiry":        tokens["auth0_expiry"],
                }
                skegox_auth = SkegoxAuthManager("", "", region=REGION_ELSEWHERE, token_store=token_store)
                skegox_api  = SkegoxApi(skegox_auth)
                _run_async(skegox_api.discover())
                device_dicts = _run_async(skegox_api.get_all_devices())
                if device_dicts:
                    vacuums = [_SkegoxWrapper(SkegoxDevice(skegox_api, d), skegox_api) for d in device_dicts]
                    api = skegox_api

            with _state_lock:
                _state["api"]        = api
                _state["vacuums"]    = vacuums
                _state["vacuum"]     = vacuums[0] if vacuums else None
                _state["authed"]     = bool(vacuums)
                _state["login_in_progress"] = False
                _state["login_status"] = (
                    f"\u2713 Conectado \u2014 {vacuums[0].name}" if vacuums
                    else "\u274c No se encontraron robots."
                )
            if vacuums:
                _refresh_state()
        except Exception as exc:
            with _state_lock:
                _state["login_status"] = f"\u274c Error: {str(exc)[:120]}"
                _state["login_in_progress"] = False

    threading.Thread(target=_do_callback, daemon=True).start()
    return _CALLBACK_WAITING_HTML


# HTML minimo para la pestaña de callback
_CALLBACK_WAITING_HTML = """<!DOCTYPE html><html><head><meta charset="UTF-8">
<title>Shark IQ \u2014 Auth</title><style>*{box-sizing:border-box;margin:0;padding:0}
body{background:#070D18;color:#E8F3FF;font-family:'Segoe UI',sans-serif;
display:flex;align-items:center;justify-content:center;min-height:100vh;padding:20px}
.c{background:#0C1520;border:1px solid #1B2C40;border-radius:16px;
padding:32px 24px;max-width:320px;text-align:center}
.sp{display:inline-block;width:32px;height:32px;border:3px solid #1B2C40;
border-top-color:#2896FF;border-radius:50%;animation:spin .8s linear infinite;margin-bottom:16px}
@keyframes spin{to{transform:rotate(360deg)}}
</style></head><body><div class="c">
<div class="sp"></div>
<p style="font-size:16px;font-weight:700" id="ttl">Completando autenticaci&#xf3;n...</p>
<p style="color:#5E7E9A;font-size:13px;margin-top:8px" id="msg">Podés cerrar esta pesta&#xf1;a cuando termine</p>
</div>
<script>
function poll(){
  fetch('/auth/status').then(r=>r.json()).then(d=>{
    if(d.authed){
      document.querySelector('.sp').style.display='none';
      document.getElementById('ttl').textContent='\u2705 Login completado';
      document.getElementById('msg').textContent='Volvé a la pestaña de Shark IQ';
      setTimeout(()=>window.close(),2000);
    } else if(d.msg && d.msg.startsWith('\u274c')){
      document.querySelector('.sp').style.display='none';
      document.getElementById('ttl').textContent=d.msg;
      document.getElementById('msg').textContent='Cerrá esta pestaña y reintentá';
    } else { setTimeout(poll,1000); }
  }).catch(()=>setTimeout(poll,1500));
}
setTimeout(poll,600);
</script></body></html>"""


@app.route("/auth/browser-url")
def auth_browser_url():
    """Genera la URL de Auth0 para el flujo OAuth web (cloud)."""
    verifier, challenge, state_val = _pkce_generate()
    with _state_lock:
        _state["pkce_verifier"] = verifier
    auth_url = _build_auth_url(verifier, challenge, state_val)
    return jsonify({"ok": True, "url": auth_url})


@app.route("/auth/browser-code", methods=["POST"])
def auth_browser_code():
    """Recibe la URL de redirección copiada del navegador y completa el login."""
    if _state["login_in_progress"]:
        return jsonify({"ok": False, "msg": "Login ya en progreso"})

    data = request.get_json(force=True) or {}
    redirect_url = (data.get("redirect_url") or "").strip()

    verifier = _state.get("pkce_verifier")
    if not verifier:
        return jsonify({"ok": False, "msg": "Sesión expirada — obtené una nueva URL."})

    # Extraer code de la URL de redirección (esquema com.sharkninja.shark://...?code=...)
    code = None
    try:
        if "?" in redirect_url:
            query_str = redirect_url.split("?", 1)[1]
            params = urllib.parse.parse_qs(query_str)
            code = params.get("code", [None])[0]
    except Exception:
        pass

    if not code:
        return jsonify({"ok": False, "msg": "URL inválida — no se encontró el código. Copiá la URL completa."})

    with _state_lock:
        _state["login_in_progress"] = True
        _state["login_status"] = "⏳ Autenticando con Shark..."
        _state["pkce_verifier"] = None

    def _do_web():
        try:
            import aiohttp as _aiohttp
            async def _exchange():
                sess = _aiohttp.ClientSession()
                try:
                    token_payload = {
                        "grant_type": "authorization_code",
                        "client_id": AUTH0_CLIENT_ID,
                        "code": code,
                        "redirect_uri": AUTH0_REDIRECT_URI,
                        "code_verifier": verifier,
                    }
                    async with sess.post(AUTH0_TOKEN_URL, json=token_payload) as r:
                        token_data = await r.json()
                    id_token = token_data.get("id_token")
                    if not id_token:
                        raise RuntimeError(f"Sin id_token: {token_data}")
                    ayla_payload = {
                        "app_id": SHARK_APP_ID,
                        "app_secret": SHARK_APP_SECRET,
                        "token": id_token,
                    }
                    async with sess.post(f"{LOGIN_URL}/api/v1/token_sign_in",
                                         json=ayla_payload,
                                         headers={"Content-Type": "application/json",
                                                  "User-Agent": "Mozilla/5.0"}) as r:
                        ayla_data = await r.json()
                    if "access_token" not in ayla_data:
                        raise RuntimeError(f"Sin access_token: {ayla_data}")
                    return sess, id_token, token_data, ayla_data
                except Exception:
                    await sess.close()
                    raise

            sess, id_token, token_data, ayla_data = _run_async(_exchange())

            from datetime import timezone
            tokens = {
                "auth0_id_token":      id_token,
                "auth0_refresh_token": token_data.get("refresh_token"),
                "auth0_access_token":  token_data.get("access_token"),
                "auth0_expiry":        (
                    datetime.now(timezone.utc)
                    + timedelta(seconds=token_data.get("expires_in", 86400))
                ).isoformat(),
                "ayla_access_token":   ayla_data["access_token"],
                "ayla_refresh_token":  ayla_data.get("refresh_token"),
            }
            _save_tokens(tokens)

            api = get_ayla_api("", "", websession=sess)
            api._auth0_id_token  = id_token
            api._access_token    = ayla_data["access_token"]
            api._refresh_token   = ayla_data.get("refresh_token")
            api._auth_expiration = datetime.now() + timedelta(hours=1)
            api._is_authed       = True

            vacuums = []
            try:
                vacuums = _run_async(api.async_get_devices(update=False))
                for v in vacuums:
                    try: _run_async(v.async_update())
                    except: pass
            except: pass

            if not vacuums:
                from sharkiq import SkegoxApi, SkegoxAuthManager, SkegoxDevice
                from sharkiq.const import REGION_ELSEWHERE
                token_store = {
                    "auth0_id_token":      id_token,
                    "auth0_refresh_token": token_data.get("refresh_token"),
                    "auth0_access_token":  token_data.get("access_token"),
                    "auth0_expiry":        tokens["auth0_expiry"],
                }
                skegox_auth = SkegoxAuthManager("", "", region=REGION_ELSEWHERE, token_store=token_store)
                skegox_api  = SkegoxApi(skegox_auth)
                _run_async(skegox_api.discover())
                device_dicts = _run_async(skegox_api.get_all_devices())
                if device_dicts:
                    vacuums = [_SkegoxWrapper(SkegoxDevice(skegox_api, d), skegox_api) for d in device_dicts]
                    api = skegox_api

            with _state_lock:
                _state["api"]        = api
                _state["vacuums"]    = vacuums
                _state["vacuum"]     = vacuums[0] if vacuums else None
                _state["authed"]     = bool(vacuums)
                _state["login_in_progress"] = False
                _state["login_status"] = (
                    f"✓ Conectado — {vacuums[0].name}" if vacuums
                    else "❌ No se encontraron robots."
                )
            if vacuums:
                _refresh_state()
        except Exception as exc:
            with _state_lock:
                _state["login_status"] = f"❌ Error: {str(exc)[:120]}"
                _state["login_in_progress"] = False

    threading.Thread(target=_do_web, daemon=True).start()
    return jsonify({"ok": True})


@app.route("/auth/restore-tokens", methods=["POST"])
def auth_restore_tokens():
    """Acepta el JSON del shark_web_tokens.json local y restaura la sesión."""
    if _state["login_in_progress"]:
        return jsonify({"ok": False, "msg": "Login ya en progreso"})
    data = request.get_json(force=True) or {}
    token_str = (data.get("tokens") or "").strip()
    try:
        tokens = json.loads(token_str)
    except Exception:
        return jsonify({"ok": False, "msg": "JSON inválido — copiá el archivo completo"})
    for k in ("auth0_id_token", "ayla_access_token"):
        if k not in tokens:
            return jsonify({"ok": False, "msg": f"Falta campo: {k}"})
    with _state_lock:
        _state["login_in_progress"] = True
        _state["login_status"] = "\u23f3 Restaurando sesión..."
    def _do_restore():
        try:
            api, vacuums, sess = _run_async(_init_from_tokens(tokens))
            if vacuums:
                _save_tokens(tokens)
            with _state_lock:
                _state["api"]        = api
                _state["vacuums"]    = vacuums
                _state["vacuum"]     = vacuums[0] if vacuums else None
                _state["authed"]     = bool(vacuums)
                _state["login_in_progress"] = False
                _state["login_status"] = (
                    f"\u2713 Sesión restaurada \u2014 {vacuums[0].name}" if vacuums
                    else "\u274c No se encontraron robots."
                )
            if vacuums:
                _refresh_state()
        except Exception as exc:
            with _state_lock:
                _state["login_status"] = f"\u274c Error: {str(exc)[:120]}"
                _state["login_in_progress"] = False
    threading.Thread(target=_do_restore, daemon=True).start()
    return jsonify({"ok": True})


@app.route("/auth/email", methods=["POST"])
def auth_email():
    """Login con email + contraseña (alternativa al navegador)."""
    if _state["login_in_progress"]:
        return jsonify({"ok": False, "msg": "Login ya en progreso"})
    data  = request.get_json(force=True) or {}
    email = (data.get("email") or "").strip()
    pwd   = data.get("password") or ""
    if not email or not pwd:
        return jsonify({"ok": False, "msg": "Email y contraseña requeridos"})

    with _state_lock:
        _state["login_in_progress"] = True
        _state["login_status"] = "⏳ Verificando credenciales..."

    def _do():
        import aiohttp as _aio

        async def _login():
            sess = _aio.ClientSession()
            try:
                api = get_ayla_api(email, pwd, websession=sess)
                await api.async_sign_in()
                vacuums = await api.async_get_devices(update=False)
                for v in vacuums:
                    try:
                        await v.async_update()
                    except Exception:
                        pass

                # Fallback: modelo nuevo → usar SkegoxApi con email+contraseña
                if not vacuums:
                    from sharkiq import SkegoxApi, SkegoxAuthManager, SkegoxDevice
                    from sharkiq.const import REGION_ELSEWHERE
                    skegox_auth = SkegoxAuthManager(email, pwd, region=REGION_ELSEWHERE)
                    skegox_api  = SkegoxApi(skegox_auth)
                    await skegox_api.discover()
                    device_dicts = await skegox_api.get_all_devices()
                    if device_dicts:
                        vacuums = [_SkegoxWrapper(SkegoxDevice(skegox_api, d), skegox_api)
                                   for d in device_dicts]
                        api = skegox_api

                return api, vacuums, sess
            except Exception:
                await sess.close()
                raise

        try:
            api, vacuums, sess = _run_async(_login())
            with _state_lock:
                _state["api"]        = api
                _state["vacuums"]    = vacuums
                _state["vacuum"]     = vacuums[0] if vacuums else None
                _state["authed"]     = bool(vacuums)
                _state["login_in_progress"] = False
                _state["login_status"] = (
                    f"✓ Conectado — {vacuums[0].name}" if vacuums
                    else "❌ No se encontraron robots."
                )
            if vacuums:
                _refresh_state()
        except Exception as exc:
            msg = str(exc)
            if "401" in msg:
                hint = "❌ Error 401: Shark bloqueó el acceso. Usa 'Iniciar sesión en el PC'."
            else:
                hint = f"❌ Error: {msg[:120]}"
            with _state_lock:
                _state["login_status"] = hint
                _state["login_in_progress"] = False

    threading.Thread(target=_do, daemon=True).start()
    return jsonify({"ok": True})


@app.route("/auth/logout", methods=["POST"])
def auth_logout():
    with _state_lock:
        _state.update({"api": None, "vacuum": None, "vacuums": [],
                        "authed": False, "login_status": "", "map_png": None})
    if os.path.exists(TOKEN_FILE):
        os.remove(TOKEN_FILE)
    return jsonify({"ok": True})


@app.route("/dashboard")
def dashboard():
    if not _state["authed"]:
        return redirect(url_for("login_page"))
    vac = _state["vacuum"]
    return render_template_string(DASHBOARD_HTML,
        robot_name=vac.name if vac else "Robot",
        has_map=(_state["map_png"] is not None),
        demo_mode=False)


@app.route("/demo")
def demo_dashboard():
    """Vista local de demostración: no requiere cuenta ni controla el robot."""
    if CLOUD:
        return Response("Modo demo no disponible en cloud", status=404)
    return render_template_string(DASHBOARD_HTML,
        robot_name="Shark (modo demo)",
        has_map=False,
        demo_mode=True)


@app.route("/api/status")
def api_status():
    vac = _state["vacuum"]
    if vac is None:
        return jsonify({"ok": False, "msg": "No conectado"})
    return jsonify({
        "ok":          True,
        "mode":        _state.get("mode", "UNKNOWN"),
        "mode_text":   _state.get("mode_text", "● Desconocido"),
        "mode_color":  _state.get("mode_color", "#8b949e"),
        "battery":     _state.get("battery"),
        "name":        vac.name,
        "mop_attached": _state.get("mop_attached"),
        "power_mode":   _state.get("power_mode"),
        "mission_complete": _state.get("mission_complete"),
        "docked": _state.get("docked"),
    })


@app.route("/api/debug/properties")
def api_debug_properties():
    """Expone properties_full del robot para diagnóstico."""
    if not _state["authed"]:
        return jsonify({"ok": False, "msg": "No autenticado"})
    vac = _state["vacuum"]
    if vac is None:
        return jsonify({"ok": False, "msg": "Sin robot"})
    try:
        dev = getattr(vac, "_dev", vac)
        props = getattr(dev, "properties_full", {})
        # Unwrap {"value": ...} dicts para legibilidad
        flat = {}
        for k, v in props.items():
            flat[k] = v.get("value") if isinstance(v, dict) else v
        # También mostrar room list raw
        room_list_raw = dev.get_property_value("GET_Robot_Room_List")
        floor_id = getattr(dev, '_floor_id', None)
        has_v3 = getattr(dev, '_has_areas_v3', None)
        room_name_map = getattr(dev, '_room_name_map', None) or {}
        robot_rooms = getattr(dev, '_rooms', None) or []
        return jsonify({"ok": True, "properties": flat, "robot_room_list": room_list_raw,
                        "floor_id": floor_id, "has_areas_v3": has_v3,
                        "room_name_map": room_name_map, "robot_rooms": robot_rooms})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)})


@app.route("/api/refresh", methods=["POST"])
def api_refresh():
    if not _state["authed"]:
        return jsonify({"ok": False, "msg": "No autenticado"})
    try:
        _refresh_state()
        return api_status()
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)})


@app.route("/api/command/<cmd>", methods=["POST"])
def api_command(cmd):
    if not _state["authed"]:
        return jsonify({"ok": False, "msg": "No autenticado"})
    vac = _state["vacuum"]
    if vac is None:
        return jsonify({"ok": False, "msg": "Sin robot"})

    CMD_MAP = {
        "start": OperatingModes.START,
        "pause": OperatingModes.PAUSE,
        "dock":  OperatingModes.RETURN,
    }
    mode = CMD_MAP.get(cmd)
    if mode is None:
        return jsonify({"ok": False, "msg": f"Comando desconocido: {cmd}"})

    try:
        _run_async(vac.async_set_operating_mode(mode))
        if cmd == "start":
            _create_cleaning_mission("manual", "Limpieza manual", [])
        elif cmd == "dock":
            _finish_active_mission("interrupted", "RETURN")
        import time; time.sleep(1.5)
        _refresh_state()
        return api_status()
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)})


@app.route("/api/power-mode", methods=["POST"])
def api_power_mode():
    if not _state["authed"]:
        return jsonify({"ok": False, "msg": "No autenticado"})
    vac = _state["vacuum"]
    if vac is None:
        return jsonify({"ok": False, "msg": "Sin robot"})

    requested = str((request.get_json() or {}).get("mode", "")).lower()
    modes = {"eco": PowerModes.ECO, "normal": PowerModes.NORMAL, "max": PowerModes.MAX}
    mode = modes.get(requested)
    if mode is None:
        return jsonify({"ok": False, "msg": "Potencia inválida"})

    try:
        if hasattr(vac, "async_set_power_mode"):
            _run_async(vac.async_set_power_mode(mode))
        else:
            _run_async(vac.async_set_property_value(Properties.POWER_MODE, mode))
        with _state_lock:
            _state["power_mode"] = int(mode)
        return api_status()
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)})


@app.route("/api/map", methods=["POST"])
def api_load_map():
    """Descarga el mapa del robot y lo sirve como PNG."""
    if not _state["authed"]:
        return jsonify({"ok": False, "msg": "No autenticado"})
    vac = _state["vacuum"]
    api = _state["api"]
    if vac is None or not hasattr(vac, "_dev"):
        return jsonify({"ok": False, "msg": "Mapa no disponible para este modelo"})

    try:
        png_bytes, rooms, ftypes = _run_async(_fetch_map(vac, api))
        with _state_lock:
            _state["map_png"]     = png_bytes
            _state["rooms"]       = rooms
            _state["map_ts"]      = datetime.now().isoformat()
            if ftypes:
                for rn, ft in ftypes.items():
                    if ft and ft != "none":
                        _state["carpet_rooms"].add(rn)
        return jsonify({"ok": True, "rooms": rooms, "carpet_rooms": list(_state["carpet_rooms"])})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)})


@app.route("/api/map/image")
def api_map_image():
    png = _state.get("map_png")
    if png is None:
        return Response(status=204)
    return Response(png, mimetype="image/png",
                    headers={"Cache-Control": "no-cache"})


@app.route("/api/rooms")
def api_rooms():
    return jsonify({
        "rooms":        _state["rooms"],
        "carpet_rooms": list(_state["carpet_rooms"]),
    })


@app.route("/api/notifications")
def api_notifications():
    if not _state["authed"]:
        return jsonify({"ok": False, "msg": "No autenticado"}), 401
    try:
        notifications, unread = _list_notifications(request.args.get("limit", 50))
        return jsonify({
            "ok": True,
            "notifications": notifications,
            "unread_count": unread,
        })
    except (TypeError, ValueError):
        return jsonify({"ok": False, "msg": "Límite inválido"}), 400


@app.route("/api/notifications/<notification_id>/read", methods=["POST"])
def api_notification_read(notification_id):
    if not _state["authed"]:
        return jsonify({"ok": False, "msg": "No autenticado"}), 401
    with _schedule_lock, _schedule_db() as conn:
        result = conn.execute("""
            UPDATE notifications SET read_at=COALESCE(read_at, ?) WHERE id=?
        """, (datetime.now(SCHEDULE_TZ).isoformat(), notification_id))
    if not result.rowcount:
        return jsonify({"ok": False, "msg": "Notificación no encontrada"}), 404
    return jsonify({"ok": True})


@app.route("/api/notifications/read-all", methods=["POST"])
def api_notifications_read_all():
    if not _state["authed"]:
        return jsonify({"ok": False, "msg": "No autenticado"}), 401
    with _schedule_lock, _schedule_db() as conn:
        conn.execute("""
            UPDATE notifications SET read_at=? WHERE read_at IS NULL
        """, (datetime.now(SCHEDULE_TZ).isoformat(),))
    return jsonify({"ok": True})


@app.route("/api/schedules", methods=["GET", "POST"])
def api_schedules():
    if not _state["authed"]:
        return jsonify({"ok": False, "msg": "No autenticado"}), 401
    if request.method == "GET":
        return jsonify({
            "ok": True,
            "schedules": _list_schedules(),
            "timezone": SCHEDULE_TZ_NAME,
            "persistent_storage": bool(
                os.environ.get("SHARK_DATA_DIR")
                or os.environ.get("RAILWAY_VOLUME_MOUNT_PATH")
            ),
        })

    try:
        item = _validate_schedule(request.get_json() or {})
        now_iso = datetime.now(SCHEDULE_TZ).isoformat()
        schedule_id = uuid.uuid4().hex
        with _schedule_lock, _schedule_db() as conn:
            conn.execute("""
                INSERT INTO schedules
                    (id, name, time_hm, days_json, rooms_json, enabled, created_at, updated_at)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?)
            """, (
                schedule_id, item["name"], item["time"],
                json.dumps(item["days"]), json.dumps(item["rooms"], ensure_ascii=False),
                int(item["enabled"]), now_iso, now_iso,
            ))
        created = next(s for s in _list_schedules() if s["id"] == schedule_id)
        return jsonify({"ok": True, "schedule": created}), 201
    except (ValueError, TypeError) as exc:
        return jsonify({"ok": False, "msg": str(exc)}), 400


@app.route("/api/schedules/<schedule_id>", methods=["PUT", "DELETE"])
def api_schedule_item(schedule_id):
    if not _state["authed"]:
        return jsonify({"ok": False, "msg": "No autenticado"}), 401
    with _schedule_lock, _schedule_db() as conn:
        row = conn.execute("SELECT * FROM schedules WHERE id=?", (schedule_id,)).fetchone()
    if row is None:
        return jsonify({"ok": False, "msg": "Tarea no encontrada"}), 404

    if request.method == "DELETE":
        with _schedule_lock, _schedule_db() as conn:
            conn.execute("DELETE FROM schedules WHERE id=?", (schedule_id,))
        return jsonify({"ok": True})

    try:
        current = _schedule_row(row)
        item = _validate_schedule(request.get_json() or {}, current=current)
        now_iso = datetime.now(SCHEDULE_TZ).isoformat()
        with _schedule_lock, _schedule_db() as conn:
            conn.execute("""
                UPDATE schedules
                   SET name=?, time_hm=?, days_json=?, rooms_json=?, enabled=?, updated_at=?
                 WHERE id=?
            """, (
                item["name"], item["time"], json.dumps(item["days"]),
                json.dumps(item["rooms"], ensure_ascii=False), int(item["enabled"]),
                now_iso, schedule_id,
            ))
        updated = next(s for s in _list_schedules() if s["id"] == schedule_id)
        return jsonify({"ok": True, "schedule": updated})
    except (ValueError, TypeError) as exc:
        return jsonify({"ok": False, "msg": str(exc)}), 400


@app.route("/api/clean-rooms", methods=["POST"])
def api_clean_rooms():
    if not _state["authed"]:
        return jsonify({"ok": False, "msg": "No autenticado"})
    data = request.get_json() or {}
    selected  = data.get("rooms", [])
    if not selected:
        return jsonify({"ok": False, "msg": "Ninguna habitación seleccionada"})

    try:
        clean_type = _execute_room_cleaning(selected)
        mission_id = _create_cleaning_mission(
            "manual", "Limpieza de ambientes", selected,
        )
        return jsonify({
            "ok": True, "cleaning": selected, "clean_type": clean_type,
            "mission_id": mission_id,
        })
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)})


@app.route("/api/find-device", methods=["POST"])
def api_find_device():
    if not _state["authed"]:
        return jsonify({"ok": False, "msg": "No autenticado"})
    vac = _state["vacuum"]
    if vac is None:
        return jsonify({"ok": False, "msg": "Sin robot"})
    try:
        dev = getattr(vac, "_dev", vac)
        if hasattr(dev, "async_find_device"):
            _run_async(dev.async_find_device())
        else:
            _run_async(dev.async_set_property_value("Find_Device", 1))
        return jsonify({"ok": True})
    except Exception as e:
        return jsonify({"ok": False, "msg": str(e)})


# ── Descarga de mapa (async) ──────────────────────────────────────────────────
async def _fetch_map(vac, api):
    import aiohttp as _aiohttp
    from PIL import Image as _PILImage

    snd   = vac._dev._snd
    files = await api.list_property_files(snd)

    def _find(prefix):
        return next((f for f in files
                     if f.get("property", "").upper().startswith(prefix.upper())), None)

    sess = await api._auth._get_session()

    async def _download(entry):
        url = (entry.get("presignedUrl") or entry.get("url") or entry.get("downloadUrl"))
        if not url:
            return None
        async with sess.get(url, timeout=_aiohttp.ClientTimeout(total=60)) as r:
            return await r.read() if r.status < 300 else None

    # MARD → habitaciones
    rooms = {}
    room_polygons = {}
    carpet_zones  = []
    nogo_zones    = []
    room_floor_types = {}
    mard_entry = _find("MARD")
    if mard_entry:
        mard_data = await _download(mard_entry)
        if mard_data:
            vac._dev.load_mard(mard_data)
            rooms = vac._dev.room_name_map or {r: r for r in vac._dev.rooms}
            room_polygons = vac._dev.room_polygons
            mard_raw = getattr(vac._dev, "_mard_raw", None)
            if isinstance(mard_raw, dict):
                room_bboxes = {}
                for area in mard_raw.get("areas", []):
                    m_a = area.get("area_meta_data", "")
                    if m_a.startswith("UserRoom:"):
                        rn   = area.get("robot_room_name", "")
                        rpts = [(p["x"], p["y"]) for p in area.get("points", [])
                                if "x" in p and "y" in p]
                        if rn and rpts:
                            xs = [p[0] for p in rpts]; ys = [p[1] for p in rpts]
                            room_bboxes[rn] = (min(xs), min(ys), max(xs), max(ys))
                for area in mard_raw.get("areas", []):
                    m_a  = area.get("area_meta_data", "")
                    rpts = [(p["x"], p["y"]) for p in area.get("points", [])
                            if "x" in p and "y" in p]
                    if m_a.startswith("UserCarpet:") and rpts:
                        carpet_zones.append(rpts)
                        ccx = sum(p[0] for p in rpts) / len(rpts)
                        ccy = sum(p[1] for p in rpts) / len(rpts)
                        for rn, (rx0, ry0, rx1, ry1) in room_bboxes.items():
                            if rx0 <= ccx <= rx1 and ry0 <= ccy <= ry1:
                                room_floor_types[rn] = "carpet"; break
                    elif m_a.startswith("UserNoGo:") and rpts:
                        nogo_zones.append(rpts)

    # Imagen del plano
    img = None
    if room_polygons:
        img = _draw_polygon_map(room_polygons, 390, 290,
                                {"carpet": carpet_zones, "nogo": nogo_zones})
    if img is None:
        for prop in ["Visual_Floor", "Persistent_Floor"]:
            entry = _find(prop)
            if not entry:
                continue
            raw = await _download(entry)
            if not raw:
                continue
            try:
                img = _PILImage.open(io.BytesIO(raw))
                img.load()
                img = img.resize((390, 290), _PILImage.LANCZOS)
                break
            except Exception:
                pass
            try:
                vac._dev.parse_floor_plan(raw)
                fp = vac._dev.floor_plan_image
                if fp:
                    img = fp.resize((390, 290), _PILImage.LANCZOS)
                    break
            except Exception:
                pass

    png_bytes = None
    if img is not None:
        buf = io.BytesIO()
        img.save(buf, "PNG")
        png_bytes = buf.getvalue()

    return png_bytes, rooms, room_floor_types


def _draw_polygon_map(room_polygons, max_w, max_h, extra_zones=None):
    from PIL import Image as _PILImage, ImageDraw, ImageFont
    if not room_polygons:
        return None

    COLORS = [
        ((31,  87, 167), (79,  148, 240)),
        ((22,  100, 40),  (52,  199,  89)),
        ((140, 75,  10),  (251, 176,  64)),
        ((100, 40,  160), (186, 104, 255)),
        ((150, 30,  30),  (255, 100, 100)),
        ((15,  120, 120), (56,  210, 210)),
        ((120, 80,  20),  (230, 170,  60)),
        ((60,  100, 160), (130, 190, 255)),
        ((80,  50,  130), (170, 130, 230)),
    ]

    all_pts = [p for poly in room_polygons.values() for p in poly]
    if not all_pts:
        return None
    xs = [p[0] for p in all_pts]; ys = [p[1] for p in all_pts]
    min_x, max_x = min(xs), max(xs)
    min_y, max_y = min(ys), max(ys)
    span_x = max_x - min_x or 1
    span_y = max_y - min_y or 1
    scale  = min(max_w / span_x, max_h / span_y) * 0.88
    off_x  = (max_w  - span_x * scale) / 2
    off_y  = (max_h - span_y * scale) / 2

    def to_px(x, y):
        return (int((x - min_x) * scale + off_x),
                int((y - min_y) * scale + off_y))

    img  = _PILImage.new("RGB", (max_w, max_h), (13, 17, 23))
    draw = ImageDraw.Draw(img, "RGBA")

    try:
        font = ImageFont.truetype("arial.ttf", max(8, int(scale * 2)))
    except Exception:
        font = ImageFont.load_default()

    for idx, (room_name, poly) in enumerate(room_polygons.items()):
        fill_c, border_c = COLORS[idx % len(COLORS)]
        px_pts = [to_px(x, y) for x, y in poly]
        if len(px_pts) >= 3:
            draw.polygon(px_pts, fill=fill_c + (180,), outline=border_c + (230,))
            cx = int(sum(p[0] for p in px_pts) / len(px_pts))
            cy = int(sum(p[1] for p in px_pts) / len(px_pts))
            draw.text((cx, cy), room_name, fill="white", font=font, anchor="mm")

    if extra_zones:
        for pts in extra_zones.get("carpet", []):
            px_pts = [to_px(x, y) for x, y in pts]
            if len(px_pts) >= 3:
                draw.polygon(px_pts, fill=(139, 90, 43, 120), outline=(205, 133, 63, 200))
        for pts in extra_zones.get("nogo", []):
            px_pts = [to_px(x, y) for x, y in pts]
            if len(px_pts) >= 3:
                draw.polygon(px_pts, fill=(189, 31, 31, 100), outline=(255, 64, 64, 200))

    return img


# ── Intentar auto-login desde tokens guardados al arrancar ────────────────────
def _try_autoload():
    tokens = _load_tokens()
    if not tokens:
        return
    try:
        api, vacuums, sess = _run_async(_init_from_tokens(tokens))
        if vacuums:
            with _state_lock:
                _state["api"]     = api
                _state["vacuums"] = vacuums
                _state["vacuum"]  = vacuums[0]
                _state["authed"]  = True
                _state["login_status"] = f"✓ Sesión restaurada — {vacuums[0].name}"
            _refresh_state()
            print(f"  ✓ Sesión restaurada: {vacuums[0].name}")
    except Exception as e:
        print(f"  [WARN] No se pudo restaurar sesión: {e}")


# ════════════════════════════════════════════════════════════════════════════
#  HTML TEMPLATES
# ════════════════════════════════════════════════════════════════════════════

LOGIN_HTML = """<!DOCTYPE html>
<html lang="es">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width,initial-scale=1,maximum-scale=1">
<meta name="theme-color" content="#0055CC">
<title>Shark IQ — Login</title>
<style>
  *{box-sizing:border-box;margin:0;padding:0}
  body{background:#070D18;color:#E8F3FF;font-family:'Segoe UI',system-ui,sans-serif;
       min-height:100dvh;display:flex;flex-direction:column;align-items:center;justify-content:center;padding:16px}
  .card{background:#0C1520;border:1px solid #1B2C40;border-radius:16px;
        padding:32px 24px;width:min(360px,100%);text-align:center}
  .logo{font-size:52px;margin-bottom:10px}
  h1{font-size:22px;font-weight:700;color:#E8F3FF;margin-bottom:4px}
  .sub{font-size:13px;color:#5E7E9A;margin-bottom:24px}
  .btn{display:block;width:100%;padding:15px;border:none;border-radius:10px;
       font-size:15px;font-weight:700;cursor:pointer;transition:.15s;margin-bottom:10px}
  .btn-primary{background:#006FDE;color:#fff}
  .btn-primary:hover{background:#2896FF}
  .btn-primary:disabled{background:#1B2C40;color:#5E7E9A;cursor:not-allowed}
  .btn-ghost{background:transparent;color:#5E7E9A;font-size:13px;padding:8px;
             border:1px solid #1B2C40;border-radius:8px;cursor:pointer;width:100%;margin-top:4px}
  .btn-ghost:hover{border-color:#2896FF;color:#2896FF}
  .hint{font-size:12px;color:#3A5770;line-height:1.5;margin-bottom:16px;text-align:left}
  .steps{text-align:left;color:#5E7E9A;font-size:13px;padding-left:18px;
         line-height:2;margin:10px 0 14px}
  .steps li{padding-left:4px}
  .divider{display:flex;align-items:center;gap:10px;margin:16px 0;color:#3A5770;font-size:12px}
  .divider::before,.divider::after{content:'';flex:1;height:1px;background:#1B2C40}
  .field{width:100%;background:#070D18;border:1px solid #1B2C40;border-radius:8px;
         padding:12px 14px;font-size:14px;color:#E8F3FF;margin-bottom:10px;outline:none}
  .field:focus{border-color:#2896FF}
  textarea.field{font-size:11px;font-family:monospace;resize:none;line-height:1.4}
  .status{min-height:36px;font-size:13px;color:#5E7E9A;margin-top:14px;line-height:1.5;word-break:break-word}
  .status.err{color:#FF4040}
  .status.ok{color:#00C878}
  .spinner{display:inline-block;width:14px;height:14px;border:2px solid #1B2C40;
           border-top-color:#2896FF;border-radius:50%;animation:spin .8s linear infinite;
           vertical-align:middle;margin-right:5px}
  @keyframes spin{to{transform:rotate(360deg)}}
  #emailForm{display:none;text-align:left}
  a{color:#2896FF}
</style>
</head>
<body>
<div class="card">
  <div class="logo">🦈</div>
  <h1>Shark IQ</h1>
  <p class="sub">Controlador de robot aspirador</p>

{% if is_cloud %}
  <!-- ── MODO CLOUD: OAuth web ── -->
  <div id="step-launch">
    <a href="/auth/launch" target="_blank" rel="noopener"
       class="btn btn-primary" id="webBtn"
       onclick="onLaunchClick(event)"
       style="display:block;text-decoration:none;text-align:center">
      🔐 Iniciar sesión con Shark
    </a>
    <p class="hint" style="text-align:center">Se abrirá la página oficial de Shark en una nueva pestaña.<br>
      <strong style="color:#FFD700">Si estás en el celular, hacé esto desde una PC.</strong></p>

    <div class="divider">o</div>
    <button class="btn-ghost" onclick="toggleEmail()">📧 Intentar con email</button>
    <div id="emailForm">
      <br>
      <input class="field" type="email" id="emailInp" placeholder="Email" autocomplete="email">
      <input class="field" type="password" id="passInp" placeholder="Contraseña" autocomplete="current-password">
      <button class="btn btn-primary" id="emailBtn" onclick="startEmail()">Conectar</button>
    </div>

    <div class="divider">o</div>
    <button class="btn-ghost" onclick="toggleTokens()">📋 Restaurar sesión desde tokens</button>
    <div id="tokenForm" style="display:none;margin-top:10px;text-align:left">
      <p style="font-size:11px;color:#5E7E9A;margin-bottom:6px">Pegá el contenido del archivo <code style="color:#AAD4FF;font-size:10px">shark_web_tokens.json</code> de tu PC local:</p>
      <textarea class="field" id="tokenJsonInp" rows="4"
        placeholder='{"auth0_id_token":"...", "ayla_access_token":"..."}'
        oninput="document.getElementById('restoreBtn').disabled=!this.value.trim()"></textarea>
      <button class="btn btn-primary" id="restoreBtn" onclick="submitTokens()" disabled>Restaurar sesión</button>
    </div>
  </div>

  <!-- Paso 2: pegar URL -->
  <div id="step-paste" style="display:none">
    <p style="font-size:13px;font-weight:700;color:#E8F3FF;margin-bottom:10px;text-align:center">Login desde PC (Chrome o Firefox)</p>
    <ol class="steps">
      <li>Abrí <a href="/auth/launch" target="_blank" rel="noopener" id="sharkLoginLink">este link en tu PC ↗</a><br><span style="font-size:11px;color:#3A5770">en Chrome o Firefox — en la PC, no en el celular</span></li>
      <li>Iniciá sesión con tu cuenta Shark</li>
      <li>El navegador mostrará un error “no se puede abrir” &mdash; <strong style="color:#E8F3FF">copiá la URL completa</strong> de la barra de direcciones<br><span style="font-size:11px;color:#3A5770">(empieza con com.sharkninja.shark://...)</span></li>
      <li>Pegala acá:</li>
    </ol>
    <textarea class="field" id="redirectUrlInp" rows="3"
      placeholder="com.sharkninja.shark://..."
      oninput="document.getElementById('continueBtn').disabled=!this.value.trim()"></textarea>
    <button class="btn btn-primary" id="continueBtn" onclick="submitCode()" disabled>
      Continuar →
    </button>
    <button class="btn-ghost" style="margin-top:6px" onclick="resetOAuth()">← Volver</button>
  </div>

{% else %}
  <!-- ── MODO LOCAL: navegador del PC ── -->
  <div id="step-launch">
    <a href="/auth/launch" target="_blank" rel="noopener"
       class="btn btn-primary" id="webBtn" onclick="onLaunchClick(event)"
       style="display:block;text-decoration:none;text-align:center">
      🔐 Iniciar sesión con Shark
    </a>
    <p class="hint" style="text-align:center">Usá este método si el acceso directo o por email pide verificación.</p>

    <div class="divider">o</div>
    <button class="btn-ghost" onclick="startBrowser()">🖥️ Intentar ventana integrada</button>

    <div class="divider">o</div>
    <button class="btn-ghost" onclick="toggleEmail()">📧 Iniciar sesión con email</button>
    <div id="emailForm">
      <br>
      <input class="field" type="email" id="emailInp" placeholder="Email" autocomplete="email">
      <input class="field" type="password" id="passInp" placeholder="Contraseña" autocomplete="current-password">
      <button class="btn btn-primary" id="emailBtn" onclick="startEmail()">Conectar</button>
    </div>
  </div>

  <div id="step-paste" style="display:none">
    <p style="font-size:13px;font-weight:700;margin-bottom:10px">Completar inicio de sesión</p>
    <ol class="steps">
      <li>Iniciá sesión en la pestaña oficial de Shark.</li>
      <li>Cuando el navegador no pueda abrir la página, copiá la URL completa de la barra.<br>
        <span style="font-size:11px;color:#3A5770">Empieza con com.sharkninja.shark://...</span></li>
      <li>Pegala aquí:</li>
    </ol>
    <textarea class="field" id="redirectUrlInp" rows="3"
      placeholder="com.sharkninja.shark://...?code=..."
      oninput="document.getElementById('continueBtn').disabled=!this.value.trim()"></textarea>
    <button class="btn btn-primary" id="continueBtn" onclick="submitCode()" disabled>Continuar →</button>
    <button class="btn-ghost" onclick="resetOAuth()">← Volver</button>
  </div>
{% endif %}

  <div class="status" id="status">{{ status }}</div>
</div>
<script>
let polling = false;
let emailVisible = false;

function toggleEmail(){
  emailVisible = !emailVisible;
  document.getElementById('emailForm').style.display = emailVisible ? 'block' : 'none';
}

let tokenVisible = false;
function toggleTokens(){
  tokenVisible = !tokenVisible;
  document.getElementById('tokenForm').style.display = tokenVisible ? 'block' : 'none';
}
async function submitTokens(){
  const tokenJson = document.getElementById('tokenJsonInp').value.trim();
  document.getElementById('restoreBtn').disabled = true;
  setStatus('<span class="spinner"></span> Restaurando sesión...', '');
  polling = true;
  const d = await apiFetch('/auth/restore-tokens','POST',{tokens:tokenJson});
  if(!d.ok){ setStatus('\u274c '+d.msg,'err'); document.getElementById('restoreBtn').disabled=false; polling=false; return; }
  poll();
}

// ── Cloud: web OAuth ────────────────────────────────────────────────────────
function onLaunchClick(e){
  // El <a href="/auth/launch" target="_blank"> navega nativamente — solo actualizar UI
  document.getElementById('webBtn').style.pointerEvents = 'none';
  document.getElementById('webBtn').style.opacity = '0.5';
  const loginLink = document.getElementById('sharkLoginLink');
  if(loginLink) loginLink.href = '/auth/launch';
  document.getElementById('step-launch').style.display = 'none';
  document.getElementById('step-paste').style.display = 'block';
  setStatus('', '');
}

function startWebOAuth(){
  // fallback: llamar onLaunchClick y abrir manualmente
  window.open('/auth/launch', '_blank');
  onLaunchClick(null);
}

function resetOAuth(){
  document.getElementById('step-launch').style.display = 'block';
  document.getElementById('step-paste').style.display = 'none';
  const wb = document.getElementById('webBtn');
  wb.style.pointerEvents = '';
  wb.style.opacity = '';
  document.getElementById('redirectUrlInp').value = '';
  document.getElementById('continueBtn').disabled = true;
  setStatus('', '');
}

async function submitCode(){
  const redirectUrl = document.getElementById('redirectUrlInp').value.trim();
  if(!redirectUrl){ setStatus('Pegá la URL primero', 'err'); return; }
  document.getElementById('continueBtn').disabled = true;
  setStatus('<span class="spinner"></span> Verificando...', '');
  polling = true;
  const d = await apiFetch('/auth/browser-code','POST',{redirect_url:redirectUrl});
  if(!d.ok){ setStatus('❌ '+d.msg,'err'); document.getElementById('continueBtn').disabled=false; polling=false; return; }
  poll();
}

// ── Local: navegador del PC ─────────────────────────────────────────────────
function startBrowser(){
  const loginBtn = document.getElementById('loginBtn');
  if(loginBtn) loginBtn.disabled = true;
  setStatus('<span class="spinner"></span> Abriendo navegador en el PC...', '');
  polling = true;
  apiFetch('/auth/start','POST').then(()=>poll());
}

// ── Email ───────────────────────────────────────────────────────────────────
function startEmail(){
  const email = document.getElementById('emailInp').value.trim();
  const pass  = document.getElementById('passInp').value;
  if(!email || !pass){ setStatus('Completa email y contraseña', 'err'); return; }
  const lb = document.getElementById('loginBtn'); if(lb) lb.disabled = true;
  document.getElementById('emailBtn').disabled = true;
  setStatus('<span class="spinner"></span> Verificando credenciales...', '');
  polling = true;
  apiFetch('/auth/email','POST',{email,password:pass}).then(()=>poll());
}

// ── Polling ─────────────────────────────────────────────────────────────────
function poll(){
  if(!polling) return;
  apiFetch('/auth/status').then(d=>{
    if(d.authed){ window.location='/dashboard'; return; }
    const cls = d.msg.startsWith('❌') ? 'err' : d.msg.startsWith('✓') ? 'ok' : '';
    setStatus(d.in_progress ? '<span class="spinner"></span> '+d.msg : d.msg, cls);
    if(d.in_progress || (!d.authed && !d.msg.startsWith('❌'))){
      setTimeout(poll, 1500);
    } else {
      ['webBtn','loginBtn','emailBtn','continueBtn'].forEach(id=>{
        const el=document.getElementById(id); if(el) el.disabled=false;
      });
      polling = false;
    }
  }).catch(()=>setTimeout(poll, 2000));
}

function setStatus(html, cls){
  const el = document.getElementById('status');
  el.innerHTML = html;
  el.className = 'status ' + (cls||'');
}

async function apiFetch(url, method='GET', body=null){
  try {
    const opts = { method, headers: {'Content-Type':'application/json'} };
    if(body) opts.body = JSON.stringify(body);
    const r = await fetch(url, opts);
    return await r.json();
  } catch(e){ return {ok:false, msg:String(e)}; }
}
{% if in_progress %}
window.onload = function(){ startBrowser(); };
{% endif %}
</script>
</body></html>"""


DASHBOARD_HTML = """<!DOCTYPE html>
<html lang="es">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width,initial-scale=1,maximum-scale=1">
<meta name="theme-color" content="#0055CC">
<title>Shark IQ</title>
<style>
*{box-sizing:border-box;margin:0;padding:0;-webkit-tap-highlight-color:transparent}
body{background:#070D18;color:#E8F3FF;font-family:'Segoe UI',system-ui,sans-serif;
     overscroll-behavior:none}
/* Header */
.hdr{background:#0055CC;height:64px;display:flex;align-items:center;
     justify-content:space-between;padding:0 18px;position:sticky;top:0;z-index:10}
.hdr-logo{font-size:22px;font-weight:800;color:#fff;letter-spacing:1px}
.hdr-logo span{font-size:11px;font-weight:400;color:#AAD4FF;display:block;letter-spacing:0}
.hdr-actions{display:flex;align-items:center;gap:12px}
.conn{display:flex;flex-direction:column;align-items:flex-end;gap:2px}
.conn-dot{font-size:18px}
.conn-lbl{font-size:11px;color:#AAD4FF}
.notification-btn{position:relative;width:42px;height:42px;border-radius:12px;border:1px solid #3A8BE8;
                  background:#064AA3;color:#fff;font-size:20px;cursor:pointer}
.notification-badge{display:none;position:absolute;right:-5px;top:-5px;min-width:20px;height:20px;
                    padding:0 5px;border-radius:10px;background:#FF4040;color:#fff;font-size:11px;
                    font-weight:800;align-items:center;justify-content:center;border:2px solid #0055CC}
.notification-badge.show{display:flex}
.notification-overlay{display:none;position:fixed;inset:0;background:rgba(2,7,14,.72);z-index:30}
.notification-overlay.open{display:block}
.notification-drawer{position:absolute;right:0;top:0;width:min(430px,100%);height:100%;overflow-y:auto;
                     background:#070D18;border-left:1px solid #1B2C40;padding:18px 14px 28px}
.notification-head{display:flex;align-items:center;justify-content:space-between;gap:12px;margin-bottom:12px}
.notification-title{font-size:19px;font-weight:800}
.notification-actions{display:flex;gap:7px}
.notification-browser{display:none;background:#0B2A49;border:1px solid #225D91;border-radius:10px;
                      color:#AAD4FF;padding:10px 12px;margin-bottom:10px;font-size:12px;line-height:1.4}
.notification-browser.show{display:block}
.notification-list{display:flex;flex-direction:column;gap:8px}
.notification-item{background:#0C1520;border:1px solid #1B2C40;border-radius:12px;padding:12px;cursor:pointer}
.notification-item.unread{border-color:#227DCE;background:#0B1B2C}
.notification-item-top{display:flex;align-items:center;justify-content:space-between;gap:10px}
.notification-item-title{font-size:14px;font-weight:800}
.notification-dot{width:8px;height:8px;border-radius:50%;background:#2896FF;flex-shrink:0}
.notification-message{font-size:12px;color:#8FA9C1;line-height:1.45;margin-top:5px}
.notification-time{font-size:10px;color:#5E7E9A;margin-top:7px}
.notification-empty{color:#5E7E9A;text-align:center;padding:45px 15px;font-size:13px}
/* Robot card */
.card{background:#0C1520;border:1px solid #1B2C40;border-radius:14px;
      margin:14px 12px 0;padding:16px}
.robot-row{display:flex;align-items:center;gap:14px}
.robot-icon{width:56px;height:56px;background:#141E2C;border-radius:12px;
            display:flex;align-items:center;justify-content:center;font-size:26px;flex-shrink:0}
.robot-info{flex:1;min-width:0}
.robot-name{font-size:17px;font-weight:700;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.robot-mode{font-size:12px;margin-top:3px;font-weight:600}
.battery-col{text-align:right;flex-shrink:0}
.batt-pct{font-size:22px;font-weight:800;color:#FFAD00}
.batt-bar-wrap{background:#141E2C;border-radius:4px;height:6px;width:64px;margin-top:4px}
.batt-bar{background:#00C878;border-radius:4px;height:6px;transition:.4s}
/* Tabs */
.tabs{display:flex;margin:14px 12px 0;background:#0C1520;
      border-radius:12px;padding:4px;border:1px solid #1B2C40}
.tab{flex:1;padding:10px;text-align:center;font-size:14px;font-weight:700;
     color:#5E7E9A;border-radius:9px;cursor:pointer;transition:.15s;user-select:none}
.tab.active{background:#141E2C;color:#2896FF}
.panel{display:none;padding:0 12px 24px}
.panel.active{display:block}
/* Buttons */
.btn-grid{display:grid;grid-template-columns:1fr 1fr;gap:10px;margin-top:14px}
.btn{border:none;border-radius:12px;font-size:15px;font-weight:700;color:#fff;
     cursor:pointer;padding:18px 8px;transition:.15s;width:100%;letter-spacing:.3px}
.btn-start{background:#007A50}
.btn-start:active{background:#00C878}
.btn-pause{background:#C27500}
.btn-pause:active{background:#FFAD00}
.btn-dock{grid-column:1/-1;background:#006FDE;padding:16px}
.btn-dock:active{background:#2896FF}
.btn-sm{background:#141E2C;font-size:13px;padding:12px 8px;color:#E8F3FF;
        border-radius:10px;border:none;cursor:pointer;width:100%;font-weight:600}
.btn-sm:active{background:#1B2C40}
.btn-sm-grid{display:grid;grid-template-columns:1fr 1fr;gap:8px;margin-top:8px}
.power-card{background:#0C1520;border:1px solid #1B2C40;border-radius:12px;
            margin-top:12px;padding:12px}
.power-title{font-size:13px;font-weight:700;margin-bottom:9px}
.power-options{display:grid;grid-template-columns:repeat(3,1fr);gap:7px}
.power-btn{background:#141E2C;color:#8FA9C1;border:1px solid #1B2C40;border-radius:9px;
           padding:11px 5px;font-size:13px;font-weight:700;cursor:pointer}
.power-btn.active{background:#063568;color:#fff;border-color:#2896FF}
.power-btn:disabled{opacity:.55;cursor:wait}
.btn-danger{background:#BD1F1F}
.btn-danger:active{background:#FF4040}
/* Log */
.log-area{background:#0C1520;border:1px solid #1B2C40;border-radius:10px;
          padding:10px 12px;margin-top:12px;height:130px;overflow-y:auto;
          font-family:monospace;font-size:12px;color:#5E7E9A;scroll-behavior:smooth}
/* Map */
.map-wrap{background:#0C1520;border:1px solid #1B2C40;border-radius:12px;
          margin-top:14px;overflow:hidden;text-align:center;min-height:200px;
          display:flex;align-items:center;justify-content:center}
.map-wrap img{width:100%;height:auto;display:block}
.map-placeholder{color:#5E7E9A;font-size:13px;padding:40px 20px}
/* Rooms list */
.room-list{margin-top:10px;display:flex;flex-direction:column;gap:6px}
.room-row{background:#141E2C;border:1px solid #1B2C40;border-radius:10px;
          display:flex;align-items:center;padding:12px 14px;cursor:pointer;
          transition:.1s;user-select:none}
.room-row.selected{border-color:#006FDE;background:#0a1a30}
.room-row.excl{opacity:.55}
.room-check{width:22px;height:22px;border:2px solid #5E7E9A;border-radius:6px;
            flex-shrink:0;display:flex;align-items:center;justify-content:center;
            font-size:14px;margin-right:12px;transition:.1s}
.room-row.selected .room-check{background:#006FDE;border-color:#006FDE}
.room-name{flex:1;font-size:15px;font-weight:500}
.carpet-badge{font-size:12px;background:#2d1a08;border:1px solid #8b5e2a;
              border-radius:6px;padding:2px 8px;color:#c8813a;cursor:pointer;
              user-select:none;flex-shrink:0}
.carpet-badge.excl-on{background:#1a0d04;color:#6a3f10;text-decoration:line-through}
.btn-clean{background:#007A50;border:none;border-radius:12px;color:#fff;
           font-size:16px;font-weight:700;width:100%;padding:16px;
           margin-top:12px;cursor:pointer;transition:.15s}
.btn-clean:active{background:#00C878}
.btn-clean:disabled{background:#141E2C;color:#5E7E9A;cursor:not-allowed}
/* Spinner */
.spinner{display:inline-block;width:14px;height:14px;border:2px solid #1B2C40;
         border-top-color:#2896FF;border-radius:50%;animation:spin .7s linear infinite;
         vertical-align:middle;margin-right:4px}
@keyframes spin{to{transform:rotate(360deg)}}
/* Status bar */
.status-bar{background:#141E2C;border-radius:8px;padding:8px 12px;margin-top:10px;
             font-size:12px;color:#5E7E9A;text-align:center}
/* Schedules */
.schedule-head{display:flex;justify-content:space-between;align-items:center;margin-top:14px;gap:10px}
.schedule-title{font-size:17px;font-weight:800}
.schedule-sub{font-size:11px;color:#5E7E9A;margin-top:3px}
.schedule-form{display:none;background:#0C1520;border:1px solid #1B2C40;border-radius:12px;
               padding:14px;margin-top:12px}
.schedule-form.open{display:block}
.field-label{display:block;font-size:12px;color:#8FA9C1;font-weight:700;margin:12px 0 6px}
.field-input{width:100%;background:#141E2C;color:#E8F3FF;border:1px solid #1B2C40;
             border-radius:9px;padding:12px;font-size:15px;outline:none}
.field-input:focus{border-color:#2896FF}
.day-grid{display:grid;grid-template-columns:repeat(7,1fr);gap:5px}
.day-chip{background:#141E2C;color:#8FA9C1;border:1px solid #1B2C40;border-radius:8px;
          padding:9px 2px;text-align:center;font-size:11px;font-weight:800;cursor:pointer}
.day-chip.selected{background:#063568;color:#fff;border-color:#2896FF}
.schedule-rooms{display:flex;flex-direction:column;gap:6px;max-height:260px;overflow-y:auto}
.schedule-room{background:#141E2C;border:1px solid #1B2C40;border-radius:9px;
               padding:10px 12px;display:flex;align-items:center;gap:10px;cursor:pointer}
.schedule-room.selected{border-color:#006FDE;background:#0a1a30}
.schedule-room-mark{width:20px;height:20px;border:2px solid #5E7E9A;border-radius:5px;
                    display:flex;align-items:center;justify-content:center;font-size:12px;flex-shrink:0}
.schedule-room.selected .schedule-room-mark{background:#006FDE;border-color:#006FDE}
.form-actions{display:grid;grid-template-columns:1fr 1fr;gap:8px;margin-top:14px}
.schedule-list{display:flex;flex-direction:column;gap:9px;margin-top:12px}
.schedule-card{background:#0C1520;border:1px solid #1B2C40;border-radius:12px;padding:13px}
.schedule-card.disabled{opacity:.58}
.schedule-card-top{display:flex;align-items:flex-start;justify-content:space-between;gap:10px}
.schedule-card-name{font-size:15px;font-weight:800}
.schedule-time{font-size:20px;font-weight:800;color:#2896FF;white-space:nowrap}
.schedule-meta{font-size:12px;color:#8FA9C1;margin-top:6px;line-height:1.45}
.schedule-result{font-size:11px;color:#5E7E9A;margin-top:7px;border-top:1px solid #1B2C40;padding-top:7px}
.schedule-actions{display:grid;grid-template-columns:1fr 1fr 1fr;gap:6px;margin-top:10px}
.schedule-empty{background:#0C1520;border:1px dashed #1B2C40;border-radius:12px;
                color:#5E7E9A;text-align:center;padding:28px 14px;margin-top:12px;font-size:13px}
.storage-warn{background:#2a1d08;border:1px solid #7b5518;color:#FFCA70;border-radius:9px;
              font-size:11px;padding:9px 11px;margin-top:10px}
</style>
</head>
<body>
<div class="hdr">
  <div>
    <div class="hdr-logo">SHARK <span>IQ Controller</span></div>
  </div>
  <div class="hdr-actions">
    <button class="notification-btn" onclick="openNotifications()" aria-label="Notificaciones">
      🔔<span class="notification-badge" id="notificationBadge">0</span>
    </button>
    <div class="conn">
      <div class="conn-dot" id="connDot">●</div>
      <div class="conn-lbl" id="connLbl">Conectando...</div>
    </div>
  </div>
</div>

<div class="notification-overlay" id="notificationOverlay" onclick="closeNotifications(event)">
  <aside class="notification-drawer" role="dialog" aria-label="Centro de notificaciones">
    <div class="notification-head">
      <div class="notification-title">Notificaciones</div>
      <div class="notification-actions">
        <button class="btn-sm" style="width:auto;padding:9px" onclick="markAllNotificationsRead()">Leer todas</button>
        <button class="btn-sm" style="width:auto;padding:9px 12px" onclick="closeNotifications()">✕</button>
      </div>
    </div>
    <div class="notification-browser" id="notificationBrowser">
      Recibe un aviso aunque estés viendo otra pestaña.
      <button class="btn-sm" style="margin-top:8px" onclick="enableBrowserNotifications()">Activar avisos del navegador</button>
    </div>
    <div class="notification-list" id="notificationList">
      <div class="notification-empty">Cargando...</div>
    </div>
  </aside>
</div>

<!-- Robot card -->
<div class="card">
  <div class="robot-row">
    <div class="robot-icon">🤖</div>
    <div class="robot-info">
      <div class="robot-name" id="robotName">{{ robot_name }}</div>
      <div class="robot-mode" id="robotMode" style="color:#5E7E9A">● Actualizando...</div>
      <div id="mopBadge" style="display:none;margin-top:4px;font-size:11px;padding:2px 8px;
           border-radius:6px;background:#0C1520;border:1px solid #1B2C40;width:fit-content"></div>
    </div>
    <div class="battery-col">
      <div class="batt-pct" id="battPct">--%</div>
      <div class="batt-bar-wrap"><div class="batt-bar" id="battBar" style="width:0%"></div></div>
    </div>
  </div>
</div>

<!-- Tabs -->
<div class="tabs">
  <div class="tab active" onclick="switchTab('control')">Control</div>
  <div class="tab" onclick="switchTab('map')">Mapa</div>
  <div class="tab" onclick="switchTab('schedule')">Programar</div>
</div>

<!-- Panel: Control -->
<div class="panel active" id="panel-control">
  <div class="btn-grid">
    <button class="btn btn-start" onclick="sendCmd('start')">▶ Iniciar</button>
    <button class="btn btn-pause" onclick="sendCmd('pause')">⏸ Pausar</button>
    <button class="btn btn-dock"  onclick="sendCmd('dock')">🏠 Volver a la base</button>
  </div>
  <div class="power-card">
    <div class="power-title">Potencia de limpieza</div>
    <div class="power-options" id="powerOptions">
      <button class="power-btn" data-power="eco" onclick="setPowerMode('eco')">Eco</button>
      <button class="power-btn" data-power="normal" onclick="setPowerMode('normal')">Normal</button>
      <button class="power-btn" data-power="max" onclick="setPowerMode('max')">Máxima</button>
    </div>
  </div>
  <div class="btn-sm-grid">
    <button class="btn-sm" onclick="doRefresh()">🔄 Actualizar</button>
    <button class="btn-sm" onclick="findDevice()">📍 Localizar robot</button>
    <button class="btn-sm btn-danger" onclick="doLogout()">🚪 Cerrar sesión</button>
  </div>
  <div class="log-area" id="logArea"></div>
</div>

<!-- Panel: Mapa -->
<div class="panel" id="panel-map">
  <button class="btn-sm" style="margin-top:14px;width:100%;padding:14px;font-size:14px"
          onclick="loadMap()">🔄 Cargar / actualizar mapa</button>
  <div class="status-bar" id="mapStatus">Pulsa el botón para descargar el plano</div>

  <div class="map-wrap" id="mapWrap">
    <div class="map-placeholder">Sin mapa cargado</div>
  </div>

  <div id="roomsSection" style="display:none">
    <div style="display:flex;justify-content:space-between;align-items:center;margin-top:14px">
      <span style="font-size:13px;font-weight:700;color:#E8F3FF">Habitaciones</span>
      <span style="font-size:11px;color:#5E7E9A" id="carpetHint">🟫 = alfombra — toca para excluir</span>
    </div>
    <div id="wetModeNote" style="display:none;margin-top:6px;padding:7px 10px;background:#0d1a14;
         border:1px solid #005533;border-radius:8px;font-size:11px;color:#00C878">
      🧽 Modo húmedo: alfombras excluidas automáticamente
    </div>
    <div class="room-list" id="roomList"></div>
    <button class="btn-clean" id="cleanBtn" disabled onclick="cleanRooms()">
      🧹 Limpiar seleccionadas
    </button>
  </div>
</div>

<!-- Panel: Programación -->
<div class="panel" id="panel-schedule">
  <div class="schedule-head">
    <div>
      <div class="schedule-title">Tareas programadas</div>
      <div class="schedule-sub">Varias tareas por día, cada una con sus ambientes</div>
    </div>
    <button class="btn-sm" style="width:auto;padding:10px 14px" onclick="openScheduleForm()">＋ Nueva</button>
  </div>
  <div id="scheduleStorageWarning"></div>

  <div class="schedule-form" id="scheduleForm">
    <div style="font-size:15px;font-weight:800" id="scheduleFormTitle">Nueva tarea</div>
    <label class="field-label" for="scheduleName">Nombre</label>
    <input class="field-input" id="scheduleName" maxlength="60" placeholder="Ej. Cocina después de cenar">
    <label class="field-label" for="scheduleTime">Hora</label>
    <input class="field-input" id="scheduleTime" type="time" value="09:00">
    <div class="field-label">Días</div>
    <div class="day-grid" id="scheduleDays"></div>
    <div class="field-label">Ambientes</div>
    <div class="schedule-rooms" id="scheduleRooms">
      <div class="schedule-sub">Cargando ambientes...</div>
    </div>
    <div class="form-actions">
      <button class="btn-sm" onclick="closeScheduleForm()">Cancelar</button>
      <button class="btn-sm" style="background:#007A50;color:#fff" onclick="saveSchedule()">Guardar tarea</button>
    </div>
  </div>

  <div class="schedule-list" id="scheduleList">
    <div class="schedule-empty"><span class="spinner"></span> Cargando tareas...</div>
  </div>
</div>

<script>
// ── Estado ────────────────────────────────────────────────────────────────────
const S = { selected: new Set(), carpetExcl: new Set(), rooms: {}, carpet: new Set(),
            schedules: [], scheduleDays: new Set(), scheduleRooms: new Set(), scheduleEditing: null,
            notifications: [], knownNotificationIds: new Set(), notificationsLoaded: false };
const DEMO_MODE = {{ 'true' if demo_mode else 'false' }};
let demoPowerMode = 0;

// ── Notificaciones ───────────────────────────────────────────────────────────
function openNotifications(){
  document.getElementById('notificationOverlay').classList.add('open');
  updateBrowserNotificationPrompt();
  loadNotifications();
}

function closeNotifications(event){
  const overlay = document.getElementById('notificationOverlay');
  if(event && event.target !== overlay) return;
  overlay.classList.remove('open');
}

function updateBrowserNotificationPrompt(){
  const host = document.getElementById('notificationBrowser');
  host.classList.toggle('show', 'Notification' in window && Notification.permission === 'default');
}

async function enableBrowserNotifications(){
  if(!('Notification' in window)) return;
  await Notification.requestPermission();
  updateBrowserNotificationPrompt();
}

function showBrowserNotification(item){
  if(!('Notification' in window) || Notification.permission !== 'granted') return;
  try { new Notification(item.title, {body:item.message, tag:item.id}); } catch(e) {}
}

function formatNotificationTime(value){
  if(!value) return '';
  return new Date(value).toLocaleString('es-AR', {
    day:'2-digit', month:'2-digit', hour:'2-digit', minute:'2-digit'
  });
}

function renderNotifications(unreadCount){
  const badge = document.getElementById('notificationBadge');
  badge.textContent = unreadCount > 99 ? '99+' : unreadCount;
  badge.classList.toggle('show', unreadCount > 0);
  const host = document.getElementById('notificationList');
  if(!S.notifications.length){
    host.innerHTML = '<div class="notification-empty">Las nuevas tareas terminadas aparecerán aquí, incluso si se iniciaron desde Shark o Google Home.</div>';
    return;
  }
  host.innerHTML = S.notifications.map(item=>`
    <div class="notification-item ${item.read_at?'':'unread'}" onclick="markNotificationRead('${item.id}')">
      <div class="notification-item-top">
        <div class="notification-item-title">${item.kind==='success'?'✓':'⚠'} ${esc(item.title)}</div>
        ${item.read_at?'':'<div class="notification-dot"></div>'}
      </div>
      <div class="notification-message">${esc(item.message)}</div>
      <div class="notification-time">${esc(formatNotificationTime(item.created_at))}</div>
    </div>`).join('');
}

async function loadNotifications(){
  const result = await api('/api/notifications');
  if(!result.ok) return;
  const items = result.notifications || [];
  if(S.notificationsLoaded){
    items.filter(item=>!item.read_at && !S.knownNotificationIds.has(item.id))
         .forEach(showBrowserNotification);
  }
  items.forEach(item=>S.knownNotificationIds.add(item.id));
  S.notificationsLoaded = true;
  S.notifications = items;
  renderNotifications(result.unread_count || 0);
}

async function markNotificationRead(id){
  const item = S.notifications.find(entry=>entry.id===id);
  if(!item || item.read_at) return;
  await api('/api/notifications/'+id+'/read','POST');
  await loadNotifications();
}

async function markAllNotificationsRead(){
  await api('/api/notifications/read-all','POST');
  await loadNotifications();
}

// ── Tabs ──────────────────────────────────────────────────────────────────────
function switchTab(name){
  document.querySelectorAll('.tab').forEach((t,i)=>{
    t.classList.toggle('active', ['control','map','schedule'][i]===name);
  });
  document.querySelectorAll('.panel').forEach(p=>{
    p.classList.toggle('active', p.id==='panel-'+name);
  });
  if(name==='map' && Object.keys(S.rooms).length===0) loadMap();
  if(name==='schedule') prepareSchedules();
}

// ── Status polling ────────────────────────────────────────────────────────────
async function doRefresh(){
  log('🔄 Actualizando...');
  const d = await api('/api/refresh','POST');
  if(d.ok) updateStatus(d);
  else log('⚠ '+d.msg);
}

function updateStatus(d){
  document.getElementById('robotMode').textContent = d.mode_text || '●';
  document.getElementById('robotMode').style.color = d.mode_color || '#5E7E9A';
  if(d.battery != null){
    document.getElementById('battPct').textContent = d.battery+'%';
    const batt = parseInt(d.battery);
    const color = batt>40?'#00C878':batt>20?'#FFAD00':'#FF4040';
    document.getElementById('battBar').style.width = batt+'%';
    document.getElementById('battBar').style.background = color;
    document.getElementById('battPct').style.color = color;
  }
  document.getElementById('connDot').style.color = '#00C878';
  document.getElementById('connLbl').textContent = d.name||'Conectado';
  if(d.power_mode !== null && d.power_mode !== undefined){
    const names = {1:'eco', 0:'normal', 2:'max'};
    document.querySelectorAll('.power-btn').forEach(btn=>
      btn.classList.toggle('active', btn.dataset.power === names[d.power_mode]));
  }
  // Indicador almohadilla
  if(d.mop_attached !== null && d.mop_attached !== undefined){
    const badge = document.getElementById('mopBadge');
    if(d.mop_attached){
      badge.textContent = '🧽 Almohadilla colocada';
      badge.style.color = '#00C878';
      badge.style.borderColor = '#005533';
    } else {
      badge.textContent = '🧹 Sin almohadilla (modo seco)';
      badge.style.color = '#5E7E9A';
      badge.style.borderColor = '#1B2C40';
    }
    badge.style.display = 'block';
  }
  // Actualizar lógica de alfombras según modo — solo si cambia
  const prevMop = window._mopAttached;
  window._mopAttached = !!(d.mop_attached);
  // Solo resetear carpetExcl si cambia el modo mop
  if(prevMop !== window._mopAttached) applyMopMode();
}

// Auto-refresh every 30 s — llama /api/refresh para actualizar estado del robot
setInterval(()=>{
  api('/api/refresh','POST').then(d=>{ if(d.ok) updateStatus(d); });
}, 30000);
setInterval(loadNotifications, 15000);

// Initial load
doRefresh();
loadNotifications();

// Aplica auto-exclusión de alfombras según modo mopa
function applyMopMode(){
  const wet = window._mopAttached;
  const hint = document.getElementById('carpetHint');
  const note = document.getElementById('wetModeNote');
  if(hint) hint.textContent = wet ? '' : '🟧 = alfombra';
  if(note) note.style.display = wet ? 'block' : 'none';
  if(wet){
    // Modo húmedo: todas las alfombras excluidas automáticamente
    S.carpet.forEach(rn => S.carpetExcl.add(rn));
  } else {
    // Modo seco: limpiar alfombras por defecto (usuario puede cambiar)
    S.carpetExcl.clear();
  }
  if(Object.keys(S.rooms).length > 0) renderRooms();
  updateCleanBtn();
}

// ── Comandos ──────────────────────────────────────────────────────────────────
async function sendCmd(cmd){
  const labels = {start:'Iniciando limpieza...',pause:'Pausando...',dock:'Volviendo a la base...'};
  log('⏳ '+labels[cmd]);
  const d = await api('/api/command/'+cmd,'POST');
  if(d.ok){ updateStatus(d); log('✓ '+d.mode_text); }
  else log('⚠ '+d.msg);
}

async function setPowerMode(mode){
  const labels = {eco:'Eco',normal:'Normal',max:'Máxima'};
  const buttons = document.querySelectorAll('.power-btn');
  buttons.forEach(btn=>btn.disabled=true);
  log('⏳ Ajustando potencia '+labels[mode]+'...');
  const d = await api('/api/power-mode','POST',{mode});
  buttons.forEach(btn=>btn.disabled=false);
  if(d.ok){ updateStatus(d); log('✓ Potencia '+labels[mode]+' seleccionada'); }
  else log('⚠ '+d.msg);
}

async function findDevice(){
  log('📍 Buscando robot...');
  const d = await api('/api/find-device','POST');
  if(d.ok) log('✓ El robot debería emitir un sonido');
  else log('⚠ '+d.msg);
}

// ── Mapa ──────────────────────────────────────────────────────────────────────
async function loadMap(){
  setMapStatus('<span class="spinner"></span> Descargando mapa...');
  const d = await api('/api/map','POST');
  if(!d.ok){ setMapStatus('⚠ '+d.msg); return; }

  // Imagen
  const img = document.createElement('img');
  img.src = '/api/map/image?ts='+Date.now();
  img.alt = 'Mapa';
  const wrap = document.getElementById('mapWrap');
  wrap.innerHTML = ''; wrap.appendChild(img);

  // Habitaciones
  S.rooms  = d.rooms || {};
  S.carpet = new Set(d.carpet_rooms || []);
  S.selected.clear(); S.carpetExcl.clear();
  // Debug: mostrar mapa robot_name → display_name para diagnosticar selección errónea
  log('🗂 Habitaciones (robot_id → nombre): '+Object.entries(S.rooms).map(([k,v])=>k+(k!==v?'→'+v:'')).join(' | '));
  applyMopMode();
  renderRooms();
  document.getElementById('roomsSection').style.display = 'block';
  setMapStatus('✓ Mapa cargado — '+Object.keys(S.rooms).length+' habitaciones');
}

function renderRooms(){
  const list = document.getElementById('roomList');
  list.innerHTML = '';
  const wet = window._mopAttached;
  for(const [rn, dn] of Object.entries(S.rooms)){
    const isCarpet   = S.carpet.has(rn);
    const isSelected = S.selected.has(rn);
    const carpetExcl = S.carpetExcl.has(rn);
    const row = document.createElement('div');
    row.className = 'room-row' + (isSelected?' selected':'');

    // Badge de alfombra
    let badgeHtml = '';
    if(isCarpet){
      if(wet){
        // Modo húmedo: alfombra siempre excluida (bloqueado)
        badgeHtml = '<div class="carpet-badge excl-on">🚫 sin alfombra</div>';
      } else if(carpetExcl){
        // Modo seco, alfombra excluida por usuario
        badgeHtml = '<div class="carpet-badge excl-on" data-carpet="'+rn+'">🟧 sin alfombra ↺</div>';
      } else {
        // Modo seco, alfombra incluida
        badgeHtml = '<div class="carpet-badge" data-carpet="'+rn+'">🟧 con alfombra ×</div>';
      }
    }

    row.innerHTML = `
      <div class="room-check">${isSelected?'✓':''}</div>
      <div class="room-name">${dn}</div>
      ${badgeHtml}
    `;

    // Click en la fila: seleccionar/deseleccionar habitación
    row.addEventListener('click', e=>{
      if(e.target.dataset.carpet) return;
      if(isSelected) S.selected.delete(rn);
      else S.selected.add(rn);
      renderRooms(); updateCleanBtn();
    });

    // Click en badge alfombra (solo modo seco): toggle incluir/excluir zona de alfombra
    if(!wet){
      const badge = row.querySelector('[data-carpet]');
      if(badge) badge.addEventListener('click', e=>{
        e.stopPropagation();
        if(carpetExcl) S.carpetExcl.delete(rn);
        else S.carpetExcl.add(rn);
        renderRooms(); updateCleanBtn();
      });
    }

    list.appendChild(row);
  }
}

function updateCleanBtn(){
  // El botón se habilita cuando hay habitaciones seleccionadas.
  // S.carpetExcl es independiente: no afecta si se puede limpiar o no.
  const count = S.selected.size;
  const btn = document.getElementById('cleanBtn');
  btn.disabled = count === 0;
  btn.textContent = count
    ? `🧹 Limpiar ${count} habitación${count>1?'es':''}`
    : '🧹 Limpiar seleccionadas';
}

async function cleanRooms(){
  const rooms      = [...S.selected];
  const carpetExcl = [...S.carpetExcl];
  if(!rooms.length){ log('⚠ Ninguna habitación seleccionada'); return; }
  log('🧹 Enviando: '+rooms.join(', '));
  const d = await api('/api/clean-rooms','POST',{rooms, carpet_excluded: carpetExcl});
  if(d.ok) log('✓ Robot recibirá: '+(d.cleaning||rooms).join(', '));
  else log('⚠ '+d.msg);
}

function setMapStatus(html){
  document.getElementById('mapStatus').innerHTML = html;
}

// ── Logout ────────────────────────────────────────────────────────────────────
const DAY_NAMES = ['Lun','Mar','Mié','Jue','Vie','Sáb','Dom'];

function esc(value){
  return String(value ?? '').replace(/[&<>"']/g, ch=>({
    '&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'
  }[ch]));
}

async function prepareSchedules(){
  if(Object.keys(S.rooms).length===0){
    let roomData = await api('/api/rooms');
    S.rooms = roomData.rooms || {};
    S.carpet = new Set(roomData.carpet_rooms || []);
    if(Object.keys(S.rooms).length===0){
      roomData = await api('/api/map','POST');
      if(roomData.ok){
        S.rooms = roomData.rooms || {};
        S.carpet = new Set(roomData.carpet_rooms || []);
      }
    }
  }
  renderScheduleRooms();
  await loadSchedules();
}

function renderScheduleDays(){
  const host = document.getElementById('scheduleDays');
  host.innerHTML = '';
  DAY_NAMES.forEach((name, day)=>{
    const chip = document.createElement('div');
    chip.className = 'day-chip'+(S.scheduleDays.has(day)?' selected':'');
    chip.textContent = name;
    chip.addEventListener('click', ()=>{
      if(S.scheduleDays.has(day)) S.scheduleDays.delete(day);
      else S.scheduleDays.add(day);
      renderScheduleDays();
    });
    host.appendChild(chip);
  });
}

function renderScheduleRooms(){
  const host = document.getElementById('scheduleRooms');
  host.innerHTML = '';
  const entries = Object.entries(S.rooms);
  if(!entries.length){
    host.innerHTML = '<div class="schedule-sub">No se pudieron cargar los ambientes. Abre primero la pestaña Mapa.</div>';
    return;
  }
  entries.forEach(([roomId, displayName])=>{
    const selected = S.scheduleRooms.has(roomId);
    const row = document.createElement('div');
    row.className = 'schedule-room'+(selected?' selected':'');
    const mark = document.createElement('div');
    mark.className = 'schedule-room-mark';
    mark.textContent = selected ? '✓' : '';
    const label = document.createElement('div');
    label.textContent = displayName;
    row.append(mark, label);
    row.addEventListener('click', ()=>{
      if(S.scheduleRooms.has(roomId)) S.scheduleRooms.delete(roomId);
      else S.scheduleRooms.add(roomId);
      renderScheduleRooms();
    });
    host.appendChild(row);
  });
}

function openScheduleForm(item=null){
  S.scheduleEditing = item ? item.id : null;
  S.scheduleDays = new Set(item ? item.days : [(new Date().getDay()+6)%7]);
  S.scheduleRooms = new Set(item ? item.rooms : []);
  document.getElementById('scheduleFormTitle').textContent = item ? 'Editar tarea' : 'Nueva tarea';
  document.getElementById('scheduleName').value = item ? item.name : '';
  document.getElementById('scheduleTime').value = item ? item.time : '09:00';
  document.getElementById('scheduleForm').classList.add('open');
  renderScheduleDays();
  renderScheduleRooms();
  document.getElementById('scheduleName').focus();
}

function closeScheduleForm(){
  S.scheduleEditing = null;
  document.getElementById('scheduleForm').classList.remove('open');
}

async function saveSchedule(){
  const payload = {
    name: document.getElementById('scheduleName').value.trim(),
    time: document.getElementById('scheduleTime').value,
    days: [...S.scheduleDays],
    rooms: [...S.scheduleRooms],
  };
  if(!S.scheduleEditing) payload.enabled = true;
  const url = S.scheduleEditing ? '/api/schedules/'+S.scheduleEditing : '/api/schedules';
  const method = S.scheduleEditing ? 'PUT' : 'POST';
  const result = await api(url, method, payload);
  if(!result.ok){ alert(result.msg || 'No se pudo guardar la tarea'); return; }
  closeScheduleForm();
  await loadSchedules();
}

async function loadSchedules(){
  const result = await api('/api/schedules');
  if(!result.ok){
    document.getElementById('scheduleList').innerHTML =
      '<div class="schedule-empty">⚠ '+esc(result.msg || 'No se pudieron cargar las tareas')+'</div>';
    return;
  }
  S.schedules = result.schedules || [];
  const warning = document.getElementById('scheduleStorageWarning');
  warning.innerHTML = result.persistent_storage ? '' :
    '<div class="storage-warn">⚠ Para conservar las tareas después de un nuevo despliegue, configura un volumen persistente en Railway.</div>';
  renderSchedules();
}

function scheduleWhen(item){ return item.days.map(day=>DAY_NAMES[day]).join(', '); }
function scheduleRoomNames(item){ return item.rooms.map(room=>S.rooms[room] || room).join(', '); }

function formatNextRun(value){
  if(!value) return 'Sin próxima ejecución';
  return 'Próxima: '+new Date(value).toLocaleString('es-AR',{
    weekday:'short',day:'2-digit',month:'2-digit',hour:'2-digit',minute:'2-digit'
  });
}

function renderSchedules(){
  const host = document.getElementById('scheduleList');
  if(!S.schedules.length){
    host.innerHTML = '<div class="schedule-empty">Todavía no hay tareas.<br>Crea una y elige sus ambientes.</div>';
    return;
  }
  host.innerHTML = S.schedules.map(item=>{
    const statusIcon = item.last_status==='completed' ? '✓ '
      : item.last_status==='running' ? '⏳ ' : '⚠ ';
    const last = item.last_run_at
      ? (statusIcon+(item.last_message || 'Ejecutada'))
      : 'Aún no se ejecutó';
    return `<div class="schedule-card ${item.enabled?'':'disabled'}">
      <div class="schedule-card-top">
        <div><div class="schedule-card-name">${esc(item.name)}</div>
             <div class="schedule-meta">${esc(scheduleWhen(item))}</div></div>
        <div class="schedule-time">${esc(item.time)}</div>
      </div>
      <div class="schedule-meta">🧹 ${esc(scheduleRoomNames(item))}</div>
      <div class="schedule-meta">${esc(formatNextRun(item.next_run_at))}</div>
      <div class="schedule-result">${esc(last)}</div>
      <div class="schedule-actions">
        <button class="btn-sm" onclick="editSchedule('${item.id}')">Editar</button>
        <button class="btn-sm" onclick="toggleSchedule('${item.id}',${!item.enabled})">${item.enabled?'Pausar':'Activar'}</button>
        <button class="btn-sm btn-danger" onclick="deleteSchedule('${item.id}')">Eliminar</button>
      </div>
    </div>`;
  }).join('');
}

function editSchedule(id){
  const item = S.schedules.find(schedule=>schedule.id===id);
  if(item) openScheduleForm(item);
}

async function toggleSchedule(id, enabled){
  const result = await api('/api/schedules/'+id,'PUT',{enabled});
  if(!result.ok){ alert(result.msg || 'No se pudo actualizar la tarea'); return; }
  await loadSchedules();
}

async function deleteSchedule(id){
  const item = S.schedules.find(schedule=>schedule.id===id);
  if(!confirm('¿Eliminar la tarea "'+(item?.name || '')+'"?')) return;
  const result = await api('/api/schedules/'+id,'DELETE');
  if(!result.ok){ alert(result.msg || 'No se pudo eliminar la tarea'); return; }
  await loadSchedules();
}

async function doLogout(){
  if(!confirm('¿Cerrar sesión?')) return;
  await api('/auth/logout','POST');
  window.location='/login';
}

// ── Log ───────────────────────────────────────────────────────────────────────
function log(msg){
  const area = document.getElementById('logArea');
  const ts   = new Date().toLocaleTimeString('es',{hour:'2-digit',minute:'2-digit',second:'2-digit'});
  area.innerHTML += `<div>[${ts}] ${msg}</div>`;
  area.scrollTop = area.scrollHeight;
}

// ── Fetch helper ──────────────────────────────────────────────────────────────
async function api(url, method='GET', body=null){
  if(DEMO_MODE){
    await new Promise(resolve=>setTimeout(resolve, 180));
    if(url === '/api/power-mode'){
      const values = {eco:1, normal:0, max:2};
      demoPowerMode = values[body && body.mode] ?? demoPowerMode;
    }
    if(url === '/api/status' || url === '/api/refresh' || url === '/api/power-mode'){
      return {ok:true, mode:'STOP', mode_text:'● Modo demostración', mode_color:'#2896FF',
              battery:82, name:'Shark (modo demo)', mop_attached:false,
              power_mode:demoPowerMode};
    }
    if(url === '/api/notifications'){
      return {ok:true, notifications:[], unread_count:0};
    }
    if(url.startsWith('/api/notifications/')) return {ok:true};
    return {ok:false, msg:'Esta acción no controla el robot en modo demo'};
  }
  try {
    const opts = { method, headers: {'Content-Type':'application/json'} };
    if(body) opts.body = JSON.stringify(body);
    const r = await fetch(url, opts);
    return await r.json();
  } catch(e){ return {ok:false, msg:String(e)}; }
}
</script>
</body></html>"""


# ── Inicialización al importar (gunicorn arranca aquí) ───────────────────────
def _startup():
    _init_schedule_db()
    if not os.environ.get("SHARK_DISABLE_SCHEDULER"):
        threading.Thread(target=_schedule_worker, daemon=True, name="shark-scheduler").start()
        threading.Thread(
            target=_mission_monitor_worker, daemon=True, name="shark-mission-monitor"
        ).start()
    if SHARKIQ_OK and not os.environ.get("SHARK_SKIP_AUTOLOAD"):
        try:
            _try_autoload()
        except Exception as e:
            print(f"[STARTUP] WARN: {e}", flush=True)

_startup()

# ── Punto de entrada local ────────────────────────────────────────────────────
if __name__ == "__main__":
    import socket
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(("8.8.8.8", 80))
        local_ip = s.getsockname()[0]
        s.close()
    except Exception:
        local_ip = "localhost"

    print("=" * 52)
    print("  🦈  Shark IQ Web Controller")
    print("=" * 52)
    if CLOUD:
        print(f"  Cloud → puerto {PORT}")
    else:
        print(f"  PC       → http://localhost:{PORT}")
        print(f"  Celular  → http://{local_ip}:{PORT}")
        print("  (ambos deben estar en la misma red WiFi)")
    print("=" * 52)
    if not SHARKIQ_OK:
        print("  ⚠  sharkiq no encontrado — instala dependencias")
    print("  Presiona Ctrl+C para detener\n")
    app.run(host="0.0.0.0", port=PORT, debug=False, use_reloader=False)
