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
import subprocess
import sys
import threading
import urllib.parse
from datetime import datetime, timedelta

from flask import Flask, Response, jsonify, make_response, redirect, render_template_string, request, session, url_for

# ── Importar sharkiq ─────────────────────────────────────────────────────────
try:
    from sharkiq import get_ayla_api, OperatingModes, Properties
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
}
_state_lock = threading.Lock()

# ── Bucle asyncio en hilo secundario ─────────────────────────────────────────
_loop = asyncio.new_event_loop()
_loop_thread = threading.Thread(target=lambda: _loop.run_forever(), daemon=True)
_loop_thread.start()


def _run_async(coro):
    """Ejecuta una coroutine en el loop secundario y espera el resultado."""
    future = asyncio.run_coroutine_threadsafe(coro, _loop)
    return future.result(timeout=60)


# ── PKCE ─────────────────────────────────────────────────────────────────────
def _pkce_generate():
    chars = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789"
    verifier  = "".join(random.choice(chars) for _ in range(43))
    state_val = "".join(random.choice(chars) for _ in range(43))
    digest    = hashlib.sha256(codecs.encode(verifier, "utf-8")).digest()
    challenge = (base64.b64encode(digest).decode()
                 .replace("+", "-").replace("/", "_").replace("=", "").replace("$", ""))
    return verifier, challenge, state_val


def _build_auth_url(verifier, challenge, state_val):
    params = {
        "os": "ios",
        "response_type": "code",
        "mobile_shark_app_version": "rn1.01",
        "client_id": AUTH0_CLIENT_ID,
        "state": state_val,
        "scope": AUTH0_SCOPES,
        "redirect_uri": AUTH0_REDIRECT_URI,
        "code_challenge": challenge,
        "screen_hint": "signin",
        "code_challenge_method": "S256",
        "ui_locales": "en",
    }
    return AUTH0_URL + "/authorize?" + urllib.parse.urlencode(params)


# ── Tokens persistentes ───────────────────────────────────────────────────────
def _save_tokens(data: dict):
    with open(TOKEN_FILE, "w") as f:
        json.dump(data, f)


def _load_tokens() -> dict | None:
    if not os.path.exists(TOKEN_FILE):
        return None
    try:
        with open(TOKEN_FILE) as f:
            return json.load(f)
    except Exception:
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


# ── Mapeo de modo a texto/color ───────────────────────────────────────────────
MODE_MAP = {
    "START":      ("▶ Limpiando",        "#3fb950"),
    "STOP":       ("⏹ Detenido",         "#f85149"),
    "PAUSE":      ("⏸ Pausado",          "#e3b341"),
    "RETURN":     ("🏠 Volviendo a base", "#58a6ff"),
    "RECHARGING": ("🔌 Cargando",         "#3fb950"),
    "UNKNOWN":    ("● Desconocido",       "#8b949e"),
}


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
        charging = vac.get_property_value("GET_Charging_Status")
        docked   = vac.get_property_value("GET_Docked_Status")
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
        with _state_lock:
            _state["mode"]    = mode_key
            _state["mode_text"]  = mode_text
            _state["mode_color"] = mode_color
            _state["battery"] = battery
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
        has_map=(_state["map_png"] is not None))


@app.route("/api/status")
def api_status():
    vac = _state["vacuum"]
    if vac is None:
        return jsonify({"ok": False, "msg": "No conectado"})
    return jsonify({
        "ok":         True,
        "mode":       _state.get("mode", "UNKNOWN"),
        "mode_text":  _state.get("mode_text", "● Desconocido"),
        "mode_color": _state.get("mode_color", "#8b949e"),
        "battery":    _state.get("battery"),
        "name":       vac.name,
    })


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
        "dock":  OperatingModes.STOP,
    }
    mode = CMD_MAP.get(cmd)
    if mode is None:
        return jsonify({"ok": False, "msg": f"Comando desconocido: {cmd}"})

    try:
        _run_async(vac.async_set_operating_mode(mode))
        import time; time.sleep(1.5)
        _refresh_state()
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


@app.route("/api/clean-rooms", methods=["POST"])
def api_clean_rooms():
    if not _state["authed"]:
        return jsonify({"ok": False, "msg": "No autenticado"})
    data = request.get_json() or {}
    selected  = data.get("rooms", [])      # [robot_name, ...]
    excluded  = set(data.get("excluded", []))  # carpet rooms to skip
    to_clean  = [r for r in selected if r not in excluded]
    if not to_clean:
        return jsonify({"ok": False, "msg": "Ninguna habitación seleccionada"})

    vac = _state["vacuum"]
    try:
        _run_async(vac.async_set_operating_mode(OperatingModes.START,
                                                 room_names=to_clean))
        return jsonify({"ok": True, "cleaning": to_clean})
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
        print(f"  ⚠ No se pudo restaurar sesión: {e}")


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
    <button class="btn btn-primary" id="webBtn" onclick="startWebOAuth()">
      🔐 Iniciar sesión con Shark
    </button>
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
  </div>

  <!-- Paso 2: pegar URL de redirección -->
  <div id="step-paste" style="display:none">
    <p style="font-size:13px;font-weight:700;color:#E8F3FF;margin-bottom:8px;text-align:left">Pasos:</p>
    <ol class="steps">
      <li>Abrí el <a id="sharkLoginLink" href="#" target="_blank">Shark Login ↗</a></li>
      <li>Ingresá con tu cuenta Shark</li>
      <li>El navegador mostrará un error — <strong style="color:#E8F3FF">copiá la URL</strong> de la barra de direcciones</li>
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
  <button class="btn btn-primary" id="loginBtn" onclick="startBrowser()">
    🖥️ Iniciar sesión en el PC
  </button>
  <p class="hint" style="text-align:center">Se abrirá una ventana en el PC para autenticarte.<br>
    <strong style="color:#E8F3FF">Fijate en el escritorio del PC</strong> cuando hagas clic.</p>

  <div class="divider">o</div>
  <button class="btn-ghost" onclick="toggleEmail()">📧 Iniciar sesión con email</button>
  <div id="emailForm">
    <br>
    <input class="field" type="email" id="emailInp" placeholder="Email" autocomplete="email">
    <input class="field" type="password" id="passInp" placeholder="Contraseña" autocomplete="current-password">
    <button class="btn btn-primary" id="emailBtn" onclick="startEmail()">Conectar</button>
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

// ── Cloud: web OAuth ────────────────────────────────────────────────────────
async function startWebOAuth(){
  // Abrir la ventana ANTES del await para evitar que el browser bloquee el popup
  const popup = window.open('', '_blank');
  document.getElementById('webBtn').disabled = true;
  setStatus('<span class="spinner"></span> Generando URL...', '');
  const d = await apiFetch('/auth/browser-url');
  if(!d.ok){
    if(popup) popup.close();
    setStatus('❌ '+d.msg, 'err');
    document.getElementById('webBtn').disabled=false;
    return;
  }
  if(popup) popup.location.href = d.url;
  document.getElementById('sharkLoginLink').href = d.url;
  document.getElementById('step-launch').style.display = 'none';
  document.getElementById('step-paste').style.display = 'block';
  setStatus('', '');
}

function resetOAuth(){
  document.getElementById('step-launch').style.display = 'block';
  document.getElementById('step-paste').style.display = 'none';
  document.getElementById('webBtn').disabled = false;
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
  document.getElementById('loginBtn').disabled = true;
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
.conn{display:flex;flex-direction:column;align-items:flex-end;gap:2px}
.conn-dot{font-size:18px}
.conn-lbl{font-size:11px;color:#AAD4FF}
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
</style>
</head>
<body>
<div class="hdr">
  <div>
    <div class="hdr-logo">SHARK <span>IQ Controller</span></div>
  </div>
  <div class="conn">
    <div class="conn-dot" id="connDot">●</div>
    <div class="conn-lbl" id="connLbl">Conectando...</div>
  </div>
</div>

<!-- Robot card -->
<div class="card">
  <div class="robot-row">
    <div class="robot-icon">🤖</div>
    <div class="robot-info">
      <div class="robot-name" id="robotName">{{ robot_name }}</div>
      <div class="robot-mode" id="robotMode" style="color:#5E7E9A">● Actualizando...</div>
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
</div>

<!-- Panel: Control -->
<div class="panel active" id="panel-control">
  <div class="btn-grid">
    <button class="btn btn-start" onclick="sendCmd('start')">▶ Iniciar</button>
    <button class="btn btn-pause" onclick="sendCmd('pause')">⏸ Pausar</button>
    <button class="btn btn-dock"  onclick="sendCmd('dock')">🏠 Volver a la base</button>
  </div>
  <div class="btn-sm-grid">
    <button class="btn-sm" onclick="doRefresh()">🔄 Actualizar</button>
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
      <span style="font-size:11px;color:#5E7E9A">🟫 = alfombra — toca para excluir</span>
    </div>
    <div class="room-list" id="roomList"></div>
    <button class="btn-clean" id="cleanBtn" disabled onclick="cleanRooms()">
      🧹 Limpiar seleccionadas
    </button>
  </div>
</div>

<script>
// ── Estado ────────────────────────────────────────────────────────────────────
const S = { selected: new Set(), excluded: new Set(), rooms: {}, carpet: new Set() };

// ── Tabs ──────────────────────────────────────────────────────────────────────
function switchTab(name){
  document.querySelectorAll('.tab').forEach((t,i)=>{
    t.classList.toggle('active', ['control','map'][i]===name);
  });
  document.querySelectorAll('.panel').forEach(p=>{
    p.classList.toggle('active', p.id==='panel-'+name);
  });
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
}

// Auto-refresh every 30 s
setInterval(()=>{
  api('/api/status').then(d=>{ if(d.ok) updateStatus(d); });
}, 30000);

// Initial load
doRefresh();

// ── Comandos ──────────────────────────────────────────────────────────────────
async function sendCmd(cmd){
  const labels = {start:'Iniciando limpieza...',pause:'Pausando...',dock:'Volviendo a la base...'};
  log('⏳ '+labels[cmd]);
  const d = await api('/api/command/'+cmd,'POST');
  if(d.ok){ updateStatus(d); log('✓ '+d.mode_text); }
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
  S.selected.clear(); S.excluded.clear();
  renderRooms();
  document.getElementById('roomsSection').style.display = 'block';
  setMapStatus('✓ Mapa cargado — '+Object.keys(S.rooms).length+' habitaciones');
}

function renderRooms(){
  const list = document.getElementById('roomList');
  list.innerHTML = '';
  for(const [rn, dn] of Object.entries(S.rooms)){
    const row = document.createElement('div');
    row.className = 'room-row' + (S.selected.has(rn)?' selected':'') + (S.excluded.has(rn)?' excl':'');
    row.innerHTML = `
      <div class="room-check">${S.selected.has(rn)?'✓':''}</div>
      <div class="room-name">${dn}</div>
      ${S.carpet.has(rn)?'<div class="carpet-badge'+(S.excluded.has(rn)?' excl-on':'')+'" data-rn="'+rn+'">🟫 excl.</div>':''}
    `;
    // Toggle selección
    row.addEventListener('click', e=>{
      if(e.target.classList.contains('carpet-badge')) return;
      if(S.selected.has(rn)) S.selected.delete(rn);
      else S.selected.add(rn);
      renderRooms(); updateCleanBtn();
    });
    // Toggle exclusión alfombra
    const badge = row.querySelector('.carpet-badge');
    if(badge) badge.addEventListener('click', e=>{
      e.stopPropagation();
      if(S.excluded.has(rn)) S.excluded.delete(rn);
      else S.excluded.add(rn);
      renderRooms(); updateCleanBtn();
    });
    list.appendChild(row);
  }
}

function updateCleanBtn(){
  const active = [...S.selected].filter(r=>!S.excluded.has(r));
  const btn = document.getElementById('cleanBtn');
  btn.disabled = active.length === 0;
  btn.textContent = active.length
    ? `🧹 Limpiar ${active.length} habitación${active.length>1?'es':''}`
    : '🧹 Limpiar seleccionadas';
}

async function cleanRooms(){
  const rooms    = [...S.selected];
  const excluded = [...S.excluded];
  log('🧹 Limpiando '+rooms.filter(r=>!excluded.includes(r)).length+' habitaciones...');
  const d = await api('/api/clean-rooms','POST',{rooms, excluded});
  if(d.ok) log('✓ Limpieza iniciada');
  else log('⚠ '+d.msg);
}

function setMapStatus(html){
  document.getElementById('mapStatus').innerHTML = html;
}

// ── Logout ────────────────────────────────────────────────────────────────────
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
    if SHARKIQ_OK:
        try:
            _try_autoload()
        except Exception as e:
            print(f"[STARTUP] ⚠ {e}", flush=True)

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
