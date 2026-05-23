"""
Shark Browser Auth — Script auxiliar de autenticación OAuth PKCE.
Abre un navegador embebido, el usuario inicia sesión, y captura el código
de autorización de la redirección automática.

Uso: python shark_browser_auth.py <auth_url>
Salida (stdout): <redirect_url>  o  ERROR:<mensaje>
"""

import sys
import threading


def main():
    if len(sys.argv) < 2:
        print("ERROR:sin_url")
        sys.exit(1)

    auth_url = sys.argv[1]

    try:
        import webview
        from webview.platforms.edgechromium import EdgeChrome
    except ImportError:
        print("ERROR:pywebview_no_instalado")
        sys.exit(1)

    SHARK_SCHEME = "com.sharkninja.shark://"
    captured = []
    window_ref = [None]

    def _close():
        import time
        time.sleep(0.3)
        try:
            if window_ref[0]:
                window_ref[0].destroy()
        except Exception:
            pass

    # ── Monkey-patch NavigationStarting ──────────────────────────────────────
    # pywebview 6.x no expone la URL en before_load, pero el handler interno
    # on_navigation_start recibe args.Uri y args.Cancel — lo parcheamos para
    # interceptar la redirección al scheme de Shark antes de que WebView2
    # intente abrirlo (y falle).
    original_on_nav_start = EdgeChrome.on_navigation_start

    def patched_on_nav_start(self, sender, args):
        try:
            url = str(args.Uri)
            if SHARK_SCHEME in url:
                if not captured:
                    captured.append(url)
                    threading.Thread(target=_close, daemon=True).start()
                args.Cancel = True  # Cancelar la navegación al scheme desconocido
                return
        except Exception:
            pass
        original_on_nav_start(self, sender, args)

    EdgeChrome.on_navigation_start = patched_on_nav_start

    # ── JS fallback para redirecciones client-side ────────────────────────────
    class Api:
        def capture(self, url):
            if not captured:
                captured.append(url)
                threading.Thread(target=_close, daemon=True).start()

    api = Api()

    def on_loaded():
        try:
            window_ref[0].evaluate_js("""
                (function() {
                    if (window._sharkHooked) return;
                    window._sharkHooked = true;
                    var SCHEME = 'com.sharkninja.shark://';
                    function tryCapture(url) {
                        if (url && url.indexOf(SCHEME) === 0) {
                            try { window.pywebview.api.capture(url); } catch(e) {}
                            return true;
                        }
                        return false;
                    }
                    try {
                        var origAssign = window.location.assign.bind(window.location);
                        window.location.assign = function(u) {
                            if (!tryCapture(u)) origAssign(u);
                        };
                        var origReplace = window.location.replace.bind(window.location);
                        window.location.replace = function(u) {
                            if (!tryCapture(u)) origReplace(u);
                        };
                    } catch(e) {}
                })();
            """)
        except Exception:
            pass

    window_ref[0] = webview.create_window(
        "Iniciar sesión — Shark Clean",
        auth_url,
        js_api=api,
        width=480,
        height=680,
        resizable=True,
        text_select=False,
    )
    window_ref[0].events.loaded += on_loaded

    webview.start()

    if captured:
        print(captured[0], flush=True)
        sys.exit(0)
    else:
        print("ERROR:login_cancelado", flush=True)
        sys.exit(1)


if __name__ == "__main__":
    main()
