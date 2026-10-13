"""
panel.py - Web panel for the Telegram Master Engine.

Serves the front-end pages (login.html, owner_login.html, mode.html) and
implements the JSON API they call:

    POST /api/auth/login              POST /api/auth/verify-login-otp
    POST /api/auth/send-register-otp  POST /api/auth/verify-register-otp
    POST /api/auth/register           POST /api/auth/forgot-otp
    POST /api/auth/reset-password     POST /api/owner/login

Users live in MongoDB Atlas (collection 'panel_users'); OTPs are emailed via
SMTP and also returned in the JSON response, because the supplied front-end
reads data.otp and prints it on screen. See README for the security caveat.

No third-party dependency beyond what the bot already installs
(aiohttp, pymongo); email/hashing use the standard library.
"""

import os
import re
import time
import secrets
import hashlib
import logging
import smtplib
from email.mime.text import MIMEText
from email.utils import formataddr

from aiohttp import web

try:
    from pymongo import MongoClient
except Exception:  # pragma: no cover - pymongo is a hard requirement in practice
    MongoClient = None

log = logging.getLogger("panel")
if not log.handlers:
    logging.basicConfig(level=logging.INFO, format="%(asctime)s [panel] %(levelname)s %(message)s")

# ---------------------------------------------------------------------------
# Configuration (all overridable via environment variables)
# ---------------------------------------------------------------------------
PANEL_DIR = os.path.dirname(os.path.abspath(__file__))

MONGO_URI = os.getenv("MONGODB_URI", "").strip()
DB_NAME = os.getenv("PANEL_DB_NAME", "igtgwp_db")

OWNER_USERNAME = os.getenv("OWNER_USERNAME", "owner")
OWNER_PASSCODE = os.getenv("OWNER_PASSCODE", "")

SMTP_HOST = os.getenv("SMTP_HOST", "").strip()
SMTP_PORT = int(os.getenv("SMTP_PORT", "587"))
SMTP_USER = os.getenv("SMTP_USER", "").strip()
SMTP_PASS = os.getenv("SMTP_PASS", "")
SMTP_FROM = os.getenv("SMTP_FROM", SMTP_USER).strip()
SMTP_FROM_NAME = os.getenv("SMTP_FROM_NAME", "IGTGWP MASTER")
SMTP_SSL = os.getenv("SMTP_SSL", "false").lower() in ("1", "true", "yes")

OTP_TTL_SECONDS = int(os.getenv("OTP_TTL_SECONDS", "600"))
SESSION_TTL_SECONDS = int(os.getenv("SESSION_TTL_SECONDS", str(7 * 24 * 3600)))

EMAIL_RE = re.compile(r"^[^@\s]+@[^@\s]+\.[^@\s]+$")

# ---------------------------------------------------------------------------
# Storage
# ---------------------------------------------------------------------------
_db = None


def get_db():
    """Lazily connect to MongoDB Atlas and return the panel database."""
    global _db
    if _db is not None:
        return _db
    if not MONGO_URI:
        raise RuntimeError(
            "MONGODB_URI is not set. The panel stores users in MongoDB Atlas; "
            "set MONGODB_URI in the environment."
        )
    if MongoClient is None:
        raise RuntimeError("pymongo is not installed.")
    client = MongoClient(MONGO_URI, serverSelectionTimeoutMS=5000)
    _db = client[DB_NAME]
    log.info("Panel connected to MongoDB database '%s'", DB_NAME)
    return _db


def _users():
    return get_db()["panel_users"]


def _otps():
    return get_db()["panel_otps"]


def _sessions():
    return get_db()["panel_sessions"]


def ensure_indexes():
    try:
        _users().create_index("email", unique=True)
        _otps().create_index([("email", 1), ("purpose", 1)])
        _sessions().create_index("token", unique=True)
        _sessions().create_index("expires", expireAfterSeconds=0)
    except Exception as e:  # non-fatal
        log.warning("Could not create panel indexes: %s", e)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------
def cors_headers():
    return {
        "Access-Control-Allow-Origin": "*",
        "Access-Control-Allow-Methods": "GET, POST, OPTIONS",
        "Access-Control-Allow-Headers": "Content-Type, Authorization",
    }


def json_ok(payload, status=200):
    return web.json_response(payload, status=status, headers=cors_headers())


def json_err(message, status=200):
    # Front-end branches on data.success, so keep 200 unless the caller needs otherwise.
    return web.json_response({"success": False, "message": message}, status=status, headers=cors_headers())


def hash_password(password, salt=None):
    salt = salt or secrets.token_hex(16)
    digest = hashlib.pbkdf2_hmac("sha256", password.encode("utf-8"), bytes.fromhex(salt), 120_000)
    return digest.hex(), salt


def verify_password(password, stored_hash, salt):
    try:
        calc, _ = hash_password(password, salt)
        return secrets.compare_digest(calc, stored_hash)
    except Exception:
        return False


def gen_otp():
    return f"{secrets.randbelow(1_000_000):06d}"


def mask_email(email):
    try:
        name, domain = email.split("@", 1)
        if len(name) <= 2:
            masked = name[0] + "*"
        else:
            masked = name[0] + "*" * (len(name) - 2) + name[-1]
        return f"{masked}@{domain}"
    except Exception:
        return email


def store_otp(email, purpose, otp):
    _otps().replace_one(
        {"email": email, "purpose": purpose},
        {
            "email": email,
            "purpose": purpose,
            "otp": otp,
            "verified": False,
            "expires": int(time.time()) + OTP_TTL_SECONDS,
            "created": int(time.time()),
        },
        upsert=True,
    )


def check_otp(email, purpose, otp, mark_verified=False):
    doc = _otps().find_one({"email": email, "purpose": purpose})
    if not doc:
        return False
    if doc.get("expires", 0) < int(time.time()):
        return False
    if not secrets.compare_digest(str(doc.get("otp", "")), str(otp)):
        return False
    if mark_verified:
        _otps().update_one({"_id": doc["_id"]}, {"$set": {"verified": True}})
    return True


def create_session(email, role="user"):
    token = secrets.token_urlsafe(32)
    _sessions().insert_one({
        "token": token,
        "email": email,
        "role": role,
        "created": int(time.time()),
        "expires": int(time.time()) + SESSION_TTL_SECONDS,
    })
    return token


def send_email(to_addr, subject, body):
    """Return True if the mail was handed to the SMTP server, else False."""
    if not (SMTP_HOST and SMTP_USER):
        log.warning("SMTP not configured; OTP for %s not emailed (returned in API response).", to_addr)
        return False
    try:
        msg = MIMEText(body, "plain", "utf-8")
        msg["Subject"] = subject
        msg["From"] = formataddr((SMTP_FROM_NAME, SMTP_FROM))
        msg["To"] = to_addr

        if SMTP_SSL:
            server = smtplib.SMTP_SSL(SMTP_HOST, SMTP_PORT, timeout=20)
        else:
            server = smtplib.SMTP(SMTP_HOST, SMTP_PORT, timeout=20)
            server.ehlo()
            server.starttls()
            server.ehlo()
        server.login(SMTP_USER, SMTP_PASS)
        server.sendmail(SMTP_FROM, [to_addr], msg.as_string())
        server.quit()
        log.info("OTP email sent to %s", to_addr)
        return True
    except Exception as e:
        log.error("Failed to email %s: %s", to_addr, e)
        return False


def email_otp(to_addr, otp, purpose):
    titles = {
        "login": "Your login verification code",
        "register": "Verify your email address",
        "reset": "Reset your password",
    }
    subject = titles.get(purpose, "Your verification code")
    body = (
        f"{subject}\n\n"
        f"Your 6-digit code is: {otp}\n\n"
        f"It expires in {OTP_TTL_SECONDS // 60} minutes. "
        f"If you did not request this, you can ignore this email."
    )
    return send_email(to_addr, f"{SMTP_FROM_NAME}: {subject}", body)


# ---------------------------------------------------------------------------
# Static page routes
# ---------------------------------------------------------------------------
async def _serve(name):
    path = os.path.join(PANEL_DIR, name)
    if not os.path.exists(path):
        return web.Response(status=404, text=f"{name} not found on server", headers=cors_headers())
    return web.FileResponse(path, headers={"Cache-Control": "no-store"})


async def page_login(request):
    return await _serve("login.html")


async def page_owner_login(request):
    return await _serve("owner_login.html")


async def page_mode(request):
    return await _serve("mode.html")


async def page_root(request):
    raise web.HTTPFound("/login")


# ---------------------------------------------------------------------------
# Auth API
# ---------------------------------------------------------------------------
async def api_login(request):
    try:
        data = await request.json()
    except Exception:
        return json_err("Invalid request body.")
    email = (data.get("email") or "").strip().lower()
    password = data.get("password") or ""

    user = _users().find_one({"email": email})
    if not user or not verify_password(password, user.get("pw_hash", ""), user.get("salt", "")):
        return json_err("Invalid email or password!")
    if not user.get("verified", False):
        return json_err("Please verify your email before signing in.")

    otp = gen_otp()
    store_otp(email, "login", otp)
    emailed = email_otp(email, otp, "login")

    return json_ok({
        "success": True,
        "requireOtp": True,
        "email": email,
        "maskedEmail": mask_email(email),
        "otp": otp,  # front-end displays this; see README security note
        "emailed": emailed,
        "message": "OTP sent to your registered email." if emailed else "OTP generated (email not configured).",
    })


async def api_verify_login_otp(request):
    try:
        data = await request.json()
    except Exception:
        return json_err("Invalid request body.")
    email = (data.get("email") or "").strip().lower()
    otp = (data.get("otp") or "").strip()

    if not check_otp(email, "login", otp):
        return json_err("Invalid or expired OTP code!")

    token = create_session(email, "user")
    resp = json_ok({"success": True, "message": "Login verified! Redirecting...", "redirect": "/mode"})
    resp.set_cookie("panel_session", token, httponly=True, samesite="Lax", max_age=SESSION_TTL_SECONDS)
    return resp


async def api_send_register_otp(request):
    try:
        data = await request.json()
    except Exception:
        return json_err("Invalid request body.")
    email = (data.get("email") or "").strip().lower()

    if not EMAIL_RE.match(email):
        return json_err("Enter a valid email address to receive the OTP!")
    if _users().find_one({"email": email}):
        return json_err("This email is already registered. Please sign in.")

    otp = gen_otp()
    store_otp(email, "register", otp)
    emailed = email_otp(email, otp, "register")
    return json_ok({
        "success": True,
        "otp": otp,
        "emailed": emailed,
        "message": "OTP sent to your email." if emailed else "OTP generated (email not configured).",
    })


async def api_verify_register_otp(request):
    try:
        data = await request.json()
    except Exception:
        return json_err("Invalid request body.")
    email = (data.get("email") or "").strip().lower()
    otp = (data.get("otp") or "").strip()

    if not check_otp(email, "register", otp, mark_verified=True):
        return json_err("Invalid or expired OTP code!")
    return json_ok({"success": True, "message": "Email verified successfully!"})


async def api_register(request):
    try:
        data = await request.json()
    except Exception:
        return json_err("Invalid request body.")
    name = (data.get("name") or "").strip()
    email = (data.get("email") or "").strip().lower()
    phone = (data.get("phone") or "").strip()
    password = data.get("password") or ""

    if not EMAIL_RE.match(email):
        return json_err("Please provide a valid email address.")
    if len(password) < 6:
        return json_err("Password must be at least 6 characters.")
    if _users().find_one({"email": email}):
        return json_err("This email is already registered. Please sign in.")

    reg = _otps().find_one({"email": email, "purpose": "register", "verified": True})
    if not reg or reg.get("expires", 0) < int(time.time()):
        return json_err("Please verify your email OTP first!")

    pw_hash, salt = hash_password(password)
    _users().insert_one({
        "email": email,
        "name": name,
        "phone": phone,
        "pw_hash": pw_hash,
        "salt": salt,
        "verified": True,
        "created": int(time.time()),
    })
    _otps().delete_many({"email": email, "purpose": "register"})

    token = create_session(email, "user")
    resp = json_ok({"success": True, "message": "Account registered successfully!", "redirect": "/mode"})
    resp.set_cookie("panel_session", token, httponly=True, samesite="Lax", max_age=SESSION_TTL_SECONDS)
    return resp


async def api_forgot_otp(request):
    try:
        data = await request.json()
    except Exception:
        return json_err("Invalid request body.")
    email = (data.get("email") or "").strip().lower()

    if not _users().find_one({"email": email}):
        return json_err("No registered account with this email!")

    otp = gen_otp()
    store_otp(email, "reset", otp)
    emailed = email_otp(email, otp, "reset")
    return json_ok({
        "success": True,
        "otp": otp,
        "emailed": emailed,
        "message": "OTP sent to your email." if emailed else "OTP generated (email not configured).",
    })


async def api_reset_password(request):
    try:
        data = await request.json()
    except Exception:
        return json_err("Invalid request body.")
    email = (data.get("email") or "").strip().lower()
    otp = (data.get("otp") or "").strip()
    new_password = data.get("newPassword") or ""

    if len(new_password) < 6:
        return json_err("New password must be at least 6 characters.")
    if not check_otp(email, "reset", otp):
        return json_err("Invalid or expired OTP code!")

    pw_hash, salt = hash_password(new_password)
    result = _users().update_one({"email": email}, {"$set": {"pw_hash": pw_hash, "salt": salt}})
    if result.matched_count == 0:
        return json_err("No registered account with this email!")
    _otps().delete_many({"email": email, "purpose": "reset"})
    return json_ok({"success": True, "message": "Password reset successfully! Please sign in."})


async def api_owner_login(request):
    try:
        data = await request.json()
    except Exception:
        return json_err("Invalid request body.")
    username = (data.get("username") or "").strip()
    passcode = (data.get("ownerpass") or data.get("password") or "").strip()

    if not OWNER_PASSCODE:
        return json_err("Owner login is not configured on the server (set OWNER_PASSCODE).")
    if username == OWNER_USERNAME and secrets.compare_digest(passcode, OWNER_PASSCODE):
        token = create_session(username, "owner")
        resp = json_ok({"success": True, "message": "Owner access granted! Redirecting...", "redirect": "/mode"})
        resp.set_cookie("panel_session", token, httponly=True, samesite="Lax", max_age=SESSION_TTL_SECONDS)
        return resp
    return json_err("Invalid owner credentials!")


async def api_options(request):
    return web.Response(headers=cors_headers())


# ---------------------------------------------------------------------------
# Dashboard page + profile / session endpoints (telegram_dashboard.html)
# ---------------------------------------------------------------------------
DASHBOARD_JINJA_OWNER = re.compile(r"\{%\s*if\s+role\s*==\s*'owner'\s*%\}(.*?)\{%\s*endif\s*%\}", re.S)


def _current_session(request):
    """Return the panel_sessions document for this request's cookie, or None."""
    token = request.cookies.get("panel_session")
    if not token:
        return None
    try:
        doc = _sessions().find_one({"token": token})
    except Exception:
        return None
    if not doc or doc.get("expires", 0) < int(time.time()):
        return None
    return doc


async def page_dashboard(request):
    sess = _current_session(request)
    role = (sess or {}).get("role", "guest")
    path = os.path.join(PANEL_DIR, "telegram_dashboard.html")
    if not os.path.exists(path):
        return web.Response(status=404, text="telegram_dashboard.html not found on server", headers=cors_headers())
    with open(path, "r", encoding="utf-8") as f:
        html = f.read()
    # The page was written for Jinja; render its single role block here.
    html = DASHBOARD_JINJA_OWNER.sub(lambda m: m.group(1) if role == "owner" else "", html)
    return web.Response(text=html, content_type="text/html", headers={"Cache-Control": "no-store"})


async def page_owner(request):
    raise web.HTTPFound("/owner/login")


async def page_logout(request):
    token = request.cookies.get("panel_session")
    if token:
        try:
            _sessions().delete_one({"token": token})
        except Exception:
            pass
    resp = web.Response(status=302, headers={"Location": "/login"})
    resp.del_cookie("panel_session")
    return resp


def json_status(payload, status=200):
    # The dashboard's profile endpoints branch on data.status, not data.success.
    return web.json_response(payload, status=status, headers=cors_headers())


async def api_auth_me(request):
    sess = _current_session(request)
    if not sess:
        return json_status({"success": False, "message": "Not authenticated"}, status=401)
    remaining = max(0, int(sess.get("expires", 0) - time.time()))
    return json_status({
        "success": True,
        "email": sess.get("email"),
        "role": sess.get("role"),
        "remainingSeconds": remaining,
    })


async def api_user_profile(request):
    sess = _current_session(request)
    if not sess:
        return json_status({"success": False, "message": "Not authenticated"}, status=401)
    user = _users().find_one({"email": sess.get("email")})
    if not user:
        return json_status({"success": False, "message": "Account not found"}, status=404)
    return json_status({
        "success": True,
        "name": user.get("name", ""),
        "email": user.get("email", ""),
        "phone": user.get("phone", ""),
        "role": sess.get("role"),
    })


async def api_user_profile_update(request):
    sess = _current_session(request)
    if not sess:
        return json_status({"status": "error", "message": "Not authenticated"}, status=401)
    try:
        data = await request.json()
    except Exception:
        return json_status({"status": "error", "message": "Invalid request body."})
    name = (data.get("name") or "").strip()
    email = (data.get("email") or "").strip().lower()
    phone = (data.get("phone") or "").strip()
    password = (data.get("password") or "").strip()

    if not name or not email:
        return json_status({"status": "error", "message": "Name and Email are required!"})
    if not EMAIL_RE.match(email):
        return json_status({"status": "error", "message": "Please provide a valid email address."})

    current = sess.get("email")
    if email != current and _users().find_one({"email": email}):
        return json_status({"status": "error", "message": "That email is already in use!"})

    update = {"name": name, "email": email, "phone": phone}
    if password:
        if len(password) < 6:
            return json_status({"status": "error", "message": "Password must be at least 6 characters."})
        pw_hash, salt = hash_password(password)
        update["pw_hash"] = pw_hash
        update["salt"] = salt

    _users().update_one({"email": current}, {"$set": update})
    if email != current:
        _sessions().update_many({"email": current}, {"$set": {"email": email}})
    return json_status({"status": "ok", "message": "Profile updated successfully!"})


# ---------------------------------------------------------------------------
# Wiring
# ---------------------------------------------------------------------------
panel_routes = web.RouteTableDef()

panel_routes.get("/")(page_root)
panel_routes.get("/login")(page_login)
panel_routes.get("/owner/login")(page_owner_login)
panel_routes.get("/owner")(page_owner)
panel_routes.get("/mode")(page_mode)
panel_routes.get("/telegram_master")(page_dashboard)
panel_routes.get("/dashboard")(page_dashboard)
panel_routes.get("/logout")(page_logout)

panel_routes.post("/api/auth/login")(api_login)
panel_routes.post("/api/auth/verify-login-otp")(api_verify_login_otp)
panel_routes.post("/api/auth/send-register-otp")(api_send_register_otp)
panel_routes.post("/api/auth/verify-register-otp")(api_verify_register_otp)
panel_routes.post("/api/auth/register")(api_register)
panel_routes.post("/api/auth/forgot-otp")(api_forgot_otp)
panel_routes.post("/api/auth/reset-password")(api_reset_password)
panel_routes.post("/api/owner/login")(api_owner_login)

panel_routes.get("/api/auth/me")(api_auth_me)
panel_routes.get("/api/user/profile")(api_user_profile)
panel_routes.post("/api/user/profile/update")(api_user_profile_update)

panel_routes.options("/api/{tail:.*}")(api_options)


def setup_panel(app, add_log=None):
    """Register the panel routes on an existing aiohttp Application."""
    app.add_routes(panel_routes)
    ensure_indexes()
    msg = "🖥️  Web panel mounted: /login, /owner/login, /mode, /api/auth/*, /api/owner/login"
    if add_log:
        add_log(msg)
    else:
        log.info(msg)
    return app
