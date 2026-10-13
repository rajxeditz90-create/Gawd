# Deploying the Telegram Master Engine on Render

This bundle contains everything needed to run the bot **and its web panel** as a Render **Web Service** (Docker).

## Files

| File | Purpose |
|------|---------|
| `main.py` | The bot. Two changes from your original: the port reads Render's `$PORT`, and `main()` mounts the web panel. |
| `panel.py` | The web panel: serves the HTML pages and implements the `/api/auth/*` and `/api/owner/login` endpoints. |
| `login.html` | User portal (your file, unchanged). Served at `/login`. |
| `owner_login.html` | Owner portal (your file, unchanged). Served at `/owner/login`. |
| `mode.html` | The post-login landing page both portals redirect to (`/mode`). Newly added — your bundle had no page there. |
| `telegram_dashboard.html` | The Telegram control dashboard (your file). Served at `/telegram_master`. |
| `requirements.txt` | Python dependencies. The panel adds none beyond what the bot already needs. |
| `Dockerfile` | Builds the image; installs `ffmpeg` (required by PyTgCalls) plus build tools. |
| `render.yaml` | Render Blueprint — one-click service definition with env-var placeholders. |
| `.dockerignore` | Keeps sessions, `.env`, and caches out of the image. |
| `.python-version` | Pins Python 3.12 for a **native** Render Python service. Ignored by the Docker build (which pins 3.12 in the image). |

## The one code change to the port (important)

Your script had the web port hardcoded:

```python
SERVICE_PORT = 20826
```

Render does not give you a fixed port — it injects `$PORT` and routes traffic there. `main.py` in this bundle already has:

```python
SERVICE_PORT = int(os.getenv("PORT", "20826"))
```

Without this, Render's health check and public URL would never reach your aiohttp app and the deploy would be marked unhealthy. The app binds `0.0.0.0`, which is already correct for containers.

## The web panel

`main()` now calls `panel.setup_panel(app, ...)`, which mounts these routes on the same aiohttp server the bot already runs:

| Method | Route | What it does |
|--------|-------|--------------|
| GET | `/` | Redirects to `/login` |
| GET | `/login` | Serves `login.html` |
| GET | `/owner/login` | Serves `owner_login.html` |
| GET | `/mode` | Serves `mode.html` (live status from `/health`) |
| POST | `/api/auth/send-register-otp` | Sends a registration OTP |
| POST | `/api/auth/verify-register-otp` | Verifies the registration OTP |
| POST | `/api/auth/register` | Creates the account |
| POST | `/api/auth/login` | Checks credentials, sends a login OTP |
| POST | `/api/auth/verify-login-otp` | Verifies the login OTP, sets a session cookie |
| POST | `/api/auth/forgot-otp` | Sends a password-reset OTP |
| POST | `/api/auth/reset-password` | Verifies the reset OTP and sets the new password |
| POST | `/api/owner/login` | Owner portal login (username + master passcode) |

Users are stored in MongoDB Atlas, in the `panel_users` collection of the `igtgwp_db` database (the same database the bot already uses). Passwords are hashed with PBKDF2-SHA256 and a per-user salt — never stored in plain text. OTPs live in `panel_otps` and expire after 10 minutes.

## The Telegram dashboard

`telegram_dashboard.html` is served at `/telegram_master` (and `/dashboard`). It was written for a Jinja template with a single `{% if role == 'owner' %}` block, so `panel.py` renders that one block at request time — the OWNER nav link appears only for owner sessions, and no template tags leak into the page.

The page calls `/tg_*` paths, which do not match the bot's own `/userbot/*` and `/swarm/*` route names. Rather than change either file, `main.py` registers thin aliases that point each `/tg_*` path at the bot's existing handler — the dashboard's request and response shapes already line up with what those handlers return:

| Dashboard calls | Bot handler behind it |
|-----------------|-----------------------|
| `/tg_userbot_send_code`, `/tg_userbot_verify_code`, `/tg_userbot_verify_2fa` | `api_send_code`, `api_verify_code`, `api_verify_2fa` |
| `/tg_userbot_qr_gen`, `/tg_userbot_qr_check` | `api_qr_gen`, `api_qr_check` |
| `/tg_userbot_disconnect`, `/tg_userbot_set_admin` | `api_ub_disconnect`, `api_ub_set_admin` |
| `/tg_swarm_save`, `/tg_swarm_start`, `/tg_swarm_stop`, `/tg_swarm_delete` | `api_swarm_save`, `api_swarm_start`, `api_swarm_stop`, `api_swarm_delete` |
| `/tg_master_status` | `api_all_status` (the bot's `/status`) |

The dashboard's profile and session calls are served by the panel: `GET /api/auth/me` (returns `remainingSeconds` for the countdown), `GET /api/user/profile`, `POST /api/user/profile/update` (returns `status: ok`, as the page expects), and `GET /logout`. `/owner` redirects to the owner portal at `/owner/login`.

Note the two different response conventions in play: the auth endpoints branch on `success`, while the dashboard's profile endpoints branch on `status`. Both are handled.

## Environment variables to set in Render

| Key | Notes |
|-----|-------|
| `TELEGRAM_API_ID` | From my.telegram.org |
| `TELEGRAM_API_HASH` | From my.telegram.org |
| `TELEGRAM_PHONE` | The userbot phone number, e.g. `+91...` |
| `MASTER_ADMIN_ID` | Your Telegram numeric user id |
| `MONGODB_URI` | MongoDB Atlas connection string (also used by the panel) |
| `SESSION_STORAGE` | Set to `mongodb` |
| `OWNER_USERNAME` | Username for the owner portal (default `owner`) |
| `OWNER_PASSCODE` | Master passcode for the owner portal — **set this**, it is disabled otherwise |
| `SMTP_HOST` | Mail server, e.g. `smtp.gmail.com` |
| `SMTP_PORT` | `587` (STARTTLS) or `465` (SSL) |
| `SMTP_USER` | SMTP username / login |
| `SMTP_PASS` | SMTP password (for Gmail, an **App Password**, not your account password) |
| `SMTP_FROM` | From address on the OTP emails |
| `SMTP_SSL` | `true` for port 465, otherwise `false` |

`PORT` is injected by Render automatically — do **not** set it yourself.

If SMTP is left unset, the panel still works: the OTP is returned in the JSON response (which is what the front-end displays), and a warning is logged. Set SMTP to actually email codes.

## Deploy steps

1. Put every file in this bundle in the root of a GitHub repo.
2. In Render: **New → Blueprint**, pick the repo. Render reads `render.yaml` and creates the service. (Or **New → Web Service**, Runtime **Docker**, and set the env vars manually.)
3. Enter the secret env-var values when prompted (`sync: false` values are asked for at deploy time).
4. Confirm the health check path is `/health`.
5. Deploy. The panel is then at `https://<service-name>.onrender.com/login`.

### If you deploy as a native Python service (not Docker)

The bundle is built for the Docker runtime, but if you create a Render **Python** web service instead, two things differ:

- **Python version.** Render's native default is now 3.14, which PyTgCalls' engine (`ntgcalls`) has no wheels for, so the install fails. The `.python-version` file in this bundle pins `3.12` — keep it at the repo root so Render uses 3.12. (You can also set a `PYTHON_VERSION` env var to a fully qualified version like `3.12.11`; it takes precedence over the file.)
- **Build and start commands.** Set build `pip install -r requirements.txt` and start `python main.py`.

The Docker path avoids both issues and also installs `ffmpeg`, so it stays the recommended option.

## Two things to know before you go live

**Free plan spins down.** A Render *free* web service sleeps after ~15 minutes with no inbound traffic, and a sleeping service cannot stay connected to Telegram — the bot will drop. To keep it up 24/7 use a paid instance type (`starter` and above, as set in `render.yaml`), or run it as a **Background Worker** (paid, no HTTP) and hit the service with an external uptime pinger so it never idles. This is a hosting-platform limitation, not something the code can fix.

**Sessions must live outside the container.** Render's disk is ephemeral — it is wiped on every deploy/restart. That is why `SESSION_STORAGE=mongodb` with a valid `MONGODB_URI` matters; otherwise every restart loses your logged-in userbot sessions and you re-authenticate each time.

## Security notes

**OTPs are returned in the API response.** The supplied `login.html` reads `data.otp` and prints the code on screen, so the panel returns it. That means anyone who knows a registered email can complete a login without access to that mailbox — it is not a real second factor. To make OTPs meaningful, remove `otp` from the JSON responses in `panel.py` (the keys are marked with a comment) and rely on the emailed code only.

**Rotate the credentials that shipped in the source.** `main.py` contains real-looking defaults for `TELEGRAM_API_ID`, `TELEGRAM_API_HASH`, `TELEGRAM_PHONE`, `MASTER_ADMIN_ID`, **and a MongoDB Atlas connection string with a username and password**. Since that file has been shared, treat all of them as compromised: rotate the Telegram API hash on my.telegram.org, change the Atlas database user's password, and set every one of these through Render's environment variables rather than relying on the in-code defaults. Never commit a real `.env` or `*.session` file — `.dockerignore` already excludes them.

**Set `OWNER_PASSCODE`.** Until you do, the owner portal rejects all logins (by design).

**The bot's control endpoints have no authentication.** The `/tg_*` aliases (and the `/userbot/*`, `/swarm/*` routes behind them) do not check the panel session — anyone who can reach the service URL can link userbots, set admin IDs, and start or stop swarms. The login portal in front of them is cosmetic unless those routes are gated. If you want the panel to actually protect the bot, the next step is to require a valid `panel_session` cookie on the `/tg_*` and `/userbot/*` / `/swarm/*` routes; say the word and I'll wire that in.

**Pages linked but not included.** The dashboard's nav originally linked to `/mode`, `/gc_creator`, `/multi_gc`, `/ig_private_api`, `/wp_bots_nc_setup` and `/whatsapp_call_setup`. Those pages were never provided, so those nav links have been removed from `telegram_dashboard.html`; the nav now keeps only `/telegram_master`, the conditional OWNER link, PROFILE and LOGOUT. The `/mode` page still exists and still works — it is just no longer linked from the dashboard. Add the links back if you later build those pages.
