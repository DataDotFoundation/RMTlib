#!/usr/bin/env python3
"""YouTube access for the Dissemination videos: sign-in, tokens, and a few read checks.

Canonical copy: DataDotFoundation/DisseminationLib, Dissemination/common/youtube.py (byte-identical copies
downstream, pinned by Dissemination/SOURCE). Stdlib only. See Dissemination/README.md, "YouTube".

Credentials come from the environment, never from the repository:
    YT_CLIENT, YT_SECRET     the OAuth client (type "Desktop app") of the channel's Google Cloud project
    YT_REFRESH_TOKEN         optional: a refresh token, if the owner chose to provide one this way
    YT_TOKEN_FILE            optional: where tokens are stored
                             (default ~/.config/dissemination/youtube_token.json, mode 0600)

Sign-in (the channel owner approves once, in their own browser):
    python3 -I youtube.py login [--write]   # prints a link; --write asks for the `youtube` scope
    # the owner approves; the browser lands on http://127.0.0.1:8765/?...code=... (it does not load)
    python3 -I youtube.py exchange 'http://127.0.0.1:8765/?...code=...'

Use:
    python3 -I youtube.py whoami            # the channel the token belongs to
    python3 -I youtube.py playlists         # the channel's playlists
    curl -H "Authorization: Bearer $(python3 -I youtube.py token)" https://www.googleapis.com/youtube/v3/...

Only `token` prints a credential (a short-lived access token), and only to stdout for a pipe.
"""

import base64
import hashlib
import json
import os
import secrets
import sys
import time
import urllib.error
import urllib.parse
import urllib.request

REDIRECT = "http://127.0.0.1:8765"
SCOPES = {"read": "https://www.googleapis.com/auth/youtube.readonly",
          "write": "https://www.googleapis.com/auth/youtube"}
AUTH = "https://accounts.google.com/o/oauth2/v2/auth"
TOKEN = "https://oauth2.googleapis.com/token"
API = "https://www.googleapis.com/youtube/v3/"


def die(msg):
    print(msg, file=sys.stderr)
    sys.exit(1)


def client():
    cid, sec = os.environ.get("YT_CLIENT"), os.environ.get("YT_SECRET")
    if not cid or not sec:
        die("YT_CLIENT and YT_SECRET must be set in the environment (never in the repository)")
    return cid, sec


def token_file():
    return os.environ.get("YT_TOKEN_FILE") or os.path.expanduser(
        "~/.config/dissemination/youtube_token.json")


def write_private(path, data):
    os.makedirs(os.path.dirname(path), mode=0o700, exist_ok=True)
    fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
    with os.fdopen(fd, "w") as f:
        json.dump(data, f)


def post(url, fields):
    req = urllib.request.Request(url, data=urllib.parse.urlencode(fields).encode())
    try:
        with urllib.request.urlopen(req, timeout=30) as r:
            return json.load(r)
    except urllib.error.HTTPError as e:
        body = json.loads(e.read() or b"{}")
        die(f"{url}: {e.code} {body.get('error')}: {body.get('error_description', '')}")


def cmd_login(args):
    cid, _ = client()
    scope = SCOPES["write" if "--write" in args else "read"]
    verifier = secrets.token_urlsafe(64)[:96]
    challenge = base64.urlsafe_b64encode(hashlib.sha256(verifier.encode()).digest()).rstrip(b"=").decode()
    write_private(token_file() + ".verifier", {"verifier": verifier, "scope": scope})
    q = {"client_id": cid, "redirect_uri": REDIRECT, "response_type": "code", "scope": scope,
         "code_challenge": challenge, "code_challenge_method": "S256",
         "access_type": "offline", "prompt": "consent"}
    print(AUTH + "?" + urllib.parse.urlencode(q))


def cmd_exchange(args):
    if not args:
        die("usage: youtube.py exchange 'http://127.0.0.1:8765/?...code=...'")
    cid, sec = client()
    code = urllib.parse.parse_qs(urllib.parse.urlparse(args[0]).query).get("code", [None])[0]
    if not code:
        die("no code= in that address")
    vpath = token_file() + ".verifier"
    try:
        v = json.load(open(vpath))
    except FileNotFoundError:
        die("no pending sign-in: run `youtube.py login` first, in the same environment")
    tok = post(TOKEN, {"code": code, "client_id": cid, "client_secret": sec, "redirect_uri": REDIRECT,
                       "grant_type": "authorization_code", "code_verifier": v["verifier"]})
    tok["obtained_at"] = int(time.time())
    write_private(token_file(), tok)
    os.remove(vpath)
    print(f"stored a token for scope {tok.get('scope')} in {token_file()}"
          f"{' (with a refresh token)' if 'refresh_token' in tok else ''}")


def access_token():
    cid, sec = client()
    tok = {}
    if os.path.exists(token_file()):
        tok = json.load(open(token_file()))
    if tok.get("access_token") and time.time() < tok.get("obtained_at", 0) + tok.get("expires_in", 0) - 60:
        return tok["access_token"]
    refresh = tok.get("refresh_token") or os.environ.get("YT_REFRESH_TOKEN")
    if not refresh:
        die("no valid token: run `youtube.py login`, have the owner approve, then `exchange`")
    new = post(TOKEN, {"client_id": cid, "client_secret": sec, "refresh_token": refresh,
                       "grant_type": "refresh_token"})
    new["obtained_at"] = int(time.time())
    new.setdefault("refresh_token", refresh)
    write_private(token_file(), new)
    return new["access_token"]


def get(path, params):
    req = urllib.request.Request(API + path + "?" + urllib.parse.urlencode(params),
                                 headers={"Authorization": "Bearer " + access_token()})
    try:
        with urllib.request.urlopen(req, timeout=30) as r:
            return json.load(r)
    except urllib.error.HTTPError as e:
        die(f"{path}: {e.code} {json.loads(e.read() or b'{}').get('error', {}).get('message', '')}")


def cmd_whoami(_):
    for it in get("channels", {"part": "snippet,statistics", "mine": "true"}).get("items", []):
        s, st = it["snippet"], it.get("statistics", {})
        print(f"{s['title']} ({s.get('customUrl', '')}): {st.get('videoCount', '?')} videos, "
              f"{st.get('subscriberCount', '?')} subscribers, channel {it['id']}")


def cmd_playlists(_):
    page = None
    while True:
        p = {"part": "snippet,contentDetails,status", "mine": "true", "maxResults": "50"}
        if page:
            p["pageToken"] = page
        j = get("playlists", p)
        for it in j.get("items", []):
            print(f"{it['snippet']['publishedAt'][:10]}  {it['status']['privacyStatus']:8} "
                  f"{it['contentDetails']['itemCount']:>4} videos  {it['snippet']['title']}  [{it['id']}]")
        page = j.get("nextPageToken")
        if not page:
            break


def cmd_token(_):
    print(access_token())


def main(argv):
    cmds = {"login": cmd_login, "exchange": cmd_exchange, "whoami": cmd_whoami,
            "playlists": cmd_playlists, "token": cmd_token}
    if not argv or argv[0] not in cmds:
        die(__doc__)
    cmds[argv[0]](argv[1:])


if __name__ == "__main__":
    main(sys.argv[1:])
