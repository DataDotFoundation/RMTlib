#!/usr/bin/env python3
"""Check the Lake pins of this repository against its upstreams, and bump them.

The three live repositories depend on each other by pinned git revision, never by copied code:

    MeaningLib  <-  RMTlib  <-  RH-Dual        (all pin the same Mathlib and Lean toolchain)

This script makes the rules for those pins mechanical, so that agents (and people) do not have to
remember them. For every Lake package in the repository (every tracked `lakefile.toml`) it checks:

  pin-form    every git `[[require]]` has a `rev` that is a commit hash (7 to 40 hex digits),
              not a branch or tag;
  manifest    `lake-manifest.json` agrees with the lakefile: same url, `inputRev` equal to `rev`,
              and the locked full hash starts with `rev`;
  on-main     for a repository we own, the pinned commit is on that repository's default branch
              (a pin to an unmerged feature branch breaks once the branch is rebased or deleted);
              how far the pin is behind is reported, and is an error with --fresh;
  toolchain   every direct dependency, at its pinned commit, has the same `lean-toolchain`;
  shared      every package a direct dependency locks (its `lake-manifest.json` at the pinned
              commit) is locked here at the same commit, so we build what the dependency tested;
  clean       every checked-out package under `.lake/packages/` is at its locked commit and has no
              local edits (fix the dependency upstream, never in `.lake/packages/`);
  copy        this script is byte-identical to the copy each owned dependency carries at its
              pinned commit (canonical copy: DataDotFoundation/MeaningLib, scripts/check_pins.py),
              and so is every shared file (`SHARED_FILES`, empty today) that both this repository
              and the dependency carry. A **self-pin** (a dependency whose URL is this repository's
              own `origin`, e.g. a sub-package frozen at a tag of an earlier toolchain) is frozen by
              design: `copy` and `on-main` freshness are reported, not failed;
  source      if the repository has `Dissemination/SOURCE` (`repo …` and `commit <40 hex>` lines),
              every file listed in `Dissemination/SHARED` of that repository at that commit and
              carried here is byte-identical to it (canonical: DataDotFoundation/DisseminationLib;
              MeaningLib#44). A listed file not carried here is reported, not failed.

Every check is a rule applied to files and git objects; nothing is judged. Dependencies are read
from `.lake/packages/` when present, otherwise fetched (blob-less) into `.lake/pin-check.git`.

usage:
  python3 -I <path>/check_pins.py [--offline] [--fresh] [--owned PREFIX ...] [PKGDIR ...]
  python3 -I <path>/check_pins.py bump NAME [REV] [--pkg PKGDIR] [--allow-off-main]
  python3 -I <path>/check_pins.py source-bump [REV]

`bump` sets the pin of NAME (default: the head of its default branch) in PKGDIR/lakefile.toml,
refreshes this script and the shared files this repository carries from the dependency if it
carries different copies, and prints the `lake
update` to run next. It never edits `lake-manifest.json`: Lake does that.

Exit codes: 0 no FAIL; 1 some FAIL; 2 a check could not run (network, git), unless --offline,
which turns those into SKIP lines. Stdlib only.
"""
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import tomllib

SCRIPT = os.path.abspath(__file__)
SCRIPT_NAME = "check_pins.py"
COPY_PATHS = ("scripts/" + SCRIPT_NAME, "tools/scripts/" + SCRIPT_NAME)
# Files kept byte-identical down the chain, canonical in MeaningLib. A repository that does not
# carry one is not checked for it. Empty since the Dissemination files moved to DisseminationLib,
# which is checked through `Dissemination/SOURCE` instead (the `source` check; MeaningLib#44).
SHARED_FILES = ()
SOURCE_PATH = os.path.join("Dissemination", "SOURCE")
SOURCE_KEYS = ("repo", "commit")


def local_bytes(root, rel):
    path = os.path.join(root, rel)
    if not os.path.isfile(path):
        return None
    with open(path, "rb") as f:
        return f.read()
DEFAULT_OWNED = ("https://github.com/DataDotFoundation/",)
HEX = re.compile(r"^[0-9a-f]{7,40}$")
FULL = re.compile(r"^[0-9a-f]{40}$")


def git(args, cwd=None, check=True, binary=False):
    """Run git; return stdout (str, or bytes if binary), or None on failure when check is False."""
    r = subprocess.run(["git", *args], cwd=cwd, capture_output=True)
    if r.returncode != 0:
        if check:
            raise GitError(" ".join(["git", *args]), r.stderr.decode(errors="replace").strip())
        return None
    return r.stdout if binary else r.stdout.decode().strip()


class GitError(Exception):
    pass


def is_owned(url, owned):
    return any(norm_url(url).startswith(norm_url(o)) for o in owned)


def norm_url(url):
    url = url.strip().rstrip("/")
    if url.endswith(".git"):
        url = url[:-4]
    return url.lower()


def repo_root():
    return git(["rev-parse", "--show-toplevel"], cwd=os.path.dirname(SCRIPT))


def own_origin(root):
    """This repository's own `origin` URL, normalised (None without one)."""
    try:
        u = git(["remote", "get-url", "origin"], cwd=root, check=False)
    except GitError:
        return None
    if not u:
        return None
    u = u.strip()
    # git@github.com:Owner/Repo(.git) and https://github.com/Owner/Repo(.git) are the same repository
    if u.startswith("git@") and ":" in u:
        host, path = u[4:].split(":", 1)
        u = f"https://{host}/{path}"
    return norm_url(u)


class Upstreams:
    """Read files and history of a dependency at a commit: `.lake/packages/<name>` first, then a
    blob-less fetch into a cache repository. One instance per run; fetches are memoised."""

    def __init__(self, root, offline, owned):
        self.cache = os.path.join(root, ".lake", "pin-check.git")
        self.offline = offline
        self.owned = owned
        self.fetched = {}
        self.heads = {}

    def _cache(self):
        if not os.path.isdir(self.cache):
            os.makedirs(os.path.dirname(self.cache), exist_ok=True)
            git(["init", "--bare", "-q", self.cache])
        return self.cache

    def _remote(self, url):
        name = "r" + hashlib.sha1(norm_url(url).encode()).hexdigest()[:12]
        c = self._cache()
        if git(["remote", "get-url", name], cwd=c, check=False) is None:
            git(["remote", "add", name, url], cwd=c)
            git(["config", f"remote.{name}.promisor", "true"], cwd=c)
            git(["config", f"remote.{name}.partialclonefilter", "blob:none"], cwd=c)
        return name

    def default_head(self, url):
        """(branch, full hash) of the default branch of url, fetched with history into the cache."""
        key = norm_url(url)
        if key in self.heads:
            return self.heads[key]
        if self.offline:
            raise GitError("offline", f"default branch of {url} not fetched")
        out = git(["ls-remote", "--symref", url, "HEAD"])
        m = re.search(r"^ref: refs/heads/(\S+)\s+HEAD", out, re.M)
        branch = m.group(1) if m else "main"
        name = self._remote(url)
        git(["fetch", "-q", "--filter=blob:none", name,
             f"+refs/heads/{branch}:refs/remotes/{name}/{branch}"], cwd=self.cache)
        head = git(["rev-parse", f"refs/remotes/{name}/{branch}"], cwd=self.cache)
        self.heads[key] = (branch, head)
        return self.heads[key]

    def where(self, url, rev, pkg_dir=None):
        """A git directory holding commit rev of url: pkg_dir if it has it, else the cache."""
        if pkg_dir and os.path.exists(os.path.join(pkg_dir, ".git")):
            if git(["cat-file", "-e", f"{rev}^{{commit}}"], cwd=pkg_dir, check=False) is not None:
                return pkg_dir
        if os.path.isdir(self.cache) and git(
                ["cat-file", "-e", f"{rev}^{{commit}}"], cwd=self.cache, check=False) is not None:
            return self.cache
        if self.offline:
            raise GitError("offline", f"{url} @ {rev[:12]} not available locally")
        key = (norm_url(url), rev)
        if key not in self.fetched:
            name = self._remote(url)
            if is_owned(url, self.owned) or not FULL.match(rev):
                # history of the default branch (owned repositories are small; an abbreviated
                # hash can only be found in fetched history); then the commit itself if elsewhere
                self.default_head(url)
                if FULL.match(rev) and git(["cat-file", "-e", f"{rev}^{{commit}}"],
                                           cwd=self.cache, check=False) is None:
                    git(["fetch", "-q", "--filter=blob:none", name, rev], cwd=self.cache, check=False)
            else:  # one commit of a large foreign repository (Mathlib): never its history
                git(["fetch", "-q", "--filter=blob:none", "--depth=1", name, rev], cwd=self.cache)
            self.fetched[key] = True
        if git(["cat-file", "-e", f"{rev}^{{commit}}"], cwd=self.cache, check=False) is None:
            raise GitError("fetch", f"{url} has no commit {rev}")
        return self.cache

    def resolve(self, url, rev, pkg_dir=None):
        d = self.where(url, rev, pkg_dir)
        return git(["rev-parse", f"{rev}^{{commit}}"], cwd=d)

    def show(self, url, rev, path, pkg_dir=None):
        d = self.where(url, rev, pkg_dir)
        return git(["show", f"{rev}:{path}"], cwd=d, check=False, binary=True)

    def on_branch(self, url, rev):
        """(is rev an ancestor of the default branch, commits behind, branch, head). The cache
        holds the whole history of the default branch, so a commit missing there is not on it."""
        branch, head = self.default_head(url)
        full = git(["rev-parse", "--verify", "-q", f"{rev}^{{commit}}"], cwd=self.cache, check=False)
        ok = bool(full) and git(["merge-base", "--is-ancestor", full, head],
                                cwd=self.cache, check=False) is not None
        behind = int(git(["rev-list", "--count", f"{full}..{head}"], cwd=self.cache)) if ok else None
        return ok, behind, branch, head


class Report:
    def __init__(self, offline):
        self.offline = offline
        self.fails = 0
        self.errors = 0

    def line(self, tag, check, subject, detail):
        print(f"{tag:<5} {check:<9} {subject}: {detail}")
        if tag == "FAIL":
            self.fails += 1
        elif tag == "ERROR":
            self.errors += 1

    def ok(self, *a):
        self.line("OK", *a)

    def fail(self, *a):
        self.line("FAIL", *a)

    def info(self, *a):
        self.line("--", *a)

    def warn(self, *a):
        self.line("WARN", *a)

    def unavailable(self, check, subject, exc):
        self.line("SKIP" if self.offline else "ERROR", check, subject, f"{exc.args[0]}: {exc.args[1]}")


def load_package(pkg):
    with open(os.path.join(pkg, "lakefile.toml"), "rb") as f:
        lake = tomllib.load(f)
    mpath = os.path.join(pkg, "lake-manifest.json")
    manifest = None
    if os.path.isfile(mpath):
        with open(mpath) as f:
            manifest = json.load(f)
    tpath = os.path.join(pkg, "lean-toolchain")
    toolchain = open(tpath).read().strip() if os.path.isfile(tpath) else None
    return lake, manifest, toolchain


def manifest_index(manifest):
    return {p["name"]: p for p in (manifest or {}).get("packages", [])}


def check_package(pkg, root, up, rep, owned, fresh):
    rel = os.path.relpath(pkg, root)
    lake, manifest, toolchain = load_package(pkg)
    print(f"== {lake.get('name', rel)} ({rel}/lakefile.toml)")
    mine = manifest_index(manifest) if manifest is not None else None
    pkgs_dir = os.path.join(pkg, lake.get("packagesDir", ".lake/packages"))
    requires = lake.get("require", [])
    if not requires:
        rep.info("pin-form", lake.get("name", rel), "no [[require]]; nothing is pinned")
    if requires and manifest is None:
        rep.warn("manifest", rel, "no lake-manifest.json; Lake resolves the pins afresh on each clone")

    with open(SCRIPT, "rb") as f:
        my_script = f.read()

    for req in requires:
        name = req.get("name", "?")
        if "path" in req:
            dep_dir = os.path.normpath(os.path.join(pkg, req["path"]))
            rep.info("pin-form", name, f"path dependency {req['path']} (pinned by this repository)")
            dlake, dman, dtool = load_package(dep_dir) if os.path.isfile(
                os.path.join(dep_dir, "lakefile.toml")) else (None, None, None)
            if dtool is not None and toolchain is not None:
                (rep.ok if dtool == toolchain else rep.fail)(
                    "toolchain", name, f"{dtool}" + ("" if dtool == toolchain else f" (here {toolchain})"))
            compare_shared(name, "(working tree)", dman, mine, rep)
            continue
        if "git" not in req:
            rep.fail("pin-form", name, "neither git nor path; registry requires are not pinned by commit")
            continue
        url, rev = req["git"], str(req.get("rev", ""))
        if not HEX.match(rev):
            rep.fail("pin-form", name, f"rev {rev!r} is not a commit hash; run: {bump_hint(name, rel)}")
            continue
        rep.ok("pin-form", name, f"{rev}")

        ent = (mine or {}).get(name)
        locked = None
        if ent is None:
            if manifest is not None:
                rep.fail("manifest", name, f"not in lake-manifest.json; run: {lake_update(rel, name)}")
        else:
            probs = []
            if ent.get("type") != "git":
                probs.append(f"type {ent.get('type')!r}")
            if norm_url(ent.get("url", "")) != norm_url(url):
                probs.append(f"url {ent.get('url')!r}")
            if ent.get("inputRev") != rev:
                probs.append(f"inputRev {ent.get('inputRev')!r}")
            if not str(ent.get("rev", "")).startswith(rev):
                probs.append(f"locked rev {str(ent.get('rev'))[:12]}")
            if probs:
                rep.fail("manifest", name, "lakefile says rev " + rev + ", manifest has " + ", ".join(probs)
                         + f"; run: {lake_update(rel, name)}")
            else:
                locked = ent["rev"]
                rep.ok("manifest", name, f"locked at {locked}")
        target = locked or rev
        dep_pkg = os.path.join(pkgs_dir, name)
        self_pin = own_origin(root) is not None and norm_url(url) == own_origin(root)

        if self_pin:
            rep.info("on-main", name, f"self-pin: this repository at {target[:12]}, frozen by design")
        elif is_owned(url, owned):
            try:
                ok, behind, branch, head = up.on_branch(url, target)
                if not ok:
                    rep.fail("on-main", name, f"{target[:12]} is not on {branch} ({head[:12]}); "
                                              "pin a merged commit")
                elif behind == 0:
                    rep.ok("on-main", name, f"at the head of {branch}")
                else:
                    (rep.fail if fresh else rep.warn)(
                        "on-main", name, f"on {branch}, {behind} commit(s) behind {head[:12]}; "
                                         f"to move: {bump_hint(name, rel)}")
            except GitError as e:
                rep.unavailable("on-main", name, e)
        else:
            rep.info("on-main", name, "not owned here; pinned only")

        try:
            dtool = up.show(url, target, "lean-toolchain", dep_pkg)
            if dtool is None:
                rep.info("toolchain", name, "dependency has no lean-toolchain")
            else:
                dtool = dtool.decode().strip()
                (rep.ok if dtool == toolchain else rep.fail)(
                    "toolchain", name, dtool + ("" if dtool == toolchain else f" (here {toolchain})"))
            dman = up.show(url, target, "lake-manifest.json", dep_pkg)
            compare_shared(name, target[:12], json.loads(dman) if dman else None, mine, rep)
            if self_pin:
                rep.info("copy", name, f"self-pin: this repository's own files at {target[:12]} "
                                       "are not compared with the working tree")
            elif is_owned(url, owned):
                copies = [(p, up.show(url, target, p, dep_pkg)) for p in COPY_PATHS]
                copies = [(p, b) for p, b in copies if b is not None]
                if not copies:
                    rep.info("copy", name, f"carries no {SCRIPT_NAME} at {target[:12]}")
                for p, b in copies:
                    if b == my_script:
                        rep.ok("copy", name, f"{p} at {target[:12]} is identical")
                    else:
                        rep.fail("copy", name, f"{p} at {target[:12]} differs from this copy; "
                                               f"refresh it with: {bump_hint(name, rel, target)}")
                for f in SHARED_FILES:
                    mine_f = local_bytes(root, f)
                    if mine_f is None:
                        continue
                    theirs = up.show(url, target, f, dep_pkg)
                    if theirs is None:
                        rep.info("copy", name, f"{f}: not carried at {target[:12]}")
                    elif theirs == mine_f:
                        rep.ok("copy", name, f"{f} at {target[:12]} is identical")
                    else:
                        rep.fail("copy", name, f"{f} differs from {name} at {target[:12]}; "
                                               f"refresh it with: {bump_hint(name, rel, target)}")
        except GitError as e:
            rep.unavailable("shared", name, e)

    check_clean(manifest, pkgs_dir, rep)


def compare_shared(dep, at, dman, mine, rep):
    if dman is None:
        rep.info("shared", dep, f"no lake-manifest.json at {at}")
        return
    if mine is None:
        rep.info("shared", dep, "not compared: this package has no lake-manifest.json")
        return
    bad = 0
    for p in dman.get("packages", []):
        if p.get("type") != "git":
            continue
        here = mine.get(p["name"])
        if here is None:
            rep.fail("shared", dep, f"locks {p['name']} at {p['rev'][:12]}, which this manifest lacks; "
                                    f"run: lake update {dep}")
            bad += 1
        elif here.get("rev") != p.get("rev"):
            rep.fail("shared", dep, f"locks {p['name']} at {p['rev'][:12]}, here {here.get('rev', '')[:12]}")
            bad += 1
    if not bad:
        n = sum(1 for p in dman.get("packages", []) if p.get("type") == "git")
        rep.ok("shared", dep, f"the {n} git package(s) it locks are locked here at the same commit"
               if n else "it locks no git packages")


def check_clean(manifest, pkgs_dir, rep):
    for p in (manifest or {}).get("packages", []):
        if p.get("type") != "git":
            continue
        d = os.path.join(pkgs_dir, p["name"])
        if not os.path.exists(os.path.join(d, ".git")):
            continue
        head = git(["rev-parse", "HEAD"], cwd=d, check=False)
        dirty = git(["status", "--porcelain"], cwd=d, check=False)
        if head != p.get("rev"):
            rep.fail("clean", p["name"], f".lake/packages checkout at {str(head)[:12]}, locked "
                                         f"{p['rev'][:12]}; run: lake build (or lake update)")
        elif dirty:
            first = dirty.splitlines()[0]
            rep.fail("clean", p["name"], f"local edits in .lake/packages ({first} ...); "
                                         "fix upstream instead, then reset the checkout")
        else:
            rep.ok("clean", p["name"], "checkout at the locked commit, no local edits")


def lake_update(rel, name):
    return f"lake update {name}" if rel in (".", "") else f"(cd {rel} && lake update {name})"


def bump_hint(name, rel, rev=None):
    here = os.path.relpath(SCRIPT, os.getcwd())
    pkg = "" if rel in (".", "") else f" --pkg {rel}"
    return f"python3 -I {here} bump {name}{' ' + rev[:12] if rev else ''}{pkg}"


def packages(root, given):
    if given:
        return [os.path.abspath(g) for g in given]
    out = git(["ls-files", "--", "lakefile.toml", "*/lakefile.toml"], cwd=root)
    return sorted(os.path.join(root, os.path.dirname(f)) for f in out.splitlines() if f)


def parse_source(path):
    """`Dissemination/SOURCE`: `key value` lines, `#` comments and blank lines ignored."""
    pin, errs = {}, []
    with open(path, encoding="utf-8") as f:
        for n, line in enumerate(f, 1):
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            key, _, val = line.partition(" ")
            if key not in SOURCE_KEYS or not val.strip():
                errs.append(f"line {n}: expected one of {SOURCE_KEYS} followed by a value")
            else:
                pin[key] = val.strip()
    errs += [f"missing `{k}`" for k in SOURCE_KEYS if k not in pin]
    if "commit" in pin and not re.fullmatch(r"[0-9a-f]{40}", pin["commit"]):
        errs.append("`commit` must be a full 40-hex commit")
    return pin, errs


def source_clone(root, repo, offline):
    """A local clone of the source repository: $DISSEMINATIONLIB, or a blob-less cache under .lake/."""
    local = os.environ.get("DISSEMINATIONLIB")
    if local:
        return local
    cache = os.path.join(root, ".lake", "source-check.git")
    if not os.path.isdir(cache):
        if offline:
            raise GitError("offline", f"no clone of {repo} (set DISSEMINATIONLIB)")
        git(["clone", "-q", "--bare", "--filter=blob:none", f"https://github.com/{repo}.git", cache])
    return cache


def source_rev(clone, rev, offline):
    sha = git(["rev-parse", "--verify", "-q", f"{rev}^{{commit}}"], cwd=clone, check=False)
    if sha is None and not offline:
        git(["fetch", "-q", "origin", "+refs/heads/*:refs/heads/*"], cwd=clone, check=False)
        sha = git(["rev-parse", "--verify", "-q", f"{rev}^{{commit}}"], cwd=clone, check=False)
    if sha is None:
        raise GitError("rev-parse", f"{rev} not found in {clone}")
    return sha.strip()


def source_listing(clone, sha):
    listing = git(["show", f"{sha}:Dissemination/SHARED"], cwd=clone, check=False)
    if listing is None:
        raise GitError("show", f"Dissemination/SHARED missing at {sha[:12]}")
    return [l.strip() for l in listing.splitlines() if l.strip() and not l.startswith("#")]


def check_source(root, rep, offline):
    path = os.path.join(root, SOURCE_PATH)
    if not os.path.isfile(path):
        return
    pin, errs = parse_source(path)
    for e in errs:
        rep.fail("source", SOURCE_PATH, e)
    if errs:
        return
    try:
        clone = source_clone(root, pin["repo"], offline)
        sha = source_rev(clone, pin["commit"], offline)
        for rel in source_listing(clone, sha):
            f = os.path.join("Dissemination", rel)
            theirs = git(["show", f"{sha}:Dissemination/{rel}"], cwd=clone, check=False, binary=True)
            if theirs is None:
                rep.fail("source", f, f"listed in SHARED but absent at {sha[:12]}")
                continue
            mine = local_bytes(root, f)
            if mine is None:
                rep.info("source", f, "not carried here")
            elif mine == theirs:
                rep.ok("source", f, f"identical to {pin['repo']} at {sha[:12]}")
            else:
                rep.fail("source", f, f"differs from {pin['repo']} at {sha[:12]}; change it "
                                      f"there, then `check_pins.py source-bump`")
    except GitError as e:
        rep.unavailable("source", SOURCE_PATH, e)


def cmd_source_bump(rev):
    root = repo_root()
    path = os.path.join(root, SOURCE_PATH)
    pin = {"repo": "DataDotFoundation/DisseminationLib"}
    if os.path.isfile(path):
        pin, errs = parse_source(path)
        if "repo" not in pin:
            print(f"{SOURCE_PATH}: {'; '.join(errs)}", file=sys.stderr)
            return 2
    try:
        clone = source_clone(root, pin["repo"], offline=False)
        sha = source_rev(clone, rev or "main", offline=False)
        for rel in source_listing(clone, sha):
            f = os.path.join("Dissemination", rel)
            theirs = git(["show", f"{sha}:Dissemination/{rel}"], cwd=clone, check=False, binary=True)
            mine = local_bytes(root, f)
            if theirs is not None and mine is not None and theirs != mine:
                with open(os.path.join(root, f), "wb") as out:
                    out.write(theirs)
                print(f"{f}: refreshed from {pin['repo']} at {sha[:12]}")
    except GitError as e:
        print(f"{e.args[0]}: {e.args[1]}", file=sys.stderr)
        return 2
    with open(path, "w", encoding="utf-8") as f:
        f.write(f"repo {pin['repo']}\ncommit {sha}\n")
    print(f"{SOURCE_PATH}: pinned {sha[:12]}; commit it with the refreshed files.")
    return 0


def cmd_check(a):
    root = repo_root()
    up, rep = Upstreams(root, a.offline, a.owned), Report(a.offline)
    for pkg in packages(root, a.pkgdirs):
        check_package(pkg, root, up, rep, a.owned, a.fresh)
    check_source(root, rep, a.offline)
    print(f"-- {rep.fails} FAIL, {rep.errors} ERROR")
    return 1 if rep.fails else (2 if rep.errors else 0)


def cmd_bump(a):
    root = repo_root()
    pkg = os.path.abspath(a.pkg or root)
    path = os.path.join(pkg, "lakefile.toml")
    lake, _, _ = load_package(pkg)
    req = next((r for r in lake.get("require", []) if r.get("name") == a.name), None)
    if req is None or "git" not in req:
        print(f"no git [[require]] named {a.name} in {path}", file=sys.stderr)
        return 2
    up = Upstreams(root, offline=False, owned=a.owned)
    url = req["git"]
    try:
        branch, head = up.default_head(url)
        new = up.resolve(url, a.rev) if a.rev else head
        owned = is_owned(url, a.owned)
        if owned and not a.allow_off_main and git(
                ["merge-base", "--is-ancestor", new, head], cwd=up.cache, check=False) is None:
            print(f"{a.name} {new[:12]} is not on {branch}; merge it first (or --allow-off-main)",
                  file=sys.stderr)
            return 1
        dep_script = None
        for p in COPY_PATHS:
            dep_script = up.show(url, new, p)
            if dep_script is not None:
                break
        dep_shared = {f: up.show(url, new, f) for f in SHARED_FILES}
    except GitError as e:
        print(f"{e.args[0]}: {e.args[1]}", file=sys.stderr)
        return 2
    text = open(path).read()
    blocks = re.split(r"(?m)^(?=\[)", text)
    hit = 0
    for i, b in enumerate(blocks):
        if b.startswith("[[require]]") and re.search(
                r'(?m)^name\s*=\s*"' + re.escape(a.name) + r'"\s*$', b):
            nb, n = re.subn(r'(?m)^(rev\s*=\s*)"[^"]*"', lambda m: f'{m.group(1)}"{new}"', b)
            blocks[i], hit = nb, hit + n
    if hit != 1:
        print(f"expected one rev line for {a.name} in {path}, found {hit}", file=sys.stderr)
        return 2
    old = str(req.get("rev"))
    with open(path, "w") as f:
        f.write("".join(blocks))
    rel = os.path.relpath(pkg, root)
    print(f"{rel}/lakefile.toml: {a.name} {old} -> {new}")
    with open(SCRIPT, "rb") as f:
        mine = f.read()
    if dep_script is not None and dep_script != mine:
        with open(SCRIPT, "wb") as f:
            f.write(dep_script)
        print(f"{os.path.relpath(SCRIPT, root)}: refreshed from {a.name} at {new[:12]}")
    for f, theirs in dep_shared.items():
        mine_f = local_bytes(root, f)
        if theirs is not None and mine_f is not None and theirs != mine_f:
            with open(os.path.join(root, f), "wb") as out:
                out.write(theirs)
            print(f"{f}: refreshed from {a.name} at {new[:12]}")
    print(f"next: {lake_update(rel, a.name)}, then rerun this script without arguments;")
    print("commit the lakefile, the manifest (and the refreshed files) together, nothing else.")
    return 0


def main(argv):
    if argv and argv[0] == "source-bump":
        return cmd_source_bump(argv[1] if len(argv) > 1 else None)
    if argv and argv[0] == "bump":
        p = argparse.ArgumentParser(prog="check_pins.py bump")
        p.add_argument("name")
        p.add_argument("rev", nargs="?")
        p.add_argument("--pkg")
        p.add_argument("--allow-off-main", action="store_true")
        p.add_argument("--owned", action="append", default=list(DEFAULT_OWNED))
        return cmd_bump(p.parse_args(argv[1:]))
    p = argparse.ArgumentParser(prog="check_pins.py", description=__doc__.split("\n")[0])
    p.add_argument("pkgdirs", nargs="*", help="package directories (default: every tracked lakefile.toml)")
    p.add_argument("--offline", action="store_true", help="no network: unreachable checks are SKIP")
    p.add_argument("--fresh", action="store_true", help="a pin behind its default branch is a FAIL")
    p.add_argument("--owned", action="append", default=list(DEFAULT_OWNED),
                   help="url prefix of repositories we own (repeatable)")
    return cmd_check(p.parse_args(argv))


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
