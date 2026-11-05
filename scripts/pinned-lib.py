#!/usr/bin/env python3
"""The pinned-library gate (docs/decisions/0001-vbm-llm.md). A library outside this one that it executes (today: vbm-json) is trusted as the pinned one only while
the library on disk is exactly the one the protected lock `scripts/pinned-libs.lock` names. One line per library, `#` comments:
    NAME REV SPEC_HASH ROOT SPEC_PATHS        (REV: 40 hex, the git commit; SPEC_HASH: 64 hex, defined below; ROOT: the Lean module root; SPEC_PATHS: comma list, a trailing / = a directory)
spec_hash = sha256 of the text "<sha256 of file> <path relative to the package>\\n", sorted in the C locale, over every regular file under the SPEC_PATHS of the package checkout (working tree,
so an untracked or edited file counts; `.git` never does). A missing SPEC_PATH is an error, never an empty set.
    scripts/pinned-lib.py hash DIR PATHS        print the spec_hash of DIR for the comma list PATHS (used to write a lock line, never to check one)
    scripts/pinned-lib.py verify  [--lock F] [--manifest F] [--pkgs D]
          exit 0 when every package of the lake manifest is locked and every lock line is `absent` (not adopted yet) or `ok`; exit 1 and the reasons otherwise.
          `ok` = the manifest's rev is the lock's, the checkout's HEAD is that rev, and its spec_hash is the lock's. Anything else is BAD (a stale rev, a hash mismatch, a fork, an unlocked package).
    scripts/pinned-lib.py fetch   [same]        a locked library whose checkout is MISSING (a cold CI runner, a fresh scratch tree) is cloned from the manifest's url and checked out at the LOCK's rev (never at the manifest's):
          the fetch trusts nothing, `verify` runs after it and judges rev, HEAD and spec_hash exactly as before; an existing checkout is left alone (verify judges it); needs git and the network, no cache, no HOME.
    scripts/pinned-lib.py verdict [same]        one line per lock entry, `ROOT ok DIR HASH | absent | bad REASON`: the machine-readable verdict
    scripts/pinned-lib.py names [--lock F]      the lock's library names (scripts/trust-ledger-check.sh requires an entry `pin:NAME`)
    scripts/pinned-lib.py protected [--list F]  the lock, this script and its tests are protected paths (scripts/protected-set.sh --superset): exit 1 and the unprotected ones otherwise
A lock line is gate-defining: a change to the lock is judged by the relabel-attack suite (scripts/relabel-attacks.sh), and the lock, this tool and its test are protected paths.
Self-test: scripts/test_pinned_lib.sh."""
import hashlib, json, os, re, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT_DIR = os.path.dirname(HERE)
LOCK = os.path.join(HERE, "pinned-libs.lock")
MANIFEST = os.path.join(ROOT_DIR, "lake-manifest.json")
RESERVED = {"VbmLlm", "VbmLlmProofs", "Init", "Std", "Lean", "Lake"}      # roots that are ours or the toolchain's: a lock line may not claim them
PROTECTED = ["scripts/pinned-libs.lock", "scripts/pinned-lib.py", "scripts/test_pinned_lib.sh"]

def die(msg, code=1):
    print(f"pinned-lib: {msg}", file=sys.stderr); sys.exit(code)

def parse_lock(path):
    """-> list of dicts; a malformed line, a duplicate name or root, a reserved root, an unsafe path is an error (the lock is read strictly)."""
    try: text = open(path).read()
    except OSError as e: die(f"cannot read the lock {path}: {e}", 2)
    out, names, roots = [], set(), set()
    for n, raw in enumerate(text.splitlines(), 1):
        l = raw.split("#")[0].strip()
        if not l: continue
        f = l.split()
        if len(f) != 5: die(f"{path}:{n}: want 'NAME REV SPEC_HASH ROOT SPEC_PATHS' (5 fields), got {len(f)}", 2)
        name, rev, h, root, paths = f
        if not re.fullmatch(r"[a-z0-9][a-z0-9_-]*", name): die(f"{path}:{n}: bad name {name!r}", 2)
        if not re.fullmatch(r"[0-9a-f]{40}", rev): die(f"{path}:{n}: rev must be 40 hex digits (a full commit), got {rev!r}", 2)
        if not re.fullmatch(r"[0-9a-f]{64}", h): die(f"{path}:{n}: spec_hash must be 64 hex digits, got {h!r}", 2)
        if not re.fullmatch(r"[A-Z][A-Za-z0-9_]*", root) or root in RESERVED: die(f"{path}:{n}: bad or reserved module root {root!r}", 2)
        ps = paths.split(",")
        if any(not p or p.startswith("/") or ".." in p.split("/") for p in ps): die(f"{path}:{n}: unsafe spec path in {paths!r}", 2)
        if name in names or root in roots: die(f"{path}:{n}: duplicate library name or root", 2)
        names.add(name); roots.add(root)
        out.append({"name": name, "rev": rev, "hash": h, "root": root, "paths": ps})
    return out

def spec_hash(pkg, paths):
    files = []
    for p in paths:
        full = os.path.join(pkg, p)
        if p.endswith("/"):
            if not os.path.isdir(full): raise ValueError(f"spec directory {p} is missing")
            for d, dirs, fs in os.walk(full):
                dirs[:] = sorted(x for x in dirs if x != ".git")
                for x in fs:
                    q = os.path.join(d, x)
                    if os.path.islink(q) or not os.path.isfile(q): raise ValueError(f"{os.path.relpath(q, pkg)} is not a regular file")
                    files.append(os.path.relpath(q, pkg))
        else:
            if not os.path.isfile(full) or os.path.islink(full): raise ValueError(f"spec file {p} is missing or not a regular file")
            files.append(p)
    lines = sorted({f"{hashlib.sha256(open(os.path.join(pkg, f), 'rb').read()).hexdigest()} {f}\n" for f in files}, key=lambda s: s.encode())
    return hashlib.sha256("".join(lines).encode()).hexdigest()

def load_manifest(path):
    try: return json.load(open(path))
    except (OSError, ValueError) as e: die(f"cannot read the lake manifest {path}: {e}", 2)

def head_of(pkg):
    """The HEAD of PKG when PKG is itself a git checkout (its own top level: a directory inside another repository answers for THAT repository, which is no checkout of the library)."""
    if not os.path.exists(os.path.join(pkg, ".git")): return None
    top = subprocess.run(["git", "-C", pkg, "rev-parse", "--show-toplevel"], capture_output=True, text=True)
    if top.returncode or os.path.realpath(top.stdout.strip()) != os.path.realpath(pkg): return None
    r = subprocess.run(["git", "-C", pkg, "rev-parse", "HEAD"], capture_output=True, text=True)
    return r.stdout.strip() if r.returncode == 0 else None

def judge(lock, manifest, pkgs):
    """-> (verdicts: {name: (status, detail, dir, hash)}, problems for the whole manifest)."""
    mf = load_manifest(manifest)
    base = pkgs or os.path.join(os.path.dirname(os.path.abspath(manifest)), mf.get("packagesDir", ".lake/packages"))
    listed = {str(p.get("name")).strip("«»"): p for p in mf.get("packages", [])}   # lake writes a name with a hyphen as «vbm-json»; its directory is vbm-json
    problems = []
    names = {e["name"] for e in lock}
    for n, p in sorted(listed.items(), key=lambda x: str(x[0])):
        if n not in names: problems.append(f"the lake manifest lists package {n} ({p.get('url') or p.get('dir')}), which is not in the lock: an unlocked library")
    out = {}
    for e in lock:
        p = listed.get(e["name"])
        if p is None: out[e["name"]] = ("absent", "not in the lake manifest (not adopted)", None, None); continue
        pkg = os.path.join(base, e["name"]); why = []
        if p.get("type") != "git": why.append(f"the manifest entry is type {p.get('type')!r}, not git")
        if p.get("rev") != e["rev"]: why.append(f"stale rev: the manifest has {p.get('rev')}, the lock {e['rev']}")
        if not os.path.isdir(pkg): why.append(f"the checkout {pkg} is missing")
        else:
            h = head_of(pkg)
            if h is None: why.append(f"{pkg} is not a git checkout")
            elif h != e["rev"]: why.append(f"the checkout is at {h}, not the locked {e['rev']} (a fork or a moved checkout)")
            try: got = spec_hash(pkg, e["paths"])
            except ValueError as x: got = None; why.append(str(x))
            if got is not None and got != e["hash"]: why.append(f"spec_hash mismatch: the checkout hashes to {got}, the lock says {e['hash']}")
        out[e["name"]] = ("bad", "; ".join(why), pkg, None) if why else ("ok", "rev and spec_hash match the lock", pkg, e["hash"])
    return out, problems

def args_of(argv):
    o = {"lock": LOCK, "manifest": MANIFEST, "pkgs": None, "list": os.path.join(HERE, "protected-paths.txt")}
    i = 0
    while i < len(argv):
        k = argv[i]
        if k in ("--lock", "--manifest", "--pkgs", "--list") and i + 1 < len(argv): o[k[2:]] = argv[i + 1]; i += 2
        else: die(f"unknown argument {k}", 2)
    return o

def main(argv):
    if not argv: die("usage: pinned-lib.py hash|verify|verdict|names|protected", 2)
    cmd, rest = argv[0], argv[1:]
    if cmd == "hash":
        if len(rest) != 2: die("usage: pinned-lib.py hash DIR PATHS", 2)
        try: print(spec_hash(rest[0], rest[1].split(",")))
        except ValueError as x: die(str(x), 2)
        return 0
    a = args_of(rest)
    lock = parse_lock(a["lock"])
    if cmd == "names":
        for e in lock: print(e["name"])
        return 0
    if cmd == "protected":
        r = subprocess.run(["bash", os.path.join(HERE, "protected-set.sh"), "--superset", "/dev/stdin", a["list"]], input="\n".join(PROTECTED) + "\n", capture_output=True, text=True)
        if r.returncode: print("pinned-lib: not protected (scripts/protected-paths.txt must cover them, or a change could loosen the lock unseen):\n  " + "\n  ".join(r.stdout.split()), file=sys.stderr); return 1
        print("pinned-lib: the lock, its tool and its test are in the protected set")
        return 0
    if cmd == "fetch":
        mf = load_manifest(a["manifest"])
        base = a["pkgs"] or os.path.join(os.path.dirname(os.path.abspath(a["manifest"])), mf.get("packagesDir", ".lake/packages"))
        listed = {str(p.get("name")).strip("«»"): p for p in mf.get("packages", [])}
        env = dict(os.environ, GIT_TERMINAL_PROMPT="0")
        for e in lock:
            p = listed.get(e["name"]); pkg = os.path.join(base, e["name"])
            if p is None or os.path.exists(pkg): continue
            if p.get("rev") != e["rev"] or p.get("type") != "git" or not p.get("url"): continue   # verify names the mismatch; nothing is fetched for a pin that is already wrong
            print(f"pinned-lib: fetching {e['name']} {e['rev'][:12]} from {p['url']}")
            os.makedirs(base, exist_ok=True)
            for cmd_ in (["git", "clone", "-q", "--no-checkout", p["url"], pkg], ["git", "-C", pkg, "checkout", "-q", "--detach", e["rev"]]):
                r = subprocess.run(cmd_, env=env, capture_output=True, text=True, timeout=600)
                if r.returncode: print(f"pinned-lib: {' '.join(cmd_[:3])} failed: {r.stderr.strip()[-300:]}", file=sys.stderr); return 1
        return 0
    verdicts, problems = judge(lock, a["manifest"], a["pkgs"])
    if cmd == "verdict":
        for e in lock:
            st, why, pkg, h = verdicts[e["name"]]
            print(f"{e['root']} {st} {pkg or '-'} {h or why.replace(chr(10), ' ')}")
        for p in problems: print(f"- unlocked {p}")
        return 0
    if cmd == "verify":
        bad = list(problems)
        for e in lock:
            st, why, _, _ = verdicts[e["name"]]
            print(f"pin {e['name']} {e['root']} {e['rev'][:12]}: {st.upper() if st == 'bad' else st}: {why}")
            if st == "bad": bad.append(f"{e['name']}: {why}")
        for p in problems: print(f"pinned-lib: {p}", file=sys.stderr)
        for b in bad: print(f"pinned-lib: BAD {b}", file=sys.stderr)
        return 1 if bad else 0
    die(f"unknown command {cmd}", 2)

if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
