#!/usr/bin/env bash
# Is the gate-file diff of a change purely IMPROVING?  The owner's rule: a PR that touches the gate-defining set may be landed by the caretaker only if
# its gate-file diff is purely improving; otherwise it waits for the owner.
#   scripts/gate-diff-improving.sh <base-ref> <head-ref>      (run in the repo; the diff is taken from the merge base, like protected-set.sh)
# One line per changed gate-defining file ("PASS|FAIL file: why", FAIL names the exact offending lines), then a final PASS/FAIL. Exit 0 = PASS, 1 = FAIL, 2 = cannot decide.
#   NUMERIC BASELINES: every key moves only in its improving direction (table RULES below; an unknown key or field FAILS; a baseline that appears or disappears FAILS).
#   scripts/tier1.sh:  may only GAIN lines: a removed or changed line FAILS, so does an added line that weakens (|| true, exit 0, set +e, if false, ...) or that joins
#                      onto an existing line (a trailing backslash / && / || / |, or an added line that continues the one above).
#   Generated files (docs/proof-ledger.md): accepted only when the ledger baseline moved improving, or (counts unchanged) when its render source VbmLlmProofs/Ledger.lean changed
#                      (the ledger is owner-gated by protected-set.sh).
#   LISTS and GATE SOURCE: FAIL on ANY change (add, edit, delete): owner only.
#   --suite-judged (what scripts/land runs): a LIST or GATE SOURCE change is not owner-only but judged by the RELABEL-ATTACK SUITE (scripts/relabel-attacks.sh, run by the lander on the
#      proposed tree) instead; here it PASSes except scripts/protected-paths.txt, which must still protect everything the base list did
#      (scripts/protected-set.sh --superset). tier1.sh and the numeric baselines are judged the same in both modes.
#   --touched <base> <head>: print the gate-defining files the change touches (one per line; nothing = none): the lander runs the suite exactly when this prints something.
# Files outside this set are not judged here (scripts/protected-set.sh judges the wider protected set). Self-test: scripts/test_gate_diff_improving.sh.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
export GDI_HERE=$here GDI_SUITE=0 GDI_TOUCHED=0
while :; do case ${1:-} in --suite-judged) GDI_SUITE=1; shift;; --touched) GDI_TOUCHED=1; shift;; *) break;; esac; done
base=${1:?usage: gate-diff-improving.sh [--suite-judged|--touched] <base-ref> <head-ref>}; head=${2:?usage: gate-diff-improving.sh [--suite-judged|--touched] <base-ref> <head-ref>}
mb=$(git merge-base "$base" "$head") || { echo "gate-diff-improving: no merge base for $base $head" >&2; exit 2; }
# The judge is bounded: GDI_TIMEOUT seconds (default 120), then exit 2 "cannot decide" with a clear message (a gate must never hold the land lock unbounded).
rc=0; timeout -k 5 "${GDI_TIMEOUT:-120}" python3 - "$mb" "$head" <<'PY' || rc=$?
import os, re, subprocess, sys, tempfile
SUITE, TOUCHED, HERE = os.environ["GDI_SUITE"] == "1", os.environ["GDI_TOUCHED"] == "1", os.environ["GDI_HERE"]
mb, head = sys.argv[1:3]
def git(*a, check=True):
    r = subprocess.run(["git", *a], capture_output=True, text=True)
    if check and r.returncode: sys.exit(f"gate-diff-improving: git {' '.join(a)}: {r.stderr.strip()}") or 2
    return r.stdout if r.returncode == 0 else None
changed = set(git("diff", "--name-only", "--no-renames", mb, head).split("\n")) - {""}
def show(ref, p): return git("show", f"{ref}:{p}", check=False)

# RULES: baseline file -> [(key regex, {field: rule}, removable)].  Fields are `name=int` or positional (f0, f1, ...). Rules: down (may only fall), up (may only
# rise), free (not a ratchet), ratio (specified_share S T: the fraction S/T may only rise, compared exactly).  A key absent on one side counts as 0 on it
# (a new unverified module or a new allocation is a raise); a key that is not `removable` may not disappear (a target, or coverage of a function/module).
D = lambda *n: {k: "down" for k in n}
RULES = {
 "scripts/ledger-baseline.txt":  [(r"proved", {"f0": "up"}, False), (r"open", {"f0": "down"}, False), (r"total", {"f0": "up"}, False), (r"covered", {"f0": "up"}, False)],
}
LISTS = ["scripts/proof-eval-allow.txt", "scripts/protected-paths.txt", "scripts/generated-paths.txt", "scripts/pinned-libs.lock", "scripts/public-banned-hashes.txt",
         "docs/clause-index.txt", "scripts/protected-set.sh"]
SOURCE = ["scripts/LedgerGate.lean", "scripts/AxiomGate.lean", "scripts/land-direct", "scripts/regen-baselines.sh", "scripts/tier2.sh", "scripts/gate-diff-improving.sh",
          "scripts/trust-ledger-check.sh", "scripts/trust_ledger.py", "scripts/relabel-attacks.sh", "scripts/lint-pipefail.sh", "scripts/lint-proof-eval.sh", "scripts/lint-public", "scripts/pinned-lib.py",
          "scripts/run-tests-parallel.sh", "scripts/land.conf", "scripts/lib-no-crash-record.sh", "scripts/lint-workflows.py", "scripts/git-hermetic.sh"]
SOURCE_DIRS = ["scripts/attacks/", "scripts/land/", "scripts/land.d/"]   # the attack files, the pinned lander and its hooks are gate source too
out, bad = [], 0
def say(ok, f, why):
    global bad; bad += (not ok); out.append(f"{'PASS' if ok else 'FAIL'} {f}: {why}")

def parse(text):
    d = {}
    for l in (text or "").splitlines():
        if l.startswith("#") or not l.strip(): continue
        k, *f = l.split(); v = {}
        for i, x in enumerate(f):
            n, _, val = x.partition("=") if "=" in x else (f"f{i}", "", x)
            try: v[n] = int(val)
            except ValueError: v[n] = val
        d[k] = (l, v)
    return d

def baseline(p):
    o, n = show(mb, p), show(head, p)
    if o is None or n is None: return say(False, p, "the baseline " + ("appears" if o is None else "disappears") + " (owner only)")
    old, new, why = parse(o), parse(n), []
    for k in sorted(set(old) | set(new)):
        line = (new.get(k) or old[k])[0]
        rule = next(((fl, rm) for rx, fl, rm in RULES[p] if re.fullmatch(rx, k)), None)
        if rule is None: why.append(f"unknown key '{k}': +{line}"); continue
        fl, removable = rule
        if k not in new and not removable: why.append(f"key '{k}' removed: -{old[k][0]}"); continue
        ov, nv = (old.get(k) or ("", {}))[1], (new.get(k) or ("", {}))[1]
        if ov == nv: continue
        if "*" in fl: fl = {f: "down" for f in set(ov) | set(nv)}
        for f in sorted(set(ov) | set(nv)):
            if f not in fl: why.append(f"unknown field '{f}' of '{k}': +{line}"); continue
            a, b = ov.get(f, 0), nv.get(f, 0)
            if not isinstance(a, int) or not isinstance(b, int): why.append(f"non-numeric field '{f}' of '{k}': +{line}"); continue
            r = fl[f]
            if r == "ratio":
                if f == "f0":  # judged once, on the pair
                    (s0, t0), (s1, t1) = (ov.get("f0", 0), ov.get("f1", 1)), (nv.get("f0", 0), nv.get("f1", 1))
                    if s1 * t0 < s0 * t1: why.append(f"'{k}' fell {s0}/{t0} -> {s1}/{t1}: -{old[k][0]} +{line}")
            elif (r == "down" and b > a) or (r == "up" and b < a):
                why.append(f"'{k}' {f} moved the wrong way {a} -> {b} (may only {'fall' if r == 'down' else 'rise'}): " + (f"-{old[k][0]} " if k in old else "") + (f"+{line}" if k in new else ""))
    say(not why, p, "improving only" if not why else "; ".join(why))
    return not why

# An ADDED tier1.sh line must be a plain step or a guard: a denylist of masks (`|| true`) is a list the next mask is not on (`! cmd`, `cmd && :`, `: $(cmd)`, `trap 'exit 0' EXIT`, `cmd &`).
Q = r'(?:"(?:[^"\\]|\\.)*"|\'[^\']*\')'
# W is one alternation under ONE quantifier, every alternative starting on a distinct character (a nested `(?:x+|y)+` backtracks exponentially on a long line that fails to match: it ran 47 min on one).
W = rf'(?:[A-Za-z0-9_./=:,+@%-]|\$(?:\{{[A-Za-z_][A-Za-z0-9_]*\}}|[A-Za-z_][A-Za-z0-9_]*(?![A-Za-z0-9_]))|{Q})+'
R = rf'(?:>>? ?{W}|2>&1|>&2|2>>? ?{W}|< ?{W})'
CMD = rf'{W}(?: (?:{W}|{R}))*'
PLAIN = re.compile(rf'^{CMD}(?: \| {CMD})*$')
GUARD = re.compile(rf'^\[ [^\]]* \](?: && \[ [^\]]* \])* \|\| \{{ (?:echo|printf) {Q}(?: >&2)?; exit 1; \}}$')
BAD_FIRST = {":", "true", "false", "set", "trap", "exit", "return", "eval", "export", "local", "source", ".", "unset", "shopt", "exec", "test", "[", "if", "then", "fi", "for", "do", "done", "while",
             "until", "case", "esac", "function", "else", "elif", "alias", "builtin", "command", "wait", "kill", "disown", "read", "cd"}
def plain_step(a):
    s = re.sub(r"\s+#.*$", "", a.strip())
    if not s or s.startswith("#"): return True
    if GUARD.match(s): return True
    if "$(" in s or "`" in s: return False
    first = re.sub(Q, "Q", s).split()[0]
    return bool(PLAIN.match(s)) and first not in BAD_FIRST

WEAK = re.compile(r"\|\|\s*(true|:|echo|printf|continue|break|return|exit\s+0)\b|\|\|\s*:|set\s+\+e|\bexit(\s+0)?\s*($|;|&)|\breturn\s+0\b|\bif\s+(false|true)\b|\bwhile\s+false\b")
def tier1(p):
    d = git("diff", "-U0", "--no-renames", mb, head, "--", p); why = []; hl = (show(head, p) or "").splitlines()
    lines = d.splitlines(); i = 0
    while i < len(lines):
        m = re.match(r"@@ -\d+(?:,\d+)? \+(\d+)(?:,(\d+))? @@", lines[i])
        if not m: i += 1; continue
        start = int(m.group(1)); i += 1; added = []
        while i < len(lines) and not lines[i].startswith("@@"):
            l = lines[i]
            if l.startswith("-"): why.append(f"removed/changed: {l}")
            elif l.startswith("+"): added.append(l[1:])
            i += 1
        for a in added:
            if WEAK.search(re.sub(r"\s#.*$", "", a)): why.append(f"weakening: +{a}")
            elif not plain_step(a): why.append(f"not a plain step (an added line is one command, or a `[ test ] || {{ echo ...; exit 1; }}` guard; a loop, `if`, `!`, `&&`, `;`, `&`, `trap`, `set`, `:` or a `$(...)` argument can mask a failure: put it in a scripts/test_*.sh, which Tier 1 picks up by name): +{a}")
        if added:
            prev = hl[start - 2] if start >= 2 else ""
            cont = re.compile(r"(\\|&&|\|\||\|)\s*$")
            if cont.search(prev) and not prev.lstrip().startswith("#"): why.append(f"joins onto the line above ({prev.strip()[-40:]!r}): +{added[0]}")
            if cont.search(added[-1]) or re.match(r"\s*(&&|\|\||\|)", added[0]): why.append(f"joins onto an existing line: +{added[-1] if cont.search(added[-1]) else added[0]}")
    say(not why, p, "only added lines" if not why else "; ".join(why))

def is_source(p): return p in SOURCE or any(p.startswith(d) for d in SOURCE_DIRS)
if TOUCHED:
    print("\n".join(sorted(p for p in changed if p in RULES or p in LISTS or is_source(p) or p == "scripts/tier1.sh"))); sys.exit(0)

def protected_superset(p):
    """The protected list may only grow: every entry of the base list is still covered (scripts/protected-set.sh --superset, this copy's own)."""
    with tempfile.TemporaryDirectory() as d:
        for n, ref in (("old", mb), ("new", head)):
            open(f"{d}/{n}", "w").write(show(ref, p) or "")
        r = subprocess.run([f"{HERE}/protected-set.sh", "--superset", f"{d}/old", f"{d}/new"], capture_output=True, text=True)
    say(r.returncode == 0, p, "every entry of the base list is still protected (judged by the relabel-attack suite for the rest)" if r.returncode == 0 else "drops protection of: " + " ".join(r.stdout.split() or [r.stderr.strip()]))

ledger_ok = None
for p in sorted(changed):
    if p in RULES:
        ok = baseline(p)
        if p == "scripts/ledger-baseline.txt": ledger_ok = ok
    elif p == "scripts/tier1.sh": tier1(p)
    elif SUITE and p == "scripts/protected-paths.txt": protected_superset(p)
    elif (p in LISTS or is_source(p)) and SUITE: say(True, p, "a list/gate source: judged by the relabel-attack suite (scripts/relabel-attacks.sh), not by the owner")
    elif p in LISTS or is_source(p): say(False, p, "a list/gate source: any change waits for the owner")
gen = {"docs/proof-ledger.md"} | {l.split("#")[0].strip() for l in (show(mb, "scripts/generated-paths.txt") or "").splitlines()}
for p in sorted(changed & gen - set(RULES) - set(LISTS) - set(SOURCE) - {"scripts/tier1.sh"}):
    if p == "scripts/generated-paths.txt": continue
    ok = ledger_ok is True or (ledger_ok is None and ("VbmLlmProofs/Ledger.lean" in changed or "docs/clause-index.txt" in changed))
    say(ok, p, ("generated: the ledger baseline moved improving" if ledger_ok else "generated: re-rendered from the changed VbmLlmProofs/Ledger.lean, counts unchanged") if ok else "generated file changed but neither the ledger baseline moved improving nor its source VbmLlmProofs/Ledger.lean changed (hand edit?)")
if not out: out.append("PASS (no gate-defining file changed)")
print("\n".join(out)); print("FAIL" if bad else "PASS"); sys.exit(1 if bad else 0)
PY
case $rc in 124|137) echo "gate-diff-improving: FAIL: the judge ran past GDI_TIMEOUT=${GDI_TIMEOUT:-120}s and was killed (rc=$rc): cannot decide" >&2; exit 2;; *) exit "$rc";; esac
