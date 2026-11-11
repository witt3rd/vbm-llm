#!/usr/bin/env python3
"""scripts/mutants.py: the scorecard's code-mutation metric (construction.mutation_score), reproduced locally on the working tree (docs/mutants.md).
The sites, the operator swaps, the seeded sample and the verdicts are the scorecard runner's (the VBM scorecard's runner: MUT_OPS, MUT_TOKEN, mutation_sites, MUT_LOOP, run_mutation):
one operator swap at a time in a COPY of the tree, then the harness; exit 0 = survived, 99 = not viable, anything else (a timeout included) = killed. The configuration below is a copy of the
[mutation] table of the scorecard's adapter for this repository; --adapter FILE reads the table from the adapter instead (the numbers then are the card's).
Mutant ids are `file:line:col:old:new` (line 1-based, col 0-based, as in the runner: two equal swaps on a line differ by the column). mutants-equivalent.txt (id TAB reason TAB expiry) lists the
mutants proved or argued equivalent; an entry with no reason, a bad id or an expired date is rejected, and one that matches no mutant is stale (both fail the run): the score is
killed / (killed + surviving non-equivalent). Usage: mise exec -- scripts/mutants.py [--adapter FILE] [--allowlist FILE] [--list] [--fast]   (--fast: reuse .lake of the tree; the default builds nothing: run setup yourself)"""
import argparse, concurrent.futures, datetime, os, queue, random, re, shutil, subprocess, sys, tempfile, tomllib

OPS = {"==": "!=", "!=": "==", "<=": "<", ">=": ">", "<": "<=", ">": ">=", "&&": "||", "||": "&&", "+": "-", "-": "+"}
TOKEN = re.compile(r"<<=|>>=|\+\+|--|->|<<|>>|\+=|-=|==|!=|<=|>=|&&|\|\||<|>|\+|-")
CFG = dict(files=["abi/vbm_json.c"], comment="//", mutants=50, seed=1, kill_timeout_seconds=120,
           setup_cmd="lake build LeanJson:static vbm-json-vectors >/dev/null 2>&1 && lake exe vbm-json-vectors --n 4 --out /tmp/v >/dev/null 2>&1",
           kill_cmd='leanc -isystem /usr/include $(test -d /usr/include/$(uname -m)-linux-gnu && echo -isystem /usr/include/$(uname -m)-linux-gnu) -I include -o /tmp/abi_t tests/abi_test.c abi/vbm_json.c .lake/build/lib/libvbm_x2djson_LeanJson.a >/dev/null 2>&1 || exit 99; /tmp/abi_t /tmp/v/vectors.jsonl >/dev/null 2>&1')  # probe-ok: run() puts it under .land/tool/bin/run-probe


def sites(root, files, comment):
    out = []
    for f in files:
        for ln, line in enumerate(open(os.path.join(root, f), errors="replace").read().split("\n")):
            code, q = "", None
            for ch in line:   # blank string and char literals; comments are cut at `comment` only (a `/* */` tail is NOT recognised: the runner's rule, so those sites are real mutants of a comment)
                if q: q = None if ch == q else q; code += " "
                elif ch in "\"'": q = ch; code += " "
                else: code += ch
            cut = code.find(comment) if comment else -1; code = code if cut < 0 else code[:cut]
            if code.lstrip().startswith(("*", "/*", "#")): continue
            out += [(f, ln, m.start(), m.group(), OPS[m.group()]) for m in TOKEN.finditer(code) if m.group() in OPS]
    return out


def mid(s): return f"{s[0]}:{s[1] + 1}:{s[2]}:{s[3]}:{s[4]}"


def load_allowlist(path, ids, today):
    """id TAB reason TAB expiry (YYYY-MM-DD); returns (set of equivalent ids, problems)."""
    eq, bad = set(), []
    for n, raw in enumerate(open(path).read().split("\n") if os.path.exists(path) else [], 1):
        if not raw.strip() or raw.lstrip().startswith("#"): continue
        p = raw.split("\t")
        if len(p) != 3 or not p[1].strip() or len(p[1].strip()) < 20: bad.append(f"{path}:{n}: need `id TAB reason (>= 20 chars) TAB expiry`"); continue
        try: exp = datetime.date.fromisoformat(p[2].strip())
        except ValueError: bad.append(f"{path}:{n}: the expiry {p[2]!r} is not YYYY-MM-DD"); continue
        if exp < today: bad.append(f"{path}:{n}: expired {exp}: re-argue {p[0]} or kill it")
        elif p[0] not in ids: bad.append(f"{path}:{n}: {p[0]} matches no mutant (stale id: the line moved or the code changed)")
        else: eq.add(p[0])
    return eq, bad


def main(argv):
    ap = argparse.ArgumentParser(); ap.add_argument("--adapter"); ap.add_argument("--allowlist", default="mutants-equivalent.txt"); ap.add_argument("--list", action="store_true")
    ap.add_argument("--jobs", type=int, default=1, help="mutants run in parallel, each worker in its own copy of the tree and its own scratch directory (the verdicts do not depend on it)")
    a = ap.parse_args(argv); root = os.getcwd(); cfg = dict(CFG)
    if a.adapter: cfg.update(tomllib.load(open(a.adapter, "rb"))["mutation"])
    ss = sites(root, cfg["files"], cfg["comment"])
    picked = sorted(random.Random(cfg["seed"]).sample(ss, min(cfg["mutants"], len(ss))))
    ids = {mid(s) for s in picked}
    eq, bad = load_allowlist(os.path.join(root, a.allowlist), ids, datetime.date.today())
    for b in bad: print("mutants: " + b, file=sys.stderr)
    if a.list:
        for s in picked: print(mid(s) + ("  [equivalent]" if mid(s) in eq else ""))
        return 1 if bad else 0
    tmp = tempfile.mkdtemp(prefix="mutants-")
    # a mutant may crash: every kill command runs under the shared probe helper (.land/tool/bin/run-probe: ulimit -c 0 PLUS the dumpable-clear preload, a private TMPDIR; ulimit alone still writes a crash-journal record), and "/tmp/" in it is this worker's private scratch
    def run(w, scratch, cmd, t):
        try: return subprocess.run([".land/tool/bin/run-probe", "bash", "-c", cmd.replace("/tmp/", scratch + "/")], cwd=w, timeout=t, capture_output=True).returncode
        except subprocess.TimeoutExpired: return 124
    def worker(j, todo, res):
        w = os.path.join(tmp, f"w{j}"); scratch = os.path.join(tmp, f"s{j}"); os.mkdir(scratch); shutil.copytree(root, w, symlinks=True, ignore=shutil.ignore_patterns(".git"))
        if cfg["setup_cmd"] and run(w, scratch, cfg["setup_cmd"], 3000): return "the setup command failed"
        base = run(w, scratch, cfg["kill_cmd"], cfg["kill_timeout_seconds"])
        if base != 0: return f"the harness fails on the UNMUTATED tree (exit {base}): a kill proves nothing"
        while True:
            try: s = todo.get_nowait()
            except queue.Empty: return None
            p = os.path.join(w, s[0]); lines = open(p).read().split("\n"); orig = lines[s[1]]
            lines[s[1]] = orig[:s[2]] + s[4] + orig[s[2] + len(s[3]):]; open(p, "w").write("\n".join(lines))
            res[mid(s)] = run(w, scratch, cfg["kill_cmd"], cfg["kill_timeout_seconds"]); lines[s[1]] = orig; open(p, "w").write("\n".join(lines))
    try:
        todo, res = queue.Queue(), {}
        for s in picked: todo.put(s)
        with concurrent.futures.ThreadPoolExecutor(max(1, a.jobs)) as ex: errs = [e for e in ex.map(lambda j: worker(j, todo, res), range(max(1, a.jobs))) if e]
        if errs: print("mutants: " + errs[0], file=sys.stderr); return 2
    finally: shutil.rmtree(tmp, ignore_errors=True)
    killed = [i for i, c in res.items() if c not in (0, 99)]; surv = [i for i, c in res.items() if c == 0]; nv = [i for i, c in res.items() if c == 99]
    open_ = [i for i in surv if i not in eq]; eqs = [i for i in surv if i in eq]
    for i in open_: print("SURVIVES   " + i)
    for i in eqs: print("equivalent " + i)
    raw = round(100 * len(killed) / max(1, len(killed) + len(surv)), 1); adj = round(100 * len(killed) / max(1, len(killed) + len(open_)), 1)
    print(f"mutants: LOCAL {len(picked)} mutants of {len(ss)} sites: {len(killed)} killed, {len(surv)} survived ({len(eqs)} argued equivalent), {len(nv)} not viable; score {raw} raw, {adj} over non-equivalent mutants")
    stale_eq = [i for i in eq if i not in surv]
    for i in stale_eq: print(f"mutants: {i} is listed as equivalent but was KILLED or not viable: drop the entry", file=sys.stderr)
    return 1 if (bad or open_ or stale_eq) else 0


if __name__ == "__main__": sys.exit(main(sys.argv[1:]))
