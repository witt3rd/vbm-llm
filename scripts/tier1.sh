#!/usr/bin/env bash
# Tier 1 (pre-landing gate): forbidden constructs, the import rule, zero-warning build, the axiom gate, the obligation ledger (with the spec-clause tags), the trust ledger, the pinned library,
# the vendored lander's drift check, the public-readiness lint, the conformance vectors, and the offline self-tests of the process scripts (protected set, diff judge, relabel-attack suite).
# Every gate has a negative self-test and runs it here. Run from the repo root: mise exec -- scripts/tier1.sh.
set -euo pipefail
cd "$(dirname "$0")/.."
# RAN-EVIDENCE (.land/tool/docs/ran-evidence.md): a gate or self-test that never ran must not pass. Every test script and every concurrent gate ends with `ran: NAME: N cases` (N > 0, or the gate's own count line named in
# scripts/ran-gates.txt); .land/tool/bin/run-tests-parallel and the check below FAIL a job without it, and a refused tool, a SKIPPED check or a stop by a guard is a failure, never a pass. The tools are the vendored ones: land-check refuses an edited copy.
# No test may leave a crash record (systemd-coredump, hence a desktop notification): the whole run is wrapped (.land/tool/lib/no-crash-record.sh, tested in vbm-land).
. .land/tool/lib/no-crash-record.sh; nocrash_begin

# The independent test scripts are declared with `par` where they are described below and run in parallel at the end (.land/tool/bin/run-tests-parallel): Tier 1 wall time is the longest script, not the sum.
# A test script must use its own temp dirs. Every scripts/test_*.sh must be declared.
tests=(); par() { tests+=("$@"); }
# The gates after the build are independent of each other and of the tests: they run concurrently (`bg NAME CMD...`, output kept and shown on failure; `bgwait` below).
bgdir=$(mktemp -d); bgnames=()
bg() { local n=$1; shift; bgnames+=("$n"); ( "$@" ) > "$bgdir/$n.log" 2>&1 & echo $! > "$bgdir/$n.pid"; }
bgwait() { local bad=0 n; for n in "${bgnames[@]}"; do if wait "$(cat "$bgdir/$n.pid")"; then cat "$bgdir/$n.log"; else echo "tier1: FAILED: $n" >&2; cat "$bgdir/$n.log" >&2; bad=1; fi; done; [ $bad = 0 ] || exit 1; }

# Lean sources under the roots that exist: VbmLlm (spec + code), VbmLlmProofs, vectors (the checker), and the two umbrella files.
lean_sources() { find VbmLlm VbmLlmProofs vectors -name '*.lean' 2>/dev/null; ls VbmLlm.lean VbmLlmProofs.lean 2>/dev/null; }

# 1. Forbidden constructs anywhere in Lean sources (AGENTS.md hard rules). Comments may mention them only on lines marked `-- tier1-allow`.
forbidden() { grep -HnE '\b(sorry|admit|axiom|unsafe|implemented_by|csimp)\b' "$@" | grep -v 'tier1-allow' || true; }
bad=$(forbidden $(lean_sources))
if [ -n "$bad" ]; then echo "tier1: forbidden construct(s):" >&2; echo "$bad" >&2; exit 1; fi
# the scan can fail: each forbidden word is flagged, and the tier1-allow marker (and only it) lets a comment mention one
st=$(mktemp); trap 'rm -f "$st"; rm -rf "$bgdir"' EXIT
for w in sorry admit axiom unsafe implemented_by csimp; do
  echo "theorem t : True := by $w" > "$st"; [ -n "$(forbidden "$st")" ] || { echo "tier1: the forbidden-constructs scan does not flag '$w'" >&2; exit 1; }
done
echo "-- a comment that says sorry -- tier1-allow" > "$st"; [ -z "$(forbidden "$st")" ] || { echo "tier1: the tier1-allow marker is not honoured" >&2; exit 1; }
echo "-- a comment that says sorry" > "$st"; [ -n "$(forbidden "$st")" ] || { echo "tier1: an unmarked comment is not flagged" >&2; exit 1; }
echo "tier1: forbidden-constructs scan: negative self-tests ok (each forbidden word is flagged, the tier1-allow marker is honoured)"

# 1a. VbmLlm/ imports Init (implicitly), the pinned LeanJson and other VbmLlm modules: no Std, no Lean, no VbmLlmProofs, no `prelude`, nothing else.
bad_imports() { grep -HnE '^[[:space:]]*((public|meta|private)[[:space:]]+)*(import|prelude)\b' "$@" | grep -vE ':[0-9]+:import (VbmLlm|LeanJson)(\.[A-Za-z0-9_]+)*[[:space:]]*$' || true; }
bad=$(bad_imports $(find VbmLlm -name '*.lean') VbmLlm.lean)
if [ -n "$bad" ]; then echo "tier1: VbmLlm may import only VbmLlm and LeanJson modules (Init is implicit):" >&2; echo "$bad" >&2; exit 1; fi
for imp in 'import Lean' 'import Std.Data.HashMap' 'import VbmLlmProofs.Ledger' 'prelude' 'public import Lean.Data.Json' 'import LeanJsonX' 'import LeanJsonProofs.Ledger'; do
  printf '%s\n' "$imp" > "$st"; [ -n "$(bad_imports "$st")" ] || { echo "tier1: the import scan does not flag: $imp" >&2; exit 1; }
done
printf 'import LeanJson.Value\nimport VbmLlm.Wire\n' > "$st"; [ -z "$(bad_imports "$st")" ] || { echo "tier1: the import scan flags an allowed import" >&2; exit 1; }
echo "tier1: import scan: negative self-tests ok (each import outside Init, LeanJson and VbmLlm is flagged)"

# 1b. Pipefail-unsafe pipelines (an early-exiting consumer) are flaky by construction; the lint has a negative self-test.
scripts/lint-pipefail.sh
# Long runners (scripts/long-runners.txt; none declared today) run under the vendored .land/tool/bin/run-scoped.sh (a bounded transient scope, reaped on exit); the heavy-host guard's lint checks it (vbm-land docs/no-build-host.md).
.land/tool/bin/no-build-guard --lint .


# 1d. The vendored lander is the pinned copy (no local patch): the drift check, offline.
.land/tool/bin/land-check

# 1e. Pinned libraries: every vendored library is exactly its lock line (.land/pins.lock; vbm-land docs/pin.md), and there is one copy of each in the closure.
.land/tool/bin/land-pin verify

# 2. Build the libraries and the vector checker; warningAsError is set in lakefile.lean, so any warning fails. The mechanism is checked: the option is set, and a file with a warning fails under it.
grep -q 'warningAsError, true' lakefile.lean || { echo "tier1: lakefile.lean does not set warningAsError" >&2; exit 1; }
printf 'def f (x : Nat) : Nat :=\n  let y := 1\n  2\n' > "$st"
wout=$(lake env lean -DwarningAsError=true "$st" 2>&1) && { echo "tier1: a build with a warning succeeds under warningAsError (the zero-warning gate cannot fail)" >&2; exit 1; }
grep -q 'not explicitly referenced' <<<"$wout" || { echo "tier1: the file with a warning failed, but not because of the warning (the self-test would pass for the wrong reason): $wout" >&2; exit 1; }
printf 'def f (x : Nat) : Nat := x\n' > "$st"
lake env lean -DwarningAsError=true "$st" >/dev/null 2>&1 || { echo "tier1: a clean file fails under warningAsError (the control of the zero-warning self-test)" >&2; exit 1; }
echo "tier1: zero-warning build: negative self-test ok (a file with a warning fails under warningAsError)"
# The inline check above is the first version (it passes when lake is refused: the defect); scripts/check-zero-warning.sh is the check: the warning's own diagnostic is required, a clean file must pass, it prints `ran: zero-warning: 3 cases`.
scripts/check-zero-warning.sh
lake build VbmSimd:static LeanJson:static   # built alone first: a module of vbm-simd reached by two paths is then never built twice at once
lake build VbmLlm VbmLlmProofs vbm-llm-vectors   # once, for the gates and every test (they build nothing more)

# 2a. The axiom gate: every constant of ours depends only on propext, Classical.choice, Quot.sound (--selftest: a non-standard axiom is rejected).
bg axiom-gate .land/tool/bin/land-lean axiom --selftest
.land/tool/bin/land-lean trust   # the trust ledger (docs/trust-ledger.md): what cannot be proven is marked as trusted, and what must be marked is derived from the tree (vbm-land docs/lean-gates.md)

# 2b. The obligation ledger: named theorems exist; spec-clause tags are in the index; proved may only rise, open may only fall, coverage may only rise. Renders docs/proof-ledger.md.
bg ledger-gate lake env lean --run scripts/LedgerGate.lean --selftest


# 2d. The conformance vectors (vectors/openai-chat): every recorded reply decodes to its expectation, and the check is shown able to fail (a tampered row, a missing vector).
bg vectors-check lake exe vbm-llm-vectors --check --selftest


# 2f. The public-readiness lint: no private name, no path of ours, anywhere in the tree; it is shown able to fail.
par scripts/test_lint_public.sh

# 3. The process scripts, offline, in scratch repos.
# 3b. The test-running runtime (ran-evidence, the parallel runner, the crash-record check, run-scoped, the reaper) is the vendored tool's and is tested in vbm-land.
# Every concurrent gate must say how its count is read: a `bg NAME` of this script has a line in scripts/ran-gates.txt, or prints its own `ran: NAME: N cases` (the tests job does).
for g in $(sed -nE 's/^bg ([A-Za-z0-9_-]+) .*/\1/p' scripts/tier1.sh); do
  [ "$g" = tests ] && continue
  grep -qE "^$g " scripts/ran-gates.txt || { echo "tier1: the concurrent gate $g has no line in scripts/ran-gates.txt: its count is not required" >&2; exit 1; }
done

# 4. The declared test scripts, in parallel; a failing, missing or silently skipped one fails Tier 1. Every scripts/test_*.sh must be declared.
for f in scripts/test_*.sh; do case " ${tests[*]} " in *" $f "*) ;; *) echo "tier1: $f is not declared with par" >&2; exit 1;; esac; done
echo "tier1: ${#tests[@]} test scripts: ${tests[*]}"
bg tests .land/tool/bin/run-tests-parallel "${tests[@]}"
bgwait
.land/tool/bin/ran-evidence check-dir "$bgdir" scripts/ran-gates.txt   # every concurrent gate and the tests job ran something: its own count (scripts/ran-gates.txt) or a ran line
nocrash_end

echo "tier1: ok"
