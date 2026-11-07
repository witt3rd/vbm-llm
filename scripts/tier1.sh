#!/usr/bin/env bash
# Tier 1 (pre-landing gate): forbidden constructs, the import rule, zero-warning build, the axiom gate, the obligation ledger (with the spec-clause tags), the trust ledger, the pinned library,
# the vendored lander's drift check, the public-readiness lint, the conformance vectors, and the offline self-tests of the process scripts (protected set, diff judge, relabel-attack suite).
# Every gate has a negative self-test and runs it here. Run from the repo root: mise exec -- scripts/tier1.sh.
set -euo pipefail
cd "$(dirname "$0")/.."
# A sourced library that has been replaced by a stub (`exit 0`) would end this script, and every test of it, with success: each is checked to define its function before it is sourced (the relabel-attack suite attacks this).
[ "$(grep -c '^nocrash_begin()' scripts/lib-no-crash-record.sh)" = 1 ] || { echo "tier1: scripts/lib-no-crash-record.sh does not define nocrash_begin" >&2; exit 1; }
# RAN-EVIDENCE (docs/decisions/0002-ran-evidence.md): a gate or self-test that never ran must not pass. Every test script and every concurrent gate ends with `ran: NAME: N cases` (N > 0, or the gate's own count line named in
# scripts/ran-gates.txt); scripts/run-tests-parallel.sh and the check below FAIL a job without it, and a refused tool, a SKIPPED check or a stop by a guard is a failure, never a pass (scripts/ran-evidence.sh, scripts/test_ran_evidence.sh).
[ "$(grep -c '^ran_done()' scripts/lib-ran.sh)" = 1 ] || { echo "tier1: scripts/lib-ran.sh does not define ran_done" >&2; exit 1; }
[ "$(grep -c '^must_fail()' scripts/lib-ran.sh)" = 1 ] || { echo "tier1: scripts/lib-ran.sh does not define must_fail" >&2; exit 1; }
[ "$(grep -c '^  check-dir)' scripts/ran-evidence.sh)" = 1 ] || { echo "tier1: scripts/ran-evidence.sh does not define check-dir" >&2; exit 1; }
# No test may leave a crash record (systemd-coredump, hence a desktop notification): the whole run is wrapped (scripts/lib-no-crash-record.sh; its self-test is test_no_crash_record.sh).
. scripts/lib-no-crash-record.sh; nocrash_begin

# The independent test scripts are declared with `par` where they are described below and run in parallel at the end (scripts/run-tests-parallel.sh): Tier 1 wall time is the longest script, not the sum.
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
# Long runners (scripts/long-runners.txt) run under scripts/run-scoped.sh (a bounded transient scope, reaped on exit: an aborted run cannot orphan); the lint is negative-tested here (a guard against accidents: indirection is its stated limit).
scripts/lint-scoped-runners.sh --selftest


# 1d. The vendored lander is the pinned copy (no local patch): the drift check, offline.
scripts/land/bin/land-check

# 1e. Pinned libraries: every package of the lake manifest is a line of the protected lock scripts/pinned-libs.lock, and every adopted one is exactly what the lock says (rev, checkout, spec hash).
scripts/pinned-lib.py fetch
scripts/pinned-lib.py verify

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
# vbm-json (from c0d7830) compiles with `-include <its own dir>/.lake/packages/vbm-simd/include/vbm_simd.h`, but as a dependency lake puts its own dependency vbm-simd beside it: link that path to the one lake made (an upstream defect of vbm-json's lakefile).
lake resolve-deps; mkdir -p .lake/packages/vbm-json/.lake/packages; ln -sfn ../../../vbm-simd .lake/packages/vbm-json/.lake/packages/vbm-simd
lake build VbmLlm VbmLlmProofs vbm-llm-vectors   # once, for the gates and every test (they build nothing more)

# 2a. The axiom gate: every constant of ours depends only on propext, Classical.choice, Quot.sound (--selftest: a non-standard axiom is rejected).
bg axiom-gate lake env lean --run scripts/AxiomGate.lean --selftest

# 2b. The obligation ledger: named theorems exist; spec-clause tags are in the index; proved may only rise, open may only fall, coverage may only rise. Renders docs/proof-ledger.md.
bg ledger-gate lake env lean --run scripts/LedgerGate.lean --selftest


# 2d. The conformance vectors (vectors/openai-chat): every recorded reply decodes to its expectation, and the check is shown able to fail (a tampered row, a missing vector).
bg vectors-check lake exe vbm-llm-vectors --check --selftest


# 2f. The public-readiness lint: no private name, no path of ours, anywhere in the tree; it is shown able to fail.
par scripts/test_lint_public.sh

# 3. The process scripts, offline, in scratch repos.
# 3b. The parallel runner: a failing, missing or silently skipped script fails the run.
# 3c'. The ran-evidence mechanism (scripts/lib-ran.sh, scripts/ran-evidence.sh): the shared negative test: a refused, missing, skipped, silent or zero-count check FAILS.
par scripts/test_ran_evidence.sh
par scripts/test_run_parallel.sh
# 3c. The crash-record check and the quiet probe runner (scripts/lib-no-crash-record.sh): a coredumpctl entry fails the run (shim), a quiet crash leaves none.
par scripts/test_no_crash_record.sh

# 3f. scripts/run-scoped.sh (status, bound, an aborted run leaves no orphan) and scripts/lib-reap.sh (an aborted script leaves none of its background jobs).
par scripts/test_run_scoped.sh
par scripts/test_reap.sh

# 4. The declared test scripts, in parallel; a failing, missing or silently skipped one fails Tier 1. Every scripts/test_*.sh must be declared.
for f in scripts/test_*.sh; do case " ${tests[*]} " in *" $f "*) ;; *) echo "tier1: $f is not declared with par" >&2; exit 1;; esac; done
echo "tier1: ${#tests[@]} test scripts: ${tests[*]}"
bg tests scripts/run-tests-parallel.sh "${tests[@]}"
bgwait
scripts/ran-evidence.sh check-dir "$bgdir" scripts/ran-gates.txt   # every concurrent gate and the tests job ran something: its own count (scripts/ran-gates.txt) or a ran line
nocrash_end

echo "tier1: ok"
