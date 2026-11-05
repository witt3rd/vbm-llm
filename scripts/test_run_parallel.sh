#!/usr/bin/env bash
# Tier 1: scripts/run-tests-parallel.sh runs scripts concurrently, in separate temp dirs, and can fail: a failing script, a missing script, and a
# script the runner silently skipped each fail the run and name the script; the failing script's log is printed; a clean run passes.
set -euo pipefail
cd "$(dirname "$0")/.."
unset TEST_JOBS   # a caller (a memory-capped runner) may cap the parallelism; this test is about running in parallel
run=$(pwd)/scripts/run-tests-parallel.sh
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
fail() { echo "tier1: run-tests-parallel: $*" >&2; exit 1; }
mk() { printf '#!/usr/bin/env bash\n%s\n' "$2" > "$T/$1.sh"; }
mk ok1 'sleep 1; echo hi-from-ok1'
mk ok2 'sleep 1; d=$(mktemp -d); case "$d" in "$TMPDIR"/*) ;; *) echo "mktemp left TMPDIR: $d" >&2; exit 9;; esac'   # its mktemp lands in its own TMPDIR
mk bad 'echo boom-from-bad >&2; exit 3'
mk skipme 'echo never-runs'
# an xargs that silently drops the script named skipme (a runner that loses a script): the runner must notice there is no result for it
mkdir "$T/bin"; real=$(command -v xargs)
printf '#!/usr/bin/env bash\ntr "\\0" "\\n" | grep -v skipme | tr "\\n" "\\0" | %s "$@"\n' "$real" > "$T/bin/xargs"; chmod +x "$T/bin/xargs"
# 1. two scripts that sleep 1 s each finish together in well under 2 s, and pass
# (milliseconds, not $SECONDS: whole-second ticks made two parallel 1 s scripts read as 2 s whenever the run straddled a second boundary, which failed main's CI once; serial would be >= 2000 ms)
t0=$(date +%s%N); "$run" "$T/ok1.sh" "$T/ok2.sh" > "$T/out" 2>&1 || fail "a clean run failed: $(cat "$T/out")"
dt=$(( ($(date +%s%N) - t0) / 1000000 ))
[ "$dt" -lt 1900 ] || fail "two 1 s scripts took $dt ms: they did not run in parallel"
grep -q 'ok   .*ok1.sh' "$T/out" && grep -q '2 scripts passed' "$T/out" || fail "the clean run did not report both: $(cat "$T/out")"
# 2. a failing script fails the run, is named, and its log is printed; the others still ran
if "$run" "$T/ok1.sh" "$T/bad.sh" > "$T/out" 2>&1; then fail "a failing script passed"; fi
grep -q 'FAIL .*bad.sh: exit 3' "$T/out" && grep -q 'boom-from-bad' "$T/out" && grep -q 'ok   .*ok1.sh' "$T/out" || fail "a failing script is not reported with its log: $(cat "$T/out")"
# 3. a missing script fails the run
if "$run" "$T/ok1.sh" "$T/nothere.sh" > "$T/out" 2>&1; then fail "a missing script passed"; fi
grep -q 'FAIL .*nothere.sh: no such script' "$T/out" || fail "a missing script is not named: $(cat "$T/out")"
# 4. a script that is silently skipped (no result recorded) fails the run
if PATH="$T/bin:$PATH" "$run" "$T/ok1.sh" "$T/skipme.sh" > "$T/out" 2>&1; then fail "a silently skipped script passed"; fi
grep -q 'FAIL .*skipme.sh: no result' "$T/out" || fail "a silently skipped script is not reported: $(cat "$T/out")"
# 5. a script listed twice and an empty list are refused
if "$run" "$T/ok1.sh" "$T/ok1.sh" >/dev/null 2>&1; then fail "a duplicate was accepted"; fi
if "$run" >/dev/null 2>&1; then fail "an empty list passed"; fi
echo "run-tests-parallel: parallel, isolated, and fails on a failing, missing or silently skipped script: ok"
