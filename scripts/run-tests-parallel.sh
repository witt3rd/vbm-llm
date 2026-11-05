#!/usr/bin/env bash
# Run independent test scripts in parallel (Tier 1 wall time = the longest script, not the sum). Usage: scripts/run-tests-parallel.sh SCRIPT...
# Each script runs in its own TMPDIR (so its mktemp dirs cannot clash) with its output captured; a passing script prints one line, a failing
# one prints its whole log. The run FAILS if any script fails, is missing, or leaves no result (killed, or never started): a skipped script
# is a failure, never a pass. TEST_JOBS caps the parallelism (default: the core count). Scripts must bind port 0 (scripts/mock-serve.sh).
# A test that passes alone but fails here (or only on the CI runner) is a bug in the test: find it, never retry it or raise a timeout. Reproduce
# CI's 4 cores with `mise exec -- taskset -c 0-3 scripts/run-tests-parallel.sh $(grep -o '^par scripts/[a-z_]*\.sh' scripts/tier1.sh | cut -d' ' -f2)`,
# and one script in a loop with `for i in $(seq 30); do taskset -c 0-3 bash scripts/test_X.sh || break; done` (docs/worktrees.md, "A test that fails only in CI").
# Do not wait a fixed time; wait on the readiness signal. Do not `kill $!` of a backgrounded function or pipeline and assume the program in it died.
set -uo pipefail
cd "$(dirname "$0")/.."
[ $# -gt 0 ] || { echo "run-tests-parallel: no scripts given" >&2; exit 1; }
[ -z "$(printf '%s\n' "$@" | sort | uniq -d)" ] || { echo "run-tests-parallel: a script is listed twice" >&2; exit 1; }
out=$(mktemp -d); trap 'rm -rf "$out"' EXIT
export out
name() { echo "${1//\//_}"; }
run_one() {  # run_one SCRIPT: result files rc and secs only when the script ran to its end
  local n; n=$(name "$1"); mkdir "$out/$n.tmp"
  local t0=$SECONDS
  TMPDIR="$out/$n.tmp" bash "$1" > "$out/$n.log" 2>&1 < /dev/null; local rc=$?
  echo $(( SECONDS - t0 )) > "$out/$n.secs"; echo $rc > "$out/$n.rc"
}
export -f name run_one
printf '%s\0' "$@" | xargs -0 -n1 -P "${TEST_JOBS:-$(nproc)}" bash -c 'run_one "$0"'
bad=0
for s in "$@"; do
  n=$(name "$s")
  if [ ! -f "$s" ]; then echo "FAIL $s: no such script" >&2; bad=1
  elif [ ! -f "$out/$n.rc" ]; then echo "FAIL $s: no result (it was skipped, or died before it finished)" >&2; cat "$out/$n.log" 2>/dev/null >&2; bad=1
  elif [ "$(cat "$out/$n.rc")" != 0 ]; then echo "FAIL $s: exit $(cat "$out/$n.rc") after $(cat "$out/$n.secs") s" >&2; cat "$out/$n.log" >&2; bad=1
  else echo "ok   $s ($(cat "$out/$n.secs") s)"
  fi
done
[ $bad = 0 ] && echo "run-tests-parallel: $# scripts passed" || echo "run-tests-parallel: FAILED" >&2
exit $bad
