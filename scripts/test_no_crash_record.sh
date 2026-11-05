#!/usr/bin/env bash
# Tier 1: scripts/lib-no-crash-record.sh. Negative self-tests: a coredumpctl that reports an entry for a /tmp executable makes nocrash_end FAIL (shim, no real core), an empty one passes, an unrelated
# executable is ignored, a missing coredumpctl is skipped with a note; and a REAL deliberate crash under `quiet` exits 139 (asserted via $?) and leaves nothing for the real coredumpctl.
set -euo pipefail
cd "$(dirname "$0")/.."
. scripts/lib-ran.sh   # ran_case counts each executed check, ran_done prints the evidence line `ran: NAME: N cases` (docs/decisions/0002-ran-evidence.md)
[ "$(bash -c '. scripts/lib-no-crash-record.sh; echo loaded')" = loaded ] && ran_case || { echo "test_no_crash_record: scripts/lib-no-crash-record.sh does not load (a stub that exits?)" >&2; exit 1; }
. scripts/lib-no-crash-record.sh
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
fail() { echo "test_no_crash_record: $*" >&2; exit 1; }
mkshim() { printf '#!/usr/bin/env bash\n%s\n' "$1" > "$T/cdc"; chmod +x "$T/cdc"; }
export NOCRASH_COREDUMPCTL="$T/cdc"
mkshim 'echo "Wed 2026-01-01 00:00:00 UTC 1 1000 1000 SIGSEGV none /tmp/tmp.x/M/layout -"'
nocrash_begin; if nocrash_end >/dev/null 2>"$T/err"; then fail "an entry for a /tmp executable did not fail the check"; fi
grep -q 'M/layout' "$T/err" && ran_case || fail "the failure did not name the record"
mkshim 'exit 0'; nocrash_begin; nocrash_end >/dev/null 2>&1 && ran_case || fail "an empty list failed the check"
mkshim 'echo "Wed 2026-01-01 00:00:00 UTC 1 1000 1000 SIGSEGV none /usr/bin/firefox -"'; nocrash_begin; nocrash_end >/dev/null 2>&1 && ran_case || fail "an unrelated crash failed the check"
export NOCRASH_COREDUMPCTL="$T/none"; nocrash_begin 2>"$T/err"; grep -q SKIPPED "$T/err" && ran_case || fail "a missing coredumpctl was not noted"; nocrash_end >/dev/null && ran_case || fail "a missing coredumpctl failed the check"
# real: a deliberate SIGSEGV and SIGABRT under quiet, status asserted, and the real coredumpctl sees nothing
unset NOCRASH_COREDUMPCTL
printf '#include <stdlib.h>\nint main(int c, char **v) { if (c > 1) abort(); *(volatile int *)0 = 1; return 0; }\n' > "$T/c.c"; "${CC:-cc}" -o "$T/crash" "$T/c.c"
nocrash_begin
rc=0; quiet "$T/crash" 2>/dev/null || rc=$?; [ "$rc" = 139 ] && ran_case || fail "the quiet SIGSEGV probe exited $rc, not 139"
rc=0; quiet "$T/crash" abort 2>/dev/null || rc=$?; [ "$rc" = 134 ] && ran_case || fail "the quiet SIGABRT probe exited $rc, not 134"
nocrash_end && ran_case || fail "a quiet crash left a record"
ran_done test_no_crash_record
echo "test_no_crash_record: ok (shim: a record fails the check, none or unrelated passes, missing tool skips; real quiet crashes: 139 and 134, no record)"
