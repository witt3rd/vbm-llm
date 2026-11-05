#!/usr/bin/env bash
# Tier 1: the crash-record check is the VENDORED, scoped one (scripts/land/lib/no-crash-record.sh; vbm-land's own tests are its full self-test): this repository's library IS that file, another process's crash is ignored, a crash of this run's own
# process tree fails the check, a quiet crash exits 139 and leaves no record, and a probe launched without ulimit -c 0 is refused by run-probe.
set -euo pipefail
cd "$(dirname "$0")/.."
. scripts/lib-ran.sh
ok_end=0; trap '[ "$ok_end" = 1 ] || { echo "test_no_crash_record: did not run to its end (a neutered or exiting library?)" >&2; exit 1; }' EXIT   # a library that exits when sourced must not pass
command -v jq >/dev/null || { echo "test_no_crash_record: jq is required" >&2; exit 1; }
. scripts/lib-no-crash-record.sh
T=$(mktemp -d); sleep 60 >/dev/null 2>&1 & kid=$!; trap 'kill "$kid" 2>/dev/null || true; rm -rf "$T"; [ "$ok_end" = 1 ] || { echo "test_no_crash_record: did not run to its end" >&2; exit 1; }' EXIT
fail() { echo "test_no_crash_record: $*" >&2; exit 1; }
cmp -s scripts/lib-no-crash-record.sh scripts/land/lib/no-crash-record.sh && ran_case || fail "scripts/lib-no-crash-record.sh is not the vendored library"
rec() { jq -nc --arg pid "$1" --arg pp "$2" --arg exe "$3" --arg ts "$(( $(date +%s) * 1000000 ))" '{MESSAGE_ID:"fc2e22bc6ee647b6b90729ab34a250b1",COREDUMP_PID:$pid,COREDUMP_PROC_STATUS:("PPid:\t\($pp)\nNSsid:\t4242000\n"),COREDUMP_CGROUP:"/x/other.scope",COREDUMP_EXE:$exe,COREDUMP_TIMESTAMP:$ts,COREDUMP_CMDLINE:$exe}'; }
shim() { printf '#!/usr/bin/env bash\ncat <<"EOF"\n%s\nEOF\n' "$(cat)" > "$T/jc"; chmod +x "$T/jc"; }
nocrash_begin 2>/dev/null; export NOCRASH_JOURNALCTL=$T/jc
rec 4242001 1 /tmp/other_probe | shim; nocrash_end >/dev/null 2>&1 && ran_case || fail "another process's crash (a fixed /tmp probe name) failed this landing's check"
rec 4242002 "$kid" /usr/bin/foo | shim; nocrash_end >/dev/null 2>&1 && fail "a crash inside this run's own process tree passed the check" || ran_case
unset NOCRASH_JOURNALCTL
printf '#include <stdlib.h>\nint main(int c, char **v) { if (c > 1) abort(); *(volatile int *)0 = 1; return 0; }\n' > "$T/c.c"; "${CC:-cc}" -o "$T/crash" "$T/c.c"
nocrash_begin 2>/dev/null
rc=0; quiet "$T/crash" 2>/dev/null || rc=$?; [ "$rc" = 139 ] && ran_case || fail "the quiet SIGSEGV probe exited $rc, not 139"
rc=0; quiet "$T/crash" abort 2>/dev/null || rc=$?; [ "$rc" = 134 ] && ran_case || fail "the quiet SIGABRT probe exited $rc, not 134"
nocrash_end >/dev/null && ran_case || fail "a quiet crash left a record of this landing's tree"
rc=0; bash -c 'ulimit -c unlimited; scripts/land/bin/run-probe --require' >/dev/null 2>&1 || rc=$?; [ "$rc" = 2 ] && ran_case || fail "a probe without ulimit -c 0 was not refused (exit $rc)"
rc=0; scripts/land/bin/run-probe --core-limit 1 true >/dev/null 2>&1 || rc=$?; [ "$rc" = 2 ] && ran_case || fail "a raised core limit was not refused (exit $rc)"
ran_done test_no_crash_record; ok_end=1
echo "test_no_crash_record: ok (the vendored scoped check: foreign crash ignored, own tree's crash fails, quiet crashes 139 and 134 leave no record, an unscoped probe is refused)"
