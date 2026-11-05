# Sourced library: nothing a test does on purpose may leave a crash record (systemd-coredump) or a desktop notification. Two parts.
#  1. quiet CMD...: run CMD (a probe or mutant that is MEANT to crash) so that the kernel never dumps it. `ulimit -c 0` or 1 does NOT do it: with a piped core_pattern
#     (systemd-coredump) the kernel pipes the crash anyway and the journal gets a record (measured on kernel 7.2: both limits still produced one). What does it is the process clearing its
#     own dumpable flag (prctl PR_SET_DUMPABLE 0); an LD_PRELOAD constructor does that for any dynamic binary. The exit status is the shell's own: 139 SIGSEGV, 134 SIGABRT; assert it with $?.
#  2. nocrash_begin / nocrash_end: wrap a whole test run; nocrash_end FAILS (returns 1) when coredumpctl gained an entry for an executable under /tmp or the repo since nocrash_begin.
#     Without coredumpctl it prints a note and passes. NOCRASH_COREDUMPCTL names the command (the self-test uses a shim).
nocrash_quiet_so=""
nocrash_build() {  # builds the preload once per process tree into a private temp dir
  [ -n "$nocrash_quiet_so" ] && [ -f "$nocrash_quiet_so" ] && return 0
  local d; d=$(mktemp -d); nocrash_quiet_so="$d/quiet.so"
  printf '#include <sys/prctl.h>\n__attribute__((constructor)) static void q(void) { prctl(PR_SET_DUMPABLE, 0, 0, 0, 0); }\n' > "$d/q.c"
  "${CC:-cc}" -shared -fPIC -o "$nocrash_quiet_so" "$d/q.c" || { echo "lib-no-crash-record: cannot build the quiet preload with ${CC:-cc}" >&2; return 1; }
}
quiet() {  # quiet CMD...: runs in a subshell with no core limit and the dumpable flag cleared; returns CMD's status
  nocrash_build || return 1
  ( ulimit -c 0; LD_PRELOAD="$nocrash_quiet_so${LD_PRELOAD:+:$LD_PRELOAD}" exec "$@" )
}
nocrash_cmd() { echo "${NOCRASH_COREDUMPCTL:-coredumpctl}"; }
nocrash_begin() {
  nocrash_t0=$(date +%s)
  command -v "$(nocrash_cmd)" >/dev/null 2>&1 || echo "no-crash-record: SKIPPED ($(nocrash_cmd) not available: no crash records to check)" >&2
}
nocrash_end() {  # prints the offending records and returns 1 when there are any
  command -v "$(nocrash_cmd)" >/dev/null 2>&1 || { echo "no-crash-record: skipped, $(nocrash_cmd) not available"; return 0; }
  sleep 2   # systemd-coredump records asynchronously
  local out; out=$("$(nocrash_cmd)" list --no-pager --no-legend --since "@$nocrash_t0" 2>/dev/null | grep -E " (/tmp/|$(pwd -P)/)" || true)
  if [ -n "$out" ]; then echo "no-crash-record: FAILED: a test left a crash record (a probe that is meant to crash must run under 'quiet', scripts/lib-no-crash-record.sh):" >&2; echo "$out" >&2; return 1; fi
  echo "no-crash-record: ok (no coredumpctl entry for /tmp or the repo during the run)"
}
