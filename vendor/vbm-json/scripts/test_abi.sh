#!/usr/bin/env bash
# Tier 1: the C ABI (include/vbm_json.h, abi/vbm_json.c) against the Lean reference. Builds the static library, generates the shared vectors from the REFERENCE
# (verdict, error code, canonical form; the JSONTestSuite files included), builds tests/abi_test.c with the shim and runs it: every row's verdict through vbm_json_parse, an accepted row's
# tape read back to the canonical bytes, 100000-deep input = VBM_JSON_DEPTH, a failing allocator = VBM_JSON_NOMEM with nothing leaked, no resident growth over 30000 parses.
# The hosted C (stdio, pthread) is compiled by the Lean toolchain's clang with the system headers: `leanc -isystem /usr/include` (the bundle has none) plus the multiarch directory
# `/usr/include/<arch>-linux-gnu` where it exists: Debian/Ubuntu (a cold machine) keep `bits/libc-header-start.h` there, Arch keeps it in /usr/include. A PREFLIGHT compiles a probe of the
# headers first and, when it fails, names the package to install (libc6-dev on Debian/Ubuntu, glibc on Arch) instead of a bare "file not found".
# VBM_JSON_SYSINCLUDE overrides /usr/include (a local rehearsal of that layout). Run: mise exec -- scripts/test_abi.sh
set -euo pipefail
cd "$(dirname "$0")/.."
. .land/tool/lib/ran.sh   # ran_case / ran_done / must_fail: the self-tests count what they executed and a refused tool is a failure (.land/tool/docs/ran-evidence.md)
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
sysinc_flags() { printf '%s\n' -isystem "$1"; [ ! -d "$1/$(uname -m)-linux-gnu" ] || printf '%s\n' -isystem "$1/$(uname -m)-linux-gnu"; }
preflight() {  # preflight SYSINC: the hosted headers the test needs must compile; otherwise say which package provides them
  local flags; mapfile -t flags < <(sysinc_flags "$1")
  printf '#include <stdio.h>\n#include <stdint.h>\n#include <stdlib.h>\n#include <string.h>\n#include <pthread.h>\nint main(void){return 0;}\n' > "$tmp/probe.c"
  leanc -fsyntax-only "${flags[@]}" "$tmp/probe.c" 2>"$tmp/probe.err" || {
    echo "test_abi: the C library headers are missing or not found under $1 (the bundled clang has none; this test is hosted C: stdio, pthread)." >&2
    echo "test_abi: install them: libc6-dev (Debian/Ubuntu: apt-get install libc6-dev), glibc (Arch), glibc-devel (Fedora); the compiler said:" >&2
    sed 's/^/test_abi:   /' "$tmp/probe.err" >&2; return 1; }
}
preflight "${VBM_JSON_SYSINCLUDE:-/usr/include}"
mapfile -t SYSFLAGS < <(sysinc_flags "${VBM_JSON_SYSINCLUDE:-/usr/include}")
[ -x .lake/build/bin/vbm-json-vectors ] && [ -f .lake/build/lib/libvbm_x2djson_LeanJson.a ] || lake build LeanJson:static vbm-json-vectors >/dev/null   # tier1 builds these once; concurrent lake runs in one tree are avoided
lib=.lake/build/lib/libvbm_x2djson_LeanJson.a; [ -f "$lib" ] || { echo "test_abi: $lib was not built" >&2; exit 1; }
v=${VBM_JSON_VECTORS:-}   # tier1 generates the vectors once and shares them; alone, the script generates its own
[ -n "$v" ] || { .lake/build/bin/vbm-json-vectors --n 4 --out "$tmp/v" >/dev/null; v="$tmp/v/vectors.jsonl"; }
build() { leanc "${SYSFLAGS[@]}" -Wall -Wextra -Werror -I include -o "$1" tests/abi_test.c "$2" "$lib"; }   # build OUT SHIM.c
build "$tmp/abi_test" abi/vbm_json.c
"$tmp/abi_test" "$v"; ran_case   # every row, depth, allocator, leak
ran_done test_abi
echo "test_abi: ok"
