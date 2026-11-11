#!/usr/bin/env bash
# Tier 1: the FREESTANDING native library (scripts/build_native.sh: the generated C, abi/vbm_json.c and runtime/rt.c, -ffreestanding -nostdlib, no libc) against the Lean reference.
#   1. Builds it; `nm -u` of the object, the archive's member and the shared library is EMPTY and the only global symbols defined are the five ABI functions.
#   2. The shared vectors (vbm-json-vectors-1: JSONTestSuite and the bignum rows included) go through tests/abi_test.c linked against ONLY this library (the whole ABI test: every row, 100000-deep input, the
#      allocator hook, fault injection, no resident growth), and tests/abi_dump.c's answers (rc and a hash of every tape) are IDENTICAL to the hosted build's (shim + the toolchain's runtime).
#   3. tests/lean_layout.c: abi/lean_mini.h (the freestanding stand-in for lean.h, used by the shim here and by the scorecard's freestanding compile) agrees with lean.h; tests/native_rt.c: memcpy,
#      memmove, memset against references, and the runtime heap is flat over 4000 parses.
# Run: mise exec -- scripts/test_native.sh
set -euo pipefail
cd "$(dirname "$0")/.."
. .land/tool/lib/ran.sh   # ran_case / ran_done / must_fail: the self-tests count what they executed and a refused tool is a failure (.land/tool/docs/ran-evidence.md)
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
sysinc_flags() { printf '%s\n' -isystem "$1"; [ ! -d "$1/$(uname -m)-linux-gnu" ] || printf '%s\n' -isystem "$1/$(uname -m)-linux-gnu"; }
mapfile -t SYSFLAGS < <(sysinc_flags "${VBM_JSON_SYSINCLUDE:-/usr/include}")
[ -x .lake/build/bin/vbm-json-vectors ] && [ -f .lake/build/lib/libvbm_x2djson_LeanJson.a ] || lake build vbm-json-vectors LeanJson:static >/dev/null   # tier1 builds these once; concurrent lake runs in one tree are avoided
lib=.lake/build/lib/libvbm_x2djson_LeanJson.a
# 1. the build and its symbols
scripts/build_native.sh "$tmp/lib" > "$tmp/build.txt"; sed 's/^/test_native: /' "$tmp/build.txt"
for f in "$tmp/lib/vbm_json.o"; do
  [ -z "$(nm -u "$f")" ] || { echo "test_native: $f has undefined symbols" >&2; exit 1; }
  [ "$(nm -g --defined-only "$f" | sed 's/^[0-9a-f]* . //' | sort | tr '\n' ' ')" = "vbm_json_bytes_free vbm_json_escape_string vbm_json_free vbm_json_parse vbm_json_print_tape " ] || { echo "test_native: $f exports more than the ABI" >&2; nm -g --defined-only "$f" >&2; exit 1; }
done
[ -z "$(nm -D -u "$tmp/lib/libvbm_json.so")" ] || { echo "test_native: libvbm_json.so has undefined symbols" >&2; exit 1; }
[ "$(nm -D --defined-only "$tmp/lib/libvbm_json.so" | sed 's/^[0-9a-f]* . //' | sort | tr '\n' ' ')" = "vbm_json_bytes_free vbm_json_escape_string vbm_json_free vbm_json_parse vbm_json_print_tape " ] || { echo "test_native: libvbm_json.so exports more than the ABI" >&2; exit 1; }
echo "test_native: nm -u is empty for the object and the shared library; the only exports are the five ABI functions"
# 2. the vectors against this library only
v=${VBM_JSON_VECTORS:-}   # tier1 generates the vectors once and shares them; alone, the script generates its own
[ -n "$v" ] || { .lake/build/bin/vbm-json-vectors --n 4 --out "$tmp/v" >/dev/null; v="$tmp/v/vectors.jsonl"; }
leanc "${SYSFLAGS[@]}" -Wall -Wextra -Werror -I include -o "$tmp/abi_test" tests/abi_test.c "$tmp/lib/libvbm_json.a"
"$tmp/abi_test" "$v" | sed 's/^/test_native: /'; ran_case
leanc "${SYSFLAGS[@]}" -Wall -Wextra -Werror -I include -o "$tmp/dump_free" tests/abi_dump.c "$tmp/lib/libvbm_json.a"
leanc "${SYSFLAGS[@]}" -Wall -Wextra -Werror -I include -o "$tmp/dump_host" tests/abi_dump.c abi/vbm_json.c "$lib"
"$tmp/dump_free" "$v" > "$tmp/free.txt"; "$tmp/dump_host" "$v" > "$tmp/host.txt"
cmp "$tmp/free.txt" "$tmp/host.txt" || { echo "test_native: the freestanding library and the hosted build disagree" >&2; exit 1; }; [ -s "$tmp/free.txt" ] || { echo "test_native: the dump of the vectors is empty (nothing ran)" >&2; exit 1; }; ran_case
echo "test_native: freestanding == hosted: $(wc -l < "$tmp/free.txt") rows, same return code and same tape (hash) on every row"
# 3. lean_mini.h against lean.h, and the runtime from outside
layout() { leanc "${SYSFLAGS[@]}" -Wall -Wextra -Werror -I include -o "$1/layout" "$1/tests/lean_layout.c" && "$1/layout"; }   # layout DIR: DIR has tests/ and abi/
mkdir -p "$tmp/L/tests" "$tmp/L/abi"; cp tests/lean_layout.c "$tmp/L/tests/"; cp abi/lean_mini.h "$tmp/L/abi/"
layout "$tmp/L" | sed 's/^/test_native: /'
keepsyms="memcpy memmove memset vbm_json_rt_live"
rtmem() {  # rtmem OUTDIR [VBM_RT_C]: the runtime-test build with the memory functions kept global, and the test run
  VBM_KEEP="$keepsyms" ${2:+VBM_RT_C=$2} scripts/build_native.sh "$1" --no-so >/dev/null
  leanc "${SYSFLAGS[@]}" -O1 -fno-builtin-memcpy -Wall -Wextra -Werror -I include -o "$1/native_rt" tests/native_rt.c "$1/libvbm_json.a" && "$1/native_rt" "$v"
}
rtmem "$tmp/R" | sed 's/^/test_native: /'
ran_done test_native
echo "test_native: ok"
