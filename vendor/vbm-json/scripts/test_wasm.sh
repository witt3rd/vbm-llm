#!/usr/bin/env bash
# Tier 1 (when `node` is on PATH; VBM_JSON_REQUIRE_NODE=1 makes its absence a failure): the freestanding wasm32 build of the fast parser (scripts/build_wasm.sh: the generated C of LeanJson, the unmodified
# abi/vbm_json.c, runtime/rt.c; clang --target=wasm32 -nostdlib, no libc, no WASI, no imports) against the Lean reference and the native ABI.
#   1. Builds the module; generates the shared vectors (vbm-json-vectors-1, JSONTestSuite included) from the REFERENCE; tests/wasm/wasm_test.mjs runs every row through the module (verdict, error code,
#      the tape read back to the canonical bytes), 100000-deep input = depth error without a trap, the allocator refuses an impossible size, no leak.
#   2. The native ABI (tests/abi_dump.c over abi/vbm_json.c) answers the same rows; the two answer files (rc and a hash of the whole tape per row) must be IDENTICAL.
# Run: mise exec -- scripts/test_wasm.sh
set -euo pipefail
cd "$(dirname "$0")/.."
. .land/tool/lib/ran.sh   # ran_case / ran_done / must_fail: the self-tests count what they executed and a refused tool is a failure (.land/tool/docs/ran-evidence.md)
if ! command -v node >/dev/null 2>&1; then
  if [ -n "${VBM_JSON_REQUIRE_NODE:-}" ]; then echo "test_wasm: node is required here (VBM_JSON_REQUIRE_NODE=1) and was not found" >&2; exit 1; fi
  echo "test_wasm: SKIPPED: node was not found on PATH (set VBM_JSON_REQUIRE_NODE=1 to require it)"; exit 0
fi
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
sysinc_flags() { printf '%s\n' -isystem "$1"; [ ! -d "$1/$(uname -m)-linux-gnu" ] || printf '%s\n' -isystem "$1/$(uname -m)-linux-gnu"; }
mapfile -t SYSFLAGS < <(sysinc_flags "${VBM_JSON_SYSINCLUDE:-/usr/include}")
[ -x .lake/build/bin/vbm-json-vectors ] && [ -f .lake/build/lib/libvbm_x2djson_LeanJson.a ] || lake build LeanJson:static vbm-json-vectors >/dev/null   # tier1 builds these once; concurrent lake runs in one tree are avoided
lib=.lake/build/lib/libvbm_x2djson_LeanJson.a; [ -f "$lib" ] || { echo "test_wasm: $lib was not built" >&2; exit 1; }
scripts/build_wasm.sh "$tmp/vbm.wasm"
v=${VBM_JSON_VECTORS:-}   # tier1 generates the vectors once and shares them; alone, the script generates its own
[ -n "$v" ] || { .lake/build/bin/vbm-json-vectors --n 4 --out "$tmp/v" >/dev/null; v="$tmp/v/vectors.jsonl"; }
run() { node tests/wasm/wasm_test.mjs "$1" "$2" "$tmp/w.$BASHPID.txt"; }   # each (concurrent) run has its own answer file; the main shell's is $tmp/w.$$.txt   # run WASM VECTORS
run "$tmp/vbm.wasm" "$v"; ran_case
leanc "${SYSFLAGS[@]}" -Wall -Wextra -Werror -I include -o "$tmp/abi_dump" tests/abi_dump.c abi/vbm_json.c "$lib" \
  || { echo "test_wasm: the native build needs the C library headers (see the preflight in scripts/test_abi.sh)" >&2; exit 1; }
"$tmp/abi_dump" "$v" > "$tmp/native.txt"
cmp "$tmp/native.txt" "$tmp/w.$$.txt" || { echo "test_wasm: the wasm build and the native ABI disagree (first differences):" >&2; diff "$tmp/native.txt" "$tmp/w.$$.txt" > "$tmp/d.txt" || true; sed -n 1,5p "$tmp/d.txt" >&2; exit 1; }; [ -s "$tmp/native.txt" ] || { echo "test_wasm: the native dump of the vectors is empty (nothing ran)" >&2; exit 1; }; ran_case
echo "test_wasm: wasm == native: $(wc -l < "$tmp/native.txt") rows, same return code and same tape (hash) on every row; module $(stat -c %s "$tmp/vbm.wasm") bytes"
# the bignum set (long and huge numbers, runtime has no bignum code: T10) must be in the vectors and pass
grep -c '"set":"bignum"' "$v" > "$tmp/nbig.txt"; [ "$(cat "$tmp/nbig.txt")" -ge 200 ] || { echo "test_wasm: the vectors lack the bignum set" >&2; exit 1; }
grep '"set":"bignum"' "$v" > "$tmp/big.jsonl"
export VBM_MIN_ROWS=200
run "$tmp/vbm.wasm" "$tmp/big.jsonl" >/dev/null; ran_case
ran_done test_wasm
echo "test_wasm: ok"
