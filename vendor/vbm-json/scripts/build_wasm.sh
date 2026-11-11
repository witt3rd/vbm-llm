#!/usr/bin/env bash
# Build the freestanding wasm32 module of the fast parser: the generated C of the LeanJson modules (lake's IR output), the unmodified ABI shim abi/vbm_json.c, and runtime/rt.c
# (the trusted freestanding runtime), compiled by the Lean toolchain's clang with --target=wasm32 -nostdlib and linked by its ld.lld (wasm flavour). No libc, no WASI, no imports.
# Env (self-tests only): VBM_RT_C replaces runtime/rt.c, VBM_LD_EXTRA adds linker flags.
# Usage: build_wasm.sh OUT.wasm [EXTRA.c...]   (run from anywhere; lake must have built LeanJson:static). Prints the size.
set -euo pipefail
. "$(dirname "$0")/lib-objcache.sh"
here=$(cd "$(dirname "$0")/.." && pwd); cd "$here"
out=${1:?usage: build_wasm.sh OUT.wasm}; shift
tc=$(dirname "$(dirname "$(readlink -f "$(command -v lean)")")")
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
cf=(--target=wasm32 -nostdlib -O2 -ffreestanding -nostdlibinc -mbulk-memory -DNDEBUG -I"$here/runtime/include" -I"$tc/include")
objs=()
for f in Value Policy Grammar Reference Print Parse Struct Tape PrintBytes PrintTape; do
  [ -f ".lake/build/ir/LeanJson/$f.c" ] || { echo "build_wasm: .lake/build/ir/LeanJson/$f.c missing: run lake build LeanJson:static first" >&2; exit 1; }
  cc "${cf[@]}" -c ".lake/build/ir/LeanJson/$f.c" -o "$tmp/$f.o"; objs+=("$tmp/$f.o")
done
# the bit-parallel parser (the export `vbm_json_parse_tape`): LeanJsonSimd and the pinned dependency VbmSimd, each with the dependency's trusted header (docs/trust-ledger.md T14) included first
hdr="$here/vendor/vbm-simd/include/vbm_simd.h"; [ -f "$hdr" ] || { echo "build_wasm: $hdr missing" >&2; exit 1; }
for f in LeanJsonSimd/Stage1 LeanJsonSimd/ParseSimd LeanJsonSimd/PrintSimd; do
  [ -f ".lake/build/ir/$f.c" ] || { echo "build_wasm: .lake/build/ir/$f.c missing: run lake build LeanJson:static first" >&2; exit 1; }
  cc "${cf[@]}" -include "$hdr" -c ".lake/build/ir/$f.c" -o "$tmp/s_$(basename "$f").o"; objs+=("$tmp/s_$(basename "$f").o")
done
for f in Spec Lanes Escape PrefixXor Shims Bytes Cursor Find Inset Append Classify; do
  [ -f "vendor/vbm-simd/.lake/build/ir/VbmSimd/$f.c" ] || { echo "build_wasm: the VbmSimd C of $f is missing" >&2; exit 1; }
  cc "${cf[@]}" -include "$hdr" -c "vendor/vbm-simd/.lake/build/ir/VbmSimd/$f.c" -o "$tmp/v_$f.o"; objs+=("$tmp/v_$f.o")
done
cc "${cf[@]}" -Wall -Wextra -Werror -c abi/vbm_json.c -o "$tmp/abi.o"; objs+=("$tmp/abi.o")
cc "${cf[@]}" -Wall -Wextra -Werror -c "${VBM_RT_C:-runtime/rt.c}" -o "$tmp/rt.o"; objs+=("$tmp/rt.o")
for x in "$@"; do cc "${cf[@]}" -c "$x" -o "$tmp/x$(basename "$x").o"; objs+=("$tmp/x$(basename "$x").o"); done
ld.lld -flavor wasm -error-limit=0 --no-entry --gc-sections --export-memory -z stack-size=1048576 --max-memory=2147483648 \
  --export=vbm_json_parse --export=vbm_json_free --export=vbm_json_print_tape --export=vbm_json_escape_string --export=vbm_json_bytes_free --export=vbm_json_wasm_alloc --export=vbm_json_wasm_dealloc --export=vbm_json_wasm_live ${VBM_LD_EXTRA:-} -o "$out" "${objs[@]}"
echo "build_wasm: $out $(stat -c %s "$out") bytes"
