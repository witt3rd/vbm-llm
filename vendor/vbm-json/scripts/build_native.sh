#!/usr/bin/env bash
# Build the FREESTANDING native library of the fast parser: the generated C of the LeanJson modules (lake's IR output), the ABI shim abi/vbm_json.c and runtime/rt.c (the same trusted runtime the wasm
# build links), compiled with the Lean toolchain's clang -ffreestanding -nostdlib -nostdlibinc (the stub headers of runtime/include, never the system's) and combined into ONE relocatable object whose only
# global symbols are the ABI's (vbm_json_parse, vbm_json_free): the runtime's own malloc/memcpy/... become local, so they cannot clash with, or be mistaken for, a libc. No libc symbol is referenced:
# `nm -u` of the result is EMPTY, and the script fails otherwise. Outputs in OUTDIR: libvbm_json.a (static), libvbm_json.so (links with no libc and no Lean prefix), vbm_json.o.
# Env (self-tests only): VBM_RT_C replaces runtime/rt.c; VBM_EXTRA_C adds C files (compiled like the rest), VBM_KEEP adds global symbols to keep (to prove the nm check can fail).
# Usage: build_native.sh OUTDIR [--no-so]   (run from anywhere; lake must have built LeanJson:static first, this script does it). Prints the sizes.
set -euo pipefail
. "$(dirname "$0")/lib-objcache.sh"
here=$(cd "$(dirname "$0")/.." && pwd); cd "$here"
out=${1:?usage: build_native.sh OUTDIR}; mkdir -p "$out"
[ -f .lake/build/lib/libvbm_x2djson_LeanJson.a ] || lake build LeanJson:static >/dev/null
tc=$(dirname "$(dirname "$(readlink -f "$(command -v lean)")")")
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
cf=(-ffreestanding -nostdlib -nostdlibinc -fno-stack-protector -fno-builtin -ffunction-sections -fdata-sections -O2 -fPIC -DNDEBUG -I"$here/runtime/include" -I"$tc/include")
# aarch64: clang defaults to "outline atomics" (calls to __aarch64_cas4_acq_rel, __aarch64_ldadd4_relax: libgcc/compiler-rt helpers a freestanding build does not have); inline the atomics instead.
arch=(); [ "$(uname -m)" != aarch64 ] || arch=(-mno-outline-atomics)
cf+=("${arch[@]}")
objs=()
for f in Value Policy Grammar Reference Print Parse Struct Tape PrintBytes PrintTape; do
  [ -f ".lake/build/ir/LeanJson/$f.c" ] || { echo "build_native: .lake/build/ir/LeanJson/$f.c missing" >&2; exit 1; }
  cc "${cf[@]}" -c ".lake/build/ir/LeanJson/$f.c" -o "$tmp/$f.o"; objs+=("$tmp/$f.o")
done
# the bit-parallel parser (the export `vbm_json_parse_tape`): LeanJsonSimd and the pinned dependency VbmSimd, each with the dependency's trusted header (docs/trust-ledger.md T14) included first
hdr="$here/vendor/vbm-simd/include/vbm_simd.h"; [ -f "$hdr" ] || { echo "build_native: $hdr missing" >&2; exit 1; }
for f in LeanJsonSimd/Stage1 LeanJsonSimd/ParseSimd LeanJsonSimd/PrintSimd; do
  [ -f ".lake/build/ir/$f.c" ] || { echo "build_native: .lake/build/ir/$f.c missing" >&2; exit 1; }
  cc "${cf[@]}" -include "$hdr" -c ".lake/build/ir/$f.c" -o "$tmp/s_$(basename "$f").o"; objs+=("$tmp/s_$(basename "$f").o")
done
for f in Spec Lanes Escape PrefixXor Shims Bytes Cursor Find Inset Append Classify; do
  [ -f "vendor/vbm-simd/.lake/build/ir/VbmSimd/$f.c" ] || { echo "build_native: the VbmSimd C of $f is missing" >&2; exit 1; }
  cc "${cf[@]}" -include "$hdr" -c "vendor/vbm-simd/.lake/build/ir/VbmSimd/$f.c" -o "$tmp/v_$f.o"; objs+=("$tmp/v_$f.o")
done
# the shim is compiled as the scorecard compiles it: freestanding, with the Lean include directory only (lean_mini.h stands in for lean.h); the runtime with the stub headers
cc "${arch[@]}" -ffreestanding -nostdlib -nostdinc -ffunction-sections -fdata-sections -O2 -fPIC -DNDEBUG -Wall -Wextra -Werror -I include -I "$tc/include" -c abi/vbm_json.c -o "$tmp/abi.o"; objs+=("$tmp/abi.o")
cc "${cf[@]}" -Wall -Wextra -Werror -c "${VBM_RT_C:-runtime/rt.c}" -o "$tmp/rt.o"; objs+=("$tmp/rt.o")
for x in ${VBM_EXTRA_C:-}; do cc "${cf[@]}" -c "$x" -o "$tmp/x$(basename "$x").o"; objs+=("$tmp/x$(basename "$x").o"); done
keep=(vbm_json_parse vbm_json_free vbm_json_print_tape vbm_json_escape_string vbm_json_bytes_free ${VBM_KEEP:-})
und_args=(); for k in "${keep[@]}"; do und_args+=(--undefined="$k"); done
ld.lld -r --gc-sections "${und_args[@]}" -o "$tmp/all.o" "${objs[@]}"
printf '%s\n' "${keep[@]}" > "$tmp/keep.txt"
objcopy --keep-global-symbols="$tmp/keep.txt" "$tmp/all.o" "$out/vbm_json.o"
rm -f "$out/libvbm_json.a"; llvm-ar rcs "$out/libvbm_json.a" "$out/vbm_json.o"
und=$(nm -u "$out/vbm_json.o" | sed 's/^ *U //')
if [ -n "$und" ]; then echo "build_native: the library references symbols it does not define (a libc leak): $(echo $und)" >&2; exit 1; fi
if [ "${2:-}" != --no-so ]; then
  ld.lld -shared -z noexecstack --gc-sections --no-undefined -o "$out/libvbm_json.so" "$out/vbm_json.o"
  und=$(nm -D -u "$out/libvbm_json.so" | sed 's/^ *U //')
  if [ -n "$und" ]; then echo "build_native: libvbm_json.so imports symbols (a libc leak): $(echo $und)" >&2; exit 1; fi
fi
echo "build_native: $out: libvbm_json.a $(stat -c %s "$out/libvbm_json.a") bytes, vbm_json.o $(stat -c %s "$out/vbm_json.o") bytes, nm -u: none"
[ -f "$out/libvbm_json.so" ] && echo "build_native: libvbm_json.so $(stat -c %s "$out/libvbm_json.so") bytes"
true
