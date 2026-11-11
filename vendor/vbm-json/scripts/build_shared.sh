#!/usr/bin/env bash
# Build libvbm_json.so into the directory given: the library the bindings load. It is the FREESTANDING native library (scripts/build_native.sh: the generated C, abi/vbm_json.c and runtime/rt.c, no libc,
# no Lean prefix, no rpath: `nm -D -u` is empty), so a binding on another machine needs nothing but the file. Run: mise exec -- scripts/build_shared.sh OUTDIR
set -euo pipefail
cd "$(dirname "$0")/.."
out=${1:?usage: build_shared.sh OUTDIR}; mkdir -p "$out"
scripts/build_native.sh "$out" >/dev/null
syms=$(nm -D "$out/libvbm_json.so"); grep -q ' T vbm_json_parse$' <<<"$syms" || { echo "build_shared: libvbm_json.so does not export vbm_json_parse" >&2; exit 1; }
echo "build_shared: $out/libvbm_json.so"
