#!/usr/bin/env bash
# Build and run the end-to-end C prototype (e2e.c) against the library's own tape. RUN under `systemd-run --user --scope -p MemoryMax=12G -p MemorySwapMax=0 mise exec -- docs/perf/simd-proto/run_e2e.sh CORPUS_DIR`
# (builds the static library first). Columns (MB/s of input, best of 3 windows of 0.4 s): stage 1 alone with AVX2 / with SWAR, the flatten alone, stage 2 alone, the whole pipeline (with the result copy) with each stage 1.
set -euo pipefail
corp=${1:?corpus dir}; ulimit -c 0
top=$(cd "$(dirname "$0")/../../.." && pwd); here=$top/docs/perf/simd-proto; cd "$top"; out=$(mktemp -d); trap 'rm -rf "$out"' EXIT
lake build LeanJson:static >/dev/null
inc=(-isystem /usr/include); [ ! -d "/usr/include/$(uname -m)-linux-gnu" ] || inc+=(-isystem "/usr/include/$(uname -m)-linux-gnu")
L=$(dirname "$(dirname "$(command -v lean)")")
# two builds of the same source: (a) gcc -O3 with AVX2 enabled (the C compiler auto-vectorizes the SWAR code), (b) vectorization off: the portable-SWAR numbers are the (b) ones
gcc -O3 -mavx2 -mpclmul -mbmi -mbmi2 -mpopcnt -I "$L/include" -I include -c -o "$out/e2e.o" "$here/e2e.c"
gcc -O3 -fno-tree-vectorize -fno-tree-slp-vectorize -mavx2 -mpclmul -mbmi -mbmi2 -mpopcnt -I "$L/include" -I include -c -o "$out/e2e_novec.o" "$here/e2e.c"
leanc -O2 "${inc[@]}" -I include -c -o "$out/shim.o" abi/vbm_json.c
leanc -o "$out/e2e" "$out/e2e.o" "$out/shim.o" .lake/build/lib/libvbm_x2djson_LeanJson.a
leanc -o "$out/e2e_novec" "$out/e2e_novec.o" "$out/shim.o" .lake/build/lib/libvbm_x2djson_LeanJson.a
echo "== build (a): C compiler may vectorize (s1-swar / pipe-swar are auto-vectorized SWAR)"; timeout 900 "$out/e2e" "$corp"/*.json
echo "== build (b): vectorization off (s1-swar / pipe-swar are portable scalar SWAR)"; timeout 900 "$out/e2e_novec" "$corp"/*.json
