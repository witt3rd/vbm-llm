#!/usr/bin/env bash
# Build and run the stage-1 prototype (docs/perf/simd-plan.md). RUN under `systemd-run --user --scope -p MemoryMax=12G -p MemorySwapMax=0 mise exec -- docs/perf/simd-proto/run.sh CORPUS_DIR`.
#   1. Stage1.lean -> C with Lean's emitter (Init only), 2. classify.c (scalar, SWAR, AVX2 variants) + Stage1.c linked together, 3. the differential tests (random bytes, UTF-8 sequences, the corpora),
#   4. the timing table (MB/s per variant, best of 3 windows of 0.4 s). Nothing here is a gate. Needs gcc or clang with AVX2 + PCLMUL + BMI on the build host; the Lean-emitted variant is built with leanc.
set -euo pipefail
corp=${1:?corpus dir}; ulimit -c 0
here=$(cd "$(dirname "$0")" && pwd); out=$(mktemp -d); trap 'rm -rf "$out"' EXIT
inc=(-isystem /usr/include); [ ! -d "/usr/include/$(uname -m)-linux-gnu" ] || inc+=(-isystem "/usr/include/$(uname -m)-linux-gnu")
timeout 300 lean -R "$here" -c "$out/Stage1.c" "$here/Stage1.lean"
L=$(dirname "$(dirname "$(command -v lean)")")   # the toolchain root (include/lean/lean.h)
cflags=(-O3 -mavx2 -mpclmul -mbmi -mbmi2 -mpopcnt -DWITH_LEAN -I "$L/include" -I "$here")
# the Lean-emitted code is built twice: by the toolchain's own clang (what the library uses) and by gcc; the harness (intrinsics) is always gcc (the bundled clang ships no intrinsics headers)
timeout 300 leanc -O3 -mavx2 -mbmi -mbmi2 -mpopcnt -include "$here/s1_shim.h" -c "${inc[@]}" -o "$out/Stage1.clang.o" "$out/Stage1.c"
timeout 300 gcc -O3 -DNDEBUG -mavx2 -mbmi -mbmi2 -mpopcnt -include "$here/s1_shim.h" -c -I "$L/include" -o "$out/Stage1.gcc.o" "$out/Stage1.c"
timeout 300 gcc "${cflags[@]}" -c -o "$out/classify.o" "$here/classify.c"
for cc in clang gcc; do timeout 300 leanc -o "$out/classify.$cc" "$out/classify.o" "$out/Stage1.$cc.o"; done
"$out/classify.clang" --utf8
"$out/classify.clang" --fuzz 200000
echo "== swar-Lean column: Stage1.c built by $(leanc --version | sed -n 1p)"; timeout 900 "$out/classify.clang" "$corp"/*.json
echo "== swar-Lean column: Stage1.c built by $(gcc --version | sed -n 1p)"; timeout 900 "$out/classify.gcc" "$corp"/*.json
