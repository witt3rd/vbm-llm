#!/usr/bin/env bash
# The before/after measurement of the perf slices (docs/perf/profile.md method, minus the sampler). RUN ON a quiet machine, in a scratch copy of the tree:
#   mise exec -- docs/perf/bench.sh CORPUS_DIR     under systemd-run --user --scope -p MemoryMax=8G, ulimit -c 0 (set here), with timeouts.
# Builds docs/perf/prof.c against the static library twice (`prof` with the allocation counters, `prof_plain` without) and prints, per corpus: allocations of ONE parse and
# MB/s through the C ABI (median of 5 windows of 0.6 s; the best of REPS=2 runs, to shed a noisy window). Nothing here is a gate.
set -euo pipefail
corp=${1:?corpus dir}; ulimit -c 0
top=$(cd "$(dirname "$0")/../.." && pwd); cd "$top"; out=$(mktemp -d); trap 'rm -rf "$out"' EXIT
lake build LeanJson:static >/dev/null
inc=(-isystem /usr/include); [ ! -d "/usr/include/$(uname -m)-linux-gnu" ] || inc+=(-isystem "/usr/include/$(uname -m)-linux-gnu")
wrap=(-Wl,--wrap=lean_alloc_object -Wl,--wrap=lean_alloc_small_object_core -Wl,--wrap=lean_dec_ref_cold)
leanc -O2 -DCOUNT_WRAP "${inc[@]}" -I include "${wrap[@]}" -o "$out/prof" docs/perf/prof.c abi/vbm_json.c .lake/build/lib/libvbm_x2djson_LeanJson.a
leanc -O2 "${inc[@]}" -I include -o "$out/prof_plain" docs/perf/prof.c abi/vbm_json.c .lake/build/lib/libvbm_x2djson_LeanJson.a
printf '%-22s %10s %12s %10s %12s\n' corpus bytes small_allocs large_allocs MB/s
for f in "$corp"/*.json; do
  n=$(basename "$f" .json); c=$(timeout 120 "$out/prof" "$f" count)
  small=$(sed -n 's/.*lean_alloc_small_object_core \([0-9]*\) .*/\1/p' <<<"$c"); large=$(sed -n 's/.*lean_alloc_object \([0-9]*\) .*/\1/p' <<<"$c")
  best=0; for _ in 1 2; do m=$(timeout 120 "$out/prof_plain" "$f" bench 3); best=$(awk -v a="$best" -v b="$m" 'BEGIN{print (b>a)?b:a}'); done
  printf '%-22s %10s %12s %10s %12s\n' "$n" "$(stat -c %s "$f")" "$small" "$large" "$best"
done
