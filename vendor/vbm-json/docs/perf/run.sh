#!/usr/bin/env bash
# The profiling run of docs/perf/profile.md. RUN ON a quiet machine, inside a SCRATCH CLONE of the library (it edits a copy of LeanJson/Tape.lean):
#   mise exec -- docs/perf/run.sh CORPUS_DIR OUT_DIR       under systemd-run --user --scope -p MemoryMax=8G, with timeouts.
# Builds docs/perf/prof.c against the static library (the shim, the generated C, the Lean runtime: -O3 as the library is) in two ways: `prof` (counters wrapped in with the linker's --wrap; used for count and sample)
# and `prof_plain` (no wrap; used for every MB/s). Runs per corpus: count (allocations of one parse), bench / shim / parseonly (MB/s), sample (where the time goes, docs/perf/resolve.py).
set -euo pipefail
corp=${1:?corpus dir}; out=${2:?out dir}; mkdir -p "$out"; ulimit -c 0
top=$(cd "$(dirname "$0")/../.." && pwd); cd "$top"
cp LeanJson/Tape.lean "$out/Tape.lean.orig"
cat >> LeanJson/Tape.lean <<'L'
namespace LeanJson
@[export prof_parse_only] def profParseOnly (a : ByteArray) : UInt64 := match parseFast a with | .error e => UInt64.ofNat e.code | .ok (.arr xs) => UInt64.ofNat xs.length | .ok _ => 1
end LeanJson
L
trap 'cp "$out/Tape.lean.orig" LeanJson/Tape.lean' EXIT
lake build LeanJson:static >/dev/null
inc=(-isystem /usr/include); [ ! -d "/usr/include/$(uname -m)-linux-gnu" ] || inc+=(-isystem "/usr/include/$(uname -m)-linux-gnu")
wrap=(-Wl,--wrap=lean_alloc_object -Wl,--wrap=lean_alloc_small_object_core -Wl,--wrap=lean_dec_ref_cold)
leanc -O2 -g -DCOUNT_WRAP "${inc[@]}" -I include "${wrap[@]}" -o "$out/prof" docs/perf/prof.c abi/vbm_json.c .lake/build/lib/libvbm_x2djson_LeanJson.a
leanc -O2 -g "${inc[@]}" -I include -o "$out/prof_plain" docs/perf/prof.c abi/vbm_json.c .lake/build/lib/libvbm_x2djson_LeanJson.a
for f in "$corp"/*.json; do
  n=$(basename "$f" .json); echo "== $n ($(stat -c %s "$f") bytes, sha256 $(sha256sum "$f" | cut -c1-16))"
  timeout 120 "$out/prof" "$f" count
  echo "MB/s full (median of 5 x 0.6 s): $(timeout 120 "$out/prof_plain" "$f" bench 3)   parseFast only: $(timeout 120 "$out/prof_plain" "$f" parseonly 3)   shim byte movement only: $(timeout 120 "$out/prof_plain" "$f" shim 3)"
  timeout 120 "$out/prof" "$f" sample 8 "$out/$n.samples"
  python3 docs/perf/resolve.py "$out/prof" "$out/$n.samples" 40
done
