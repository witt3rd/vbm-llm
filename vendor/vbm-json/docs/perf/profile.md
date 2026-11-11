# vbm-json native parser: where the time goes (profile, no rewrite)

Phase 1 of the throughput gap: the scorecard measured the subject through the C ABI at 54.8 MB/s against Python's C `json` at 129.4 (sandbox). This is the profile that comes before any change. **Report only: nothing in `LeanJson/` was touched.**

Every number below is **local, on the reference machine** (22 cores, 62 GB, load ~0.4; subject commit `14eabaa`, Lean 4.35.0, `leanc -O2`, the library built as Tier 1 builds it). None is from a hosted run. Run under `systemd-run --user --scope -p MemoryMax=8G`, `ulimit -c 0`, with timeouts. Median of 5 windows of 0.6 s unless stated.

## Method (reproduce: `docs/perf/run.sh`, on a quiet machine, in a scratch clone)

`perf` and `valgrind` are not assumed to be installed, so the harness is self-contained:
- `docs/perf/prof.c` calls `vbm_json_parse` / `vbm_json_free` through the ABI (the shim, the generated C, the static Lean runtime with mimalloc), as the scorecard's bench does.
- **Where the time goes**: an in-process `SIGPROF` sampler (`ITIMER_PROF`, 1 kHz, ~8000 samples per corpus, instruction pointer, resolved against `nm -n` by `docs/perf/resolve.py`). Function granularity (inlined callees fold into their caller); the phase table is a fixed regex grouping of symbols, printed with the raw symbol list so it can be audited. The sampled binary carries 3 counters wrapped in with the linker's `--wrap` (2.3 to 3.6% of samples, shown as "instrumentation"); every MB/s figure comes from a build WITHOUT the wrap.
- **Allocations**: `--wrap` of `lean_alloc_object`, `lean_alloc_small_object_core`, `lean_dec_ref_cold`, counted over ONE parse.
- **Parse vs tape**: a scratch copy of `LeanJson/Tape.lean` gains one export (`prof_parse_only`: `parseFast`, then drop the Value). Full minus parse-only is the tape-building and Value-to-tape conversion cost. The repository has no such symbol (`run.sh` restores the file).
- **Shim**: the shim's own byte movement (alloc and copy the input into a ByteArray, alloc and copy the tape out, free) measured alone.
- Corpora (kept OUT of the repo; fetch commands and hashes below; synthetic ones come from `docs/perf/gen_corpus.py`, seed fixed):

| corpus | bytes | sha256 | source |
|---|---|---|---|
| twitter.json | 631515 | `30721e49...8dedf200` (full: `30721e496a8d73cfc50658923c34eb2c0fbe15ee6835005e43ee624d8dedf200`) | `simdjson/simdjson` `jsonexamples/twitter.json` (identical in `simdjson/simdjson-data`) |
| canada.json | 2251051 | `f83b3b354030d5dd58740c68ac4fecef64cb730a0d12a90362a7f23077f50d78` | `miloyip/nativejson-benchmark` `data/canada.json` (numbers, long digit strings) |
| citm_catalog.json | 1727204 | `a73e7a883f6ea8de113dff59702975e60119b4b58d451d518a929f31c92e2059` | `simdjson/simdjson` `jsonexamples/citm_catalog.json` (whitespace-heavy, nested) |
| small-objects.json | 2412355 | `12b0bc9c4c312449ce677f4fd03e6b693ba7f232f5b1332219bddc2b049af2c8` | `gen_corpus.py`: 60000 records `{"id","ok","v","n"}` |
| string-heavy.json | 2915939 | `e42cabee744c0288079e5eb037aefb069f1e3efda8dd15263fbe4081e5e73228` | `gen_corpus.py`: 20000 strings of 20..200 chars, 25% escapes, 25% multibyte UTF-8 |
| scorecard-corpus.json | 1033424 | `857fc854d687e2f3881fd7f3a700d58659902a5edb91e156484726f1204f202c` | the adapter's bench corpus (`random.Random(5)`, 4000 records), regenerated here |

(`curl -sfL https://raw.githubusercontent.com/simdjson/simdjson/master/jsonexamples/twitter.json`, same pattern for citm_catalog; `https://raw.githubusercontent.com/miloyip/nativejson-benchmark/master/data/canada.json`. Fetched 2026-11-04; verify the hash, the `master` branches can move.)

## Result 1: throughput, and how much is the tape (local)

| corpus | subject MB/s (full, through the ABI) | parseFast alone | tape + conversion share (1 - full/parse) | shim byte movement share | Python `json` | serde_json (`Value`) | simdjson (DOM) |
|---|---|---|---|---|---|---|---|
| twitter | 97.8 | 125.6 | 22% | 0.4% | 255.1 | 365.5 | 4686.6 |
| canada | 41.4 | 73.2 | 43% | 0.3% | 96.9 | 331.0 | 1439.5 |
| citm_catalog | 142.1 | 216.7 | 34% | 0.7% | 299.5 | 699.9 | 5037.6 |
| small-objects | 38.2 | 74.0 | 48% | 0.4% | 106.6 | 90.8 | 1401.4 |
| string-heavy | 80.1 | 100.5 | 20% | 0.5% | 295.3 | 331.0 | 3149.3 |
| scorecard corpus | 49.9 | 97.1 | 49% | n/m | 116.8 | 171.2 | 1577.2 |

The 49.9 against the scorecard's 54.8 is the same corpus on a different host. The comparators are measured here only to size the gap. The shim (copy in, copy out) is under 1% on every corpus: **the boundary is not the problem**, the Lean code behind it is.

## Result 2: allocations per document (local; one parse; lean_alloc_* calls)

| corpus | input bytes | small objects (`lean_alloc_small_object_core`) | large (`lean_alloc_object`) | bytes allocated | allocs per input byte | `lean_dec_ref_cold` calls |
|---|---|---|---|---|---|---|
| twitter | 631515 | 393392 | 2110 | 10.0 MB | 0.63 | 379063 |
| canada | 2251051 | 2751536 | 111127 | 86.7 MB | 1.27 | 444682 |
| citm_catalog | 1727204 | 534807 | 14393 | 15.8 MB | 0.32 | 384490 |
| small-objects | 2412355 | 2502358 | 120001 | 66.6 MB | 1.09 | 1800046 |
| string-heavy | 2915939 | 2695942 | 1 | 67.0 MB | 0.92 | 2675980 |
| scorecard corpus | 1033424 | 1069428 | 36001 | 30.7 MB | 1.07 | 532732 |

Attribution from the counts: string-heavy has 2.49 M text bytes and 2.70 M small allocations: **about one heap object per decoded character** (the generated `strLoop` calls `decodeCharA`, which returns `Option (Nat × Nat)`: `lean_alloc_ctor(0,2,0)` for the pair and `(1,1,0)` for the `some`, visible in `.lake/build/ir/LeanJson/Parse.c`, and the net count is about one per character, so reuse recovers part of it). canada has 111127 large allocations = one `ByteArray.mk` per number (111 k numbers) and 2.75 M small ones = ~25 per number: digit lists (a `Digit` list cons per digit, built reversed, `reverse`d, then `printInt` `map`s it, `toArray`s it).

## Result 3: the breakdown by phase (local; % of samples)

Phases are regex groups over symbols (`resolve.py`, bottom of its output). "Allocator" and "free side" are the Lean runtime's mimalloc and refcounting, so they are the cost of the allocations in Result 2, charged to whoever caused them in the next table.

| phase | twitter | canada | citm | small-obj | string-heavy | scorecard corpus | evidence (symbols) |
|---|---|---|---|---|---|---|---|
| free side: refcount dec, `lean_del`, `mi_free` | 32.2 | 12.5 | 17.5 | 19.4 | 39.6 | 18.2 | `lean_dec_ref_cold`, `mi_free`, `lean_del_core_other`, `lean_free_object` |
| allocator: `lean_alloc_*`, `mi_malloc`, page extend | 14.4 | 16.6 | 12.5 | 14.9 | 13.5 | 15.4 | `lean_alloc_small_object_core`, `mi_malloc`, `mi_page_free_list_extend` |
| parse: string chars (UTF-8 decode, escapes, `String.push`) | 21.1 | 0 | 8.1 | 3.9 | 25.8 | 4.5 | `strLoop`, `lean_string_push`, `Char.ofNat`, `push_unicode_scalar` |
| parse: whitespace | 4.4 | 0.8 | 17.5 | 1.9 | 0.7 | 1.8 | `skipWsA`, `isWs` (a call per byte: not inlined) |
| parse: number lexemes (digit lists) | 0.5 | 7.0 | 1.3 | 1.9 | 0 | 4.1 | `digitsAcc`, `parseNumA` |
| parse: driver (`run`, stack) | 3.5 | 1.9 | 5.1 | 6.4 | 1.9 | 3.9 | `LeanJson_run` |
| List.reverse / List.length | 2.5 | 28.6 | 9.3 | 11.8 | 1.0 | 16.5 | `List.reverseAux` (element lists, digit lists), `List.lengthTR` (`xs.length` in `encValue`, `toArray`) |
| tape: encode (`encValue`, `TapeBuf.node/leaf`, `ByteArray.push`) | 12.8 | 12.7 | 17.9 | 26.3 | 8.0 | 19.0 | `lean_byte_array_push` (8 pushes per u64 word), `TapeBuf_node`, `copy_slice` |
| tape: number printing (`printInt` map, `List.toArray`, `ByteArray.mk`) | 0.9 | 12.5 | 5.1 | 3.1 | 0 | 8.3 | `List.mapTR.loop at printInt`, `toArrayAux`, `lean_byte_array_mk` |
| outside the binary (libc `memcpy`/`memset`/`malloc`: the shim's copies, `mi` large) | 2.9 | 3.3 | 2.6 | 6.2 | 5.2 | 3.6 | unresolved addresses (shared libc) |
| instrumentation (`--wrap` counters) | 3.5 | 2.5 | 2.3 | 2.6 | 3.6 | 2.7 | `__wrap_*` |

What the phases hide, assembled from Results 1 and 2 (this is the table that matters):

| cost centre | share, where it is large | evidence |
|---|---|---|
| **per-character heap objects in string scanning** (alloc + free + `strLoop` + `String.push`) | up to ~67% of twitter, ~79% of string-heavy, ~30% of citm (sum of the string, alloc and free phases; some alloc/free belongs to other objects) | 1.08 objects per text byte on string-heavy; `lean_dec_ref_cold` 30% self there; 2.68 M `dec_ref_cold` calls for 2.49 M chars |
| **tape building and Value-to-tape conversion** (second traversal of the whole Value) | 22% twitter, 34% citm, 43% canada, 48% small-objects, 49% scorecard corpus | parse-only vs full MB/s; `lean_byte_array_push` is 5 to 13% self (every u64 is 8 pushes) |
| **numbers as digit lists** (build, reverse, print via map/toArray/mk, free) | ~48% of canada, ~28% of the scorecard corpus (digit/reverse/print phases, plus their share of alloc and free) | 25 small + 1 large object per number; `reverseAux` 18.6% self on canada |
| whitespace skipped one byte per call | 17% of citm (pretty-printed input) | `skipWsA` 10.2% + `isWs` 6.2% self |
| the reuse/reset checks (`lean_is_exclusive`) and inline refcount ops | cannot be separated at function granularity; bounded by the self time of `run`/`strLoop`/`encValue` (2 to 14%) | `Parse.c`: 14 `lean_is_exclusive`, 86 `lean_alloc_ctor`, 1088 `lean_dec*`, 66 `lean_inc*` sites. The refcount cost that shows is `lean_dec_ref_cold` (freeing), a consequence of the allocation count, not of the checks |
| UTF-8 validation proper | inside `strLoop` self time (12 to 14% on twitter/string-heavy, validation and decoding together; not separable at this granularity): small next to the allocation it drags along | `decodeUtf8A` is inlined into `strLoop` |
| the C shim | < 1% | shim byte movement alone: 0.3 to 0.7% of a parse |

## The three changes with the best expected gain (proposals; not implemented)

Gains are **estimates** by Amdahl on the shares above (local), not measurements.

### 1. Scan string runs without a heap object per character
`strLoop` becomes an index loop: advance over plain ASCII bytes (`0x20..0x7F` except `"` and `\`) and validated multi-byte sequences using the UTF-8 decision as a `Bool`/`Nat` result (no `Option (Nat × Nat)`), then append the whole run in one step (`String.fromUTF8` of `a.extract i j`, or one `push` per scalar only for escapes). Escapes keep the current path.
- **Expected gain**: string-heavy 80 to ~170-200 MB/s (2.1 to 2.5x), twitter 98 to ~170-190 (1.7 to 1.9x), citm ~1.3x, canada and small-objects ~1.0x (little text).
- **Proofs**: `parseFast_eq_parse` and every public statement stay as they are. Restated: the leaf lemmas of `LeanJsonProofs/FastLeaf.lean` about `strLoop` / `decodeCharA` (`decodeCharA_adv` and the equation `strLoop a i s` to the reference character loop): add a run lemma "a run of plain bytes appended in one step equals the per-character pushes", and a bridge from the run validator to `decodeUtf8A`. No spec change (`Value`, Grammar, policies untouched); the closure gate is unaffected (Init only: `String.fromUTF8` is Init).
- **Risk**: medium-low. Local to one function and its leaf proofs. The vector set already has the UTF-8 negative cases (overlongs, surrogates, truncations), generated from the reference.

### 2. Make the tape pass cheap without changing what it computes
`encValue` and friends: write each u64 word without 8 separate `ByteArray.push` (build the tape into a pre-sized `ByteArray` and set bytes in place, or push a word as one `copySlice` of a small constant buffer); take `xs.length` from the parser's count instead of a `List.lengthTR` per container; print numbers straight into the text buffer (`pushNumber`: no `List`, `map`, `toArray`, `ByteArray.mk`); keep the tape and text buffers unshared (the in-place path).
- **Expected gain**: tape + conversion is 20 to 49% of the time (Result 1); halving it gives ~1.1x (string-heavy) to ~1.3x (small-objects, scorecard corpus, canada 1.3 to 1.4x as number printing is 12.5% on top).
- **Proofs**: the tape layout theorem is not yet proved (`Tape.lean` says "the layout theorem is the next slice"), so no `proved` ledger claim is restated; what lands is a new statement `pushNumber b n = b ++ printNumber n` (small, in the Print proofs) and the same `encValue` equation the layout theorem will use. If the layout theorem is proved first, these are its lemmas.
- **Risk**: low. Behaviour is byte-identical (the vectors and `scripts/test_abi.sh` compare the tape with the reference's canonical bytes); no ABI change.

### 3. Fuse parsing and tape emission: never build the `Value` on the ABI path
`parseTapeFast` runs the same index-based loop as `run` but appends the node to the tape and the text region as it goes, validating a number by scanning (no digit lists) and writing its canonical lexeme (`e`/`E` kept as `e`, `+` dropped) from the input bytes; `Value` stays as the specification and `parseFast` stays as the oracle for `parse`.
- **Expected gain**: removes the Value allocation and free, the digit lists, the second traversal: small-objects 38 to ~110-130 MB/s, canada 41 to ~120-150, scorecard corpus 50 to ~120-140 (2.5 to 3.5x on number and small-object documents); string documents gain what change 1 gives. This is the change that closes most of the gap to Python's C `json` (116.8 on the scorecard corpus) and gets near serde_json's `Value` (171).
- **Proofs**: a new refinement theorem `parseTapeFast a = parseTape-of (parseFast a)` (status and tape words/text identical to `parseTape (parseFast a)`), proved by the same simulation as `run_sound`/`parseFast_eq_parse` over the new loop (a loop invariant that the tape built so far is `encValue` of the Values finished so far). `parseFast_eq_parse` is untouched; the ledger gets a new `proved` claim and the closure gate's entry point (`parseTape`) changes from `parseFast` to the fused function, so the baseline file and `scripts/closure-entries.txt` are restated. Depends on the layout theorem (change 2's statements) being proved first.
- **Risk**: high (the largest proof of the three: comparable in size to `Fast.lean` + `FastLeaf.lean`, ~1000 lines, which is over the 150-line production budget and needs a decomposition plan and a `Diff-Budget` trailer), and moderate engineering risk in the number normalisation. Do 1 and 2 first; they also shrink what 3 has to prove.

Suggested order: 2 (cheapest, unblocks 3), 1, then 3 behind a decomposition plan.

## Caveats
- Sampling is function-level at 1 kHz on one host, one run per corpus; the phase percentages are good to a point or two, the grouping is by symbol name.
- The counters wrap `lean_alloc_object` and `lean_alloc_small_object_core` only; an allocation through any other entry would not be counted, so the counts are lower bounds. The cost of the allocator shows up as `mi_malloc`/`mi_free`.
- The Lean runtime and mimalloc are linked statically here (as the scorecard's bench does); the `.so` build (`scripts/build_shared.sh`) uses the shared runtime and was not profiled.
- The scorecard's own figure (54.8 MB/s) was measured in its sandbox on another host (CPU-capped to 2 cpus); the 49.9 measured here on the same corpus is the same order, not the same number.
