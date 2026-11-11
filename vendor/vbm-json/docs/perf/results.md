# Perf slices: measured results (before / after, per slice)

Method: `docs/perf/bench.sh` (the profile's harness: the C ABI through `docs/perf/prof.c`, static library, `leanc -O2`; allocations of ONE parse via the linker's `--wrap`; MB/s = median of 5 windows of 0.6 s, best of 2 runs). **Every number is local, on the reference machine** (22 cores), run under `systemd-run --user --scope -p MemoryMax=8G`, `ulimit -c 0`; the machine is shared, so repeated runs of the same build differ by about 5%. None is from a hosted run. Corpora and their sha256: `docs/perf/profile.md` (the scorecard corpus is the adapter's `random.Random(5)` generator, 4000 records, regenerated here; hash matches). Order (maintainer, 2026-11-04): change 1 (string runs), then change 2 (cheaper tape pass); change 3 is `docs/perf/fuse-plan.md` only.

## Slice 1: plain ASCII bytes in a string are pushed without a decoder call (`strLoop`)

`strLoop` tests `plainAscii` (`0x20 ≤ x < 0x80`, not `"` (tested before), not `\`) and pushes `Char.ofNat x` at once; every other byte goes through `decodeCharA` as before. No heap object per ASCII character (the `Option (Nat × Nat)` of `decodeCharA` is gone from the hot path). 7 production lines (`LeanJson/Parse.lean`).
Proofs: `decodeCharA_plain` (a plain ASCII byte is `decodeCharA`'s answer `(x, i+1)`), `strLoop_step` (one decoded character, shared by both branches), `strLoop_eq` and `strLoop_adv` re-proved with the extra case; `parseFast_eq_parse` and every public statement unchanged, no new axioms, ledger and closure baselines unchanged (specified share 100%).
A 3-byte (CJK) fast path was also built and proved, and measured: twitter small allocations 122k to 90k but MB/s within the noise (137 to 140), string-heavy not better. Not landed (more code and proof for no measured gain).

| corpus | bytes | MB/s before | MB/s after | small allocs before | small allocs after |
|---|---|---|---|---|---|
| twitter | 631515 | 98.7 | 137.3 | 393392 | 122109 |
| canada | 2251051 | 40.9 | 42.5 | 2751536 | 2751446 |
| citm_catalog | 1727204 | 140.5 | 164.5 | 534807 | 313778 |
| small-objects | 2412355 | 37.6 | 42.5 | 2502358 | 2142358 |
| string-heavy | 2915939 | 80.9 | 157.1 | 2695942 | 300004 |
| scorecard corpus | 1033424 | 49.0 | 54.3 | 1069428 | 884538 |

(large allocations, one per number or tape, unchanged: 111127 / 14393 / 120001 / 1 / 2110 / 36001.) What is left in strings: one `String.push` (a runtime call) per character, and the decoder tuple for non-ASCII characters and escapes.

## Slice 2: the tape pass (`LeanJson/Tape.lean`)

What changed (about 45 production lines): `pushWordFast` (one append of 8 zero bytes, then 8 in-place `set!` stores, instead of 8 `ByteArray.push` runtime calls per u64 word); `pushNumber` (the number lexeme is written straight into the text region: no `List` of bytes, no `map`, no `List.toArray`, no `ByteArray.mk`, so no per-number large allocation); `TapeBuf.num` (reads the buffers apart first so both stay unshared and the in-place path is kept). `pushWord` and `printNumber` stay as the DEFINITIONS of the layout.
Proofs (`LeanJsonProofs/Tape.lean`, new, no new axioms): `pushWordFast_eq : pushWordFast b w = pushWord b w`, `pushDigits_eq`, `pushNumber_eq : pushNumber b n = b ++ ⟨(printNumber n).toArray⟩`, `TapeBuf.num_eq : s.num n = s.leaf kindNum ⟨(printNumber n).toArray⟩`. The layout theorem is still the later slice (ledger `tape-encode-decode` stays open); these are its lemmas. `xs.length` per container was left as it is (cheap next to the rest).

Before = main after slice 1 (`70b9a78`) on the same run conditions; after = the slice 2 tree. Local, `docs/perf/bench.sh`.

| corpus | bytes | MB/s before | MB/s after | small allocs before | small allocs after | large allocs before | large allocs after |
|---|---|---|---|---|---|---|---|
| twitter | 631515 | 131.7 | 144.1 | 122109 | 121642 | 2111 | 2 |
| canada | 2251051 | 41.0 | 51.3 | 2751446 | 2584803 | 111128 | 2 |
| citm_catalog | 1727204 | 157.4 | 189.4 | 313778 | 313778 | 14394 | 2 |
| small-objects | 2412355 | 41.2 | 46.1 | 2142358 | 2142285 | 120002 | 2 |
| string-heavy | 2915939 | 154.6 | 162.0 | 300004 | 300004 | 2 | 2 |
| scorecard corpus | 1033424 | 52.5 | 63.7 | 884538 | 860500 | 36002 | 2 |

(A "large" allocation is `lean_alloc_object`: before, one `ByteArray.mk` per number and per string text; after, only the tape and the text region. The 1-or-2 difference between the slice 1 table and this one is the shim's output buffers after the freestanding-ABI landing.) What is left: canada and small-objects are bound by the `Value` itself (digit lists, one object per node, the reversed element lists), which only the fused parse (`docs/perf/fuse-plan.md`) removes.

## Slice 3 (preview, F4): the fused loop, measured before it is proved or exported

`parseTapeFast` (`LeanJson/Tape.lean`) measured in a scratch copy whose `vbm_json_parse_tape` export points at it; the base is the same tree with the export on `parseTape` (main at F4), run back to back in the same session. **Local** (22 cores), `docs/perf/bench.sh` under `systemd-run --user --scope -p MemoryMax=8G`, `ulimit -c 0`, `ulimit -s 8192`, one run each (the machine is shared: about 5% noise). The same tree passes the differential (`vbm-json-vectors --check --corpus`) on all six corpora: the fused bytes are `parseTape`'s bytes. Nothing in the repository exports the fused path yet (that is F6, after `parseTapeFast_eq`).

| corpus | bytes | MB/s base | MB/s fused | speedup | small allocs base | small allocs fused |
|---|---|---|---|---|---|---|
| twitter | 631515 | 142.7 | 209.8 | 1.47x | 121642 | 76421 |
| canada | 2251051 | 54.0 | 183.2 | 3.39x | 2584803 | 167200 |
| citm_catalog | 1727204 | 195.0 | 280.3 | 1.44x | 313778 | 81729 |
| small-objects | 2412355 | 46.9 | 86.1 | 1.84x | 2142285 | 780002 |
| string-heavy | 2915939 | 165.2 | 293.6 | 1.78x | 300004 | 180002 |
| scorecard corpus | 1033424 | 63.7 | 138.3 | 2.17x | 860500 | 180002 |

The estimate in `docs/perf/fuse-plan.md` (small-objects 110 to 130, canada 120 to 150, scorecard corpus 120 to 140) is met on canada (183) and the scorecard corpus (138) and missed on small-objects (86: 13 small allocations per record remain, the `Option (TapeBuf x Nat)` of each string and key node and the `FStack` cells).

## Slice 3 (landed, F6): the export is the fused parser (`parseTapeFast_eq` proved)

The measurement of the real export (main at `127abfa`), **local, on the reference machine**, `docs/perf/bench.sh` under `systemd-run --user --scope -p MemoryMax=12G -p MemorySwapMax=0`, `ulimit -c 0`, `ulimit -s 8192`, one run; the base column is the slice 2 table above (same corpora, same method, an earlier session; the machine is shared, about 5 to 10% noise: the preview in the section before measured 138.3 on the scorecard corpus, this run 120.9).

| corpus | MB/s slice 2 | MB/s fused (export) | speedup | small allocs slice 2 | small allocs fused | large allocs |
|---|---|---|---|---|---|---|
| twitter | 144.1 | 201.8 | 1.40x | 121642 | 76421 | 2 |
| canada | 51.3 | 158.9 | 3.10x | 2584803 | 167200 | 2 |
| citm_catalog | 189.4 | 271.4 | 1.43x | 313778 | 81729 | 2 |
| small-objects | 46.1 | 78.5 | 1.70x | 2142285 | 780002 | 2 |
| string-heavy | 162.0 | 274.9 | 1.70x | 300004 | 180002 | 2 |
| scorecard corpus | 63.7 | 120.9 | 1.90x | 860500 | 180002 | 2 |

Against the estimate of `docs/perf/fuse-plan.md` (small-objects 110 to 130, canada 120 to 150, scorecard corpus 120 to 140): met on canada and the scorecard corpus, missed on small-objects (78 to 86; 13 small allocations per record remain: the `Option (TapeBuf x Nat)` of each string and key node, the `FStack` cells). The efficiency floor of about 85 MB/s on the scorecard corpus is cleared (120.9 here, 138.3 in the preview run). Left: the `tapeOk` copy of tape and text into the result (two memcpy), the per-byte `ByteArray.push` of plain string bytes (a `copySlice` of the plain run would replace it), the `Option` tuples of string nodes.

Kernel re-check of the proof set, **local, on the reference machine**, capped, one run: `leanchecker --fresh LeanJson` 36.8 s, `LeanJsonProofs` 40.0 s, `leanexport` 12.5 s (364.6 MB): 89.3 s; the same three on `0c1e995`, before F0: 37.2 + 39.3 + 12.3 = 88.8 s (361.1 MB). The 1700 added proof lines did not lengthen the kernel re-check measurably.

## Slice 4 (S8 and the first tuning slice): the export is the index-driven parser, `runW`

`vbm_json_parse_tape` is now `LeanJson.parseTapeSimd` (stage 1, then `runW`, the scalar `parseTapeFast` as the fallback; `parseTapeSimd_eq` proved, `LeanJsonProofs/ParseW.lean`). `runW` is `runI` (the index-driven loop of S5 to S7, measured slower than the scalar parser in `simd-results.md`) with its costs removed, one by one, each measured:

| cost found in the `runI` profile (sampler, `docs/perf/resolve.py`) | class | what `runW` does instead |
|---|---|---|
| the tape words: `pushWordFast` 19%, `copy_slice` 7%, `setWord` 3% of small-objects | **Lean emitter / runtime call per word**: an append call and eight checked byte stores for every 8 bytes | `tape` is a byte array longer than what is written; a node is two `st64` (inline 8-byte stores); 4096 zero bytes are appended when room is needed (the zeros land in cache that the stores use at once) |
| `nextSet` + `nextSetGo` 16 to 34% | **Nat arithmetic in the hot path**: `lean_nat_mul` re-checks the product by a division, `Nat` `<<<` goes to GMP (`__gmpz_mul_2exp` showed up at 6% when tried), and a call per skip | `skipF`: the word holding `j` is read in line with a `Nat` shift and `USize` arithmetic; the generic walk only when that word has no bit |
| `Option (TapeBuf × Nat)`, `TapeBuf` rebuilt per token | **boxing** | tape, word count and text are three loop arguments; no pair is built |
| one `String`/`ByteArray` push per byte of a plain string, one list-free but per-byte number copy | **per-byte runtime calls** | a plain ASCII string and a number without `E` or `+` are one `copySlice` from the input |
| growing the tape by doubling and zero-filling a cold array (rounds 1 and 2 of the experiment) | **memory traffic**: first-touch page faults and a copy of everything written so far; +25% when removed by growing in cache-sized zero chunks | 4096-byte chunks into the array's own doubling capacity |
| `isWs`, `isOp` called, not inlined | call overhead | `@[inline]` |

Measured end to end through the C ABI (`docs/perf/bench.sh`'s harness `prof.c`, `leanc -O2`, static library, the shim's input copy in and tape copy out included; A and B built from the two trees and run alternately, best of 3 windows of 2 s per cell). **Local, host x (22 cores), load 2.0 to 2.1 before and after (not below 2: reported, not waited for), a shared machine: about 5% noise.** A = main at `origin/fm/vbm-json-simd2` (the export is the scalar `parseTapeFast`), B = this slice:

| corpus | bytes | MB/s A (scalar) | MB/s B (`parseTapeSimd`) | B / A |
|---|---|---|---|---|
| canada | 2251051 | 174.3 | 224.9 | 1.29 |
| citm_catalog | 1727204 | 274.0 | 511.1 | 1.87 |
| scorecard corpus | 1033424 | 133.3 | 198.3 | 1.49 |
| small-objects | 2412355 | 81.7 | 127.4 | 1.56 |
| string-heavy | 2915939 | 277.8 | 276.9 | 1.00 |
| twitter | 631515 | 213.8 | 264.5 | 1.24 |

The comparators on the same host, in the same hour (the prebuilt `serde_json` `Value` and `simdjson` DOM of the scorecard, `comp/run.sh`): serde_json 320.8 / 644.8 / 164.8 / 87.6 / 317.8 / 348.1 and simdjson 1422.2 / 4946.4 / 1437.3 / 1383.1 / 3006.7 / 4096.1 on the same six rows in the same order. The scorecard corpus is at 1.20x of serde_json (it was 0.81x). Stage 1 alone runs at 1.1 to 1.4 GB/s here (`stage1` mode of the scratch harness), 15 to 22% of the time of the parse; the rest of the time is the loop.

What is left (the slices after this one): string-heavy is flat because every string with an escape or a non-ASCII byte takes the byte-at-a-time `strBytes`; the digit run of a number is scanned a byte at a time and the scan allocates its `Option`; the literals are matched by `litA` over a list; each open container allocates an `FStack` cell; the result is copied twice more at the end (`finishW`, then the shim).

## Slice 5 (S10a): word-parallel leaves: the plain run of a string and the digit run of a number

`plainOff` finds the end of a run of plain string bytes eight at a time (`ld64`, the byte-lane test `plainBad`, `ctz` of the first flagged lane) and `strBytesW` copies the run with one `copySlice`, then handles the one byte that stopped it (a quote, a backslash, a non-ASCII byte) as `strBytes` does and continues. `scanDigitsW` does the same for the digits of a number (`ndFlags`), so a number is scanned in one or two words and `scanNumW` (`scanNum` with it) does not call a byte loop. Every addition in the two lane tests is carry-free (a masked operand and a constant below `0x80`), so each lane is a function of its own byte; the proof (`LeanJsonProofs/Swar.lean`) shows that for the three byte-wise operations and for `+` under the no-carry condition (`ln_add`: the sum of two numbers whose base-256 digits add without carry has the sums as digits), then the lane statements are 256 cases each, and `first_flag` ties `ctz` to the first flagged lane. `strBytesW_eq`, `scanDigitsW_eq` and `scanNumW_eq` are the equations against the leaves they replace; `parseTapeSimd_eq` and `runW_sound` are unchanged in statement.

Through the C ABI, as slice 4 (the harness is `docs/perf/prof.c`; A, B, C built from three trees and run alternately, best of 3 windows of 2 s per cell). **Local, host x, load 2.4 before and after (above 2: reported, not waited for), about 5 to 10% noise.** A = the scalar export (slice 3), B = slice 4, C = this slice:

| corpus | bytes | A scalar `parseTapeFast` | B `runW` (slice 4) | C word-parallel leaves | C / B |
|---|---|---|---|---|---|
| canada | 2251051 | 149.8 | 183.5 | 209.5 | 1.14 |
| citm_catalog | 1727204 | 269.4 | 474.3 | 510.3 | 1.08 |
| scorecard corpus | 1033424 | 126.7 | 197.0 | 215.3 | 1.09 |
| small-objects | 2412355 | 81.2 | 124.5 | 126.7 | 1.02 |
| string-heavy | 2915939 | 269.1 | 258.6 | 317.8 | 1.23 |
| twitter | 631515 | 211.0 | 256.9 | 250.0 | 0.97 |

Through the Lean entry point (no shim copies, same machine, load 1.5) the same change measured 1.12 / 1.07 / 1.08 / 1.03 / 1.33 / 1.01: the gain is where the bytes are (string-heavy, canada), and twitter, whose strings are short and mostly non-ASCII, is flat within the noise. Measured and not landed: marking `scanNum` `@[inline]` (the `Option Nat` it returns allocates; removing the allocation was within the noise).

(One thing the slice taught: `plainOff` first added its eight with a non-tail call (`8 + plainOff ...`), which is a stack frame per eight bytes; the WebAssembly test (row 43667 of the `bignum` set, a 100000-digit object key) trapped on the 1 MiB stack. The accumulator form is a loop. The native build has a larger stack and passed: the class is **a recursion that is not a loop** in emitted code, and Lean does not warn; `scanDigitsW`, `strBytesW`, `plainRun`, `lexRun`, `runW` are all tail calls.)

## Slice 6 (S10b): the number lexeme is checked for `E` and `+` eight bytes at a time (`lexOk`)

After slice 5 the sampler (`docs/perf/prof.c sample`, `resolve.py`) shows `lexRun`, the byte-at-a-time check that a number's lexeme has no `E` and no `+` (so that it can be copied from the input in one `copySlice`), at 8.2% of the scorecard corpus and 16.5% of canada. `lexOk` tests eight bytes at a time (`lexBad`: two `eqLanes`), the last partial word with its lanes past the end of the lexeme cleared (`(1 <<< 8n) - 1`); `lexOk_eq : lexOk a p e = lexRun a p e` for `e ≤ a.size` (`LeanJsonProofs/Swar.lean`: the lane statement, "a word is zero when its lanes are", the mask's lanes, then the same characterisation as for `plainRun`).

Through the C ABI as before (A = slice 5, B = this slice; best of 3 windows of 2 s; local, host x, load 2.0 before and 1.8 after, about 5% noise):

| corpus | bytes | MB/s A (slice 5) | MB/s B (`lexOk`) | B / A |
|---|---|---|---|---|
| canada | 2251051 | 247.2 | 286.3 | 1.16 |
| citm_catalog | 1727204 | 516.0 | 516.7 | 1.00 |
| scorecard corpus | 1033424 | 218.7 | 236.5 | 1.08 |
| small-objects | 2412355 | 134.4 | 130.7 | 0.97 |
| string-heavy | 2915939 | 368.9 | 354.6 | 0.96 |
| twitter | 631515 | 252.0 | 260.8 | 1.04 |

The three corpora with few numbers (citm_catalog, string-heavy, small-objects) do not run the changed code to a measurable degree; their differences are the noise of the machine (the Lean entry point, no shim, shows 0.97 to 1.01 on them).

## Summary of the S8 to S10b series (final table, same session, same method)

Through the C ABI (`docs/perf/prof.c`, `leanc -O2`, static library, shim copies included), four trees built and run alternately, best of 4 windows of 2 s per cell. **Local, host x (22 cores), load 1.6 before and 3.2 after (a shared machine, not quiet at the end: about 5 to 10% noise).** T1 = the scalar export (`origin/fm/vbm-json-simd2`), T2 = S8 (`runW`, slice 4), T3 = S10a and S10b (slices 5 and 6, `main` at `8b34bbe`). The comparators are the scorecard's prebuilt binaries on the same host (`comp/run.sh`, best of 3, load 2.1 to 2.7):

| corpus | bytes | T1 scalar | T2 S8 | T3 final | T3 / T1 | serde_json (`Value`) | T3 / serde_json | simdjson (DOM) |
|---|---|---|---|---|---|---|---|---|
| canada | 2251051 | 174.4 | 223.4 | 305.3 | 1.75 | 333.0 | 0.92 | 1395.7 |
| citm_catalog | 1727204 | 284.3 | 511.1 | 552.0 | 1.94 | 668.2 | 0.83 | 4877.0 |
| scorecard corpus | 1033424 | 122.2 | 190.2 | 220.0 | 1.80 | 163.8 | **1.34** | 1483.3 |
| small-objects | 2412355 | 74.2 | 117.5 | 123.8 | 1.67 | 85.8 | 1.44 | 1194.0 |
| string-heavy | 2915939 | 256.0 | 242.9 | 316.7 | 1.24 | 304.1 | 1.04 | 2843.2 |
| twitter | 631515 | 211.7 | 264.4 | 263.5 | 1.24 | 345.0 | 0.76 | 4524.9 |

On the scorecard corpus the export went from 0.75x to 1.34x of serde_json (the "within 2x" pass line was met before and is met with room); 2x of serde_json (328 MB/s) was **not reached** (220). Every row is above the scalar export; none is below by more than noise (T2 string-heavy 243 against T1 256 is the one row below, within the noise, and is the row slice 5 then raised by 30%).

Where the time goes now (the sampler of `prof.c` on the final tree, scorecard corpus, 7965 samples): `runW` itself 51.6%, stage 1 16.4%, the word-parallel leaves 13.6% (`plainOff` 5.5, `scanDigitsW` 5.2, `lexOk` 2.9), memory movement 13% (`_fini`, libc's copy of the input and tape: 6.7; `lean_byte_array_copy_slice`, the string and number text and the final tape copy: 3.4; `vbm_copy_`, the shim's copy of the tape out: 2.9), allocation 2.8%. Inside `runW` the cost is spread over hundreds of instructions with no hot spot (the 25 most-sampled addresses are under 1% each); by source line (the same sampler with the objects compiled `-g`, on the tree of slice 4), 53% of all samples were in `lean.h` inline functions: `lean_nat_dec_lt` (the bounds test of every `byteAt`/`byteIs`) 10%, `lean_box`/`lean_unbox` 7.5%, `lean_nat_add` and the other checked `Nat` operations.

### The class of the cost, and what it says about the rest of the library

1. **The class: per-token overhead of Lean-emitted code, not bytes.** Stage 2 is a state machine over tokens; each token costs tens of `Nat` operations (every `Nat` is a boxed scalar with a tag test and an overflow check on each operation, a `lean_nat_mul` re-checks its product by a division, `Nat` `<<<` goes to GMP), several runtime calls on byte arrays (an append or a `copySlice` is a function call with a capacity and exclusivity check), and, in the first version, an allocation per token (`Option`, a pair, the `TapeBuf` struct). The first design of the memo projected stage 2 at 1.5 to 4 times slower than hand-written C; the measurements put it at about 5x (50 cycles per node against 5 to 10). The memory side of the same class: the output is 2.5 to 4 times the input, so a parse touches tens of megabytes for one megabyte of input (first-touch page faults on a freshly mapped array, doubling growth, the copy into the exact-size result, the shim's copy out), which is 14% here and a third on small-objects.
2. **Other places in the library with the same cost:** (a) the scalar fused parser `runT` and its leaves (`strBytes`, `scanDigits`, `skipWsA`, `pushLex`, `pushWordFast`: one byte per iteration with `Nat` positions and an append per tape word); it is now the fallback and the *error path*, so an invalid document is parsed at the old speed; (b) the reference parser and the printer (`Print.lean`: `pushDigits`, `String` and `List` per character); (c) the ABI shim's copy loops (`vbm_copy_`, `dflt_alloc_`), trusted C that moves the whole output once more than the parse needed; (d) stage 1 itself, 15% here, at the speed of portable word-at-a-time code (1.1 to 1.4 GB/s).
3. **The class-level remedy, in the order that paid:** keep hot state in unboxed scalars or in preallocated arrays with inline stores (`st64`), not in structures, pairs or `Nat`; replace a byte loop by a word-parallel test whose lanes cannot interact (carry-free), proved once as a lane toolkit (`LeanJsonProofs/Swar.lean`) and used by every leaf; copy runs with one runtime call instead of a call per byte; make every loop a tail call (a non-tail recursion is a stack frame per eight bytes and a trap on WebAssembly); grow output buffers in cache-sized chunks into the array's own doubling capacity and never zero-fill cold memory. Not yet applied, and the next two levers by the measurements: positions and counters as `USize` throughout `runW` and its leaves (the 25 to 30% that is `Nat` arithmetic, with the proof cost of restating the leaves), and a vector kernel for stage 1 (S9: stage 1 would go from 15% to about 4%; it adds trusted C and needs the owner's decision of memo section 10, item 3). Both together are about what 2x of serde_json on the scorecard corpus needs.

## Round two, slice 1: positions, counters and fuel as `USize` (`runU`)

The profile above put a quarter of `runW` in checked `Nat` arithmetic. `runU` (`LeanJsonSimd/ParseSimd.lean`) is `runW` with the positions (`i`, `tw`, every leaf's result), the nesting budget and the fuel as `USize`; a byte is read with `uget` after one comparison against `a.usize`; the literals `null`/`true`/`false` are unrolled `byteIsU` tests; the skip (`skipU`), the plain-string run (`plainOffU`), the digit scans (`scanDigitsU`, `scanNumU`, which answers `0` for "none" instead of allocating an `Option`) and the lexeme test (`lexOkU`) are the `USize` versions. The text region keeps `Nat` sizes (its length has no bound in the types). Guards are written so that no `USize` operation can wrap (`p ≤ a.usize ∧ 8 ≤ a.usize - p`, not `p + 8 ≤ a.usize`).

The proof (`LeanJsonProofs/ParseU.lean`, no new axiom): each leaf equals the `Nat` leaf it replaces through `toNat` (`byteIsU_eq`, `delimAtU_eq`, `skipU_eq`, `plainOffU_eq`, `scanDigitsU_eq`, `scanNumU_eq` (an `Opt` relation: 0 is none), `lexOkU_eq`, `strU_eq`, `putNodeU_eq`), and `runU_sound : runU ... = some t → runW ... = some t` is the induction of `runW_sound` over the same branches, carrying the bounds that keep `USize` from wrapping (position ≤ size + 1, `tw + 4 f ≤ 4 size + 8`, tape ≤ 8 tw + 4096, depth + open containers ≤ 512). `parseTapeSimd_eq` is now `runU_sound`, then `runW_sound`, then `parseTapeI_eq`; `runW`, `runI`, `runT` stay as the stepping stones. One consequence is in the statement: `simdLimit` went from 256 MiB to 64 MiB, because the tape of a 256 MiB input does not fit a 32-bit `USize` (wasm32); larger inputs take the scalar parser.

Through the C ABI (`docs/perf/prof.c`, `leanc -O2`, static library, best of 3 windows of 1 s per cell, the two builds alternated). **Local, host x (22 cores), load 2.4 at the start, 1.3 at the end (above 2 at the start: reported), about 5% noise.** A = main before (`be5d779`), B = this slice:

| corpus | bytes | MB/s A | MB/s B (`runU`) | B / A |
|---|---|---|---|---|
| canada | 2251051 | 303.6 | 387.4 | 1.28 |
| citm_catalog | 1727204 | 551.0 | 674.6 | 1.22 |
| scorecard corpus | 1033424 | 239.2 | 328.1 | 1.37 |
| small-objects | 2412355 | 136.8 | 191.9 | 1.40 |
| string-heavy | 2915939 | 368.6 | 440.0 | 1.19 |
| twitter | 631515 | 256.8 | 319.5 | 1.24 |

No corpus is slower. The scorecard corpus is at about 2.0x of serde_json (163.8 in the table above, same host).

## Round two, slice 3: the AVX2 classifier of stage 1 (the fourth trusted shim)

After slice 1 the sampler put stage 1 at 22% of the scorecard corpus (12% of small-objects, 25% of canada, 22% of twitter): about 41 ns per block of 64 bytes, about 140 cycles, in the portable SWAR classifier (eight words, four `eqLanes` or `pack8` chains each). The four class masks of a block (quotes, backslashes, operators, white space) now come from `VbmSimd.inset64`, a trusted AVX2 shim in the pinned vbm-simd (its landing: clause VS-12, ledger T12, `include/vbm_simd.h`; Lean model `insetSpec`, the per-byte machine; `scripts/test-shims.sh`: 3.5 million comparisons against the model, a guard-page test, seven mutants of the C each caught), in the pattern of the three before it. `LeanJsonSimd.Stage1.stage1Fast` takes it **only where `hasAvx2 ()`** (cpuid and xgetbv, cached in the shim) and runs the proved portable `stage1` otherwise (arm64, wasm, an x86-64 CPU without AVX2); the escape carry, the string state and the scalar starts (`maskOut`) are the same proved Lean for both. `stage1Fast_eq : stage1Fast a = stage1 a` (`LeanJsonProofs/Stage1Avx.lean`) holds for either answer of the CPU test, by the model: each of the four sets flags exactly the bytes of the portable class mask (256 cases per class; the padding byte 0 is in none). The shim is a carve-out outside the share (`scripts/carveouts.txt`: `VbmSimd.inset64`, `VbmSimd.hasAvx2`, ledger T14); the specified share stays **100.00%** (spec 42526 of 42526 nodes; boundary 49: `hasAvx2`, `ctz`, `ld64`, `st64`, `inset64`).

A mistake found on the way, worth the class: `hasAvx2 ()` in `stage1Fast` was extracted by the compiler as a closed constant computed once at start-up (`lean_uint8_once`), a runtime function the freestanding builds do not have (the native and wasm tests failed to link); passing a `Unit` that depends on the input does not help (a `Unit` is always `box 0`), the cure is `never_extract` on the shim's declaration (vbm-simd `e01a3fc`).

Through the C ABI, as before (A = after slice 1, B = this slice; best of 3 windows of 1 s; **local, host x, load 0.8 at the start, 1.6 at the end, about 5% noise**):

| corpus | bytes | MB/s A | MB/s B (AVX2 stage 1) | B / A |
|---|---|---|---|---|
| canada | 2251051 | 384.6 | 472.2 | 1.23 |
| citm_catalog | 1727204 | 680.2 | 924.0 | 1.36 |
| scorecard corpus | 1033424 | 322.3 | 390.5 | 1.21 |
| small-objects | 2412355 | 187.0 | 195.6 | 1.05 |
| string-heavy | 2915939 | 435.8 | 535.7 | 1.23 |
| twitter | 631515 | 312.8 | 369.2 | 1.18 |

Stage 1 is now 9% of the scorecard corpus (the shim 6%, the Lean loop around it 3%). A batch kernel (the four masks of 32 blocks in one call with the constants hoisted: measured in C alone at 4 ns per block against 10 ns for five calls) would take most of the rest of that 9% and is not built.

## Round two, slice 4: the tape, the text and the result are allocated with their capacity (no doubling copy)

The sampler of the tree after slice 3 (a profile build whose handler also records the return address, to say who called libc's `memcpy`): `lean_copy_sarray` 4.6% (scorecard corpus), 6.7% (canada), 9.3% (small-objects), and the `memcpy` under `lean_byte_array_copy_slice` another 3 to 8%. The first is the runtime growing a byte array that has no room left: every `copySlice` or `push` onto an array at capacity allocates twice the capacity and copies everything written so far. The tape (grown 4096 bytes at a time), the text region and the result (`finishW`: the header, then the tape appended, then the text appended: two growths) each did it, about one full copy of the output more than the parse needs. Now the three arrays are allocated with their capacity and filled within it: the text with the input's size (a hint: no theorem depends on it), the tape with `16 * popcount(structural mask) + 4096` bytes (every node starts at a set bit of the mask and a node is 16 bytes; `popLoop`, a tail-recursive count over the words of the mask, about 0.2 operations per input byte; the pages of the capacity that are never written are never touched) in `initTape`, and the result with `24 + 8 * tw + text.size`. In the proof only sizes matter (`initTape_size`; `finishW_eq` takes `emptyWithCapacity c = empty`, which is `rfl`).

Through the C ABI (A = after slice 3, B = this slice; best of 3 windows of 1 s; **local, host x, load 2.4 at the start (above 2: reported), 1.4 at the end, about 5% noise**):

| corpus | bytes | MB/s A | MB/s B | B / A |
|---|---|---|---|---|
| canada | 2251051 | 472.0 | 531.6 | 1.13 |
| citm_catalog | 1727204 | 957.5 | 972.5 | 1.02 |
| scorecard corpus | 1033424 | 366.7 | 387.6 | 1.06 |
| small-objects | 2412355 | 207.0 | 228.0 | 1.10 |
| string-heavy | 2915939 | 536.0 | 586.1 | 1.09 |
| twitter | 631515 | 368.7 | 364.1 | 0.99 |

(twitter: 0.99 is within the noise; its strings are short, mostly non-ASCII, and its time is in `strBytesW`.)

## Round two, slice 5: the string decoder without an `Option` per character (`decodeCharK`)

After slice 4 the profile of twitter (real text: Japanese, escapes `\n` and `\"`) was: `strBytesW` 19%, `lean_dec_ref_cold` 7.4% (32638 cold frees against 34993 small allocations in one parse), `plainOff` 8%, `copySlice` and `memcpy` 11%: every escape and every multi-byte character went through `decodeCharA`, which returns `Option (Nat × Nat)`, and Lean's compiler does not remove the `some (n, j)` that the next `match` takes apart (nested matches through `if`s are not floated into each other; the closed-form `@[inline]` of `decodeCharA` does not help). `decodeCharK` (with `decodeUtf8K` and `decodeUK`) is the same decoder in continuation-passing style: the branches call a continuation `k n j` (inlined at each use) instead of building the pair, so the string loop of `strBytesW` allocates nothing per character. `decodeCharK_eq : decodeCharK a i k d = match decodeCharA a i with | some (n, j) => k n j | none => d` (`LeanJsonProofs/ParseW.lean`, a case analysis of the same shape as the decoder); `strBytesW_eq` uses it unchanged otherwise. Also: a zero-length plain run is no longer a `copySlice` call.

Through the C ABI (A = after slice 4, B = this slice; best of 3 windows of 1 s; **local, host x, load 2.1 at the start, 1.5 at the end (above 2 at the start: reported), about 5% noise**):

| corpus | bytes | MB/s A | MB/s B | B / A |
|---|---|---|---|---|
| canada | 2251051 | 529.8 | 531.1 | 1.00 |
| citm_catalog | 1727204 | 971.2 | 968.0 | 1.00 |
| scorecard corpus | 1033424 | 392.7 | 391.5 | 1.00 |
| small-objects | 2412355 | 222.2 | 230.2 | 1.04 |
| string-heavy | 2915939 | 590.3 | 593.1 | 1.00 |
| twitter | 631515 | 347.6 | 458.0 | 1.32 |

(string-heavy does not move: its escapes are `\uXXXX` and its multi-byte characters are one per run, and what it spends is the per-character `pushChar` (a runtime call per byte) and the word loop restarting after each character.)

## Round two, summary: the six-corpus table and the class of what is left

Three trees built and run alternately in one session (the C ABI, `docs/perf/prof.c`, `leanc -O2`, static library; best of 3 windows of 1 s; **local, host x, load 1.4 before and 1.3 after**, about 5% noise): T1 = the scalar export (`origin/fm/vbm-json-simd2`), T3 = round one (`8b34bbe`), now = main after round two (`7a2d69a` slice 1, `dd80767` slice 3, `cc4f94b` slice 4, `2ed07f7` slice 5). The comparators are the table of "Summary of the S8 to S10b series" above (same host, earlier session: serde_json `Value` 333.0 / 668.2 / 163.8 / 85.8 / 304.1 / 345.0, simdjson DOM 1395.7 / 4877.0 / 1483.3 / 1194.0 / 2843.2 / 4524.9, same row order).

| corpus | bytes | T1 scalar start | T3 round one | now | now / T3 | now / serde_json | now / simdjson |
|---|---|---|---|---|---|---|---|
| canada | 2251051 | 168.6 | 284.6 | 522.4 | 1.84 | 1.57 | 0.37 |
| citm_catalog | 1727204 | 268.9 | 548.6 | 963.4 | 1.76 | 1.44 | 0.20 |
| scorecard corpus | 1033424 | 132.1 | 237.8 | 398.8 | 1.68 | **2.43** | 0.27 |
| small-objects | 2412355 | 83.8 | 136.5 | 231.6 | 1.70 | 2.70 | 0.19 |
| string-heavy | 2915939 | 284.5 | 356.9 | 584.9 | 1.64 | 1.92 | 0.21 |
| twitter | 631515 | 207.3 | 256.1 | 460.7 | 1.80 | 1.34 | 0.10 |

(The earlier tables put T3 at 305.3 / 552.0 / 220.0 / 123.8 / 316.7 / 263.5 on a busier machine; in this session T3 is 284.6 / 548.6 / 237.8 / 136.5 / 356.9 / 256.1. Ratios within one session are the information.) The scorecard corpus went from 0.81x (the scalar export, early) to 2.43x of serde_json; it is 3.7 times slower than simdjson (round one ended at 6.2 times, the scalar start was 11.2 times). The freestanding native library (`scripts/build_native.sh`, the scorecard's build, `rt.c`'s own `memcpy` and `memmove`) runs the same corpora at 93 to 97% of these numbers (canada 478 against 507, scorecard 360 against 384, small-objects 224 against 234, twitter 435 against 463).

The specified share, last line of the closure gate on the tree after slice 5: `closure gate: spec 42526 | boundary 49 | unverified 0 | total 42526 | specified share 100.00% (floor 100.00%)`; carve-outs, listed in `scripts/carveouts.txt` and outside the share: `VbmSimd.hasAvx2`, `ctz`, `ld64`, `st64`, `inset64` (49 nodes). No new axiom (the axiom gate: 632 constants checked, 0 offending); `parseTapeSimd_eq` is the theorem of the ledger's `simd-parser-equals-scalar-parser`, now through `stage1Fast_eq`, `runU_sound` and `runW_sound`.

What each slice was worth on the scorecard corpus (same session, each against the one before): `runU` 1.37x, the AVX2 classifier 1.21x, capacity-sized buffers 1.06x, the allocation-free string decoder 1.00x (1.32x on twitter, whose strings are real text). The product is 1.68x of round one on it.

### Where the time is now, and the class

The sampler on the final tree (scorecard corpus, 5977 samples): `runU` 61.5%, `lean_byte_array_copy_slice` 6.8%, the AVX2 shim 6.6% and the Lean loop around it 3.1%, libc `memcpy` under the runtime 6.5%, the ABI shim's copy out and in (`vbm_copy_`) 4.7%, `lexOkU` 4.4%, `popLoop` 1.8%. Twitter (5972 samples): `runU` 29.6%, `strBytesW` 23.2%, `plainOff` 8.3%, the shim 7.1%, `lean_byte_array_push` 3.2% and `pushChar` 2.9%. Inside `runU` there is no hot spot (by source line of the generated C the largest line is 3% and the 400 largest add up to 46%): about 45 cycles per node, where a hand-written C stage 2 does 5 to 10.

1. **The class: per-token overhead of Lean-emitted code, then per-call overhead of the Lean runtime.** What round one named (checked `Nat` arithmetic on boxed positions, a runtime call for each tape append, a pair or `Option` per token) was removed in order, and each removal paid: the positions to `USize` (and a byte read as one `USize` comparison and one `uget`), the vector classifier, the arrays sized for what is written into them instead of grown by the runtime's doubling copy, the decoder's result passed to a continuation instead of built as an `Option` (the compiler does **not** remove the `some (n, j)` that the next `match` takes apart: one allocation and one cold free per escape or multi-byte character, 7% of twitter). What is left in `runU` is the work of the token loop itself, spread thin: two `st64` shim calls for every node (each tests the array for exclusiveness and its bounds: they are what makes the shim total), two to four `skipU` per token (a mask word load with its bounds test, a shift, `ctz`), a bound test on every byte read, up to ten loop arguments; and, outside it, one `lean_byte_array_copy_slice` runtime call (about 40 cycles with its `memcpy`) for the text of every string and number.
2. **The other places with the same cost:** (a) `strBytesW`, the path of every string that has an escape or a non-ASCII character: after each such character the word loop restarts, a run is copied by a runtime call, and the character is pushed by `lean_byte_array_push` once per byte (twitter 23%, string-heavy 20%); (b) the scalar fused parser `runT` and the reference parser and printer, which are the error path, the 64 MiB fallback and the specification (the same class as round one's list, untouched); (c) the ABI shim's input and result copies and `finishW`'s copy of the tape (about 10% together, bandwidth-bound: the output is 2.5 to 4 times the input); (d) the number lexeme check `lexOkU` (4 to 9% on number-heavy corpora): a second pass over bytes the digit scan has just read.
3. **The class-level remedy, in the order of the profile:** (i) carry the structural mask as a cursor (word and remaining bits in two loop arguments, as `VbmSimd.Cursor` already offers) instead of a stateless `skipU` that reloads and bounds-tests the mask word at every token; (ii) give the short text copy its own inline path (a short run is two overlapping 8-byte moves) so that most strings never reach the runtime's `copySlice`, which needs one more trusted primitive (an unaligned store at a byte offset) and the owner's decision, as the vector shim needed it; (iii) copy multi-byte UTF-8 as bytes after a validity check (`encode (decode x) = x` for well-formed input, a proof, and the validity test is the same `Tail`, `Second3`, `Second4` predicates the decoder uses), so that `strBytesW` runs over mixed runs instead of per character; (iv) have the number scan return whether an exponent was consumed, so `lexOkU` is not needed when it was not; (v) a batch kernel for the classifier (the four masks of 32 blocks in one call, the constants hoisted: 4 ns per block in C against 10 ns for five calls). The first three are each worth a few percent to a quarter on the rows they touch; none was built: (i) and (iii) change the loop's invariants and every branch of the soundness proof, and (ii) is outside what the owner approved.

## Round three, slice 1: the structural mask as a cursor (`runC`)

`runU` asked the mask for "the first structural position at or after `j`" (`skipU`) two to four times per token, each call loading the mask word, bounds-testing it and shifting by a variable count. `runC` (`LeanJsonSimd/ParseSimd.lean`) carries the mask as a cursor instead, as `VbmSimd.Cursor` offers: the word index `w` and `b`, the bits of that word not yet consumed, as loop arguments next to the position `i` they stand at. Consuming a structural byte is `advK` (`clearLowest`, the next non-empty word only when the word is used up: `nextWordU`; written in continuation-passing style so that nothing is built); a string consumes its opening and closing quote, an operator one bit, a number or literal one bit with a check that the next structural position lies at or after the end of the lexeme (else `runC` declines). The proof (`LeanJsonProofs/ParseC.lean`): `CurInv m w b lo` says the cursor stands at `lo` (`b` is the part of word `w` at or after `lo`, nothing set between `lo` and the word); `curPos_eq` (the reported position is `skipI m size lo`), `advK_spec` (the cursor after consuming the lowest bit stands after it: `clearLowest_bit` and `ctzModel_spec` of vbm-simd, `nextWordU_spec`), `curInv_skip`, `startK_spec`, then `runC_sound : runC ... = some t → runU ... = some t` by the induction of `runU_sound` over the same branches. `parseTapeSimd_eq` is now `runC_sound`, then `parseTapeU_eq` (the old statement for the `runU` parser, `parseTapeU`, kept as the stepping stone and run by no export).

Through the C ABI (`docs/perf/prof.c`, `leanc -O2`, static library, the two binaries alternated, best of 3 rounds of the median of 5 windows of 0.4 s, **pinned to CPU 2 of host x (a P core of a hybrid CPU), load 3.7 before and 2.9 after: not quiet by the "below 2" rule; the machine was otherwise idle (97% idle in `top`), so this is the noise of a shared host, about 5 to 10%**). A = main before (`b689b52`), B = this slice:

| corpus | bytes | MB/s A | MB/s B (`runC`) | B / A |
|---|---|---|---|---|
| canada | 2251051 | 470.3 | 502.3 | 1.07 |
| citm_catalog | 1727204 | 881.5 | 1055.8 | 1.20 |
| scorecard corpus | 1033424 | 362.6 | 397.4 | 1.10 |
| small-objects | 2412355 | 211.1 | 236.2 | 1.12 |
| string-heavy | 2915939 | 541.0 | 601.7 | 1.11 |
| twitter | 631515 | 420.5 | 457.6 | 1.09 |

A first version that recomputed the position from `(w, b)` at the top of every loop iteration (`curPosU`: a test, a shift, `ctz`, an add) measured slower than main on canada (0.93) and scorecard (0.97) and faster on citm_catalog (1.10): the position is now computed once, by `advK`, and passed on as a loop argument. Every row is above main. The closure gate: spec 46966 | boundary 49 | unverified 0 | specified share 100.00%.

## Round three, slice 2: multi-byte UTF-8 copied as bytes (`mbRun`)

The slow path of a string (`strBytesW`: a string with an escape or a non-ASCII byte) decoded every multi-byte character and wrote it back byte by byte (`decodeCharK`, then `pushChar`, one runtime call per byte). `mbRun` (`LeanJsonSimd/ParseSimd.lean`) continues a run of plain ASCII bytes over well-formed multi-byte characters, a validity check by `decodeUtf8K` (whose scalar is not used), so that `strBytesW` copies the whole mixed run with one `copySlice`; `runEnd` is the run's end (the word-parallel plain run, then `mbRun` only when the byte that stopped it is not ASCII). The proof (`LeanJsonProofs/ParseW.lean`): `pushChar_2`, `pushChar_3`, `pushChar_4` (the UTF-8 encoding of the decoding of a well-formed sequence is the sequence: the byte arithmetic by `Nat.two_pow_add_eq_or_of_lt`, no `decide` over bytes, the scalar is a valid `Char` by `Second3`/`Second4`), `dec_multi` (what `decodeUtf8A` reads is copied by `pushChar` of its scalar), `mbRun_run` and `strBytes_run` (`strBytes` over the run appends it), then `strBytesW_eq` as before. The first version called `mbRun` for every run and measured 7% slower on string-heavy, whose non-ASCII is all `\uXXXX` escapes (the extra non-inlined call and boxed `Nat` tests per escape); now the call is made only where the stopping byte is not ASCII (`runEnd`).

Through the C ABI as before (A = main at `ca2edaa`, B = this slice; best of 3 rounds of the median of 5 windows of 0.4 s, pinned to CPU 2 of host x; **load 3.8 before and 3.5 after: not quiet**):

| corpus | bytes | MB/s A | MB/s B | B / A |
|---|---|---|---|---|
| canada | 2251051 | 473.4 | 493.7 | 1.04 |
| citm_catalog | 1727204 | 1039.5 | 1061.1 | 1.02 |
| scorecard corpus | 1033424 | 389.5 | 405.5 | 1.04 |
| small-objects | 2412355 | 225.0 | 225.2 | 1.00 |
| string-heavy | 2915939 | 593.1 | 592.3 | 1.00 |
| twitter | 631515 | 410.4 | 489.7 | 1.19 |

Only twitter (real text: Japanese, 3-byte characters) runs the changed path (the other rows' differences are the noise of the machine). Repeated at a load of 6 to 22 (another tenant busy on the host; absolute numbers halved, ratios are the information): twitter 1.34 and 1.37, every other row between 0.96 and 1.08.

## Round three, slice 3: the short text copy (`appendBytes`, a new trusted primitive in vbm-simd)

After slice 1 the text of every string without an escape and of every number was copied from the input into the text region by the runtime's `copySlice` (a call, an exclusiveness and a capacity check, then `memcpy`: about 40 cycles for a few bytes). `appendBytes` (vbm-simd `VbmSimd/Append.lean`, clause VS-13, trust-ledger entry T13 there and in the paragraph "The short append" of T14 here; landed in vbm-simd as `54ab2fb`, `5aeb353`, `77e145f`) appends `a[i, i + n)` to a byte array: for at most 32 bytes, an unshared destination with room in its capacity and a run inside the source it moves the run with two overlapping pairs of 8-byte loads and stores (16 to 32 bytes; 8, 4, 2, 1 bytes at each end below) and sets the size; in every other case it is the runtime's `copySlice` (so its Lean body, the model, is `copySlice`: `appendBytes_spec` in vbm-simd, and `runC_sound` takes it for the call it replaces by `rfl`). The C is tested in vbm-simd against the model (about 160000 comparisons on an unshared and a shared destination; the predicate that decides the fast path against its plain statement at the edges of `size_t`; the moves with source and destination against unmapped pages) and by eleven deliberate mutants. It is listed in `scripts/carveouts.txt` (`VbmSimd.appendBytes`, T14): the closure gate line is `spec 47790 | boundary 76 | unverified 0 | specified share 100.00% (floor 100.00%)`. `runC` uses it for the string text (`strC`) and the number lexeme; the slow path (`strBytesW`) still uses the runtime's call.

Two things the measurement taught. The first version moved up to 16 bytes, and canada, whose numbers are 17 to 20 bytes, took the runtime path through the extra checks and ran slower; the limit is 32. And with `vbm_simd_append` a `static inline` function the loop, which uses it at several sites, was slower on canada (0.96) than with the runtime call; `noinline` made it faster on every row.

Through the C ABI as before (A = main at `3affd0c`, B = this slice; best of 12 rounds of one window of 0.2 s, **pinned to CPU 8 of host x (a P core whose hyperthread sibling and neighbours were idle; CPU 2, used in the earlier tables of this round, has a sibling that another tenant kept at 93%), load 7.1 before and 4.0 after**):

| corpus | bytes | MB/s A | MB/s B | B / A |
|---|---|---|---|---|
| canada | 2251051 | 522.4 | 549.6 | 1.05 |
| citm_catalog | 1727204 | 1038.1 | 1108.5 | 1.07 |
| scorecard corpus | 1033424 | 389.3 | 432.8 | 1.11 |
| small-objects | 2412355 | 247.0 | 274.1 | 1.11 |
| string-heavy | 2915939 | 589.8 | 602.1 | 1.02 |
| twitter | 631515 | 578.1 | 603.3 | 1.04 |

## Round three, slice 4: the result handed out in place (the ABI shim)

The shim (`abi/vbm_json.c`, T09) copied the Lean result (the header, the tape, the text: 2.5 to 4 times the input) into a block of the default allocator, which is itself a Lean `ByteArray`: a second allocation (first-touch page faults on fresh memory) and a second copy of everything the parse had written. With the default allocator, a result nobody else holds and the words 8-aligned in its payload, the shim now hands the result `ByteArray` itself out: `tape->words` and `tape->text` point into it, `vbm_json_free` releases it with `lean_dec_ref`. A custom allocator, a shared result, or a payload that is only 4-aligned (wasm32) copies as before. The Lean side is unchanged (no theorem moves); the shim's tests were rewritten for the new layout (the block is the object; the sizes in its header against the tape; the fault enumeration of the shim's checks runs once in place and once with the copy forced, so the old block layout stays exercised), `lean_mini.h` gained `lean_is_exclusive` (checked against `lean.h`'s in `tests/lean_layout.c`), and the whole-shim mutation metric (`scripts/mutants.py`) is 100 over the non-equivalent mutants. Not done: the input is still copied into a Lean `ByteArray` (a Lean object cannot wrap the caller's buffer), and `finishW` still copies the tape and the text into the result (writing the tape in place needs the array's size to be exact at the end, which no runtime call offers without a copy).

Through the C ABI as before (A = main at `5759575`, B = this slice; best of 12 rounds of one window of 0.2 s, pinned to CPU 8 of host x; **load 6.6 before and 6.7 after (another tenant busy on the host: CPU 9, the sibling of 8, was at 72% at the start)**):

| corpus | bytes | MB/s A | MB/s B | B / A |
|---|---|---|---|---|
| canada | 2251051 | 443.0 | 465.2 | 1.05 |
| citm_catalog | 1727204 | 921.6 | 947.5 | 1.03 |
| scorecard corpus | 1033424 | 365.6 | 385.4 | 1.05 |
| small-objects | 2412355 | 223.9 | 258.0 | 1.15 |
| string-heavy | 2915939 | 508.9 | 532.1 | 1.05 |
| twitter | 631515 | 477.0 | 492.2 | 1.03 |

## Round three, slice 5: the number lexeme's flag from two bytes (`scanNumK`), no second pass (`lexOkU`)

After slice 4 the profile (the sampler of `docs/perf/prof.c` on the tree of `529b0ea`, host x) had `lexOkU` at 11.5% of canada and 5.8% of the scorecard corpus: the check that the lexeme of a number has no `E` and no `+` (so that it can be copied from the input and not rewritten by `pushLex`), a second pass over the bytes the scan had just read. `scanNumK` (`LeanJsonSimd/ParseSimd.lean`, continuation-passing) returns the end of the number and the flag from two bytes at the end of the fraction: those bytes can only be in the exponent, whose letter is `E`, or `e` followed by `+`. `runC` copies the lexeme (`appendBytes`) when the flag is false and rewrites it (`pushLex`) otherwise. The proof (`LeanJsonProofs/NumFlag.lean`): the integer and fraction parts are digits, `-` and `.` (`scanInt_lex`, `scanFrac_lex`, `scanDigits1_lex`: the proofs of the `NumRun` lemmas of `ParseSimd.lean` over the stronger byte predicate `lexByte`), `exp_lex` (the exponent part has no `E` and no `+` exactly when the flag read at its first bytes is false: the letter, the optional sign and the digits), and `scanNumK_spec`: the flag is false exactly when `lexOkU` is true, so `runC_sound` takes the two branches for the ones of `runU` (`lexOkU` itself is no longer called by the export).

Measured by **instructions retired per input byte and (user) cycles per input byte** (`perf_event_open` on the P core, the minimum of 15 parses of one run through the C ABI; the instruction count does not depend on the load, the cycle count does: host x was saturated by other tenants, load 25 to 60, during this measurement, and every wall-clock rate taken then was meaningless), three trees built from the same host: START = `b689b52` (the start of round three), A = main after slice 4 (`529b0ea`), B = this slice:

| corpus | START instr/B | START cycles/B | A instr/B | A cycles/B | B instr/B | B cycles/B | B / A (instr) |
|---|---|---|---|---|---|---|---|
| canada | 40.56 | 10.70 | 36.91 | 7.93 | 32.92 | 6.95 | 0.89 |
| citm_catalog | 21.69 | 7.83 | 17.05 | 4.20 | 16.86 | 5.35 | 0.99 |
| scorecard corpus | 50.73 | 13.19 | 41.52 | 12.59 | 40.52 | 12.87 | 0.98 |
| small-objects | 74.87 | 25.19 | 58.91 | 16.56 | 59.77 | 15.95 | 1.01 |
| string-heavy | 31.71 | 10.97 | 27.79 | 7.25 | 28.35 | 8.25 | 1.02 |
| twitter | 43.06 | 13.77 | 29.18 | 8.06 | 29.39 | 7.03 | 1.01 |

The gain is where the numbers are: canada 11% fewer instructions (and, in the cycles that this load allowed, 12% fewer). The corpora without long numbers move by 1 to 2% in instructions either way (string-heavy has no number at all: the 2% is the code layout of the larger loop, which the cycle minimum over 40 parses puts at 2%); the cycle columns of the other rows are the noise of the shared host (citm_catalog 4.20 to 5.35 with fewer instructions). The earlier alternation measurements of this slice's first version (a flag from the exponent letter alone, no proof) gave canada +5 to +7%, the others within the noise.

## Round three, summary: the six-corpus table, the share line, and the class of what is left

What landed (vbm-json `main`, each slice proved, Tier 1 green on the landing machine, arm64 included): the structural mask carried as a cursor (`runC`, `ca2edaa`), multi-byte UTF-8 copied as bytes (`mbRun`, `3affd0c`), the short text copy (`appendBytes`, a new trusted primitive in vbm-simd: `54ab2fb`, `5aeb353`, `77e145f`; vbm-json `5759575`), the result handed out in place by the ABI shim (`529b0ea`), the number lexeme's flag from two bytes (`scanNumK`, `82d4876`). Each slice's own table is in its section above (alternated binaries, one session each, the load printed).

The six corpora, start of the round (`b689b52`) and now (`82d4876`), same host, same session, same P core. **Host x was saturated by other tenants during this last measurement (load 30 to 35; the hyperthread-free core 8 was used), so wall-clock rates were unusable and are given only as ratios of two alternated binaries; the two columns that do not depend on the load are the instructions retired per input byte and the user cycles per input byte (`perf_event_open`, the minimum of 40 parses of one run through the C ABI; cycles still carry some contention)**:

| corpus | bytes | start instr/B | now instr/B | start cycles/B | now cycles/B | cycles ratio (start/now) | alternated wall ratio (now/start, load 30+) |
|---|---|---|---|---|---|---|---|
| canada | 2251051 | 40.56 | 32.92 | 9.16 | 7.61 | 1.20 | 1.61 |
| citm_catalog | 1727204 | 21.69 | 16.86 | 5.90 | 5.04 | 1.17 | 1.17 |
| scorecard corpus | 1033424 | 50.73 | 40.52 | 12.19 | 8.88 | 1.37 | 1.28 |
| small-objects | 2412355 | 74.87 | 59.77 | 18.39 | 13.86 | 1.33 | 1.37 |
| string-heavy | 2915939 | 31.71 | 28.35 | 8.35 | 7.63 | 1.09 | 1.21 |
| twitter | 631515 | 43.06 | 29.39 | 13.72 | 7.56 | 1.82 | 1.49 |

The product of the per-slice ratios measured at a quieter load (slice 1 to 5 tables) is 1.37 (canada), 1.35 (citm_catalog), 1.36 (scorecard), 1.42 (small-objects), 1.19 (string-heavy), 1.39 (twitter); the round-two table put "now" at 522 / 963 / 399 / 232 / 585 / 461 MB/s, so the scorecard corpus is near 540 MB/s (0.37 of simdjson's 1483, 3.3 times serde_json) by that product; not measured in one quiet session, and said so.

The specified share, last line of the closure gate on the final tree: `closure gate: spec 47308 | boundary 76 | unverified 0 | total 47308 | specified share 100.00% (floor 100.00%)`. The carve-outs outside it (`scripts/carveouts.txt`): `VbmSimd.hasAvx2`, `ctz`, `ld64`, `st64`, `inset64` and the new `appendBytes`. No new axiom. Not landed: the zero-copy of the input (a Lean object cannot wrap the caller's buffer) and the in-place tape in the result (the result array's size must be exact and no runtime call truncates without a copy).

### Where the time is now, and the class

The sampler on `529b0ea` (scorecard corpus): `runC` 57%, `vbm_simd_append` 8.3%, the AVX2 classifier shim 8.1% with its Lean loop 4.1% and `popLoop` 2.2%, `lexOkU` 5.8% (since removed), libc `memcpy` under the shim and the runtime 5.6%, the allocator 5%, the shim's input copy 1.9%. Twitter (real text): `runC` 30%, `mbRun` 16.5%, `plainOff` 14%, the classifier 10%, `Second3` and `Tail` (the UTF-8 validity predicates, not inlined) 4.3%.

1. **The class is the same as in rounds one and two: per-token overhead of Lean-emitted code on boxed values, and a call per leaf.** Each lever of this round removed an instance of it: a stateless mask lookup per token (a load, a bounds test, a variable shift) became two loop arguments and a `blsr`; a decoder and a byte-by-byte write for every multi-byte character became a validity check and one copy; a runtime call for every short text became two overlapping moves; a second pass over the lexeme became two byte tests; a second allocation and copy of the whole result became a pointer into the first. Two of them taught the price of the class: a trusted inline function used at several sites of a big loop was slower than the call (`noinline`), and a position recomputed from the cursor at the top of every iteration made the cursor slower than no cursor (it is now computed once and passed on).
2. **Where the same cost lives elsewhere:** (a) the leaves that are still `Nat`: `mbRun`, `plainOff` and `strBytesW` (boxed positions, a non-inlined predicate per byte of a multi-byte character; 35% of twitter): the same `USize` rewrite that `runU` was; (b) the two copies the Lean object model forces: the input into a `ByteArray` and the tape and text into the result in `finishW` (about 8%): both need a primitive that Lean's runtime does not offer (wrap a foreign buffer, truncate an array without copying); (c) stage 1, 12 to 15% (the AVX2 shim 8 to 10%, the Lean loop around it, the popcount for the capacity hint): a batch kernel of 32 blocks per call; (d) what is left in `runC` itself is spread thin: two `st64` shim calls per node (each tests exclusiveness and bounds), the `FStack` cell allocated per container, `text.size` loads, a bound test per byte read; (e) the scalar fused parser, the reference parser and the printer (the error path, the 64 MiB fallback and the specification), untouched.
3. **The remedy, in the order of the profile now:** `USize` versions of the string leaves with their equations to the `Nat` ones (the pattern of `plainOffU_eq`); the container stack as a preallocated array written with the same `st64` primitive (no cell per container); the batch classifier; and, if the owner wants the last copy gone, one trusted primitive that truncates a byte array's size in place (then `finishW` is the header store and the text append).

# Round four

Round three's last profile (instructions per input byte by symbol, `perf_event_open` sampling every 500 retired instructions, `docs/perf/iprof.c`; host x): `runC` 51 to 67% of every corpus, stage 1 (the AVX2 shim, its Lean loop, the capacity-hint popcount) **12 to 39%** (the largest cross-corpus item: citm_catalog 39%, string-heavy 24%, twitter 23%, canada 21%, scorecard 16%, small-objects 12%), the string leaves (`plainOff`, `mbRun`, `strBytesW`, `Second3`, `Tail`) 28% of string-heavy and 34% of twitter, the per-container `FStack` cell (allocation, free, a pattern match per token) about 6% of canada, small-objects and the scorecard corpus, the copies (`finishW`, the input copy) about 7% of the cycles of the scorecard corpus. Measurements below: **host x was never quiet during this round (load 25 to 85, other tenants), so MB/s columns carry ratios of alternated binaries only; instructions retired per input byte do not depend on the load and are the primary column; cycles per byte are the minimum of 40 parses (user mode) and still carry some contention.**

## Round four, slice 1: stage 1 from one class call per block (`classify64`), no escape work for a block without a backslash, a cheaper capacity hint

Stage 1 asked the AVX2 shim four to five times per block of 64 bytes (`inset64`: the quote, backslash, operator, white-space masks), each call re-reading the 64 bytes and re-broadcasting its constants (about 50 instructions a call, 250 a block), then ran the escape and string-state arithmetic in a Lean loop on boxed `Nat` indices (120 instructions a block), then a second pass over the mask (`popLoop`, 70 instructions a word) for the tape's capacity hint. Three changes, each with its equation:

1. **`classify64`** (a new tiny trusted primitive in vbm-simd: clause VS-14, trust-ledger entry T14 there and in the paragraph "The AVX2 class masks" of T14 here; vbm-simd `23bb8c6`): the four masks of a block in one call, by two byte shuffles per half with nibble tables (`classByte t v = t[v & 15] & t[16 + (v >> 4)]`) and four compares: the tables (`classTbl`, 32 bytes) and the mask bytes (`classMs = 0x601C0201`) are Lean's, so what a class is stays in Lean, and the C is the same kind of thing as `inset64` (a vector membership test against a per-byte model, `classSpec`/`classifyModel`; 860000 comparisons in `tests/ShimTest.lean`, a guard-page test of the array and the table, eleven deliberate mutants). `stage1LoopB` (`LeanJsonSimd/Stage1.lean`) runs on `USize` indices and reads the four words from a 32-byte scratch array; `stage1LoopB_eq` (`LeanJsonProofs/Stage1Avx.lean`): it is `stage1Loop`, through `classify_word0` to `classify_word3` (vbm-simd) and four 256-case facts (`classTbl_quote`, `classTbl_bslash`, `classTbl_op`, `classTbl_ws`: the byte of the table's class is exactly the portable class), so `stage1Fast_eq` and everything above it is unchanged in statement. `inset64` is no longer called by any export.
2. **`maskOutF`** (`maskOutF_eq`: `maskOutF = maskOut`): the escape carry chain (a third of a block's arithmetic) is skipped when the block has no backslash (`escaped 0 e = e`, `escOut 0 e = 0`).
3. **`popLoopU`** (`tapeHint`): the capacity hint's popcount over the mask words on `USize` (no theorem depends on a hint, so no equation: `initTape_size` only).

The first version of the primitive's C copied the four words through a stack array into the scratch array and its scalar fallback shared the function's prologue (six pushes for the fast path): a scalar `noinline` fallback and a four-scalar store with a 32-byte fast path took 0.25 instructions per byte more out.

Instructions retired and user cycles per input byte (C ABI, `docs/perf/pc` harness: the minimum of 40 parses on CPU 8; **host x load 22 to 25 during the cycle runs, not quiet**), and MB/s of alternated binaries (`prof.c bench`, best of 6 windows of 0.5 s, load 23 to 25):

| corpus | bytes | instr/B before | instr/B after | cycles/B before | cycles/B after | MB/s before | MB/s after |
|---|---|---|---|---|---|---|---|
| canada | 2251051 | 32.92 | 29.59 | 7.22 | 6.41 | 312.3 | 323.0 |
| citm_catalog | 1727204 | 16.86 | 13.53 | 3.59 | 2.99 | 585.6 | 693.1 |
| scorecard corpus | 1033424 | 40.52 | 37.19 | 8.40 | 8.01 | 249.7 | 257.5 |
| small-objects | 2412355 | 59.77 | 56.44 | 14.11 | 12.68 | 165.7 | 167.1 |
| string-heavy | 2915939 | 28.35 | 25.16 | 6.84 | 6.49 | 301.5 | 355.7 |
| twitter | 631515 | 29.39 | 26.09 | 7.68 | 6.52 | 318.7 | 315.7 |

Stage 1 is now about 4 instructions per byte (round three: 6.8): the shim 1.3, the Lean loop 1.9, the hint 0.5. The closure gate: `spec 48530 | boundary 84 | unverified 0 | specified share 100.00%` (carve-outs: `classify64`, `hasAvx2`, `ctz`, `ld64`, `st64`, `appendBytes`).

## Round four, slice 2: the string leaf on `USize` (`mbRunU`, `runEndU`, `strBytesV`)

After slice 1 the profile of twitter (real text: Japanese, 3-byte characters) was: `runC` 34%, `plainOff` 16% and `mbRun` 14% (the run end of a string with a non-ASCII byte, on boxed `Nat` positions, called by `strBytesW`), `Second3` and `Tail` 3.5% (the `Prop` predicates of the continuation bytes, compiled as non-inlined functions), `strBytesW` 1%; string-heavy (ASCII with `\uXXXX` escapes) 14% `plainOff`, 13.5% `strBytesW`. `strBytesV` (`LeanJsonSimd/ParseSimd.lean`) is `strBytesW` with the run end on `USize`: `runEndU` (the plain-ASCII word loop `plainOffU` of round two, then `mbRunU`), `mbRunU` (the multi-byte check: `mbLenU` is the length of the well-formed character at a position, 0 when there is none, by `Bool` tests `tailB`, `second3B`, `second4B` on bytes read with `getU`, `0` past the end, which is no continuation byte; no `Option`, no pair, no `Nat`). The recursion of `mbRunU` is guarded (`q < e ∧ e ≤ q2`, always true for a valid character) so that it terminates without a lemma about the word loop; `runEndG` keeps the end at or after the start for the termination of `strBytesV`. The proof (`LeanJsonProofs/StrU.lean`): `tailB_iff`, `second3B_iff`, `second4B_iff`; `getU_eq` (a byte read past the end is the `Nat` side's `byteAt` default); `decodeUtf8K_mb` (the continuation-passing decoder at a lead byte consumes exactly `mbLenN` bytes or fails); `mbLenU_eq`, `mbRun_len`, `mbRunU_eq` (an induction on the bytes left, with `plainOffU_eq` of round two for the word loop), `runEndU_eq`, `runEndG_eq`, `strBytesV_eq` (the same loop as `strBytesW`, so `strU_C` and `strC_spec` take `strBytesV = strBytesW` and nothing above them moves).

One variant did not pay and was dropped: skipping the word loop `plainOffU` after a multi-byte character when the next byte is also non-ASCII (a `getU` test and a second recursive call instead of the call): +0.35 instructions per byte on twitter.

Through the same harness as slice 1 (instructions retired and user cycles per input byte, the minimum of 40 parses on CPU 8, **host x load 19 to 26, not quiet**; MB/s of alternated binaries, best of 6 windows of 0.5 s, load 19 to 21: those moved by up to 10% in either direction between runs of identical code, so they are not evidence; the instruction and cycle columns are):

| corpus | bytes | instr/B before | instr/B after | cycles/B before | cycles/B after |
|---|---|---|---|---|---|
| canada | 2251051 | 29.59 | 29.59 | 6.61 | 6.47 |
| citm_catalog | 1727204 | 13.53 | 13.52 | 3.14 | 3.16 |
| scorecard corpus | 1033424 | 37.19 | 37.19 | 8.26 | 8.21 |
| small-objects | 2412355 | 56.44 | 56.44 | 12.71 | 12.73 |
| string-heavy | 2915939 | 25.16 | 23.20 | 6.29 | 5.85 |
| twitter | 631515 | 26.09 | 20.44 | 6.45 | 5.20 |

Only the corpora with a string that has a non-ASCII byte or an escape (string-heavy, twitter) run the changed code; the others are identical to the instruction. What is left in the string leaf: the escape path of `strBytesV` (`\uXXXX`, the surrogate pair, `\n`: `decodeCharK` on `Nat`, `pushChar` one runtime call per byte) is 25% of string-heavy and is not on `USize` yet.

## The printer: `vbm_json_print_tape` and `vbm_json_escape_string` (round four, printer slices 1 to 4)

Measured through the C ABI by `docs/perf/printbench.c` (a harness like `prof.c`, not part of any gate): the document is parsed once; what is timed is `vbm_json_print_tape` of that tape, the whole call (copy of the tape into the runtime, the print, the hand-out of the bytes, the free). Host x, pinned to CPU 8, tree `72cbc66`, **host load average 18 to 31 during the runs (other tenants; the machine was saturated, so the wall-clock rates are low and noisy: three sessions, the best window of any is given next to the median of the last)**. The instruction count does not depend on the load; cycles do. MB/s are of the **output** (the compact JSON), parse MB/s of the input document in the same session.

| corpus | output bytes | instr/B | cycles/B (min of 21) | print MB/s, median (last session) | print MB/s, best window (any session) | parse MB/s (same session) | print / parse |
|---|---|---|---|---|---|---|---|
| canada | 2251027 | 90.0 | 17.1 | 117.4 | 123.7 | 277.5 | 0.42 |
| citm_catalog | 500299 | 110.0 | 19.8 | 87.1 | 114.0 | 610.8 | 0.14 (the input is 3.45 times the output: whitespace) |
| scorecard corpus | 933425 | 113.9 | 21.7 | 86.3 | 99.9 | 207.0 | 0.42 |
| small-objects | 2412355 | 146.4 | 26.3 | 70.3 | 77.9 | 126.0 | 0.56 |
| string-heavy | 2785939 | 63.5 | 13.9 | 116.0 | 162.3 | 229.7 | 0.51 |
| twitter | 466906 | 73.7 | 16.0 | 80.7 | 137.3 | 189.2 | 0.43 |

`vbm_json_escape_string` (the document's own bytes as text; valid UTF-8 on the corpora that are ASCII or valid UTF-8): 90 to 200 MB/s, the same loops as the strings of the printer (`utf8Range`, `plainEnd`).

Where it started: the first printer (`pnode` returning `Option (ByteArray × Nat)` for every node, a byte pushed at a time) ran at 32 to 62 MB/s of output (90 to 190 instructions per output byte on canada and small-objects) with 25% of the samples in the allocator (two heap objects per node). Runs copied with one `copySlice` (a string or a lexeme: `plainEnd` finds the run that needs no escape) and no allocation per scalar node (a scalar or string element is written in place by `pleaf`, only a container returns a pair) took canada from 32 to 101 MB/s and string-heavy from 62 to 115, at the load of that session.

### Where the time goes, and the class

The sampler (`printbench FILE sample`, `docs/perf/resolve.py`) on the final code: small-objects: `ldw` 42%, `lean_byte_array_push` 11%, `copySlice` 7%, `pmembers` 6.5%, `plainEnd` 6%; canada: `plainEnd` 26%, `ldw` 21%, `scanDig` 20.5%, `numLex` 5.4%; string-heavy: `plainEnd` 36%, `utf8Range` 29%, `ldw` 14%. The allocator is under 3% everywhere.

1. **The class is the parser's: per-token and per-byte overhead of Lean-emitted code on boxed `Nat` positions.** Each byte of a text is visited by three loops (the UTF-8 check `utf8Range`, the scan for the end of the run that needs no escape `plainEnd`, and the copy, one `copySlice` per run), and each iteration is a `Nat` add with an overflow test, a `Nat` compare with the array size and an unboxing `fget` (10 to 15 instructions per byte where a `USize` loop is 4 to 6). Each node reads two words as eight single-byte loads with a `Nat` index each (`ldw`: 14 to 42% of the time, about 60 instructions a word where `VbmSimd.ld64` is one load): that is the word-at-a-time remedy the parser took in round two (`wordAt`), not yet taken here because `LeanJson` may not import `VbmSimd`.
2. **Where else the same cost lives:** the parser's string leaves that are still `Nat` loops (`mbRun`, `plainOff`, `strBytesW`: round three's notes), `escapeString`/`pushString` of the byte printer (same loops, over a `String`'s bytes read in place), the binding readers (a second decoder per language, boundary), and the `numLex`/`scanDig` lexeme check (a second pass over every number, 25% of canada).
3. **The remedy, in the order of the profile:** (a) the tape printer as a `LeanJsonSimd` module reading words with `VbmSimd.ld64` (the model `ld64Model` is proved in vbm-simd, trust ledger T14, no new trusted C), with the refinement proof to the `Nat` printer that now stands (`printTape_encode` is about the `Nat` version; the pattern is `parseTapeSimd_eq`); (b) `USize` versions of `plainEnd`, `utf8Range`, `scanDig` with their equations (the pattern of `plainOffU_eq`); (c) one pass for a string: validate and find the end of the run together (an ASCII byte is plain or an escape, a lead byte starts the `decodeUtf8A` step), then one copy; (d) vbm-simd's `inset64` for the escape set (`"`, `\`, below 0x20) on 64 bytes at a time. Not done: the throughput above is what the verified `Nat` printer does.

## Round four, slice 3: the container stack in an array (`runC` with `stk` and `sp`), no cell per container

`runC` kept the open containers in an `FStack`: one heap cell per container (24004 allocations for the scorecard corpus, 56050 for canada, 60002 for small-objects), allocated at the open, matched at every token that ends a value and freed at the close: about 6% of the instructions of the three corpora with many small containers (`lean_alloc_small_object_core`, `mi_free`, `lean_free_object`) and a constructor test per token. A first attempt that kept one spare cell and built the next frame in its memory (`mkFr`: a `match` on the spare with the same constructor in each branch) measured 3 to 8 instructions per byte **worse**: the compiler did not reuse the cell and the spare was one more loop argument. The stack is now a byte array and a count: two words per container, the tape word index of its header with its kind (`2 * at + kind`) and the number of elements so far; `putNodeU` (the tape's own two-word store, which makes room first) pushes it, two loads read the top frame and one store bumps its count, a close stores the header and the subtree size with `closeU` (the size is `tw - at`, saturating at 0 as `Nat` subtraction is) and pops by `sp - 1`. The proof (`LeanJsonProofs/Stack.lean`, `ParseC.lean`): `SRel stk fst` (the array holds the frames of `fst`: the header index, the kind and the count of each, innermost last), `SInv` (and `sp` is their number, and the array stays below 12304 bytes, so that no index overflows on any platform); `push_core`, `SInv_push_arr`, `SInv_push_obj` (the frames below are unchanged: `putNode_words`, from the tape's own `ensureTape_spec`), `SInv_pop` (the two loads read the top frame, `unpack_at`, `kind_word_eq`), `SInv_inc` (one store changes one count), `closeU_eq`, `SInv_nil`; `runC_sound` carries `SInv stk sp fst` next to the depth budget and the statement above it (`parseTapeSimd_eq`) does not move.

Same harness as slices 1 and 2 (instructions retired and user cycles per input byte, the minimum of 30 parses on CPU 8, **host x load 30 to 34, not quiet: the cycle columns are noisy**; the output of the six corpora is byte-identical to the one before, checked by `cmp`):

| corpus | bytes | instr/B before | instr/B after | cycles/B before | cycles/B after |
|---|---|---|---|---|---|
| canada | 2251051 | 29.59 | 26.52 | 10.01 | 9.03 |
| citm_catalog | 1727204 | 13.52 | 12.65 | 4.72 | 4.53 |
| scorecard corpus | 1033424 | 37.19 | 34.17 | 12.86 | 11.38 |
| small-objects | 2412355 | 56.44 | 53.10 | 19.24 | 18.25 |
| string-heavy | 2915939 | 23.20 | 22.48 | 8.94 | 8.67 |
| twitter | 631515 | 20.44 | 20.11 | 7.49 | 7.57 |

## Round four, slice 4: the escapes on `USize` (`escK`, `hex4U`, `pushCharU`)

After slice 2 the profile of string-heavy (ASCII text with `\uXXXX` escapes, the surrogate pair and `\n \" \\`) had `strBytesV` at 26% (the escape path: `decodeCharK` on boxed `Nat` through `Option`-valued hex digits, then `pushChar` of a `Char`). `escK` (`LeanJsonSimd/ParseSimd.lean`) is `decodeCharK` at a backslash on `USize` and `UInt32` in continuation-passing style: a hex digit is a word below 16 (`hexU`, 16 for none), a hex quad a word below `0x10000` (`hex4U`, `0x10000` for none), the one-character escapes a word (`simpleEscU`, 0 for none), a byte past the end reads as `0` (no hex digit, no escape); `pushCharU` is `pushChar` on the scalar's word. The proof (`LeanJsonProofs/StrU.lean`): `hexU_spec`, `simpleEscU_spec` (256 cases each), `hex4At_getN`, `hex4U_eq` (the word is the value or `0x10000`), `pushCharU_eq` (for a valid scalar `pushCharU b n` is `pushChar b (Char.ofNat n)`), `escK_eq` (`escK` at a backslash is `decodeCharK`, for any continuation that agrees on the valid scalars the escape can produce; the surrogate arithmetic is on `UInt32` with no wrap), and the step in `strBytesV_eq`. Two variants did not pay: the run before an escape copied by `appendBytes` instead of `copySlice` (+0.2 instructions per byte: the runs of this corpus are 20 to 100 bytes), and the hex quad's validity as an `|||` of the four digits (a test per digit is the same cost and has no bit-level proof).

Same harness (instructions retired and user cycles per input byte, the minimum of 30 parses on CPU 8, **host x load 20 to 28, not quiet**; the output of the six corpora is byte-identical to the one before, checked by `cmp`):

| corpus | bytes | instr/B before | instr/B after | cycles/B before | cycles/B after |
|---|---|---|---|---|---|
| canada | 2251051 | 26.52 | 26.52 | 12.28 | 12.28 |
| citm_catalog | 1727204 | 12.65 | 12.65 | 3.51 | 2.79 |
| scorecard corpus | 1033424 | 34.17 | 34.17 | 8.39 | 8.63 |
| small-objects | 2412355 | 53.10 | 53.10 | 11.95 | 12.64 |
| string-heavy | 2915939 | 22.48 | 20.68 | 5.75 | 5.44 |
| twitter | 631515 | 20.11 | 20.04 | 5.21 | 5.18 |

(The cycle columns of the rows whose code did not change differ by up to 25% between the two runs: the host was shared. Only string-heavy runs the changed code to a measurable degree.)

## Round four, slice 5: the short append without a prologue (vbm-simd `9f74d05`), the number's flag only after an exponent

Two small things the profile showed. (1) `vbm_simd_append` (the text of every string and number: 9% of the scorecard corpus and of small-objects) was 40 instructions on its fast path: five callee-saved pushes and pops, because its general case (three conversions of a size to a Lean number, a call to the runtime's `copySlice`) needed registers across calls. The general case is now a function of its own (`vbm_simd_append_slow`) and the fast path is 28 instructions, with no prologue (vbm-simd `9f74d05`: the same clause VS-13 and ledger entry T13, the same tests and eleven mutants; one mutant's pattern follows the new text of the guard). (2) `scanNumK` read the byte at the end of the fraction (and the one after it) for every number to decide whether the lexeme has an `E` or a `+`; those bytes are examined only when an exponent was consumed (`r3 != r2`): a number without one, the common case, reads nothing (`scanNumK_spec` keeps its statement; the proof adds `hdet`: with no exponent consumed the flag is false, from `exp_lex` over an empty range). Two experiments that did not pay were dropped: the capacity hint's popcount four words at a time (the byte counts of four words added before one reduction: no instruction saved) and, in slice 4, the run copy by `appendBytes`.

An experiment to price the number path of canada (instructions per input byte, each variant built from this tree with one piece removed, outputs not checked: for the measurement only): no text copy (`appendBytes` and its size arithmetic) -2.8 (-56 instructions per number), the flag test and the `pushLex` branch -1.4, the second store of the tape node (`putNodeU` as one store) -0.75, the delimiter test after the number -0.4.

Same harness (instructions retired and user cycles per input byte, the minimum of 30 parses on CPU 8, **host x load 22 to 76 during these runs, not quiet; the cycle columns are noisy**; outputs byte-identical, checked by `cmp`). Before = main after slice 4 (`99134d2`), after = this slice:

| corpus | bytes | instr/B before | instr/B after | cycles/B before | cycles/B after |
|---|---|---|---|---|---|
| canada | 2251051 | 26.52 | 25.48 | 6.86 | 5.96 |
| citm_catalog | 1727204 | 12.65 | 12.25 | 2.87 | 2.88 |
| scorecard corpus | 1033424 | 34.17 | 32.65 | 8.51 | 8.76 |
| small-objects | 2412355 | 53.10 | 50.61 | 12.20 | 12.06 |
| string-heavy | 2915939 | 20.68 | 20.34 | 5.67 | 5.08 |
| twitter | 631515 | 20.04 | 19.57 | 5.12 | 5.00 |

## Round four, summary: the six-corpus table, the share line, the class of what is left, the ceiling

What landed on `main` (each slice proved, Tier 1 green on the landing machine): stage 1 from one class call per block (`classify64`, vbm-simd `23bb8c6`, `559d7b2`), the string leaf on `USize` (`mbRunU`, `runEndU`, `strBytesV`, `ca5509d`, with the fix of the differential test's count that had made the scheduled run red before this round), the container stack in an array (`926a71f`), the escapes on `USize` (`99134d2`), the short append without a prologue (vbm-simd `9f74d05`) and the number flag read only after an exponent (`49efd31`). No gate, check or lint was added.

Start of the round (`a33eafe`) and now (`49efd31`), the same host in the same session, **host x shared: load 16 to 32 during these runs (never quiet), so the cycle columns are the minimum over all the runs of the session (each run the minimum of 30 to 100 parses on CPU 8) and still carry some contention; the instruction column does not depend on the load**; the output of the six corpora is byte-identical at every slice:

| corpus | bytes | instr/B start | instr/B now | cycles/B start | cycles/B now | cycles ratio | instr ratio |
|---|---|---|---|---|---|---|---|
| canada | 2251051 | 32.92 | 25.48 | 6.92 | 5.17 | 1.34 | 1.29 |
| citm_catalog | 1727204 | 16.86 | 12.25 | 3.49 | 2.68 | 1.30 | 1.38 |
| scorecard corpus | 1033424 | 40.52 | 32.65 | 8.40 | 7.41 | 1.13 | 1.24 |
| small-objects | 2412355 | 59.77 | 50.61 | 12.86 | 11.49 | 1.12 | 1.18 |
| string-heavy | 2915939 | 28.35 | 20.34 | 6.61 | 4.97 | 1.33 | 1.39 |
| twitter | 631515 | 29.39 | 19.57 | 6.82 | 4.97 | 1.37 | 1.50 |

The same two binaries alternated through the C ABI (`prof.c bench`, best of 8 to 10 windows of 0.5 s per corpus and binary, CPU 8, load 17 to 26; three sessions, the ratios now / start): canada 1.0 to 1.26, citm_catalog 1.33 to 1.50, scorecard corpus 1.13 to 1.31, small-objects 1.18 to 1.26, string-heavy 1.24 to 1.31, twitter 1.38 to 1.47 (MB/s of the last session: 285 / 645 / 235 / 170 / 369 / 396; the spread between sessions is the host's, not the code's). The scorecard corpus is now at about 7.4 cycles per byte (round three ended at 8.4 to 8.9 by the same method), canada at 5.2, citm_catalog at 2.7.

The specified share, last line of the closure gate on the final tree: `closure gate: spec 67119 | boundary 84 | unverified 0 | total 67119 | specified share 100.00% (floor 100.00%)`; carve-outs outside it (`scripts/carveouts.txt`): `VbmSimd.classify64` (new), `hasAvx2`, `ctz`, `ld64`, `st64`, `appendBytes` (`inset64` is no longer reachable); the axiom gate: 5535 constants checked, 0 offending; no new axiom, no `sorry`. The new trusted code of the round is one primitive (`classify64`: about 70 lines of C in vbm-simd, a model, 860000 comparisons, a guard-page test, eleven mutants) and a restructuring of `appendBytes` (the same function, its general case in a function of its own).

### The class of what is left

1. **The class is the token loop's per-node cost, now dominant.** After this round `runC` is 50 to 77% of the instructions of every corpus (68% of canada, 73% of the scorecard corpus, 77% of small-objects): 140 to 170 instructions per node where a hand-written token loop spends about 30. Priced by taking one piece out at a time (canada, instructions per input byte; slice 5): the text copy of a number (`appendBytes`, its size arithmetic) 2.8, the flag test 1.4, the tape node's second store 0.75, the delimiter test 0.4; and by reading the sampler: the two `scanDigitsU` calls of a fraction (14% of canada), the `plainOffU` call of a string (about 35 instructions for a key of two characters), two to three cursor advances per token, the room test and two store calls per node, the fuel and bounds tests, `text.size` and `hdrW` on boxed `Nat`. Round four took out what had a lemma-sized cure; what is left is spread over those pieces, none above 10% of the loop.
2. **Where else the same cost lives:** (a) the copies the Lean object model forces: the input into a `ByteArray` (the shim), the tape and the text into the result (`finishW`), about 7% of the cycles of the scorecard corpus, canada and small-objects (the output is 2.5 to 4 times the input; cycles, not instructions); (b) the capacity hint's pass over the mask (2 to 3%); (c) the scalar fused parser, the reference parser and the printer, untouched by this round (the error path, the 64 MiB fallback, the specification); (d) allocation: one `Option` and one pair per string that is not plain (twitter, string-heavy: 1 to 2%).
3. **The remedy, in the order of the profile now, none approved-as-trusted beyond a tiny primitive:** (i) a fifth class in stage 1 (the bytes a plain string may not contain: below `0x20`, `\`, `"`, `0x80` and above), so that a string is plain by two mask tests and not by the word loop (`plainOffU`): needs `classify64` to compute five masks (vbm-simd) and a relation between the mask and the bytes in `runC_sound`; 4 to 7% of small-objects, the scorecard corpus and string-heavy; (ii) the text length as `USize` with the invariant that the text is no longer than the input (1.5 to 2.4%: measured by a prototype, not landed: the invariant touches every branch); (iii) a two-word store (one primitive, the model is two `st64`) for the tape node and the close (about 1.5%); (iv) the result in place: the tape written at an offset of three words into the result array and the array truncated at the end (one primitive, `truncate`; the offset touches every tape lemma): about 7% of the cycles of the corpora with a large output; (v) a one-pass number scan; (vi) beyond these a token-loop kernel in C, which is not approved.

### The ceiling, stated honestly

With verified Lean and tiny primitives (a load, a store, a count, a vector compare, a short copy), the remedies (i) to (v) are worth together about 20 to 25% of the instructions: the scorecard corpus from 7.4 to about 6, canada from 5.2 to about 4.2, citm_catalog from 2.7 to about 2.2, twitter and string-heavy from 5 to about 4. That is where this design stops: **a hand-written parser of the simdjson class does 1 to 2 cycles per byte, and the remaining factor of 3 to 4 is the token loop itself, which Lean's emitted C cannot approach** (every token is tens of operations on boxed or checked values, every store and every cursor step a call or a guarded sequence; the compiler does not see through them). Closing it takes the trusted kernel the owner has not approved; the proofs and the primitives built here (the cursor, the stacks, the leaves on `USize`) are what such a kernel would be checked against.

## The printer, round five: words, runs and one load (printer slices 5 to 8)

Four landed slices, each with its equation to the printer it replaces (`printTape_encode`, `escapeChecked_eq`, `printBytes_eq`, `escapeString_eq` are unchanged theorems; no new axiom; no gate, check or lint added):

1. `printTapeG` (`LeanJson/PrintTape.lean`): the printer is generic in the word load `ld` and the leaf writer `lf` (`@[specialize]`: the emitted C is the same as before, instruction for instruction); `printTape` is `printTapeG ldw pleaf`; the proofs of `printTape_encode` needed only the extra arguments. (`479076e`)
2. `LeanJsonSimd/PrintSimd.lean`: the export runs `printTapeS = printTapeG ldwS pleaf`; `ldwS` is one `VbmSimd.ld64` (`ldwS_eq`: the little-endian word with `|||` is `ldw`'s sum of the same eight shifted bytes, `ors_eq`). First try 1.8 times slower: a literal 2^32 in the guard is a big number to the Lean compiler (`lean_cstr_to_nat` per call); the guard is `size / 65536 < 65536`.
3. The texts a word at a time (`e39d154`): `runS flag tl x i e`, the end of a run found eight bytes at a time (`ld64`, `ctz` of the first flagged lane; the word may overhang the range: the overhang reads as zero, which both flags report); `plainEndS` (`escFlag`: below 0x20, quote, backslash), `scanDigS` (`ndFlags`), `utf8RangeS` (eight ASCII bytes at once), `numLexS`, `escLoopRS`, `pleafS` are `plainEnd`, `scanDig`, `utf8Range`, `numLex`, `escLoopR`, `pleaf` with those. `runS_eq` is proved once for any flag whose lanes are exact (`escFlag_lane`, `ndFlags_lane`) against `runEnd P`; `@[specialize]` on `runS` matters (without it the flag is a closure on boxed words: 1.5 times slower than before).
4. A lexeme that passed `numLex` is copied whole (`ea4740a`): `numLex_allC` (every byte of an accepted lexeme is a digit, `-`, `+`, `.`, `e` or `E`, from `numSign_props`, `numInt_props`, `numFrac_props`, `numExp_props`) and `escLoopR_plain` (a run with no byte to escape is one `copySlice`): the second pass over a number is gone. `ldwS` tests `i + 1 ≤ size >>> 3` (no multiplication).
5. The export `vbm_json_escape_string` runs `escapeCheckedS` (`escapeCheckedS_eq`): the UTF-8 check a word at a time, then `escLoopRS`; it was the per-byte `escLoop` with `pushEsc` and a `Nat` loop.

Measured by `docs/perf/printbench.c` through the C ABI, host x, CPU 8, tree before = `72cbc66`-era printer (`8c8831b`), after = `ea4740a` (slices 1 to 4). Instructions and cycles per **output** byte are the minimum of 41 calls; MB/s are of the output, the median of 5 windows of 0.6 s. **Host x load 18 to 22 (shared; the base and the new binary alternate on each corpus, so each pair saw the same load)**. The instruction count does not depend on the load.

| corpus | output bytes | instr/B before | instr/B after | cycles/B before | cycles/B after | MB/s before | MB/s after | speedup (MB/s) |
|---|---|---|---|---|---|---|---|---|
| canada | 2251027 | 90.0 | 44.2 | 16.7 | 8.2 | 138 | 283 | 2.04 |
| citm_catalog | 500299 | 110.0 | 71.6 | 19.9 | 13.6 | 120 | 163 | 1.36 |
| scorecard corpus | 933425 | 113.9 | 75.7 | 21.2 | 14.9 | 106 | 150 | 1.42 |
| small-objects | 2412355 | 146.4 | 109.6 | 26.4 | 21.3 | 78 | 87 | 1.12 |
| string-heavy | 2785939 | 63.5 | 36.0 | 14.1 | 7.7 | 177 | 220 | 1.24 |
| twitter | 466906 | 73.7 | 50.8 | 22.0 | 13.8 | 77 | 107 | 1.39 |

`vbm_json_escape_string` (the document's bytes as text; MB/s of input, host load 25 to 29, alternating): canada 139 to 567, citm_catalog 118 to 345, scorecard corpus 142 to 225, small-objects 121 to 138, string-heavy 152 to 304, twitter 132 to 222 (the shim's copy of the text into the runtime is in these numbers).

The specified share on the final tree: `closure gate: spec 68998 | boundary 84 | unverified 0 | total 68998 | specified share 100.00% (floor 100.00%)`; carve-outs unchanged (`VbmSimd.ld64`, `ctz` are the only primitives the new code uses; no new primitive, no new trusted code); axiom gate: 5751 constants, 0 offending; Tier 1 green on the landing machine after slices 1 to 3 (arm64 included).

### The class, and the ceiling

The class the parser rounds found holds here too: per-byte loops on boxed `Nat` positions, one read per byte, a second pass over what the first pass already checked. Three of its four forms are gone from the printer (the word read of the tape, the word-at-a-time text, the second pass over a number); the fourth (positions and counters on `USize`) is not taken: `pnode`, `pelems`, `pmembers` still count words and index the tape in `Nat` (a `lean_nat_mul` with an overflow test per node), and the proof of `pnode_eq` would have to follow. What is left, by the sampler on small-objects (a short key and a short value per member, 12 output bytes): the tape word loads 22% (`ldwS`: the `Nat` index and guard around one load, and the cache miss of the first touch of the tape), `lean_byte_array_push` 14% (the comma, the colon, the quotes, the brackets: one call each), the node loop 9%, `pleafS` 8%, the copy of a run 7% (`copySlice`), the word loops of a four-byte string 12%. Capacity was already one allocation (`x.size + w.size / 4 + 16`), no doubling appears in the profile, and there is no `Option` or pair per character.

The ceiling with verified Lean and the two primitives (`ld64`, `ctz`): about 1.3 to 1.5 times the numbers above on the corpora of short strings (small-objects, scorecard corpus, citm_catalog) by putting the node loop on `USize` and pushing the punctuation with one store (a `st64`-style primitive for the two to three bytes between nodes), and 1.1 times on canada and string-heavy, which are now copy- and word-loop-bound (7.7 to 8.2 cycles per output byte). A hand-written printer does 1 to 2 cycles per output byte; the remaining factor of 4 to 5 is the per-node cost of code Lean compiles through boxed `Nat` and checked array operations, the same wall as the parser's token loop.
