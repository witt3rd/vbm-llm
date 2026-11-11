# A verified SIMD structural stage for vbm-json: design memo, prototype, measurements (step 1)

Status: **step 1 of 2** (design and prototype). Nothing in `LeanJson/`, `LeanJsonProofs/`, the ledger, the gates or the ABI is changed; the prototype lives in [`simd-proto/`](simd-proto/) and is not part of any build or gate. Step 2 (landing the slices of section 8) waits for the owner's go. Every number below is **local** (one shared 16-thread x86-64 development machine with AVX2 and no AVX-512, load between 8 and 30 during the runs, so each cell is the best of three rounds; repeated runs of one binary differ by 10 to 40%): none is from a hosted run, none is comparable with the 22-core table in the README.

This is the VBM thesis in one repository. *Verified by construction* says the fast code is the code that was proved; *bare metal* says it runs at what the hardware can do. For a JSON parser those two have so far been separate projects: simdjson has the hardware speed and no proof, this repository has the proof and runs at 5 to 11% of simdjson. The design below is the claim that they are one project: the structural stage of simdjson (classify 64 bytes at a time into bitmasks, build an index, walk the index) can be **specified once as a byte-at-a-time machine, implemented as 64-bit bit-parallel Lean code that is proved equal to that machine, and accelerated by a very small trusted shim whose every output bit is exhaustively testable**.

## 0. Summary

| question | answer (measured where it says so) |
|---|---|
| Is the kernel specifiable and provable with the tools the gates allow? | **Yes, with one constraint found by measurement**: `bv_decide` cannot be used (it adds a per-theorem axiom, which the axiom gate rejects and the independent checkers can only take on trust). The two non-trivial pieces, the prefix-xor (carry-less multiply by all-ones) and the add-with-carry escape trick, are **proved here** (`simd-proto/Stage1Proof.lean`, standard axioms only, zero warnings) by an induction over the bit index plus a `decide` over 256 Boolean cases. |
| Does Lean's C emitter produce usable code for it? | Yes, **bit-identical to the specification** (differential test, below), but 2.3x slower than hand-written C of the same shape as emitted (about 350 MB/s). Two five-line trusted primitives (an 8-byte load and an 8-byte store) bring it to the hand-written C speed (about 880 MB/s). |
| Which path? | (i) **Portable SWAR in Lean is the verified baseline**; (ii) **whole-block AVX2/NEON/WASM-SIMD kernels behind the same Lean specification are an optional accelerator**, tested against the verified baseline. Per-intrinsic modelling is not possible in emitted Lean (section 3.2). |
| What does it buy? (C prototype of the whole pipeline, bit-identical to the library's tape on all six corpora) | 7 to 11x the current Lean parser with AVX2 stage 1, 4 to 6x with portable SWAR stage 1. A **projection** for the Lean-emitted version (stage 2 assumed 1.5 to 4x slower than my C): 107 to 294 MB/s on canada, the scorecard corpus and small-objects and 253 to 568 on the others with portable SWAR, up to 2x more with AVX2 stage 1: **above the "within 2x of serde_json" pass line on all six corpora even at the pessimistic assumption** (by 1.8x to 4.5x), and within 2x of simdjson only in the optimistic AVX2 case on three corpora. |
| The end-to-end theorem | `parseTapeSimd_eq : parseTapeSimd a = parseTapeFast a` (hence `= parseTape a`), by an **optimistic fast path with a verified-sound fallback**: any irregularity (flagged error, grammar error, depth, huge input) delegates to the existing scalar `parseTapeFast`, so only *soundness* of the fast path is proved, never completeness (section 5.4). |
| Cost | 11 slices, about 900 production lines and 3000 to 3700 proof lines (section 8). The largest is the proof that the index-driven stage 2 refines `runT`. |

## 1. The problem class, and the proof pattern it names

**Class**: *block-parallel evaluation of a finite-state transducer with a small carry state* (a chunked parallel scan). The specification is a sequential machine over bytes with a handful of state bits (inside an escape, inside a string, previous byte was a scalar, UTF-8 continuation owed). The fast code consumes 64 bytes per step, computes all 64 outputs at once from per-lane predicates and a few carry-propagating primitives (a 64-bit addition for escapes, a prefix xor for string parity), and hands a few bits of state to the next block. Every vectorized scanner of text (simdjson, UTF-8 validators, CSV and HTTP splitters) is an instance.

**The reusable proof pattern** (the five steps this plan applies to each automaton):

1. *Specification*: the Mealy machine `step : State -> Byte -> State x Out`, run with `foldl`; **this** is the definition of correct, and it is small enough to read.
2. *Lane theorem*: a carry-propagating primitive is a sequential machine in disguise (an adder's carry chain is the machine's state). Prove, by induction on the bit index, an invariant `Inv` that relates the primitive's carry at bit `i` to the machine's state at byte `i`; the induction step is a statement about a handful of Booleans, discharged by `decide` (256 cases for the escape trick: `inv_step` in the prototype). Lane-wise primitives (compare, and/or/xor) need no induction: bit `i` of the result is a function of byte `i`.
3. *Block theorem*: for every entry state and every 64-byte block, the kernel returns `(foldl step s block, outputs)` with bit `i` of the output mask equal to the machine's output at byte `i`.
4. *Chunking theorem* (generic, proved once): if a block function computes the machine's state and outputs for one block, iterating it over consecutive blocks computes them for the concatenation; the carry state is threaded. By induction on the number of blocks.
5. *Composition*: the escape machine feeds the string machine feeds the scalar machine; a composed kernel is the composed machine (the output mask of one is the input mask of the next), the product state is the tuple.

The prototype proves steps 2 for the two primitives that are not lane-wise. Steps 1, 3, 4, 5 are mechanical once those are in (section 8, slices S1 and S2).

## 2. (a) Specifying the kernel

### 2.1 The scalar specification

Per byte `c`, with state `(esc, str, scal)` (all one bit) and the sticky error flags:

```
escaped  := esc                      esc  := (c = '\')  and not escaped        -- tracked everywhere, in a string or not
quote    := (c = '"') and not escaped
str      := str xor quote            -- the opening quote is "in the string", the closing quote is not
nq       := not (op c or ws c or quote)                                         -- a byte that continues or starts a scalar
structural := (op c and not str) or quote or (nq and not scal and not str)       -- operators, both quotes, first byte of a scalar run
scal     := nq
error    := (c < 0x20 and str)  or  UTF-8 machine rejects                        -- plus: still inside a string at the end
```

`op` is `{ } [ ] : ,`; `ws` is space, tab, line feed, carriage return. Two decisions worth the owner's attention, because the specification *is* the code here:

* **Both quotes of a string are in the index** (simdjson indexes only the opening one and finds the end by scanning in stage 2). It costs one more index entry per string (`tokens/byte` in section 4 includes it) and removes the per-string scan: stage 2 reads the string's extent from the index. The prototype's stage 2 is built that way and reproduces the library's tape exactly.
* **Escapes are tracked outside strings too** (a backslash outside a string is a syntax error anyway, and stage 2 sees the backslash as a scalar token and rejects it). This is what the vector kernel computes without a branch, so the specification says it.

The UTF-8 machine is the 9-state DFA of RFC 3629 (`simd-proto/classify.c: u8step`, `Stage1.lean: u8step`). It was validated against the standard: it accepts exactly 128, 1920, 61440 and 1048576 sequences of lengths 1 to 4 (`dfa_count.c`, all 2^32 four-byte strings), which are the numbers of Unicode scalar values encoded in 1 to 4 bytes.

### 2.2 The vector operations as a named set (what the kernels may use)

| operation | meaning on 64 bits (the Lean model) | where it is lane-wise |
|---|---|---|
| `eqLanes w c` | `0x80` in every byte lane of `w` equal to `c` (exact SWAR zero-lane test `~(((x & 0x7f..) + 0x7f..) \| x \| 0x7f..)` of `w xor rep c`) | per byte |
| `pack8 m` | the eight `0x80` lanes packed to 8 bits, lane `i` to bit `i` (`((m >> 7) * 0x0102040810204080) >> 56`) | per byte (one multiply) |
| `and / or / xor / andnot`, shifts | the `UInt64` operations (Lean emits `uint64_t` expressions) | bitwise |
| `prefixXor x` | six shift-xor steps: bit `i` is the xor of bits `0..i` (this is `pclmulqdq` by all-ones, written portably) | **proved** (`px_spec`) |
| `+` with carry out | the escape trick of 2.3 | **proved** (`esc_kernel_spec`, `esc_out_spec`) |

Bit-for-bit these are `BitVec 64` operations in the proofs (`UInt64.toBitVec_*` lemmas turn the library's `UInt64` code into them by `simp`: `prefixXor_toBitVec` in the prototype); the vector kernels of section 3 are *not* modelled operation by operation (3.2 says why), they are specified as a function from 64 bytes to the five class masks.

### 2.3 What is proved in the prototype, and the constraint on the tools

`simd-proto/Stage1Proof.lean` (compiles standalone with `lean`, `Init` only; the axioms printed at the end of the file are `propext`, `Classical.choice`, `Quot.sound`):

* `px_spec`: bit `i` of the six-step cascade equals `scanXor x i` (the machine `s_0 = x_0, s_{i+1} = s_i xor x_{i+1}`). A window lemma `xw_add` (the xor over the `w` bits ending at `i` splits at any `w`) turns each doubling step into one rewrite.
* `esc_kernel_spec`: for the two-addition escape kernel and every bit `i` that is not itself a backslash, bit `i` of the kernel equals the escape machine's state at `i`; `esc_out_spec`: the carry out of bit 63 is the machine's state after byte 63. The kernel is `bs := B and not carry-in; starts := bs and not (bs << 1); ends_x := (bs + (starts and parity_x)) and not bs`, `escaped := (ends_even and odd bits) or (ends_odd and even bits) or carry-in`. The proof relates `BitVec.carry` (via `getLsbD_add` and `carry_succ`) to the machine through `Inv` and `inv_step`. The statement is restricted to non-backslash bytes on purpose: the kernel does not mark the escaped backslashes inside a run, and the only consumer (`quote and not escaped`) never asks about a byte that is a backslash.
* Not proved yet, designed: the lane theorems of `eqLanes`/`pack8` (a `decide` over 256 byte values per class), the UTF-8 pair tables (a `decide` over `Fin 16 x Fin 16 x Fin 16`, 4096 cases per error class, so it passes the proof-evaluation lint), the combination (section 1 steps 3 to 5).

**Finding: `bv_decide` is out.** The obvious tool for fixed-width circuits is Lean's `bv_decide` (bit-blast, hand to a SAT solver, check the certificate). On the pinned toolchain (4.35.0) it adds one axiom per theorem (`t._native.bv_decide.ax_1_5` in `#print axioms`), which `scripts/AxiomGate.lean` rejects by design and which no independent checker can verify on our behalf. (`decide +kernel` and `native_decide` are excluded by `scripts/lint-proof-eval.sh`.) What remains is the pattern above, which is also the more informative proof: it states *why* the carry chain computes the right thing. `bv_decide` stays useful as a development-time oracle in a scratch file to check a statement before proving it.

## 3. (b) How the kernel reaches the hardware

### 3.1 (i) SWAR on `u64`, emitted by Lean's C emitter

`simd-proto/Stage1.lean` is the kernel as library code would write it: `UInt64` operations only, a tail-recursive loop over 64-byte blocks with the carried state in unboxed arguments (the emitter compiles it to a C loop with no allocation: checked), the masks written into a caller-supplied `ByteArray`. It is compiled by `lean -c` and linked with the harness; the harness checks its output **bit for bit against the scalar specification** on 200 000 random 384-byte inputs, 1.8 million UTF-8 sequences at 20 offsets (every lane and block boundary), and the six corpora, before timing anything. It passes.

What the emitter does with it (measured, the table of section 4.1, columns "SWAR, Lean-emitted" and "+ shim"):

* a naive `rep c := c.toUInt64 * 0x0101..` is a *closed term*: the emitter initialises it once at start-up and reads it from memory; byte-lane constants must be written as literals (this alone is worth writing down for every later kernel);
* eight `uget` and shifts to assemble a `u64` are **not** combined by clang into one load, and eight `uset` calls each re-check that the array is exclusive (the generated assembly of the loop has 540 byte loads, 24 call sites of the copy-if-shared function and no vector instruction): **330 to 390 MB/s as emitted**;
* replacing those two operations by `@[extern]` primitives whose Lean body is the model (`Stage1.lean: ld64, st64`, C in `s1_shim.h`, five lines each, `static inline` so the compiler sees through them) gives **830 to 890 MB/s**: exactly the portable hand-written C (`swar-C` without vectorization). The remaining gap to a vector unit is arithmetic, not code generation.

An observation that changes how the numbers must be read: the "SWAR in C" loop **auto-vectorizes** when the C compiler is allowed AVX2 (1.4 to 1.8 GB/s, twice the scalar-SWAR speed), because eight isomorphic 64-bit lanes are what a straight-line SLP vectorizer wants. The Lean-emitted loop did not run at that speed in either shape I wrote (the assembly has no vector instruction). Whether it can be coaxed (eight words loaded first, each class computed over all eight) is slice S2's first experiment; it is a free 2x if it works, and it keeps the code inside the verified path.

### 3.2 (ii) Real intrinsics behind a small trusted shim

**A vector cannot be a Lean value.** Lean's emitter has no unboxed 128/256-bit type; a `BitVec 256` is a boxed bignum, so a kernel that held vectors in Lean variables would allocate on every operation. Modelling each intrinsic as an `@[extern]` with a Lean `BitVec 256` body is therefore a dead end for *emitted* code. What can cross the boundary is a function of scalars and bytes. The shim is thus **whole-block**:

```
@[extern "vbm_s1_classify"] def classify64 (a : @& ByteArray) (i : USize) (scratch : ByteArray) : ByteArray
   -- writes five words: quote, backslash, operator, whitespace, control masks of the 64 bytes at i   (model: the per-byte predicates; Lean body = the SWAR code)
```

and the combination (escape, string parity, scalar adjacency, error accumulation: the 40 lines whose proof is `esc_kernel_spec` and `px_spec`) stays **in Lean, verified**, on top of it. The prototype's AVX2 variant uses the same combination arithmetic in C (with `pclmulqdq` for the prefix xor, which the Lean version does in 12 `u64` operations per block) and agrees bit for bit with the specification; the measured 4.5 to 5 GB/s therefore includes the combination, which stays in Lean in the design and costs a few percent more.

Why the shim is cheap to trust: `classify64`'s output bit `i` of each mask is a function of input byte `i` alone, so it is **exhaustively testable**: 64 lanes x 256 byte values = 16 384 cases cover every behaviour of the function, and lane independence is visible in the instruction list (`vpcmpeqb`, `vpor`, `vpmovmskb`). The UTF-8 check is the only part with lookback: its per-position error is a function of the four preceding bytes through two 65 536-entry pair tables, tested exhaustively at every lane position, plus the three lane-crossing shifts tested at all 64 positions and across the block boundary (`classify.c --utf8` does 1.8 million cases). On top of that: a differential test of the shim against the verified SWAR path on every Tier 1 run and the vectors, and a start-up self-check (run both on a built-in 4 KiB block; on disagreement, disable the accelerator). AVX2, NEON and WASM simd128 are three bodies for the same Lean function; a CPU without the feature (or a build without it) uses the verified SWAR path, selected by one `cpuid`/feature bit that is an *availability* decision, never a correctness one.

What the shim does not claim: that the intrinsics have their documented semantics on this CPU (trusted, as the CPU is), and that no input reaches a lane combination the tests did not (argued above for the byte classes; for the UTF-8 pair tables by the exhaustive table check, plus the structured tests for shifts).

### 3.3 The choice

| path | measured stage 1 alone | trust added | when |
|---|---|---|---|
| Lean-emitted SWAR, no shim | 330 to 390 MB/s | none | not good enough: stage 1 alone would cost a quarter to a half of today's whole parse |
| Lean-emitted SWAR + `ld64`/`st64` (+ `ctz`, `st32`) | 570 to 890 MB/s | 4 tiny `static inline` functions, exhaustively testable | **slices S2 to S7: the verified baseline, portable (x86-64, aarch64, wasm32 with its native `i64`)** |
| the same, auto-vectorized by the C compiler | 1.2 to 1.8 GB/s (C; not yet reproduced from Lean) | none | try in S2: free if the emitted shape allows it |
| whole-block AVX2 (NEON, simd128) | 4.5 to 5.0 GB/s | one C function per target, exhaustively testable, in the ledger | **slice S9**: worth 1.2 to 2x on the whole pipeline (4.4), because stage 2 dominates |

I pick **SWAR first, intrinsics second**. SWAR is portable, it is in the verified closure, and with the shim primitives stage 1 is 19 to 57% of the projected pipeline time (4.4, central assumption) against 4 to 17% with AVX2. The vector shim comes after the index-driven stage 2 exists, when its value can be measured, not assumed.

## 4. Measurements: the prototype of the classifier and of the whole pipeline

Method: `simd-proto/run.sh CORPUS_DIR` (the classifier) and `simd-proto/run_e2e.sh CORPUS_DIR` (the pipeline; builds the static library first); the corpora, their sources and sha256 are those of [`profile.md`](profile.md) (hashes re-checked). MB/s of input, best of 3 windows of 0.4 s, best of 3 rounds; the harness runs under a memory cap with core dumps off. The current parser is measured by `bench.sh` in the same sessions; the comparators are the prebuilt serde_json (`Value`) and simdjson (DOM) benchmark binaries of the scorecard, run on the same files. gcc 16.2 built the C (AVX2, PCLMUL, BMI on); the toolchain's bundled clang 23.1 built the Lean-emitted code (it ships no intrinsics headers, so the harness is gcc; the Lean-emitted code is also built with gcc, columns in `run.sh` output, within 5% to 60% of clang's: gcc is better without the shim, 20 to 30% behind with it).

### 4.1 Stage 1 alone (the classifier: masks and the two error flags; MB/s)

| corpus | bytes | scalar spec (C) | SWAR, Lean-emitted | + `ld64`/`st64` shim | SWAR, portable C | SWAR, C auto-vectorized | AVX2 intrinsics | tokens / byte |
|---|---|---|---|---|---|---|---|---|
| canada | 2251051 | 199 | 344 | 875 | 875 | 1748 | 4947 | 0.149 |
| citm_catalog | 1727204 | 205 | 383 | 885 | 790 | 1627 | 4847 | 0.094 |
| scorecard corpus | 1033424 | 198 | 388 | 893 | 800 | 1699 | 5027 | 0.294 |
| small-objects | 2412355 | 191 | 362 | 826 | 826 | 1671 | 4826 | 0.547 |
| string-heavy | 2915939 | 135 | 384 | 886 | 794 | 1628 | 4995 | 0.096 |
| twitter | 631515 | 192 | 324 | 568 | 589 | 1149 | 4498 | 0.116 |

"Scalar spec" is the byte-at-a-time machine of 2.1 transcribed to C: the *before* for the classifier. It runs at about the speed of today's whole Lean parser, which is the point: the structural stage as a loop over bytes buys nothing; as a loop over 64-bit words with the shim it is 4 to 5x faster than scalar, with AVX2 25x. The dip on twitter (568) is its non-ASCII (Japanese) text: a block with any byte >= 0x80 falls to the scalar UTF-8 machine in the SWAR variants (the AVX2 variant has no such cliff, its Keiser-Lemire check is branch-free); a SWAR range check for non-ASCII blocks is slice S3's second half.

The three stage-1 variants and the scalar specification agree on every input tried (200 000 random 384-byte blocks over a hostile alphabet, 1.8 million UTF-8 sequences x 20 offsets, the six corpora): `classify --fuzz`, `classify --utf8`, and the corpus run print "all variants agree" or exit non-zero.

### 4.2 The whole pipeline in C (stage 1 + flatten + stage 2), checked against the library's own tape

`simd-proto/e2e.c`: stage 1 (as above), the flatten of masks to a `u32` index (`tzcnt` loop writing eight candidates unconditionally), and a grammar-checking stage 2 that walks the index and writes the **same tape the library's `vbm_json_parse` returns**: the harness compares the 64-bit words and the text region **word for word** on all six corpora before timing (all "identical"), for both stage-1 variants. Strings are copied from the input (escapes decoded, surrogate pairs combined), numbers are scanned and copied in canonical form (`E` as `e`, no `+`), a literal must be followed by a delimiter, containers use an explicit stack with the library's depth limit. Any irregularity returns "fall back". This is hand-written C, **not verified**, and it exists to bound what a verified stage 2 can reach.

| corpus | stage 1 AVX2 | flatten | stage 2 (C) | pipeline, AVX2 stage 1 | pipeline, portable SWAR stage 1 (vectorization off) |
|---|---|---|---|---|---|
| canada | 4920 | 11506 | 691 | **519** | 313 |
| citm_catalog | 4637 | 15337 | 2654 | **1343** | 566 |
| scorecard corpus | 4988 | 4807 | 629 | **452** | 321 |
| small-objects | 4568 | 2772 | 516 | **347** | 266 |
| string-heavy | 4600 | 8586 | 1484 | **909** | 492 |
| twitter | 4638 | 9460 | 2068 | **1081** | 426 |

(Each cell is the best over three rounds and over the two builds of `run_e2e.sh`, one with the C compiler's vectorizer on and one off; with it on, the SWAR pipeline reaches 412, 930, 356, 264, 668 and 638 MB/s.) Stage 2 is most of the story once stage 1 is cheap: it is 1.3 to 5x slower per byte than stage 1 + flatten, and it is bound by tokens per byte (canada: a number every 7 bytes; small-objects: a token every 2 bytes). That is where a verified build will spend its effort, and where simdjson's own advantage is also smallest (its DOM stage 2 converts numbers to doubles, which this library does not do: numbers are lexemes, so the comparison with simdjson below is generous to simdjson on number-heavy corpora and fair on text-heavy ones).

### 4.3 Against today's parser and the scorecard lines (MB/s, same sessions, best of 3)

| corpus | vbm-json today (Lean, through the C ABI) | serde_json (`Value`) | simdjson (DOM) | **C pipeline, AVX2** | speedup over today | pass line: serde_json / 2 | stretch: simdjson / 2 |
|---|---|---|---|---|---|---|---|
| canada | 66 | 160 | 593 | 519 | 7.8x | 80 | 297 |
| citm_catalog | 132 | 286 | 2227 | 1343 | 10.2x | 143 | 1113 |
| scorecard corpus | 57 | 68 | 690 | 452 | 7.9x | 34 | 345 |
| small-objects | 41 | 48 | 636 | 347 | 8.4x | 24 | 318 |
| string-heavy | 127 | 157 | 1598 | 909 | 7.2x | 78 | 799 |
| twitter | 101 | 171 | 2061 | 1081 | 10.7x | 86 | 1031 |

(This machine is slower and noisier than the one behind the README table, where the gap to serde_json today is 1.2 to 2.6x; the pass line "within 2x" is met by the current parser on four of six corpora both here and there; canada and citm_catalog fail. Ratios within one session are the information; absolute values are not.)

### 4.4 What the verified (Lean-emitted) version can be expected to reach: a projection, not a measurement

Pipeline = `1 / (1/stage1 + 1/flatten + f/stage2_C)`, with `stage1` the *measured* Lean-emitted SWAR + shim (or the AVX2 shim), `flatten` and `stage2_C` the measured C figures, and `f` the unknown factor between Lean-emitted and hand-written C for stage 2. The only evidence for `f` is stage 1: it was 2.3x as emitted and 1.0x with the two primitives. Stage 2 is branchy and writes the tape, so I use 1.5, 2.5 and 4 as optimistic, central and pessimistic.

| corpus | today | SWAR + shim, f = 1.5 / 2.5 / 4 | AVX2 shim, f = 1.5 / 2.5 / 4 | pass line | stretch |
|---|---|---|---|---|---|
| canada | 66 | 294 / 206 / 142 | 407 / 256 / 165 | 80 | 297 |
| citm_catalog | 132 | 568 / 468 / 370 | 1195 / 824 / 562 | 143 | 1113 |
| scorecard corpus | 57 | 269 / 189 / 130 | 358 / 228 / 148 | 34 | 345 |
| small-objects | 41 | 223 / 156 / 107 | 288 / 185 / 120 | 24 | 318 |
| string-heavy | 127 | 442 / 341 / 253 | 751 / 499 / 332 | 78 | 799 |
| twitter | 101 | 386 / 325 / 263 | 949 / 651 / 442 | 86 | 1031 |

Reading: **the pass line is cleared on every corpus at every `f`, by 1.8x to 4.5x, with portable SWAR alone** (slices S0 to S7 and the switch S8); the factor over today is 2.7x to 3.8x at the central assumption. The stretch (within 2x of simdjson) is reached in **one cell family only**: the optimistic AVX2 case (`f` = 1.5) on canada, citm_catalog and the scorecard corpus; at the central assumption it is reached nowhere. It should be offered to the owner as a stretch, not promised.

What is certain from the measurements: the structural stage is no longer the bottleneck once it is word-parallel; stage 2 per token is. Reducing stage 2's per-token cost (no allocation, writes through `st64`, the number lexeme copied by 8-byte moves) is the performance work of slices S5 and S10, and is independent of SIMD.

## 5. (c) The rest of the pipeline, and the refinement to the existing tape

### 5.1 UTF-8 validation (verified, vectorizable)

Specification: the DFA of 2.1 (and its relation to `decodeUtf8A`, the existing reference decoder: a lemma that the DFA accepts a byte string iff it is a concatenation of `decodeUtf8A` successes). Kernel in Lean (S3): an ASCII-block test (`or` of the eight words and `0x8080..`; only a character left open by the previous block is an error), and for non-ASCII blocks the DFA run over the block's bytes (the prototype), later a SWAR range check. The vector kernel (S9) is the Keiser-Lemire lookup (three `pshufb` nibble tables and the 3- and 4-byte lead checks). Because the design is "any flagged error falls back to the scalar parser", **only soundness is needed**: *no error flagged implies the string bytes are valid UTF-8*. That halves the proof (the table can be conservative) and lets the vector kernel be tested for completeness by the 1.8 million-case suite instead of proved. Whole-input validation (not only inside strings) is equivalent to the reference, because a non-ASCII byte outside a string is a syntax error in the grammar anyway.

### 5.2 Strings and numbers

Strings: the index delivers both quotes, so the string's byte range is known. If it contains no backslash (one `eqLanes` per 8 bytes during the copy, the same primitive) its text is a copy of the range: the lemma needed is `strBytes a (i+1) b = some (b ++ a[i+1..j), j+1)` for a range with no backslash, no control byte and valid UTF-8 (the UTF-8 round trip `pushChar (decode ..) = the bytes`, which the existing proofs of `strBytes` already use in one direction). A string with a backslash goes through the existing `strBytes` unchanged: escapes are not a SIMD problem. Numbers: `scanNum` and `pushLex` as today (`FastTape.lean`), with the number's end checked against the next token (a lexeme must end at a delimiter, otherwise fall back). A SWAR digit-run scan is possible and unmeasured; it is S10.

### 5.3 The structural index builder

`flatten`: the masks to a `u32` index (a `ByteArray` written by an `st32` primitive; an `Array UInt32` also does not allocate on 64-bit targets, where `UInt32` boxes as a tagged scalar, but it does on wasm32). In Lean there is no `ctz`: `UInt64.log2` is a loop in `lean.h` (up to 63 iterations), so the builder needs a `ctz` primitive (the model: `log2 (x and (0 - x))`; C: `tzcnt`) or the six-step arithmetic binary search (exact, slower; fine for the SWAR baseline, measured later). The theorem is `flatten_spec : (flatten masks).toList = positions of set bits in order`. Inputs of 4 GiB or more use the scalar parser (the index is `u32`).

### 5.4 Stage 2 and the end-to-end theorem

```
def specIndex (a : ByteArray) : List Nat        -- positions with the structural bit, from the scalar machine of 2.1
def specOk    (a : ByteArray) : Bool            -- no control byte in a string, valid UTF-8, no string left open at the end
def stage1    (a : ByteArray) : Option (Array UInt32)   -- Lean kernel + flatten
theorem stage1_eq : stage1 a = if specOk a then some (specIndex a).toArray else none          -- exact: the kernel IS the machine

def runI : Array UInt32 → ByteArray → ... → Option ByteArray    -- walks the index; the tape of runT, without skipWsA, without per-byte string loops
theorem runI_sound : specOk a = true → runI (specIndex a) a ... = some t → t = parseTapeFast a   -- simulation of runT, one token per step

def parseTapeSimd (a : ByteArray) : ByteArray :=
  match stage1 a with | some idx => (match runI idx a ... with | some t => t | none => parseTapeFast a) | none => parseTapeFast a
theorem parseTapeSimd_eq : parseTapeSimd a = parseTapeFast a        -- and so = parseTape a by parseTapeFast_eq
```

`parseTapeFast_eq` stays the end-to-end theorem of the *scalar* export; `parseTapeSimd_eq` is the new one, proved by `stage1_eq`, `runI_sound` and nothing else. The proof of `runI_sound` is a simulation of `runT` (`LeanJson/Tape.lean`): the same branches in the same order; between two tokens `runT` calls `skipWsA`, which lands on the next non-whitespace byte, and the lemma needed about `specIndex` is that this byte is the next index entry *unless it is inside a scalar run*, in which case `runI` has already refused (the lexeme-end check above). The nesting limit, the error discipline and the byte-for-byte tape are `runT`'s, since every error is delegated to `parseTapeFast`. This is the same kind of problem as the fused-parser proof (`FastLoop.lean`, 235 lines, on top of `FastTape.lean` and the leaf lemmas), so it is cut into slices the way `fuse-plan.md` cut F0 to F7.

**Why soundness-only is the right shape.** If the fast path ever declined a valid document, the result would still be correct (the scalar path produces it); only the speed would suffer, and that is guarded by a *test*: the six corpora and every `y_` vector must take the fast path (a counter in a test-only export, or a differential on the time). If the fast path ever accepted something wrong, `runI_sound` says it did not. A bug in the kernel that flags an error where there is none is invisible to correctness. This also means the vector kernel's *completeness* never needs proof, which matters for the Keiser-Lemire tables (the one piece whose exactness is awkward to state).

## 6. Gates, ledger, ABI

* **ABI and tape**: unchanged. The export `vbm_json_parse_tape` switches from `parseTapeFast` to `parseTapeSimd` in the last slice, after `parseTapeSimd_eq`; the vectors, the native, WASM and binding tests are the end-to-end check that nothing observable changed (they exercise both paths: valid documents take the fast path, every `n_` document the fallback).
* **Closure gate**: the entry point `LeanJson.parseTapeFast` becomes `LeanJson.parseTapeSimd` (the scalar parser stays reachable through the fallback, so the executed set grows, and the specified share stays at 100% for Lean code; extern shims count as unverified mass: the baseline is restated deliberately in the switch slice, as `fuse-plan.md` F7 did). The proofs library keeps importing `Std`; nothing from it enters the closure.
* **Trust ledger**: one new entry per boundary, each derived from the tree by `scripts/trust-ledger-check.sh`: the shim header (S2: `ld64`, `st64`, `ctz`, `st32`, a few `static inline` lines), and later one entry per vector kernel (S9: AVX2, NEON, WASM simd128), each stating its test (exhaustive lanes, differential against the verified path, start-up self-check). The `-mavx2` file is a separate translation unit; the generated C stays baseline-ISA.
* **Axiom gate, proof-evaluation lint**: the method of 2.3 uses neither; the `decide` calls are over `Bool` variables, `Fin 16^3` and `Fin 64`, with no long literal in the declaration.
* **Freestanding and WASM builds**: the SWAR path needs no libc and no new runtime function (`ByteArray` operations that the shim replaces are inline); `cpuid` is an inline-assembly instruction, not `__builtin_cpu_supports` (which needs the compiler runtime). WASM has native `i64`, so the SWAR path is already the portable kernel there; simd128 is S9.

## 7. (d) What stays unverifiable

| item | where it enters | what stands behind it |
|---|---|---|
| the C compiler's translation of the generated C and of the shims | T01, T04 (already in the ledger) | differential tests, the vectors |
| the shim C: `ld64`, `st64`, `ctz`, `st32` | new ledger entry (S2) | each has a Lean model and is exhaustively testable in a few thousand cases; the differential test calls the shim and the model on the same inputs |
| the vector kernels (AVX2, NEON, simd128) | one new ledger entry each (S9) | exhaustive per-byte test (64 lanes x 256 values), pair-table test (65 536 pairs x every position), lane-crossing shift tests, differential against the verified SWAR path on every vector and corpus, sanitizer runs, start-up self-check |
| the semantics of the vector instructions on a given CPU, and the feature-bit dispatch | hardware | the dispatch can only cost availability (an illegal instruction), never correctness: a missing bit selects the verified path |
| the 64-byte tail handling (a padded copy of the last partial block) | the Lean driver, proved: the padding is bytes that are whitespace, so the specification's answer on the padded input restricted to the real bytes is the real answer (a lemma, `pad_spec`) | proved |
| performance | nowhere | measurements; "fast path taken" is a test; no claim about timing or side channels |

The unverified base grows by about 15 lines of `static inline` C in the baseline and about 90 per vector target, against verified Lean of roughly 500 production lines and proofs of five to seven times that. The number that matters for the thesis: **no byte of the verified path's logic is outside Lean**; the shims move and compare bytes and decide nothing.

## 8. (e) Slices, effort, order

Production lines are counted against the 150-line limit per slice; proof lines are estimates (the prototype's two kernel proofs are 330 lines, written in a few hours; the realistic figures include the generic chunking theorem and the composition). Every slice keeps the vectors, `parseFast_eq_parse` and `parseTapeFast_eq` unchanged, adds no axiom, and is dead code until S8 (so the closure gate sees nothing).

| slice | content | production | proof | depends on |
|---|---|---|---|---|
| S0 | specification: the scalar machine of 2.1, `specIndex`, `specOk`; the UTF-8 DFA and its relation to `decodeUtf8A`; the owner's decisions of 2.1 (both quotes, escapes everywhere) | 60 | 200 | none |
| S1 | the generic chunking theorem; `px_spec`, `esc_kernel_spec`, `esc_out_spec` (this prototype, hardened); the lane theorems of `eqLanes`, `pack8`; the composition lemma | 40 | 500 | S0 |
| S2 | the SWAR kernel in Lean (`Stage1.lean`'s shape, with the literal-constant rule), `stage1_block_eq`, the `ld64`/`st64` shim and its ledger entry and exhaustive test; the experiment on vectorizable shape | 140 | 350 | S0, S1 |
| S3 | UTF-8: the ASCII fast path and DFA in the kernel, `utf8_sound`; then a SWAR range check for non-ASCII blocks | 80 | 300 | S2 |
| S4 | flatten (`ctz` primitive or arithmetic form), `flatten_spec`, `stage1_eq` (the induction over blocks) | 90 | 250 | S2, S3 |
| S5 | stage 2, part 1: scalars and strings from the index: `scanStrI`, the no-backslash copy lemma, `runI` for scalar documents | 130 | 450 | S4 |
| S6 | stage 2, part 2: containers (the frame stack, `closeNode` as in `runT`), `runI_sound` (the simulation), the depth and lexeme-end checks | 140 | 700 | S5 |
| S7 | `parseTapeSimd`, `parseTapeSimd_eq`, fallback test, the `n_` vectors exercise the fallback | 30 | 100 | S6 |
| S8 | the switch: export `vbm_json_parse_tape` to `parseTapeSimd`; closure entries and baseline, ledger claim, benchmark before/after in `results.md` | 5 | 50 | S7 |
| S9 | AVX2 shim (then NEON, simd128): `classify64`, ledger entry, exhaustive lane test, start-up self-check, dispatch | 90 per target | 100 (model-level lemmas, optional) | S2 (independent of S5 to S8; lands after S8 so its gain can be measured) |
| S10 | stage 2 tuning: SWAR digit-run scan, 8-byte lexeme copy, tape writes through `st64`, index window kept in L2; each change with its equation lemma | 120 | 300 | S6 |

Order: S0, S1, S2 first (the answer to "does the Lean emitter's code reach the speed" is S2); S3, S4; **S5 to S7 are the bulk of the gain and of the proof**; S8 lands the win; S9 then adds 1.2 to 2x (section 4.4) and S10 closes toward the stretch. About 925 production lines (one vector target) and 3300 proof lines in all (the existing fast parser's proofs are about 1900 lines); the kernel re-check of the proof set (116 s for the current tree) should grow by roughly a third, to be checked on S6 first, as `fuse-plan.md` risk 7 says for F5.

**Risks, in order**: (1) S6 is as large as `FastLoop.lean`: split by container kind if needed. (2) The Lean emitter's quality for stage 2, which the prototype could not measure (the `f` of 4.4): if `f` exceeds 4, the pass line still holds on five of six corpora, and S10 exists for that case; the first experiment of S5 should be a Lean-emitted stage 2 on a numbers-only document, as `fuse-plan.md` risk 6 did for F4. (3) The vectorization of the emitted SWAR (S2): unknown, free upside. (4) The 32-bit index: inputs of 4 GiB or more take the scalar path, stated in the theorem's hypothesis-free form (the fallback covers it). (5) Memory: 4 bytes of index per token is 0.4 to 2.2 bytes per input byte; windowing (stage 1 and 2 on 64 KiB at a time, carrying the state) is possible and is S10's option.

## 9. Alternative considered: SWAR inside the existing loop, no index

Keep `runT` as it is and speed up only its three hot loops with the word-parallel primitives: `skipWsA` (whitespace; 17% of citm in the profile), the plain-ASCII string run of `strBytes`, the digit run of `scanDigits`. The proofs are small loop lemmas (`skipWsFast = skipWsA`, one per loop); there is no index, no fallback, no new theorem at the top. I have **not measured** it, and by Amdahl on the profile (`profile.md`) its ceiling is the share those three loops hold, which after slices 1 to 3 of `results.md` is a minority of the time on token-dense corpora (canada, small-objects), where the per-token cost of the Lean loop (the `Option` tuples, the frame cells, the tape writes) dominates. It is a candidate for a first, cheap slice if the owner wants an early win before the big one; it does not reach the pass line on the token-dense corpora by itself, and it does not prepare the SIMD path. The two designs share S1 and S2.

## 10. What the owner decides before step 2

1. The two specification decisions of 2.1 (both quotes in the index; escapes tracked outside strings). Both are spec changes in `LeanJson/`, so protected-set approvals.
2. Admitting a **trusted C shim** at all: `ld64`, `st64`, `ctz`, `st32` as `static inline` functions with Lean models, one ledger entry (S2). Without it the emitted code stays at about 350 MB/s for stage 1, which is not enough.
3. Whether vector shims (S9) are in scope, or only the portable verified path (S0 to S8, S10).
4. The success lines: the pass line is met by S0 to S7 alone in the projection; the stretch is not promised.

## Appendix: reproducing

```
# classifier: scalar / SWAR (C, Lean-emitted, with shim) / AVX2; differential tests first
mise exec -- docs/perf/simd-proto/run.sh CORPUS_DIR
# whole pipeline in C against the library's own tape
mise exec -- docs/perf/simd-proto/run_e2e.sh CORPUS_DIR
# the prototype proofs (standalone, Init only)
mise exec -- lean docs/perf/simd-proto/Stage1Proof.lean
# the UTF-8 machine against the number of valid sequences (17 s)
gcc -O2 -o dfa docs/perf/simd-proto/dfa_count.c && ./dfa      # 128 1920 61440 1048576
```

Files: `classify.c` (scalar specification, SWAR, AVX2, flatten, the differential and exhaustive tests, the timing harness), `Stage1.lean` (the Lean kernel, `unsafe` because it stands `lcProof` in for the bounds proofs a library version carries), `s1_shim.h` (the two primitives), `e2e.c` (the pipeline), `Stage1Proof.lean`, `dfa_count.c`, `run.sh`, `run_e2e.sh`. Run under `systemd-run --user --scope -p MemoryMax=12G -p MemorySwapMax=0` with `ulimit -c 0` and timeouts on a quiet machine, in a scratch copy of the tree.
