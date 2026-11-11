# The verified structural stage: what landed, and the measured numbers (step 2, slices S0 to S7)

Status: **S0 to S7 of [`simd-plan.md`](simd-plan.md) are in the tree and proved. The export is switched (S8) with the first tuning slice, `runW` (tape written in place; the measurements of [`results.md`](results.md), slice 4). The section "Measured: not a win yet" below is the measurement of `runI` before that.** Every number below is **local**: one shared 16-thread x86-64 machine (AVX2, no AVX-512)
at load 9 to 17 during the runs, each cell the best of three windows of 0.4 s, repeated runs of one binary differing by up to 15%. **None is from a hosted run.** The comparison is within one session.

## What is in the tree

| slice | where | what is proved (standard axioms only, checked by the axiom gate, which now also audits the dependency's constants) |
|---|---|---|
| S0 | `LeanJson/Struct.lean` (the specification stays in the library root) | the structural index as a byte-at-a-time machine (`sStep`, `specIndex`): both quotes indexed, escapes tracked outside strings |
| S1, S2 | the pinned dependency [vbm-simd](https://github.com/witt3rd/vbm-simd), `LeanJsonSimd/Stage1.lean`, `LeanJsonProofs/Stage1.lean` | the kernels (prefix xor, the escape carry, SWAR byte-lane compare and pack, block mask) are proved in vbm-simd; here `blockOut_spec`: one 64-byte block's mask and carries equal the machine's, bit by bit |
| S4 | `stage1Loop_spec`, `stage1_spec`, `stage1_stream` | the loop over all blocks, the partial last block (bits past the end cleared), and the cursor over the mask yields exactly `specIndex a` |
| S5, S6 | `LeanJsonSimd/ParseSimd.lean`, `LeanJsonProofs/ParseSimd.lean` | `runI` (`runT` with the whitespace skip replaced by a lookup in the mask, every error or disagreement declined): `runI_sound`: when it answers, `runT` answers the same bytes; the invariant is `Good` (the machine is outside an escape and a string, and no scalar run continues into the byte), kept by `good_op`, `good_string`, `good_scalar` |
| S7 | `parseTapeSimd_eq` | `parseTapeSimd a = parseTapeFast a` for every input (the fallback covers every decline, an error, and an input of 2 GiB or more) |

S3 (UTF-8 in stage 1) is not needed for soundness (stage 2 still runs the existing leaves) and is deferred to the string fast path (S10). The proof is sound-only by design: a declined document is merely slower.

## Measured: not a win yet (local)

MB/s of input through the Lean entry points (no C ABI, no copy), same files and sessions as [`profile.md`](profile.md); `identical` is the tape compared byte for byte with the scalar parser's, `taken` that the fast path answered (not the fallback):

| corpus | scalar `parseTapeFast` | index-driven `parseTapeSimd` | ratio | stage 1 alone |
|---|---|---|---|---|
| canada | 73.3 | 56.2 | 0.77 | 674 |
| citm_catalog | 125.7 | 119.5 | 0.95 | 659 |
| scorecard corpus | 61.4 | 44.3 | 0.72 | 690 |
| small-objects | 42.7 | 30.2 | 0.71 | 717 |
| string-heavy | 121.3 | 87.4 | 0.72 | 693 |
| twitter | 100.4 | 82.5 | 0.82 | 740 |

All six tapes are identical and the fast path is taken on all six. A second session, under heavier load, gave ratios of 0.53 to 0.90; a variant with the first word of the skip inlined, and one with the tape words written through `st64`, were within the noise. Nothing here is a claim about the final numbers.

**Why, and what that says about the plan.** Stage 1 alone runs at 660 to 740 MB/s: 7 to 20% of the scalar parser's time per byte, a cost the index-driven stage 2 has to win back. It cannot win it back from whitespace: `runT`'s byte loop for the whitespace between tokens is a single compare on compact documents
and 17% of the time on citm_catalog at most, while a lookup in the mask costs about ten operations per token. The projection of section 4.4 of the plan assumed a stage 2 whose per-token cost is a fraction of today's (the C prototype's stage 2 is 5 to 20 times cheaper per byte than the Lean loop); the Lean loop
that landed keeps the leaves, the tape writer and the stack of `runT`. **The gain is in slice S10, not in the index**: strings copied eight bytes at a time (needs the string's extent, which the index gives, and either stage-1 UTF-8 validation or an ASCII test per word), a digit-run scan and an eight-byte lexeme copy for numbers,
tape words written through `st64` into a preallocated array, a frame stack that does not allocate. Each is an equation lemma against the existing leaf, as in the plan. S8 (the switch) should land with the first of them that makes the measured ratio exceed 1 on the six corpora.

## The finding for the standard

`bv_decide` adds one axiom per theorem, which the axiom gate rejects and no independent checker can discharge, so it cannot discharge a proof here. The two non-lane-wise kernels were proved instead by an induction over the bit index with an invariant relating the carry to a small machine,
the step being a `decide` over eight Booleans; the pattern, and the finding, are written up in vbm-simd (`docs/method.md`, `docs/findings/bv-decide.md`) for the standard. The axiom gate was not relaxed.
