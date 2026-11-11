# Change 3: fuse parsing and tape emission: the decomposition of the refinement proof (a PLAN; nothing here is implemented)

Status: IN PROGRESS (slices landed are listed in `docs/perf/fuse-log.md`). Design note, written after slices 1 and 2 of `docs/perf/results.md` (strings without a heap object per character; the cheap tape pass). Numbers quoted from there are local; the gains below are estimates (Amdahl on `docs/perf/profile.md`), not measurements. Owner decision needed before slice F0: the closure gate's entry point moves (see "What the gates see").

## 1. Goal and the statement

Today `parseTape a = match parseFast a with | .ok v => encode (encValue v) | .error e => ...`: the parser builds the whole `Value` (one object per node, digit lists, reversed element lists) and then a second traversal flattens it. After slices 1 and 2 the remaining cost on number- and node-heavy documents is that `Value` (canada 51 MB/s, small-objects 46, scorecard corpus 64, all local x, against Python's C `json` at 97 to 117 on those corpora and serde_json at 91 to 331).

The fused function `parseTapeFast : ByteArray → ByteArray` runs the loop of `run` but writes the tape and the text region as it reads, and never builds a `Value`. The one theorem the whole plan exists for:

    theorem parseTapeFast_eq (a : ByteArray) : parseTapeFast a = parseTape a

(`parseTape` as it is now, the composition with `parseFast`; the bytes, error words included). With `parseFast_eq_parse` it follows that the tape of the exports is the tape of the REFERENCE parser's value. `Value`, `parseFast`, `run` and every existing theorem stay exactly as they are (`parseFast` stays the oracle and the entry of the proved claims); `parseTapeFast` is a second loop proved against the first.

## 2. Design of `parseTapeFast` (what the proof has to be about)

State of the loop (`run`'s, with the `Value` and the element lists replaced):
- `tb : TapeBuf` (tape, text), unshared (the in-place path; the lesson of slice 2: read the buffers apart before using them).
- the explicit stack `FStack`: `nil | arr (at_ : Nat) (n : Nat) (rest)` | `obj (at_ : Nat) (n : Nat) (rest)`: the word index of the container's header and the number of elements (members) written so far. No key waits on the stack any more: the key is written to the tape the moment it is read.
- `ret : Bool` as in `run`: a value starts at `i`, or one has just been completed.

Differences from `run` that need proof:
1. A container's header has `len` (the count) and `aux` (subtree words) known only at the close: the node is pushed at the open with placeholders, and `close` patches both words (`setWord at_ ...` twice; today only `aux` is patched, the count is `xs.length` known at the open). The count rides in the frame.
2. A number is not parsed into digit lists: `scanNum a i` finds the end index `j` and `pushNumLex` appends the canonical lexeme to the text (sign, digits, `.digits`, `e`, `-` kept, `+` dropped, `E` written `e`) copying digit bytes from the input.
3. A string is not built with `String.push`: a plain run is copied from the input; an escape appends `encodeUtf8 scalar`.
4. Errors: the result bytes are `status` and two zero words; the partial tape is discarded (the reference reports the error code of the first failure; the loop's error discipline is the same as `run`'s, so the error branch is a copy of `run`'s).
5. Depth: the budget `d` is unchanged.

## 3. The proof, in slices (each a commit of at most ~150 production lines, i.e. `LeanJson/`; the proof lines are not under that budget but each slice stays reviewable)

Proof shape: the simulation of `run_sound`/`parseFast_eq_parse` again (`LeanJsonProofs/Fast.lean`, `kont` as the defunctionalised continuation), with the invariant "the tape built so far is `encValue` of the finished values", instead of "the value built so far". Two statements by induction on the fuel: `runT_val` (a value starts at `i`: `runT` returns the tape of what `run` returns, handed to the continuation) and `runT_ret` (a value was just completed).

| slice | content | theorem(s) (statements) | est. production lines | depends on |
|---|---|---|---|---|
| F0 | The layout as a pure function: `encode : Value → (words : List UInt64) × (text : ByteArray)` defined from the `Value` WITHOUT the stateful `TapeBuf` (head and aux words computed by subtree size and text offsets by a running prefix), and `TapeBuf` equals it: `encValue v s` = `s` extended by `encode v` relocated by `s.words`/`s.text.size`. This is the layout theorem the `tape-encode-decode` ledger claim wants. Spec side only (`LeanJsonProofs`, no production code), the ledger claim gets lemmas. | `encValue_eq_encode (v s) : (encValue v s).tape.data = s.tape.data ++ words (encode v s.text.size)` and the text region; `close_eq : (… ).close at_` is `setWord` of the subtree size | 0 | slice 2 (`pushWordFast_eq`, `pushNumber_eq`, landed or landing) |
| F1 | Number scanning: `scanNum a i : Option Nat` (the end index) with `pushNumLex tb a i j` writing the canonical lexeme from the input bytes. Statement: for every `i`, `scanNum a i = (parseNumA a i).map (·.2)` and, when `parseNumA a i = some (n, j)`, `pushNumLex b a i j = pushNumber b n` (so `= b ++ printNumber n`). | `scanNum_eq`, `pushNumLex_eq` | ~50 | F0 not needed; `FastLeaf.lean` (`parseNumA_eq`, `parseNumA_adv`) |
| F2 | String scanning that writes the text: `scanStr a i tb : Option (Nat × ByteArray)` = reads like `strLoop` but appends UTF-8 bytes (a plain run copied with `copySlice`, an escape through `encodeUtf8`). Statement: if `strLoop a i s = some (s', j)` then `scanStr a i b = some (j, b ++ (s'.toUTF8 minus s.toUTF8's prefix))`, i.e. `b ++ s.toUTF8 ↦ b ++ s'.toUTF8`. | `scanStr_eq`; needs `String.toUTF8 (s.push c) = s.toUTF8 ++ ofList (encodeUtf8 c.toNat)` (Init may have it only under another name: see Risks) | ~60 | slice 1 (`plainAscii`, `strLoop_step`) |
| F3 | The tape frame and `closeNode`: `FStack`, and `closeArr tb at_ n`/`closeObj`: patch `head` (kind, n) and `aux` (words from `at_`). Statement: closing after the children `vs` were written equals `encValue (.arr vs)`: `closeArr (encList vs (open at_ s)) at_ vs.length = encValue (.arr vs) s`. Also the member form. | `closeArr_encList`, `closeObj_encMembers` | ~30 | F0 |
| F4 | `runT`, the loop itself, for scalars only (no containers yet, the stack stays `nil`): fuel, `ret`, whitespace, literals, strings and numbers through F1/F2. Statement: on a text that is one scalar value, `parseTapeFast = parseTape`. | `runT_scalar_eq` | ~60 | F1, F2 |
| F5 | Containers: the open/close/comma branches of `runT` with the `FStack`; `n` incremented per element. The simulation invariant `Inv st fst tb` (relation between `run`'s `Stack` and the fused `FStack` + tape: for each open frame the children so far are in the tape after `at_`, in order, as `encList (acc.reverse)`). The heart: one lemma per branch of `run` (`runT_open_arr`, `runT_comma_arr`, `runT_close_arr`, the object versions with the key written at read time: `encMembers` writes the key node `leaf kindStr k` then the value). | `runT_val`, `runT_ret` (the pair, by induction on fuel, like `run_val`/`run_ret`) | ~60 (the object keys and the depth budget are the bulk) | F3, F4 |
| F6 | `parseTapeFast` and the equation. The ABI export `vbm_json_parse_tape` switches to `parseTapeFast`; `parseTape` stays as the spec (no longer reachable from the export). | `parseTapeFast_eq`; ledger claim `tape-encode-decode` gains `partly`/`proved` with `parseTapeFast_eq` + F0's layout theorem | ~10 | F0, F5 |
| F7 | Gates and ledger (owner-protected files, deliberate): `scripts/closure-entries.txt` (`LeanJson.parseTape` is replaced by or joined with `LeanJson.parseTapeFast`), `scripts/closure-baseline.txt`, the ledger entry; the closure gate's negative self-tests stay. Then the same bench as `docs/perf/bench.sh`, before/after, in `docs/perf/results.md`. | none (gates) | 0 | F6 |

F1, F2 and F3 are independent of each other and can land in any order (each is dead code until F4 uses it; dead code is not an export so the closure gate does not see it, and the unreached definitions are lemmas of F4). The production size is ~300 lines in total; the proofs are the bulk, estimated 1000 to 1400 lines (`Fast.lean` + `FastLeaf.lean` + `FastFuel.lean` are about 1270 lines; F5 is the part comparable to `run_sound`, 230 lines there).

## 4. Order, and why

F0 first: it is pure proof, needs nothing from the parser, and it IS the layout theorem the project wants regardless of fusing (it also strengthens slice 2). F1, F2, F3 next, smallest first (F3 then F1 then F2). F4 proves the loop skeleton on scalars before containers exist, so the first red run is cheap. F5 is the big one: if it needs more than one slice, split by branch (arrays first, objects as F5b). F6, F7 last. Each slice keeps every vector (the 43,426 + bignum + bindings + wasm of Tier 1), `parseFast_eq_parse`, and adds no axiom; the export is switched only in F6, when the equation is already proved, so no intermediate commit has an unproved export.

## 5. Risks

1. **String UTF-8 bridge (F2), medium.** `String.toUTF8 (s.push c)` equalling `s.toUTF8 ++ encodeUtf8 c` needs the Init lemmas for `String.toUTF8`/`String.push`; in Lean 4.35 `String` is a structure over `ByteArray` and these may exist (`String.toByteArray`, `String.push`'s data lemma) but this was not checked here. Fallback: represent the text region as the concatenation of `encodeUtf8` of the decoded scalars (the reference's own definition via `Print.encodeUtf8`, whose correctness `utf8_encode` is already proved) and show `s.toUTF8 = ⟨(s.toList.flatMap encodeUtf8…)⟩` once.
2. **Subtree words and text offsets under relocation (F0/F3), medium.** `aux` of a container is relative (words), of a leaf absolute (text offset): the invariant must carry the prefix sizes; mixing them up is the likeliest source of a long proof. F0 exists to settle it on the spec side first.
3. **The count in the header (F3/F5), low to medium.** Today the count is `xs.length` at the open; fused, it is a counter in the frame and the header is patched at close. The `setWord` twice must commute with children writes (they only append after `at_ + 2`): one lemma, `setWord` leaves other words alone.
4. **Error words (F4/F5), low.** The partial tape is dropped on error; the proof must show the error branch returns `run`'s error code at the same step (copy of the case analysis).
5. **Number canonicalisation (F1), low.** `E` to `e` and dropping `+` are the only rewrites; `pushNumLex_eq` is a case split on the same shape as `parseNumA`; the ABI tests (`scripts/test_abi.sh`) already compare the lexeme with the reference's canonical form.
6. **Performance does not materialise, low-medium.** The estimate (small-objects 46 to ~110-130, canada 51 to ~120-150, scorecard corpus 64 to ~120-140 MB/s, local) is Amdahl on the profile: it assumes the `Value` allocation/free (about 30 to 45% of those documents), the digit lists and the second traversal go away. Measure after F4 on scalar-heavy input (a document of numbers) before investing in F5: if F4's loop is not clearly faster per number than `run` + `encValue`, stop.
7. **Proof size and the Tier 1 time.** About 1000 to 1400 proof lines add Lean build time to every Tier 1 run; the Tier 1 speed work in flight (test selection) bears on this.

## 6. What the gates see

- Axiom gate: no new axiom (`propext`, `Classical.choice`, `Quot.sound` only); the proofs use the same tactics as `Fast.lean`.
- Closure gate: the entry `LeanJson.parseTape` (the export) is replaced by `LeanJson.parseTapeFast` in F7, so the executed set changes: `Value`-building code (`run`, `Stack`) stays reachable through `parseFast` (kept as its own entry), the digit-list leaves stay reachable the same way; the specified share must stay 100% (everything is in `LeanJson/` and counted as spec). The baseline file is restated in F7, deliberately, as a protected-set change.
- Trust ledger: no new boundary (no C, no extern); nothing to add. The C shim is untouched (the tape layout does not change: the bytes are identical by `parseTapeFast_eq`).
- Vectors, bindings, wasm: unchanged expectations; they are the end-to-end check that F6 changes nothing observable.
