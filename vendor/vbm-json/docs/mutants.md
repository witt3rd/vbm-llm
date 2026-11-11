# Mutation survivors: the list, the kills and the equivalents

The VBM scorecard (card v5, subject 3d95e74f) reports `construction.mutation_score` 61.3 against a floor of 100. This file is the finding behind that number, one row per surviving mutant. Every number below is
**LOCAL** (measured on this machine with `scripts/mutants.py`, the runner's own procedure in copies of the tree); the card's own number is only recomputed by the scorecard.

## What the metric is (read from the runner, not assumed)

- **Which code is mutated:** only `abi/vbm_json.c` (the adapter's `[mutation] files`: the trusted C edge of the ABI, T09). Not `LeanJson/`: the Lean specification and fast parser are the *other* metric, `verified.non_vacuity` (20 seeded swaps in `LeanJson/Parse.lean`
  that must break a proof; v5: 8 viable, 8 killed, 12 not viable, 100%). So the 12 survivors are **not** parser branches, printer, policy bounds or fast-parser paths: all twelve are in the 76 lines of C that move bytes.
- **How a mutant is made:** every operator token in the file outside comments (`== != <= >= < > && || + -`; `//` tails and lines starting `*`, `/*`, `#` are skipped, a `/* */` tail is not) is a site, 32 of them. One swap (`==`->`!=`, `<=`->`<`, `&&`->`||`, `+`->`-`, ...) is applied at a time to a copy of the tree; `mutants = 50`, `seed = 1`, so all 32 are used.
- **What kills:** the adapter's `kill_cmd` recompiles `tests/abi_test.c` with the mutated shim (does not build: exit 99, not viable) and runs it on the generated vectors; any non-zero exit (a crash or a timeout too) kills. The score is killed / (killed + survived) over viable mutants.
- **Reproduced:** `mise exec -- scripts/mutants.py` at main 3d95e74: 32 sites, 19 killed, 12 survived, 1 not viable, **61.3 (LOCAL)**, the same twelve survivors as the card (the card lists them without the column; two `&&` on line 53 and three on line 54 differ only by it).

## The survivors and their verdicts

Line numbers in the table below are those of the shim before the freestanding change (which added about 30 lines at the top: every id moved down; `mutants-equivalent.txt` carries the current ids).

Ids are `file:line:col:old:new` (line 1-based, column 0-based). "Before" is main 3d95e74; the killing test is in `tests/abi_test.c` unless it says otherwise.

| # | id | change | class | verdict | how |
|---|----|--------|-------|---------|-----|
| 1 | `abi/vbm_json.c:49:95:-:+` | the hyphen of the comment `/* little-endian host */` | comment (runner artefact) | **equivalent** | a comment; the runner cuts only `//` tails. In `mutants-equivalent.txt` |
| 2 | `:34:27:>:>=` | `len > LEAN_MAX_SMALL_NAT` becomes `>=` | length bound | **killed** | `fault()`: an input of exactly `LEAN_MAX_SMALL_NAT` bytes passes the check, one more is `VBM_JSON_ARG` (the real allocation of that size aborts the process in the Lean runtime, T09, so the allocation and the copy are stubbed in the second copy of the shim) |
| 3 | `:37:36:+:-` | `sizeof(size_t) + sizeof(void *)` becomes `-`: the "opts too old" check never fires | API argument | **killed** | `allocator()`: opts of every size 0, 4, .., 12 are `VBM_JSON_ARG` |
| 4 | `:40:17:\|\|:&&` | `!al->alloc \|\| !al->free` becomes `&&`: one missing function is accepted | API argument | **killed** | `allocator()`: an allocator with only `alloc`, and one with only `free`, are `VBM_JSON_ARG` (the old test had both missing) |
| 5 | `:53:18:&&:\|\|` | the error result's guard `n == 24 && nw == 0 && nt == 0` | defensive check of the Lean export's result | **killed** | `fault()`: status 1 with `n = 32`, with `nw = 1`, with `nt = 1` is `VBM_JSON_INTERNAL` |
| 6 | `:53:29:&&:\|\|` | the same guard, second `&&` | defensive check | **killed** | same cases |
| 7 | `:54:27:&&:\|\|` | the ok guard `status == 0 && ...` | defensive check | **killed** | `fault()`: an unknown status (3) with a consistent header is `VBM_JSON_INTERNAL` |
| 8 | `:54:39:-:+` | `nw <= (n - 24) / 8` becomes `(n + 24) / 8` | defensive check (overflow guard) | **equivalent, proved** | `LeanJsonProofs/ShimHeader.lean`, `plus_equiv` |
| 9 | `:54:49:&&:\|\|` | the ok guard, second `&&` | defensive check | **killed** | unknown status with consistent header |
| 10 | `:54:55:<=:<` | `nt <= n` becomes `nt < n` | defensive check (overflow guard) | **equivalent, proved** | `ShimHeader.lean`, `lt_equiv` |
| 11 | `:54:60:&&:\|\|` | the ok guard, third `&&`: the exact-sum test is bypassed | defensive check | **killed** | `fault()`: words, text and bytes that do not add up (48 bytes for one word, 24 for one word, 42 and 44 for 2 + 3) are `VBM_JSON_INTERNAL` |
| 12 | `:55:23:-:+` | `size_t total = n - 24` becomes `n + 24`: 24 bytes more are asked of the embedder and read past the result | memory size | **killed** | the block asked of the embedder is exactly `8 * words + text` (8 for an empty tape), checked through a counting allocator on a real parse (`allocator()`) and on crafted results (`fault()`) |

**After (LOCAL, `scripts/mutants.py`, same procedure): 32 sites, 28 killed, 3 survived, 1 not viable. Raw 90.3; 100.0 over the non-equivalent mutants (the three survivors are the three equivalents above: one comment and two proved).** 12 survivors in 3 kills-families: 9 killed, 3 equivalent (2 of them proved).

**The scorecard's own runner** (its `run_mutation` driven in its bubblewrap sandbox over this commit's tree, `MemoryMax=8G`; not a card of the scorecard's own run): main 3d95e74: **61.3** (19 of 31, the 12 survivors); this branch with the unmodified adapter: **90.3** (28 of 31, the 3 equivalents survive); this branch with the scorecard adapter that reads `mutants-equivalent.txt`): **100.0** (28 killed, 3 equivalent excluded, 0 rejected entries).

### The equivalents

- **#1** is a mutation of a comment. The runner's rule (`comment = "//"` in the adapter) does not recognise `/* ... */` tails; setting the adapter's comment marker to `"/*"` would remove the site (a scorecard change, awaiting the owner).
- **#8 and #10** are guards against `size_t` wraparound in `24 + 8 * nw + nt == n`. The exact-sum conjunct decides alone for every `n` below 2^62 (the byte size of a Lean array in memory; the runtime's own bound is 2^63): the looser bound `(n + 24) / 8` and the
  stricter `nt < n` accept exactly the same headers. `ShimHeader.lean` states the check on `Nat` with the modulo 2^64 spelled out and proves both for all `nw`, `nt` (a `Nat`, not only below 2^64: a stronger statement), and carries its own negative: `ltWords_not_equiv`,
  the killed neighbour `nw < (n - 24) / 8` (row 54:33) is shown NOT equivalent by the header of two words and no text.
- **Nothing is hidden:** `mutants-equivalent.txt` (id, reason of at least 20 characters, expiry date) is read by `scripts/mutants.py`: an entry with no reason, past its date, matching no mutant (the code moved) or naming a mutant the tests kill is an error, and the score is computed over the mutants not listed.
  The scorecard itself does not read this file yet (see "To do").

## The gate and its negatives

`scripts/test_abi.sh` (Tier 1, already declared) now also: runs `tests/abi_test.c` with the fault-injection and API cases above; builds **eleven** hand-made mutants into copies of the tree and requires each to fail (the two it had, and one per killed family: length edge, opts size, one allocator function missing, both error-header
guards, the ok-header status/sizes guards, block size); runs `scripts/mutants.py` and requires 100 over the non-equivalent mutants; and runs it again with a list that is only an entry for a *killed* mutant, which must fail with the three survivors and the refusal of the entry. A list entry with no reason, an expired one and a stale id
are each rejected. "Re-introduce a killed mutant, the suite fails": done by hand too (`len >= ...` in `abi/vbm_json.c`: `test_abi.sh` exits 1, LOCAL).

## The lesson (class level)

All 12 survivors are in **boundary code that the specification does not generate inputs for**:

- **8 of 12 (rows 5-7, 9, 11, plus 8 and 10) are defensive checks on the Lean export's result.** The generated vectors are produced by the reference and drive the shim only through a *correct* export, whose header is always exact, so the checks (`status`, sizes, the exact sum) are never false on any vector: a mutant that deletes one is invisible by construction. Vectors cannot reach a branch whose precondition the verified code rules out. What reaches it is **fault injection** (a fake export returning a crafted header), which is what the new test does by compiling the shim a second time under other names inside the test. The two that remain are equivalent: guards that are redundant with another conjunct.
- **3 of 12 (rows 2-4) are API contract edges** (`opts->size`, the allocator, the length bound): the rows exercise `buf, len` only. The spec is silent about argument misuse because the vectors are *about JSON*; the ABI header states these contracts and nothing generated tests them.
- **1 of 12 (row 12) is a size that no test compared with the spec**: the test checked that the allocator is used once and freed with the same size, not that the size is the tape's.
- **1 is a runner artefact** (a `/* */` comment).

So the mutants did not find a gap in the Lean proofs; they found that the **spec layer ends at the Lean export**, and the C that wraps it has contracts (argument validation, result-header validation, exact sizes) that are specified only in prose (`include/vbm_json.h`, T09). The durable fix is the one the trust ledger already plans (slice 2: the tape layout in Lean with encode/decode, so that the header is *constructed* and *checked* by one verified definition, and the C holds only the copy); until then, fault injection is the only generated-or-not evidence for these branches.
The test is hand-written C and is counted as such by the scorecard (hand-written tests); `scripts/mutants.py` and the cases are the stopgap, a generated driver for the scorecard is the replacement.

## To do (not in this slice)

- The scorecard reads `mutants-equivalent.txt` (an optional adapter key `equivalent`; an entry counts only with a reason, an unexpired date against the COMMIT's date, and a surviving mutant; negative self-tests in `test_scorecard.sh`). The card says 100 only once it is recomputed on a pinned commit at or after ce1b5e2: until then the published card says 61.3 (v5) and any number here is local.
- `verified.non_vacuity` samples 20 of 173 sites of `LeanJson/Parse.lean` (8 viable): a larger sample (the adapter allows 200) is the real test of the proofs against the fast parser; its survivors would be the spec findings this file does not have.
- `tests/abi_test.c`'s second copy of the shim relies on its path (`../abi/vbm_json.c`) and on the scorecard's compile line; if the harness moves, move both.

## Update after the printer rounds (the shim's line numbers moved; eight survivors on main)

The seeded sample of 50 changed when the shim grew (65 sites now): the two proved equivalents moved from line 90 to line 94 (`mutants-equivalent.txt` carries the current ids, `94:39:-:+` and `94:55:<=:<`); the comment mutant is not in the sample any more, so its entry is gone (it comes back if the sample picks it). Six survivors were test gaps of the printing entry points, closed in `tests/abi_test.c` (`allocator`), oracle the real library through the C ABI: `129:36` (opts too short for printing are ARG, on both entry points), `132:22` (an allocator missing one function is ARG for printing), `162:52` (a tape with more words, or more text, than the runtime holds is ARG; the mutant goes on to allocate and ends the process), and `162:19`, `162:67`, `178:27` (the limit is exact: a size AT the limit is not refused with ARG, it goes on to an allocation of about 2^63 bytes, which ends the process; observed in a child process, `at_limit_returns_arg`). `test_mutants.sh` now expects one survivor per listed entry. Local run, `--jobs 1`: 50 mutants of 65 sites, 46 killed, 2 survived (both argued equivalent), 2 not viable: 100.0 over the non-equivalent mutants (`--jobs 6` fails in the setup in this environment, in the copies' `lake build`; one job runs).
