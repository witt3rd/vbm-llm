# 0004: Tier 1 speed

Status: in progress (slice 1 of the Tier 1 speed task). Every number says local or CI.

## Measurement (local, 30 cores, quiet; `bash -x` with `EPOCHREALTIME` over `scripts/tier1.sh`; before any change)

Total 318 s local wall (299 s in the earlier run). Serial part about 56 s, then the parallel test scripts, whose wall time is the longest one.

| Step | local s |
|---|---|
| forbidden/import scans, lints, warning-mechanism check | ~3 |
| `lake build LeanJson LeanJsonProofs` | ~9 |
| AxiomGate `--selftest` | ~20 |
| LedgerGate `--selftest` | ~3 |
| ClosureGate `--selftest` | ~14 |
| trust ledger, `vbm-json-vectors --check --n 3` | ~3 |
| test_abi.sh | **265** (of which ~230 is the whole-shim mutation metric, run twice: once real, once with the equivalents unlisted) |
| test_wasm.sh | 46 |
| test_native.sh | 30 |
| test_bindings.sh | 13 |
| test_protected_set / land_direct / run_parallel / lint_workflows / githook | 8 / 5 / 4 / 1 / 0 |

## Slice 1: the mutation metric leaves Tier 1

`scripts/test_mutants.sh` (the whole-shim metric and its negative self-tests, moved verbatim out of `test_abi.sh`) runs in Tier 2 only (`scripts/tier2.sh`; declared in `TIER2_ONLY` in `tier1.sh`, so an undeclared script still fails Tier 1). Tier 1 keeps the eleven hand-written shim mutants, which kill the same families.

## Slice 2: delta selection

`scripts/select-tests.py` + `scripts/tests-map.txt` (with an explicit map instead of a derived import graph: this repo has 9 test scripts and one Lean library). Tier 1 runs only the tests the delta since the merge base (`TIER1_BASE`, else `merge-base origin/main HEAD`, plus uncommitted and untracked files) can affect. The Lean gates always run. Conservative: `TIER1_ALL=1` (Tier 2 sets it), no resolvable base, an empty delta, a gate-defining file (`tier1.sh`, the selector, the map, lakefile, toolchain pins) or ANY file the map does not place selects every test. A `par` test with no map line fails Tier 1 (drift). Negative tests: `scripts/test_select_tests.sh` (parser delta selects the four vector tests; shim the C tests; docs, proofs and gate-only files none; a workflow file only the workflow lint; gate-defining and unmapped files everything; fallbacks; untracked and uncommitted files; the drift check).
The full suite (all tests, including the 43,707-row vector runs) stays in Tier 2 (`TIER1_ALL=1`).

## Slice 3: one build, concurrent gates

`tier1.sh` builds `LeanJson LeanJsonProofs vbm-json-vectors LeanJson:static` once, then runs the independent gates (axiom, ledger, closure, trust ledger, vectors check) and the selected tests CONCURRENTLY (`bg`/`bgwait`: output kept, shown on failure, any failure fails Tier 1). Full set local: 93 s to 63 s.

## Slice 4: the negative self-tests of test_wasm.sh and test_native.sh run concurrently

Each mutant / corrupted-input check builds into its own files, so they run side by side (`bgj`/`joinj`; per-process `neg` and answer files). test_wasm 46 s to 23 s, test_native 30 s to 22 s alone (local).

## Slice 5: selection on the push CI

The `tier1` job checks out with `fetch-depth: 0` and sets `TIER1_BASE` to the push's `github.event.before`; a dispatch (empty `before`) or an unfetched base selects every test. Tier 2 (schedule, `TIER1_ALL=1` inside `tier2.sh`) runs the full suite and the mutation metric.

## Result

| Delta class | Tier 1 before (local) | after (local) | CI after |
|---|---|---|---|
| full set (gate-defining change) | 299-318 s | 63 s (before slice 4; 55 s landed) | 51 s (slice 3) |
| parser (`LeanJson/`, 4 vector tests selected) | 299-318 s | 46 s | 36 s (slice 4, selected tests) |
| shim (`abi/`, 4 tests) | 299-318 s | ~50 s (59 s before slice 4) | n/m |
| proofs only | 299-318 s | 25 s | n/m |
| docs only (a Tier 1-read doc) / gate script | 299-318 s | 24 s / 23 s | 31 s (slice 5, CI) |

The floor (24 s) is the build check plus the Lean gates (Axiom 20 s, Closure 14 s, run concurrently). The full suite (43,707 vector rows through the C ABI, wasm, native and bindings, plus the whole-shim mutation metric, leanchecker, nanoda) runs in Tier 2 (`TIER1_ALL=1`).

## Slice 6: the warm gate (the proof-module edit): the two Lean gates stop doing quadratic and redundant work

The scorecard's warm run (the card's `tier1_seconds_warm`: a comment appended to one proof module, then the gate in delta mode, so no test script runs) measured 91.2 s in a 2-CPU, 4 GB sandbox against the under-60 s floor. Profile (local, CPU seconds of each gate run alone; the serial prefix and the build are 3 to 5 s together):

| Gate | CPU s before | CPU s after | Why |
|---|---|---|---|
| `AxiomGate.lean --selftest` | ~62 | ~2.4 | `collectAxioms` was called once per constant (2244 of them), each call walking its own closure again: quadratic. One shared walk over the union of the closures; the verdict is the same (every constant's axioms are a subset of the union, so all pass iff the union is allowed); only a failure falls back to the old per-constant audit, to name the offenders |
| `ClosureGate.lean --selftest` | ~44 | ~5.5 | `measureClosure` scanned every imported constant (about 170,000 once `Lean` is loaded, in the interpreter) to find the theorems of `LeanJsonProofs`, four times (the run and three self-test walks). It now reads the data of the `LeanJsonProofs` modules only; the printed report is byte-identical |
| ledger gate, trust ledger, vectors check | 3, 3, 8 | unchanged | |

Nothing is cached and no gate is skipped: every gate still runs on the real tree and its negative self-test still runs in the same process. The axiom gate's self-test grew (a non-standard axiom behind another definition, and among clean constants, must be rejected by the shared walk; the walk must find `Classical.choice` behind `Classical.em`), so a walk that finds nothing cannot pass.

Result (local, a 16-core box under other load, three runs each; typical change = the card's: a comment in `LeanJsonProofs/Policy.lean`, `TIER1_BASE` = the parent): warm 15.2 / 20.1 / 20.5 s wall and 36 / 45 / 47 s of CPU, against 73 / 76 / 139 s wall and 162 / 129 / 143 s of CPU before (the 139 s run also met another lane's crash record and failed). The 2-CPU sandbox time is bounded by the CPU seconds, so it falls from 91 s to roughly a third.

Cold (local, a fresh clone with no `.lake`, `TIER1_ALL=1 TEST_JOBS=1`, one run each on a box at load 40 to 57, so wall time is noise): 731 s wall, 688 s user + 255 s sys before; 680 s wall, 563 s user + 259 s sys after. The cold run is dominated by the test scripts (645 s of it), which this slice does not touch; the gates' own share fell by about 120 CPU s.

The differential test of the axiom gate (a condition of landing slice 6, since the gate being changed is the gate that would vouch for itself): `scripts/AxiomGate.lean --selftest` keeps the old per-constant audit (Lean's `collectAxioms`, one call per constant) as an ORACLE, out of the hot path, and requires the shared walk to agree with it: per constant, the SET of axioms (not only the verdict), on planted axioms in every constant kind (axiom, definition, theorem, opaque, inductive, constructor, recursor, a definition over the quotient constants) at depth 0, 1 and 5 (a chain of definitions that mention the previous link only), directly, each alone, all together, and among clean constants; and on real constants (Tier 1: every 40th, 57 of 2244; Tier 2, `AXIOM_DIFF_FULL=1` from `scripts/tier2.sh`: all 2244, about 2 CPU minutes, and the module-data enumeration of the constants equals the old filter over every imported constant, so the printed count is the same). The differential shows it can fail: four deliberately broken walks (no constructors, no values, no types, nothing) must each be caught on the fixtures in the same run, and the oracle must itself flag every planted constant (a fixture that plants nothing fails). Cost: about 2 to 3.5 CPU s more on the warm gate.

