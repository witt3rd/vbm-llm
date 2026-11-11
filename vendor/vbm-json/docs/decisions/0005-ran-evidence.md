# 0005: ran-evidence: a check that never ran must not pass

Status: accepted. Every number says local or CI. CI not run: billing (the repository is private until the runner arrives).

## The defect (an honest record)

The zero-warning self-test of `scripts/tier1.sh` compiled a file with an unused variable under `-DwarningAsError=true` and demanded that the compile FAIL.
It did not look at why it failed. On a host whose heavy-tool guard refuses `lake` outside a capped slice, the call was refused (exit 126, a message about the
guard on stderr), the self-test saw "a failure with no warning in it", and reported "negative self-test ok". The gate had not run at all: the check passed vacuously.
It was found by accident when a run under the guard printed that line with no build having happened.

The class: **a negative self-test that passes when the thing under test never ran.** Its shapes: `if CMD; then fail; fi` (any non-zero exit, a refusal or a missing tool
included, is "the check failed as expected"); `must_fail` that only asks for a non-empty stderr (a guard's refusal message is one); `out=$(CMD || true)` followed by "no
output, so nothing was found"; a test that prints SKIPPED and exits 0; a gate that exits early by a guard.

## The class fix

1. **Ran-evidence line.** Every test script and every concurrent gate of Tier 1 ends with exactly one line, on stdout:

       ran: NAME: N cases

   `NAME` is `[A-Za-z0-9_.-]+`, `N` is a positive integer: the number of checks it really evaluated (a check that was evaluated and held). Reader: `scripts/ran-evidence.sh check NAME LOG`
   (exit 0 only with at least one such line, a positive sum, and no `SKIPPED` line). `VBM_ALLOW_SKIP=1` lets a wholly skipped script through, loudly ("NOT RUN"), for a box that lacks an
   optional tool; Tier 2 requires every tool and never sets it.
2. **Producers.** Test scripts source `scripts/lib-ran.sh`: `ran_case` counts a check (file-backed, so subshells and background jobs count), `ran_done NAME` prints the line and fails
   when no case ran. Gates that print their own count (the Lean gates, the ledger checks) are read from their captured output (`scripts/ran-gates.txt`, `ran-evidence.sh check-dir`); `ran-evidence.sh gate NAME REGEX CMD...` does the same around one command (Tier 2).
   No count, a count of zero, or a failing gate fails.
3. **Enforcement.** `scripts/run-tests-parallel.sh` fails a script that exits 0 without evidence (and prints `ran: tests: N cases` for the batch); `tier1.sh` runs `scripts/ran-evidence.sh check-dir` after `bgwait`: every concurrent gate's captured log must show the count named for it in `scripts/ran-gates.txt` (read from the gate's own output) or a ran line.
   A gate added without evidence cannot pass.
4. **A refusal is a failure.** `must_fail NAME CMD...` (scripts/lib-ran.sh) is the one negative self-test helper: the command must fail, must say why, and must NOT have been refused or never run:
   exit 126, 127 or 124, or a `heavy:` guard message, fails the self-test. The zero-warning check is `scripts/check-zero-warning.sh`: the failing file's output must carry the warning's own
   diagnostic, and a clean file must pass (the control).
5. **One shared negative test:** `scripts/test_ran_evidence.sh` (Tier 1): the reader, the gate wrapper, `must_fail`, the zero-warning check (with a stub `lake` that is refused, crashes, cannot fail, or behaves)
   and the runner each FAIL on a refused, missing, skipped, silent or zero-count check, and pass the control. The relabel-attack suite attacks the mechanism (attacks 11a to 11g).

## Honest weakness

A count regex proves a count was printed, not that every case was meaningful; and a script's `ran_case` count is the checks it evaluated, not coverage. (Also quoted in the header of `scripts/ran-evidence.sh`.)

The first inline zero-warning check of `tier1.sh` is kept (the diff judge lets `tier1.sh` only gain lines); it still passes when `lake` is refused, which is why `scripts/check-zero-warning.sh` is the check and runs right after it.

## What this does not cover

Gates that are plain shell checks with their own positive controls and no tool that a guard can refuse (the forbidden-constructs scan, the import scan, the pipefail lint,
the workflow lint, `land-check`) are judged by their exit status and by their in-script controls; they print no `ran:` line. The no-crash-record library prints a SKIPPED note
when `coredumpctl` is absent (the run's own wrapper, not a gate).
