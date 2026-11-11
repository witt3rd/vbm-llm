#!/usr/bin/env bash
# The scorecard's mutation metric on the whole shim (split out of test_abi.sh: it was ~230 s of the 299 s Tier 1; docs/decisions/0004-tier1-speed.md). A cold machine runs it on demand;
# Tier 1 does not (test_abi.sh keeps the eleven hand-written shim mutants). Self-contained: scripts/mutants.py builds its own copies and vectors. Run: mise exec -- scripts/test_mutants.sh
set -euo pipefail
cd "$(dirname "$0")/.."
. .land/tool/lib/ran.sh   # ran_case / ran_done / must_fail (.land/tool/docs/ran-evidence.md)
ulimit -c 0   # no core; the no-record part is the preload in scripts/mutants.py (.land/tool/lib/no-crash-record.sh)
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
# the scorecard's mutation metric on the whole shim (scripts/mutants.py, the runner's operator swaps and seeded sample, in copies of the tree): every viable mutant that is not listed in
# mutants-equivalent.txt (reasoned, dated, proved where it can be: LeanJsonProofs/ShimHeader.lean) must be killed by this test. The runner fails the metric on the first survivor.
jobs=$(nproc); [ "$jobs" -le 6 ] || jobs=6
.land/tool/bin/run-scoped.sh mutants 3600 python3 scripts/mutants.py --jobs "$jobs" > "$tmp/mut.out" || { cat "$tmp/mut.out" >&2; echo "test_mutants: a mutant of the shim survives, or the equivalence list is wrong (docs/mutants.md)" >&2; exit 1; }
grep -q ' 100.0 over non-equivalent mutants' "$tmp/mut.out" && ran_case || { echo "test_mutants: the mutation score is not 100 over the non-equivalent mutants" >&2; cat "$tmp/mut.out" >&2; exit 1; }
# NEGATIVE self-tests of the metric: without the real list the listed equivalent mutants are survivors and the run FAILS, and a list entry for a mutant the tests KILL is refused (an entry cannot hide one); an entry
# with no reason, an expired one and a stale id are each rejected
: > "$tmp/none.txt"
printf '%b\n' 'abi/vbm_json.c:70:27:>:>=\tThis one is killed by the length-edge case, so the entry must be refused.\t2027-05-04' > "$tmp/hide.txt"   # a list of ONE entry, for a killed mutant
if .land/tool/bin/run-scoped.sh mutants 3600 python3 scripts/mutants.py --jobs "$jobs" --allowlist "$tmp/hide.txt" > "$tmp/mut0.out" 2>&1; then echo "test_mutants: self-test: the mutation run passed with the equivalents unlisted (it cannot fail)" >&2; exit 1; fi
neq=$(grep -cv '^#\|^$' mutants-equivalent.txt)   # one survivor per listed entry (each is in the sample: mutants.py rejects an entry that matches no mutant)
[ "$(grep -c '^SURVIVES' "$tmp/mut0.out")" = "$neq" ] && ran_case || { echo "test_mutants: self-test: expected exactly the $neq listed equivalent mutants to survive" >&2; cat "$tmp/mut0.out" >&2; exit 1; }
grep -q 'was KILLED' "$tmp/mut0.out" && ran_case || { echo "test_mutants: self-test: an entry for a killed mutant was not refused" >&2; cat "$tmp/mut0.out" >&2; exit 1; }
bad_list() {  # bad_list NAME LINE: an equivalence list with that line (after the real entries) must be rejected, with a reason, by a mutants.py that RAN
  { cat mutants-equivalent.txt; printf '%b\n' "$2"; } > "$tmp/bad.txt"
  must_fail "an equivalence list with $1" .land/tool/bin/run-scoped.sh mutants 600 python3 scripts/mutants.py --list --allowlist "$tmp/bad.txt"
}
bad_list "no reason" 'abi/vbm_json.c:70:27:>:>=\t\t2027-05-04'
bad_list "an expired entry" 'abi/vbm_json.c:70:27:>:>=\tThis entry is long past its date and must be argued again.\t2020-01-01'
bad_list "a stale id" 'abi/vbm_json.c:999:0:>:>=\tNo such mutant: the line does not exist in the shim.\t2027-05-04'
ran_done test_mutants
echo "test_mutants: ok (the whole-shim mutation run is 100 over the non-equivalent mutants and fails without the list)"
