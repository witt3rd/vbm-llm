#!/usr/bin/env bash
# Tier 1: the relabel-attack suite (scripts/relabel-attacks.sh) judges a gate change by mechanical checks, and it can FAIL. On this tree:
#  (1) every attack is REFUSED by the tree's own gates (PASS, exit 0), except the Lean ones (Tier 2 and the lander run those);
#  (2) SABOTAGE (the negative self-test): with the gate each attack relies on replaced by a stub that always succeeds, every attack PASSES the gates and the suite FAILS (exit 1, no REFUSED line);
#  (3) a gate that fails on the UNATTACKED tree is BROKEN, not "refused" (a control), an attack of the suite missing from the tree FAILS, and the lander must call the suite and the diff judge (--check-wired).
# Every attack runs in its own scratch clone, so the runs are independent: they run in parallel and the slowest sets the wall time.
set -euo pipefail
cd "$(dirname "$0")/.."
[ "$(bash -c '. scripts/git-hermetic.sh; echo loaded')" = loaded ] || { echo "tier1: scripts/git-hermetic.sh does not load (a stub that exits?)" >&2; exit 1; }
. scripts/git-hermetic.sh   # hermetic git: no ambient config, explicit identity and branch
fail() { echo "tier1: relabel-attacks: $*" >&2; exit 1; }
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
suite=$(pwd)/scripts/relabel-attacks.sh
mapfile -t all_ids < <("$suite" --list); [ "${#all_ids[@]}" -ge 30 ] || fail "the suite lists fewer than 30 attacks (${#all_ids[@]})"
# the attacks that need `lake` (ATK_LEAN=1: they re-run a Lean gate, about a minute) are not run in Tier 1 (velocity): Tier 2 runs the whole suite (scripts/tier2.sh) and so does the lander when a gate-defining file is touched
ids=(); for i in "${all_ids[@]}"; do grep -q '^ATK_.*ATK_LEAN=1' "scripts/attacks/$i.sh" || ids+=("$i"); done
[ "${#ids[@]}" -lt "${#all_ids[@]}" ] || fail "no attack needs lake: the Lean attack is gone"
# the suite copies the compiled modules of its tree, not the executables: no attack gate runs one; this pins that, so a future attack that needs a binary fails HERE, not silently there
! grep -rq '\.lake/build/bin' scripts/attacks || fail "an attack names a binary under .lake/build/bin: scripts/relabel-attacks.sh does not copy the executables into its scratch tree"
# a standalone copy of the tree (tracked and untracked files, one commit) for the runs that damage it
mk_tree() { local d=$1; mkdir -p "$d"; git ls-files -co --exclude-standard -z | tar --null --ignore-failed-read -T - -cf - 2>/dev/null | tar -xf - -C "$d"
  git -C "$d" init -q -b main && git -C "$d" config core.hooksPath /dev/null && git -C "$d" add -A && git -C "$d" commit -q -m tree; }
one() { local mode=$1 id=$2 rc=0; if [ "$mode" = sab ]; then "$suite" --sabotage --only "$id" >"$T/$mode.$id.out" 2>&1 || rc=$?; else "$suite" --only "$id" >"$T/$mode.$id.out" 2>&1 || rc=$?; fi; echo "$rc" >"$T/$mode.$id.rc"; }
export -f one; export T suite
# the Lean attack and the slow self-test attacks first (the slowest set the wall time), then the rest; 6 at a time
order=(); for i in "${ids[@]}"; do case $i in 07*) order=("$i" "${order[@]}");; *) order+=("$i");; esac; done
mk_tree "$T/ctl"; printf '#!/usr/bin/env bash\nexit 1\n' > "$T/ctl/scripts/gate-diff-improving.sh"; git -C "$T/ctl" commit -qam "a gate that always fails"
mk_tree "$T/miss"; git -C "$T/miss" rm -q scripts/attacks/02a-ledger-proved-lowered.sh; git -C "$T/miss" commit -qm "an attack dropped"
mk_tree "$T/unwired"; sed -i '/relabel/d' "$T/unwired/scripts/land.d/post-tier1"; git -C "$T/unwired" commit -qam "the post-tier1 hook without the suite"
mk_tree "$T/nodiff"; sed -i '/gate-diff-improving/d' "$T/nodiff/scripts/land.d/post-rebase"; git -C "$T/nodiff" commit -qam "the post-rebase hook without the diff judge"
mk_tree "$T/nostub"; printf '#!/usr/bin/env bash\nexit 0\n' > "$T/nostub/scripts/land-direct"; git -C "$T/nostub" commit -qam "an entry script that does not run the pinned lander"
jobs=$(nproc); [ "$jobs" -le 6 ] || jobs=6   # as many as there are CPUs, at most 6: each run copies the tree, and a 2-CPU sandbox with a memory cap must not hold six
( for m in real sab; do for i in "${order[@]}"; do echo "$m $i"; done; done ) | xargs -P "$jobs" -L 1 bash -c 'one "$0" "$1"'
rc_ctl=0; "$suite" --tree "$T/ctl" --only 02a-ledger-proved-lowered >"$T/ctl.out" 2>&1 || rc_ctl=$?
rc_miss=0; "$suite" --tree "$T/miss" --only 02b-ledger-open-raised >"$T/miss.out" 2>&1 || rc_miss=$?
for id in "${ids[@]}"; do
  [ "$(cat "$T/real.$id.rc")" = 0 ] && [[ "$(tail -1 "$T/real.$id.out")" == "PASS relabel-attacks: "* ]] && grep -q "^REFUSED $id" "$T/real.$id.out" && ! grep -qE '^(PASSED|BROKEN|MISSING)' "$T/real.$id.out" || { cat "$T/real.$id.out" >&2; fail "the attack $id passes this tree's own gates (or its control is broken)"; }
  [ "$(cat "$T/sab.$id.rc")" = 1 ] && [[ "$(tail -1 "$T/sab.$id.out")" == "FAIL relabel-attacks"* ]] && ! grep -q '^REFUSED' "$T/sab.$id.out" && grep -q "^PASSED  $id" "$T/sab.$id.out" || { cat "$T/sab.$id.out" >&2; fail "$id: with its gates broken the suite still passes: it cannot fail"; }
done
[ "$rc_ctl" = 1 ] && grep -q '^BROKEN  02a-ledger-proved-lowered: the gate fails on the unattacked tree' "$T/ctl.out" || { cat "$T/ctl.out" >&2; fail "a gate that fails on the unattacked tree counted as refusing an attack (a vacuous refusal)"; }
[ "$rc_miss" = 1 ] && grep -q '^MISSING' "$T/miss.out" || { cat "$T/miss.out" >&2; fail "an attack dropped from the tree did not fail the suite"; }
"$suite" --check-wired || fail "the lander's hooks do not call the relabel-attack suite and the diff judge"
if "$suite" --check-wired --tree "$T/unwired" 2>/dev/null; then fail "--check-wired passes a post-tier1 hook that no longer calls the suite"; fi
if "$suite" --check-wired --tree "$T/nodiff" 2>/dev/null; then fail "--check-wired passes a post-rebase hook that no longer calls the diff judge"; fi
if "$suite" --check-wired --tree "$T/nostub" 2>/dev/null; then fail "--check-wired passes a scripts/land-direct that does not run the pinned lander"; fi
echo "relabel-attacks: ${#ids[@]} attacks: each is refused by the tree's own gates and, with its gate stubbed, passes them and fails the suite; a broken gate, a vacuous control, a dropped attack and an unwired hook or stub all FAIL: ok"
