#!/usr/bin/env bash
# The relabel-attack suite: a change to a GATE (its source, a list it reads, a baseline, tier1.sh, the lander) is judged by MECHANICAL checks, not by a human.
# The gate review (the G6 report) showed every gate can be satisfied by relabeling; each such demonstration is a small ATTACK (scripts/attacks/NN-name.sh) that the
# PROPOSED tree's gates must still REFUSE. The suite applies every attack, one at a time, in a scratch clone of the proposed tree and runs the proposed gates on it:
# an attack any gate lets through REFUSES THE CHANGE. Attacks are judged against the proposed tree itself as the new base (what could the NEXT change do?).
#   scripts/relabel-attacks.sh [--tree DIR] [--base REF] [--only ID] [--sabotage] [--no-lean]
#   scripts/relabel-attacks.sh --list | --check-wired [--tree DIR]
# --tree DIR (default .): the proposed tree (a git checkout; its HEAD plus any working-tree edits). --base REF (default origin/main): the merge-base of the change; only
#   used to check that no attack of THIS suite was dropped from the tree (the suite that judges a change is main's copy: the proposal cannot weaken its own judge).
# For each attack: a CONTROL (every gate command passes on the unattacked tree: else the gates are broken, and "refused" would be vacuous), then the attack is applied and
#   committed, then each gate command runs; the attack is REFUSED when one of them fails (and, when the attack names one, its output carries the expected words).
# --sabotage: the suite's own negative self-test: before each attack, every file the attack names in ATK_GATE_FILES is replaced by a stub that always succeeds ("a gate that
#   cannot fail"); the attack must then be NOT refused, i.e. the suite must FAIL. A suite that still passes with its gate broken is itself broken (scripts/test_relabel_attacks.sh).
# --no-lean: skip the attacks that need `lake` (ATK_LEAN=1): for the cheap Tier 1 self-test.   --list: the attack ids.   --check-wired: the lander's hooks call this suite and the diff judge.
# Exit: 0 PASS (every attack refused) | 1 FAIL (an attack passed the gates, a control failed, or an attack of the suite is missing from the tree) | 2 cannot decide.
# The LAST line is PASS/FAIL with the seconds it took. An attack file defines: ATK_DESC, ATK_GATES (commands, run in the scratch root with $ATK_BASE = the proposed commit),
# ATK_GATE_FILES, optionally ATK_LEAN=1 and ATK_EXPECT (a regex the refusal must print), and a function atk_apply (cwd = scratch root). scripts/attacks/lib.sh: helpers.
export LC_ALL=C

set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
. "$here/git-hermetic.sh"   # hermetic git (scratch repository): no ambient config, explicit identity and branch
tree=.; base=origin/main; only=; sab=0; nolean=0; mode=run
while [ $# -gt 0 ]; do case $1 in
  --tree) tree=${2:?}; shift 2;; --base) base=${2:?}; shift 2;; --only) only=${2:?}; shift 2;; --sabotage) sab=1; shift;; --no-lean) nolean=1; shift;;
  --list) mode=list; shift;; --check-wired) mode=wired; shift;; *) echo "usage: relabel-attacks.sh [--tree DIR] [--base REF] [--only ID] [--sabotage] [--no-lean] | --list | --check-wired" >&2; exit 2;; esac; done
ids() { for f in "$here"/attacks/[0-9]*.sh; do b=${f##*/}; echo "${b%.sh}"; done; }   # sorted glob (LC_ALL=C)
if [ "$mode" = list ]; then ids; exit 0; fi
tree=$(cd "$tree" && pwd)
if [ "$mode" = wired ]; then   # the suite is only a judge if the lander's hooks call it and Tier 1 tests it: removing the call is an attack too
  ok=1
  for pair in "scripts/land.d/post-tier1:relabel-attacks\.sh" "scripts/land.d/post-rebase:gate-diff-improving\.sh"; do   # hook:what it must call
    l=${pair%%:*}; re=${pair#*:}
    [ -x "$tree/$l" ] || { echo "relabel-attacks: no executable $l in the tree" >&2; ok=0; continue; }
    code=$(grep -v '^[[:space:]]*#' "$tree/$l" || true); grep -q "$re" <<<"$code" || { echo "relabel-attacks: $l does not call ${re//\\/}" >&2; ok=0; }
  done
  # and the stub must still run the pinned lander, whose hooks directory is the default
  stubcode=$(grep -v '^[[:space:]]*#' "$tree/scripts/land-direct" 2>/dev/null || true)
  { [ -x "$tree/scripts/land/bin/land-direct" ] && grep -q 'land/bin/land-direct' <<<"$stubcode"; } || { echo "relabel-attacks: scripts/land-direct does not run the pinned lander (scripts/land/bin/land-direct)" >&2; ok=0; }
  entry=$(cat "$tree/scripts/land-direct" 2>/dev/null || true)   # the entry script declares the wiring (comments included): the declaration and the hooks must agree
  { grep -q 'post-rebase runs the gate-diff judge' <<<"$entry" && grep -q 'post-tier1 runs the relabel-attack suite' <<<"$entry"; } || { echo "relabel-attacks: scripts/land-direct no longer declares the wiring contract (post-rebase runs the gate-diff judge; post-tier1 runs the relabel-attack suite)" >&2; ok=0; }
  [ -x "$tree/scripts/test_relabel_attacks.sh" ] || { echo "relabel-attacks: scripts/test_relabel_attacks.sh (the suite's negative self-test) is missing or not executable" >&2; ok=0; }
  [ "$ok" = 1 ]; exit; fi
start=$SECONDS
git -C "$tree" rev-parse --verify -q HEAD >/dev/null || { echo "FAIL relabel-attacks: $tree is not a git checkout with a HEAD" >&2; exit 2; }
# the attacks of THIS suite (the lander's copy) must all still exist in the tree: an attack is dropped by a proposal only by relabeling
missing=; for f in "$here"/attacks/[0-9]*.sh "$here"/attacks/lib.sh; do [ -e "$tree/scripts/attacks/${f##*/}" ] || missing="$missing ${f##*/}"; done
S=$(mktemp -d "${TMPDIR:-/tmp}/relabel-attacks.XXXXXX"); trap 'rm -rf "$S"' EXIT
git clone -q --shared --no-checkout "$tree" "$S/t" 2>/dev/null; cd "$S/t"
git checkout -q --detach "$(git -C "$tree" rev-parse HEAD)"
# working-tree edits of the proposed tree (the lander's tree is committed; a developer's may not be): tracked, untracked (not ignored) and deleted files
{ git -C "$tree" ls-files -co --exclude-standard -z | while IFS= read -r -d '' f; do [ -e "$tree/$f" ] && { mkdir -p "$(dirname "$f")"; cp -a "$tree/$f" "$f"; }; done; } || true
git -C "$tree" ls-files -d -z | while IFS= read -r -d '' f; do rm -f "$f"; done
# the build the Lean attacks extend (as scripts/land does): the modules' .olean/IR, NOT the executables. No attack gate runs a binary of the tree (the gates are the lander's scripts and `lake env lean --run`
# scripts/ClosureGate.lean, which read the compiled modules; `lake build VbmLlmProofs` builds the proofs library), and the executables are left out: copied on every run into a /tmp that is tmpfs (no reflink),
# nine times in one Tier 1: ~5 GB of RAM at the peak of the batch and ~2 s of system time (scripts/test_relabel_attacks.sh checks that no attack names a binary).
if [ -d "$tree/.lake" ]; then mkdir -p .lake; tar -C "$tree/.lake" --exclude=./build/bin -cf - . | tar -xf - -C .lake; fi || true
git config core.hooksPath /dev/null; git add -A; git commit -q --allow-empty -m "the proposed tree"
proposed=$(git rev-parse HEAD)
export ATK_DIR=$here/attacks
rc=0; pass=0; n=0; declare -A control=() cmsg=()
say() { echo "$*"; }
run_gate() {   # run_gate CMD: output in $S/out, exit code returned
  bash -c "$1" >"$S/out" 2>&1 </dev/null
}
for id in $(ids); do
  [ -z "$only" ] || [ "$only" = "$id" ] || continue
  ATK_DESC=; ATK_GATES=(); ATK_CONTROL=(); ATK_GATE_FILES=(); ATK_LEAN=0; ATK_EXPECT=
  . "$here/attacks/lib.sh"; . "$here/attacks/$id.sh"
  if [ "$ATK_LEAN" = 1 ] && [ "$nolean" = 1 ]; then say "skip    $id: needs lake (--no-lean)"; continue; fi
  n=$((n + 1))
  git reset -q --hard "$proposed"; git clean -fdq
  if [ "$sab" = 1 ]; then for f in "${ATK_GATE_FILES[@]}"; do neuter "$f"; done; git add -A; git commit -q --allow-empty -m "sabotaged"; fi
  export ATK_BASE; ATK_BASE=$(git rev-parse HEAD); ctl=ok
  [ "${#ATK_CONTROL[@]}" -gt 0 ] || ATK_CONTROL=("${ATK_GATES[@]}")
  for g in "${ATK_CONTROL[@]}"; do   # the control: the gate must pass on the tree as it is (one run per distinct command)
    if [ -z "${control[$g|$sab]+x}" ]; then if run_gate "$g"; then control[$g|$sab]=0; else control[$g|$sab]=1; cmsg[$g|$sab]=$(tail -3 "$S/out" | tr '\n' ' '); fi; fi
    [ "${control[$g|$sab]}" = 0 ] || { ctl="the gate fails on the unattacked tree: $g: ${cmsg[$g|$sab]:-}"; break; }
  done
  if [ "$ctl" != ok ]; then say "BROKEN  $id: $ctl"; rc=1; continue; fi
  if ! (atk_apply) >"$S/apply.out" 2>&1; then say "BROKEN  $id: the attack could not be applied to this tree (update scripts/attacks): $(tail -2 "$S/apply.out" | tr '\n' ' ')"; rc=1; continue; fi
  git add -A; git commit -q --allow-empty -m "attack $id"
  if git diff --quiet "$ATK_BASE" HEAD; then say "BROKEN  $id: the attack changed nothing"; rc=1; continue; fi
  refused=; for g in "${ATK_GATES[@]}"; do
    if ! run_gate "$g"; then
      outtxt=$(cat "$S/out"); why=0; if [ -z "$ATK_EXPECT" ]; then why=1; elif grep -Eq -- "$ATK_EXPECT" <<<"$outtxt"; then why=1; fi
      if [ "$why" = 1 ]; then refused="${g%% *}: $(grep -vxE 'PASS|FAIL' "$S/out" | grep -E -- "${ATK_EXPECT:-.}" | tail -1 | cut -c1-150 || true)"; break
      else say "note    $id: a gate failed but not for the expected reason /$ATK_EXPECT/: $g: $(tail -1 "$S/out" | cut -c1-120)"; fi
    fi; done
  if [ -n "$refused" ]; then say "REFUSED $id: $ATK_DESC -- $refused"; pass=$((pass + 1))
  else say "PASSED  $id: $ATK_DESC -- NO gate refused it"; rc=1; fi
done
[ "$n" -gt 0 ] || { echo "FAIL relabel-attacks: no attack ran" >&2; exit 2; }
if [ -n "$missing" ] && [ "$sab" = 0 ]; then say "MISSING attacks of the suite are absent from the tree:$missing"; rc=1; fi
if [ "$rc" = 0 ]; then say "PASS relabel-attacks: $pass of $n attacks refused ($((SECONDS - start)) s)"; else say "FAIL relabel-attacks: $pass of $n attacks refused ($((SECONDS - start)) s)"; fi
exit "$rc"
