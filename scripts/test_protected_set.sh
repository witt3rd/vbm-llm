#!/usr/bin/env bash
# Tier 1: the protected-set gate can fail. In a scratch repo holding every entry of scripts/protected-paths.txt, a change that modifies, deletes,
# renames out of, or adds into any entry must exit 1 naming the path; a docs-only change and an empty change must pass; a change that loosens the
# list and touches a path it dropped is still judged by the base's list. And the real list must cover the classes the owner named and point at files that exist.
set -euo pipefail
cd "$(dirname "$0")/.."
root=$(pwd); gate=$root/scripts/protected-set.sh; list=$root/scripts/protected-paths.txt
fail() { echo "tier1: protected-set: $*" >&2; exit 1; }
# the owner's classes: each must be listed (dropping one from the list fails here)
required="VbmLlm/x VbmLlm.lean VbmLlmProofs/Ledger.lean docs/trust-ledger.md docs/decisions/0001-vbm-llm.md docs/clause-index.txt lean-toolchain mise.toml lakefile.lean lake-manifest.json AGENTS.md CODEOWNERS
.github/workflows/ci.yml scripts/tier1.sh scripts/tier2.sh scripts/LedgerGate.lean scripts/AxiomGate.lean scripts/pinned-libs.lock scripts/pinned-lib.py scripts/test_pinned_lib.sh scripts/lint-public scripts/public-banned-hashes.txt
scripts/trust-ledger-check.sh scripts/trust_ledger.py scripts/ledger-baseline.txt  scripts/lint-pipefail.sh scripts/lint-proof-eval.sh scripts/proof-eval-allow.txt
scripts/protected-paths.txt scripts/protected-set.sh scripts/land-direct scripts/land.conf scripts/land.d/post-rebase scripts/land/x scripts/regen-baselines.sh scripts/generated-paths.txt scripts/run-tests-parallel.sh scripts/test_protected_set.sh scorecard.toml"
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
entries=(); while IFS= read -r l; do l=${l%%#*}; l=${l//[[:space:]]/}; [ -n "$l" ] && entries+=("$l"); done < "$list"   # entries keep a leading "?" (may not exist yet)
clean_entries=(); for e in "${entries[@]}"; do clean_entries+=("${e#\?}"); done
paths=(); for e in "${clean_entries[@]}"; do case $e in */) paths+=("${e}fixture.txt");; *) paths+=("$e");; esac; done
# every entry names something that exists in this repository (a typo is a silent hole)
for e in "${entries[@]}"; do case $e in \?*) continue;; esac; [ -n "$(git ls-files -- "$e" | sed -n 1p)" ] || [ -n "$(git ls-files --others --exclude-standard -- "$e" | sed -n 1p)" ] || fail "entry '$e' matches no file"; done
git init -q -b main "$T/r"; cd "$T/r"; git config user.email t@t; git config user.name t; git config core.hooksPath /dev/null
mkdir docs scripts; echo doc > docs/a.md; cp "$list" scripts/protected-paths.txt
for p in "${paths[@]}"; do mkdir -p "$(dirname "$p")"; [ -e "$p" ] || echo base > "$p"; done
git add -A; git commit -qm base; base=$(git rev-parse HEAD)
check() {  # <name> <expected: pass|<path>> ; the working tree is the candidate head
  git add -A; git commit -qm "$1" --allow-empty; out=$("$gate" "$base" HEAD 2>/dev/null) && rc=0 || rc=$?
  if [ "$2" = pass ]; then [ "$rc" = 0 ] || fail "$1: a clean change was refused ($out)"
  else [ "$rc" = 1 ] || fail "$1: expected exit 1, got $rc"; grep -qxF "$2" <<<"$out" || fail "$1: '$2' not reported (got: $out)"; fi
  git reset -q --hard "$base"
}
check empty pass
echo more >> docs/a.md; echo n > docs/new.md; check docs-only pass
# the widened list is precise, not a blanket: ordinary proof files and test scripts, and near-miss names, are not the owner's
mkdir -p VbmLlmProofs; echo x > VbmLlmProofs/Round.lean; echo x > scripts/test_other.sh; echo x > scripts/task-notes.md; echo x > VbmLlms.lean; echo x > .configs; check ordinary-proofs-and-near-misses pass
for r in $required; do case " ${paths[*]} " in *" $r "*) ;; *) [[ " ${paths[*]} " == *" ${r%/*}/fixture.txt "* ]] || fail "required class '$r' is not covered by scripts/protected-paths.txt";; esac; done
n=0
for p in "${paths[@]}"; do
  n=$((n+1))
  echo edited >> "$p"; check "modify $p" "$p"
  git rm -qf "$p"; check "delete $p" "$p"
  git mv "$p" "docs/moved-$n"; check "rename out of $p" "$p"
  echo added > "docs/in-$n"; check "docs only after $n" pass
  # adding a new file under a protected directory (a rename into the set)
  case "${clean_entries[$((n-1))]}" in */) git mv docs/a.md "${clean_entries[$((n-1))]}renamed-in"; check "rename into ${clean_entries[$((n-1))]}" "${clean_entries[$((n-1))]}renamed-in";; esac
done
# loosening the list does not help: the list as of the base judges the change, and the list's own edit is reported
grep -v '^lakefile.lean$' scripts/protected-paths.txt > l.tmp && mv l.tmp scripts/protected-paths.txt; echo x >> lakefile.lean
git add -A; git commit -qm loosen; out=$("$gate" "$base" HEAD 2>/dev/null) && fail "loosening the list passed"
printf '%s\n' "$out" | grep -xF lakefile.lean >/dev/null || fail "loosened path not reported"; printf '%s\n' "$out" | grep -xF scripts/protected-paths.txt >/dev/null || fail "the list's own change not reported"
git reset -q --hard "$base"
# an unreadable or empty list, or an unknown revision, fails closed (exit 2), never open
: > e.txt; rc=0; PROTECTED_PATHS_FILE=$PWD/e.txt "$gate" "$base" HEAD >/dev/null 2>&1 || rc=$?; [ "$rc" = 2 ] || fail "an empty list did not fail closed (rc=$rc)"
rc=0; "$gate" "$base" nosuchrev >/dev/null 2>&1 || rc=$?; [ "$rc" != 0 ] || fail "an unknown revision passed"
# --superset: the list may only grow: a dropped, narrowed or emptied entry is reported, an added one and a directory that covers a file are fine
printf 'a/\nb.txt\n' > old.lst
printf 'a/\nb.txt\nc/\n' > g.lst; "$gate" --superset old.lst g.lst >/dev/null || fail "--superset: a grown list was refused"
printf 'a/\n' > d.lst; out=$("$gate" --superset old.lst d.lst) && fail "--superset: a dropped entry passed"; [ "$out" = b.txt ] || fail "--superset: the dropped entry was not named ($out)"
printf 'a/x.txt\nb.txt\n' > n.lst; out=$("$gate" --superset old.lst n.lst) && fail "--superset: a narrowed directory passed"; [ "$out" = a/ ] || fail "--superset: the narrowed entry was not named ($out)"
printf '#\n' > z.lst; if "$gate" --superset old.lst z.lst >/dev/null 2>&1; then fail "--superset: an empty new list passed"; fi
printf 'a/x.txt\n' > f.lst; printf 'a/\n' > h.lst; "$gate" --superset f.lst h.lst >/dev/null || fail "--superset: a directory above a file entry was refused"
echo "protected-set: every protected class fails (modify, delete, rename out/in), docs-only passes, a loosened list does not help, bad input fails closed, --superset names a dropped or narrowed entry: ok"
