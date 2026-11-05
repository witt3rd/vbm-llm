#!/usr/bin/env bash
# The protected-set gate: does the change <base>..<head> touch a path that waits for the owner?
#   scripts/protected-set.sh <base> <head>     exit 0: touches none; exit 1: prints each touched protected path; exit 2: cannot decide (fails closed)
# The list is scripts/protected-paths.txt as of <base> (the head cannot loosen the list it is judged by; the list file is itself listed, so a change to it
# is reported too). Without a copy at <base> (the commit that introduces the gate) the working-tree copy next to this script is used.
# The diff is taken from the merge base, with renames split into a deletion and an addition, so moving a file out of (or into) the set is reported.
# PROTECTED_PATHS_FILE overrides the list (self-test only).
#   scripts/protected-set.sh --superset <old-list-file> <new-list-file>   exit 0: every entry of the old list is still protected by the new one (an exact path is covered by an equal entry or a
#                      directory above it; a directory by an equal entry or a directory above it); exit 1: prints the dropped entries. Used by scripts/gate-diff-improving.sh --suite-judged.
set -euo pipefail
covers() {  # covers ENTRY PATH-OR-DIR: does the list entry protect it (equal, or a directory prefix)
  local e=$1 p=$2
  [ "$p" = "$e" ] || { [ "${e: -1}" = "/" ] && [ "${p#"$e"}" != "$p" ]; }
}
read_entries() {  # one entry per line, "#" comments, a leading "?" dropped
  local l; while IFS= read -r l || [ -n "$l" ]; do l=${l%%#*}; l=${l//[[:space:]]/}; l=${l#\?}; [ -n "$l" ] && echo "$l"; done < "$1"
}
if [ "${1:-}" = --superset ]; then
  old=${2:?usage: protected-set.sh --superset <old> <new>}; new=${3:?usage: protected-set.sh --superset <old> <new>}
  mapfile -t ne < <(read_entries "$new"); [ "${#ne[@]}" -gt 0 ] || { echo "protected-set: the new list is empty" >&2; exit 1; }
  dropped=0
  while IFS= read -r o; do
    ok=0; for e in "${ne[@]}"; do covers "$e" "$o" && { ok=1; break; }; done
    [ "$ok" = 1 ] || { echo "$o"; dropped=1; }
  done < <(read_entries "$old")
  exit "$dropped"
fi
base=${1:?usage: protected-set.sh <base> <head>}; head=${2:?usage: protected-set.sh <base> <head>}
here=$(cd "$(dirname "$0")" && pwd)
mb=$(git merge-base "$base" "$head") || { echo "protected-set: no merge base for $base $head" >&2; exit 2; }
if [ -n "${PROTECTED_PATHS_FILE:-}" ]; then list=$(cat "$PROTECTED_PATHS_FILE")
elif list=$(git show "$base:scripts/protected-paths.txt" 2>/dev/null); then :
else list=$(cat "$here/protected-paths.txt"); fi
entries=(); while IFS= read -r l; do l=${l%%#*}; l=${l//[[:space:]]/}; l=${l#\?}; [ -n "$l" ] && entries+=("$l"); done <<<"$list"
[ "${#entries[@]}" -gt 0 ] || { echo "protected-set: the protected list is empty (refusing to pass everything)" >&2; exit 2; }
hit=0
while IFS= read -r -d '' p; do
  for e in "${entries[@]}"; do
    if [ "$p" = "$e" ] || { [ "${e: -1}" = "/" ] && [ "${p#"$e"}" != "$p" ]; }; then echo "$p"; hit=1; break; fi
  done
done < <(git diff --name-only --no-renames -z "$mb" "$head")
[ "$hit" = 0 ] || { echo "protected-set: the change touches the protected set (scripts/protected-paths.txt): it waits for the owner" >&2; exit 1; }
