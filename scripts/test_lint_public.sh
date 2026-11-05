#!/usr/bin/env bash
# Tier 1: the public-readiness lint (scripts/lint-public) passes on the whole tree AND is shown able to fail: a planted private-name hash (a harmless canary token stands in, so this file spells no private
# name), a path of ours, a retired project name, a banned token in a FILE NAME, and in an untracked file are each flagged; a clean tree passes; the hash list cannot be emptied.
export LC_ALL=C
set -euo pipefail
cd "$(dirname "$0")/.."
. scripts/lib-ran.sh   # ran_case counts each executed check, ran_done prints the evidence line `ran: NAME: N cases` (docs/decisions/0002-ran-evidence.md)
lint=$(pwd)/scripts/lint-public
fail() { echo "tier1: lint-public: $*" >&2; exit 1; }
out=$("$lint") && ran_case || fail "the tree is not public-ready: $out"
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
export GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_SYSTEM=/dev/null
mkdir "$T/r"; cp -r scripts "$T/r/scripts"; git -C "$T/r" init -q; echo "clean words only" > "$T/r/a.md"; git -C "$T/r" add -A
"$lint" --root "$T/r" >/dev/null && ran_case || fail "a clean fixture tree was flagged"
export LINT_PUBLIC_EXTRA_HASHES=$("$lint" --hash zzcanary)
chk() { "$lint" --root "$T/r" > "$T/out" 2>&1 && fail "negative self-test: $1 was NOT flagged"; grep -q "$2" "$T/out" && ran_case || fail "negative self-test: $1: wrong finding: $(cat "$T/out")"; }
echo "a ZzCanary here" > "$T/r/a.md"; chk "a banned token (any case)" "a.md:1: a private name"
echo "clean" > "$T/r/a.md"; echo "x" > "$T/r/zzcanary-notes.md"; chk "a banned token in a file name" "zzcanary-notes.md:path"; rm "$T/r/zzcanary-notes.md"
echo "x" > "$T/r/untracked.md"; echo "zzcanary" >> "$T/r/untracked.md"; chk "a banned token in an untracked file" "untracked.md:2"; rm "$T/r/untracked.md"
unset LINT_PUBLIC_EXTRA_HASHES
printf 'see %s/dt/src\n' /home > "$T/r/a.md"; chk "a home path" "a.md:1: a path of ours"
printf 'see ~%s\n' /cloud > "$T/r/a.md"; chk "a tilde path" "a.md:1: a path of ours"
echo "the $(scripts/lint-public --hash x >/dev/null; printf awe; printf some)-vbm project" > "$T/r/a.md"; chk "a retired project name" "a.md:1: a retired project name"
echo clean > "$T/r/a.md"; : > "$T/r/scripts/public-banned-hashes.txt"; "$T/r/scripts/lint-public" --root "$T/r" >/dev/null 2>&1 && fail "negative self-test: an emptied hash list passed"
ran_done test_lint_public
echo "tier1: lint-public: the whole tree is public-ready, and the lint flags names, paths, file names, untracked files, a retired project name: ok"
