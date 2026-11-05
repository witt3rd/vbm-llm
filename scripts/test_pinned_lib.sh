#!/usr/bin/env bash
# Tier 1: the pinned-library gate (scripts/pinned-lib.py, docs/decisions/0001-vbm-llm.md) can FAIL. On a scratch package checkout (scripts/attacks/pin-check.sh): the matching pin is ok and
# every mutation of it (a stale rev, an edited spec file, an extra spec file, a fork, a plain copy with no .git, an edited lock hash or rev, an unlocked package, a symlinked or missing spec path)
# is refused with its reason; a library that is not adopted yet is `absent`, not a failure; the lock is read strictly (a short hash, a reserved root, a duplicate, an unsafe path fail); `verdict`
# is the machine-readable verdict; the real lock and the real tree pass; `protected` fails on a list that does not cover the lock, its tool and its test.
export LC_ALL=C
set -euo pipefail
cd "$(dirname "$0")/.."
. scripts/git-hermetic.sh   # hermetic git: no ambient config, explicit identity and branch (scripts/lint-git-hermetic.sh)
fail() { echo "tier1: pinned-lib: $*" >&2; exit 1; }
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
tool=scripts/pinned-lib.py
chk=scripts/attacks/pin-check.sh
"$chk" none >"$T/o" 2>&1 || fail "the matching pin is refused: $(cat "$T/o")"
grep -q ': ok: rev and spec_hash match' "$T/o" || fail "the matching pin does not say ok"
want() {   # want MUTATION REGEX
  if "$chk" "$1" >"$T/o" 2>&1; then fail "mutation $1 passes verify (a gate that cannot fail)"; fi
  grep -Eq -- "$2" "$T/o" || fail "mutation $1 fails, but not for the reason ($2): $(tail -2 "$T/o" | tr '\n' ' ')"
}
want stale-rev 'stale rev'
want hash-mismatch 'spec_hash mismatch'
want extra-spec-file 'spec_hash mismatch'
want fork 'fork or a moved checkout'
want no-git 'not a git checkout'
want lock-hash 'spec_hash mismatch'
want lock-rev 'stale rev'
want unlocked 'not in the lock'
want symlink 'not a regular file'
want missing-path 'is missing or not a regular file'
# the real lock and the real tree
"$tool" verify >"$T/o" 2>&1 || fail "the tree's own lock does not verify: $(cat "$T/o")"
"$tool" protected >/dev/null 2>&1 || fail "the lock, its tool and its test are not protected"
[ "$("$tool" names | wc -l)" -ge 1 ] || fail "the lock names no library"
# the lock is read strictly; each of these is a hard error (exit 2), never a quiet skip
good=$(awk '!/^[[:space:]]*#/ && NF { print; exit }' scripts/pinned-libs.lock); set -- $good
rej() { printf '%s\n' "$2" > "$T/lock"; rc=0; "$tool" names --lock "$T/lock" >/dev/null 2>&1 || rc=$?; [ "$rc" = 2 ] || fail "a malformed lock line is accepted ($1)"; }
printf '%s\n' "$good" > "$T/lock"; [ "$("$tool" names --lock "$T/lock")" = "$1" ] || fail "a well-formed lock line is refused"
rej "a short rev" "$1 abc $3 $4 $5"; rej "a short hash" "$1 $2 abc $4 $5"; rej "a missing field" "$1 $2 $3 $4"; rej "a reserved root (VbmLlmProofs)" "$1 $2 $3 VbmLlmProofs $5"
rej "a reserved root (Lean)" "$1 $2 $3 Lean $5"; rej "an unsafe path" "$1 $2 $3 $4 ../x"; rej "an absolute path" "$1 $2 $3 $4 /etc"
printf '%s\n%s\n' "$good" "$good" > "$T/lock"; rc=0; "$tool" names --lock "$T/lock" >/dev/null 2>&1 || rc=$?; [ "$rc" = 2 ] || fail "a duplicate lock line is accepted"
# verdict: the machine-readable form (`ROOT ok DIR HASH`, `ROOT absent - why`, `ROOT bad DIR why`)
verdicts=$("$tool" verdict); grep -Eq "^$4 (ok|absent) " <<<"$verdicts" || fail "verdict does not name the lock's root $4 as ok or absent"
# protected: a list that does not cover the lock fails and names it
grep -v 'scripts/pinned-libs.lock' scripts/protected-paths.txt > "$T/list"; rc=0; "$tool" protected --list "$T/list" >"$T/o" 2>&1 || rc=$?
[ "$rc" = 1 ] && grep -q 'scripts/pinned-libs.lock' "$T/o" || fail "a protected list without the lock passes"
# fetch: a cold runner has no checkout. The library is cloned from the manifest's url at the LOCK's rev, then verify judges it; a moved or wrong source fails verify, nothing is trusted
mkdir -p "$T/src/LibA"; ( cd "$T/src" && git init -q && printf 'def a := 1\n' > LibA/A.lean && printf 'v\n' > lean-toolchain && git add -A && git commit -q -m one )
r1=$(git -C "$T/src" rev-parse HEAD); h1=$("$tool" hash "$T/src" 'LibA/,lean-toolchain')
printf 'def a := 2\n' > "$T/src/LibA/A.lean"; git -C "$T/src" commit -qam two
mf() { printf '{"version":"1.3.0","packagesDir":".lake/packages","packages":[{"type":"git","name":"«libx»","url":"file://%s","rev":"%s"}]}\n' "$T/src" "$1" > "$T/fm.json"; }
printf 'libx %s %s LibA LibA/,lean-toolchain\n' "$r1" "$h1" > "$T/flock"
mf "$r1"; rm -rf "$T/fp"; mkdir "$T/fp"
"$tool" fetch --lock "$T/flock" --manifest "$T/fm.json" --pkgs "$T/fp" >/dev/null 2>&1 || fail "fetch of a missing checkout failed"
"$tool" verify --lock "$T/flock" --manifest "$T/fm.json" --pkgs "$T/fp" >/dev/null 2>&1 || fail "the fetched checkout (the lock's rev, an older commit than the source's head) does not verify"
[ "$(git -C "$T/fp/libx" rev-parse HEAD)" = "$r1" ] || fail "fetch checked out something other than the lock's rev"
printf 'junk\n' > "$T/fp/libx/LibA/Extra.lean"   # an existing checkout is left alone: verify judges it (and fails)
"$tool" fetch --lock "$T/flock" --manifest "$T/fm.json" --pkgs "$T/fp" >/dev/null 2>&1 || fail "fetch failed on an existing checkout"
if "$tool" verify --lock "$T/flock" --manifest "$T/fm.json" --pkgs "$T/fp" >/dev/null 2>&1; then fail "an edited existing checkout verifies after fetch"; fi
mf "$(git -C "$T/src" rev-parse HEAD)"; rm -rf "$T/fp"; mkdir "$T/fp"   # the manifest names another rev than the lock: nothing is fetched, verify fails (stale rev)
"$tool" fetch --lock "$T/flock" --manifest "$T/fm.json" --pkgs "$T/fp" >/dev/null 2>&1 || true
[ ! -e "$T/fp/libx" ] || fail "fetch cloned a library whose manifest rev is not the lock's"
if "$tool" verify --lock "$T/flock" --manifest "$T/fm.json" --pkgs "$T/fp" >/dev/null 2>&1; then fail "a stale manifest rev verifies"; fi
mf "$r1"; sed -i 's/file:\/\/[^"]*/file:\/\/\/nonexistent/' "$T/fm.json"; rm -rf "$T/fp"; mkdir "$T/fp"   # an unreachable source fails loudly
if "$tool" fetch --lock "$T/flock" --manifest "$T/fm.json" --pkgs "$T/fp" >/dev/null 2>&1; then fail "fetch from an unreachable url succeeded"; fi
echo "tier1: pinned-lib: ok (a matching pin passes; a stale rev, an edited spec file, a fork, an unlocked package, an edited lock and a malformed lock all fail)"
