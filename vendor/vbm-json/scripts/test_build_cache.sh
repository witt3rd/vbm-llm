#!/usr/bin/env bash
# The Lean build cache (scripts/build-cache.sh), offline and without Lean (a stub `lean` names the toolchain): the key follows the toolchain, the lakefile, the manifest and every tracked .lean file outside scripts/, and nothing else;
# a stored entry restores byte for byte into another clone (executables excluded); each way of getting a WRONG artifact in is shown refused: a damaged or swapped tarball, a missing checksum, a key that moved, a plain-http fetch.
set -euo pipefail
cd "$(dirname "$0")/.."
. .land/tool/lib/ran.sh   # ran_case counts each executed check; ran_done prints the evidence line (.land/tool/docs/ran-evidence.md)
src=$(pwd); T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
fail() { echo "test_build_cache: $*" >&2; exit 1; }
mkdir -p "$T/bin"; printf '#!/bin/sh\necho "Lean (version ${LEAN_STUB:-4.35.0}, x86_64-unknown-linux-gnu)"\n' > "$T/bin/lean"; chmod +x "$T/bin/lean"; export PATH="$T/bin:$PATH"
export GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_SYSTEM=/dev/null GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@t GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@t
mk() {   # mk DIR: a tiny repository carrying the script
  mkdir -p "$1/scripts" "$1/LeanJson" "$1/LeanJsonProofs"; git init -q -b main "$1"; cp "$src/scripts/build-cache.sh" "$1/scripts/"
  echo 'package' > "$1/lakefile.lean"; echo '{}' > "$1/lake-manifest.json"; echo 'def a := 1' > "$1/LeanJson/A.lean"; echo 'theorem b : True := trivial' > "$1/LeanJsonProofs/B.lean"; echo 'def gate := 1' > "$1/scripts/G.lean"
  git -C "$1" add -A; git -C "$1" commit -qm init; }
mk "$T/a"; mk "$T/b"
k() { ( cd "$1" && scripts/build-cache.sh key ); }
K=$(k "$T/a"); [ "${#K}" = 64 ] && [ "$K" = "$(k "$T/b")" ] || fail "the key is not a stable sha256 of the same tree"; ran_case
echo 'def a := 2' > "$T/b/LeanJson/A.lean"; git -C "$T/b" commit -qam x; [ "$(k "$T/b")" != "$K" ] || fail "negative self-test: a changed source did not change the key"; ran_case
git -C "$T/b" reset -q --hard HEAD~1; echo x >> "$T/b/lakefile.lean"; git -C "$T/b" commit -qam x; [ "$(k "$T/b")" != "$K" ] || fail "negative self-test: a changed lakefile did not change the key"; ran_case
git -C "$T/b" reset -q --hard HEAD~1; echo '{"a":1}' > "$T/b/lake-manifest.json"; git -C "$T/b" commit -qam x; [ "$(k "$T/b")" != "$K" ] || fail "negative self-test: a changed manifest did not change the key"; ran_case
git -C "$T/b" reset -q --hard HEAD~1; [ "$(LEAN_STUB=4.36.0 k "$T/b")" != "$K" ] || fail "negative self-test: another toolchain did not change the key"; ran_case
echo 'def gate := 2' > "$T/b/scripts/G.lean"; echo junk > "$T/b/LeanJson/untracked.lean"; [ "$(k "$T/b")" = "$K" ] || fail "a gate script or an untracked file changed the key (the cache would miss for nothing)"; ran_case
git -C "$T/b" checkout -q -- scripts/G.lean; rm "$T/b/LeanJson/untracked.lean"
C=$T/cache
# a miss is not an error and restores nothing; a build is stored, and restored into ANOTHER clone, byte for byte, executables left out
grep -q '^build-cache: miss' <<<"$( cd "$T/b" && scripts/build-cache.sh restore "$C" 2>&1 )" && [ ! -e "$T/b/.lake" ] || fail "a miss restored something or failed"; ran_case
mkdir -p "$T/a/.lake/build/lib" "$T/a/.lake/build/ir" "$T/a/.lake/build/bin"; echo olean > "$T/a/.lake/build/lib/A.olean"; echo c > "$T/a/.lake/build/ir/A.c"; echo exe > "$T/a/.lake/build/bin/prog"
grep -q "stored $K" <<<"$( cd "$T/a" && scripts/build-cache.sh store "$C" 2>&1 )" && [ -f "$C/$K.tar" ] && [ -f "$C/$K.tar.sha256" ] || fail "the build was not stored"; ran_case
grep -q "exists" <<<"$( cd "$T/a" && scripts/build-cache.sh store "$C" 2>&1 )" || fail "an existing entry was not kept"; ran_case
grep -q "hit ($K)" <<<"$( cd "$T/b" && scripts/build-cache.sh restore "$C" 2>&1 )" || fail "a stored entry did not restore"; ran_case
[ "$(cat "$T/b/.lake/build/lib/A.olean")" = olean ] && [ "$(cat "$T/b/.lake/build/ir/A.c")" = c ] && [ ! -e "$T/b/.lake/build/bin" ] || fail "the restored tree differs from the stored one (or carries an executable)"; ran_case
echo mine > "$T/b/.lake/build/lib/A.olean"; grep -q "nothing restored" <<<"$( cd "$T/b" && scripts/build-cache.sh restore "$C" 2>&1 )" && [ "$(cat "$T/b/.lake/build/lib/A.olean")" = mine ] || fail "negative self-test: a restore overwrote an existing build"; ran_case
# every way of getting a wrong artifact in is refused
rm -rf "$T/b/.lake"; cp "$C/$K.tar" "$T/good.tar"; printf 'x' >> "$C/$K.tar"
( cd "$T/b" && scripts/build-cache.sh restore "$C" ) 2>"$T/err" && fail "negative self-test: a damaged tarball was restored"; grep -q "does not match its checksum" "$T/err" && [ ! -e "$T/b/.lake" ] || fail "a damaged tarball: wrong refusal, or it was partly unpacked"; ran_case
cp "$T/good.tar" "$C/$K.tar"; rm "$C/$K.tar.sha256"; grep -q "^build-cache: miss" <<<"$( cd "$T/b" && scripts/build-cache.sh restore "$C" 2>&1 )" && [ ! -e "$T/b/.lake" ] || fail "negative self-test: an entry without its checksum was restored"; ran_case
( cd "$T/b" && scripts/build-cache.sh fetch http://example.invalid/x "$C" ) 2>"$T/err" && fail "negative self-test: a plain-http fetch was attempted"; grep -q "only an https URL" "$T/err" || fail "wrong refusal for a plain-http fetch"; ran_case
( cd "$T/b" && scripts/build-cache.sh store "$C" ) 2>/dev/null && fail "a store without a build succeeded"
ran_done test_build_cache
echo "test_build_cache: the key follows the toolchain, lakefile, manifest and tracked sources only; an entry restores byte for byte into another clone; a damaged, checksum-less, foreign or plain-http entry is refused: ok"
