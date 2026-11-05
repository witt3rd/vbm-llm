#!/usr/bin/env bash
# The fixture of the pinned-library attacks (scripts/attacks/13*-pin-*.sh) and of scripts/test_pinned_lib.sh: a scratch package checkout (a real git repository), a lake manifest naming it and a lock
# line that matches it, then ONE mutation, then the tree's own scripts/pinned-lib.py verify (cwd = the root of the tree under judgement; exit = its exit code).
#   pin-check.sh [MUTATION]     MUTATION defaults to the one named in the file `atk-pin-mutation` of the tree (the attack writes it), else none (the control: must PASS).
# none | stale-rev (the manifest names another commit) | hash-mismatch (a spec file edited in the checkout) | extra-spec-file (an untracked file under a spec directory) | fork (the checkout is another
# repository at another commit) | no-git (a plain copy, no .git) | lock-hash (the lock's spec_hash edited) | lock-rev (the lock's rev edited)
# | unlocked (the manifest lists a second package the lock does not name) | symlink (a spec file is a symlink) | missing-path (a spec path is gone)
export LC_ALL=C
set -euo pipefail
. "$(dirname "$0")/../git-hermetic.sh"
mut=${1:-}; [ -n "$mut" ] || { if [ -f atk-pin-mutation ]; then mut=$(tr -d '[:space:]' < atk-pin-mutation); else mut=none; fi; }
tool=$(pwd)/scripts/pinned-lib.py
T=$(mktemp -d "${TMPDIR:-/tmp}/pin-check.XXXXXX"); trap 'rm -rf "$T"' EXIT
mkpkg() {   # mkpkg DIR TEXT: a package checkout with one commit
  mkdir -p "$1/LibA" && printf 'def a := %s\n' "$2" > "$1/LibA/A.lean" && printf 'import LibA.A\n' > "$1/LibA.lean" && printf 'leanprover/lean4:v4.35.0\n' > "$1/lean-toolchain"
  git -C "$1" init -q && git -C "$1" add -A && git -C "$1" commit -q -m "v$2"
}
paths='LibA/,LibA.lean,lean-toolchain'
mkdir -p "$T/pkgs"; mkpkg "$T/pkgs/libx" 1; rev1=$(git -C "$T/pkgs/libx" rev-parse HEAD)
printf 'def a := 2\n' > "$T/pkgs/libx/LibA/A.lean"; git -C "$T/pkgs/libx" commit -qam v2; rev=$(git -C "$T/pkgs/libx" rev-parse HEAD)
hash=$(python3 "$tool" hash "$T/pkgs/libx" "$paths")
manifest() { printf '{"version":"1.3.0","packagesDir":".lake/packages","packages":[{"type":"git","name":"«libx»","url":"https://example.invalid/libx","rev":"%s","inputRev":"main"}%s],"name":"x","lakeDir":".lake"}\n' "$1" "${2:-}"; }
lock() { printf '# t\nlibx %s %s LibA %s\n' "$1" "$2" "$paths"; }
man=$(manifest "$rev"); lk=$(lock "$rev" "$hash")
case $mut in
  none) ;;
  stale-rev) man=$(manifest "$rev1");;
  hash-mismatch) printf 'def a := 3\n' > "$T/pkgs/libx/LibA/A.lean";;
  extra-spec-file) printf 'def b := 1\n' > "$T/pkgs/libx/LibA/Extra.lean";;
  fork) rm -rf "$T/pkgs/libx"; mkpkg "$T/pkgs/libx" 9;;
  no-git) rm -rf "$T/pkgs/libx/.git";;
  lock-hash) lk=$(lock "$rev" "$(printf '%064d' 7)");;
  lock-rev) lk=$(lock "$rev1" "$hash");;
  unlocked) man=$(manifest "$rev" ',{"type":"git","name":"evil","url":"https://example.invalid/evil","rev":"'"$rev"'","inputRev":"main"}');;
  symlink) rm "$T/pkgs/libx/LibA.lean"; ln -s LibA/A.lean "$T/pkgs/libx/LibA.lean";;
  missing-path) rm "$T/pkgs/libx/lean-toolchain";;
  *) echo "pin-check: unknown mutation $mut" >&2; exit 2;;
esac
printf '%s\n' "$man" > "$T/manifest.json"; printf '%s\n' "$lk" > "$T/lock"
python3 "$tool" verify --lock "$T/lock" --manifest "$T/manifest.json" --pkgs "$T/pkgs"
