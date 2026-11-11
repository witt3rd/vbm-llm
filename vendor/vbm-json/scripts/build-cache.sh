#!/usr/bin/env bash
# The Lean build cache: a cold clone rebuilds both libraries (about a minute on 2 CPUs); with a cache entry for the SAME toolchain and the SAME sources it restores them instead.
#   scripts/build-cache.sh key                 print the key: sha256 over the Lean version, lakefile.lean, lake-manifest.json and every tracked .lean file outside scripts/ (path and content)
#   scripts/build-cache.sh restore [DIR]       when .lake/build is absent and DIR/<key>.tar (+ .sha256) exists and matches its checksum: unpack it into .lake/. A miss is not an error (prints "miss").
#   scripts/build-cache.sh store   [DIR]       after a build: pack .lake/build (modules only, no executables) as DIR/<key>.tar + .sha256, atomically; an existing entry is kept.
#   scripts/build-cache.sh fetch URL [DIR]     opt-in, needs the network: download URL/<key>.tar and URL/<key>.tar.sha256 into DIR, then restore. A bad checksum is refused and removed.
# The file list is git's own (byte order): the key does not depend on the caller's locale (a `sort` once made a cache miss in a sandbox that runs with LANG=C).
# DIR defaults to $VBM_BUILD_CACHE, else ~/.cache/vbm-json/build. This is a CONVENIENCE for a contributor's second and later clones and worktrees; it is never on the path of a gate: scripts/tier1.sh and the lander do not call it,
# and Lake re-checks every restored module against the hash of its source (a stale or foreign entry is rebuilt, never believed). The checksum detects a damaged or swapped file, not a forged one: a fresh clone rebuilds from source, so what lands never rests on a restored artifact. Run from anywhere inside the repository. Self-test (offline, no Lean needed): scripts/test_build_cache.sh.
export LC_ALL=C
set -euo pipefail
cd "$(dirname "$0")/.."
sha() { sha256sum | cut -d' ' -f1; }
key() {
  v=$(lean --version 2>&1) || true
  { echo "lean: ${v%%$'\n'*}"
    for f in lakefile.lean lake-manifest.json; do echo "$f $(sha256sum < "$f" | cut -d' ' -f1)"; done
    git ls-files -z -- '*.lean' ':!scripts/' | while IFS= read -r -d '' f; do echo "$f $(sha256sum < "$f" | cut -d' ' -f1)"; done
  } | sha
}
dir=${VBM_BUILD_CACHE:-$HOME/.cache/vbm-json/build}
cmd=${1:-}; shift || true
case $cmd in
  key) key;;
  restore)
    [ -z "${1:-}" ] || dir=$1
    k=$(key); t=$dir/$k.tar
    if [ -e .lake/build ]; then echo "build-cache: .lake/build exists: nothing restored"; exit 0; fi
    if [ ! -f "$t" ] || [ ! -f "$t.sha256" ]; then echo "build-cache: miss ($k)"; exit 0; fi
    if [ "$(sha < "$t")" != "$(cut -d' ' -f1 "$t.sha256")" ]; then echo "build-cache: $t does not match its checksum: refused" >&2; exit 1; fi
    mkdir -p .lake; tar -xf "$t" -C .lake; echo "build-cache: hit ($k): restored .lake/build";;
  store)
    [ -z "${1:-}" ] || dir=$1
    [ -d .lake/build ] || { echo "build-cache: no .lake/build to store" >&2; exit 1; }
    k=$(key); t=$dir/$k.tar; mkdir -p "$dir"
    if [ -f "$t" ] && [ -f "$t.sha256" ]; then echo "build-cache: entry $k exists"; exit 0; fi
    tmp=$(mktemp "$dir/.store.XXXXXX"); trap 'rm -f "$tmp"' EXIT
    tar -C .lake --exclude=./build/bin -cf "$tmp" ./build; chmod 644 "$tmp"; echo "$(sha < "$tmp")  $k.tar" > "$tmp.sha256"
    mv -f "$tmp.sha256" "$t.sha256"; mv -f "$tmp" "$t"; echo "build-cache: stored $k";;
  fetch)
    url=${1:?usage: build-cache.sh fetch URL [DIR]}; [ -z "${2:-}" ] || dir=$2
    k=$(key); mkdir -p "$dir"; tmp=$(mktemp -d "$dir/.fetch.XXXXXX"); trap 'rm -rf "$tmp"' EXIT
    case $url in https://*) ;; *) echo "build-cache: only an https URL is fetched" >&2; exit 2;; esac
    curl -fsSL --max-time 300 "$url/$k.tar" -o "$tmp/$k.tar" && curl -fsSL --max-time 60 "$url/$k.tar.sha256" -o "$tmp/$k.tar.sha256" || { echo "build-cache: miss at $url ($k)"; exit 0; }
    if [ "$(sha < "$tmp/$k.tar")" != "$(cut -d' ' -f1 "$tmp/$k.tar.sha256")" ]; then echo "build-cache: the download does not match its checksum: refused" >&2; exit 1; fi
    mv -f "$tmp/$k.tar.sha256" "$dir/$k.tar.sha256"; mv -f "$tmp/$k.tar" "$dir/$k.tar"; "$0" restore "$dir";;
  *) echo "usage: build-cache.sh key | restore [DIR] | store [DIR] | fetch URL [DIR]" >&2; exit 2;;
esac
