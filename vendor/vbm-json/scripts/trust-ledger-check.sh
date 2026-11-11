#!/usr/bin/env bash
# Tier 1: the trust ledger (docs/trust-ledger.md) names everything outside our direct control that vbm-json executes or depends on. The REQUIRED set is derived
# from the tree, not from the ledger: every @[extern] symbol in the sources, every C file under runtime/ and abi/, every hand-written binding loader,
# the build pins, the Lean compiler/runtime/clang pieces the pin brings, the closure modules that are neither spec nor toolchain (scripts/ClosureGate.lean --emit),
# and the tools scripts/ call. A new boundary with no entry FAILS; an entry covering nothing required FAILS. Prints `trust ledger: N entries ...` (.land/land-direct
# quotes it). The checker (scripts/trust_ledger.py) negative-self-tests itself on every run: remove any entry and it must fail.
# Entries for things not in the tree yet (runtime.c, the ABI edge, binding loaders, HACL*) are written under "Planned" in the ledger, not gated, and become
# `### Tnn.` entries in the PR that adds the file (then this derivation requires them).
# The derivation is repo-specific (see the class-level note in docs/decisions/0001-vbm-json.md).
# Usage: scripts/trust-ledger-check.sh [ledger]     (--count: only print N, no build needed)
set -euo pipefail
cd "$(dirname "$0")/.."
ledger=${1:-docs/trust-ledger.md}
if [ "${1:-}" = --count ]; then grep -c '^### T[0-9]' docs/trust-ledger.md; exit 0; fi
req=$(mktemp); trap 'rm -f "$req"' EXIT
files() { git ls-files --cached --others --exclude-standard "$@"; }   # a file not yet added is still required
{
  # the C and loaders we execute, the build pins (files). Generated binding code is not listed: it is counted as boundary through the ABI description.
  { files 'runtime/*.c' 'abi/*.c' 'bindings/*/loader.*' lean-toolchain mise.toml lakefile.lean lake-manifest.json; } | sed 's/^/file:/'
  # the pinned dependencies (vendor/, locked in .land/pins.lock): every C header they carry (trusted code that runs in our artifacts) and every @[extern] symbol their Lean sources declare
  for d in vendor/*/; do [ -d "$d" ] || continue; n=$(basename "$d"); for h in "$d"include/*.h; do [ -f "$h" ] && echo "dep:$n/include/$(basename "$h")" || true; done
    grep -rhE '^[[:space:]]*@\[extern' "$d" --include='*.lean' --exclude-dir=.lake --exclude-dir=tests 2>/dev/null | sed -E 's/.*@\[extern[^"]*"([^"]+)".*/extern:\1/; t; s/.*/extern:UNNAMED/' | sort -u || true; done
  # every FFI symbol declared in Lean (private externs are invisible to the closure walk, so read the source; an unnamed one needs a key too)
  grep -rhE '^[[:space:]]*@\[extern' LeanJson abi --include='*.lean' 2>/dev/null | sed -E 's/.*@\[extern[^"]*"([^"]+)".*/extern:\1/; t; s/.*/extern:UNNAMED/' | sort -u || true
  # what the Lean pin brings: the compiler (frontend, kernel, C emitter), the runtime (lean.h, libleanrt), the bundled clang and ld.lld
  [ -f lean-toolchain ] && printf '%s\n' lean-compiler lean-runtime clang-lld || true
  # closure modules that are neither spec nor toolchain (none yet: the closure is empty)
  lake env lean --run scripts/ClosureGate.lean --emit | awk '$1=="emit" && $2!="toolchain"{ print "module:" $3 }' | sort -u
  # tools run as processes: a fixed watch-list found in scripts/ and the build file
  [ -f scripts/trust_ledger.py ] && echo tool:python3 || true   # the checker itself (excluded from the grep below: it names every watch-listed tool)
  for t in git gh mise wt flock lake leanc node cargo; do
    files scripts lakefile.lean | grep -v -e 'scripts/trust' | xargs grep -lw -- "$t" >/dev/null 2>&1 && echo "tool:$t" || true; done
} | sort -u > "$req"
python3 scripts/trust_ledger.py "$ledger" "$req"
