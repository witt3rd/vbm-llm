#!/usr/bin/env bash
# Tier 1: the trust ledger (docs/trust-ledger.md) names everything outside our direct control that vbm-llm executes or depends on. The REQUIRED set is derived
# from the tree, not from the ledger: every @[extern] symbol in the sources, every C file, every CI workflow, the build pins, the Lean compiler/runtime/clang pieces the
# pin brings, the pinned libraries (one key per line of scripts/pinned-libs.lock), the pinned landing tool, and the tools scripts/ call. A new boundary with no entry FAILS;
# an entry covering nothing required FAILS. Prints `trust ledger: N entries ...`. The checker (scripts/trust_ledger.py) negative-self-tests itself on every run: remove any
# entry and it must fail. (The project the gates were first built in also requires an entry for every closure module that is neither spec nor toolchain; the closure gate is
# not ported yet, and the one outside library is the pin above.)
# Usage: scripts/trust-ledger-check.sh [ledger]     (--count: only print N)
set -euo pipefail
cd "$(dirname "$0")/.."
ledger=${1:-docs/trust-ledger.md}
if [ "${1:-}" = --count ]; then grep -c '^### T[0-9]' docs/trust-ledger.md; exit 0; fi
req=$(mktemp); trap 'rm -f "$req"' EXIT
files() { git ls-files --cached --others --exclude-standard "$@"; }   # a file not yet added is still required
{
  # the C we would execute (none), the CI that gates us, the build pins and the pinned landing tool (files)
  { files '*.c' '.github/workflows/*' lean-toolchain mise.toml lakefile.lean lake-manifest.json scripts/land/PIN; } | sed 's/^/file:/'
  # every FFI symbol declared in Lean (the library has none: an extern is a new boundary)
  grep -rhE '^[[:space:]]*@\[extern' VbmLlm vectors --include='*.lean' 2>/dev/null | sed -E 's/.*@\[extern[^"]*"([^"]+)".*/extern:\1/; t; s/.*/extern:UNNAMED/' | sort -u || true
  # what the Lean pin brings: the compiler (frontend, kernel, C emitter), the runtime (lean.h, libleanrt), the bundled clang and ld.lld
  [ -f lean-toolchain ] && printf '%s\n' lean-compiler lean-runtime clang-lld || true
  # the pinned libraries (scripts/pinned-lib.py): one key per line of the protected lock, adopted or not
  python3 scripts/pinned-lib.py names | sed 's/^/pin:/'
  # tools run as processes: a fixed watch-list found in scripts/ and the build file
  [ -f scripts/trust_ledger.py ] && echo tool:python3 || true   # the checker itself (excluded from the grep below: it names every watch-listed tool)
  for t in git gh mise flock lake leanc leanchecker nanoda; do
    files scripts lakefile.lean | grep -v -e 'scripts/trust' | xargs grep -lw -- "$t" >/dev/null 2>&1 && echo "tool:$t" || true; done
} | sort -u > "$req"
python3 scripts/trust_ledger.py "$ledger" "$req"
