#!/usr/bin/env bash
# Regenerate the generated paths (scripts/generated-paths.txt) from the tree as it is: build, then the ledger gate's own --write (improvements only).
#   scripts/regen-baselines.sh      exit 0: written (or unchanged); exit 3: the gate does NOT pass against the baseline on disk, i.e. the measured value is WORSE
#                                   than the baseline (or the gate is broken): nothing is written. A deliberate worsening is a baseline edit made by the
#                                   change's author, never by this script.
# Used by scripts/land-direct after it took main's version of a conflicting baseline. Run from the repo root (mise exec -- ...).
set -euo pipefail
cd "$(dirname "$0")/.."
lake build VbmLlm VbmLlmProofs >/dev/null     # fresh .olean/IR: the gate reads what the build just produced
lake env lean --run scripts/LedgerGate.lean >/dev/null || { echo "regen-baselines: scripts/ledger-baseline.txt does not pass against the baseline on disk: the measured value is worse (or the gate is broken); not written" >&2; exit 3; }
lake env lean --run scripts/LedgerGate.lean --write >/dev/null
echo "regen-baselines: ok"
