#!/usr/bin/env bash
# Tier 2 (assurance gate, the SLOW checks; run on main by CI: .github/workflows/ci.yml, every 6 hours and on dispatch; it never gates a landing):
#  1. Tier 1 again (everything quick).
#  2. The whole relabel-attack suite (the Lean attacks too; Tier 1 runs the others).
#  3. The independent kernel re-check: `leanchecker --fresh` replays every declaration of VbmLlm and VbmLlmProofs (and what they import) in a fresh environment (guards a tampered or stale .olean).
#  4. An independent external checker (nanoda) over the exported proof of both libraries and their dependencies.
set -euo pipefail
cd "$(dirname "$0")/.."
LEAN_PREFIX=$(lean --print-prefix)

scripts/tier1.sh
echo "tier2: the whole relabel-attack suite (the Lean attacks too; Tier 1 runs the others)"
scripts/relabel-attacks.sh
echo "tier2: leanchecker --fresh VbmLlm"
lake env "$LEAN_PREFIX/bin/leanchecker" --fresh VbmLlm
echo "tier2: leanchecker --fresh VbmLlmProofs"
lake env "$LEAN_PREFIX/bin/leanchecker" --fresh VbmLlmProofs
echo "tier2: external checker (nanoda) over the exported proof"
exp=$(mktemp); cfg=$(mktemp)
trap 'rm -f "$exp" "$cfg"' EXIT
lake env "$LEAN_PREFIX/bin/leanexport" VbmLlm VbmLlmProofs > "$exp"
cat > "$cfg" <<JSON
{"export_file_path":"$exp","permitted_axioms":["propext","Classical.choice","Quot.sound","Lean.trustCompiler"],"unpermitted_axiom_hard_error":false,"nat_extension":true,"string_extension":true,"print_success_message":true}
JSON
out=$("$LEAN_PREFIX/bin/nanoda_bin" "$cfg" 2>&1) || { echo "$out"; exit 1; }
grep -q "with no typechecker errors" <<<"$out" || { echo "$out"; exit 1; }
echo "$out" | sed -n 1p
echo "tier2: ok"
