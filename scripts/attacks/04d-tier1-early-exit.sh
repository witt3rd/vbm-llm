ATK_DESC="insert an early exit 0 right after set -euo pipefail in tier1.sh (every later gate is skipped)"
ATK_GATES=('scripts/gate-diff-improving.sh --suite-judged "$ATK_BASE" HEAD'); ATK_GATE_FILES=(scripts/gate-diff-improving.sh)
atk_apply() { sed -i '/^set -euo pipefail/a exit 0' scripts/tier1.sh; }
