ATK_DESC='add a masked or unchecked step to tier1.sh: if scripts/lint-pipefail.sh; then :; fi'
ATK_GATES=('scripts/gate-diff-improving.sh --suite-judged "$ATK_BASE" HEAD'); ATK_GATE_FILES=(scripts/gate-diff-improving.sh)
atk_apply() { add_before_end scripts/tier1.sh 'if scripts/lint-pipefail.sh; then :; fi'; }
