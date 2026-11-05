ATK_DESC="delete ledger-baseline.txt (a baseline that disappears)"
ATK_GATES=('scripts/gate-diff-improving.sh --suite-judged "$ATK_BASE" HEAD'); ATK_GATE_FILES=(scripts/gate-diff-improving.sh)
atk_apply() { git rm -q scripts/ledger-baseline.txt; }
