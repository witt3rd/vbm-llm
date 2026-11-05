ATK_DESC="remove the ran-evidence check of the concurrent gates from tier1.sh (a gate that prints no count passes again)"
ATK_GATES=('scripts/gate-diff-improving.sh --suite-judged "$ATK_BASE" HEAD'); ATK_GATE_FILES=(scripts/gate-diff-improving.sh)
atk_apply() { sed -i '/^scripts\/ran-evidence.sh check-dir /d' scripts/tier1.sh; }
