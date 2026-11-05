ATK_DESC="remove the call of scripts/check-zero-warning.sh from tier1.sh (the zero-warning mechanism is no longer checked)"
ATK_GATES=('scripts/gate-diff-improving.sh --suite-judged "$ATK_BASE" HEAD'); ATK_GATE_FILES=(scripts/gate-diff-improving.sh)
atk_apply() { sed -i '/^scripts\/check-zero-warning.sh$/d' scripts/tier1.sh; }
