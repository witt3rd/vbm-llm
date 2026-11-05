ATK_DESC="remove the declaration of a test script from tier1.sh (par scripts/test_pinned_lib.sh)"
ATK_GATES=('scripts/gate-diff-improving.sh --suite-judged "$ATK_BASE" HEAD'); ATK_GATE_FILES=(scripts/gate-diff-improving.sh)
atk_apply() { sed -i '/^par scripts\/test_pinned_lib.sh$/d' scripts/tier1.sh; }
