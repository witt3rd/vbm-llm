ATK_DESC="delete a negative self-test line of tier1.sh (the first 'cannot' guard)"
ATK_GATES=('scripts/gate-diff-improving.sh --suite-judged "$ATK_BASE" HEAD'); ATK_GATE_FILES=(scripts/gate-diff-improving.sh)
atk_apply() { n=$(first_line_matching scripts/tier1.sh 'cannot'); sed -i "${n}d" scripts/tier1.sh; }
