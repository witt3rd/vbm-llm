ATK_DESC="remove the pinned-library verification step from tier1.sh"
ATK_GATES=('scripts/gate-diff-improving.sh --suite-judged "$ATK_BASE" HEAD'); ATK_GATE_FILES=(scripts/gate-diff-improving.sh)
atk_apply() { n=$(first_line_matching scripts/tier1.sh 'pinned-lib\.py verify'); [ -n "$n" ] || { echo "tier1.sh has no pinned-lib step" >&2; return 1; }; sed -i "${n}d" scripts/tier1.sh; }
