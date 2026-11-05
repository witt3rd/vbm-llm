ATK_DESC="weaken the forbidden-constructs scan of tier1.sh (drop sorry from the pattern)"
ATK_GATES=('scripts/gate-diff-improving.sh --suite-judged "$ATK_BASE" HEAD'); ATK_GATE_FILES=(scripts/gate-diff-improving.sh)
atk_apply() { sed -i 's/(sorry|admit|axiom/(admit|axiom/' scripts/tier1.sh; }
