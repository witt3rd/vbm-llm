ATK_DESC="delete the suite's own negative self-test (scripts/test_relabel_attacks.sh)"
ATK_GATES=('scripts/relabel-attacks.sh --check-wired'); ATK_GATE_FILES=(scripts/relabel-attacks.sh)
atk_apply() { git rm -q scripts/test_relabel_attacks.sh; }
