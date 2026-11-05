ATK_DESC="neuter scripts/git-hermetic.sh (a sourced library that exits): the self-tests that source it must FAIL (a stub that ends them with success is not a pass)"
ATK_GATES=('scripts/test_gate_diff_improving.sh'); ATK_GATE_FILES=(scripts/test_gate_diff_improving.sh)
atk_apply() { neuter scripts/git-hermetic.sh; }
