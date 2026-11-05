ATK_DESC="neuter scripts/gate-diff-improving.sh (a stub that always succeeds): its self-test scripts/test_gate_diff_improving.sh must FAIL (a gate whose self-test cannot fail)"
ATK_GATES=('scripts/test_gate_diff_improving.sh'); ATK_GATE_FILES=(scripts/test_gate_diff_improving.sh)
atk_apply() { neuter scripts/gate-diff-improving.sh; }
