ATK_DESC="neuter scripts/protected-set.sh (a stub that always succeeds): its self-test scripts/test_protected_set.sh must FAIL (a gate whose self-test cannot fail)"
ATK_GATES=('scripts/test_protected_set.sh'); ATK_GATE_FILES=(scripts/test_protected_set.sh)
atk_apply() { neuter scripts/protected-set.sh; }
