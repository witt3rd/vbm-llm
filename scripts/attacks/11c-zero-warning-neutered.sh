ATK_DESC="neuter scripts/check-zero-warning.sh (a stub that always succeeds, the original defect in another form): the shared negative test, which runs it with lake REFUSED, must FAIL"
ATK_GATES=('scripts/test_ran_evidence.sh'); ATK_GATE_FILES=(scripts/test_ran_evidence.sh)
atk_apply() { neuter scripts/check-zero-warning.sh; }
