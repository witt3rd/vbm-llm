ATK_DESC="neuter scripts/ran-evidence.sh (a stub that always succeeds): its shared negative test scripts/test_ran_evidence.sh must FAIL (a reader of ran-evidence that accepts everything)"
ATK_GATES=('scripts/test_ran_evidence.sh'); ATK_GATE_FILES=(scripts/test_ran_evidence.sh)
atk_apply() { neuter scripts/ran-evidence.sh; }
