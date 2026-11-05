ATK_DESC="neuter scripts/run-tests-parallel.sh (a stub that always succeeds): its self-test scripts/test_run_parallel.sh must FAIL (a gate whose self-test cannot fail)"
ATK_GATES=('scripts/test_run_parallel.sh'); ATK_GATE_FILES=(scripts/test_run_parallel.sh)
atk_apply() { neuter scripts/run-tests-parallel.sh; }
