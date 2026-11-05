ATK_DESC="neuter scripts/lib-no-crash-record.sh (a stub that always succeeds): its self-test scripts/test_no_crash_record.sh must FAIL (a gate whose self-test cannot fail)"
ATK_GATES=('scripts/test_no_crash_record.sh'); ATK_GATE_FILES=(scripts/test_no_crash_record.sh)
atk_apply() { neuter scripts/lib-no-crash-record.sh; }
