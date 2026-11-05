ATK_DESC="remove the ran-evidence check from scripts/run-tests-parallel.sh (a test that exits 0 with no evidence passes again): the shared negative test must FAIL"
ATK_GATES=('scripts/test_ran_evidence.sh'); ATK_GATE_FILES=(scripts/test_ran_evidence.sh)
atk_apply() { sed -i 's|"\$ev" check "\$s"|true "$s"|' scripts/run-tests-parallel.sh; }
