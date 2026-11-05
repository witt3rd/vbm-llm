ATK_DESC="drop a concurrent gate's line from scripts/ran-gates.txt (its count is no longer required): the shared negative test, which checks every bg gate of tier1.sh is covered, must FAIL"
ATK_GATES=('scripts/test_ran_evidence.sh'); ATK_GATE_FILES=(scripts/test_ran_evidence.sh)
atk_apply() { sed -i '/^axiom-gate /d' scripts/ran-gates.txt; }
