ATK_DESC="neuter scripts/lint-workflows.py (a stub that always succeeds): its self-test scripts/test_lint_workflows.sh must FAIL (a gate whose self-test cannot fail)"
ATK_GATES=('scripts/test_lint_workflows.sh'); ATK_GATE_FILES=(scripts/test_lint_workflows.sh)
atk_apply() { neuter scripts/lint-workflows.py; }
