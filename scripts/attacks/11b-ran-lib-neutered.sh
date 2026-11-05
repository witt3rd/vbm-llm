ATK_DESC="neuter scripts/lib-ran.sh (a sourced library that exits ends every test script with success, evidence or not): tier1.sh's own definition check must refuse it"
ATK_CONTROL=('[ "$(grep -c "^ran_done()" scripts/lib-ran.sh)" = 1 ]')   # the full tier1.sh is not run as a control (it is the whole gate): the pristine library defines the function
ATK_GATES=('scripts/tier1.sh'); ATK_GATE_FILES=(scripts/tier1.sh); ATK_EXPECT='does not define ran_done'
atk_apply() { neuter scripts/lib-ran.sh; }
