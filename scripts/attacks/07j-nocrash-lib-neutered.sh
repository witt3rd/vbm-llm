ATK_DESC="neuter scripts/lib-no-crash-record.sh (a sourced library that exits ends tier1.sh itself with success): tier1.sh's own definition check must refuse it"
ATK_CONTROL=('[ "$(grep -c "^nocrash_begin()" scripts/lib-no-crash-record.sh)" = 1 ]')   # the full tier1.sh is not run as a control (it is the whole gate): the pristine library defines the function
ATK_GATES=('scripts/tier1.sh'); ATK_GATE_FILES=(scripts/tier1.sh); ATK_EXPECT='does not define nocrash_begin'
atk_apply() { neuter scripts/lib-no-crash-record.sh; }
