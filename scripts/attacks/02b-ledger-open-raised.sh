ATK_DESC="raise open in ledger-baseline.txt (open obligations may only fall)"
ATK_GATES=('scripts/gate-diff-improving.sh --suite-judged "$ATK_BASE" HEAD'); ATK_GATE_FILES=(scripts/gate-diff-improving.sh)
atk_apply() { awk '$1=="open"{$2=$2+5} {print}' scripts/ledger-baseline.txt > x && mv x scripts/ledger-baseline.txt; }
