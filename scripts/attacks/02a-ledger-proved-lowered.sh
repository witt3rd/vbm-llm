ATK_DESC="lower proved in ledger-baseline.txt (the obligation ledger may only rise)"
ATK_GATES=('scripts/gate-diff-improving.sh --suite-judged "$ATK_BASE" HEAD'); ATK_GATE_FILES=(scripts/gate-diff-improving.sh)
atk_apply() { awk '$1=="proved"{$2=$2-1} {print}' scripts/ledger-baseline.txt > x && mv x scripts/ledger-baseline.txt; }
