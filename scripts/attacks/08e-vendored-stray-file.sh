ATK_DESC="add a file to the pinned lander's tree (scripts/land/lib/local.sh): the drift check must refuse"
ATK_GATES=('scripts/land/bin/land-check'); ATK_GATE_FILES=(scripts/land/bin/land-check)
atk_apply() { echo '# local' > scripts/land/lib/local.sh; }
