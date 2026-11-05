ATK_DESC="patch the pinned lander in place (a local edit of scripts/land/bin/land-red): the drift check must refuse"
ATK_GATES=('scripts/land/bin/land-check'); ATK_GATE_FILES=(scripts/land/bin/land-check)
atk_apply() { echo '# local patch' >> scripts/land/bin/land-red; }
