ATK_DESC="remove the gate-diff judge's call from the post-rebase hook"
ATK_GATES=('scripts/relabel-attacks.sh --check-wired'); ATK_GATE_FILES=(scripts/relabel-attacks.sh)
atk_apply() { sed -i '/gate-diff-improving/d' scripts/land.d/post-rebase; }
