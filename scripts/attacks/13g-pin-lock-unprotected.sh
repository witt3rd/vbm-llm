ATK_DESC="drop the lock from scripts/protected-paths.txt (a lock outside the protected set can be loosened unseen)"
ATK_GATES=('python3 scripts/pinned-lib.py protected'); ATK_GATE_FILES=(scripts/pinned-lib.py); ATK_EXPECT='not protected'
atk_apply() { sed -i '/^scripts\/pinned-libs\.lock$/d' scripts/protected-paths.txt; }
