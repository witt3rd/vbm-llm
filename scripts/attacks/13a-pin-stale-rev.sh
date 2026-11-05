ATK_DESC="pin a stale rev: the lake manifest names another commit of the pinned library than the lock (a bumped dependency, the lock left behind)"
ATK_CONTROL=('"$ATK_DIR/pin-check.sh"')
ATK_GATES=('"$ATK_DIR/pin-check.sh"'); ATK_GATE_FILES=(scripts/pinned-lib.py); ATK_EXPECT='stale rev'
atk_apply() { echo stale-rev > atk-pin-mutation; }
