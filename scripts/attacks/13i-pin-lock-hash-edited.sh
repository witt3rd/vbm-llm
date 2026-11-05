ATK_DESC="edit the lock's spec_hash (and nothing else) to a value the checkout does not have: the verify step refuses a lock that does not describe the library on disk"
ATK_CONTROL=('"$ATK_DIR/pin-check.sh"')
ATK_GATES=('"$ATK_DIR/pin-check.sh"'); ATK_GATE_FILES=(scripts/pinned-lib.py); ATK_EXPECT='spec_hash mismatch'
atk_apply() { echo lock-hash > atk-pin-mutation; }
