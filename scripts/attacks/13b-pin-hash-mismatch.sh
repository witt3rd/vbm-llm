ATK_DESC="edit the pinned library in place: a spec file of the checkout differs from the locked bytes while its rev still matches (spec_hash mismatch)"
ATK_CONTROL=('"$ATK_DIR/pin-check.sh"')
ATK_GATES=('"$ATK_DIR/pin-check.sh"'); ATK_GATE_FILES=(scripts/pinned-lib.py); ATK_EXPECT='spec_hash mismatch'
atk_apply() { echo hash-mismatch > atk-pin-mutation; }
