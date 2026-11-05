ATK_DESC="a fork under the pinned name: the checkout is another repository at another commit (the manifest still claims the locked rev)"
ATK_CONTROL=('"$ATK_DIR/pin-check.sh"')
ATK_GATES=('"$ATK_DIR/pin-check.sh"'); ATK_GATE_FILES=(scripts/pinned-lib.py); ATK_EXPECT='fork or a moved checkout'
atk_apply() { echo fork > atk-pin-mutation; }
