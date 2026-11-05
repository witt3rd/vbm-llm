ATK_DESC="add a module that declares a non-standard axiom and a theorem on it to the proofs library (the axiom gate must name it)"
ATK_GATES=('lake build VbmLlmProofs >/dev/null && lake env lean --run scripts/AxiomGate.lean'); ATK_GATE_FILES=(scripts/AxiomGate.lean); ATK_LEAN=1; ATK_EXPECT='non-standard axiom|offending'
atk_apply() { printf 'axiom atkAx : False\ntheorem atkT : False := atkAx\n' > VbmLlmProofs/AtkAxiom.lean; sed -i '1i import VbmLlmProofs.AtkAxiom' VbmLlmProofs.lean; }
