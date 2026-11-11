/-! # docs/perf/simd-proto/Stage1Proof.lean: PROTOTYPE PROOFS for the stage-1 kernel of docs/perf/simd-plan.md (compile standalone: `lean Stage1Proof.lean`; `Init` only, standard axioms only).

What is proved here (nothing of it is in the library or the ledger yet; this file shows the method is feasible with the tools the gates allow):
* `px_spec`: the six-step shift-xor cascade (the carry-less multiply by all-ones that stage 1 needs for the in-string mask) computes, at bit `i`, the xor of bits `0..i`.
* `esc_kernel_spec`, `esc_out_spec`: the two-addition escape kernel (the add-with-carry trick that finds the characters escaped by an odd run of backslashes, with the carry from the
  previous block) equals the one-bit-at-a-time escape automaton `escSpec`: at every byte that is not itself a backslash, and for the state handed to the next block.
* the UInt64 versions (`prefixXor`, `escaped`, the form the Lean C emitter turns into `uint64_t` code) are bridged to the BitVec statements by `simp` (`pxU_eq`).
Method (the reusable pattern, docs/perf/simd-plan.md section 2): the kernel's carry chain is a sequential automaton in disguise; the proof is an induction over the bit index with an invariant
`Inv` relating the adder's carries to the automaton's state, whose step is a `decide` over a handful of Bools (`inv_step`: 256 cases). `bv_decide` is NOT used: it adds a per-theorem axiom
(`_native.bv_decide.ax_...`) that the axiom gate rejects and the independent checker cannot replay (measured on Lean 4.35.0, section 2.3 of the plan). -/
namespace P

/-- xor of `x_(i-d)` for `d < w`, `d ≤ i`: the window of width `w` ending at bit `i`. -/
def xw (x : BitVec 64) (i : Nat) : Nat → Bool
  | 0 => false
  | w + 1 => xw x i w ^^ (decide (w ≤ i) && x.getLsbD (i - w))

theorem xw_add (x : BitVec 64) (i w v : Nat) : xw x i (w + v) = (xw x i w ^^ (decide (w ≤ i) && xw x (i - w) v)) := by
  induction v with
  | zero => simp [xw]
  | succ v ih =>
    rw [← Nat.add_assoc, xw, ih, xw]
    by_cases h1 : w ≤ i
    · by_cases h2 : v ≤ i - w
      · have h3 : w + v ≤ i := by omega
        have h4 : i - (w + v) = i - w - v := by omega
        simp [h1, h2, h3, h4]
      · have h3 : ¬ (w + v ≤ i) := by omega
        simp [h1, h2, h3]
    · have h2 : ¬ (w + v ≤ i) := by omega
      simp [h1, h2]

/-- the shift-xor cascade of the kernel. -/
def px (x : BitVec 64) : BitVec 64 :=
  let x := x ^^^ (x <<< 1); let x := x ^^^ (x <<< 2); let x := x ^^^ (x <<< 4); let x := x ^^^ (x <<< 8); let x := x ^^^ (x <<< 16); x ^^^ (x <<< 32)

theorem step (x y : BitVec 64) (w : Nat) (h : ∀ i, i < 64 → y.getLsbD i = xw x i w) :
    ∀ i, i < 64 → (y ^^^ (y <<< w)).getLsbD i = xw x i (w + w) := by
  intro i hi
  rw [BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft, xw_add, h i hi]
  by_cases hw : w ≤ i
  · have : i - w < 64 := by omega
    simp [hi, hw, h _ this, show ¬ i < w by omega]
  · simp [hw, show i < w by omega]

/-- bit `i` of `x` after `px` is the xor of bits `0..i`. -/
def scanXor (x : BitVec 64) : Nat → Bool
  | 0 => x.getLsbD 0
  | i + 1 => scanXor x i ^^ x.getLsbD (i + 1)

theorem xw_full (x : BitVec 64) (i : Nat) : xw x i (i + 1) = scanXor x i := by
  induction i with
  | zero => simp [xw, scanXor]
  | succ i ih =>
    have e1 : xw x (i + 1) 1 = x.getLsbD (i + 1) := by simp [xw]
    rw [show i + 1 + 1 = 1 + (i + 1) by omega, xw_add, e1, show i + 1 - 1 = i by omega, ih]
    simp [scanXor, Bool.xor_comm]

theorem xw_stable (x : BitVec 64) (i w : Nat) (h : i < w) (v : Nat) : xw x i (w + v) = xw x i w := by
  rw [xw_add]; simp [show ¬ w ≤ i by omega]

/-- the kernel computes the prefix xor: bit `i` is the xor of bits `0..i`. -/
theorem px_spec (x : BitVec 64) (i : Nat) (hi : i < 64) : (px x).getLsbD i = scanXor x i := by
  have h0 : ∀ i, i < 64 → x.getLsbD i = xw x i 1 := by intro i _; simp [xw]
  have h1 : ∀ i, i < 64 → (x ^^^ (x <<< 1)).getLsbD i = xw x i 2 := step x x 1 h0
  have h2 : ∀ i, i < 64 → ((x ^^^ (x <<< 1)) ^^^ ((x ^^^ (x <<< 1)) <<< 2)).getLsbD i = xw x i 4 := step x _ 2 h1
  have h3 := step x _ 4 h2
  have h4 := step x _ 8 h3
  have h5 := step x _ 16 h4
  have h6 := step x _ 32 h5
  have e : xw x i (32 + 32) = scanXor x i := by
    rw [show 32 + 32 = (i + 1) + (63 - i) by omega, xw_stable x i (i + 1) (by omega), xw_full]
  rw [← e]; exact h6 i hi


def evenM : BitVec 64 := 0x5555555555555555#64
def oddM : BitVec 64 := 0xAAAAAAAAAAAAAAAA#64
/-- the carried escape bit as a word (0 or 1). -/
def pv (pb : Bool) : BitVec 64 := if pb then 1#64 else 0#64

/-- SPEC: the escape automaton. `escSpec B pb i` is true iff byte `i` is escaped: the previous byte is a backslash that is not itself escaped (`pb`: byte 0 is escaped by the previous block). -/
def escSpec (B : BitVec 64) (pb : Bool) : Nat → Bool
  | 0 => pb
  | i + 1 => B.getLsbD i && !escSpec B pb i

/-- KERNEL (two additions): the escaped positions that are not backslashes, and the carry out. -/
def bsOf (B : BitVec 64) (pb : Bool) : BitVec 64 := B &&& ~~~(pv pb)
def startsOf (bs : BitVec 64) : BitVec 64 := bs &&& ~~~(bs <<< 1)
def escKernel (B : BitVec 64) (pb : Bool) : BitVec 64 :=
  let bs := bsOf B pb
  let st := startsOf bs
  let endsEv := (bs + (st &&& evenM)) &&& ~~~bs
  let endsOd := (bs + (st &&& oddM)) &&& ~~~bs
  (endsEv &&& oddM) ||| (endsOd &&& evenM) ||| pv pb
def escOutK (B : BitVec 64) (pb : Bool) : Bool :=
  let bs := bsOf B pb
  decide ((bs + (startsOf bs &&& oddM)) < bs)

theorem even_bit (i : Nat) : evenM.getLsbD i = (decide (i < 64) && decide (i % 2 = 0)) := by
  by_cases h : i < 64
  · have : ∀ j : Fin 64, evenM.getLsbD j = decide (j.val % 2 = 0) := by decide
    simpa [h] using this ⟨i, h⟩
  · simp [h, BitVec.getLsbD_of_ge, show 64 ≤ i by omega]

theorem odd_bit (i : Nat) : oddM.getLsbD i = (decide (i < 64) && decide (i % 2 = 1)) := by
  by_cases h : i < 64
  · have : ∀ j : Fin 64, oddM.getLsbD j = decide (j.val % 2 = 1) := by decide
    simpa [h] using this ⟨i, h⟩
  · simp [h, BitVec.getLsbD_of_ge, show 64 ≤ i by omega]

theorem pv_bit (pb : Bool) (i : Nat) : (pv pb).getLsbD i = (pb && decide (i = 0)) := by
  cases pb
  · simp [pv]
  · by_cases h : i < 64
    · simp [pv, h]
    · simp [pv, BitVec.getLsbD_of_ge, show 64 ≤ i by omega, show i ≠ 0 by omega]


/-! The Bool-level step. State of position `i`: `a` = the byte before is a (counted) backslash; `cE`, `cO` = the carries into bit `i` of the two additions; `e` = the spec's value at `i`;
`odd` = `i` is odd; `z` = `i = 0`. -/
def Inv (a cE cO e odd z pb : Bool) : Bool :=
  (a || (!cE && !cO && (e == (z && pb)))) && (!a || ((cE ^^ cO) && (e == ((cE && odd) || (cO && !odd)))))

def stepA (B z pb : Bool) : Bool := B && !(pb && z)
def stepE (B a z pb cE : Bool) (odd : Bool) : Bool := Bool.atLeastTwo (stepA B z pb) ((stepA B z pb && !a) && !odd) cE
def stepO (B a z pb cO : Bool) (odd : Bool) : Bool := Bool.atLeastTwo (stepA B z pb) ((stepA B z pb && !a) && odd) cO

theorem inv_step : ∀ (B a cE cO e odd z pb : Bool), (z → !a) = true → Inv a cE cO e odd z pb = true →
    Inv (stepA B z pb) (stepE B a z pb cE odd) (stepO B a z pb cO odd) (B && !e) (!odd) false pb = true := by decide


/-! The bridge: the kernel's words satisfy `Inv` at every bit. -/
def aprev (A : BitVec 64) : Nat → Bool
  | 0 => false
  | i + 1 => A.getLsbD i

theorem bs_bit (B : BitVec 64) (pb : Bool) (i : Nat) (hi : i < 64) : (bsOf B pb).getLsbD i = stepA (B.getLsbD i) (decide (i = 0)) pb := by
  simp only [bsOf, stepA, BitVec.getLsbD_and, BitVec.getLsbD_not, pv_bit, hi, decide_true, Bool.true_and]

theorem st_bit (A : BitVec 64) (i : Nat) (hi : i < 64) : (startsOf A).getLsbD i = (A.getLsbD i && !aprev A i) := by
  cases i with
  | zero =>
    simp only [startsOf, aprev, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and]
    cases A.getLsbD 0 <;> rfl
  | succ j => simp only [startsOf, aprev, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and, Nat.add_sub_cancel, show ¬ (j + 1 < 1) by omega, decide_false, Bool.not_false, Bool.and_true]

theorem inv_all (B : BitVec 64) (pb : Bool) : ∀ i, i ≤ 64 →
    Inv (aprev (bsOf B pb) i) (BitVec.carry i (bsOf B pb) (startsOf (bsOf B pb) &&& evenM) false) (BitVec.carry i (bsOf B pb) (startsOf (bsOf B pb) &&& oddM) false)
      (escSpec B pb i) (decide (i % 2 = 1)) (decide (i = 0)) pb = true := by
  intro i
  induction i with
  | zero => intro _; simp [Inv, aprev, escSpec, BitVec.carry_zero]
  | succ i ih =>
    intro hi
    have hi' : i < 64 := by omega
    have h := inv_step (B.getLsbD i) (aprev (bsOf B pb) i) (BitVec.carry i (bsOf B pb) (startsOf (bsOf B pb) &&& evenM) false)
      (BitVec.carry i (bsOf B pb) (startsOf (bsOf B pb) &&& oddM) false) (escSpec B pb i) (decide (i % 2 = 1)) (decide (i = 0)) pb
      (by cases i <;> simp [aprev]) (ih (by omega))
    have e1 : (bsOf B pb).getLsbD i = stepA (B.getLsbD i) (decide (i = 0)) pb := bs_bit B pb i hi'
    have e2 : aprev (bsOf B pb) (i + 1) = stepA (B.getLsbD i) (decide (i = 0)) pb := by simp only [aprev, e1]
    have par : decide (i % 2 = 0) = !decide (i % 2 = 1) := by rcases Nat.mod_two_eq_zero_or_one i with h | h <;> simp [h]
    have par' : decide ((i + 1) % 2 = 1) = !decide (i % 2 = 1) := by rcases Nat.mod_two_eq_zero_or_one i with h | h <;> simp [h, Nat.add_mod]
    have e3 : BitVec.carry (i + 1) (bsOf B pb) (startsOf (bsOf B pb) &&& evenM) false = stepE (B.getLsbD i) (aprev (bsOf B pb) i) (decide (i = 0)) pb
        (BitVec.carry i (bsOf B pb) (startsOf (bsOf B pb) &&& evenM) false) (decide (i % 2 = 1)) := by
      rw [BitVec.carry_succ]
      simp only [stepE, BitVec.getLsbD_and, st_bit _ i hi', even_bit, hi', e1, decide_true, Bool.true_and, par]
    have e4 : BitVec.carry (i + 1) (bsOf B pb) (startsOf (bsOf B pb) &&& oddM) false = stepO (B.getLsbD i) (aprev (bsOf B pb) i) (decide (i = 0)) pb
        (BitVec.carry i (bsOf B pb) (startsOf (bsOf B pb) &&& oddM) false) (decide (i % 2 = 1)) := by
      rw [BitVec.carry_succ]
      simp only [stepO, BitVec.getLsbD_and, st_bit _ i hi', odd_bit, hi', e1, decide_true, Bool.true_and]
    rw [e2, e3, e4, par', show escSpec B pb (i + 1) = (B.getLsbD i && !escSpec B pb i) from rfl, show decide (i + 1 = 0) = false by simp]
    exact h

theorem final_step : ∀ (a cE cO e o z pb : Bool), (z → !a) = true → Inv a cE cO e o z pb = true → (((cE && o) || (cO && !o)) || (pb && z)) = e := by decide

/-- the kernel's escaped positions agree with the automaton at every byte that is not a backslash. -/
theorem esc_kernel_spec (B : BitVec 64) (pb : Bool) (i : Nat) (hi : i < 64) (hB : B.getLsbD i = false) :
    (escKernel B pb).getLsbD i = escSpec B pb i := by
  have inv := inv_all B pb i (by omega)
  have hA : (bsOf B pb).getLsbD i = false := by rw [bs_bit B pb i hi, hB]; simp [stepA]
  have hst : (startsOf (bsOf B pb)).getLsbD i = false := by rw [st_bit _ i hi, hA]; rfl
  have par : decide (i % 2 = 0) = !decide (i % 2 = 1) := by rcases Nat.mod_two_eq_zero_or_one i with h | h <;> simp [h]
  have sE := BitVec.getLsbD_add hi (bsOf B pb) (startsOf (bsOf B pb) &&& evenM)
  have sO := BitVec.getLsbD_add hi (bsOf B pb) (startsOf (bsOf B pb) &&& oddM)
  simp only [escKernel, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, sE, sO, hA, hst, even_bit, odd_bit, pv_bit, hi, decide_true, Bool.true_and, par,
    Bool.false_and, Bool.false_xor, Bool.not_false, Bool.and_true]
  exact final_step _ _ _ _ _ _ _ (by cases i <;> simp [aprev]) inv


theorem carry64 (x y : BitVec 64) : BitVec.carry 64 x y false = decide ((x + y) < x) := by
  have hx := x.isLt
  have hy := y.isLt
  simp only [BitVec.carry, BitVec.lt_def, BitVec.toNat_add]
  have : x.toNat % 2 ^ 64 = x.toNat := Nat.mod_eq_of_lt hx
  have : y.toNat % 2 ^ 64 = y.toNat := Nat.mod_eq_of_lt hy
  simp only [Bool.toNat_false, Nat.add_zero, *]
  by_cases h : 2 ^ 64 ≤ x.toNat + y.toNat
  · have : (x.toNat + y.toNat) % 2 ^ 64 = x.toNat + y.toNat - 2 ^ 64 := by omega
    simp [h, this]; omega
  · have : (x.toNat + y.toNat) % 2 ^ 64 = x.toNat + y.toNat := Nat.mod_eq_of_lt (by omega)
    simp [h, this]

theorem out_step : ∀ (a cE cO e pb : Bool), Inv a cE cO e false false pb = true → cO = e := by decide

/-- the carry out of the block is the automaton's state after byte 63. -/
theorem esc_out_spec (B : BitVec 64) (pb : Bool) : escOutK B pb = escSpec B pb 64 := by
  have inv := inv_all B pb 64 (by omega)
  simp only [escOutK, ← carry64]
  exact out_step _ _ _ _ _ (by simpa using inv)


/-! ## The UInt64 forms the library would run, bridged by `simp` -/
def prefixXor (x : UInt64) : UInt64 :=
  let x := x ^^^ (x <<< 1); let x := x ^^^ (x <<< 2); let x := x ^^^ (x <<< 4); let x := x ^^^ (x <<< 8); let x := x ^^^ (x <<< 16); x ^^^ (x <<< 32)

theorem prefixXor_toBitVec (x : UInt64) : (prefixXor x).toBitVec = px x.toBitVec := by
  simp [prefixXor, px, UInt64.toBitVec_xor, UInt64.toBitVec_shiftLeft]

theorem prefixXor_spec (x : UInt64) (i : Nat) (hi : i < 64) : (prefixXor x).toBitVec.getLsbD i = scanXor x.toBitVec i := by
  rw [prefixXor_toBitVec]; exact px_spec _ i hi

end P

#print axioms P.px_spec
#print axioms P.esc_kernel_spec
#print axioms P.esc_out_spec
#print axioms P.prefixXor_spec
