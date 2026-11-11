import LeanJsonSimd.Stage1
import VbmSimdProofs
/-! # Proof: stage 1 computes the structural machine, block by block (`LeanJson.Stage1`, `LeanJson.Struct`)

Slice S2 of `docs/perf/simd-plan.md`. For one block of 64 bytes `g` (as eight words) and the machine's state `s0` before it, `blockOut` returns the structural mask whose bit `p` is the machine's output at byte `p`, and the
three bits of the state after the block (`blockOut_spec`). The proof composes the proved kernels of `VbmSimd` (the compare and pack of byte lanes, the escape carry, the prefix xor) with three small inductions over the byte
index relating the machine's `esc`, `str`, `scal` to those kernels' outputs. The next slice threads the carries through consecutive blocks. -/
namespace LeanJsonProofs
open LeanJson VbmSimd VbmSimdProofs

/-! ## Bytes -/

/-- Byte `j` of a word, as a `UInt8`. -/
def u8 (w : UInt64) (j : Nat) : UInt8 := UInt8.ofBitVec (byte w j)

theorem laneEq_u8 (c w : UInt64) (j : Nat) : laneEq c w j = (u8 w j == u8 c j) := by
  unfold laneEq u8
  by_cases h : byte w j = byte c j
  · simp [h]
  · have h' : ¬ UInt8.ofBitVec (byte w j) = UInt8.ofBitVec (byte c j) := fun hh => h (UInt8.ofBitVec.inj hh)
    simp [h, h']

theorem u8_or (w c : UInt64) (j : Nat) : u8 (w ||| c) j = u8 w j ||| u8 c j := by
  simp [u8, byte, BitVec.extractLsb'_or]

/-- A statement about every byte, from its 256 cases (as 16 times 16, so `decide` stays within the elaborator's recursion limit). -/
theorem u8_forall (P : UInt8 → Prop) (h : ∀ a b : Fin 16, P (UInt8.ofNat (16 * a + b))) : ∀ x, P x := fun x => by
  have hx := x.toNat_lt
  have := h ⟨x.toNat / 16, by simp at hx; omega⟩ ⟨x.toNat % 16, by omega⟩
  have e : 16 * (x.toNat / 16) + x.toNat % 16 = x.toNat := by omega
  simpa [e] using this

theorem op_cases : ∀ x : UInt8, ((x ||| 0x20 == 0x7b) || (x ||| 0x20 == 0x7d) || x == 0x3a || x == 0x2c) = isOp x := u8_forall _ (by decide)
theorem ws_cases : ∀ x : UInt8, (x == 0x20 || x == 0x09 || x == 0x0a || x == 0x0d) = isWs x := u8_forall _ (by decide)

theorem u8_cQuote : ∀ j : Fin 8, u8 cQuote j = 0x22 := by decide
theorem u8_cBslash : ∀ j : Fin 8, u8 cBslash j = 0x5c := by decide
theorem u8_cLbrace : ∀ j : Fin 8, u8 cLbrace j = 0x7b := by decide
theorem u8_cRbrace : ∀ j : Fin 8, u8 cRbrace j = 0x7d := by decide
theorem u8_cColon : ∀ j : Fin 8, u8 cColon j = 0x3a := by decide
theorem u8_cComma : ∀ j : Fin 8, u8 cComma j = 0x2c := by decide
theorem u8_cSpace : ∀ j : Fin 8, u8 cSpace j = 0x20 := by decide
theorem u8_cTab : ∀ j : Fin 8, u8 cTab j = 0x09 := by decide
theorem u8_cLf : ∀ j : Fin 8, u8 cLf j = 0x0a := by decide
theorem u8_cCr : ∀ j : Fin 8, u8 cCr j = 0x0d := by decide

/-! ## The class masks of a block -/

/-- `g` gives the bytes of the block, and `w0 .. w7` are its eight words. -/
def Blk (g : Nat → UInt8) (w0 w1 w2 w3 w4 w5 w6 w7 : UInt64) : Prop := ∀ p, p < 64 → u8 (blockWord w0 w1 w2 w3 w4 w5 w6 w7 (p / 8)) (p % 8) = g p

theorem eqMask64_u8 {g : Nat → UInt8} {w0 w1 w2 w3 w4 w5 w6 w7 : UInt64} (hb : Blk g w0 w1 w2 w3 w4 w5 w6 w7) (c : UInt64) (x : UInt8) (hc : ∀ j : Fin 8, u8 c j = x)
    (p : Nat) (hp : p < 64) : bit (eqMask64 c w0 w1 w2 w3 w4 w5 w6 w7) p = (g p == x) := by
  have := eqMask64_spec c w0 w1 w2 w3 w4 w5 w6 w7 (p / 8) (p % 8) (by omega) (by omega)
  rw [show 8 * (p / 8) + p % 8 = p by omega] at this
  rw [this, laneEq_u8, hb p hp, hc ⟨p % 8, by omega⟩]

theorem opWord_bit (w : UInt64) (j : Nat) (hj : j < 8) :
    bit (opWord w) j = ((u8 w j ||| 0x20 == 0x7b) || (u8 w j ||| 0x20 == 0x7d) || u8 w j == 0x3a || u8 w j == 0x2c) := by
  have hlow : ∀ i, i < 64 → i % 8 ≠ 7 → bit (eqLanes cLbrace (w ||| cSpace) ||| eqLanes cRbrace (w ||| cSpace) ||| eqLanes cColon w ||| eqLanes cComma w) i = false := by
    intro i hi h
    simp [bit_or, eqLanes_low _ _ i hi h]
  have h1 := pack8_spec _ hlow j hj
  have h2 : ∀ c w', bit (eqLanes c w') (8 * j + 7) = laneEq c w' j := fun c w' => eqLanes_spec c w' j hj
  unfold opWord
  simp only [h1, laneFlag, bit_or, h2, laneEq_u8, u8_or, u8_cSpace ⟨j, hj⟩, u8_cLbrace ⟨j, hj⟩, u8_cRbrace ⟨j, hj⟩, u8_cColon ⟨j, hj⟩, u8_cComma ⟨j, hj⟩]

theorem wsWord_bit (w : UInt64) (j : Nat) (hj : j < 8) :
    bit (wsWord w) j = (u8 w j == 0x20 || u8 w j == 0x09 || u8 w j == 0x0a || u8 w j == 0x0d) := by
  have hlow : ∀ i, i < 64 → i % 8 ≠ 7 → bit (eqLanes cSpace w ||| eqLanes cTab w ||| eqLanes cLf w ||| eqLanes cCr w) i = false := by
    intro i hi h
    simp [bit_or, eqLanes_low _ _ i hi h]
  have h1 := pack8_spec _ hlow j hj
  have h2 : ∀ c, bit (eqLanes c w) (8 * j + 7) = laneEq c w j := fun c => eqLanes_spec c w j hj
  unfold wsWord
  simp only [h1, laneFlag, bit_or, h2, laneEq_u8, u8_cSpace ⟨j, hj⟩, u8_cTab ⟨j, hj⟩, u8_cLf ⟨j, hj⟩, u8_cCr ⟨j, hj⟩]

theorem opMask_bit {g : Nat → UInt8} {w0 w1 w2 w3 w4 w5 w6 w7 : UInt64} (hb : Blk g w0 w1 w2 w3 w4 w5 w6 w7) (p : Nat) (hp : p < 64) :
    bit (mask8 opWord w0 w1 w2 w3 w4 w5 w6 w7) p = isOp (g p) := by
  have hf : ∀ w i, 8 ≤ i → bit (opWord w) i = false := fun w i hi => by
    unfold opWord
    exact pack8_high _ (fun i' hi' h => by simp [bit_or, eqLanes_low _ _ i' hi' h]) i hi
  have := mask8_bit opWord hf w0 w1 w2 w3 w4 w5 w6 w7 (p / 8) (p % 8) (by omega) (by omega)
  rw [show 8 * (p / 8) + p % 8 = p by omega] at this
  rw [this, opWord_bit _ _ (by omega), hb p hp, op_cases]

theorem wsMask_bit {g : Nat → UInt8} {w0 w1 w2 w3 w4 w5 w6 w7 : UInt64} (hb : Blk g w0 w1 w2 w3 w4 w5 w6 w7) (p : Nat) (hp : p < 64) :
    bit (mask8 wsWord w0 w1 w2 w3 w4 w5 w6 w7) p = isWs (g p) := by
  have hf : ∀ w i, 8 ≤ i → bit (wsWord w) i = false := fun w i hi => by
    unfold wsWord
    exact pack8_high _ (fun i' hi' h => by simp [bit_or, eqLanes_low _ _ i' hi' h]) i hi
  have := mask8_bit wsWord hf w0 w1 w2 w3 w4 w5 w6 w7 (p / 8) (p % 8) (by omega) (by omega)
  rw [show 8 * (p / 8) + p % 8 = p by omega] at this
  rw [this, wsWord_bit _ _ (by omega), hb p hp, ws_cases]

/-! ## The machine over a block -/

/-- The machine run over the bytes `g 0, g 1, ...` from the state `s0`: the state before byte `p`. -/
def sAtG (g : Nat → UInt8) (s0 : SState) : Nat → SState
  | 0 => s0
  | p + 1 => (sStep (sAtG g s0 p) (g p)).1

/-- Running the machine over a whole input and over a block of it from the state before the block agree. -/
theorem sAt_add (a : ByteArray) (k : Nat) : ∀ p, sAt a (k + p) = sAtG (fun i => byteD a (k + i)) (sAt a k) p := by
  intro p
  induction p with
  | zero => rfl
  | succ p ih => rw [← Nat.add_assoc]; simp only [sAt, sAtG, ih]

/-- The escape state is the escape machine of `[VS-2]`. -/
theorem esc_eq (g : Nat → UInt8) (b : UInt64) (hbm : ∀ p, p < 64 → bit b p = (g p == 0x5c)) (s0 : SState) :
    ∀ p, p ≤ 64 → (sAtG g s0 p).esc = escSpec b s0.esc p := by
  intro p
  induction p with
  | zero => intro _; rfl
  | succ p ih =>
    intro hp
    have := ih (by omega)
    simp only [sAtG, sStep, escSpec, this, hbm p (by omega)]

/-- A quote is an unescaped quote exactly when the kernel's `q &&& ~~~escaped` says so. -/
theorem isQ_eq (g : Nat → UInt8) (q b : UInt64) (hq : ∀ p, p < 64 → bit q p = (g p == 0x22)) (hbm : ∀ p, p < 64 → bit b p = (g p == 0x5c)) (s0 : SState)
    (hqb : q &&& b = 0) (p : Nat) (hp : p < 64) :
    isQ (sAtG g s0 p) (g p) = bit (q &&& ~~~(escaped b (carryWord s0.esc))) p := by
  rw [quote_not_escaped_spec q b s0.esc hqb p hp, hq p hp]
  unfold isQ
  rw [esc_eq g b hbm s0 p (by omega)]

/-- The string state after byte `p` is the string kernel's prefix xor. -/
theorem str_eq (g : Nat → UInt8) (s0 : SState) (qq : UInt64) (hqq : ∀ p, p < 64 → bit qq p = isQ (sAtG g s0 p) (g p)) :
    ∀ p, p < 64 → (sAtG g s0 (p + 1)).str = (s0.str ^^ scanXor qq p) := by
  intro p
  induction p with
  | zero =>
    intro _
    have := hqq 0 (by omega)
    simp only [sAtG, sStep, scanXor, this]
  | succ p ih =>
    intro hp
    have h1 := ih (by omega)
    have h2 := hqq (p + 1) hp
    show ((sStep (sAtG g s0 (p + 1)) (g (p + 1))).1).str = _
    simp only [sStep, h1, scanXor, ← h2]
    simp [bne]
    cases s0.str <;> cases scanXor qq p <;> cases bit qq (p + 1) <;> simp

theorem bit_carryWord (c : Bool) (i : Nat) : bit (carryWord c) i = (c && decide (i = 0)) := by
  cases c
  · simp [carryWord, bit]
  · by_cases h : i = 0
    · subst h; simp [carryWord, bit]
    · simp [carryWord, bit, h]

theorem shr63 (x : UInt64) : x >>> 63 = carryWord (bit x 63) := by
  apply ext_bits
  intro i hi
  have e : (x >>> 63).toBitVec = x.toBitVec >>> 63 := by simp [UInt64.toBitVec_shiftRight]
  rw [bit_carryWord]
  simp only [bit, e, BitVec.getLsbD_ushiftRight]
  by_cases h : i = 0
  · subst h; simp
  · have : ¬ (63 + i < 64) := by omega
    simp [h, BitVec.getLsbD_of_ge, show 64 ≤ 63 + i by omega]

theorem bit_shl1 (x : UInt64) (i : Nat) (hi : i < 64) : bit (x <<< 1) i = (decide (1 ≤ i) && bit x (i - 1)) :=
  bit_shl x 1 (by omega) i hi

theorem out_bit (o qq inS nqm follows : UInt64) (p : Nat) (hp : p < 64) :
    bit ((o &&& ~~~inS) ||| qq ||| (nqm &&& ~~~follows &&& ~~~inS)) p = ((bit o p && !bit inS p) || bit qq p || (bit nqm p && !bit follows p && !bit inS p)) := by
  simp only [bit_or, bit_and, bit_not _ _ hp]

/-- Stage 1 for one block, from the class masks: bit `p` of the structural mask is the machine's output at byte `p`, and the carries out are the machine's state after byte 63. -/
theorem maskOut_spec (g : Nat → UInt8) (q b o ws : UInt64) (e0 st0 sc0 : Bool)
    (hq : ∀ p, p < 64 → bit q p = (g p == 0x22)) (hb : ∀ p, p < 64 → bit b p = (g p == 0x5c))
    (ho : ∀ p, p < 64 → bit o p = isOp (g p)) (hw : ∀ p, p < 64 → bit ws p = isWs (g p)) :
    let s0 : SState := ⟨e0, st0, sc0⟩
    let r := maskOut q b o ws (carryWord e0) (carryWord st0) (carryWord sc0)
    (∀ p, p < 64 → bit r.1 p = (sStep (sAtG g s0 p) (g p)).2) ∧ r.2.1 = carryWord (sAtG g s0 64).esc ∧ r.2.2.1 = carryWord (sAtG g s0 64).str ∧
      r.2.2.2 = carryWord (sAtG g s0 64).scal := by
  intro s0 r
  -- q and b are disjoint (a byte is not both a quote and a backslash)
  have hqb : q &&& b = 0 := by
    apply ext_bits
    intro i hi
    rw [bit_and, hq i hi, hb i hi]
    have : bit (0 : UInt64) i = false := by simp [bit]
    rw [this]
    cases hh : g i == 0x22 <;> cases hh2 : g i == 0x5c <;> simp
    have h1 : g i = 0x22 := by simpa using hh
    have h2 : g i = 0x5c := by simpa using hh2
    rw [h1] at h2; exact absurd h2 (by decide)
  have hqq : ∀ p, p < 64 → bit (q &&& ~~~(escaped b (carryWord e0))) p = isQ (sAtG g s0 p) (g p) :=
    fun p hp => (isQ_eq g q b hq hb s0 hqb p hp).symm
  have hstr := str_eq g s0 _ hqq
  have hin : ∀ p, p < 64 → bit (prefixXorC (q &&& ~~~(escaped b (carryWord e0))) (carryWord st0)) p = (sAtG g s0 (p + 1)).str := by
    intro p hp
    rw [hstr p hp, prefixXorC_spec _ st0 p hp]
  have hnq : ∀ p, p < 64 → bit (~~~(o ||| ws ||| (q &&& ~~~(escaped b (carryWord e0))))) p = isNq (sAtG g s0 p) (g p) := by
    intro p hp
    rw [bit_not _ _ hp, bit_or, bit_or, ho p hp, hw p hp, hqq p hp]
    simp [isNq]
  have hscal : ∀ p, p < 64 → bit ((~~~(o ||| ws ||| (q &&& ~~~(escaped b (carryWord e0))))) <<< 1 ||| carryWord sc0) p = (sAtG g s0 p).scal := by
    intro p hp
    rw [bit_or, bit_shl1 _ _ hp, bit_carryWord]
    cases p with
    | zero => simp [sAtG, s0]
    | succ p =>
      simp only [Nat.add_sub_cancel]
      rw [hnq p (by omega)]
      simp [sAtG, sStep]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp
    simp only [r, maskOut]
    rw [out_bit _ _ _ _ _ p hp, hnq p hp, hscal p hp, hin p hp, hqq p hp, ho p hp]
    have hs : (sAtG g s0 (p + 1)).str = ((sAtG g s0 p).str != isQ (sAtG g s0 p) (g p)) := rfl
    rw [hs]
    simp only [sStep]
    cases isQ (sAtG g s0 p) (g p) <;> cases (sAtG g s0 p).str <;> cases (sAtG g s0 p).scal <;> cases isOp (g p) <;> cases isNq (sAtG g s0 p) (g p) <;> simp
  · simp only [r, maskOut]
    rw [escOut_spec, esc_eq g b hb s0 64 (Nat.le_refl _)]
  · simp only [r, maskOut]
    rw [shr63, hin 63 (by omega)]
  · simp only [r, maskOut]
    rw [shr63, hnq 63 (by omega)]
    rfl

/-- Stage 1 for one block of eight words: the structural mask and the carries, against the machine run over the block's bytes. -/
theorem blockOut_spec (g : Nat → UInt8) (w0 w1 w2 w3 w4 w5 w6 w7 : UInt64) (hbk : Blk g w0 w1 w2 w3 w4 w5 w6 w7) (e0 st0 sc0 : Bool) :
    let s0 : SState := ⟨e0, st0, sc0⟩
    let r := blockOut w0 w1 w2 w3 w4 w5 w6 w7 (carryWord e0) (carryWord st0) (carryWord sc0)
    (∀ p, p < 64 → bit r.1 p = (sStep (sAtG g s0 p) (g p)).2) ∧ r.2.1 = carryWord (sAtG g s0 64).esc ∧ r.2.2.1 = carryWord (sAtG g s0 64).str ∧
      r.2.2.2 = carryWord (sAtG g s0 64).scal := by
  have hq : ∀ p, p < 64 → bit (eqMask64 cQuote w0 w1 w2 w3 w4 w5 w6 w7) p = (g p == 0x22) := fun p hp =>
    eqMask64_u8 hbk cQuote 0x22 u8_cQuote p hp
  have hb : ∀ p, p < 64 → bit (eqMask64 cBslash w0 w1 w2 w3 w4 w5 w6 w7) p = (g p == 0x5c) := fun p hp =>
    eqMask64_u8 hbk cBslash 0x5c u8_cBslash p hp
  exact maskOut_spec g _ _ _ _ e0 st0 sc0 hq hb (opMask_bit hbk) (wsMask_bit hbk)

/-! ## Loads: the eight words of block `k` are the bytes of the block -/

theorem u8_ld64Model (a : ByteArray) (base j : Nat) (hj : j < 8) : u8 (ld64Model a base) j = byteAt0 a (base + j) := by
  unfold u8
  have : byte (ld64Model a base) j = (byteAt0 a (base + j)).toBitVec := by
    apply BitVec.eq_of_getLsbD_eq
    intro b hb
    simp only [byte, BitVec.getLsbD_extractLsb', hb, decide_true, Bool.true_and]
    exact ld64Model_bit a base j b hj hb
  rw [this]

theorem blk_ld64Model (a : ByteArray) (base : Nat) :
    Blk (fun p => byteAt0 a (base + p)) (ld64Model a base) (ld64Model a (base + 8)) (ld64Model a (base + 16)) (ld64Model a (base + 24)) (ld64Model a (base + 32))
      (ld64Model a (base + 40)) (ld64Model a (base + 48)) (ld64Model a (base + 56)) := by
  intro p hp
  have hm : p / 8 = 0 ∨ p / 8 = 1 ∨ p / 8 = 2 ∨ p / 8 = 3 ∨ p / 8 = 4 ∨ p / 8 = 5 ∨ p / 8 = 6 ∨ p / 8 = 7 := by omega
  rcases hm with h | h | h | h | h | h | h | h <;>
    simp only [blockWord, h] <;>
    rw [u8_ld64Model _ _ _ (by omega)] <;> congr 1 <;> omega

/-! ## The loop -/

theorem stage1Loop_ge (a out : ByteArray) (k n : Nat) (esc str scal : UInt64) (h : ¬ k < n) : stage1Loop a out k n esc str scal = out := by
  rw [stage1Loop]; simp only [h, ↓reduceIte]

theorem stage1Loop_lt (a out : ByteArray) (k n : Nat) (esc str scal : UInt64) (h : k < n) :
    stage1Loop a out k n esc str scal =
      match blockOut (ld64 a (64 * k).toUSize) (ld64 a (64 * k + 8).toUSize) (ld64 a (64 * k + 16).toUSize) (ld64 a (64 * k + 24).toUSize)
        (ld64 a (64 * k + 32).toUSize) (ld64 a (64 * k + 40).toUSize) (ld64 a (64 * k + 48).toUSize) (ld64 a (64 * k + 56).toUSize) esc str scal with
      | (s, esc', str', scal') => stage1Loop a (st64 out k.toUSize s) (k + 1) n esc' str' scal' := by
  conv => lhs; rw [stage1Loop]
  simp only [h, ↓reduceIte]

theorem ld64_toUSize (a : ByteArray) (x : Nat) (hx : x < 2 ^ 32) : ld64 a x.toUSize = ld64Model a x := by
  show ld64Model a (x.toUSize).toNat = _
  rw [show (x.toUSize).toNat = x from USize.toNat_ofNat_of_lt_32 hx]

theorem st64_toUSize (a : ByteArray) (k : Nat) (w : UInt64) (hk : k < 2 ^ 32) : st64 a k.toUSize w = st64Model a k w := by
  show st64Model a (k.toUSize).toNat w = _
  rw [show (k.toUSize).toNat = k from USize.toNat_ofNat_of_lt_32 hk]

/-- Stage 1 over blocks `k .. n - 1`: every word of the result has the structural mask of its block, the earlier words and the size are untouched. -/
theorem stage1Loop_spec (a : ByteArray) (n : Nat) (hn : 64 * n + 64 < 2 ^ 32) :
    ∀ d k out esc str scal, n - k = d → esc = carryWord (sAt a (64 * k)).esc → str = carryWord (sAt a (64 * k)).str → scal = carryWord (sAt a (64 * k)).scal →
      8 * n ≤ out.size →
      (stage1Loop a out k n esc str scal).size = out.size ∧
      (∀ j, j < k → ld64Model (stage1Loop a out k n esc str scal) (8 * j) = ld64Model out (8 * j)) ∧
      (∀ j, k ≤ j → j < n → ∀ p, p < 64 → bit (ld64Model (stage1Loop a out k n esc str scal) (8 * j)) p = isStruct a (64 * j + p)) := by
  intro d
  induction d with
  | zero =>
    intro k out esc str scal hd _ _ _ _
    rw [stage1Loop_ge a out k n esc str scal (by omega)]
    exact ⟨rfl, fun _ _ => rfl, fun j hj hjn => by omega⟩
  | succ d ih =>
    intro k out esc str scal hd he hs hc hout
    have hk : k < n := by omega
    rw [stage1Loop_lt a out k n esc str scal hk]
    have l0 := ld64_toUSize a (64 * k) (by omega)
    have l1 := ld64_toUSize a (64 * k + 8) (by omega)
    have l2 := ld64_toUSize a (64 * k + 16) (by omega)
    have l3 := ld64_toUSize a (64 * k + 24) (by omega)
    have l4 := ld64_toUSize a (64 * k + 32) (by omega)
    have l5 := ld64_toUSize a (64 * k + 40) (by omega)
    have l6 := ld64_toUSize a (64 * k + 48) (by omega)
    have l7 := ld64_toUSize a (64 * k + 56) (by omega)
    rw [l0, l1, l2, l3, l4, l5, l6, l7, he, hs, hc]
    obtain ⟨hbits, hesc, hstr, hscal⟩ := blockOut_spec (fun p => byteAt0 a (64 * k + p)) _ _ _ _ _ _ _ _ (blk_ld64Model a (64 * k)) (sAt a (64 * k)).esc (sAt a (64 * k)).str (sAt a (64 * k)).scal
    have hsA : sAtG (fun p => byteAt0 a (64 * k + p)) ⟨(sAt a (64 * k)).esc, (sAt a (64 * k)).str, (sAt a (64 * k)).scal⟩ 64 = sAt a (64 * (k + 1)) := by
      rw [show 64 * (k + 1) = 64 * k + 64 by omega, sAt_add a (64 * k) 64]
      rfl
    rw [hsA] at hesc hstr hscal
    generalize blockOut (ld64Model a (64 * k)) (ld64Model a (64 * k + 8)) (ld64Model a (64 * k + 16)) (ld64Model a (64 * k + 24)) (ld64Model a (64 * k + 32))
      (ld64Model a (64 * k + 40)) (ld64Model a (64 * k + 48)) (ld64Model a (64 * k + 56)) (carryWord (sAt a (64 * k)).esc) (carryWord (sAt a (64 * k)).str)
      (carryWord (sAt a (64 * k)).scal) = r at hbits hesc hstr hscal ⊢
    obtain ⟨rs, re, rst, rsc⟩ := r
    dsimp only at hbits hesc hstr hscal ⊢
    rw [st64_toUSize out k rs (by omega)]
    have hsz : (st64Model out k rs).size = out.size := st64Model_size out k rs
    obtain ⟨h1, h2, h3⟩ := ih (k + 1) (st64Model out k rs) re rst rsc (by omega) (by rw [hesc]) (by rw [hstr]) (by rw [hscal]) (by omega)
    refine ⟨by rw [h1, hsz], fun j hj => ?_, fun j hkj hjn p hp => ?_⟩
    · rw [h2 j (by omega), ld64Model_st64Model_other out k rs j (by omega)]
    · by_cases hjk : j = k
      · subst hjk
        rw [h2 j (by omega), ld64Model_st64Model_self out j rs (by omega), hbits p hp]
        have := sAt_add a (64 * j) p
        simp only [isStruct, byteD, this]
        rfl
      · exact h3 j (by omega) hjn p hp

/-! ## The driver: the last partial block -/

/-- The low `r` bits of a word (`r < 64`): `(1 <<< r) - 1`. -/
theorem bit_lowMask (r p : Nat) (hr : r < 64) (hp : p < 64) : bit (((1 : UInt64) <<< r.toUInt64) - 1) p = decide (p < r) := by
  have e : ((1 : UInt64) <<< r.toUInt64).toBitVec = 1#64 <<< r := by
    simp [UInt64.toBitVec_shiftLeft, Nat.mod_eq_of_lt hr]
  have h1 : (((1 : UInt64) <<< r.toUInt64) - 1).toBitVec = ~~~(-(1#64 <<< r)) := by
    rw [UInt64.toBitVec_sub, e]; exact sub_one_eq_not_neg _
  simp only [bit, h1, BitVec.getLsbD_not, hp, decide_true, Bool.true_and, BitVec.getLsbD_neg]
  have hs : ∀ i, (1#64 <<< r).getLsbD i = (decide (i = r) && decide (i < 64)) := by
    intro i
    rw [BitVec.getLsbD_shiftLeft]
    by_cases hi : i < r
    · simp [hi, show i ≠ r by omega]
    · by_cases hir : i = r
      · subst hir; simp
      · have : (1#64).getLsbD (i - r) = false := by
          simp only [BitVec.getLsbD, BitVec.toNat_ofNat]
          exact Nat.testBit_lt_two_pow (by simpa using Nat.one_lt_two_pow (show i - r ≠ 0 by omega))
        simp [hi, hir, this]
  rw [hs]
  by_cases hpr : p < r
  · have hne : ¬ (∃ j, j < p ∧ (1#64 <<< r).getLsbD j = true) := by
      rintro ⟨j, hj, hh⟩; rw [hs] at hh; simp at hh; omega
    simp [hs, hpr, show p ≠ r by omega]
    intro x hx hxr; omega
  · by_cases hpr' : p = r
    · have hne : ¬ (∃ j, j < p ∧ (1#64 <<< r).getLsbD j = true) := by
        rintro ⟨j, hj, hh⟩; rw [hs] at hh; simp at hh; omega
      rw [decide_eq_false hne, decide_eq_true hpr', decide_eq_true hp, decide_eq_false hpr]; rfl
    · have hex : ∃ j, j < p ∧ (1#64 <<< r).getLsbD j = true := ⟨r, by omega, by rw [hs]; simp [hr]⟩
      rw [decide_eq_false hpr', decide_eq_true hex, decide_eq_false hpr]; rfl

/-- The size of the mask array and each word of it: stage 1 of `a` is, in bit `p` of word `j`, whether byte `64 j + p` is structural and inside `a`. -/
theorem stage1_spec (a : ByteArray) (h : a.size < 2 ^ 31) :
    (stage1 a).size = 8 * ((a.size + 63) / 64) ∧
    ∀ j, j < (a.size + 63) / 64 → ∀ p, p < 64 → bit (ld64Model (stage1 a) (8 * j)) p = (isStruct a (64 * j + p) && decide (64 * j + p < a.size)) := by
  have hz := zeroBytes_spec (8 * ((a.size + 63) / 64))
  obtain ⟨hL1, hL2, hL3⟩ := stage1Loop_spec a ((a.size + 63) / 64) (by omega) ((a.size + 63) / 64 - 0) 0 (zeroBytes (8 * ((a.size + 63) / 64))) 0 0 0 rfl rfl rfl rfl (by have := hz.1; omega)
  rw [hz.1] at hL1
  by_cases hm : a.size % 64 = 0
  · have e : (a.size % 64 == 0) = true := by simp [hm]
    unfold stage1
    simp only [e, ↓reduceIte]
    refine ⟨hL1, fun j hj p hp => ?_⟩
    rw [hL3 j (by omega) hj p hp]
    have : 64 * j + p < a.size := by omega
    simp [this]
  · have e : (a.size % 64 == 0) = false := by simp [hm]
    unfold stage1
    simp only [e, Bool.false_eq_true, ↓reduceIte]
    generalize hR : stage1Loop a (zeroBytes (8 * ((a.size + 63) / 64))) 0 ((a.size + 63) / 64) 0 0 0 = R at hL1 hL3
    have hn : (a.size + 63) / 64 - 1 + 1 = (a.size + 63) / 64 := by omega
    have hk : 8 * ((a.size + 63) / 64 - 1) + 8 ≤ R.size := by omega
    rw [st64_toUSize _ _ _ (by omega)]
    refine ⟨?_, fun j hj p hp => ?_⟩
    · rw [st64Model_size, hL1]
    · by_cases hjk : j = (a.size + 63) / 64 - 1
      · subst hjk
        have hld : ld64 R (8 * ((a.size + 63) / 64 - 1)).toUSize = ld64Model R (8 * ((a.size + 63) / 64 - 1)) := ld64_toUSize R _ (by omega)
        rw [hld, ld64Model_st64Model_self _ _ _ hk, bit_and, bit_lowMask _ _ (by omega) hp, hL3 _ (by omega) hj p hp]
        have : (64 * ((a.size + 63) / 64 - 1) + p < a.size) ↔ p < a.size % 64 := by omega
        simp [this]
      · rw [ld64Model_st64Model_other _ _ _ _ hjk, hL3 j (by omega) hj p hp]
        have : 64 * j + p < a.size := by omega
        simp [this]

theorem filter_range_lt (p : Nat → Bool) (m : Nat) : ∀ N, m ≤ N → (List.range N).filter (fun k => p k && decide (k < m)) = (List.range m).filter p := by
  intro N
  induction N with
  | zero => intro h; have : m = 0 := by omega
            subst this; rfl
  | succ N ih =>
    intro h
    by_cases hN : m ≤ N
    · rw [List.range_succ, List.filter_append, ih hN]
      simp [show ¬ N < m by omega]
    · have hm : m = N + 1 := by omega
      subst hm
      rw [List.range_succ, List.filter_append]
      have e1 : (List.range N).filter (fun k => p k && decide (k < N + 1)) = (List.range N).filter p := by
        apply List.filter_congr; intro k hk; have := List.mem_range.mp hk; simp [show k < N + 1 by omega]
      rw [e1, List.filter_append (List.range N) [N]]
      simp [List.filter_cons]

/-- The cursor over the mask array that `stage1 a` returns stands for exactly `specIndex a`, the structural positions of the byte-at-a-time machine. -/
theorem stage1_stream (a : ByteArray) (h : a.size < 2 ^ 31) :
    VbmSimd.curStream (wordAt (stage1 a)) (wordCount (stage1 a)) (cursorStart (stage1 a)).1 (cursorStart (stage1 a)).2 = specIndex a := by
  obtain ⟨hsz, hbit⟩ := stage1_spec a h
  have hwc : wordCount (stage1 a) = (a.size + 63) / 64 := by unfold wordCount; rw [hsz]; omega
  rw [cursorStart_filter, hwc]
  have e : (List.range (64 * ((a.size + 63) / 64))).filter (fun k => bit (wordAt (stage1 a) (k / 64)) (k % 64)) =
      (List.range (64 * ((a.size + 63) / 64))).filter (fun k => isStruct a k && decide (k < a.size)) := by
    apply List.filter_congr
    intro k hk
    have hk' := List.mem_range.mp hk
    have hl : wordAt (stage1 a) (k / 64) = ld64Model (stage1 a) (8 * (k / 64)) := ld64_toUSize _ _ (by omega)
    rw [hl, hbit (k / 64) (by omega) (k % 64) (by omega), show 64 * (k / 64) + k % 64 = k by omega]
  rw [e, filter_range_lt (isStruct a) a.size _ (by omega)]
  rfl

end LeanJsonProofs
