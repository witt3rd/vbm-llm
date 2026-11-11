import LeanJsonSimd.ParseSimd
import LeanJsonProofs.Stage1
/-! # Proof: the byte-lane tests of the word-parallel leaves (`ndFlags`, `plainBad`) and the first flagged lane

A word holds eight bytes, lane `k` being `u8 w k` (`LeanJsonProofs/Stage1.lean`). The tests of `LeanJsonSimd/ParseSimd.lean` are built from `&&&`, `|||`, `^^^`, `~~~` and `+` with byte-lane constants. Everything but `+` acts on each lane on its own
(`u8_and`, `u8_xor`, `u8_not`, and `u8_or` of `Stage1.lean`); an addition acts on each lane on its own as long as no lane's sum reaches 256 (`u8_add`: the natural number behind a word is its lanes in base 256, and the sum of two numbers
whose lanes add without carry has the sums as its lanes, `ln_add`). Every addition in the leaves has a masked operand (`&&& 0x7f..`) and a constant below `0x80`, so none carries. A lane's value is then a function of the lane's byte alone, and the
statements about it are 256 cases each (`u8_forall`). `first_flag`: when every lane of a flag word is `0` or `0x80`, the lowest set bit (`ctz`) is in the first flagged lane. -/
namespace LeanJsonProofs
open LeanJson VbmSimd VbmSimdProofs

/-! ## Bytes -/

theorem byteAt0_push (b : ByteArray) (v : UInt8) (n : Nat) : byteAt0 (b.push v) n = if n < b.size then byteAt0 b n else if n = b.size then v else 0 := by
  unfold byteAt0
  show (b.data.push v).getD n 0 = _
  have hs : b.size = b.data.size := rfl
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_push, Array.getD_eq_getD_getElem?, hs]
  by_cases h1 : n < b.data.size
  · have h3 : n ≠ b.data.size := by omega
    simp only [h1, h3, ↓reduceIte]
  · by_cases h3 : n = b.data.size
    · subst h3
      simp only [Nat.lt_irrefl, ↓reduceIte]; rfl
    · simp only [h1, h3, ↓reduceIte]
      rw [Array.getElem?_eq_none (by omega)]; rfl

theorem byteAt0_ge (a : ByteArray) (n : Nat) (h : a.size ≤ n) : byteAt0 a n = 0 := by
  unfold byteAt0
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by exact h)]; rfl

theorem byteAt0_lt (a : ByteArray) (n : Nat) (h : n < a.size) : byteAt0 a n = a[n] := by
  unfold byteAt0
  show a.data.getD n 0 = a.data[n]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h]; rfl

theorem ext_byteAt0 (a b : ByteArray) (hs : a.size = b.size) (h : ∀ n, byteAt0 a n = byteAt0 b n) : a = b := by
  apply ByteArray.ext_getElem hs
  intro i hi hi'
  have := h i
  rwa [byteAt0_lt a i hi, byteAt0_lt b i hi'] at this

/-! ## The lanes of a number -/

/-- Byte `k` of the natural `n` (little-endian, base 256). -/
def ln (n k : Nat) : Nat := n / 256 ^ k % 256

theorem ln_div (n k : Nat) : ln (n / 256) k = ln n (k + 1) := by
  unfold ln
  rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]

theorem ln_add : ∀ k A B, (∀ j, j ≤ k → ln A j + ln B j < 256) → ln (A + B) k = ln A k + ln B k := by
  intro k
  induction k with
  | zero =>
    intro A B h
    have := h 0 (Nat.le_refl _)
    simp only [ln, Nat.pow_zero, Nat.div_one] at this ⊢
    omega
  | succ k ih =>
    intro A B h
    have h0 := h 0 (by omega)
    simp only [ln, Nat.pow_zero, Nat.div_one] at h0
    have hd : (A + B) / 256 = A / 256 + B / 256 := by omega
    rw [← ln_div, hd, ← ln_div A, ← ln_div B]
    apply ih
    intro j hj
    rw [ln_div, ln_div]
    exact h (j + 1) (by omega)

theorem ln_mod (n k : Nat) (hk : k < 8) : ln (n % 2 ^ 64) k = ln n k := by
  unfold ln
  have : 2 ^ 64 = 256 ^ 8 := by decide
  rw [this]
  have h8 : 256 ^ 8 = 256 ^ k * 256 ^ (8 - k) := by rw [← Nat.pow_add]; congr 1; omega
  rw [h8, Nat.mod_mul_right_div_self]
  have : 256 ^ (8 - k) = 256 * 256 ^ (7 - k) := by rw [← Nat.pow_succ']; congr 1; omega
  rw [this, Nat.mod_mul_right_mod]

theorem u8_toNat (w : UInt64) (j : Nat) : (u8 w j).toNat = ln w.toNat j := by
  unfold u8 byte ln
  simp only [UInt8.toNat_ofBitVec, BitVec.extractLsb'_toNat, UInt64.toNat_toBitVec]
  rw [Nat.shiftRight_eq_div_pow, show 2 ^ (8 * j) = 256 ^ j by rw [Nat.pow_mul]]

theorem u8_and (w c : UInt64) (j : Nat) : u8 (w &&& c) j = u8 w j &&& u8 c j := by
  simp [u8, byte, BitVec.extractLsb'_and]

theorem u8_xor (w c : UInt64) (j : Nat) : u8 (w ^^^ c) j = u8 w j ^^^ u8 c j := by
  simp [u8, byte, BitVec.extractLsb'_xor]

theorem u8_not (w : UInt64) (j : Nat) (hj : j < 8) : u8 (~~~w) j = ~~~ u8 w j := by
  unfold u8 byte
  apply UInt8.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi]
  intro _; omega

theorem u8_add (a b : UInt64) (h : ∀ j, j < 8 → (u8 a j).toNat + (u8 b j).toNat < 256) (k : Nat) (hk : k < 8) : u8 (a + b) k = u8 a k + u8 b k := by
  apply UInt8.toNat_inj.mp
  rw [UInt8.toNat_add, u8_toNat, u8_toNat, u8_toNat, UInt64.toNat_add, ln_mod _ _ hk, ln_add k _ _ (fun j hj => by have := h j (by omega); simpa only [u8_toNat] using this)]
  have h1 := h k hk
  simp only [u8_toNat] at h1
  omega

/-! ## The constants -/

theorem u8_cHi (j : Nat) (hj : j < 8) : u8 cHi j = 0x80 := by
  have : ∀ j : Fin 8, u8 cHi j = 0x80 := by decide
  exact this ⟨j, hj⟩
theorem u8_cLo7 (j : Nat) (hj : j < 8) : u8 cLo7 j = 0x7f := by
  have : ∀ j : Fin 8, u8 cLo7 j = 0x7f := by decide
  exact this ⟨j, hj⟩
theorem u8_c30 (j : Nat) (hj : j < 8) : u8 0x3030303030303030 j = 0x30 := by
  have : ∀ j : Fin 8, u8 0x3030303030303030 j = 0x30 := by decide
  exact this ⟨j, hj⟩
theorem u8_c76 (j : Nat) (hj : j < 8) : u8 0x7676767676767676 j = 0x76 := by
  have : ∀ j : Fin 8, u8 0x7676767676767676 j = 0x76 := by decide
  exact this ⟨j, hj⟩
theorem u8_c60 (j : Nat) (hj : j < 8) : u8 0x6060606060606060 j = 0x60 := by
  have : ∀ j : Fin 8, u8 0x6060606060606060 j = 0x60 := by decide
  exact this ⟨j, hj⟩

theorem u8_bit (w : UInt64) (j i : Nat) (hi : i < 8) : (u8 w j).toBitVec.getLsbD i = bit w (8 * j + i) := by
  unfold u8 byte bit
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]

theorem getLsbD_0x80 (i : Nat) (hi : i < 8) : (0x80 : UInt8).toBitVec.getLsbD i = decide (i = 7) := by
  have : ∀ i : Fin 8, (0x80 : UInt8).toBitVec.getLsbD i = decide (i.val = 7) := by decide
  exact this ⟨i, hi⟩

theorem u8_eqLanes (c w : UInt64) (j : Nat) (hj : j < 8) : u8 (eqLanes c w) j = if (u8 w j == u8 c j) = true then 0x80 else 0 := by
  apply UInt8.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [u8_bit _ _ _ hi]
  by_cases h7 : i = 7
  · subst h7
    rw [eqLanes_spec c w j hj, laneEq_u8]
    by_cases hc : (u8 w j == u8 c j) = true
    · simp only [hc]; decide
    · simp only [hc]; simp
  · have hl := eqLanes_low c w (8 * j + i) (by omega) (by omega)
    by_cases hc : (u8 w j == u8 c j) = true
    · simp only [hc, ↓reduceIte, getLsbD_0x80 i hi, hl]; simp [h7]
    · simp only [hc, hl]; simp


/-! ## The flags -/

/-- An ASCII digit. -/
def isDig (x : UInt8) : Bool := decide (0x30 ≤ x.toNat ∧ x.toNat ≤ 0x39)

/-- The byte function the lane of `ndFlags` computes. -/
def ndLane (x : UInt8) : UInt8 := ((((x ^^^ 0x30) &&& 0x7f) + 0x76) ||| (x ^^^ 0x30)) &&& 0x80

theorem ndLane_spec : ∀ x : UInt8, ndLane x = if isDig x = true then 0 else 0x80 :=
  u8_forall _ (by decide)

theorem ndFlags_lane (w : UInt64) (k : Nat) (hk : k < 8) : u8 (ndFlags w) k = if isDig (u8 w k) = true then 0 else 0x80 := by
  have hadd : ∀ j, j < 8 → (u8 ((w ^^^ 0x3030303030303030) &&& cLo7) j).toNat + (u8 0x7676767676767676 j).toNat < 256 := by
    intro j hj
    rw [u8_and, u8_cLo7 j hj, u8_c76 j hj]
    generalize u8 (w ^^^ 0x3030303030303030) j = x
    revert x
    exact u8_forall _ (by decide)
  unfold ndFlags
  simp only []
  rw [u8_and, u8_or, u8_add _ _ hadd k hk, u8_and, u8_xor, u8_cLo7 k hk, u8_c76 k hk, u8_c30 k hk, u8_cHi k hk]
  exact ndLane_spec _

/-- The byte function the lane of `plainBad` computes. -/
def plainLane (x : UInt8) : UInt8 := ((~~~(((x &&& 0x7f) + 0x60)) ||| x) &&& 0x80) ||| (if x == 0x5c then 0x80 else 0) ||| (if x == 0x22 then 0x80 else 0)

theorem plainLane_spec : ∀ x : UInt8, plainLane x = if (plainAscii x && x != 0x22) = true then 0 else 0x80 :=
  u8_forall _ (by decide)

theorem plainBad_lane (w : UInt64) (k : Nat) (hk : k < 8) : u8 (plainBad w) k = if (plainAscii (u8 w k) && u8 w k != 0x22) = true then 0 else 0x80 := by
  have hadd : ∀ j, j < 8 → (u8 (w &&& cLo7) j).toNat + (u8 0x6060606060606060 j).toNat < 256 := by
    intro j hj
    rw [u8_and, u8_cLo7 j hj, u8_c60 j hj]
    generalize u8 w j = x
    revert x
    exact u8_forall _ (by decide)
  unfold plainBad
  rw [u8_or, u8_or, u8_and, u8_or, u8_not _ _ hk, u8_add _ _ hadd k hk, u8_and, u8_cHi k hk, u8_cLo7 k hk, u8_c60 k hk,
    u8_eqLanes _ _ _ hk, u8_eqLanes _ _ _ hk, u8_cBslash ⟨k, hk⟩, u8_cQuote ⟨k, hk⟩]
  have := plainLane_spec (u8 w k)
  unfold plainLane at this
  exact this


/-! ## The first flagged lane -/

/-- When every lane of a nonzero flag word is `0` or `0x80`, `ctz` lands in the first nonzero lane (at its top bit): the lanes before it are `0`, and it is `0x80`. -/
theorem first_flag (f : UInt64) (hf : f ≠ 0) (hv : ∀ k, k < 8 → u8 f k = 0 ∨ u8 f k = 0x80) :
    (ctz f).toNat / 8 < 8 ∧ u8 f ((ctz f).toNat / 8) = 0x80 ∧ ∀ m, m < (ctz f).toNat / 8 → u8 f m = 0 := by
  obtain ⟨hlt, hb, hlow⟩ := ctzModel_spec f hf
  have e : ctz f = ctzModel f := rfl
  rw [e]
  have hk : (ctzModel f).toNat / 8 < 8 := by omega
  refine ⟨hk, ?_, fun m hm => ?_⟩
  · have hbit := hb
    rw [show (ctzModel f).toNat = 8 * ((ctzModel f).toNat / 8) + (ctzModel f).toNat % 8 by omega] at hbit
    rw [← u8_bit f _ _ (by omega)] at hbit
    rcases hv _ hk with h | h
    · rw [h] at hbit; simp at hbit
    · exact h
  · have hm8 : m < 8 := by omega
    have hz := hlow (8 * m + 7) (by omega)
    rw [← u8_bit f m 7 (by omega)] at hz
    rcases hv m hm8 with h | h
    · exact h
    · rw [h] at hz; exact absurd hz (by decide)


/-! ## Digits -/

theorem digitVal_isSome (x : UInt8) : (digitVal x).isSome = isDig x := by
  unfold digitVal isDig
  by_cases h : 0x30 ≤ x.toNat ∧ x.toNat ≤ 0x39 <;> simp [h]

theorem scanDigits_unfold (a : ByteArray) (i : Nat) : scanDigits a i = if h : i < a.size then (if isDig a[i] = true then scanDigits a (i + 1) else i) else i := by
  rw [scanDigits]
  simp only [digitVal_isSome]

/-- `k` digits are skipped. -/
theorem scanDigits_skip (a : ByteArray) : ∀ k i, i + k ≤ a.size → (∀ m, m < k → ∃ h : i + m < a.size, isDig a[i + m] = true) → scanDigits a i = scanDigits a (i + k) := by
  intro k
  induction k with
  | zero => intro i _ _; rfl
  | succ k ih =>
    intro i hk hd
    obtain ⟨h0, hd0⟩ := hd 0 (by omega)
    rw [scanDigits_unfold]
    simp only [Nat.add_zero] at h0 hd0
    simp only [h0, hd0, ↓reduceDIte, ↓reduceIte]
    rw [ih (i + 1) (by omega) (fun m hm => by
      obtain ⟨h1, h2⟩ := hd (m + 1) (by omega)
      exact ⟨by omega, by simpa only [show i + 1 + m = i + (m + 1) by omega] using h2⟩)]
    rw [show i + 1 + k = i + (k + 1) by omega]

/-- The first non-digit of a run. -/
theorem scanDigits_stop (a : ByteArray) (k i : Nat) (hk : i + k < a.size) (hd : ∀ m, m < k → ∃ h : i + m < a.size, isDig a[i + m] = true)
    (hn : ∀ h : i + k < a.size, isDig a[i + k] = false) : scanDigits a i = i + k := by
  rw [scanDigits_skip a k i (by omega) hd, scanDigits_unfold]
  simp only [hk, ↓reduceDIte, hn hk, Bool.false_eq_true, ↓reduceIte]

theorem u8_zero (k : Nat) : u8 0 k = 0 := by
  simp [u8, byte]

theorem u8_ld64 (a : ByteArray) (i : Nat) (hi : i + 8 ≤ a.size) (hs : a.size < 2 ^ 31) (k : Nat) (hk : k < 8) :
    u8 (ld64 a i.toUSize) k = a[i + k]'(by omega) := by
  rw [ld64_toUSize a i (by omega), u8_ld64Model a i k hk, byteAt0_lt a _ (by omega)]

theorem scanDigitsW_eq (a : ByteArray) (hs : a.size < 2 ^ 31) : ∀ d i, a.size - i = d → scanDigitsW a i = scanDigits a i := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
    intro i hd
    rw [scanDigitsW]
    by_cases h8 : i + 8 ≤ a.size
    · simp only [h8, ↓reduceDIte]
      have hl := ndFlags_lane (ld64 a i.toUSize)
      have hv : ∀ k, k < 8 → u8 (ndFlags (ld64 a i.toUSize)) k = 0 ∨ u8 (ndFlags (ld64 a i.toUSize)) k = 0x80 := by
        intro k hk
        rw [hl k hk]
        by_cases hdg : isDig (u8 (ld64 a i.toUSize) k) = true <;> simp [hdg]
      by_cases hz : (ndFlags (ld64 a i.toUSize) == 0) = true
      · simp only [hz, ↓reduceIte]
        have hf0 : ndFlags (ld64 a i.toUSize) = 0 := by simpa using hz
        have hall : ∀ m, m < 8 → ∃ h : i + m < a.size, isDig a[i + m] = true := by
          intro m hm
          have := hl m hm
          rw [hf0, u8_zero, u8_ld64 a i h8 hs m hm] at this
          refine ⟨by omega, ?_⟩
          by_cases hdg : isDig a[i + m] = true
          · exact hdg
          · simp [hdg] at this
        rw [ih (a.size - (i + 8)) (by omega) (i + 8) rfl, scanDigits_skip a 8 i h8 hall]
      · simp only [hz, Bool.false_eq_true, ↓reduceIte]
        have hf : ndFlags (ld64 a i.toUSize) ≠ 0 := by simpa using hz
        obtain ⟨hk8, hk1, hk0⟩ := first_flag _ hf hv
        have hdig : ∀ m, m < (ctz (ndFlags (ld64 a i.toUSize))).toNat / 8 → ∃ h : i + m < a.size, isDig a[i + m] = true := by
          intro m hm
          have := hl m (by omega)
          rw [hk0 m hm, u8_ld64 a i h8 hs m (by omega)] at this
          refine ⟨by omega, ?_⟩
          by_cases hdg : isDig a[i + m] = true
          · exact hdg
          · simp [hdg] at this
        rw [scanDigits_stop a _ i (by omega) hdig]
        intro h
        have := hl _ hk8
        rw [hk1, u8_ld64 a i h8 hs _ hk8] at this
        by_cases hdg : isDig a[i + (ctz (ndFlags (ld64 a i.toUSize))).toNat / 8] = true
        · simp [hdg] at this
        · simpa using hdg
    · simp only [h8, ↓reduceDIte]


/-! ## Plain string bytes -/

/-- What `plainRun` says: every byte of `a[p, e)` is in the input, plain, and not a quote. -/
theorem plainRun_iff (a : ByteArray) : ∀ d p e, e - p = d → (plainRun a p e = true ↔ ∀ q, p ≤ q → q < e → ∃ h : q < a.size, (plainAscii a[q] && a[q] != 0x22) = true) := by
  intro d
  induction d with
  | zero =>
    intro p e hd
    rw [plainRun]
    simp only [show ¬ p < e by omega, ↓reduceDIte, true_iff]
    intro q h1 h2; omega
  | succ d ih =>
    intro p e hd
    have hlt : p < e := by omega
    rw [plainRun]
    simp only [hlt, ↓reduceDIte]
    by_cases hps : p < a.size
    · simp only [hps, ↓reduceDIte]
      by_cases hc : (plainAscii a[p] && a[p] != 0x22) = true
      · simp only [hc, ↓reduceIte]
        rw [ih (p + 1) e (by omega)]
        constructor
        · intro hh q hq1 hq2
          by_cases hqp : q = p
          · subst hqp; exact ⟨hps, hc⟩
          · exact hh q (by omega) hq2
        · intro hh q hq1 hq2
          exact hh q (by omega) hq2
      · simp only [hc, Bool.false_eq_true, ↓reduceIte, false_iff]
        intro hh
        obtain ⟨_, h2⟩ := hh p (Nat.le_refl _) hlt
        exact hc h2
    · simp only [hps, ↓reduceDIte, Bool.false_eq_true, false_iff]
      intro hh
      obtain ⟨h1, _⟩ := hh p (Nat.le_refl _) hlt
      exact hps h1

theorem plainOff_acc (a : ByteArray) : ∀ d p acc, a.size - p = d → plainOff a p acc = acc + plainOff a p 0 := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
    intro p acc hd
    conv => lhs; rw [plainOff]
    conv => rhs; rw [plainOff]
    by_cases h8 : p + 8 ≤ a.size
    · simp only [h8, ↓reduceDIte]
      by_cases hz : (plainBad (ld64 a p.toUSize) == 0) = true
      · simp only [hz, ↓reduceIte]
        rw [ih (a.size - (p + 8)) (by omega) (p + 8) (acc + 8) rfl, ih (a.size - (p + 8)) (by omega) (p + 8) (0 + 8) rfl]
        omega
      · simp only [hz, Bool.false_eq_true, ↓reduceIte]
        omega
    · simp only [h8, ↓reduceDIte]
      omega

theorem plainOff_run (a : ByteArray) (hs : a.size < 2 ^ 31) : ∀ d p, a.size - p = d → plainRun a p (p + plainOff a p 0) = true := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
    intro p hd
    rw [plainOff]
    by_cases h8 : p + 8 ≤ a.size
    · simp only [h8, ↓reduceDIte, Nat.zero_add]
      have hl := plainBad_lane (ld64 a p.toUSize)
      have hv : ∀ k, k < 8 → u8 (plainBad (ld64 a p.toUSize)) k = 0 ∨ u8 (plainBad (ld64 a p.toUSize)) k = 0x80 := by
        intro k hk
        rw [hl k hk]
        by_cases hdg : (plainAscii (u8 (ld64 a p.toUSize) k) && u8 (ld64 a p.toUSize) k != 0x22) = true <;> simp [hdg]
      by_cases hz : (plainBad (ld64 a p.toUSize) == 0) = true
      · simp only [hz, ↓reduceIte]
        have hf0 : plainBad (ld64 a p.toUSize) = 0 := by simpa using hz
        have hall : ∀ m, m < 8 → ∃ h : p + m < a.size, (plainAscii a[p + m] && a[p + m] != 0x22) = true := by
          intro m hm
          have := hl m hm
          rw [hf0, u8_zero, u8_ld64 a p h8 hs m hm] at this
          refine ⟨by omega, ?_⟩
          by_cases hdg : (plainAscii a[p + m] && a[p + m] != 0x22) = true
          · exact hdg
          · simp [hdg] at this
        have hrest := ih (a.size - (p + 8)) (by omega) (p + 8) rfl
        rw [plainOff_acc a _ (p + 8) 8 rfl, ← Nat.add_assoc] at *
        rw [plainRun_iff a _ _ _ rfl] at hrest ⊢
        intro q hq1 hq2
        by_cases hq : q < p + 8
        · obtain ⟨_, h2⟩ := hall (q - p) (by omega)
          exact ⟨by omega, by simpa only [show p + (q - p) = q by omega] using h2⟩
        · exact hrest q (by omega) (by omega)
      · simp only [hz, Bool.false_eq_true, ↓reduceIte]
        have hf : plainBad (ld64 a p.toUSize) ≠ 0 := by simpa using hz
        obtain ⟨hk8, hk1, hk0⟩ := first_flag _ hf hv
        rw [plainRun_iff a _ _ _ rfl]
        intro q hq1 hq2
        have hm : q - p < (ctz (plainBad (ld64 a p.toUSize))).toNat / 8 := by omega
        have := hl (q - p) (by omega)
        rw [hk0 _ hm, u8_ld64 a p h8 hs _ (by omega)] at this
        obtain ⟨_, h2⟩ : ∃ h : p + (q - p) < a.size, (plainAscii a[p + (q - p)] && a[p + (q - p)] != 0x22) = true := by
          refine ⟨by omega, ?_⟩
          by_cases hdg : (plainAscii a[p + (q - p)] && a[p + (q - p)] != 0x22) = true
          · exact hdg
          · simp [hdg] at this
        exact ⟨by omega, by simpa only [show p + (q - p) = q by omega] using h2⟩
    · simp only [h8, ↓reduceDIte, Nat.add_zero]
      rw [plainRun]
      simp


/-! ## The lexeme without `E` or `+` -/

theorem u8_c45 (j : Nat) (hj : j < 8) : u8 0x4545454545454545 j = 0x45 := by
  have : ∀ j : Fin 8, u8 0x4545454545454545 j = 0x45 := by decide
  exact this ⟨j, hj⟩
theorem u8_c2b (j : Nat) (hj : j < 8) : u8 0x2b2b2b2b2b2b2b2b j = 0x2b := by
  have : ∀ j : Fin 8, u8 0x2b2b2b2b2b2b2b2b j = 0x2b := by decide
  exact this ⟨j, hj⟩

theorem lexBad_lane (w : UInt64) (k : Nat) (hk : k < 8) : u8 (lexBad w) k = if (u8 w k == 0x45 || u8 w k == 0x2b) = true then 0x80 else 0 := by
  unfold lexBad
  rw [u8_or, u8_eqLanes _ _ _ hk, u8_eqLanes _ _ _ hk, u8_c45 k hk, u8_c2b k hk]
  have : ∀ x : UInt8, ((if (x == 0x45) = true then (0x80 : UInt8) else 0) ||| (if (x == 0x2b) = true then 0x80 else 0)) = if (x == 0x45 || x == 0x2b) = true then 0x80 else 0 :=
    u8_forall _ (by decide)
  exact this _

theorem eq_zero_of_u8 (x : UInt64) (h : ∀ k, k < 8 → u8 x k = 0) : x = 0 := by
  apply ext_bits
  intro i hi
  have := u8_bit x (i / 8) (i % 8) (by omega)
  rw [show 8 * (i / 8) + i % 8 = i by omega, h (i / 8) (by omega)] at this
  rw [← this]
  simp [bit]

theorem u8_lowMask (n : Nat) (hn : n < 8) (k : Nat) (hk : k < 8) : u8 (((1 : UInt64) <<< (8 * n.toUInt64)) - 1) k = if k < n then 0xff else 0 := by
  have : ∀ n : Fin 8, ∀ k : Fin 8, u8 (((1 : UInt64) <<< (8 * n.val.toUInt64)) - 1) k = if k.val < n.val then 0xff else 0 := by decide
  exact this ⟨n, hn⟩ ⟨k, hk⟩

theorem lexRun_iff (a : ByteArray) : ∀ d p e, e - p = d → (lexRun a p e = true ↔ ∀ q, p ≤ q → q < e → ∃ h : q < a.size, (a[q] != 0x45 && a[q] != 0x2B) = true) := by
  intro d
  induction d with
  | zero =>
    intro p e hd
    rw [lexRun]
    simp only [show ¬ p < e by omega, ↓reduceDIte, true_iff]
    intro q h1 h2; omega
  | succ d ih =>
    intro p e hd
    have hlt : p < e := by omega
    rw [lexRun]
    simp only [hlt, ↓reduceDIte]
    by_cases hps : p < a.size
    · simp only [hps, ↓reduceDIte]
      by_cases hc : (a[p] != 0x45 && a[p] != 0x2B) = true
      · simp only [hc, ↓reduceIte]
        rw [ih (p + 1) e (by omega)]
        constructor
        · intro hh q hq1 hq2
          by_cases hqp : q = p
          · subst hqp; exact ⟨hps, hc⟩
          · exact hh q (by omega) hq2
        · intro hh q hq1 hq2
          exact hh q (by omega) hq2
      · simp only [hc, Bool.false_eq_true, ↓reduceIte, false_iff]
        intro hh
        obtain ⟨_, h2⟩ := hh p (Nat.le_refl _) hlt
        exact hc h2
    · simp only [hps, ↓reduceDIte, Bool.false_eq_true, false_iff]
      intro hh
      obtain ⟨h1, _⟩ := hh p (Nat.le_refl _) hlt
      exact hps h1

theorem lexOk_iff (a : ByteArray) (hs : a.size < 2 ^ 31) (e : Nat) (he : e ≤ a.size) : ∀ d p, e - p = d → (lexOk a p e = true ↔ lexRun a p e = true) := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
    intro p hd
    rw [lexOk]
    by_cases h8 : p + 8 ≤ e
    · simp only [h8, ↓reduceDIte]
      have hl := lexBad_lane (ld64 a p.toUSize)
      have hbyte : ∀ k (hk : k < 8), u8 (ld64 a p.toUSize) k = a[p + k]'(by omega) := fun k hk => u8_ld64 a p (by omega) hs k hk
      by_cases hz : (lexBad (ld64 a p.toUSize) == 0) = true
      · simp only [hz, ↓reduceIte]
        have hf0 : lexBad (ld64 a p.toUSize) = 0 := by simpa using hz
        rw [ih (e - (p + 8)) (by omega) (p + 8) rfl, lexRun_iff a _ _ _ rfl, lexRun_iff a _ _ _ rfl]
        constructor
        · intro hh q hq1 hq2
          by_cases hq : q < p + 8
          · have := hl (q - p) (by omega)
            rw [hf0, u8_zero, hbyte _ (by omega)] at this
            refine ⟨by omega, ?_⟩
            have h2 : (a[p + (q - p)]'(by omega) == 0x45 || a[p + (q - p)]'(by omega) == 0x2b) = false := by
              by_cases hh2 : (a[p + (q - p)]'(by omega) == 0x45 || a[p + (q - p)]'(by omega) == 0x2b) = true
              · simp [hh2] at this
              · simpa using hh2
            simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h2
            simp only [show p + (q - p) = q by omega] at h2
            simp [h2.1, h2.2]
          · exact hh q (by omega) hq2
        · intro hh q hq1 hq2
          exact hh q (by omega) hq2
      · simp only [hz, Bool.false_eq_true, ↓reduceIte, false_iff]
        have hnz : lexBad (ld64 a p.toUSize) ≠ 0 := by simpa using hz
        rw [lexRun_iff a _ _ _ rfl]
        intro hh
        apply hnz
        apply eq_zero_of_u8
        intro k hk
        rw [hl k hk, hbyte k hk]
        obtain ⟨h1, h2⟩ := hh (p + k) (by omega) (by omega)
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h2
        have h3 : (a[p + k]'(by omega) == 0x45 || a[p + k]'(by omega) == 0x2b) = false := by
          simp [h2.1, h2.2]
        simp [h3]
    · simp only [h8, ↓reduceDIte]
      by_cases hpe : p < e
      · simp only [hpe, ↓reduceIte]
        rw [lexRun_iff a _ _ _ rfl]
        have hl := lexBad_lane (ld64 a p.toUSize)
        have hbyte : ∀ k (hk : k < e - p), u8 (ld64 a p.toUSize) k = a[p + k]'(by omega) := fun k hk => by
          rw [ld64_toUSize a p (by omega), u8_ld64Model a p k (by omega), byteAt0_lt a _ (by omega)]
        constructor
        · intro hz q hq1 hq2
          have hz' : lexBad (ld64 a p.toUSize) &&& (((1 : UInt64) <<< (8 * (e - p).toUInt64)) - 1) = 0 := by simpa using hz
          have := congrArg (fun x => u8 x (q - p)) hz'
          simp only [u8_and, u8_zero, u8_lowMask (e - p) (by omega) (q - p) (by omega), hl (q - p) (by omega), hbyte (q - p) (by omega)] at this
          refine ⟨by omega, ?_⟩
          simp only [show p + (q - p) = q by omega, show q - p < e - p by omega, ↓reduceIte] at this
          have h3 : (a[q]'(by omega) == 0x45 || a[q]'(by omega) == 0x2b) = false := by
            by_cases hh3 : (a[q]'(by omega) == 0x45 || a[q]'(by omega) == 0x2b) = true
            · simp only [hh3, ↓reduceIte] at this
              exact absurd this (by decide)
            · simpa using hh3
          simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h3
          simp [h3.1, h3.2]
        · intro hh
          have : lexBad (ld64 a p.toUSize) &&& (((1 : UInt64) <<< (8 * (e - p).toUInt64)) - 1) = 0 := by
            apply eq_zero_of_u8
            intro k hk
            rw [u8_and, u8_lowMask (e - p) (by omega) k hk]
            by_cases hke : k < e - p
            · simp only [hke, ↓reduceIte, hl k hk, hbyte k hke]
              obtain ⟨h1, h2⟩ := hh (p + k) (by omega) (by omega)
              simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h2
              have h3 : (a[p + k]'(by omega) == 0x45 || a[p + k]'(by omega) == 0x2b) = false := by simp [h2.1, h2.2]
              simp [h3]
            · simp [hke]
          simp [this]
      · simp only [hpe, ↓reduceIte]
        rw [lexRun]
        simp [hpe]

theorem lexOk_eq (a : ByteArray) (hs : a.size < 2 ^ 31) (e : Nat) (he : e ≤ a.size) (p : Nat) : lexOk a p e = lexRun a p e := by
  rw [Bool.eq_iff_iff]
  exact lexOk_iff a hs e he _ p rfl

end LeanJsonProofs
