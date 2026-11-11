import LeanJsonProofs.ParseW
import LeanJsonProofs.Stage1Avx
/-! # Proof: `runU` (positions, counters and fuel as `USize`) answers only what `runW` answers (`runU_sound`), and the parser built on it equals the scalar parser (`parseTapeU_eq`)

`LeanJsonSimd/ParseSimd.lean`, `runU`. Every leaf of `runU` is shown equal, through `Nat.toNat`, to the leaf of `runW` it replaces (`byteIsU_eq`, `delimAtU_eq`, `skipU_eq`, `plainOffU_eq`, `scanDigitsU_eq`, `scanNumU_eq`, `lexOkU_eq`, `strU_eq`,
`putNodeU_eq`); the induction is the one of `runW_sound`, over the same branches, with the bounds that keep every `USize` operation from wrapping (below `simdLimit`, on 32 bits as on 64) carried as hypotheses. -/
namespace LeanJsonProofs
open LeanJson VbmSimd VbmSimdProofs

theorem usize_ge32 : 4294967296 ≤ USize.size := by rcases USize.size_eq with h | h <;> omega

theorem usize_eq (a : ByteArray) (hs : a.size < 4294967296) : a.usize.toNat = a.size := by
  have h2 : a.usize.toNat = a.size % 2 ^ System.Platform.numBits := rfl
  rw [h2]
  apply Nat.mod_eq_of_lt
  have : USize.size = 2 ^ System.Platform.numBits := rfl
  have := usize_ge32
  omega

theorem lt_usize_iff (a : ByteArray) (hs : a.size < 4294967296) (i : USize) : i < a.usize ↔ i.toNat < a.size := by
  rw [USize.lt_iff_toNat_lt, usize_eq a hs]

theorem le_usize_iff (a : ByteArray) (hs : a.size < 4294967296) (i : USize) : i ≤ a.usize ↔ i.toNat ≤ a.size := by
  rw [USize.le_iff_toNat_le, usize_eq a hs]

theorem byteIsU_eq (a : ByteArray) (hs : a.size < 4294967296) (i : USize) (c : UInt8) : byteIsU a i c = byteIs a i.toNat c := by
  unfold byteIsU byteIs
  by_cases h : i < a.usize
  · have h2 := (lt_usize_iff a hs i).1 h
    simp only [h, h2, ↓reduceDIte]; rfl
  · have h2 : ¬ i.toNat < a.size := fun h' => h ((lt_usize_iff a hs i).2 h')
    simp only [h, h2, ↓reduceDIte]

theorem delimAtU_eq (a : ByteArray) (hs : a.size < 4294967296) (j : USize) : delimAtU a j = delimAt a j.toNat := by
  unfold delimAtU delimAt byteAt
  by_cases h : j < a.usize
  · have h2 := (lt_usize_iff a hs j).1 h
    simp only [h, h2, ↓reduceDIte]; rfl
  · have h2 : ¬ j.toNat < a.size := fun h' => h ((lt_usize_iff a hs j).2 h')
    simp only [h, h2, ↓reduceDIte]


/-! ## The skip -/

theorem usize_lit' (n : Nat) (h : n < 4294967296) : (OfNat.ofNat n : USize).toNat = n := usize_lit n h

theorem usize_shr6 (j : USize) (hj : j.toNat < 4294967296) : j >>> 6 = (j.toNat >>> 6).toUSize := by
  apply USize.toNat_inj.mp
  have h2 : System.Platform.numBits = 32 ∨ System.Platform.numBits = 64 := System.Platform.numBits_eq
  have h6 : (6 : USize).toNat = 6 := usize_lit 6 (by decide)
  have h4 : (j.toNat >>> 6) < 4294967296 := by
    rw [Nat.shiftRight_eq_div_pow]
    omega
  rw [USize.toNat_shiftRight, h6, usize_toNat_small _ h4]
  rcases h2 with h | h <;> rw [h]

theorem usize_and63 (j : USize) : (j &&& 63).toUInt64 = (j.toNat &&& 63).toUInt64 := by
  apply UInt64.toNat_inj.mp
  have h63 : (63 : USize).toNat = 63 := usize_lit 63 (by decide)
  rw [USize.toNat_toUInt64, USize.toNat_and, h63]
  have : j.toNat &&& 63 = j.toNat % 64 := by
    have := Nat.and_two_pow_sub_one_eq_mod j.toNat 6
    simpa using this
  rw [this]
  show _ = (UInt64.ofNat (j.toNat % 64)).toNat
  rw [UInt64.toNat_ofNat']
  have h64 : j.toNat % 64 < 18446744073709551616 := by omega
  exact (Nat.mod_eq_of_lt h64).symm

theorem ctz_lt (w : UInt64) (h : w ≠ 0) : (ctz w).toNat < 64 := (ctzModel_spec w h).1

theorem ctz_toUSize (w : UInt64) (h : w ≠ 0) : (ctz w).toUSize.toNat = (ctz w).toNat := by
  rw [UInt64.toNat_toUSize]
  have := ctz_lt w h
  have h2 : System.Platform.numBits = 32 ∨ System.Platform.numBits = 64 := System.Platform.numBits_eq
  apply Nat.mod_eq_of_lt
  rcases h2 with h2 | h2 <;> rw [h2] <;> omega

theorem skipI_le (m : ByteArray) (size j : Nat) : skipI m size j ≤ size := by
  unfold skipI
  dsimp only
  split <;> omega

theorem skipU_eq (m a : ByteArray) (hs : a.size < 2 ^ 31) (j : USize) (hj : j.toNat < 1073741824) :
    (skipU m a.usize j).toNat = skipI m a.size j.toNat := by
  rw [← skipF_eq]
  unfold skipU skipF
  have hu := usize_eq a (by omega)
  simp only [hj, ↓reduceIte]
  rw [usize_shr6 j (by omega), usize_and63]
  have hw : ld64 m ((j.toNat >>> 6).toUSize <<< 3) = wordAt m (j.toNat / 64) := by
    rw [skipF_shl3 j.toNat hj]; rfl
  rw [hw, skipF_mask, skipF_shl6 j.toNat hj]
  by_cases hz : (wordAt m (j.toNat / 64) &&& ((~~~(0 : UInt64)) <<< (j.toNat % 64).toUInt64)) != 0
  · simp only [hz, ↓reduceIte]
    have hne : (wordAt m (j.toNat / 64) &&& ((~~~(0 : UInt64)) <<< (j.toNat % 64).toUInt64)) ≠ 0 := by simpa using hz
    have hc := ctz_lt _ hne
    have hct := ctz_toUSize _ hne
    have hs6 : ((j.toNat >>> 6).toUSize <<< 6).toNat = 64 * (j.toNat / 64) := skipF_shl6 j.toNat hj
    have hadd : (((j.toNat >>> 6).toUSize <<< 6) + (ctz (wordAt m (j.toNat / 64) &&& ((~~~(0 : UInt64)) <<< (j.toNat % 64).toUInt64))).toUSize).toNat =
        64 * (j.toNat / 64) + (ctz (wordAt m (j.toNat / 64) &&& ((~~~(0 : UInt64)) <<< (j.toNat % 64).toUInt64))).toNat := by
      rw [usize_add_lt _ _ (by rw [hs6, hct]; have := usize_ge32; omega), hs6, hct]
    by_cases hr : 64 * (j.toNat / 64) + (ctz (wordAt m (j.toNat / 64) &&& ((~~~(0 : UInt64)) <<< (j.toNat % 64).toUInt64))).toNat < a.size
    · have hr' : ((j.toNat >>> 6).toUSize <<< 6) + (ctz (wordAt m (j.toNat / 64) &&& ((~~~(0 : UInt64)) <<< (j.toNat % 64).toUInt64))).toUSize < a.usize := by
        rw [USize.lt_iff_toNat_lt, hadd, hu]; exact hr
      simp only [hr', hr, ↓reduceIte, hadd]
    · have hr' : ¬ (((j.toNat >>> 6).toUSize <<< 6) + (ctz (wordAt m (j.toNat / 64) &&& ((~~~(0 : UInt64)) <<< (j.toNat % 64).toUInt64))).toUSize < a.usize) := by
        rw [USize.lt_iff_toNat_lt, hadd, hu]; exact hr
      simp only [hr', hr, ↓reduceIte, hu]
  · simp only [hz, Bool.false_eq_true, ↓reduceIte]
    rw [hu, usize_toNat_small _ (by have := skipI_le m a.size j.toNat; omega)]

/-! ## The word-parallel leaves -/

theorem usize_ofNat_toNat' (p : USize) : p.toNat.toUSize = p := USize.ofNat_toNat

theorem guard_iff (a : ByteArray) (hs : a.size < 2 ^ 31) (p : USize) : (p ≤ a.usize ∧ 8 ≤ a.usize - p) ↔ p.toNat + 8 ≤ a.size := by
  have hu := usize_eq a (by omega)
  have h8 := usize_lit 8 (by decide)
  constructor
  · rintro ⟨h1, h2⟩
    have h3 := USize.le_iff_toNat_le.1 h1
    have h4 := USize.le_iff_toNat_le.1 h2
    have h6 := USize.toNat_sub_of_le _ _ h1
    rw [h8, h6] at h4
    omega
  · intro h
    have h1 : p ≤ a.usize := by rw [USize.le_iff_toNat_le, hu]; omega
    refine ⟨h1, ?_⟩
    rw [USize.le_iff_toNat_le, USize.toNat_sub_of_le _ _ h1, h8, hu]
    omega

theorem plainOffU_eq (a : ByteArray) (hs : a.size < 2 ^ 31) : ∀ d (p acc : USize), a.size - p.toNat = d → acc.toNat + (a.size - p.toNat) < 4294967296 →
    (plainOffU a p acc).toNat = plainOff a p.toNat acc.toNat := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
    intro p acc hd hacc
    have h8 := usize_lit 8 (by decide)
    rw [plainOffU, plainOff]
    by_cases hg : p.toNat + 8 ≤ a.size
    · have hgu := (guard_iff a hs p).2 hg
      have hp8 : (p + 8).toNat = p.toNat + 8 := usize_add_lit p 8 (by decide) (by have := usize_ge32; omega)
      have ha8 : (acc + 8).toNat = acc.toNat + 8 := usize_add_lit acc 8 (by decide) (by have := usize_ge32; omega)
      rw [dite_eq_left_of_eq_true (eq_true hgu), dite_eq_left_of_eq_true (eq_true hg)]
      simp only [usize_ofNat_toNat']
      by_cases hf : (plainBad (ld64 a p)) == 0
      · simp only [hf, ↓reduceIte]
        have := ih (a.size - (p + 8).toNat) (by omega) (p + 8) (acc + 8) rfl (by omega)
        rw [this, hp8, ha8]
      · simp only [hf, Bool.false_eq_true, ↓reduceIte]
        have hne : plainBad (ld64 a p) ≠ 0 := by simpa using hf
        have hc := ctz_lt _ hne
        have hct := ctz_toUSize _ hne
        have hdiv : ((ctz (plainBad (ld64 a p))).toUSize / 8).toNat = (ctz (plainBad (ld64 a p))).toNat / 8 := by
          rw [USize.toNat_div, hct, h8]
        rw [usize_add_lt _ _ (by rw [hdiv]; have := usize_ge32; omega), hdiv]
    · have hgu : ¬ (p ≤ a.usize ∧ 8 ≤ a.usize - p) := fun h => hg ((guard_iff a hs p).1 h)
      rw [dite_eq_right_of_eq_false (eq_false hgu), dite_eq_right_of_eq_false (eq_false hg)]

/-- The byte loop of `scanDigitsW`'s tail. -/
theorem scanDigitsB_eq (a : ByteArray) (hs : a.size < 2 ^ 31) : ∀ d (i : USize), a.size - i.toNat = d → (scanDigitsB a i).toNat = scanDigits a i.toNat := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
    intro i hd
    rw [scanDigitsB, scanDigits]
    by_cases h : i < a.usize
    · have h2 := (lt_usize_iff a (by omega) i).1 h
      simp only [h, h2, ↓reduceDIte]
      have hi1 : (i + 1).toNat = i.toNat + 1 := usize_add_lit i 1 (by decide) (by have := usize_ge32; omega)
      by_cases hd2 : (digitVal (a.uget i (ugetOk a i h))).isSome = true
      · have hd3 : (digitVal a[i.toNat]).isSome = true := hd2
        simp only [hd2, hd3, ↓reduceIte]
        rw [ih (a.size - (i + 1).toNat) (by omega) (i + 1) rfl, hi1]
      · have hd3 : ¬ (digitVal a[i.toNat]).isSome = true := hd2
        simp only [hd2, hd3, Bool.false_eq_true, ↓reduceIte]
    · have h2 : ¬ i.toNat < a.size := fun h' => h ((lt_usize_iff a (by omega) i).2 h')
      simp only [h, h2, ↓reduceDIte]

theorem scanDigitsU_eq (a : ByteArray) (hs : a.size < 2 ^ 31) : ∀ d (i : USize), a.size - i.toNat = d → (scanDigitsU a i).toNat = scanDigitsW a i.toNat := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
    intro i hd
    have h8 := usize_lit 8 (by decide)
    rw [scanDigitsU, scanDigitsW]
    by_cases hg : i.toNat + 8 ≤ a.size
    · have hgu := (guard_iff a hs i).2 hg
      have hi8 : (i + 8).toNat = i.toNat + 8 := usize_add_lit i 8 (by decide) (by have := usize_ge32; omega)
      rw [dite_eq_left_of_eq_true (eq_true hgu), dite_eq_left_of_eq_true (eq_true hg)]
      simp only [usize_ofNat_toNat']
      by_cases hf : (ndFlags (ld64 a i)) == 0
      · simp only [hf, ↓reduceIte]
        rw [ih (a.size - (i + 8).toNat) (by omega) (i + 8) rfl, hi8]
      · simp only [hf, Bool.false_eq_true, ↓reduceIte]
        have hne : ndFlags (ld64 a i) ≠ 0 := by simpa using hf
        have hc := ctz_lt _ hne
        have hct := ctz_toUSize _ hne
        have hdiv : ((ctz (ndFlags (ld64 a i))).toUSize / 8).toNat = (ctz (ndFlags (ld64 a i))).toNat / 8 := by
          rw [USize.toNat_div, hct, h8]
        rw [usize_add_lt _ _ (by rw [hdiv]; have := usize_ge32; omega), hdiv]
    · have hgu : ¬ (i ≤ a.usize ∧ 8 ≤ a.usize - i) := fun h => hg ((guard_iff a hs i).1 h)
      rw [dite_eq_right_of_eq_false (eq_false hgu), dite_eq_right_of_eq_false (eq_false hg)]
      exact scanDigitsB_eq a hs _ i rfl


/-! ## The number scan -/

theorem scanDigits_bd (a : ByteArray) : ∀ d i, a.size - i = d → i ≤ scanDigits a i ∧ (i ≤ a.size → scanDigits a i ≤ a.size) := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
    intro i hd
    rw [scanDigits]
    by_cases h : i < a.size
    · simp only [h, ↓reduceDIte]
      by_cases hd2 : (digitVal a[i]).isSome = true
      · simp only [hd2, ↓reduceIte]
        have := ih (a.size - (i + 1)) (by omega) (i + 1) rfl
        exact ⟨by omega, fun _ => this.2 (by omega)⟩
      · simp only [hd2, Bool.false_eq_true, ↓reduceIte]
        exact ⟨Nat.le_refl _, fun h => h⟩
    · simp only [h, ↓reduceDIte]
      exact ⟨Nat.le_refl _, fun h => h⟩

/-- The `USize` answer `r` of a scan is the `Nat` answer `o`: `0` for none, else the same number (positive, inside the input). -/
def Opt (a : ByteArray) (o : Option Nat) (r : USize) : Prop := (r.toNat = 0 ∧ o = none) ∨ ∃ j, o = some j ∧ r.toNat = j ∧ 0 < j ∧ j ≤ a.size

theorem usize_zero_toNat : (0 : USize).toNat = 0 := usize_lit 0 (by decide)

theorem usize_beq_zero (r : USize) : (r == 0) = true ↔ r.toNat = 0 := by
  rw [beq_iff_eq]
  constructor
  · intro h; rw [h]; exact usize_zero_toNat
  · intro h; exact USize.toNat_inj.mp (by rw [h, usize_zero_toNat])

theorem succ_toNat (a : ByteArray) (hs : a.size < 2 ^ 31) (i : USize) (hi : i.toNat ≤ a.size) : (i + 1).toNat = i.toNat + 1 :=
  usize_add_lit i 1 (by decide) (by have := usize_ge32; omega)

theorem scanDigits1U_eq (a : ByteArray) (hs : a.size < 2 ^ 31) (i : USize) (hi : i.toNat ≤ a.size) : Opt a (scanDigits1W a i.toNat) (scanDigits1U a i) := by
  unfold scanDigits1W scanDigits1U byteAt
  by_cases h : i < a.usize
  · have h2 := (lt_usize_iff a (by omega) i).1 h
    simp only [h, h2, ↓reduceDIte]
    by_cases hd : (digitVal (a.uget i (ugetOk a i h))).isSome = true
    · have hd' : (digitVal a[i.toNat]).isSome = true := hd
      simp only [hd, hd', ↓reduceIte]
      refine Or.inr ⟨scanDigitsW a (i.toNat + 1), rfl, ?_, ?_, ?_⟩
      · rw [scanDigitsU_eq a hs _ (i + 1) rfl, succ_toNat a hs i hi]
      · rw [scanDigitsW_eq a (by omega) _ _ rfl]; have := (scanDigits_bd a _ (i.toNat + 1) rfl).1; omega
      · rw [scanDigitsW_eq a (by omega) _ _ rfl]; exact (scanDigits_bd a _ (i.toNat + 1) rfl).2 (by omega)
    · have hd' : ¬ (digitVal a[i.toNat]).isSome = true := hd
      simp only [hd, hd', Bool.false_eq_true, ↓reduceIte]
      exact Or.inl ⟨usize_zero_toNat, rfl⟩
  · have h2 : ¬ i.toNat < a.size := fun h' => h ((lt_usize_iff a (by omega) i).2 h')
    simp only [h, h2, ↓reduceDIte]
    exact Or.inl ⟨usize_zero_toNat, rfl⟩

theorem scanIntU_eq (a : ByteArray) (hs : a.size < 2 ^ 31) (i : USize) (hi : i.toNat ≤ a.size) : Opt a (scanIntW a i.toNat) (scanIntU a i) := by
  unfold scanIntW scanIntU byteAt
  by_cases h : i < a.usize
  · have h2 := (lt_usize_iff a (by omega) i).1 h
    simp only [h, h2, ↓reduceDIte]
    have e : a.uget i (ugetOk a i h) = a[i.toNat] := rfl
    simp only [e]
    by_cases h0 : (a[i.toNat] == 0x30) = true
    · simp only [h0, ↓reduceIte]
      exact Or.inr ⟨i.toNat + 1, rfl, succ_toNat a hs i hi, by omega, by omega⟩
    · simp only [h0, Bool.false_eq_true, ↓reduceIte]
      by_cases hd : (digit19 a[i.toNat]).isSome = true
      · simp only [hd, ↓reduceIte]
        refine Or.inr ⟨scanDigitsW a (i.toNat + 1), rfl, ?_, ?_, ?_⟩
        · rw [scanDigitsU_eq a hs _ (i + 1) rfl, succ_toNat a hs i hi]
        · rw [scanDigitsW_eq a (by omega) _ _ rfl]; have := (scanDigits_bd a _ (i.toNat + 1) rfl).1; omega
        · rw [scanDigitsW_eq a (by omega) _ _ rfl]; exact (scanDigits_bd a _ (i.toNat + 1) rfl).2 (by omega)
      · simp only [hd, Bool.false_eq_true, ↓reduceIte]
        exact Or.inl ⟨usize_zero_toNat, rfl⟩
  · have h2 : ¬ i.toNat < a.size := fun h' => h ((lt_usize_iff a (by omega) i).2 h')
    simp only [h, h2, ↓reduceDIte]
    exact Or.inl ⟨usize_zero_toNat, rfl⟩

theorem scanFracU_eq (a : ByteArray) (hs : a.size < 2 ^ 31) (i : USize) (hi : i.toNat ≤ a.size) (hp : 0 < i.toNat) : Opt a (scanFracW a i.toNat) (scanFracU a i) := by
  unfold scanFracW scanFracU
  rw [byteIsU_eq a (by omega)]
  by_cases hb : byteIs a i.toNat 0x2E = true
  · simp only [hb, ↓reduceIte]
    have hlt := (byteIs_spec a _ _ hb).1
    have := scanDigits1U_eq a hs (i + 1) (by rw [succ_toNat a hs i hi]; omega)
    rw [succ_toNat a hs i hi] at this
    exact this
  · simp only [hb, Bool.false_eq_true, ↓reduceIte]
    exact Or.inr ⟨i.toNat, rfl, rfl, hp, hi⟩

theorem scanExpU_eq (a : ByteArray) (hs : a.size < 2 ^ 31) (i : USize) (hi : i.toNat ≤ a.size) (hp : 0 < i.toNat) : Opt a (scanExpW a i.toNat) (scanExpU a i) := by
  unfold scanExpW scanExpU
  rw [byteIsU_eq a (by omega), byteIsU_eq a (by omega)]
  by_cases hb : (byteIs a i.toNat 0x65 || byteIs a i.toNat 0x45) = true
  · simp only [hb, ↓reduceIte]
    have hlt : i.toNat < a.size := by
      rcases Bool.or_eq_true_iff.mp hb with h1 | h1 <;> exact (byteIs_spec a _ _ h1).1
    have hi1 := succ_toNat a hs i hi
    rw [byteIsU_eq a (by omega), byteIsU_eq a (by omega), hi1]
    by_cases hc : (byteIs a (i.toNat + 1) 0x2B || byteIs a (i.toNat + 1) 0x2D) = true
    · simp only [hc, ↓reduceIte]
      have hlt2 : i.toNat + 1 < a.size := by
        rcases Bool.or_eq_true_iff.mp hc with h1 | h1 <;> exact (byteIs_spec a _ _ h1).1
      have h2 : (i + 2).toNat = i.toNat + 2 := usize_add_lit i 2 (by decide) (by have := usize_ge32; omega)
      have := scanDigits1U_eq a hs (i + 2) (by rw [h2]; omega)
      rw [h2] at this
      exact this
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      have := scanDigits1U_eq a hs (i + 1) (by rw [hi1]; omega)
      rw [hi1] at this
      exact this
  · simp only [hb, Bool.false_eq_true, ↓reduceIte]
    exact Or.inr ⟨i.toNat, rfl, rfl, hp, hi⟩

theorem scanNumU_eq (a : ByteArray) (hs : a.size < 2 ^ 31) (i : USize) (hi : i.toNat ≤ a.size) : Opt a (scanNumW a i.toNat) (scanNumU a i) := by
  unfold scanNumW scanNumU
  rw [byteIsU_eq a (by omega)]
  have key : ∀ i0 : USize, i0.toNat ≤ a.size → Opt a (scanIntW a i0.toNat) (scanIntU a i0) →
      Opt a (match scanIntW a i0.toNat with
        | none => none
        | some i1 => match scanFracW a i1 with
          | none => none
          | some i2 => scanExpW a i2) (let r1 := scanIntU a i0
        if r1 == 0 then 0 else
        let r2 := scanFracU a r1
        if r2 == 0 then 0 else scanExpU a r2) := by
    intro i0 hi0 h1
    rcases h1 with ⟨h1, h1'⟩ | ⟨j1, h1', h1'', hp1, hb1⟩
    · rw [h1']
      simp only [(usize_beq_zero _).2 h1, ↓reduceIte]
      exact Or.inl ⟨usize_zero_toNat, rfl⟩
    · rw [h1']
      have hne : ¬ (scanIntU a i0 == 0) = true := fun h => by have := (usize_beq_zero _).1 h; omega
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      have h2 := scanFracU_eq a hs (scanIntU a i0) (by omega) (by omega)
      rw [h1''] at h2
      rcases h2 with ⟨h2, h2'⟩ | ⟨j2, h2', h2'', hp2, hb2⟩
      · rw [h2']
        simp only [(usize_beq_zero _).2 h2, ↓reduceIte]
        exact Or.inl ⟨usize_zero_toNat, rfl⟩
      · rw [h2']
        have hne2 : ¬ (scanFracU a (scanIntU a i0) == 0) = true := fun h => by have := (usize_beq_zero _).1 h; omega
        simp only [hne2, Bool.false_eq_true, ↓reduceIte]
        have h3 := scanExpU_eq a hs (scanFracU a (scanIntU a i0)) (by omega) (by omega)
        rw [h2''] at h3
        exact h3
  by_cases hm : byteIs a i.toNat 0x2D = true
  · simp only [hm, ↓reduceIte]
    have hlt := (byteIs_spec a _ _ hm).1
    have h1 := succ_toNat a hs i hi
    have := key (i + 1) (by omega) (scanIntU_eq a hs (i + 1) (by omega))
    rw [h1] at this
    exact this
  · simp only [hm, Bool.false_eq_true, ↓reduceIte]
    exact key i hi (scanIntU_eq a hs i hi)


/-! ## The number text, the string leaf, the node -/

theorem guard2_iff (p e : USize) : (p ≤ e ∧ 8 ≤ e - p) ↔ p.toNat + 8 ≤ e.toNat := by
  have h8 := usize_lit 8 (by decide)
  constructor
  · rintro ⟨h1, h2⟩
    have h3 := USize.le_iff_toNat_le.1 h1
    have h4 := USize.le_iff_toNat_le.1 h2
    have h6 := USize.toNat_sub_of_le _ _ h1
    rw [h8, h6] at h4
    omega
  · intro h
    have h1 : p ≤ e := by rw [USize.le_iff_toNat_le]; omega
    refine ⟨h1, ?_⟩
    rw [USize.le_iff_toNat_le, USize.toNat_sub_of_le _ _ h1, h8]
    omega

theorem usize_toUInt64_sub (p e : USize) (h : p.toNat ≤ e.toNat) : (e - p).toUInt64 = (e.toNat - p.toNat).toUInt64 := by
  apply UInt64.toNat_inj.mp
  rw [USize.toNat_toUInt64, USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.2 h)]
  show _ = (UInt64.ofNat (e.toNat - p.toNat)).toNat
  rw [UInt64.toNat_ofNat']
  have := USize.toNat_lt_size e
  have h2 : System.Platform.numBits = 32 ∨ System.Platform.numBits = 64 := System.Platform.numBits_eq
  have h3 : e.toNat - p.toNat < 18446744073709551616 := by
    have : USize.size = 2 ^ System.Platform.numBits := rfl
    rcases h2 with h2 | h2 <;> rw [h2] at this <;> omega
  exact (Nat.mod_eq_of_lt h3).symm

theorem lexOkU_eq (a : ByteArray) (hs : a.size < 2 ^ 31) (e : USize) (he : e.toNat ≤ a.size) : ∀ d (p : USize), e.toNat - p.toNat = d → lexOkU a p e = lexOk a p.toNat e.toNat := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
    intro p hd
    rw [lexOkU, lexOk]
    by_cases hg : p.toNat + 8 ≤ e.toNat
    · have hgu := (guard2_iff p e).2 hg
      have hp8 : (p + 8).toNat = p.toNat + 8 := usize_add_lit p 8 (by decide) (by have := usize_ge32; omega)
      rw [dite_eq_left_of_eq_true (eq_true hgu), dite_eq_left_of_eq_true (eq_true hg)]
      simp only [usize_ofNat_toNat']
      by_cases hf : (lexBad (ld64 a p)) == 0
      · simp only [hf, ↓reduceIte]
        rw [ih (e.toNat - (p + 8).toNat) (by omega) (p + 8) rfl, hp8]
      · simp only [hf, Bool.false_eq_true, ↓reduceIte]
    · have hgu : ¬ (p ≤ e ∧ 8 ≤ e - p) := fun h => hg ((guard2_iff p e).1 h)
      rw [dite_eq_right_of_eq_false (eq_false hgu), dite_eq_right_of_eq_false (eq_false hg)]
      by_cases hl : p < e
      · have hl' : p.toNat < e.toNat := USize.lt_iff_toNat_lt.1 hl
        simp only [hl, hl', ↓reduceIte, usize_ofNat_toNat']
        rw [usize_toUInt64_sub p e (by omega)]
      · have hl' : ¬ p.toNat < e.toNat := fun h => hl (USize.lt_iff_toNat_lt.2 h)
        simp only [hl, hl', ↓reduceIte]

theorem plainOff_le (a : ByteArray) : ∀ d p acc, a.size - p = d → plainOff a p acc ≤ acc + (a.size - p) := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
    intro p acc hd
    rw [plainOff]
    by_cases h8 : p + 8 ≤ a.size
    · simp only [h8, ↓reduceDIte]
      by_cases hz : (plainBad (ld64 a p.toUSize) == 0) = true
      · simp only [hz, ↓reduceIte]
        have := ih (a.size - (p + 8)) (by omega) (p + 8) (acc + 8) rfl
        omega
      · simp only [hz, Bool.false_eq_true, ↓reduceIte]
        have hne : plainBad (ld64 a p.toUSize) ≠ 0 := by simpa using hz
        have := ctz_lt _ hne
        omega
    · simp only [h8, ↓reduceDIte]
      omega

theorem ensureTapeU_eq (t : ByteArray) (ht : t.size < 4294967296) (w : USize) (hw : w.toNat + 2 < 4294967296) : ensureTapeU t w = ensureTape t w.toNat := by
  unfold ensureTapeU ensureTape
  have hu := usize_eq t ht
  have h2 : (w + 2).toNat = w.toNat + 2 := usize_add_lit w 2 (by decide) (by have := usize_ge32; omega)
  have h3 : (t.usize >>> (3 : USize)).toNat = t.size / 8 := by
    rw [USize.toNat_shiftRight, usize_lit 3 (by decide), hu, Nat.shiftRight_eq_div_pow]
    have h4 : System.Platform.numBits = 32 ∨ System.Platform.numBits = 64 := System.Platform.numBits_eq
    rcases h4 with h4 | h4 <;> rw [h4] <;> rfl
  have : (w + 2 ≤ (t.usize >>> (3 : USize))) ↔ w.toNat + 2 ≤ t.size / 8 := by
    rw [USize.le_iff_toNat_le, h2, h3]
  by_cases hc : w.toNat + 2 ≤ t.size / 8
  · simp only [this.2 hc, hc, ↓reduceIte]
  · simp only [(not_congr this).2 hc, hc, ↓reduceIte]

theorem putNodeU_eq (t : ByteArray) (ht : t.size < 4294967296) (w : USize) (hw : w.toNat + 2 < 4294967296) (h x : UInt64) : putNodeU t w h x = putNode t w.toNat h x := by
  unfold putNodeU putNode
  rw [ensureTapeU_eq t ht w hw]
  have h1 : (w + 1).toNat = w.toNat + 1 := usize_add_lit w 1 (by decide) (by have := usize_ge32; omega)
  have h2 : w + 1 = (w.toNat + 1).toUSize := by
    apply USize.toNat_inj.mp
    rw [h1, usize_toNat_small _ (by omega)]
  rw [usize_ofNat_toNat', h2]

theorem putNode_size (t : ByteArray) (w : Nat) (hw : w + 2 < 4294967296) (ht : t.size ≤ 8 * w + 4096) (h x : UInt64) : (putNode t w h x).size ≤ 8 * (w + 2) + 4096 := by
  unfold putNode
  rw [st64_toUSize _ (w + 1) x (by omega), st64_toUSize _ w h (by omega), st64Model_size, st64Model_size]
  unfold ensureTape
  by_cases hc : w + 2 ≤ t.size / 8
  · simp only [hc, ↓reduceIte]; omega
  · simp only [hc, ↓reduceIte]
    have := (growTape_spec t).1
    omega


/-- The `USize` answer of the string leaf is the `Nat` answer (the position moves from `Nat` to `USize`, at most one past the end). -/
def StrRel (a : ByteArray) (o : Option (ByteArray × Nat)) (r : Option (ByteArray × USize)) : Prop :=
  (o = none ∧ r = none) ∨ ∃ (t : ByteArray) (j : Nat) (ju : USize), o = some (t, j) ∧ r = some (t, ju) ∧ ju.toNat = j ∧ j ≤ a.size + 1

theorem strU_eq (a : ByteArray) (hs26 : a.size < 2 ^ 26) (i : USize) (text : ByteArray) :
    StrRel a (strW (stage1 a) a i.toNat text) (strU (stage1 a) a i text) := by
  have hs : a.size < 2 ^ 31 := by omega
  unfold strW strU
  rw [byteIsU_eq a (by omega)]
  by_cases hq : byteIs a i.toNat 0x22 = true
  · simp only [hq, ↓reduceIte]
    have hlt := (byteIs_spec a _ _ hq).1
    have hi1 : (i + 1).toNat = i.toNat + 1 := usize_add_lit i 1 (by decide) (by have := usize_ge32; omega)
    have hfs := skipI_spec a hs (i.toNat + 1) (by omega)
    have hr1 : i.toNat + 1 ≤ skipI (stage1 a) a.size (i.toNat + 1) := hfs.1
    have hrle := skipI_le (stage1 a) a.size (i.toNat + 1)
    have hr : (skipU (stage1 a) a.usize (i + 1)).toNat = skipF (stage1 a) a.size (i.toNat + 1) := by
      rw [skipF_eq, ← hi1]
      exact skipU_eq (stage1 a) a hs (i + 1) (by rw [hi1]; omega)
    have hpo : (plainOffU a (i + 1) 0).toNat = plainOff a (i.toNat + 1) 0 := by
      rw [plainOffU_eq a hs _ (i + 1) 0 rfl (by rw [hi1, usize_zero_toNat]; omega), hi1, usize_zero_toNat]
    have hpl := plainOff_le a _ (i.toNat + 1) 0 rfl
    have hsum : (i + 1 + plainOffU a (i + 1) 0).toNat = i.toNat + 1 + plainOff a (i.toNat + 1) 0 := by
      rw [usize_add_lt _ _ (by rw [hi1, hpo]; have := usize_ge32; omega), hi1, hpo]
    have hr1' : (byteIsU a (skipU (stage1 a) a.usize (i + 1)) 0x22) = byteIs a (skipF (stage1 a) a.size (i.toNat + 1)) 0x22 := by
      rw [byteIsU_eq a (by omega), hr]
    have hcond : (i + 1 + plainOffU a (i + 1) 0 == skipU (stage1 a) a.usize (i + 1) && byteIsU a (skipU (stage1 a) a.usize (i + 1)) 0x22) =
        (i.toNat + 1 + plainOff a (i.toNat + 1) 0 == skipF (stage1 a) a.size (i.toNat + 1) && byteIs a (skipF (stage1 a) a.size (i.toNat + 1)) 0x22) := by
      rw [hr1']
      congr 1
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq]
      rw [← USize.toNat_inj, hsum, hr]
    have hrle' : skipF (stage1 a) a.size (i.toNat + 1) ≤ a.size := by rw [skipF_eq]; exact hrle
    have hr1'' : i.toNat + 1 ≤ skipF (stage1 a) a.size (i.toNat + 1) := by rw [skipF_eq]; exact hr1
    simp only [hi1, hcond]
    by_cases hc : (i.toNat + 1 + plainOff a (i.toNat + 1) 0 == skipF (stage1 a) a.size (i.toNat + 1) && byteIs a (skipF (stage1 a) a.size (i.toNat + 1)) 0x22) = true
    · simp only [hc, ↓reduceIte]
      have hi_le : i ≤ skipU (stage1 a) a.usize (i + 1) := by rw [USize.le_iff_toNat_le, hr]; omega
      have hsub1 := USize.toNat_sub_of_le _ _ hi_le
      have hi_le2 : (1 : USize) ≤ skipU (stage1 a) a.usize (i + 1) - i := by
        rw [USize.le_iff_toNat_le, hsub1, hr, usize_lit 1 (by decide)]; omega
      have hsub2 := USize.toNat_sub_of_le _ _ hi_le2
      refine Or.inr ⟨a.copySlice (i.toNat + 1) text text.size (skipF (stage1 a) a.size (i.toNat + 1) - i.toNat - 1) false, skipF (stage1 a) a.size (i.toNat + 1) + 1,
        skipU (stage1 a) a.usize (i + 1) + 1, rfl, ?_, ?_, by omega⟩
      · rw [hsub2, hsub1, hr, usize_lit 1 (by decide)]
      · exact (usize_add_lit _ 1 (by decide) (by rw [hr]; have := usize_ge32; omega)).trans (by rw [hr])
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      cases hb : strBytesW a (i.toNat + 1) text with
      | none => exact Or.inl ⟨rfl, rfl⟩
      | some tj =>
        obtain ⟨t, j⟩ := tj
        simp only []
        rw [hr]
        by_cases hj : (skipF (stage1 a) a.size (i.toNat + 1) == j - 1) = true
        · simp only [hj, ↓reduceIte]
          have hj' := beq_iff_eq.mp hj
          exact Or.inr ⟨t, j, j.toUSize, rfl, rfl, usize_toNat_small _ (by omega), by omega⟩
        · simp only [hj, Bool.false_eq_true, ↓reduceIte]
          exact Or.inl ⟨rfl, rfl⟩
  · simp only [hq, Bool.false_eq_true, ↓reduceIte]
    exact Or.inl ⟨rfl, rfl⟩


/-! ## The simulation -/

/-- The number of open containers. -/
def fsLen : FStack → Nat
  | .nil => 0
  | .arr _ _ r => fsLen r + 1
  | .obj _ _ r => fsLen r + 1

theorem sk0 (a : ByteArray) (hs : a.size < 2 ^ 26) (x : USize) (hx : x.toNat ≤ a.size + 2) :
    (skipU (stage1 a) a.usize x).toNat = skipI (stage1 a) a.size x.toNat := skipU_eq (stage1 a) a (by omega) x (by omega)

theorem add_one (a : ByteArray) (x : USize) (hx : x.toNat ≤ a.size + 2) (hs : a.size < 2 ^ 26) : (x + 1).toNat = x.toNat + 1 :=
  usize_add_lit x 1 (by decide) (by have := usize_ge32; omega)

theorem st64_size (a : ByteArray) (k : USize) (w : UInt64) : (st64 a k w).size = a.size := st64Model_size a k.toNat w

theorem pnU (a : ByteArray) (hsz : a.size < 2 ^ 26) (tape : ByteArray) (tw : USize) (hw : tw.toNat + 2 ≤ 4 * a.size + 8) (htape : tape.size ≤ 8 * tw.toNat + 4096) (h x : UInt64) :
    putNodeU tape tw h x = putNode tape tw.toNat h x ∧ (tw + 2).toNat = tw.toNat + 2 ∧ (putNode tape tw.toNat h x).size ≤ 8 * (tw.toNat + 2) + 4096 :=
  ⟨putNodeU_eq tape (by omega) tw (by omega) h x, usize_add_lit tw 2 (by decide) (by have := usize_ge32; omega), putNode_size tape tw.toNat (by omega) htape h x⟩

theorem lit3_eq (a : ByteArray) (i : Nat) (x y z : UInt8) :
    litA a (i + 1) [x, y, z] = if (byteIs a (i + 1) x && byteIs a (i + 2) y && byteIs a (i + 3) z) = true then some (i + 4) else none := by
  simp only [litA]
  cases byteIs a (i + 1) x <;> cases byteIs a (i + 2) y <;> cases byteIs a (i + 1 + 1 + 1) z <;> simp [Nat.add_assoc]

theorem lit4_eq (a : ByteArray) (i : Nat) (x y z w : UInt8) :
    litA a (i + 1) [x, y, z, w] = if (byteIs a (i + 1) x && byteIs a (i + 2) y && byteIs a (i + 3) z && byteIs a (i + 4) w) = true then some (i + 5) else none := by
  simp only [litA]
  cases byteIs a (i + 1) x <;> cases byteIs a (i + 2) y <;> cases byteIs a (i + 3) z <;> cases byteIs a (i + 1 + 1 + 1 + 1) w <;> simp [Nat.add_assoc]

theorem fsLen_arr (at_ n : Nat) (r : FStack) : fsLen (.arr at_ n r) = fsLen r + 1 := rfl
theorem fsLen_obj (at_ n : Nat) (r : FStack) : fsLen (.obj at_ n r) = fsLen r + 1 := rfl

theorem runU_sound (a : ByteArray) (hsz : a.size < 2 ^ 26) :
    ∀ (f : Nat) (fu i : USize) (ret : Bool) (tape : ByteArray) (tw : USize) (text : ByteArray) (fst : FStack) (d : USize) (t : ByteArray),
      fu.toNat = f → i.toNat ≤ a.size + 1 → tw.toNat + 4 * f ≤ 4 * a.size + 8 → tape.size ≤ 8 * tw.toNat + 4096 → d.toNat + fsLen fst ≤ 512 →
      runU (stage1 a) fu a i ret tape tw text fst d = some t →
      runW (stage1 a) f a i.toNat ret tape tw.toNat text fst d.toNat = some t := by
  have hs31 : a.size < 2 ^ 31 := by omega
  have hs32 : a.size < 4294967296 := by omega
  intro f
  induction f with
  | zero =>
    intro fu i ret tape tw text fst d t hf _ _ _ _ h
    rw [runU] at h
    have h0 : (fu == 0) = true := (usize_beq_zero fu).2 hf
    simp [h0] at h
  | succ f ih =>
    intro fu i ret tape tw text fst d t hf hi htw htape hd h
    have hfu : ¬ (fu == 0) = true := fun h0 => by have := (usize_beq_zero fu).1 h0; omega
    have hf1 : (fu - 1).toNat = f := by
      have h3 : (1 : USize) ≤ fu := by rw [USize.le_iff_toNat_le, usize_lit 1 (by decide)]; omega
      rw [USize.toNat_sub_of_le fu 1 h3, usize_lit 1 (by decide)]; omega
    rw [runU] at h
    simp only [hfu, Bool.false_eq_true, ↓reduceIte] at h
    cases ret with
    | false =>
      rw [runW]
      simp only [] at h
      by_cases hlt : i < a.usize
      · have hlt' : i.toNat < a.size := (lt_usize_iff a hs32 i).1 hlt
        have e : a.uget i (ugetOk a i hlt) = a[i.toNat] := rfl
        simp only [hlt, ↓reduceDIte, e] at h
        simp only [byteAt, hlt', ↓reduceDIte]
        have pe3 : (tw + 2).toNat = tw.toNat + 2 := usize_add_lit tw 2 (by decide) (by have := usize_ge32; omega)
        by_cases h5b : (a[i.toNat] == 0x5B) = true
        · simp only [h5b, ↓reduceIte] at h ⊢
          by_cases hd0 : (d == 0) = true
          · simp [hd0] at h
          · have hdn : (d.toNat == 0) = false := by
              have := (usize_beq_zero d); simp only [hd0, Bool.false_eq_true, false_iff] at this; simpa using this
            have hdpos : d.toNat ≠ 0 := by simpa using hdn
            simp only [hd0, hdn, Bool.false_eq_true, ↓reduceIte] at h ⊢
            have hi1 := add_one a i (by omega) hsz
            have hk := sk0 a hsz (i + 1) (by omega)
            have hkle := skipI_le (stage1 a) a.size (i.toNat + 1)
            rw [hi1] at hk
            simp only [byteIsU_eq a hs32] at h
            rw [skipF_eq, ← hk]
            by_cases h5d : byteIs a (skipU (stage1 a) a.usize (i + 1)).toNat 0x5D = true
            · simp only [h5d, ↓reduceIte] at h ⊢
              obtain ⟨pe2, -, pe4⟩ := pnU a hsz tape tw (by omega) htape (hdrW 5 0) 2
              have e1 := add_one a (skipU (stage1 a) a.usize (i + 1)) (by omega) hsz
              have key := ih _ _ _ _ _ _ _ _ _ hf1 (by rw [e1]; omega) (by rw [pe3]; omega) (by rw [pe2, pe3]; exact pe4) (by omega) h
              rw [e1, pe2, pe3] at key
              exact key
            · simp only [h5d, Bool.false_eq_true, ↓reduceIte] at h ⊢
              obtain ⟨pe2, -, pe4⟩ := pnU a hsz tape tw (by omega) htape (hdrW 5 0) 0
              have hd1 : (d - 1).toNat = d.toNat - 1 := by
                rw [USize.toNat_sub_of_le d 1 (by rw [USize.le_iff_toNat_le, usize_lit 1 (by decide)]; omega), usize_lit 1 (by decide)]
              have key := ih _ _ _ _ _ _ _ _ _ hf1 (by omega) (by rw [pe3]; omega) (by rw [pe2, pe3]; exact pe4) (by rw [hd1, fsLen_arr]; omega) h
              rw [pe2, pe3, hd1] at key
              exact key
        · simp only [h5b, Bool.false_eq_true, ↓reduceIte] at h ⊢
          by_cases h7b : (a[i.toNat] == 0x7B) = true
          · simp only [h7b, ↓reduceIte] at h ⊢
            by_cases hd0 : (d == 0) = true
            · simp [hd0] at h
            · have hdn : (d.toNat == 0) = false := by
                have := (usize_beq_zero d); simp only [hd0, Bool.false_eq_true, false_iff] at this; simpa using this
              have hdpos : d.toNat ≠ 0 := by simpa using hdn
              simp only [hd0, hdn, Bool.false_eq_true, ↓reduceIte] at h ⊢
              have hi1 := add_one a i (by omega) hsz
              have hk := sk0 a hsz (i + 1) (by omega)
              have hkle := skipI_le (stage1 a) a.size (i.toNat + 1)
              rw [hi1] at hk
              simp only [byteIsU_eq a hs32] at h
              rw [skipF_eq, ← hk]
              have hd1 : (d - 1).toNat = d.toNat - 1 := by
                rw [USize.toNat_sub_of_le d 1 (by rw [USize.le_iff_toNat_le, usize_lit 1 (by decide)]; omega), usize_lit 1 (by decide)]
              by_cases h7d : byteIs a (skipU (stage1 a) a.usize (i + 1)).toNat 0x7D = true
              · simp only [h7d, ↓reduceIte] at h ⊢
                obtain ⟨pe2, -, pe4⟩ := pnU a hsz tape tw (by omega) htape (hdrW 6 0) 2
                have e1 := add_one a (skipU (stage1 a) a.usize (i + 1)) (by omega) hsz
                have key := ih _ _ _ _ _ _ _ _ _ hf1 (by rw [e1]; omega) (by rw [pe3]; omega) (by rw [pe2, pe3]; exact pe4) (by omega) h
                rw [e1, pe2, pe3] at key
                exact key
              · simp only [h7d, Bool.false_eq_true, ↓reduceIte] at h ⊢
                obtain ⟨pe2, -, pe4⟩ := pnU a hsz tape tw (by omega) htape (hdrW 6 0) 0
                rcases strU_eq a hsz (skipU (stage1 a) a.usize (i + 1)) text with ⟨ho, hr⟩ | ⟨t', j, ju, ho, hr, hj, hjb⟩
                · rw [hr] at h; simp at h
                · rw [hr] at h
                  rw [ho]
                  simp only [] at h ⊢
                  subst hj
                  have hk2 := sk0 a hsz ju (by omega)
                  have hk2le := skipI_le (stage1 a) a.size ju.toNat
                  rw [skipF_eq, ← hk2]
                  by_cases hc : byteIs a (skipU (stage1 a) a.usize ju).toNat 0x3A = true
                  · simp only [hc, ↓reduceIte] at h ⊢
                    have e1 := add_one a (skipU (stage1 a) a.usize ju) (by omega) hsz
                    have hk3 := sk0 a hsz (skipU (stage1 a) a.usize ju + 1) (by omega)
                    rw [e1] at hk3
                    have hk3le := skipI_le (stage1 a) a.size ((skipU (stage1 a) a.usize ju).toNat + 1)
                    rw [skipF_eq, ← hk3]
                    obtain ⟨pf2, pf3, pf4⟩ := pnU a hsz (putNodeU tape tw (hdrW 6 0) 0) (tw + 2) (by omega) (by rw [pe2, pe3]; exact pe4) (hdrW 4 (t'.size - text.size)) (UInt64.ofNat text.size)
                    have pe5 : (tw + 4).toNat = tw.toNat + 4 := usize_add_lit tw 4 (by decide) (by have := usize_ge32; omega)
                    have key := ih _ _ _ _ _ _ _ _ _ hf1 (by omega) (by rw [pe5]; omega) (by rw [pf2, pe2, pe5, pe3]; rw [pe2, pe3] at pf4; omega)
                      (by rw [hd1, fsLen_obj]; omega) h
                    rw [pf2, pe2, pe3, pe5, hd1] at key
                    exact key
                  · simp only [hc, Bool.false_eq_true, ↓reduceIte] at h ⊢
                    simp at h
          · simp only [h7b, Bool.false_eq_true, ↓reduceIte] at h ⊢
            by_cases h22 : (a[i.toNat] == 0x22) = true
            · simp only [h22, ↓reduceIte] at h ⊢
              rcases strU_eq a hsz i text with ⟨ho, hr⟩ | ⟨t', j, ju, ho, hr, hj, hjb⟩
              · rw [hr] at h; simp at h
              · rw [hr] at h
                rw [ho]
                simp only [] at h ⊢
                subst hj
                obtain ⟨pe2, -, pe4⟩ := pnU a hsz tape tw (by omega) htape (hdrW 4 (t'.size - text.size)) (UInt64.ofNat text.size)
                have key := ih _ _ _ _ _ _ _ _ _ hf1 hjb (by rw [pe3]; omega) (by rw [pe2, pe3]; exact pe4) hd h
                rw [pe2, pe3] at key
                exact key
            · simp only [h22, Bool.false_eq_true, ↓reduceIte] at h ⊢
              have hi2 : (i + 2).toNat = i.toNat + 2 := usize_add_lit i 2 (by decide) (by have := usize_ge32; omega)
              have hi3 : (i + 3).toNat = i.toNat + 3 := usize_add_lit i 3 (by decide) (by have := usize_ge32; omega)
              have hi4 : (i + 4).toNat = i.toNat + 4 := usize_add_lit i 4 (by decide) (by have := usize_ge32; omega)
              have hi5 : (i + 5).toNat = i.toNat + 5 := usize_add_lit i 5 (by decide) (by have := usize_ge32; omega)
              have hi1 := add_one a i (by omega) hsz
              by_cases h6e : (a[i.toNat] == 0x6E) = true
              · simp only [h6e, ↓reduceIte] at h ⊢
                simp only [byteIsU_eq a hs32, delimAtU_eq a hs32, hi1, hi2, hi3, hi4] at h
                rw [lit3_eq]
                by_cases hc3 : (byteIs a (i.toNat + 1) 0x75 && byteIs a (i.toNat + 2) 0x6C && byteIs a (i.toNat + 3) 0x6C) = true
                · simp only [hc3, ↓reduceIte] at h ⊢
                  simp only [Bool.and_eq_true] at hc3
                  have hlt3 := (byteIs_spec a _ _ hc3.2).1
                  by_cases hdl : delimAt a (i.toNat + 4) = true
                  · simp only [hdl, ↓reduceIte] at h ⊢
                    obtain ⟨pe2, -, pe4⟩ := pnU a hsz tape tw (by omega) htape (hdrW 0 0) 0
                    have key := ih _ _ _ _ _ _ _ _ _ hf1 (by rw [hi4]; omega) (by rw [pe3]; omega) (by rw [pe2, pe3]; exact pe4) hd h
                    rw [hi4, pe2, pe3] at key
                    exact key
                  · simp only [hdl, Bool.false_eq_true, ↓reduceIte] at h; simp at h
                · simp only [hc3, Bool.false_eq_true, ↓reduceIte] at h; simp at h
              · simp only [h6e, Bool.false_eq_true, ↓reduceIte] at h ⊢
                by_cases h74 : (a[i.toNat] == 0x74) = true
                · simp only [h74, ↓reduceIte] at h ⊢
                  simp only [byteIsU_eq a hs32, delimAtU_eq a hs32, hi1, hi2, hi3, hi4] at h
                  rw [lit3_eq]
                  by_cases hc3 : (byteIs a (i.toNat + 1) 0x72 && byteIs a (i.toNat + 2) 0x75 && byteIs a (i.toNat + 3) 0x65) = true
                  · simp only [hc3, ↓reduceIte] at h ⊢
                    simp only [Bool.and_eq_true] at hc3
                    have hlt3 := (byteIs_spec a _ _ hc3.2).1
                    by_cases hdl : delimAt a (i.toNat + 4) = true
                    · simp only [hdl, ↓reduceIte] at h ⊢
                      obtain ⟨pe2, -, pe4⟩ := pnU a hsz tape tw (by omega) htape (hdrW 2 0) 0
                      have key := ih _ _ _ _ _ _ _ _ _ hf1 (by rw [hi4]; omega) (by rw [pe3]; omega) (by rw [pe2, pe3]; exact pe4) hd h
                      rw [hi4, pe2, pe3] at key
                      exact key
                    · simp only [hdl, Bool.false_eq_true, ↓reduceIte] at h; simp at h
                  · simp only [hc3, Bool.false_eq_true, ↓reduceIte] at h; simp at h
                · simp only [h74, Bool.false_eq_true, ↓reduceIte] at h ⊢
                  by_cases h66 : (a[i.toNat] == 0x66) = true
                  · simp only [h66, ↓reduceIte] at h ⊢
                    simp only [byteIsU_eq a hs32, delimAtU_eq a hs32, hi1, hi2, hi3, hi4, hi5] at h
                    rw [lit4_eq]
                    by_cases hc3 : (byteIs a (i.toNat + 1) 0x61 && byteIs a (i.toNat + 2) 0x6C && byteIs a (i.toNat + 3) 0x73 && byteIs a (i.toNat + 4) 0x65) = true
                    · simp only [hc3, ↓reduceIte] at h ⊢
                      simp only [Bool.and_eq_true] at hc3
                      have hlt3 := (byteIs_spec a _ _ hc3.2).1
                      by_cases hdl : delimAt a (i.toNat + 5) = true
                      · simp only [hdl, ↓reduceIte] at h ⊢
                        obtain ⟨pe2, -, pe4⟩ := pnU a hsz tape tw (by omega) htape (hdrW 1 0) 0
                        have key := ih _ _ _ _ _ _ _ _ _ hf1 (by rw [hi5]; omega) (by rw [pe3]; omega) (by rw [pe2, pe3]; exact pe4) hd h
                        rw [hi5, pe2, pe3] at key
                        exact key
                      · simp only [hdl, Bool.false_eq_true, ↓reduceIte] at h; simp at h
                    · simp only [hc3, Bool.false_eq_true, ↓reduceIte] at h; simp at h
                  · simp only [h66, Bool.false_eq_true, ↓reduceIte] at h ⊢
                    rcases scanNumU_eq a hs31 i (by omega) with ⟨h0, ho⟩ | ⟨j, ho, hj, hp, hb⟩
                    · simp only [(usize_beq_zero _).2 h0, ↓reduceIte] at h
                      simp at h
                    · rw [ho]
                      simp only [] at h ⊢
                      have hne : ¬ (scanNumU a i == 0) = true := fun h' => by have := (usize_beq_zero _).1 h'; omega
                      have hadv := scanNum_adv a i.toNat j (by rw [← scanNumW_eq a hs31]; exact ho)
                      have hle : i ≤ scanNumU a i := by rw [USize.le_iff_toNat_le, hj]; omega
                      have hsub := USize.toNat_sub_of_le _ _ hle
                      rw [hj] at hsub
                      have hlex := lexOkU_eq a hs31 (scanNumU a i) (by omega) _ i rfl
                      rw [hj] at hlex
                      simp only [hne, Bool.false_eq_true, ↓reduceIte, delimAtU_eq a hs32, hj, hsub, hlex] at h
                      by_cases hdl : delimAt a j = true
                      · simp only [hdl, ↓reduceIte] at h ⊢
                        obtain ⟨pe2, -, pe4⟩ := pnU a hsz tape tw (by omega) htape
                          (hdrW 3 ((if lexOk a i.toNat j = true then a.copySlice i.toNat text text.size (j - i.toNat) false else pushLex a i.toNat j text).size - text.size)) (UInt64.ofNat text.size)
                        have key := ih _ _ _ _ _ _ _ _ _ hf1 (by rw [hj]; omega) (by rw [pe3]; omega) (by rw [pe2, pe3]; exact pe4) hd h
                        rw [hj, pe2, pe3] at key
                        exact key
                      · simp only [hdl, Bool.false_eq_true, ↓reduceIte] at h; simp at h
      · simp only [hlt, ↓reduceDIte] at h
        simp at h
    | true =>
      have hk := sk0 a hsz i (by omega)
      have hkle := skipI_le (stage1 a) a.size i.toNat
      cases fst with
      | nil =>
        rw [runW]
        simp only [] at h
        simp only [skipF_eq, ← hk]
        have : (a.usize ≤ skipU (stage1 a) a.usize i) ↔ a.size ≤ (skipU (stage1 a) a.usize i).toNat := by
          rw [USize.le_iff_toNat_le, usize_eq a hs32]
        by_cases hc : a.usize ≤ skipU (stage1 a) a.usize i
        · simp only [hc, ↓reduceIte, this.1 hc, Option.some.injEq] at h ⊢
          exact h
        · simp only [hc, ↓reduceIte] at h
          simp at h
      | arr at_ n rest =>
        rw [runW]
        simp only [] at h
        have hdl : (d + 1).toNat = d.toNat + 1 := usize_add_lit d 1 (by decide) (by have := usize_ge32; rw [fsLen_arr] at hd; omega)
        simp only [byteIsU_eq a hs32] at h
        simp only [skipF_eq, ← hk]
        have e1 := add_one a (skipU (stage1 a) a.usize i) (by omega) hsz
        by_cases hcomma : byteIs a (skipU (stage1 a) a.usize i).toNat 0x2C = true
        · simp only [hcomma, ↓reduceIte] at h ⊢
          have hk2 := sk0 a hsz (skipU (stage1 a) a.usize i + 1) (by omega)
          rw [e1] at hk2
          have hk2le := skipI_le (stage1 a) a.size ((skipU (stage1 a) a.usize i).toNat + 1)
          rw [← hk2]
          have key := ih _ _ _ _ _ _ _ _ _ hf1 (by omega) (by omega) htape (by rw [fsLen_arr] at hd ⊢; omega) h
          exact key
        · simp only [hcomma, Bool.false_eq_true, ↓reduceIte] at h ⊢
          by_cases hclose : byteIs a (skipU (stage1 a) a.usize i).toNat 0x5D = true
          · simp only [hclose, ↓reduceIte] at h ⊢
            have key := ih _ _ _ _ _ _ _ _ _ hf1 (by omega) (by omega) (by rw [st64_size, st64_size]; exact htape) (by rw [hdl]; rw [fsLen_arr] at hd; omega) h
            rw [e1, hdl] at key
            exact key
          · simp only [hclose, Bool.false_eq_true, ↓reduceIte] at h
            simp at h
      | obj at_ n rest =>
        rw [runW]
        simp only [] at h
        have hdl : (d + 1).toNat = d.toNat + 1 := usize_add_lit d 1 (by decide) (by have := usize_ge32; rw [fsLen_obj] at hd; omega)
        simp only [byteIsU_eq a hs32] at h
        simp only [skipF_eq, ← hk]
        have e1 := add_one a (skipU (stage1 a) a.usize i) (by omega) hsz
        by_cases hcomma : byteIs a (skipU (stage1 a) a.usize i).toNat 0x2C = true
        · simp only [hcomma, ↓reduceIte] at h ⊢
          have hk2 := sk0 a hsz (skipU (stage1 a) a.usize i + 1) (by omega)
          rw [e1] at hk2
          have hk2le := skipI_le (stage1 a) a.size ((skipU (stage1 a) a.usize i).toNat + 1)
          rw [← hk2]
          rcases strU_eq a hsz (skipU (stage1 a) a.usize (skipU (stage1 a) a.usize i + 1)) text with ⟨ho, hr⟩ | ⟨t', j, ju, ho, hr, hj, hjb⟩
          · rw [hr] at h; simp at h
          · rw [hr] at h
            rw [ho]
            simp only [] at h ⊢
            subst hj
            have hk3 := sk0 a hsz ju (by omega)
            have hk3le := skipI_le (stage1 a) a.size ju.toNat
            rw [← hk3]
            by_cases hc : byteIs a (skipU (stage1 a) a.usize ju).toNat 0x3A = true
            · simp only [hc, ↓reduceIte] at h ⊢
              have e2 := add_one a (skipU (stage1 a) a.usize ju) (by omega) hsz
              have hk4 := sk0 a hsz (skipU (stage1 a) a.usize ju + 1) (by omega)
              rw [e2] at hk4
              have hk4le := skipI_le (stage1 a) a.size ((skipU (stage1 a) a.usize ju).toNat + 1)
              rw [← hk4]
              obtain ⟨pe2, pe3, pe4⟩ := pnU a hsz tape tw (by omega) htape (hdrW 4 (t'.size - text.size)) (UInt64.ofNat text.size)
              have key := ih _ _ _ _ _ _ _ _ _ hf1 (by omega) (by rw [pe3]; omega) (by rw [pe2, pe3]; exact pe4) (by rw [fsLen_obj] at hd ⊢; omega) h
              rw [pe2, pe3] at key
              exact key
            · simp only [hc, Bool.false_eq_true, ↓reduceIte] at h
              simp at h
        · simp only [hcomma, Bool.false_eq_true, ↓reduceIte] at h ⊢
          by_cases hclose : byteIs a (skipU (stage1 a) a.usize i).toNat 0x7D = true
          · simp only [hclose, ↓reduceIte] at h ⊢
            have key := ih _ _ _ _ _ _ _ _ _ hf1 (by omega) (by omega) (by rw [st64_size, st64_size]; exact htape) (by rw [hdl]; rw [fsLen_obj] at hd; omega) h
            rw [e1, hdl] at key
            exact key
          · simp only [hclose, Bool.false_eq_true, ↓reduceIte] at h
            simp at h

theorem initTape_size (cap : Nat) : (initTape cap).size = 4096 := by
  unfold initTape
  have hz : zeros4k.size = 4096 := (zeroBytes_spec 4096).1
  have e0 : (ByteArray.emptyWithCapacity cap).size = 0 := rfl
  have h := copy_append zeros4k (ByteArray.emptyWithCapacity cap) 0 4096
  rw [h, ByteArray.size_append, e0, ByteArray.size_extract, hz]
  omega

/-- The parser with `runU` returns exactly what the scalar fused parser returns (and so, by `parseTapeFast_eq`, the tape of the `Value`). -/
theorem parseTapeU_eq (a : ByteArray) : parseTapeU a = parseTapeFast a := by
  unfold parseTapeU
  by_cases hsz : a.size < simdLimit
  · simp only [hsz, ↓reduceIte]
    have hsz' : a.size < 2 ^ 26 := by unfold simdLimit at hsz; omega
    have hs31 : a.size < 2 ^ 31 := by omega
    rw [stage1Fast_eq a hs31]
    have hmd : (maxDepth.toUSize).toNat = maxDepth := usize_toNat_small _ (by unfold maxDepth; decide)
    have hfu : (a.usize + 2).toNat = a.size + 2 := by
      rw [usize_add_lit _ 2 (by decide) (by have := usize_ge32; rw [usize_eq a (by omega)]; omega), usize_eq a (by omega)]
    have hk := sk0 a hsz' 0 (by rw [usize_zero_toNat]; omega)
    rw [usize_zero_toNat] at hk
    have hz : zeros4k.size = 4096 := (zeroBytes_spec 4096).1
    generalize hT : initTape (tapeHint (stage1 a)) = T0
    have ht0 : T0.size = 4096 := by rw [← hT]; exact initTape_size _
    cases hr : runU (stage1 a) (a.usize + 2) a (skipU (stage1 a) a.usize 0) false T0 0 (ByteArray.emptyWithCapacity a.size) FStack.nil maxDepth.toUSize with
    | none => rfl
    | some t =>
      have hW := runU_sound a hsz' (a.size + 2) (a.usize + 2) _ false T0 0 (ByteArray.emptyWithCapacity a.size) FStack.nil maxDepth.toUSize t hfu
        (by have := skipI_le (stage1 a) a.size 0; omega) (by rw [usize_zero_toNat]; omega) (by rw [usize_zero_toNat]; omega) (by rw [hmd]; unfold maxDepth; simp [fsLen]) hr
      rw [hk, usize_zero_toNat, hmd] at hW
      have h0 : Rel T0 0 (ByteArray.emptyWithCapacity a.size) ⟨ByteArray.empty, ByteArray.empty⟩ := ⟨by omega, by simp [ByteArray.size_empty], fun n hn => by omega, rfl⟩
      have hI := runW_sound a hs31 _ _ false T0 0 (ByteArray.emptyWithCapacity a.size) FStack.nil maxDepth ⟨ByteArray.empty, ByteArray.empty⟩ t
        (by omega) h0 trivial hW
      have h := parseTapeI_eq a
      unfold parseTapeI at h
      simp only [hsz, ↓reduceIte, hI] at h
      exact h
  · simp [hsz]

end LeanJsonProofs
