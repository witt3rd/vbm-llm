import LeanJsonProofs.ParseU
import LeanJsonProofs.NumFlag
import LeanJsonProofs.StrU
import LeanJsonProofs.Stack
/-! # Proof: `runC` (the structural mask carried as a cursor) answers only what `runU` answers (`runC_sound`)

`LeanJsonSimd/ParseSimd.lean`, `runC`. `CurInv m w b lo` says that the cursor `(w, b)` stands at the position `lo`: `b` is the part of word `w` of the mask that lies at or after `lo`, and no bit of the mask is set between `lo` and the word. Then the
position the cursor reports (`curPosU`) is `skipI m size lo` (`curPos_eq`), the cursor after consuming that bit stands at the position after it (`advK_spec`: `clearLowest`, then the next non-empty word, `nextWordU_spec`), and a cursor that stands at
`lo` also stands at any later `lo'` below its position (`curInv_skip`). `runC_sound` is then the induction of `runU_sound` with `skipU` replaced by these. -/
namespace LeanJsonProofs
open LeanJson VbmSimd VbmSimdProofs

/-- The cursor `(w, b)` stands at the position `lo`. -/
def CurInv (m : ByteArray) (w : Nat) (b : UInt64) (lo : Nat) : Prop :=
  (∀ i, i < 64 → bit b i = (bitPos (wordAt m) (64 * w + i) && decide (lo ≤ 64 * w + i))) ∧
  (∀ k, lo ≤ k → k < 64 * w → bitPos (wordAt m) k = false) ∧ lo ≤ 64 * (w + 1)

/-- The cursor is normal: a bit is left in the word, or there is no later word. -/
def CurNorm (m : ByteArray) (w : Nat) (b : UInt64) : Prop := b ≠ 0 ∨ wordCount m ≤ w + 1

/-- The mask array has room for `size` bits, a size that fits every `USize`, and no set bit at or past `size`. -/
def MaskOk (m : ByteArray) (size : Nat) : Prop :=
  size ≤ 64 * wordCount m ∧ wordCount m < 2 ^ 21 ∧ ∀ k, size ≤ k → k < 2 ^ 28 → bitPos (wordAt m) k = false

theorem wordAt_wsh (m : ByteArray) (w : USize) (hw : w.toNat < 2 ^ 28) : ld64 m (w <<< 3) = wordAt m w.toNat := by
  unfold wordAt
  congr 1
  apply USize.toNat_inj.mp
  have h2 : System.Platform.numBits = 32 ∨ System.Platform.numBits = 64 := System.Platform.numBits_eq
  have h4 : (3 : USize).toNat = 3 := USize.toNat_ofNat_of_lt_32 (by decide)
  rw [USize.toNat_shiftLeft, h4, usize_toNat_small _ (by omega)]
  rw [Nat.shiftLeft_eq]
  rcases h2 with h | h <;> rw [h] <;> simp only [Nat.reduceMod, Nat.reducePow] <;> omega

theorem wordCount_usize (m : ByteArray) (hm : m.size < 2 ^ 28) : ((m.usize + 7) >>> 3).toNat = wordCount m := by
  have hu : m.usize.toNat = m.size := usize_eq m (by omega)
  have h7 : (7 : USize).toNat = 7 := usize_lit 7 (by decide)
  have h3 : (3 : USize).toNat = 3 := usize_lit 3 (by decide)
  have hadd : (m.usize + 7).toNat = m.size + 7 := by
    rw [usize_add_lt _ _ (by rw [hu, h7]; have := usize_ge32; omega), hu, h7]
  rw [USize.toNat_shiftRight, hadd, h3, Nat.shiftRight_eq_div_pow]
  unfold wordCount
  have h2 : System.Platform.numBits = 32 ∨ System.Platform.numBits = 64 := System.Platform.numBits_eq
  rcases h2 with h | h <;> rw [h] <;> simp only [Nat.reduceMod, Nat.reducePow] <;> omega

/-- `nextWordU`: the first non-empty word after `w`, or `n`. -/
theorem nextWordU_spec (m : ByteArray) (n : USize) (hn : n.toNat < 2 ^ 28) : ∀ d (w : USize), n.toNat - w.toNat = d → w.toNat < n.toNat →
    w.toNat < (nextWordU m n w).toNat ∧ (nextWordU m n w).toNat ≤ n.toNat ∧ (∀ k, w.toNat < k → k < (nextWordU m n w).toNat → wordAt m k = 0) ∧
      ((nextWordU m n w).toNat = n.toNat ∨ wordAt m (nextWordU m n w).toNat ≠ 0) := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
    intro w hd hw
    have h1 : (w + 1).toNat = w.toNat + 1 := usize_add_lit w 1 (by decide) (by have := usize_ge32; omega)
    rw [nextWordU]
    by_cases hc : w < w + 1 ∧ w + 1 < n
    · have hlt : w.toNat + 1 < n.toNat := by have := USize.lt_iff_toNat_lt.1 hc.2; omega
      simp only [hc, and_self, ↓reduceDIte]
      rw [wordAt_wsh m (w + 1) (by omega)]
      by_cases hz : (wordAt m (w + 1).toNat != 0) = true
      · simp only [hz, ↓reduceIte]
        refine ⟨by omega, by omega, fun k hk hk' => by omega, Or.inr (by simpa using hz)⟩
      · simp only [hz, Bool.false_eq_true, ↓reduceIte]
        have hz' : wordAt m (w + 1).toNat = 0 := by simpa using hz
        obtain ⟨r1, r2, r3, r4⟩ := ih (n.toNat - (w + 1).toNat) (by omega) (w + 1) rfl (by omega)
        refine ⟨by omega, r2, fun k hk hk' => ?_, r4⟩
        by_cases hk1 : k = (w + 1).toNat
        · rw [hk1]; exact hz'
        · exact r3 k (by omega) hk'
    · have hnn : ¬ (w < w + 1 ∧ w + 1 < n) := hc
      simp only [hnn, ↓reduceDIte]
      have hle : ¬ (w.toNat + 1 < n.toNat) := fun h => hc ⟨by rw [USize.lt_iff_toNat_lt, h1]; omega, by rw [USize.lt_iff_toNat_lt, h1]; exact h⟩
      refine ⟨by omega, Nat.le_refl _, fun k hk hk' => by omega, Or.inl trivial⟩

theorem wsh6 (w : USize) (hw : w.toNat < 2 ^ 26) : (w <<< 6).toNat = 64 * w.toNat := by
  have h2 : System.Platform.numBits = 32 ∨ System.Platform.numBits = 64 := System.Platform.numBits_eq
  have h6 : (6 : USize).toNat = 6 := USize.toNat_ofNat_of_lt_32 (by decide)
  rw [USize.toNat_shiftLeft, h6, Nat.shiftLeft_eq]
  rcases h2 with h | h <;> rw [h] <;> simp only [Nat.reduceMod, Nat.reducePow] <;> omega

theorem bit_zero (i : Nat) : bit (0 : UInt64) i = false := by simp [bit]

/-- What a normal cursor with a bit left says: the lowest bit, `ctz b`, is the first set bit of the mask at or after `lo`. -/
theorem curInv_ne (m : ByteArray) (w : Nat) (b : UInt64) (lo : Nat) (hc : CurInv m w b lo) (hb : b ≠ 0) :
    (ctz b).toNat < 64 ∧ bitPos (wordAt m) (64 * w + (ctz b).toNat) = true ∧ lo ≤ 64 * w + (ctz b).toNat ∧
      ∀ k, lo ≤ k → k < 64 * w + (ctz b).toNat → bitPos (wordAt m) k = false := by
  obtain ⟨h1, h2, h3⟩ := hc
  obtain ⟨hlt, hset, hlow⟩ := ctzModel_spec b hb
  have hc : (ctz b).toNat = (ctzModel b).toNat := rfl
  rw [hc]
  have hs := h1 _ hlt
  rw [hset] at hs
  have hs' : bitPos (wordAt m) (64 * w + (ctzModel b).toNat) = true ∧ lo ≤ 64 * w + (ctzModel b).toNat := by simpa using hs.symm
  refine ⟨hlt, hs'.1, hs'.2, fun k hk hk' => ?_⟩
  by_cases hk2 : k < 64 * w
  · exact h2 k hk hk2
  · have := h1 (k - 64 * w) (by omega)
    rw [hlow (k - 64 * w) (by omega), show 64 * w + (k - 64 * w) = k by omega] at this
    have hd : decide (lo ≤ k) = true := by simpa using hk
    rw [hd] at this
    simpa using this.symm

/-- A cursor with a bit left is on a word that exists. -/
theorem curInv_lt (m : ByteArray) (w : Nat) (b : UInt64) (lo : Nat) (hc : CurInv m w b lo) (hb : b ≠ 0) (hw : w < 2 ^ 28) : w < wordCount m := by
  obtain ⟨-, hs, -⟩ := curInv_ne m w b lo hc hb
  refine Classical.byContradiction fun hn => ?_
  have h0 := wordAt_ge m w hn hw
  unfold bitPos at hs
  rw [show (64 * w + (ctz b).toNat) / 64 = w by have := (curInv_ne m w b lo hc hb).1; omega, h0] at hs
  simp [bit] at hs

/-- The position the cursor reports is the first structural position at or after `lo`. -/
theorem curPos_eq (a m : ByteArray) (hM : MaskOk m a.size) (hs : a.size < 2 ^ 26) (w : USize) (b : UInt64) (lo : Nat) (hw : w.toNat ≤ wordCount m)
    (hc : CurInv m w.toNat b lo) (hn : CurNorm m w.toNat b) : (curPosU a.usize w b).toNat = skipI m a.size lo := by
  obtain ⟨hM1, hM2, hM3⟩ := hM
  have hu := usize_eq a (by omega)
  have hw28 : w.toNat < 2 ^ 26 := by omega
  unfold curPosU skipI
  by_cases hb : b = 0
  · subst hb
    have hn' : wordCount m ≤ w.toNat + 1 := by rcases hn with h | h; exact absurd rfl h; exact h
    simp only [beq_self_eq_true, ↓reduceIte, hu]
    have hge : a.size ≤ nextSet m lo := by
      by_cases hl : lo ≤ 64 * wordCount m
      · obtain ⟨n1, n2, n3, n4⟩ := nextSet_spec m lo hl
        generalize nextSet m lo = p at n1 n2 n3 n4 ⊢
        refine Classical.byContradiction fun hlt => ?_
        rcases n4 with h4 | h4
        · omega
        · by_cases hp : p < 64 * w.toNat
          · have := hc.2.1 _ n1 hp
            rw [this] at h4; exact absurd h4 (by simp)
          · have hi := hc.1 (p - 64 * w.toNat) (by omega)
            rw [bit_zero, show 64 * w.toNat + (p - 64 * w.toNat) = p by omega, h4] at hi
            have hd : decide (lo ≤ p) = true := by simpa using n1
            rw [hd] at hi
            simp at hi
      · have : ¬ lo / 64 < wordCount m := by omega
        unfold nextSet
        simp only [this, ↓reduceIte]
        omega
    split <;> omega
  · have hbn : (b == 0) = false := by simpa using hb
    simp only [hbn, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨c1, c2, c3, c4⟩ := curInv_ne m w.toNat b lo hc hb
    have hwl := curInv_lt m w.toNat b lo hc hb (by omega)
    have hl : lo ≤ 64 * wordCount m := by omega
    obtain ⟨n1, n2, n3, n4⟩ := nextSet_spec m lo hl
    have hp : nextSet m lo = 64 * w.toNat + (ctz b).toNat := by
      generalize nextSet m lo = p at n1 n2 n3 n4 ⊢
      by_cases h1 : p ≤ 64 * w.toNat + (ctz b).toNat
      · by_cases h2 : p < 64 * w.toNat + (ctz b).toNat
        · exfalso
          rcases n4 with h4 | h4
          · omega
          · rw [c4 p n1 h2] at h4; exact absurd h4 (by simp)
        · omega
      · exfalso
        have := n3 _ c3 (by omega)
        rw [c2] at this; exact absurd this (by simp)
    rw [hp]
    have hlt : 64 * w.toNat + (ctz b).toNat < a.size := by
      refine Classical.byContradiction fun hge => ?_
      have := hM3 (64 * w.toNat + (ctz b).toNat) (by omega) (by omega)
      rw [c2] at this; exact absurd this (by simp)
    have hs6 := wsh6 w hw28
    have hct := ctz_toUSize b hb
    rw [usize_add_lt _ _ (by rw [hs6, hct]; have := usize_ge32; omega), hs6, hct]
    simp only [hlt, ↓reduceIte]

theorem bitPos_word (m : ByteArray) (r i : Nat) (hi : i < 64) : bitPos (wordAt m) (64 * r + i) = bit (wordAt m r) i := by
  unfold bitPos
  rw [show (64 * r + i) / 64 = r by omega, show (64 * r + i) % 64 = i by omega]

/-- The cursor after consuming the lowest bit: `clearLowest`, then the next non-empty word. -/
theorem advK_spec (a m : ByteArray) (hM : MaskOk m a.size) (w : USize) (b : UInt64) (lo : Nat) (hw : w.toNat ≤ wordCount m)
    (hc : CurInv m w.toNat b lo) (hb : b ≠ 0) :
    ∃ (w1 : USize) (b1 : UInt64), (∀ (β : Type) (k : USize → UInt64 → USize → β), advK m a.usize w b k = k w1 b1 (curPosU a.usize w1 b1)) ∧
      CurInv m w1.toNat b1 (64 * w.toNat + (ctz b).toNat + 1) ∧ CurNorm m w1.toNat b1 ∧ w1.toNat ≤ wordCount m := by
  obtain ⟨hM1, hM2, hM3⟩ := hM
  have hwl := curInv_lt m w.toNat b lo hc hb (by omega)
  obtain ⟨c1, c2, c3, c4⟩ := curInv_ne m w.toNat b lo hc hb
  obtain ⟨h1, h2, h3⟩ := hc
  have hcl : ∀ i, i < 64 → bit (clearLowest b) i = (decide ((ctz b).toNat < i) && bit b i) := by
    intro i hi
    apply Bool.eq_iff_iff.mpr
    rw [clearLowest_bit b i hi]
    obtain ⟨hlt, hset, hlow⟩ := ctzModel_spec b hb
    have hcz : (ctz b).toNat = (ctzModel b).toNat := rfl
    rw [hcz]
    constructor
    · rintro ⟨hbi, j, hj, hbj⟩
      have : (ctzModel b).toNat ≤ j := by
        refine Classical.byContradiction fun h => ?_
        have := hlow j (by omega)
        rw [this] at hbj; exact absurd hbj (by simp)
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨by omega, hbi⟩
    · intro h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨h.2, (ctzModel b).toNat, h.1, hset⟩
  by_cases hz : (clearLowest b != 0) = true
  · have hne : clearLowest b ≠ 0 := by simpa using hz
    have hbe : (clearLowest b == 0) = false := by simpa using hne
    refine ⟨w, clearLowest b, fun β k => ?_, ⟨?_, ?_, ?_⟩, Or.inl hne, hw⟩
    · unfold advK
      simp only [hz, ↓reduceIte, curPosU, hbe, Bool.false_eq_true]
    · intro i hi
      rw [hcl i hi, h1 i hi]
      by_cases hci : (ctz b).toNat < i
      · have hd1 : decide ((ctz b).toNat < i) = true := by simpa using hci
        have hd2 : decide (lo ≤ 64 * w.toNat + i) = true := by simp; omega
        have hd3 : decide (64 * w.toNat + (ctz b).toNat + 1 ≤ 64 * w.toNat + i) = true := by simp; omega
        rw [hd1, hd2, hd3]; simp
      · have hd1 : decide ((ctz b).toNat < i) = false := by simpa using hci
        have hd3 : decide (64 * w.toNat + (ctz b).toNat + 1 ≤ 64 * w.toNat + i) = false := by simp; omega
        rw [hd1, hd3]; simp
    · intro k hk hk'
      exact h2 k (by omega) hk'
    · omega
  · have hz0 : clearLowest b = 0 := by simpa using hz
    have hmsz : m.size < 2 ^ 28 := by unfold wordCount at hM2; omega
    have hn := wordCount_usize m hmsz
    obtain ⟨r1, r2, r3, r4⟩ := nextWordU_spec m ((m.usize + 7) >>> 3) (by rw [hn]; omega) _ w rfl (by rw [hn]; omega)
    rw [hn] at r2 r4
    generalize hr : nextWordU m ((m.usize + 7) >>> 3) w = w1 at r1 r2 r3 r4
    have hwsh := wordAt_wsh m w1 (by omega)
    refine ⟨w1, ld64 m (w1 <<< 3), fun β k => ?_, ⟨?_, ?_, ?_⟩, ?_, r2⟩
    · unfold advK
      simp only [hz, Bool.false_eq_true, ↓reduceIte, hr]
    · intro i hi
      rw [hwsh, bitPos_word m w1.toNat i hi]
      have hd : decide (64 * w.toNat + (ctz b).toNat + 1 ≤ 64 * w1.toNat + i) = true := by simp; omega
      rw [hd]; simp
    · intro k hk hk'
      by_cases hk2 : k < 64 * (w.toNat + 1)
      · have hi := hcl (k - 64 * w.toNat) (by omega)
        rw [hz0, bit_zero] at hi
        have hbk := h1 (k - 64 * w.toNat) (by omega)
        have hdc : decide ((ctz b).toNat < k - 64 * w.toNat) = true := by simp; omega
        rw [hdc] at hi
        have hbb : bit b (k - 64 * w.toNat) = false := by simpa using hi.symm
        rw [hbb, show 64 * w.toNat + (k - 64 * w.toNat) = k by omega] at hbk
        have hd : decide (lo ≤ k) = true := by simp; omega
        rw [hd] at hbk
        simpa using hbk.symm
      · have := r3 (k / 64) (by omega) (by omega)
        unfold bitPos
        rw [this]
        exact bit_zero _
    · omega
    · rcases r4 with h | h
      · exact Or.inr (by omega)
      · rw [hwsh]; exact Or.inl h

/-- A cursor that stands at `lo` also stands at a later `lo'` when no bit of the mask lies between them (and `lo'` is within the word). -/
theorem curInv_skip (m : ByteArray) (w : Nat) (b : UInt64) (lo lo' : Nat) (hc : CurInv m w b lo) (h1 : lo ≤ lo') (h2 : ∀ k, lo ≤ k → k < lo' → bitPos (wordAt m) k = false)
    (h3 : lo' ≤ 64 * (w + 1)) : CurInv m w b lo' := by
  obtain ⟨c1, c2, c3⟩ := hc
  refine ⟨fun i hi => ?_, fun k hk hk' => c2 k (by omega) hk', h3⟩
  rw [c1 i hi]
  by_cases hl : lo' ≤ 64 * w + i
  · have e1 : decide (lo ≤ 64 * w + i) = true := by simp; omega
    have e2 : decide (lo' ≤ 64 * w + i) = true := by simp; omega
    rw [e1, e2]
  · have e2 : decide (lo' ≤ 64 * w + i) = false := by simp; omega
    by_cases hl2 : lo ≤ 64 * w + i
    · have := h2 (64 * w + i) hl2 (by omega)
      rw [this, e2]; simp
    · have e1 : decide (lo ≤ 64 * w + i) = false := by simp; omega
      rw [e1, e2]

/-- The cursor at the start. -/
theorem startK_spec (a m : ByteArray) (hM : MaskOk m a.size) :
    ∃ (w0 : USize) (b0 : UInt64), (∀ (β : Type) (k : USize → UInt64 → USize → β), startK m a.usize k = k w0 b0 (curPosU a.usize w0 b0)) ∧
      CurInv m w0.toNat b0 0 ∧ CurNorm m w0.toNat b0 ∧ w0.toNat ≤ wordCount m := by
  obtain ⟨hM1, hM2, hM3⟩ := hM
  have h0 : ld64 m 0 = wordAt m 0 := rfl
  have hz0 : (0 : USize).toNat = 0 := usize_lit 0 (by decide)
  have hsh : ld64 m ((0 : USize) <<< 3) = ld64 m 0 := by rw [wordAt_wsh m 0 (by rw [hz0]; omega), hz0, h0]
  by_cases hz : (ld64 m 0 != 0) = true
  · refine ⟨0, ld64 m 0, fun β k => ?_, ⟨?_, ?_, ?_⟩, Or.inl (by simpa using hz), by rw [hz0]; omega⟩
    · unfold startK
      simp only [hz, ↓reduceIte]
    · intro i hi
      have := bitPos_word m 0 i hi
      simp only [hz0, h0, Nat.mul_zero, Nat.zero_add, Nat.zero_le, decide_true, Bool.and_true] at this ⊢
      exact this.symm
    · intro k hk hk'; rw [hz0] at hk'; omega
    · rw [hz0]; omega
  · have hz' : ld64 m 0 = 0 := by simpa using hz
    have hw0 : wordAt m 0 = 0 := by rw [← h0]; exact hz'
    have hmsz : m.size < 2 ^ 28 := by unfold wordCount at hM2; omega
    have hn := wordCount_usize m hmsz
    by_cases hn0 : wordCount m = 0
    · have hnu : ((m.usize + 7) >>> 3) = 0 := by apply USize.toNat_inj.mp; rw [hn, hn0, hz0]
      have hr : nextWordU m ((m.usize + 7) >>> 3) 0 = 0 := by
        rw [nextWordU]
        simp only [hnu]
        simp
      refine ⟨0, ld64 m 0, fun β k => ?_, ⟨?_, ?_, ?_⟩, Or.inr (by rw [hz0]; omega), by rw [hz0]; omega⟩
      · unfold startK
        simp only [hz, Bool.false_eq_true, ↓reduceIte, hr, hsh]
      · intro i hi
        have := bitPos_word m 0 i hi
        simp only [hz0, hz', hw0, Nat.mul_zero, Nat.zero_add, Nat.zero_le, decide_true, Bool.and_true] at this ⊢
        rw [this]
      · intro k hk hk'; rw [hz0] at hk'; omega
      · rw [hz0]; omega
    · obtain ⟨r1, r2, r3, r4⟩ := nextWordU_spec m ((m.usize + 7) >>> 3) (by rw [hn]; omega) _ 0 rfl (by rw [hn, hz0]; omega)
      rw [hn] at r2 r4
      rw [hz0] at r1 r3
      generalize hr : nextWordU m ((m.usize + 7) >>> 3) 0 = w1 at r1 r2 r3 r4
      have hwsh := wordAt_wsh m w1 (by omega)
      refine ⟨w1, ld64 m (w1 <<< 3), fun β k => ?_, ⟨?_, ?_, ?_⟩, ?_, r2⟩
      · unfold startK
        simp only [hz, Bool.false_eq_true, ↓reduceIte, hr]
      · intro i hi
        rw [hwsh, bitPos_word m w1.toNat i hi]
        simp
      · intro k hk hk'
        by_cases hk2 : k < 64
        · unfold bitPos
          rw [show k / 64 = 0 by omega, hw0]
          exact bit_zero _
        · have := r3 (k / 64) (by omega) (by omega)
          unfold bitPos
          rw [this]
          exact bit_zero _
      · omega
      · rcases r4 with h | h
        · exact Or.inr (by omega)
        · rw [hwsh]; exact Or.inl h

/-! ## The relation of a cursor to the position of `runU` -/

/-- The cursor `(w, b)`, which reports the position `i`, stands at `lo`. -/
def CRel (a m : ByteArray) (w : USize) (b : UInt64) (i : USize) (lo : Nat) : Prop :=
  CurInv m w.toNat b lo ∧ CurNorm m w.toNat b ∧ w.toNat ≤ wordCount m ∧ i = curPosU a.usize w b

theorem curPos_ne (a m : ByteArray) (hM : MaskOk m a.size) (w : USize) (b : UInt64) (hw : w.toNat ≤ wordCount m) (hb : b ≠ 0) :
    (curPosU a.usize w b).toNat = 64 * w.toNat + (ctz b).toNat := by
  obtain ⟨hM1, hM2, hM3⟩ := hM
  have hbn : (b == 0) = false := by simpa using hb
  unfold curPosU
  simp only [hbn, Bool.false_eq_true, ↓reduceIte]
  have hs6 := wsh6 w (by omega)
  have hct := ctz_toUSize b hb
  rw [usize_add_lt _ _ (by rw [hs6, hct]; have := usize_ge32; have := (ctzModel_spec b hb).1; have : (ctz b).toNat = (ctzModel b).toNat := rfl; omega), hs6, hct]

theorem curPos_zero (a : ByteArray) (w : USize) : curPosU a.usize w 0 = a.usize := by
  unfold curPosU
  simp

/-- A cursor that reports `i` and stands at `lo` (within the input): `i` is the first structural position at or after `lo`, and the cursor stands at `i` too. -/
theorem rel_settle (a m : ByteArray) (hM : MaskOk m a.size) (hs : a.size < 2 ^ 26) (w : USize) (b : UInt64) (i : USize) (lo : Nat) (hr : CRel a m w b i lo) (hlo : lo ≤ a.size) :
    i.toNat = skipI m a.size lo ∧ lo ≤ i.toNat ∧ i.toNat ≤ a.size ∧ (∀ k, lo ≤ k → k < i.toNat → bitPos (wordAt m) k = false) ∧ CRel a m w b i i.toNat ∧
      (i.toNat < a.size → b ≠ 0 ∧ i.toNat = 64 * w.toNat + (ctz b).toNat) := by
  obtain ⟨hc, hn, hw, hi⟩ := hr
  have hM' := hM
  obtain ⟨hM1, hM2, hM3⟩ := hM
  have hpos := curPos_eq a m hM' hs w b lo hw hc hn
  rw [← hi] at hpos
  have hu := usize_eq a (by omega)
  have hl : lo ≤ 64 * wordCount m := by omega
  obtain ⟨n1, n2, n3, n4⟩ := nextSet_spec m lo hl
  have hsk : lo ≤ skipI m a.size lo ∧ skipI m a.size lo ≤ a.size ∧ ∀ k, lo ≤ k → k < skipI m a.size lo → bitPos (wordAt m) k = false := by
    unfold skipI
    simp only []
    by_cases hp : nextSet m lo < a.size
    · simp only [hp, ↓reduceIte]
      exact ⟨n1, by omega, fun k hk hk' => n3 k hk hk'⟩
    · simp only [hp, ↓reduceIte]
      exact ⟨hlo, Nat.le_refl _, fun k hk hk' => n3 k hk (by omega)⟩
  rw [← hpos] at hsk
  have hb0 : b = 0 → i.toNat = a.size := by
    intro hb; rw [hi, hb, curPos_zero, hu]
  have hb1 : b ≠ 0 → i.toNat = 64 * w.toNat + (ctz b).toNat := by
    intro hb; rw [hi]; exact curPos_ne a m ⟨hM1, hM2, hM3⟩ w b hw hb
  have hle : i.toNat ≤ 64 * (w.toNat + 1) := by
    by_cases hb : b = 0
    · have := hb0 hb
      rcases hn with h | h
      · exact absurd hb h
      · omega
    · have := hb1 hb; have := (ctzModel_spec b hb).1; have : (ctz b).toNat = (ctzModel b).toNat := rfl; omega
  refine ⟨hpos, hsk.1, hsk.2.1, hsk.2.2, ⟨curInv_skip m w.toNat b lo _ hc hsk.1 hsk.2.2 hle, hn, hw, hi⟩, fun hlt => ?_⟩
  by_cases hb : b = 0
  · have := hb0 hb; omega
  · exact ⟨hb, hb1 hb⟩

/-- A cursor that stands at `lo` and reports `i` stands at every position from `lo` up to `i`. -/
theorem rel_mono (a m : ByteArray) (hM : MaskOk m a.size) (hs : a.size < 2 ^ 26) (w : USize) (b : UInt64) (i : USize) (lo lo' : Nat) (hr : CRel a m w b i lo) (hlo : lo ≤ a.size)
    (h1 : lo ≤ lo') (h2 : lo' ≤ i.toNat) : CRel a m w b i lo' := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := rel_settle a m hM hs w b i lo hr hlo
  obtain ⟨hc, hn, hw, hi⟩ := hr
  have h3 := e5.1.2.2
  exact ⟨curInv_skip m w.toNat b lo lo' hc h1 (fun k hk hk' => e4 k hk (by omega)) (by omega), hn, hw, hi⟩

/-- Consuming the structural byte at `i`, at which the cursor stands and which lies inside the input: the next cursor reports the next structural position, which is `skipI` of the position after `i`. -/
theorem adv_full (a m : ByteArray) (hM : MaskOk m a.size) (hs : a.size < 2 ^ 26) (w : USize) (b : UInt64) (i : USize) (hr : CRel a m w b i i.toNat) (hlt : i.toNat < a.size) :
    ∃ (w1 : USize) (b1 : UInt64), (∀ (β : Type) (k : USize → UInt64 → USize → β), advK m a.usize w b k = k w1 b1 (curPosU a.usize w1 b1)) ∧
      (curPosU a.usize w1 b1).toNat = skipI m a.size (i.toNat + 1) ∧ i.toNat + 1 ≤ (curPosU a.usize w1 b1).toNat ∧ (curPosU a.usize w1 b1).toNat ≤ a.size ∧
      CRel a m w1 b1 (curPosU a.usize w1 b1) (i.toNat + 1) ∧ CRel a m w1 b1 (curPosU a.usize w1 b1) (curPosU a.usize w1 b1).toNat := by
  obtain ⟨e1, e2, e3, e4, e5, hb⟩ := rel_settle a m hM hs w b i i.toNat hr (by omega)
  have hrr := hr
  obtain ⟨hc, hn, hw, hi⟩ := hr
  obtain ⟨w1, b1, hk, c1, c2, c3⟩ := advK_spec a m hM w b i.toNat hw hc (hb hlt).1
  rw [← (hb hlt).2] at c1
  have hr1 : CRel a m w1 b1 (curPosU a.usize w1 b1) (i.toNat + 1) := ⟨c1, c2, c3, rfl⟩
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := rel_settle a m hM hs w1 b1 _ (i.toNat + 1) hr1 (by omega)
  exact ⟨w1, b1, hk, f1, f2, f3, hr1, f5⟩

theorem maskOk_stage1 (a : ByteArray) (hs : a.size < 2 ^ 26) : MaskOk (stage1 a) a.size := by
  obtain ⟨hsz, hbit⟩ := stage1_spec a (by omega)
  have hwc : wordCount (stage1 a) = (a.size + 63) / 64 := by unfold wordCount; rw [hsz]; omega
  refine ⟨by omega, by omega, fun k hk hk2 => ?_⟩
  by_cases hkn : k < 64 * wordCount (stage1 a)
  · have hl : wordAt (stage1 a) (k / 64) = ld64Model (stage1 a) (8 * (k / 64)) := ld64_toUSize _ _ (by omega)
    unfold bitPos
    rw [hl, hbit (k / 64) (by omega) (k % 64) (by omega)]
    have : decide (64 * (k / 64) + k % 64 < a.size) = false := by simp; omega
    rw [this]; simp
  · unfold bitPos
    rw [wordAt_ge _ (k / 64) (by omega) (by omega)]
    exact bit_zero _

/-- `skipU` is the position the cursor reports. -/
theorem skipU_cur (a m : ByteArray) (hM : MaskOk m a.size) (hs : a.size < 2 ^ 26) (w : USize) (b : UInt64) (i : USize) (lo : Nat) (hr : CRel a m w b i lo) (hlo : lo ≤ a.size)
    (x : USize) (hx : x.toNat = lo) : skipU m a.usize x = i := by
  obtain ⟨e1, -⟩ := rel_settle a m hM hs w b i lo hr hlo
  apply USize.toNat_inj.mp
  rw [e1, skipU_eq m a (by omega) x (by omega), hx]

theorem advK_none {β : Type} (m : ByteArray) (size : USize) (w : USize) (b : UInt64) (k : USize → UInt64 → USize → Option β) (hk : ∀ w b i, k w b i = none) :
    advK m size w b k = none := by
  unfold advK
  by_cases h1 : (clearLowest b != 0) = true <;> simp [h1, hk]

theorem strU_C (m a : ByteArray) (hs : a.size < 2 ^ 26) (i : USize) (text : ByteArray) : strU m a i text = strC a i (skipU m a.usize (i + 1)) text := by
  have e : ∀ j b, strBytesV a j b = strBytesW a j b := fun j b => strBytesV_eq a hs _ j b rfl
  unfold strU strC
  simp only [e]
  rfl

theorem strC_spec (a : ByteArray) (hs : a.size < 2 ^ 26) (i r : USize) (text t' : ByteArray) (j : USize) (h : strC a i r text = some (t', j)) :
    i.toNat < a.size ∧ r.toNat < a.size ∧ j = r + 1 ∧ j.toNat = r.toNat + 1 := by
  have hs32 : a.size < 4294967296 := by omega
  unfold strC at h
  by_cases hq : byteIsU a i 0x22 = true
  · have hq0 := hq
    rw [byteIsU_eq a hs32] at hq
    have hi := (byteIs_spec a _ _ hq).1
    have hi1 : (i + 1).toNat = i.toNat + 1 := add_one a i (by omega) hs
    simp only [hq0, ↓reduceIte] at h
    rw [hi1] at h
    by_cases hc : (i + 1 + plainOffU a (i + 1) 0 == r && byteIsU a r 0x22) = true
    · simp only [hc, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, hj⟩ := h
      have hr : byteIsU a r 0x22 = true := by simp only [Bool.and_eq_true] at hc; exact hc.2
      rw [byteIsU_eq a hs32] at hr
      have hr' := (byteIs_spec a _ _ hr).1
      exact ⟨hi, hr', hj.symm, by rw [← hj]; exact add_one a r (by omega) hs⟩
    · simp only [hc, Bool.false_eq_true, ↓reduceIte] at h
      rw [strBytesV_eq a hs _ _ _ rfl] at h
      cases hb : strBytesW a (i.toNat + 1) text with
      | none => rw [hb] at h; simp at h
      | some tj =>
        obtain ⟨t, j'⟩ := tj
        rw [hb] at h
        simp only [] at h
        by_cases hj : (r.toNat == j' - 1) = true
        · simp only [hj, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨-, hjj⟩ := h
          have hj2 := beq_iff_eq.mp hj
          rw [strBytesW_eq a (by omega) _ _ _ rfl] at hb
          obtain ⟨e1, e2⟩ := strBytes_end a _ _ _ _ _ rfl hb
          have hr1 : r.toNat < a.size := by omega
          have hjt : j.toNat = r.toNat + 1 := by rw [← hjj, usize_toNat_small _ (by omega)]; omega
          refine ⟨hi, hr1, ?_, hjt⟩
          apply USize.toNat_inj.mp
          rw [hjt]; exact (add_one a r (by omega) hs).symm
        · simp [hj] at h
  · simp [hq] at h

theorem byteIsU_oob (a : ByteArray) (hs : a.size < 2 ^ 26) (i : USize) (hi : ¬ i.toNat < a.size) (c : UInt8) : byteIsU a i c = false := by
  have hs32 : a.size < 4294967296 := by omega
  rw [byteIsU_eq a hs32]
  unfold byteIs
  simp [hi]

theorem strC_oob (a : ByteArray) (hs : a.size < 2 ^ 26) (i r : USize) (text : ByteArray) (hi : ¬ i.toNat < a.size) : strC a i r text = none := by
  unfold strC
  simp [byteIsU_oob a hs i hi]

theorem scanNumU_adv (a : ByteArray) (hs : a.size < 2 ^ 26) (i : USize) (hi : i.toNat ≤ a.size) (hne : ¬ (scanNumU a i == 0) = true) :
    i.toNat < (scanNumU a i).toNat ∧ (scanNumU a i).toNat ≤ a.size := by
  have hs31 : a.size < 2 ^ 31 := by omega
  rcases scanNumU_eq a hs31 i hi with ⟨h0, ho⟩ | ⟨j, ho, hj, hp, hb⟩
  · exact absurd ((usize_beq_zero _).2 h0) hne
  · have hadv := scanNum_adv a i.toNat j (by rw [← scanNumW_eq a hs31]; exact ho)
    exact ⟨by omega, by omega⟩

theorem usize_add_k (a : ByteArray) (hs : a.size < 2 ^ 26) (i : USize) (k : Nat) (hk : k < 16) (hi : i.toNat ≤ a.size + 2) : (i + (OfNat.ofNat k : USize)).toNat = i.toNat + k :=
  usize_add_lit i k (by omega) (by have := usize_ge32; omega)

theorem runC_sound (a : ByteArray) (hsz : a.size < 2 ^ 26) :
    ∀ (f : Nat) (fu : USize) (w : USize) (b : UInt64) (i iU : USize) (ret : Bool) (tape : ByteArray) (tw : USize) (text : ByteArray) (fst : FStack) (stk : ByteArray) (sp : USize) (d : USize) (t : ByteArray),
      fu.toNat = f → iU.toNat ≤ a.size → tw.toNat + 4 * f ≤ 4 * a.size + 8 → tape.size ≤ 8 * tw.toNat + 4096 → d.toNat + fsLen fst ≤ 512 → SInv stk sp fst →
      CRel a (stage1 a) w b i iU.toNat → (ret = false → iU = i) →
      runC (stage1 a) fu a w b i ret tape tw text stk sp d = some t →
      runU (stage1 a) fu a iU ret tape tw text fst d = some t := by
  have hM := maskOk_stage1 a hsz
  have hs31 : a.size < 2 ^ 31 := by omega
  have hs32 : a.size < 4294967296 := by omega
  intro f
  induction f with
  | zero =>
    intro fu w b i iU ret tape tw text fst stk sp d t hf _ _ _ _ _ _ _ h
    rw [runC] at h
    have h0 : (fu == 0) = true := (usize_beq_zero fu).2 hf
    simp [h0] at h
  | succ f ih =>
    intro fu w b i iU ret tape tw text fst stk sp d t hf hi htw htape hd hS hr hiU h
    have hfu : ¬ (fu == 0) = true := fun h0 => by have := (usize_beq_zero fu).1 h0; omega
    have hf1 : (fu - 1).toNat = f := by
      have h3 : (1 : USize) ≤ fu := by rw [USize.le_iff_toNat_le, usize_lit 1 (by decide)]; omega
      rw [USize.toNat_sub_of_le fu 1 h3, usize_lit 1 (by decide)]; omega
    have pe3 : (tw + 2).toNat = tw.toNat + 2 := usize_add_lit tw 2 (by decide) (by have := usize_ge32; omega)
    have hdd : ∀ d' : USize, ¬ (d' == 0) = true → (d' - 1).toNat = d'.toNat - 1 := fun d' hd0 => by
      have : d'.toNat ≠ 0 := fun h0 => hd0 ((usize_beq_zero d').2 h0)
      rw [USize.toNat_sub_of_le d' 1 (by rw [USize.le_iff_toNat_le, usize_lit 1 (by decide)]; omega), usize_lit 1 (by decide)]
    rw [runC] at h
    simp only [hfu, Bool.false_eq_true, ↓reduceIte] at h
    rw [runU]
    simp only [hfu, Bool.false_eq_true, ↓reduceIte]
    cases ret with
    | false =>
      obtain rfl := hiU rfl
      simp only [] at h ⊢
      by_cases hlt : iU < a.usize
      · have hlt' : iU.toNat < a.size := (lt_usize_iff a hs32 iU).1 hlt
        have e : a.uget iU (ugetOk a iU hlt) = a[iU.toNat] := rfl
        simp only [hlt, ↓reduceDIte, e] at h ⊢
        obtain ⟨w1, b1, hk, hp1, hp2, hp3, hr1, hr1s⟩ := adv_full a (stage1 a) hM hsz w b iU hr hlt'
        have hi1 := add_one a iU (by omega) hsz
        have e1 : skipU (stage1 a) a.usize (iU + 1) = curPosU a.usize w1 b1 := by
          apply USize.toNat_inj.mp
          rw [skipU_eq (stage1 a) a hs31 _ (by rw [hi1]; omega), hi1, hp1]
        rw [e1]
        generalize curPosU a.usize w1 b1 = i1 at hk hp1 hp2 hp3 hr1 hr1s e1 ⊢
        by_cases h5b : (a[iU.toNat] == 0x5B) = true
        · simp only [h5b, ↓reduceIte] at h ⊢
          by_cases hd0 : (d == 0) = true
          · simp [hd0] at h
          · simp only [hd0, Bool.false_eq_true, ↓reduceIte] at h ⊢
            rw [hk] at h
            by_cases h5d : byteIsU a i1 0x5D = true
            · simp only [h5d, ↓reduceIte] at h ⊢
              have h5d' := h5d
              rw [byteIsU_eq a hs32] at h5d'
              have hlt1 : i1.toNat < a.size := (byteIs_spec a _ _ h5d').1
              obtain ⟨w2, b2, hk2, hq1, hq2, hq3, hr2, hr2s⟩ := adv_full a (stage1 a) hM hsz w1 b1 i1 hr1s hlt1
              rw [hk2] at h
              generalize curPosU a.usize w2 b2 = i2 at hk2 hq1 hq2 hq3 hr2 hr2s h
              obtain ⟨pe2, -, pe4⟩ := pnU a hsz tape tw (by omega) htape (hdrW 5 0) 2
              have hi2 := add_one a i1 (by omega) hsz
              exact ih (fu - 1) w2 b2 i2 (i1 + 1) true _ (tw + 2) text fst stk sp d t hf1 (by rw [hi2]; omega) (by rw [pe3]; omega) (by rw [pe2, pe3]; exact pe4) hd hS
                (by rw [hi2]; exact hr2) (fun h => by simp at h) h
            · simp only [h5d, Bool.false_eq_true, ↓reduceIte] at h ⊢
              obtain ⟨pe2, -, pe4⟩ := pnU a hsz tape tw (by omega) htape (hdrW 5 0) 0
              have hdpos : d.toNat ≠ 0 := fun h0 => hd0 ((usize_beq_zero d).2 h0)
              exact ih (fu - 1) w1 b1 i1 i1 false _ (tw + 2) text _ _ _ (d - 1) t hf1 hp3 (by rw [pe3]; omega) (by rw [pe2, pe3]; exact pe4)
                (by rw [hdd d hd0, fsLen_arr]; omega) (SInv_push_arr stk sp fst hS (by have := hS.1; omega) tw (by omega)) hr1s (fun _ => rfl) h
        · simp only [h5b, Bool.false_eq_true, ↓reduceIte] at h ⊢
          by_cases h7b : (a[iU.toNat] == 0x7B) = true
          · simp only [h7b, ↓reduceIte] at h ⊢
            by_cases hd0 : (d == 0) = true
            · simp [hd0] at h
            · simp only [hd0, Bool.false_eq_true, ↓reduceIte] at h ⊢
              have hdpos : d.toNat ≠ 0 := fun h0 => hd0 ((usize_beq_zero d).2 h0)
              rw [hk] at h
              by_cases h7d : byteIsU a i1 0x7D = true
              · simp only [h7d, ↓reduceIte] at h ⊢
                have h7d' := h7d
                rw [byteIsU_eq a hs32] at h7d'
                have hlt1 : i1.toNat < a.size := (byteIs_spec a _ _ h7d').1
                obtain ⟨w2, b2, hk2, hq1, hq2, hq3, hr2, hr2s⟩ := adv_full a (stage1 a) hM hsz w1 b1 i1 hr1s hlt1
                rw [hk2] at h
                generalize curPosU a.usize w2 b2 = i2 at hk2 hq1 hq2 hq3 hr2 hr2s h
                obtain ⟨pe2, -, pe4⟩ := pnU a hsz tape tw (by omega) htape (hdrW 6 0) 2
                have hi2 := add_one a i1 (by omega) hsz
                exact ih (fu - 1) w2 b2 i2 (i1 + 1) true _ (tw + 2) text fst stk sp d t hf1 (by rw [hi2]; omega) (by rw [pe3]; omega) (by rw [pe2, pe3]; exact pe4) hd hS
                  (by rw [hi2]; exact hr2) (fun h => by simp at h) h
              · simp only [h7d, Bool.false_eq_true, ↓reduceIte] at h ⊢
                obtain ⟨pe2, -, pe4⟩ := pnU a hsz tape tw (by omega) htape (hdrW 6 0) 0
                by_cases hlt1 : i1.toNat < a.size
                · obtain ⟨w2, b2, hk2, hq1, hq2, hq3, hr2, hr2s⟩ := adv_full a (stage1 a) hM hsz w1 b1 i1 hr1s hlt1
                  rw [hk2] at h
                  have hi2 := add_one a i1 (by omega) hsz
                  have e2 : skipU (stage1 a) a.usize (i1 + 1) = curPosU a.usize w2 b2 := by
                    apply USize.toNat_inj.mp
                    rw [skipU_eq (stage1 a) a hs31 _ (by rw [hi2]; omega), hi2, hq1]
                  generalize curPosU a.usize w2 b2 = i2 at hk2 hq1 hq2 hq3 hr2 hr2s h e2
                  rw [strU_C _ _ hsz, e2]
                  cases hsc : strC a i1 i2 text with
                  | none => rw [hsc] at h; simp at h
                  | some tj =>
                    obtain ⟨text', j⟩ := tj
                    rw [hsc] at h
                    simp only [] at h ⊢
                    obtain ⟨-, hr', hj, hjt⟩ := strC_spec a hsz i1 i2 text text' j hsc
                    obtain ⟨w3, b3, hk3, hs1, hs2, hs3, hr3, hr3s⟩ := adv_full a (stage1 a) hM hsz w2 b2 i2 hr2s hr'
                    rw [hk3] at h
                    have e3 : skipU (stage1 a) a.usize j = curPosU a.usize w3 b3 := by
                      apply USize.toNat_inj.mp
                      rw [skipU_eq (stage1 a) a hs31 _ (by omega), hjt, hs1]
                    rw [e3]
                    generalize curPosU a.usize w3 b3 = i3 at hk3 hs1 hs2 hs3 hr3 hr3s h e3
                    by_cases hc3 : byteIsU a i3 0x3A = true
                    · simp only [hc3, ↓reduceIte] at h ⊢
                      have hc3' := hc3
                      rw [byteIsU_eq a hs32] at hc3'
                      have hlt3 : i3.toNat < a.size := (byteIs_spec a _ _ hc3').1
                      obtain ⟨w4, b4, hk4, hu1, hu2, hu3, hr4, hr4s⟩ := adv_full a (stage1 a) hM hsz w3 b3 i3 hr3s hlt3
                      rw [hk4] at h
                      have hi3 := add_one a i3 (by omega) hsz
                      have e4 : skipU (stage1 a) a.usize (i3 + 1) = curPosU a.usize w4 b4 := by
                        apply USize.toNat_inj.mp
                        rw [skipU_eq (stage1 a) a hs31 _ (by rw [hi3]; omega), hi3, hu1]
                      rw [e4]
                      generalize curPosU a.usize w4 b4 = i4 at hk4 hu1 hu2 hu3 hr4 hr4s h e4
                      obtain ⟨pf2, pf3, pf4⟩ := pnU a hsz (putNodeU tape tw (hdrW 6 0) 0) (tw + 2) (by omega) (by rw [pe2, pe3]; exact pe4)
                        (hdrW 4 (text'.size - text.size)) (UInt64.ofNat text.size)
                      have pe5 : (tw + 4).toNat = tw.toNat + 4 := usize_add_lit tw 4 (by decide) (by have := usize_ge32; omega)
                      exact ih (fu - 1) w4 b4 i4 i4 false _ (tw + 4) text' _ _ _ (d - 1) t hf1 hu3 (by rw [pe5]; omega)
                        (by rw [pf2, pe2, pe5, pe3]; rw [pe2, pe3] at pf4; omega) (by rw [hdd d hd0, fsLen_obj]; omega)
                        (SInv_push_obj stk sp fst hS (by have := hS.1; omega) tw (by omega)) hr4s (fun _ => rfl) h
                    · simp only [hc3, Bool.false_eq_true, ↓reduceIte] at h
                      simp at h
                · exfalso
                  rw [advK_none] at h
                  · simp at h
                  · intro w2 b2 i2
                    simp only [strC_oob a hsz i1 i2 text hlt1]
          · simp only [h7b, Bool.false_eq_true, ↓reduceIte] at h ⊢
            by_cases h22 : (a[iU.toNat] == 0x22) = true
            · simp only [h22, ↓reduceIte] at h ⊢
              rw [hk] at h
              rw [strU_C _ _ hsz, e1]
              cases hsc : strC a iU i1 text with
              | none => rw [hsc] at h; simp at h
              | some tj =>
                obtain ⟨text', j⟩ := tj
                rw [hsc] at h
                simp only [] at h ⊢
                obtain ⟨-, hr', hj, hjt⟩ := strC_spec a hsz iU i1 text text' j hsc
                obtain ⟨w2, b2, hk2, hq1, hq2, hq3, hr2, hr2s⟩ := adv_full a (stage1 a) hM hsz w1 b1 i1 hr1s hr'
                rw [hk2] at h
                generalize curPosU a.usize w2 b2 = i2 at hk2 hq1 hq2 hq3 hr2 hr2s h
                obtain ⟨pe2, -, pe4⟩ := pnU a hsz tape tw (by omega) htape (hdrW 4 (text'.size - text.size)) (UInt64.ofNat text.size)
                exact ih (fu - 1) w2 b2 i2 j true _ (tw + 2) text' fst stk sp d t hf1 (by omega) (by rw [pe3]; omega) (by rw [pe2, pe3]; exact pe4) hd hS
                  (by rw [hjt]; exact hr2) (fun h => by simp at h) h
            · simp only [h22, Bool.false_eq_true, ↓reduceIte] at h ⊢
              have hi2 := usize_add_k a hsz iU 2 (by omega) (by omega)
              have hi3 := usize_add_k a hsz iU 3 (by omega) (by omega)
              have hi4 := usize_add_k a hsz iU 4 (by omega) (by omega)
              have hi5 := usize_add_k a hsz iU 5 (by omega) (by omega)
              by_cases h6e : (a[iU.toNat] == 0x6E) = true
              · simp only [h6e, ↓reduceIte] at h ⊢
                by_cases hc3 : (byteIsU a (iU + 1) 0x75 && byteIsU a (iU + 2) 0x6C && byteIsU a (iU + 3) 0x6C) = true
                · simp only [hc3, ↓reduceIte] at h ⊢
                  by_cases hdl : delimAtU a (iU + 4) = true
                  · simp only [hdl, ↓reduceIte] at h ⊢
                    rw [hk] at h
                    have hlt3 : iU.toNat + 3 < a.size := by
                      simp only [Bool.and_eq_true] at hc3
                      have := hc3.2
                      rw [byteIsU_eq a hs32, hi3] at this
                      exact (byteIs_spec a _ _ this).1
                    by_cases hlt4 : i1 < iU + 4
                    · simp [hlt4] at h
                    · simp only [hlt4, ↓reduceIte] at h
                      have hge : ¬ (i1.toNat < (iU + 4).toNat) := fun h' => hlt4 (USize.lt_iff_toNat_lt.2 h')
                      obtain ⟨pe2, -, pe4⟩ := pnU a hsz tape tw (by omega) htape (hdrW 0 0) 0
                      exact ih (fu - 1) w1 b1 i1 (iU + 4) true _ (tw + 2) text fst stk sp d t hf1 (by rw [hi4]; omega) (by rw [pe3]; omega) (by rw [pe2, pe3]; exact pe4) hd hS
                        (by rw [hi4]; exact rel_mono a (stage1 a) hM hsz w1 b1 i1 _ _ hr1 (by omega) (by omega) (by rw [hi4] at hge; omega)) (fun h => by simp at h) h
                  · simp [hdl] at h
                · simp [hc3] at h
              · simp only [h6e, Bool.false_eq_true, ↓reduceIte] at h ⊢
                by_cases h74 : (a[iU.toNat] == 0x74) = true
                · simp only [h74, ↓reduceIte] at h ⊢
                  by_cases hc3 : (byteIsU a (iU + 1) 0x72 && byteIsU a (iU + 2) 0x75 && byteIsU a (iU + 3) 0x65) = true
                  · simp only [hc3, ↓reduceIte] at h ⊢
                    by_cases hdl : delimAtU a (iU + 4) = true
                    · simp only [hdl, ↓reduceIte] at h ⊢
                      rw [hk] at h
                      have hlt3 : iU.toNat + 3 < a.size := by
                        simp only [Bool.and_eq_true] at hc3
                        have := hc3.2
                        rw [byteIsU_eq a hs32, hi3] at this
                        exact (byteIs_spec a _ _ this).1
                      by_cases hlt4 : i1 < iU + 4
                      · simp [hlt4] at h
                      · simp only [hlt4, ↓reduceIte] at h
                        have hge : ¬ (i1.toNat < (iU + 4).toNat) := fun h' => hlt4 (USize.lt_iff_toNat_lt.2 h')
                        obtain ⟨pe2, -, pe4⟩ := pnU a hsz tape tw (by omega) htape (hdrW 2 0) 0
                        exact ih (fu - 1) w1 b1 i1 (iU + 4) true _ (tw + 2) text fst stk sp d t hf1 (by rw [hi4]; omega) (by rw [pe3]; omega) (by rw [pe2, pe3]; exact pe4) hd hS
                          (by rw [hi4]; exact rel_mono a (stage1 a) hM hsz w1 b1 i1 _ _ hr1 (by omega) (by omega) (by rw [hi4] at hge; omega)) (fun h => by simp at h) h
                    · simp [hdl] at h
                  · simp [hc3] at h
                · simp only [h74, Bool.false_eq_true, ↓reduceIte] at h ⊢
                  by_cases h66 : (a[iU.toNat] == 0x66) = true
                  · simp only [h66, ↓reduceIte] at h ⊢
                    by_cases hc3 : (byteIsU a (iU + 1) 0x61 && byteIsU a (iU + 2) 0x6C && byteIsU a (iU + 3) 0x73 && byteIsU a (iU + 4) 0x65) = true
                    · simp only [hc3, ↓reduceIte] at h ⊢
                      by_cases hdl : delimAtU a (iU + 5) = true
                      · simp only [hdl, ↓reduceIte] at h ⊢
                        rw [hk] at h
                        have hlt3 : iU.toNat + 4 < a.size := by
                          simp only [Bool.and_eq_true] at hc3
                          have := hc3.2
                          rw [byteIsU_eq a hs32, hi4] at this
                          exact (byteIs_spec a _ _ this).1
                        by_cases hlt4 : i1 < iU + 5
                        · simp [hlt4] at h
                        · simp only [hlt4, ↓reduceIte] at h
                          have hge : ¬ (i1.toNat < (iU + 5).toNat) := fun h' => hlt4 (USize.lt_iff_toNat_lt.2 h')
                          obtain ⟨pe2, -, pe4⟩ := pnU a hsz tape tw (by omega) htape (hdrW 1 0) 0
                          exact ih (fu - 1) w1 b1 i1 (iU + 5) true _ (tw + 2) text fst stk sp d t hf1 (by rw [hi5]; omega) (by rw [pe3]; omega) (by rw [pe2, pe3]; exact pe4) hd hS
                            (by rw [hi5]; exact rel_mono a (stage1 a) hM hsz w1 b1 i1 _ _ hr1 (by omega) (by omega) (by rw [hi5] at hge; omega)) (fun h => by simp at h) h
                      · simp [hdl] at h
                    · simp [hc3] at h
                  · simp only [h66, Bool.false_eq_true, ↓reduceIte] at h ⊢
                    obtain ⟨bad, hK, hbad⟩ := scanNumK_spec a hs31 iU hi
                    rw [hK] at h
                    by_cases hne : (scanNumU a iU == 0) = true
                    · simp [hne] at h
                    · simp only [hne, Bool.false_eq_true, ↓reduceIte] at h ⊢
                      obtain ⟨hadv, hjb⟩ := scanNumU_adv a hsz iU hi hne
                      by_cases hdl : delimAtU a (scanNumU a iU) = true
                      · simp only [hdl, ↓reduceIte] at h ⊢
                        rw [hk] at h
                        by_cases hlt4 : i1 < scanNumU a iU
                        · simp [hlt4] at h
                        · simp only [hlt4, ↓reduceIte] at h
                          have hge : ¬ (i1.toNat < (scanNumU a iU).toNat) := fun h' => hlt4 (USize.lt_iff_toNat_lt.2 h')
                          have hlex := hbad hne
                          by_cases hbd : bad = true
                          · have hnl : ¬ lexOkU a iU (scanNumU a iU) = true := fun hh => by have := hlex.1 hh; simp [hbd] at this
                            simp only [hbd, ↓reduceIte] at h
                            simp only [hnl, Bool.false_eq_true, ↓reduceIte]
                            generalize pushLex a iU.toNat (scanNumU a iU).toNat text = text' at h ⊢
                            obtain ⟨pe2, -, pe4⟩ := pnU a hsz tape tw (by omega) htape (hdrW 3 (text'.size - text.size)) (UInt64.ofNat text.size)
                            exact ih (fu - 1) w1 b1 i1 (scanNumU a iU) true _ (tw + 2) text' fst stk sp d t hf1 hjb (by rw [pe3]; omega) (by rw [pe2, pe3]; exact pe4) hd hS
                              (rel_mono a (stage1 a) hM hsz w1 b1 i1 _ _ hr1 (by omega) (by omega) (by omega)) (fun h => by simp at h) h
                          · have hbf : bad = false := by simpa using hbd
                            have hl : lexOkU a iU (scanNumU a iU) = true := hlex.2 hbf
                            simp only [hbf, Bool.false_eq_true, ↓reduceIte] at h
                            simp only [hl, ↓reduceIte]
                            unfold appendBytes at h
                            generalize a.copySlice iU.toNat text text.size (scanNumU a iU - iU).toNat false = text' at h ⊢
                            obtain ⟨pe2, -, pe4⟩ := pnU a hsz tape tw (by omega) htape (hdrW 3 (text'.size - text.size)) (UInt64.ofNat text.size)
                            exact ih (fu - 1) w1 b1 i1 (scanNumU a iU) true _ (tw + 2) text' fst stk sp d t hf1 hjb (by rw [pe3]; omega) (by rw [pe2, pe3]; exact pe4) hd hS
                              (rel_mono a (stage1 a) hM hsz w1 b1 i1 _ _ hr1 (by omega) (by omega) (by omega)) (fun h => by simp at h) h
                      · simp [hdl] at h
      · simp only [hlt, ↓reduceDIte] at h
        simp at h
    | true =>
      obtain ⟨e1, e2, e3, e4, e5, e6⟩ := rel_settle a (stage1 a) hM hsz w b i iU.toNat hr hi
      have e0 : skipU (stage1 a) a.usize iU = i := skipU_cur a (stage1 a) hM hsz w b i iU.toNat hr hi iU rfl
      cases fst with
      | nil =>
        simp only [] at h ⊢
        rw [e0]
        have hsp0 : (sp == 0) = true := (usize_beq_zero sp).2 (by rw [hS.1]; rfl)
        simp only [hsp0, ↓reduceIte] at h
        exact h
      | arr at_ n rest =>
        simp only [] at h ⊢
        rw [e0]
        have hSl := hS.1
        simp only [fsLen] at hSl
        have hsp0 : ¬ (sp == 0) = true := fun h0 => by have := (usize_beq_zero sp).1 h0; omega
        simp only [hsp0, Bool.false_eq_true, ↓reduceIte] at h
        have hS0 : SInv stk sp (if 0 = 0 then FStack.arr at_ n rest else FStack.obj at_ n rest) := by simpa using hS
        obtain ⟨r0, rn, hSp, hat⟩ := SInv_pop stk sp at_ n rest 0 (by decide) hS0 (by rw [fsLen_arr] at hd; omega)
        rw [r0, rn, kind_word_eq at_ 0 (by decide)] at h
        simp only [show (UInt64.ofNat 0 == 0) = true from rfl, ↓reduceIte] at h
        by_cases hcomma : byteIsU a i 0x2C = true
        · simp only [hcomma, ↓reduceIte] at h ⊢
          have hc' := hcomma
          rw [byteIsU_eq a hs32] at hc'
          have hlti : i.toNat < a.size := (byteIs_spec a _ _ hc').1
          obtain ⟨w1, b1, hk, hp1, hp2, hp3, hr1, hr1s⟩ := adv_full a (stage1 a) hM hsz w b i e5 hlti
          rw [hk] at h
          have hi1 := add_one a i (by omega) hsz
          have e1' : skipU (stage1 a) a.usize (i + 1) = curPosU a.usize w1 b1 := by
            apply USize.toNat_inj.mp
            rw [skipU_eq (stage1 a) a hs31 _ (by rw [hi1]; omega), hi1, hp1]
          rw [e1']
          generalize curPosU a.usize w1 b1 = i1 at hk hp1 hp2 hp3 hr1 hr1s h
          rw [ofNat_succ'] at h
          have hS1 := SInv_inc stk sp at_ n rest 0 (by decide) hS0 (by rw [fsLen_arr] at hd; omega)
          simp only [↓reduceIte] at hS1
          exact ih (fu - 1) w1 b1 i1 i1 false tape tw text _ _ _ d t hf1 hp3 (by omega) htape (by rw [fsLen_arr] at hd ⊢; omega) hS1 hr1s (fun _ => rfl) h
        · simp only [hcomma, Bool.false_eq_true, ↓reduceIte] at h ⊢
          by_cases hclose : byteIsU a i 0x5D = true
          · simp only [hclose, ↓reduceIte] at h ⊢
            have hc' := hclose
            rw [byteIsU_eq a hs32] at hc'
            have hlti : i.toNat < a.size := (byteIs_spec a _ _ hc').1
            obtain ⟨w1, b1, hk, hp1, hp2, hp3, hr1, hr1s⟩ := adv_full a (stage1 a) hM hsz w b i e5 hlti
            rw [hk] at h
            have hi1 := add_one a i (by omega) hsz
            have hdl : (d + 1).toNat = d.toNat + 1 := usize_add_lit d 1 (by decide) (by have := usize_ge32; rw [fsLen_arr] at hd; omega)
            generalize curPosU a.usize w1 b1 = i1 at hk hp1 hp2 hp3 hr1 hr1s h
            rw [unpack_at at_ 0 (by decide) hat, closeU_eq tape tw at_ hat, ofNat_succ'] at h
            exact ih (fu - 1) w1 b1 i1 (i + 1) true _ tw text rest _ _ (d + 1) t hf1 (by omega) (by omega) (by rw [st64_size, st64_size]; exact htape)
              (by rw [hdl]; rw [fsLen_arr] at hd; omega) hSp (by rw [hi1]; exact hr1) (fun h => by simp at h) h
          · simp only [hclose, Bool.false_eq_true, ↓reduceIte] at h
            simp at h
      | obj at_ n rest =>
        simp only [] at h ⊢
        rw [e0]
        have hSl := hS.1
        simp only [fsLen] at hSl
        have hsp0 : ¬ (sp == 0) = true := fun h0 => by have := (usize_beq_zero sp).1 h0; omega
        simp only [hsp0, Bool.false_eq_true, ↓reduceIte] at h
        have hS0 : SInv stk sp (if 1 = 0 then FStack.arr at_ n rest else FStack.obj at_ n rest) := by simpa using hS
        obtain ⟨r0, rn, hSp, hat⟩ := SInv_pop stk sp at_ n rest 1 (by decide) hS0 (by rw [fsLen_obj] at hd; omega)
        rw [r0, rn, kind_word_eq at_ 1 (by decide)] at h
        simp only [show (UInt64.ofNat 1 == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte] at h
        by_cases hcomma : byteIsU a i 0x2C = true
        · simp only [hcomma, ↓reduceIte] at h ⊢
          have hc' := hcomma
          rw [byteIsU_eq a hs32] at hc'
          have hlti : i.toNat < a.size := (byteIs_spec a _ _ hc').1
          obtain ⟨w1, b1, hk, hp1, hp2, hp3, hr1, hr1s⟩ := adv_full a (stage1 a) hM hsz w b i e5 hlti
          rw [hk] at h
          have hi1 := add_one a i (by omega) hsz
          have e1' : skipU (stage1 a) a.usize (i + 1) = curPosU a.usize w1 b1 := by
            apply USize.toNat_inj.mp
            rw [skipU_eq (stage1 a) a hs31 _ (by rw [hi1]; omega), hi1, hp1]
          rw [e1']
          generalize curPosU a.usize w1 b1 = i1 at hk hp1 hp2 hp3 hr1 hr1s h
          by_cases hlt1 : i1.toNat < a.size
          · obtain ⟨w2, b2, hk2, hq1, hq2, hq3, hr2, hr2s⟩ := adv_full a (stage1 a) hM hsz w1 b1 i1 hr1s hlt1
            rw [hk2] at h
            have hi2 := add_one a i1 (by omega) hsz
            have e2' : skipU (stage1 a) a.usize (i1 + 1) = curPosU a.usize w2 b2 := by
              apply USize.toNat_inj.mp
              rw [skipU_eq (stage1 a) a hs31 _ (by rw [hi2]; omega), hi2, hq1]
            generalize curPosU a.usize w2 b2 = i2 at hk2 hq1 hq2 hq3 hr2 hr2s h e2'
            rw [strU_C _ _ hsz, e2']
            cases hsc : strC a i1 i2 text with
            | none => rw [hsc] at h; simp at h
            | some tj =>
              obtain ⟨text', j⟩ := tj
              rw [hsc] at h
              simp only [] at h ⊢
              obtain ⟨-, hr', hj, hjt⟩ := strC_spec a hsz i1 i2 text text' j hsc
              obtain ⟨w3, b3, hk3, hs1, hs2, hs3, hr3, hr3s⟩ := adv_full a (stage1 a) hM hsz w2 b2 i2 hr2s hr'
              rw [hk3] at h
              have e3 : skipU (stage1 a) a.usize j = curPosU a.usize w3 b3 := by
                apply USize.toNat_inj.mp
                rw [skipU_eq (stage1 a) a hs31 _ (by omega), hjt, hs1]
              rw [e3]
              generalize curPosU a.usize w3 b3 = i3 at hk3 hs1 hs2 hs3 hr3 hr3s h e3
              by_cases hc3 : byteIsU a i3 0x3A = true
              · simp only [hc3, ↓reduceIte] at h ⊢
                have hc3' := hc3
                rw [byteIsU_eq a hs32] at hc3'
                have hlt3 : i3.toNat < a.size := (byteIs_spec a _ _ hc3').1
                obtain ⟨w4, b4, hk4, hu1, hu2, hu3, hr4, hr4s⟩ := adv_full a (stage1 a) hM hsz w3 b3 i3 hr3s hlt3
                rw [hk4] at h
                have hi3 := add_one a i3 (by omega) hsz
                have e4 : skipU (stage1 a) a.usize (i3 + 1) = curPosU a.usize w4 b4 := by
                  apply USize.toNat_inj.mp
                  rw [skipU_eq (stage1 a) a hs31 _ (by rw [hi3]; omega), hi3, hu1]
                rw [e4]
                generalize curPosU a.usize w4 b4 = i4 at hk4 hu1 hu2 hu3 hr4 hr4s h e4
                obtain ⟨pf2, pf3, pf4⟩ := pnU a hsz tape tw (by omega) htape (hdrW 4 (text'.size - text.size)) (UInt64.ofNat text.size)
                rw [ofNat_succ'] at h
                have hS1 := SInv_inc stk sp at_ n rest 1 (by decide) hS0 (by rw [fsLen_obj] at hd; omega)
                simp only [show (1 : Nat) ≠ 0 by decide, ↓reduceIte] at hS1
                exact ih (fu - 1) w4 b4 i4 i4 false _ (tw + 2) text' _ _ _ d t hf1 hu3 (by rw [pf3]; omega)
                  (by rw [pf2, pf3]; exact pf4) (by rw [fsLen_obj] at hd ⊢; omega) hS1 hr4s (fun _ => rfl) h
              · simp only [hc3, Bool.false_eq_true, ↓reduceIte] at h
                simp at h
          · exfalso
            rw [advK_none] at h
            · simp at h
            · intro w2 b2 i2
              simp only [strC_oob a hsz i1 i2 text hlt1]
        · simp only [hcomma, Bool.false_eq_true, ↓reduceIte] at h ⊢
          by_cases hclose : byteIsU a i 0x7D = true
          · simp only [hclose, ↓reduceIte] at h ⊢
            have hc' := hclose
            rw [byteIsU_eq a hs32] at hc'
            have hlti : i.toNat < a.size := (byteIs_spec a _ _ hc').1
            obtain ⟨w1, b1, hk, hp1, hp2, hp3, hr1, hr1s⟩ := adv_full a (stage1 a) hM hsz w b i e5 hlti
            rw [hk] at h
            have hi1 := add_one a i (by omega) hsz
            have hdl : (d + 1).toNat = d.toNat + 1 := usize_add_lit d 1 (by decide) (by have := usize_ge32; rw [fsLen_obj] at hd; omega)
            generalize curPosU a.usize w1 b1 = i1 at hk hp1 hp2 hp3 hr1 hr1s h
            rw [unpack_at at_ 1 (by decide) hat, closeU_eq tape tw at_ hat, ofNat_succ'] at h
            exact ih (fu - 1) w1 b1 i1 (i + 1) true _ tw text rest _ _ (d + 1) t hf1 (by omega) (by omega) (by rw [st64_size, st64_size]; exact htape)
              (by rw [hdl]; rw [fsLen_obj] at hd; omega) hSp (by rw [hi1]; exact hr1) (fun h => by simp at h) h
          · simp only [hclose, Bool.false_eq_true, ↓reduceIte] at h
            simp at h

/-- The index-driven parser returns exactly what the scalar fused parser returns (and so, by `parseTapeFast_eq`, the tape of the `Value`). -/
theorem parseTapeSimd_eq (a : ByteArray) : parseTapeSimd a = parseTapeFast a := by
  have hU := parseTapeU_eq a
  unfold parseTapeSimd
  by_cases hsz : a.size < simdLimit
  · simp only [hsz, ↓reduceIte]
    have hsz' : a.size < 2 ^ 26 := by unfold simdLimit at hsz; omega
    have hs31 : a.size < 2 ^ 31 := by omega
    have hM := maskOk_stage1 a hsz'
    unfold parseTapeU at hU
    simp only [hsz, ↓reduceIte] at hU
    rw [stage1Fast_eq a hs31] at hU ⊢
    obtain ⟨w0, b0, hk, hc, hn, hw⟩ := startK_spec a (stage1 a) hM
    rw [hk]
    have hmd : (maxDepth.toUSize).toNat = maxDepth := usize_toNat_small _ (by unfold maxDepth; decide)
    have hfu : (a.usize + 2).toNat = a.size + 2 := by
      rw [usize_add_lit _ 2 (by decide) (by have := usize_ge32; rw [usize_eq a (by omega)]; omega), usize_eq a (by omega)]
    have hz : zeros4k.size = 4096 := (zeroBytes_spec 4096).1
    generalize hT : initTape (tapeHint (stage1 a)) = T0 at hU ⊢
    have ht0 : T0.size = 4096 := by rw [← hT]; exact initTape_size _
    generalize hT2 : initTape 8192 = S0 at hU ⊢
    have hs0 : S0.size = 4096 := by rw [← hT2]; exact initTape_size _
    cases hr : runC (stage1 a) (a.usize + 2) a w0 b0 (curPosU a.usize w0 b0) false T0 0 (ByteArray.emptyWithCapacity a.size) S0 0 maxDepth.toUSize with
    | none => rfl
    | some t =>
      have hrel : CRel a (stage1 a) w0 b0 (curPosU a.usize w0 b0) 0 := ⟨hc, hn, hw, rfl⟩
      have hle : 0 ≤ a.size := Nat.zero_le _
      have e0 : skipU (stage1 a) a.usize 0 = curPosU a.usize w0 b0 := skipU_cur a (stage1 a) hM hsz' w0 b0 _ 0 hrel hle 0 usize_zero_toNat
      have hrel' : CRel a (stage1 a) w0 b0 (curPosU a.usize w0 b0) (skipU (stage1 a) a.usize 0).toNat := by
        rw [e0]
        exact (rel_settle a (stage1 a) hM hsz' w0 b0 _ 0 hrel hle).2.2.2.2.1
      have hsk := skipI_le (stage1 a) a.size 0
      have hkk := sk0 a hsz' 0 (by rw [usize_zero_toNat]; omega)
      rw [usize_zero_toNat] at hkk
      have hu := runC_sound a hsz' (a.size + 2) (a.usize + 2) w0 b0 _ (skipU (stage1 a) a.usize 0) false T0 0 (ByteArray.emptyWithCapacity a.size) FStack.nil S0 0 maxDepth.toUSize t hfu
        (by rw [hkk]; omega) (by rw [usize_zero_toNat]; omega) (by rw [usize_zero_toNat]; omega) (by rw [hmd]; unfold maxDepth; simp [fsLen]) (SInv_nil S0 (by omega)) hrel' (fun _ => e0) hr
      simp only [hu] at hU
      exact hU
  · simp [hsz]

end LeanJsonProofs
