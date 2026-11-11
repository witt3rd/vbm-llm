import LeanJson
/-! # Facts about the grammar relation (about the specification: nothing here is run)

The strict-text policy as theorems: every scalar value a derivation produces is a Unicode scalar value (no surrogate, nothing past U+10FFFF), so reading it with
`Char.ofNat` is faithful and a `String` cannot hold a lone surrogate. -/
namespace LeanJson

/-- A Unicode scalar value: not a surrogate, not past U+10FFFF. -/
def Scalar (n : Nat) : Prop := n < 0xD800 ∨ (0xE000 ≤ n ∧ n < 0x110000)

theorem utf8_scalar {bs : Bytes} {n : Nat} (h : Utf8 bs n) : Scalar n := by
  have h8 := UInt8.toNat_lt_size
  cases h with
  | u1 ha => unfold Scalar; omega
  | u2 ha hb hc => rename_i a b; have := UInt8.toNat_lt_size a; have := UInt8.toNat_lt_size b; unfold Scalar Tail at *; omega
  | u3 ha hb hc hd => rename_i a b c; have := UInt8.toNat_lt_size a; have := UInt8.toNat_lt_size b; have := UInt8.toNat_lt_size c; unfold Scalar Second3 Tail at *; omega
  | u4 ha hb hc hd he => rename_i a b c d; have := UInt8.toNat_lt_size a; have := UInt8.toNat_lt_size b; have := UInt8.toNat_lt_size c; have := UInt8.toNat_lt_size d; unfold Scalar Second4 Tail at *; omega

theorem hexVal_lt {b : UInt8} {k : Nat} (h : hexVal b = some k) : k < 16 := by
  unfold hexVal at h
  split at h
  · simp at h; omega
  · split at h
    · simp at h; omega
    · split at h
      · simp at h; omega
      · simp at h

theorem hex4_lt {bs : Bytes} {n : Nat} (h : Hex4 bs n) : n < 0x10000 := by
  cases h with
  | mk ha hb hc hd => have := hexVal_lt ha; have := hexVal_lt hb; have := hexVal_lt hc; have := hexVal_lt hd; omega

theorem esc_scalar {bs : Bytes} {n : Nat} (h : Esc bs n) : Scalar n := by
  cases h with
  | simple hs =>
    unfold simpleEsc at hs
    repeat' split at hs
    all_goals (simp at hs <;> (unfold Scalar; omega))
  | uni hh hn => have := hex4_lt hh; unfold Scalar; omega
  | pair h1 h2 a b c d => have := hex4_lt h1; have := hex4_lt h2; unfold Scalar; omega

theorem strChar_scalar {bs : Bytes} {n : Nat} (h : StrChar bs n) : Scalar n := by
  cases h with
  | plain hu => exact utf8_scalar hu
  | esc he => exact esc_scalar he

theorem ofNat_toNat_of_scalar {n : Nat} (hs : Scalar n) : (Char.ofNat n).toNat = n := by
  have hv : n.isValidChar := by unfold Nat.isValidChar Scalar at *; omega
  unfold Char.ofNat
  split
  · rfl
  · contradiction

/-- Every scalar a string derivation yields is a Unicode scalar value, so `Char.ofNat` reads it back unchanged. -/
theorem chars_scalar {bs : Bytes} {ns : List Nat} (h : Chars bs ns) : ∀ n ∈ ns, Scalar n ∧ (Char.ofNat n).toNat = n := by
  induction h with
  | nil => simp
  | cons hc _ ih =>
    intro n hn
    rcases List.mem_cons.mp hn with rfl | hn
    · exact ⟨strChar_scalar hc, ofNat_toNat_of_scalar (strChar_scalar hc)⟩
    · exact ih n hn

end LeanJson
