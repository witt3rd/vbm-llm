import LeanJsonProofs.Stage1
import LeanJsonProofs.ParseW
import VbmSimdProofs.Classify
/-! # Proof: the AVX2 classifier gives the portable stage 1 (`stage1Fast_eq`)

`LeanJsonSimd/Stage1.lean`, `stage1LoopB`. The four class masks of a block come from `classify64`, whose Lean body (its model: the shim is trusted, trust ledger T14, vbm-simd T14) is `classifyModel`: word `r` of the result is
the mask whose bit `p` is "byte `64 k + p` exists and its class bits under the nibble tables `classTbl` meet the mask byte `r` of `classMs`". Each of the four mask bytes is shown to flag exactly the bytes the portable masks flag
(`classTbl_quote`, `classTbl_bslash`, `classTbl_op`, `classTbl_ws`, 256 cases each; the byte `0` that pads past the end has no class bit), so the four masks are equal as words (`ext_bits`), `maskOutF` of them is `blockOut` of the eight
words (`maskOutF_eq`: the escape computation skipped for a block with no backslash), and the two loops, and so `stage1A` and `stage1`, are equal. `stage1Fast` (the shim where `hasAvx2 ()`, the portable
`stage1` otherwise) is `stage1` for either answer of the CPU test. -/
namespace LeanJsonProofs
open LeanJson VbmSimd VbmSimdProofs

theorem classTbl_quote : ∀ v : UInt8, ((classByte classTbl v &&& 0x01) != 0) = (v == 0x22) := u8_forall _ (by decide)
theorem classTbl_bslash : ∀ v : UInt8, ((classByte classTbl v &&& 0x02) != 0) = (v == 0x5c) := u8_forall _ (by decide)
theorem classTbl_op : ∀ v : UInt8, ((classByte classTbl v &&& 0x1C) != 0) = isOp v := u8_forall _ (by decide)
theorem classTbl_ws : ∀ v : UInt8, ((classByte classTbl v &&& 0x60) != 0) = isWs v := u8_forall _ (by decide)
theorem classTbl_zero (m : UInt8) : ((classByte classTbl 0 &&& m) != 0) = false := by
  have : classByte classTbl 0 = 0 := by decide
  rw [this]; simp

theorem byteAt0_ge' (a : ByteArray) (n : Nat) (h : a.size ≤ n) : byteAt0 a n = 0 := byteAt0_ge a n h

/-- Bit `p` of the class mask for the block at `64 k`: the byte exists and its class bits meet `m` (the model). -/
theorem pad_class (a : ByteArray) (i : Nat) (Q : UInt8 → Bool) (h0 : Q 0 = false) : (decide (i < a.size) && Q (byteAt0 a i)) = Q (byteAt0 a i) := by
  by_cases hs : i < a.size
  · simp [hs]
  · simp [hs, byteAt0_ge' a i (by omega), h0]

theorem maskOutF_eq (q b o ws esc str scal : UInt64) : maskOutF q b o ws esc str scal = maskOut q b o ws esc str scal := by
  unfold maskOutF maskOut
  by_cases hb : b == 0
  · have hb' : b = 0 := by simpa using hb
    subst hb'
    have h1 : escaped 0 esc = esc := by simp [escaped]
    have h2 : escOut 0 esc = 0 := by simp [escOut]
    simp [h1, h2]
  · simp [hb]

theorem shl6_usize (w : USize) (hw : w.toNat < 2 ^ 26) : (w <<< 6).toNat = 64 * w.toNat := by
  have h2 : System.Platform.numBits = 32 ∨ System.Platform.numBits = 64 := System.Platform.numBits_eq
  have h6 : (6 : USize).toNat = 6 := USize.toNat_ofNat_of_lt_32 (by decide)
  rw [USize.toNat_shiftLeft, h6, Nat.shiftLeft_eq]
  rcases h2 with h | h <;> rw [h] <;> simp only [Nat.reduceMod, Nat.reducePow] <;> omega

theorem ld64_lit (x : ByteArray) (n : Nat) (hn : n < 4294967296) : ld64 x (OfNat.ofNat n : USize) = ld64Model x n := by
  show ld64Model x (OfNat.ofNat n : USize).toNat = _
  rw [usize_lit n hn]

theorem blockB_eq (a : ByteArray) (k : Nat) (hk : 64 * k + 64 < 4294967296) (cls : ByteArray) (hcls : 32 ≤ cls.size) (esc str scal : UInt64) :
    maskOutF (ld64Model (classifyModel a (64 * k) classTbl classMs cls) 0) (ld64Model (classifyModel a (64 * k) classTbl classMs cls) 8)
      (ld64Model (classifyModel a (64 * k) classTbl classMs cls) 16) (ld64Model (classifyModel a (64 * k) classTbl classMs cls) 24) esc str scal =
    blockOut (ld64 a (64 * k).toUSize) (ld64 a (64 * k + 8).toUSize) (ld64 a (64 * k + 16).toUSize) (ld64 a (64 * k + 24).toUSize) (ld64 a (64 * k + 32).toUSize)
      (ld64 a (64 * k + 40).toUSize) (ld64 a (64 * k + 48).toUSize) (ld64 a (64 * k + 56).toUSize) esc str scal := by
  rw [maskOutF_eq]
  have hk' : 64 * k < 4294967296 := by omega
  rw [ld64_toUSize a _ hk', ld64_toUSize a (64 * k + 8) (by omega), ld64_toUSize a (64 * k + 16) (by omega), ld64_toUSize a (64 * k + 24) (by omega), ld64_toUSize a (64 * k + 32) (by omega),
    ld64_toUSize a (64 * k + 40) (by omega), ld64_toUSize a (64 * k + 48) (by omega), ld64_toUSize a (64 * k + 56) (by omega)]
  have hb := blk_ld64Model a (64 * k)
  unfold blockOut
  have w0 := classify_word0 a (64 * k) classTbl classMs cls hcls
  have w1 := classify_word1 a (64 * k) classTbl classMs cls hcls
  have w2 := classify_word2 a (64 * k) classTbl classMs cls hcls
  have w3 := classify_word3 a (64 * k) classTbl classMs cls hcls
  have hq : classSpec a (64 * k) classTbl 0x01 = eqMask64 cQuote (ld64Model a (64 * k)) (ld64Model a (64 * k + 8)) (ld64Model a (64 * k + 16)) (ld64Model a (64 * k + 24))
      (ld64Model a (64 * k + 32)) (ld64Model a (64 * k + 40)) (ld64Model a (64 * k + 48)) (ld64Model a (64 * k + 56)) := by
    apply ext_bits; intro p hp
    rw [bit_classSpec a _ _ _ p hp, eqMask64_u8 hb cQuote 0x22 u8_cQuote p hp, ← classTbl_quote]
    exact pad_class a _ (fun v => (classByte classTbl v &&& 0x01) != 0) (classTbl_zero _)
  have hbs : classSpec a (64 * k) classTbl 0x02 = eqMask64 cBslash (ld64Model a (64 * k)) (ld64Model a (64 * k + 8)) (ld64Model a (64 * k + 16)) (ld64Model a (64 * k + 24))
      (ld64Model a (64 * k + 32)) (ld64Model a (64 * k + 40)) (ld64Model a (64 * k + 48)) (ld64Model a (64 * k + 56)) := by
    apply ext_bits; intro p hp
    rw [bit_classSpec a _ _ _ p hp, eqMask64_u8 hb cBslash 0x5c u8_cBslash p hp, ← classTbl_bslash]
    exact pad_class a _ (fun v => (classByte classTbl v &&& 0x02) != 0) (classTbl_zero _)
  have ho : classSpec a (64 * k) classTbl 0x1C = mask8 opWord (ld64Model a (64 * k)) (ld64Model a (64 * k + 8)) (ld64Model a (64 * k + 16)) (ld64Model a (64 * k + 24))
      (ld64Model a (64 * k + 32)) (ld64Model a (64 * k + 40)) (ld64Model a (64 * k + 48)) (ld64Model a (64 * k + 56)) := by
    apply ext_bits; intro p hp
    rw [bit_classSpec a _ _ _ p hp, opMask_bit hb p hp, ← classTbl_op]
    exact pad_class a _ (fun v => (classByte classTbl v &&& 0x1C) != 0) (classTbl_zero _)
  have hw : classSpec a (64 * k) classTbl 0x60 = mask8 wsWord (ld64Model a (64 * k)) (ld64Model a (64 * k + 8)) (ld64Model a (64 * k + 16)) (ld64Model a (64 * k + 24))
      (ld64Model a (64 * k + 32)) (ld64Model a (64 * k + 40)) (ld64Model a (64 * k + 48)) (ld64Model a (64 * k + 56)) := by
    apply ext_bits; intro p hp
    rw [bit_classSpec a _ _ _ p hp, wsMask_bit hb p hp, ← classTbl_ws]
    exact pad_class a _ (fun v => (classByte classTbl v &&& 0x60) != 0) (classTbl_zero _)
  rw [w0, w1, w2, w3]
  have m0 : (classMs).toUInt8 = 0x01 := by decide
  have m1 : (classMs >>> 8).toUInt8 = 0x02 := by decide
  have m2 : (classMs >>> 16).toUInt8 = 0x1C := by decide
  have m3 : (classMs >>> 24).toUInt8 = 0x60 := by decide
  rw [m0, m1, m2, m3, hq, hbs, ho, hw]

theorem stage1LoopB_eq (a : ByteArray) (n : USize) (hn : 64 * n.toNat + 64 < 4294967296) :
    ∀ d (k : USize) (cls out : ByteArray) esc str scal, n.toNat - k.toNat = d → 32 ≤ cls.size →
      stage1LoopB a cls out k n esc str scal = stage1Loop a out k.toNat n.toNat esc str scal := by
  intro d
  induction d with
  | zero =>
    intro k cls out esc str scal hd hcls
    have hk : ¬ k < n := by rw [USize.lt_iff_toNat_lt]; omega
    rw [stage1Loop_ge a out k.toNat n.toNat esc str scal (by omega), stage1LoopB]
    simp only [hk, ↓reduceDIte]
  | succ d ih =>
    intro k cls out esc str scal hd hcls
    have hk : k < n := by rw [USize.lt_iff_toNat_lt]; omega
    have hk' : k.toNat < n.toNat := USize.lt_iff_toNat_lt.1 hk
    have hk26 : k.toNat < 2 ^ 26 := by omega
    rw [stage1Loop_lt a out k.toNat n.toNat esc str scal hk', stage1LoopB]
    simp only [hk, ↓reduceDIte]
    have hcl : classify64 a (k <<< 6) classTbl classMs cls = classifyModel a (64 * k.toNat) classTbl classMs cls := by
      rw [classify64_spec, shl6_usize k hk26]
    rw [hcl]
    have e0 : ld64 (classifyModel a (64 * k.toNat) classTbl classMs cls) 0 = ld64Model (classifyModel a (64 * k.toNat) classTbl classMs cls) 0 := ld64_lit _ 0 (by decide)
    have e1 : ld64 (classifyModel a (64 * k.toNat) classTbl classMs cls) 8 = ld64Model (classifyModel a (64 * k.toNat) classTbl classMs cls) 8 := ld64_lit _ 8 (by decide)
    have e2 : ld64 (classifyModel a (64 * k.toNat) classTbl classMs cls) 16 = ld64Model (classifyModel a (64 * k.toNat) classTbl classMs cls) 16 := ld64_lit _ 16 (by decide)
    have e3 : ld64 (classifyModel a (64 * k.toNat) classTbl classMs cls) 24 = ld64Model (classifyModel a (64 * k.toNat) classTbl classMs cls) 24 := ld64_lit _ 24 (by decide)
    rw [e0, e1, e2, e3, blockB_eq a k.toNat (by omega) cls hcls esc str scal]
    cases blockOut (ld64 a (64 * k.toNat).toUSize) (ld64 a (64 * k.toNat + 8).toUSize) (ld64 a (64 * k.toNat + 16).toUSize) (ld64 a (64 * k.toNat + 24).toUSize) (ld64 a (64 * k.toNat + 32).toUSize)
      (ld64 a (64 * k.toNat + 40).toUSize) (ld64 a (64 * k.toNat + 48).toUSize) (ld64 a (64 * k.toNat + 56).toUSize) esc str scal with
    | mk s r =>
      obtain ⟨e, r2⟩ := r
      obtain ⟨t, c⟩ := r2
      simp only []
      have hcls' : 32 ≤ (classifyModel a (64 * k.toNat) classTbl classMs cls).size := by rw [classify64_size]; exact hcls
      have hnk : n.toNat - (k + 1).toNat = d := by
        have h1 : (1 : USize).toNat = 1 := USize.toNat_ofNat_of_lt_32 (by decide)
        have h7 := USize.toNat_lt_size n
        have h9 : k.toNat + 1 < USize.size := by omega
        have h8 : (k + 1).toNat = k.toNat + 1 := by
          rw [USize.toNat_add, h1]; exact Nat.mod_eq_of_lt h9
        omega
      rw [ih (k + 1) _ _ _ _ _ hnk hcls']
      have h8 : (k + 1).toNat = k.toNat + 1 := by
        have h1 : (1 : USize).toNat = 1 := USize.toNat_ofNat_of_lt_32 (by decide)
        have h7 := USize.toNat_lt_size n
        have h9 : k.toNat + 1 < USize.size := by omega
        rw [USize.toNat_add, h1]; exact Nat.mod_eq_of_lt h9
      rw [h8]
      have hku : k.toNat.toUSize = k := USize.ofNat_toNat
      rw [hku]

theorem stage1A_eq (a : ByteArray) (h : a.size < 2 ^ 31) : stage1A a = stage1 a := by
  unfold stage1A stage1
  dsimp only
  have hn : ((a.size + 63) / 64).toUSize.toNat = (a.size + 63) / 64 := usize_toNat_small _ (by omega)
  have hz : (zeroBytes 32).size = 32 := (zeroBytes_spec 32).1
  have hz0 : (0 : USize).toNat = 0 := USize.toNat_ofNat_of_lt_32 (by decide)
  rw [stage1LoopB_eq a ((a.size + 63) / 64).toUSize (by rw [hn]; omega) ((a.size + 63) / 64) 0 (zeroBytes 32) (zeroBytes (8 * ((a.size + 63) / 64))) 0 0 0 (by rw [hn, hz0]; omega) (by omega)]
  rw [hn, hz0]

/-- The structural mask the parser uses is the portable stage 1, for either answer of the CPU test (the shim is the model). -/
theorem stage1Fast_eq (a : ByteArray) (h : a.size < 2 ^ 31) : stage1Fast a = stage1 a := by
  unfold stage1Fast
  split
  · exact stage1A_eq a h
  · rfl

end LeanJsonProofs
