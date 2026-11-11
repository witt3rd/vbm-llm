import LeanJsonProofs.ParseU
/-! # Proof: the container stack in an array is the container stack of `runU` (`SInv`)

`LeanJsonSimd/ParseSimd.lean`, `runC`. `runU` keeps the open containers in an `FStack`, one heap cell each; `runC` keeps them in a byte array `stk` and a count `sp`, two words per container: word `2k` is `2 * at_ + kind` (the tape word index
of the container's header, kind 0 for an array and 1 for an object) and word `2k + 1` the number of elements completed in it, frame 0 the outermost. `SRel stk fst` says the array holds the frames of `fst`; `SInv stk sp fst` adds that `sp`
is their number and that the array stays small (so that every index and size fits a `USize` on any platform). The frame is pushed by `putNodeU` (the tape's own two-word store, which makes room first), read back by two loads, and its
count is bumped by one store: each is a lemma here, and none touches the frames below. -/
namespace LeanJsonProofs
open LeanJson VbmSimd VbmSimdProofs

/-- The array holds the frames of `fst` (innermost last): the header index (below `2^32`) with its kind, and the count. -/
def SRel (stk : ByteArray) : FStack → Prop
  | .nil => True
  | .arr at_ n rest => at_ + 2 < 2 ^ 32 ∧ 16 * (fsLen rest + 1) ≤ stk.size ∧ ld64Model stk (16 * fsLen rest) = UInt64.ofNat (2 * at_) ∧ ld64Model stk (16 * fsLen rest + 8) = UInt64.ofNat n ∧ SRel stk rest
  | .obj at_ n rest => at_ + 2 < 2 ^ 32 ∧ 16 * (fsLen rest + 1) ≤ stk.size ∧ ld64Model stk (16 * fsLen rest) = UInt64.ofNat (2 * at_ + 1) ∧ ld64Model stk (16 * fsLen rest + 8) = UInt64.ofNat n ∧ SRel stk rest

/-- The invariant of the stack array: it holds `fst`, `sp` counts the frames, and it is small. -/
def SInv (stk : ByteArray) (sp : USize) (fst : FStack) : Prop := sp.toNat = fsLen fst ∧ SRel stk fst ∧ stk.size ≤ 12304

theorem SRel_size (stk : ByteArray) : ∀ fst, SRel stk fst → 16 * fsLen fst ≤ stk.size
  | .nil, _ => by simp [fsLen]
  | .arr _ _ rest, h => by simp only [SRel] at h; simp only [fsLen]; omega
  | .obj _ _ rest, h => by simp only [SRel] at h; simp only [fsLen]; omega

/-- A later array that agrees with the earlier one on the words below `2 * fsLen fst` (and is not smaller) holds the same frames. -/
theorem SRel_agree (stk stk' : ByteArray) (hsz : stk.size ≤ stk'.size) : ∀ fst, (∀ j, j < 2 * fsLen fst → ld64Model stk' (8 * j) = ld64Model stk (8 * j)) → SRel stk fst → SRel stk' fst
  | .nil, _, _ => trivial
  | .arr at_ n rest, hag, h => by
    simp only [SRel] at h ⊢
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    have hl : fsLen (FStack.arr at_ n rest) = fsLen rest + 1 := rfl
    refine ⟨h1, by omega, ?_, ?_, SRel_agree stk stk' hsz rest (fun j hj => hag j (by rw [hl]; omega)) h5⟩
    · have := hag (2 * fsLen rest) (by rw [hl]; omega)
      rw [show 8 * (2 * fsLen rest) = 16 * fsLen rest by omega] at this
      rw [this, h3]
    · have := hag (2 * fsLen rest + 1) (by rw [hl]; omega)
      rw [show 8 * (2 * fsLen rest + 1) = 16 * fsLen rest + 8 by omega] at this
      rw [this, h4]
  | .obj at_ n rest, hag, h => by
    simp only [SRel] at h ⊢
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    have hl : fsLen (FStack.obj at_ n rest) = fsLen rest + 1 := rfl
    refine ⟨h1, by omega, ?_, ?_, SRel_agree stk stk' hsz rest (fun j hj => hag j (by rw [hl]; omega)) h5⟩
    · have := hag (2 * fsLen rest) (by rw [hl]; omega)
      rw [show 8 * (2 * fsLen rest) = 16 * fsLen rest by omega] at this
      rw [this, h3]
    · have := hag (2 * fsLen rest + 1) (by rw [hl]; omega)
      rw [show 8 * (2 * fsLen rest + 1) = 16 * fsLen rest + 8 by omega] at this
      rw [this, h4]

theorem SInv_nil (stk : ByteArray) (h : stk.size ≤ 12304) : SInv stk 0 .nil := ⟨by rw [usize_zero_toNat]; rfl, trivial, h⟩

/-! ## The stores and loads -/

theorem ld64Model_congr (a b : ByteArray) (i : Nat) (h : ∀ n, i ≤ n → n < i + 8 → byteAt0 a n = byteAt0 b n) : ld64Model a i = ld64Model b i := by
  unfold ld64Model
  rw [h i (by omega) (by omega), h (i + 1) (by omega) (by omega), h (i + 2) (by omega) (by omega), h (i + 3) (by omega) (by omega), h (i + 4) (by omega) (by omega),
    h (i + 5) (by omega) (by omega), h (i + 6) (by omega) (by omega), h (i + 7) (by omega) (by omega)]

theorem ensureTape_size_cases (t : ByteArray) (w : Nat) : (ensureTape t w).size = t.size ∨ ((ensureTape t w).size = t.size + 4096 ∧ ¬ w + 2 ≤ t.size / 8) := by
  by_cases hc : w + 2 ≤ t.size / 8
  · left; simp [ensureTape, hc]
  · right
    refine ⟨?_, hc⟩
    simp only [ensureTape, hc, ↓reduceIte]
    exact (growTape_spec t).1

theorem putNode_words (t : ByteArray) (w : Nat) (hw : 8 * w ≤ t.size) (hw32 : w + 2 < 2 ^ 32) (h x : UInt64) :
    8 * (w + 2) ≤ (putNode t w h x).size ∧ t.size ≤ (putNode t w h x).size ∧ ld64Model (putNode t w h x) (8 * w) = h ∧ ld64Model (putNode t w h x) (8 * (w + 1)) = x ∧
    ∀ j, j ≠ w → j ≠ w + 1 → 8 * j + 8 ≤ t.size → ld64Model (putNode t w h x) (8 * j) = ld64Model t (8 * j) := by
  obtain ⟨e1, e2, e3⟩ := ensureTape_spec t w hw
  have hp : putNode t w h x = st64Model (st64Model (ensureTape t w) w h) (w + 1) x := by
    unfold putNode
    rw [st64_toUSize _ (w + 1) x (by omega), st64_toUSize _ w h (by omega)]
  rw [hp]
  have s1 : (st64Model (ensureTape t w) w h).size = (ensureTape t w).size := st64Model_size _ _ _
  have s2 : (st64Model (st64Model (ensureTape t w) w h) (w + 1) x).size = (ensureTape t w).size := by rw [st64Model_size, s1]
  refine ⟨by omega, by omega, ?_, ?_, ?_⟩
  · rw [ld64Model_st64Model_other _ (w + 1) x w (by omega), ld64Model_st64Model_self _ w h (by omega)]
  · exact ld64Model_st64Model_self _ (w + 1) x (by omega)
  · intro j hj1 hj2 hj
    rw [ld64Model_st64Model_other _ (w + 1) x j hj2, ld64Model_st64Model_other _ w h j hj1]
    exact ld64Model_congr _ _ _ (fun n hn1 hn2 => e3 n (by omega))

theorem shl_usize (y : USize) (k : Nat) (hk : k < 32) (hy : 2 ^ k * y.toNat < 2 ^ 32) : (y <<< (OfNat.ofNat k : USize)).toNat = 2 ^ k * y.toNat := by
  have h2 : System.Platform.numBits = 32 ∨ System.Platform.numBits = 64 := System.Platform.numBits_eq
  have hk' : (OfNat.ofNat k : USize).toNat = k := usize_lit k (by omega)
  have hmod : k % System.Platform.numBits = k := Nat.mod_eq_of_lt (by rcases h2 with h | h <;> rw [h] <;> omega)
  rw [USize.toNat_shiftLeft, hk', hmod, Nat.shiftLeft_eq, Nat.mul_comm]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hy usize_ge32)

theorem shl1_usize (y : USize) (hy : 2 * y.toNat < 2 ^ 32) : (y <<< (1 : USize)).toNat = 2 * y.toNat := by
  have h2 : System.Platform.numBits = 32 ∨ System.Platform.numBits = 64 := System.Platform.numBits_eq
  have hk' : (1 : USize).toNat = 1 := usize_lit 1 (by decide)
  have hmod : 1 % System.Platform.numBits = 1 := Nat.mod_eq_of_lt (by rcases h2 with h | h <;> rw [h] <;> omega)
  rw [USize.toNat_shiftLeft, hk', hmod, Nat.shiftLeft_eq, Nat.mul_comm, Nat.pow_one]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hy usize_ge32)

theorem shl3_usize (y : USize) (hy : 8 * y.toNat < 2 ^ 32) : (y <<< (3 : USize)).toNat = 8 * y.toNat := by
  have h2 : System.Platform.numBits = 32 ∨ System.Platform.numBits = 64 := System.Platform.numBits_eq
  have hk' : (3 : USize).toNat = 3 := usize_lit 3 (by decide)
  have hmod : 3 % System.Platform.numBits = 3 := Nat.mod_eq_of_lt (by rcases h2 with h | h <;> rw [h] <;> omega)
  rw [USize.toNat_shiftLeft, hk', hmod, Nat.shiftLeft_eq, Nat.mul_comm]
  have : 2 ^ 3 * y.toNat = 8 * y.toNat := rfl
  rw [this]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hy usize_ge32)

theorem ofNat_succ' (n : Nat) : UInt64.ofNat n + 1 = UInt64.ofNat (n + 1) := by
  apply UInt64.toNat_inj.mp
  simp [UInt64.toNat_add, UInt64.toNat_ofNat]

theorem two_mul_word (tw : USize) (k : Nat) : tw.toUInt64 * 2 + UInt64.ofNat k = UInt64.ofNat (2 * tw.toNat + k) := by
  apply UInt64.toNat_inj.mp
  simp [UInt64.toNat_add, UInt64.toNat_mul, USize.toNat_toUInt64, UInt64.toNat_ofNat]
  omega

theorem usize_add1 (y : USize) (h : y.toNat + 1 < 2 ^ 32) : (y + 1).toNat = y.toNat + 1 := usize_add_lit y 1 (by decide) (by have := usize_ge32; omega)

theorem usize_sub1 (y : USize) (h : 0 < y.toNat) : (y - 1).toNat = y.toNat - 1 := by
  have h3 : (1 : USize) ≤ y := by rw [USize.le_iff_toNat_le, usize_lit 1 (by decide)]; omega
  rw [USize.toNat_sub_of_le y 1 h3, usize_lit 1 (by decide)]

/-- Pushing a frame: the two words are stored at the top, the frames below are as they were, the array is still small. -/
theorem push_core (stk : ByteArray) (sp : USize) (fst : FStack) (hS : SInv stk sp fst) (hsp : sp.toNat ≤ 511) (w0 : UInt64) :
    (putNodeU stk (sp <<< 1) w0 0).size ≤ 12304 ∧ 16 * (fsLen fst + 1) ≤ (putNodeU stk (sp <<< 1) w0 0).size ∧ ld64Model (putNodeU stk (sp <<< 1) w0 0) (16 * fsLen fst) = w0 ∧
      ld64Model (putNodeU stk (sp <<< 1) w0 0) (16 * fsLen fst + 8) = 0 ∧ (sp + 1).toNat = fsLen fst + 1 ∧ stk.size ≤ (putNodeU stk (sp <<< 1) w0 0).size ∧
      ∀ j, j < 2 * fsLen fst → ld64Model (putNodeU stk (sp <<< 1) w0 0) (8 * j) = ld64Model stk (8 * j) := by
  obtain ⟨hl, hr, hsz⟩ := hS
  have hs1 : (sp <<< (1 : USize)).toNat = 2 * sp.toNat := shl1_usize sp (by omega)
  have hp1 := usize_add1 sp (by omega)
  have hfl := SRel_size stk fst hr
  have hw : (sp <<< (1 : USize)).toNat + 2 < 4294967296 := by omega
  have hput : putNodeU stk (sp <<< 1) w0 0 = putNode stk (2 * fsLen fst) w0 0 := by
    rw [putNodeU_eq stk (by omega) _ hw, hs1, hl]
  rw [hput]
  obtain ⟨p1, p2, p3, p4, p5⟩ := putNode_words stk (2 * fsLen fst) (by omega) (by omega) w0 0
  have p3' : ld64Model (putNode stk (2 * fsLen fst) w0 0) (16 * fsLen fst) = w0 := by rw [show 16 * fsLen fst = 8 * (2 * fsLen fst) by omega]; exact p3
  have p4' : ld64Model (putNode stk (2 * fsLen fst) w0 0) (16 * fsLen fst + 8) = 0 := by rw [show 16 * fsLen fst + 8 = 8 * (2 * fsLen fst + 1) by omega]; exact p4
  refine ⟨?_, by omega, p3', p4', by rw [hp1, hl], p2, fun j hj => p5 j (by omega) (by omega) (by omega)⟩
  rcases ensureTape_size_cases stk (2 * fsLen fst) with h | h
  · have : (putNode stk (2 * fsLen fst) w0 0).size = (ensureTape stk (2 * fsLen fst)).size := by
      unfold putNode
      rw [st64_toUSize _ _ _ (by omega), st64_toUSize _ _ _ (by omega), st64Model_size, st64Model_size]
    omega
  · have : (putNode stk (2 * fsLen fst) w0 0).size = (ensureTape stk (2 * fsLen fst)).size := by
      unfold putNode
      rw [st64_toUSize _ _ _ (by omega), st64_toUSize _ _ _ (by omega), st64Model_size, st64Model_size]
    have := h.2
    omega

theorem SInv_push_arr (stk : ByteArray) (sp : USize) (fst : FStack) (hS : SInv stk sp fst) (hsp : sp.toNat ≤ 511) (tw : USize) (htw : tw.toNat + 2 < 2 ^ 32) :
    SInv (putNodeU stk (sp <<< 1) (tw.toUInt64 * 2) 0) (sp + 1) (.arr tw.toNat 0 fst) := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := push_core stk sp fst hS hsp (tw.toUInt64 * 2)
  have hw : tw.toUInt64 * 2 = UInt64.ofNat (2 * tw.toNat) := by
    have := two_mul_word tw 0
    simpa using this
  refine ⟨by rw [c5]; rfl, ?_, c1⟩
  simp only [SRel]
  exact ⟨htw, c2, by rw [c3, hw], by rw [c4]; rfl, SRel_agree stk _ c6 fst c7 hS.2.1⟩

theorem SInv_push_obj (stk : ByteArray) (sp : USize) (fst : FStack) (hS : SInv stk sp fst) (hsp : sp.toNat ≤ 511) (tw : USize) (htw : tw.toNat + 2 < 2 ^ 32) :
    SInv (putNodeU stk (sp <<< 1) (tw.toUInt64 * 2 + 1) 0) (sp + 1) (.obj tw.toNat 0 fst) := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := push_core stk sp fst hS hsp (tw.toUInt64 * 2 + 1)
  have hw : tw.toUInt64 * 2 + 1 = UInt64.ofNat (2 * tw.toNat + 1) := by
    have := two_mul_word tw 1
    simpa using this
  refine ⟨by rw [c5]; rfl, ?_, c1⟩
  simp only [SRel]
  exact ⟨htw, c2, by rw [c3, hw], by rw [c4]; rfl, SRel_agree stk _ c6 fst c7 hS.2.1⟩

/-- The loads at the top frame (the index arithmetic of `runC`). -/
theorem top_index (sp : USize) (L : Nat) (hL : sp.toNat = L + 1) (hsp : sp.toNat ≤ 512) :
    (sp - 1).toNat = L ∧ ((sp - 1) <<< (1 : USize)).toNat = 2 * L ∧ (((sp - 1) <<< (1 : USize)) <<< (3 : USize)).toNat = 16 * L ∧
      (((sp - 1) <<< (1 : USize)) + 1).toNat = 2 * L + 1 ∧ ((((sp - 1) <<< (1 : USize)) + 1) <<< (3 : USize)).toNat = 16 * L + 8 := by
  have h1 : (sp - 1).toNat = L := by rw [usize_sub1 sp (by omega)]; omega
  have h2 : ((sp - 1) <<< (1 : USize)).toNat = 2 * L := by rw [shl1_usize _ (by omega), h1]
  have h3 : (((sp - 1) <<< (1 : USize)) <<< (3 : USize)).toNat = 16 * L := by rw [shl3_usize _ (by omega), h2]; omega
  have h4 : (((sp - 1) <<< (1 : USize)) + 1).toNat = 2 * L + 1 := by rw [usize_add1 _ (by omega), h2]
  have h5 : ((((sp - 1) <<< (1 : USize)) + 1) <<< (3 : USize)).toNat = 16 * L + 8 := by rw [shl3_usize _ (by omega), h4]; omega
  exact ⟨h1, h2, h3, h4, h5⟩

theorem SInv_pop (stk : ByteArray) (sp : USize) (at_ n : Nat) (rest : FStack) (kind : Nat) (hk : kind < 2) (hS : SInv stk sp (if kind = 0 then .arr at_ n rest else .obj at_ n rest)) (hsp : sp.toNat ≤ 512) :
    ld64 stk (((sp - 1) <<< (1 : USize)) <<< (3 : USize)) = UInt64.ofNat (2 * at_ + kind) ∧ ld64 stk ((((sp - 1) <<< (1 : USize)) + 1) <<< (3 : USize)) = UInt64.ofNat n ∧
      SInv stk (sp - 1) rest ∧ at_ + 2 < 2 ^ 32 := by
  obtain ⟨hl, hr, hsz⟩ := hS
  have hkc : kind = 0 ∨ kind = 1 := by omega
  rcases hkc with rfl | rfl
  · simp only [↓reduceIte] at hl hr
    simp only [fsLen] at hl
    obtain ⟨ti1, ti2, ti3, ti4, ti5⟩ := top_index sp (fsLen rest) hl hsp
    simp only [SRel] at hr
    obtain ⟨r1, r2, r3, r4, r5⟩ := hr
    refine ⟨?_, ?_, ⟨ti1, r5, hsz⟩, r1⟩
    · show ld64Model stk _ = _; rw [ti3, r3]; rfl
    · show ld64Model stk _ = _; rw [ti5, r4]
  · simp only [show (1 : Nat) ≠ 0 by decide, ↓reduceIte] at hl hr
    simp only [fsLen] at hl
    obtain ⟨ti1, ti2, ti3, ti4, ti5⟩ := top_index sp (fsLen rest) hl hsp
    simp only [SRel] at hr
    obtain ⟨r1, r2, r3, r4, r5⟩ := hr
    refine ⟨?_, ?_, ⟨ti1, r5, hsz⟩, r1⟩
    · show ld64Model stk _ = _; rw [ti3, r3]
    · show ld64Model stk _ = _; rw [ti5, r4]

theorem SInv_inc (stk : ByteArray) (sp : USize) (at_ n : Nat) (rest : FStack) (kind : Nat) (hk : kind < 2) (hS : SInv stk sp (if kind = 0 then .arr at_ n rest else .obj at_ n rest)) (hsp : sp.toNat ≤ 512) :
    SInv (st64 stk (((sp - 1) <<< (1 : USize)) + 1) (UInt64.ofNat (n + 1))) sp (if kind = 0 then .arr at_ (n + 1) rest else .obj at_ (n + 1) rest) := by
  have hS' := hS
  obtain ⟨hl, hr, hsz⟩ := hS
  have hkc : kind = 0 ∨ kind = 1 := by omega
  rcases hkc with rfl | rfl
  · simp only [↓reduceIte] at hl hr hS' ⊢
    simp only [fsLen] at hl
    obtain ⟨ti1, ti2, ti3, ti4, ti5⟩ := top_index sp (fsLen rest) hl hsp
    simp only [SRel] at hr
    obtain ⟨r1, r2, r3, r4, r5⟩ := hr
    have hst : st64 stk (((sp - 1) <<< (1 : USize)) + 1) (UInt64.ofNat (n + 1)) = st64Model stk (2 * fsLen rest + 1) (UInt64.ofNat (n + 1)) := by
      show st64Model stk _ _ = _; rw [ti4]
    rw [hst]
    refine ⟨hl, ?_, by rw [st64Model_size]; exact hsz⟩
    simp only [SRel]
    refine ⟨r1, by rw [st64Model_size]; exact r2, ?_, ?_, ?_⟩
    · rw [show 16 * fsLen rest = 8 * (2 * fsLen rest) by omega, ld64Model_st64Model_other _ (2 * fsLen rest + 1) _ (2 * fsLen rest) (by omega)]
      rw [← show 16 * fsLen rest = 8 * (2 * fsLen rest) by omega]; exact r3
    · rw [show 16 * fsLen rest + 8 = 8 * (2 * fsLen rest + 1) by omega]
      exact ld64Model_st64Model_self _ _ _ (by omega)
    · refine SRel_agree stk _ (by rw [st64Model_size]; exact Nat.le_refl _) rest (fun j hj => ?_) r5
      exact ld64Model_st64Model_other _ (2 * fsLen rest + 1) _ j (by omega)
  · simp only [show (1 : Nat) ≠ 0 by decide, ↓reduceIte] at hl hr hS' ⊢
    simp only [fsLen] at hl
    obtain ⟨ti1, ti2, ti3, ti4, ti5⟩ := top_index sp (fsLen rest) hl hsp
    simp only [SRel] at hr
    obtain ⟨r1, r2, r3, r4, r5⟩ := hr
    have hst : st64 stk (((sp - 1) <<< (1 : USize)) + 1) (UInt64.ofNat (n + 1)) = st64Model stk (2 * fsLen rest + 1) (UInt64.ofNat (n + 1)) := by
      show st64Model stk _ _ = _; rw [ti4]
    rw [hst]
    refine ⟨hl, ?_, by rw [st64Model_size]; exact hsz⟩
    simp only [SRel]
    refine ⟨r1, by rw [st64Model_size]; exact r2, ?_, ?_, ?_⟩
    · rw [show 16 * fsLen rest = 8 * (2 * fsLen rest) by omega, ld64Model_st64Model_other _ (2 * fsLen rest + 1) _ (2 * fsLen rest) (by omega)]
      rw [← show 16 * fsLen rest = 8 * (2 * fsLen rest) by omega]; exact r3
    · rw [show 16 * fsLen rest + 8 = 8 * (2 * fsLen rest + 1) by omega]
      exact ld64Model_st64Model_self _ _ _ (by omega)
    · refine SRel_agree stk _ (by rw [st64Model_size]; exact Nat.le_refl _) rest (fun j hj => ?_) r5
      exact ld64Model_st64Model_other _ (2 * fsLen rest + 1) _ j (by omega)

theorem ofNat_toNat64 (n : Nat) : (UInt64.ofNat n).toNat = n % 2 ^ 64 := rfl

theorem kind_word_eq (x k : Nat) (hk : k < 2) : ((UInt64.ofNat (2 * x + k)) &&& 1) = UInt64.ofNat k := by
  apply UInt64.toNat_inj.mp
  have e : (1 : UInt64).toNat = 1 := rfl
  rw [UInt64.toNat_and, ofNat_toNat64, ofNat_toNat64, e, Nat.and_one_is_mod]
  omega

theorem unpack_at (x k : Nat) (hk : k < 2) (hx : x + 2 < 2 ^ 32) : (UInt64.ofNat (2 * x + k) >>> 1).toUSize = x.toUSize := by
  apply USize.toNat_inj.mp
  rw [usize_toNat_small _ (by omega)]
  have e : (1 : UInt64).toNat = 1 := rfl
  rw [UInt64.toNat_toUSize, UInt64.toNat_shiftRight, ofNat_toNat64, e]
  have h1 : (2 * x + k) % 2 ^ 64 = 2 * x + k := Nat.mod_eq_of_lt (by omega)
  rw [h1, Nat.shiftRight_eq_div_pow]
  have : (2 * x + k) / 2 ^ (1 % 64) = x := by
    rw [show (2 : Nat) ^ (1 % 64) = 2 from rfl]
    omega
  rw [this]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by omega : x < 2 ^ 32) usize_ge32)

theorem closeU_eq (tape : ByteArray) (tw : USize) (at_ : Nat) (hat : at_ + 2 < 2 ^ 32) (h : UInt64) :
    closeU tape at_.toUSize tw h = st64 (st64 tape at_.toUSize h) (at_ + 1).toUSize (UInt64.ofNat (tw.toNat - at_)) := by
  unfold closeU
  have h2 : at_.toUSize.toNat = at_ := usize_toNat_small _ (by omega)
  have h1 : at_.toUSize + 1 = (at_ + 1).toUSize := by
    apply USize.toNat_inj.mp
    rw [usize_add1 _ (by rw [h2]; omega), h2, usize_toNat_small _ (by omega)]
  rw [h1]
  by_cases hle : at_.toUSize ≤ tw
  · have hle' : at_ ≤ tw.toNat := by have := USize.le_iff_toNat_le.1 hle; omega
    simp only [hle, ↓reduceIte]
    rw [usize_toUInt64_sub _ _ (by omega), h2]
  · have hle' : tw.toNat < at_ := by
      have : ¬ at_.toUSize.toNat ≤ tw.toNat := fun h' => hle (USize.le_iff_toNat_le.2 h')
      omega
    simp only [hle, ↓reduceIte]
    have : tw.toNat - at_ = 0 := by omega
    rw [this]
    rfl

end LeanJsonProofs
