import LeanJsonSimd.ParseSimd
import LeanJsonProofs.ParseSimd
import LeanJsonProofs.Swar
/-! # Proof: `runW` (the tape written in place) answers only what `runI` answers (`runW_sound`)

`LeanJsonSimd/ParseSimd.lean`, `runW`. `runI` carries the tape and the text region in a `TapeBuf`; `runW` carries `tape` (a byte array at least `8 * tw` long: the first `8 * tw` bytes are the tape, the rest is zero-filled room),
`tw` (the words written) and `text`. The relation `Rel` says they are the `TapeBuf`. Each way `runW` writes is shown to keep the relation: a node (`Rel_put`), the patch of a closed container (`Rel_patch`), the text of a
string or a number (`strW_sound`, `numText_eq`), the end (`finishW_eq`); the skip is `skipI` (`skipF_eq`). The induction is the one of `runI_sound`, over the same branches. -/
namespace LeanJsonProofs
open LeanJson VbmSimd VbmSimdProofs

/-! ## Bytes -/

/-- `pushWord` writes byte `j` of the word at `b.size + j`. -/
theorem byteAt0_pushWord (b : ByteArray) (w : UInt64) (n : Nat) :
    byteAt0 (pushWord b w) n = if n < b.size then byteAt0 b n else if n < b.size + 8 then (w >>> UInt64.ofNat (8 * (n - b.size))).toUInt8 else 0 := by
  simp only [pushWord, byteAt0_push, ByteArray.size_push]
  by_cases h1 : n < b.size
  · simp only [h1, ↓reduceIte, show n < b.size + 1 by omega, show n < b.size + 1 + 1 by omega, show n < b.size + 1 + 1 + 1 by omega, show n < b.size + 1 + 1 + 1 + 1 by omega,
      show n < b.size + 1 + 1 + 1 + 1 + 1 by omega, show n < b.size + 1 + 1 + 1 + 1 + 1 + 1 by omega, show n < b.size + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]
  · by_cases h2 : n < b.size + 8
    · have hj : n = b.size ∨ n = b.size + 1 ∨ n = b.size + 2 ∨ n = b.size + 3 ∨ n = b.size + 4 ∨ n = b.size + 5 ∨ n = b.size + 6 ∨ n = b.size + 7 := by omega
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp +arith [h1, h2] <;> rfl
    · simp only [h1, h2, ↓reduceIte]
      have e : ¬ n < b.size + 1 + 1 + 1 + 1 + 1 + 1 + 1 := by omega
      simp only [e, ↓reduceIte, show n ≠ b.size + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]


/-! ## The relation -/

/-- `tape`, `tw`, `text` of `runW` are the tape and the text of the `TapeBuf` `tb`: the first `8 * tw` bytes of `tape` are `tb.tape` (which has no more), and the text is the text. -/
structure Rel (tape : ByteArray) (tw : Nat) (text : ByteArray) (tb : TapeBuf) : Prop where
  le : 8 * tw ≤ tape.size
  sz : tb.tape.size = 8 * tw
  eq : ∀ n, n < 8 * tw → byteAt0 tape n = byteAt0 tb.tape n
  tx : tb.text = text

theorem Rel.words {tape tw text tb} (h : Rel tape tw text tb) : tb.words = tw := by
  unfold TapeBuf.words; rw [h.sz]; omega

/-- A store inside the written part. -/
theorem Rel_st64 {tape tw text tb} (h : Rel tape tw text tb) (k : Nat) (_hk : k < tw) (w : UInt64) :
    Rel (st64Model tape k w) tw text ⟨st64Model tb.tape k w, tb.text⟩ := by
  refine ⟨?_, ?_, ?_, h.tx⟩
  · rw [st64Model_size]; exact h.le
  · simp only [st64Model_size]; exact h.sz
  · intro n hn
    simp only []
    by_cases hin : 8 * k ≤ n ∧ n < 8 * k + 8
    · obtain ⟨j, rfl, hj⟩ : ∃ j, n = 8 * k + j ∧ j < 8 := ⟨n - 8 * k, by omega, by omega⟩
      rw [byteAt0_st64Model_in _ k w j hj (by have := h.le; omega), byteAt0_st64Model_in _ k w j hj (by have := h.sz; omega)]
    · rw [byteAt0_st64Model_out _ k w n (by omega), byteAt0_st64Model_out _ k w n (by omega)]
      exact h.eq n hn

theorem growTape_spec (t : ByteArray) : (growTape t).size = t.size + 4096 ∧ ∀ n, n < t.size → byteAt0 (growTape t) n = byteAt0 t n := by
  have hz : zeros4k.size = 4096 := (zeroBytes_spec 4096).1
  have hd : (growTape t).data = t.data ++ zeros4k.data := by
    unfold growTape
    rw [ByteArray.copySlice_eq_append]
    have e1 : t.extract 0 t.size = t := ByteArray.extract_zero_size
    have e2 : zeros4k.extract 0 (0 + 4096) = zeros4k := by
      rw [← hz, Nat.zero_add]; exact ByteArray.extract_zero_size
    have e3 : t.extract (t.size + min 4096 (zeros4k.data.size - 0)) t.data.size = ByteArray.empty := by
      apply ByteArray.extract_eq_empty_iff.mpr; show min t.data.size t.size ≤ _; omega
    rw [e1, e2, e3]
    simp [ByteArray.data_append]
  refine ⟨?_, fun n hn => ?_⟩
  · show (growTape t).data.size = t.data.size + 4096
    rw [hd, Array.size_append]; show t.data.size + zeros4k.data.size = _; rw [show zeros4k.data.size = 4096 from hz]
  · unfold byteAt0
    rw [hd, Array.getD_eq_getD_getElem?, Array.getElem?_append_left (by exact hn), ← Array.getD_eq_getD_getElem?]

theorem ensureTape_spec (t : ByteArray) (w : Nat) (h : 8 * w ≤ t.size) : 8 * (w + 2) ≤ (ensureTape t w).size ∧ t.size ≤ (ensureTape t w).size ∧
    ∀ n, n < t.size → byteAt0 (ensureTape t w) n = byteAt0 t n := by
  unfold ensureTape
  by_cases hc : w + 2 ≤ t.size / 8
  · simp only [hc, ↓reduceIte, Nat.le_refl, implies_true, and_true]; omega
  · simp only [hc, ↓reduceIte]
    obtain ⟨g1, g2⟩ := growTape_spec t
    exact ⟨by omega, by omega, g2⟩


theorem hdrW_eq (kind : Nat) (len : Nat) : hdrW (UInt64.ofNat kind) len = UInt64.ofNat (kind + len * 256) := by
  unfold hdrW
  rw [UInt64.ofNat_add, UInt64.ofNat_mul, UInt64.add_comm]
  rfl

theorem size_pushWord (b : ByteArray) (w : UInt64) : (pushWord b w).size = b.size + 8 := by
  simp [pushWord, ByteArray.size_push]

/-- A node written at the end: the two words, with room made first. -/
theorem Rel_put {tape tw text tb} (hr : Rel tape tw text tb) (htw : tw + 1 < 2 ^ 32) (h x : UInt64) (text' : ByteArray) :
    Rel (putNode tape tw h x) (tw + 2) text' ⟨pushWord (pushWord tb.tape h) x, text'⟩ := by
  obtain ⟨e1, e2, e3⟩ := ensureTape_spec tape tw hr.le
  have s64a := st64_toUSize (ensureTape tape tw) tw h (by omega)
  have s64b := st64_toUSize (st64Model (ensureTape tape tw) tw h) (tw + 1) x htw
  unfold putNode
  rw [s64a, s64b]
  refine ⟨?_, ?_, ?_, rfl⟩
  · simp only [st64Model_size]; exact e1
  · simp only [size_pushWord, hr.sz]; omega
  · intro n hn
    simp only [byteAt0_pushWord, size_pushWord, hr.sz]
    by_cases h1 : n < 8 * tw
    · rw [byteAt0_st64Model_out _ (tw + 1) x n (by omega), byteAt0_st64Model_out _ tw h n (by omega), e3 n (by have := hr.le; omega), hr.eq n h1]
      simp only [h1, ↓reduceIte, show n < 8 * tw + 8 by omega]
    · by_cases h2 : n < 8 * tw + 8
      · obtain ⟨j, rfl, hj⟩ : ∃ j, n = 8 * tw + j ∧ j < 8 := ⟨n - 8 * tw, by omega, by omega⟩
        rw [byteAt0_st64Model_out _ (tw + 1) x _ (by omega), byteAt0_st64Model_in _ tw h j hj (by omega)]
        simp only [h1, h2, ↓reduceIte, show 8 * tw + j - 8 * tw = j by omega]
      · obtain ⟨j, rfl, hj⟩ : ∃ j, n = 8 * tw + 8 + j ∧ j < 8 := ⟨n - (8 * tw + 8), by omega, by omega⟩
        rw [show 8 * tw + 8 + j = 8 * (tw + 1) + j by omega, byteAt0_st64Model_in _ (tw + 1) x j hj (by simp only [st64Model_size]; omega)]
        simp only [show ¬ 8 * (tw + 1) + j < 8 * tw + 8 by omega, ↓reduceIte, show 8 * (tw + 1) + j - (8 * tw + 8) = j by omega, show 8 * (tw + 1) + j < 8 * tw + 8 + 8 by omega]


/-- `TapeBuf.node`: the node of a header word and an auxiliary word. -/
theorem Rel_node {tape tw text tb} (hr : Rel tape tw text tb) (htw : tw + 1 < 2 ^ 32) (kind : Nat) (k : UInt64) (hk : k = UInt64.ofNat kind) (len aux : Nat) :
    Rel (putNode tape tw (hdrW k len) (UInt64.ofNat aux)) (tw + 2) text (tb.node kind len aux) := by
  have := Rel_put hr htw (hdrW k len) (UInt64.ofNat aux) text
  rw [hk, hdrW_eq] at this ⊢
  have e : tb.node kind len aux = ⟨pushWord (pushWord tb.tape (UInt64.ofNat (kind + len * 256))) (UInt64.ofNat aux), text⟩ := by
    rw [← hr.tx]; simp only [TapeBuf.node, pushWordFast_eq]
  rw [e]; exact this

theorem setWord_eq (b : ByteArray) (i : Nat) (w : UInt64) : setWord b i w = st64Model b i w := rfl

/-- The patch of a closed container: the header and the subtree size are stored over the placeholders. -/
theorem Rel_close {tape tw text tb} (hr : Rel tape tw text tb) (at_ : Nat) (hat : at_ + 1 < tw) (htw : tw < 2 ^ 32) (kind : Nat) (k : UInt64) (hk : k = UInt64.ofNat kind) (n : Nat) :
    Rel (st64 (st64 tape at_.toUSize (hdrW k n)) (at_ + 1).toUSize (UInt64.ofNat (tw - at_))) tw text (tb.closeNode kind at_ n) := by
  have e1 := st64_toUSize tape at_ (hdrW k n) (by omega)
  have e2 := st64_toUSize (st64Model tape at_ (hdrW k n)) (at_ + 1) (UInt64.ofNat (tw - at_)) (by omega)
  have h1 := Rel_st64 hr at_ (by omega) (hdrW k n)
  have h2 := Rel_st64 h1 (at_ + 1) hat (UInt64.ofNat (tw - at_))
  have hsz : tb.tape.size / 8 = tw := by have := hr.sz; omega
  have e : tb.closeNode kind at_ n = ⟨st64Model (st64Model tb.tape at_ (hdrW k n)) (at_ + 1) (UInt64.ofNat (tw - at_)), tb.text⟩ := by
    cases tb
    simp only [TapeBuf.closeNode, setWord_eq] at hsz ⊢
    rw [hsz, hk, hdrW_eq]
  rw [e1, e2, e]
  exact h2


theorem tape_extract {tape tw text tb} (hr : Rel tape tw text tb) : tb.tape = tape.extract 0 (8 * tw) := by
  apply ext_byteAt0
  · rw [ByteArray.size_extract, hr.sz]; have := hr.le; omega
  · intro n
    by_cases hn : n < 8 * tw
    · rw [← hr.eq n hn]
      unfold byteAt0
      rw [ByteArray.data_extract, Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_extract]
      have : n < min (8 * tw) tape.size := by have := hr.le; omega
      have h2 : n < min (8 * tw) tape.data.size - 0 := this
      simp only [h2, ↓reduceIte, Nat.zero_add]
    · rw [byteAt0_ge _ n (by rw [hr.sz]; omega), byteAt0_ge]
      rw [ByteArray.size_extract]; have := hr.le; omega

/-- The end: the result bytes of `runW` are the result bytes of `runI`. -/
theorem finishW_eq {tape tw text tb} (hr : Rel tape tw text tb) : finishW tape text tw = tapeOk tb := by
  have hw : tb.words = tw := hr.words
  have hx : tb.tape = tape.extract 0 (8 * tw) := tape_extract hr
  have htx : tb.text = text := hr.tx
  have hle : 8 * tw ≤ tape.size := hr.le
  unfold finishW tapeOk
  rw [hw, htx, hx]
  generalize hH : pushWordFast (pushWordFast (pushWordFast (ByteArray.emptyWithCapacity (24 + 8 * tw + text.size)) 0) (UInt64.ofNat tw)) (UInt64.ofNat text.size) = H
  have hh : H.size = 24 := by
    rw [← hH]; simp only [pushWordFast_eq, size_pushWord, show (ByteArray.emptyWithCapacity (24 + 8 * tw + text.size)).size = 0 from rfl]
  have hHe : pushWordFast (pushWordFast (pushWordFast ByteArray.empty 0) (UInt64.ofNat tw)) (UInt64.ofNat text.size) = H := hH
  rw [hHe]
  have e1 : tape.copySlice 0 H 24 (8 * tw) false = H ++ tape.extract 0 (8 * tw) := by
    rw [ByteArray.copySlice_eq_append, ← hh]
    have a1 : H.extract 0 H.size = H := ByteArray.extract_zero_size
    have a3 : H.extract (H.size + min (8 * tw) (tape.data.size - 0)) H.data.size = ByteArray.empty := by
      apply ByteArray.extract_eq_empty_iff.mpr; show min H.data.size H.size ≤ _; omega
    rw [a1, Nat.zero_add, a3, ByteArray.append_empty]
  dsimp only
  rw [e1, ByteArray.copySlice_eq_append]
  generalize H ++ tape.extract 0 (8 * tw) = R
  have b1 : R.extract 0 R.size = R := ByteArray.extract_zero_size
  have b2 : text.extract 0 (0 + text.size) = text := by rw [Nat.zero_add]; exact ByteArray.extract_zero_size
  have b3 : R.extract (R.size + min text.size (text.data.size - 0)) R.data.size = ByteArray.empty := by
    apply ByteArray.extract_eq_empty_iff.mpr; show min R.data.size R.size ≤ _; omega
  rw [b1, b2, b3, ByteArray.append_empty]


/-! ## Leaves -/

theorem push_extract (b a : ByteArray) (p e : Nat) (h : p < e) (hp : p < a.size) : b.push a[p] ++ a.extract (p + 1) e = b ++ a.extract p e := by
  rw [ByteArray.extract_eq_extract_append_extract (i := p) (k := e) (p + 1) (by omega) (by omega), ByteArray.extract_add_one (by omega),
    ← ByteArray.append_assoc, ByteArray.append_toByteArray_singleton]

/-- A run of plain bytes is copied: `strBytes` over `a[p, e)` appends it. -/
theorem strBytes_plain (a : ByteArray) : ∀ d p e b, e - p = d → p ≤ e → plainRun a p e = true → strBytes a p b = strBytes a e (b ++ a.extract p e) := by
  intro d
  induction d with
  | zero =>
    intro p e b hd hpe _
    have : p = e := by omega
    subst this
    rw [ByteArray.extract_same, ByteArray.append_empty]
  | succ d ih =>
    intro p e b hd hpe hrun
    have hlt : p < e := by omega
    rw [plainRun] at hrun
    simp only [hlt, ↓reduceDIte] at hrun
    by_cases hps : p < a.size
    · simp only [hps, ↓reduceDIte] at hrun
      by_cases hc : (plainAscii a[p] && a[p] != 0x22) = true
      · simp only [hc, ↓reduceIte] at hrun
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
        rw [strBytes]
        simp only [hps, ↓reduceDIte]
        have hq : (a[p] == 0x22) = false := by simpa using hc.2
        simp only [hq, Bool.false_eq_true, ↓reduceIte, hc.1]
        rw [ih (p + 1) e _ (by omega) (by omega) hrun, push_extract b a p e hlt hps]
      · simp [hc] at hrun
    · simp [hps] at hrun


/-! ## The skip -/

theorem usize_toNat_small (n : Nat) (h : n < 4294967296) : (n.toUSize).toNat = n := USize.toNat_ofNat_of_lt_32 h

theorem skipF_shl3 (j : Nat) (hj : j < 1073741824) : ((j >>> 6).toUSize <<< 3) = (8 * (j / 64)).toUSize := by
  apply USize.toNat_inj.mp
  have h2 : System.Platform.numBits = 32 ∨ System.Platform.numBits = 64 := System.Platform.numBits_eq
  have h3 : (j >>> 6) < 2 ^ 24 := by rw [Nat.shiftRight_eq_div_pow]; omega
  have h4 : (3 : USize).toNat = 3 := USize.toNat_ofNat_of_lt_32 (by decide)
  rw [USize.toNat_shiftLeft, h4, usize_toNat_small _ (by omega), usize_toNat_small _ (by omega)]
  rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  rcases h2 with h | h <;> rw [h] <;> simp only [Nat.reduceMod, Nat.reducePow] <;> omega

theorem skipF_shl6 (j : Nat) (hj : j < 1073741824) : ((j >>> 6).toUSize <<< 6).toNat = 64 * (j / 64) := by
  have h2 : System.Platform.numBits = 32 ∨ System.Platform.numBits = 64 := System.Platform.numBits_eq
  have h3 : (j >>> 6) < 2 ^ 24 := by rw [Nat.shiftRight_eq_div_pow]; omega
  have h4 : (6 : USize).toNat = 6 := USize.toNat_ofNat_of_lt_32 (by decide)
  rw [USize.toNat_shiftLeft, h4, usize_toNat_small _ (by omega)]
  rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  rcases h2 with h | h <;> rw [h] <;> simp only [Nat.reduceMod, Nat.reducePow] <;> omega

theorem skipF_mask (j : Nat) : ((~~~(0 : UInt64)) <<< (j &&& 63).toUInt64) = (~~~(0 : UInt64)) <<< (j % 64).toUInt64 := by
  have : j &&& 63 = j % 64 := by
    have := Nat.and_two_pow_sub_one_eq_mod j 6
    simpa using this
  rw [this]

theorem wordAt_ge (m : ByteArray) (w : Nat) (h : ¬ w < wordCount m) (hw : w < 2 ^ 28) : wordAt m w = 0 := by
  unfold wordAt
  rw [ld64_toUSize m (8 * w) (by omega)]
  have hm : m.size ≤ 8 * w := by unfold wordCount at h; omega
  unfold ld64Model
  simp only [byteAt0_ge m (8 * w) hm, byteAt0_ge m (8 * w + 1) (by omega), byteAt0_ge m (8 * w + 2) (by omega), byteAt0_ge m (8 * w + 3) (by omega),
    byteAt0_ge m (8 * w + 4) (by omega), byteAt0_ge m (8 * w + 5) (by omega), byteAt0_ge m (8 * w + 6) (by omega), byteAt0_ge m (8 * w + 7) (by omega)]
  rfl

theorem skipF_eq (m : ByteArray) (size j : Nat) : skipF m size j = skipI m size j := by
  unfold skipF
  by_cases hj : j < 1073741824
  · simp only [hj, ↓reduceIte]
    have hw : ld64 m ((j >>> 6).toUSize <<< 3) = wordAt m (j / 64) := by
      rw [skipF_shl3 j hj]; rfl
    rw [hw, skipF_mask, skipF_shl6 j hj]
    by_cases hz : (wordAt m (j / 64) &&& ((~~~(0 : UInt64)) <<< (j % 64).toUInt64)) != 0
    · simp only [hz, ↓reduceIte]
      have hlt : j / 64 < wordCount m := by
        refine Classical.byContradiction fun hn => ?_
        rw [wordAt_ge m _ hn (by omega)] at hz
        simp at hz
      unfold skipI nextSet
      simp only [hlt, ↓reduceIte]
      obtain ⟨f, hf⟩ : ∃ f, wordCount m - j / 64 = f + 1 := ⟨wordCount m - j / 64 - 1, by omega⟩
      rw [hf, nextSetGo]
      simp only [hz, ↓reduceIte]
    · simp only [hz, Bool.false_eq_true, ↓reduceIte]
  · simp only [hj, ↓reduceIte]


theorem copy_append (src dest : ByteArray) (o len : Nat) : src.copySlice o dest dest.size len false = dest ++ src.extract o (o + len) := by
  rw [ByteArray.copySlice_eq_append]
  have a1 : dest.extract 0 dest.size = dest := ByteArray.extract_zero_size
  have a3 : dest.extract (dest.size + min len (src.data.size - o)) dest.data.size = ByteArray.empty := by
    apply ByteArray.extract_eq_empty_iff.mpr; show min dest.data.size dest.size ≤ _; omega
  rw [a1, a3, ByteArray.append_empty]

theorem strBytes_quote (a : ByteArray) (r : Nat) (b : ByteArray) (h : byteIs a r 0x22 = true) : strBytes a r b = some (b, r + 1) := by
  obtain ⟨hr, hb⟩ := byteIs_spec a r _ h
  rw [strBytes]
  have : a[r] = 0x22 := by rw [← byteD_eq a r hr]; exact hb
  simp [hr, this]

/-! ## The continuation-passing decoder is the decoder -/

theorem decodeUtf8K_eq {β : Type} (a : ByteArray) (i : Nat) (k : Nat → Nat → β) (d : β) :
    decodeUtf8K a i k d = (match decodeUtf8A a i with | some (n, j) => k n j | none => d) := by
  unfold decodeUtf8K decodeUtf8A
  cases byteAt a i with
  | none => rfl
  | some x =>
    simp only []
    by_cases h1 : x.toNat < 0x80
    · simp only [h1, ↓reduceIte]
    · simp only [h1, ↓reduceIte]
      by_cases h2 : 0xC2 ≤ x.toNat ∧ x.toNat ≤ 0xDF
      · simp only [h2, and_self, ↓reduceIte]
        cases byteAt a (i + 1) with
        | none => rfl
        | some b =>
          simp only []
          by_cases h3 : Tail b <;> simp only [h3, ↓reduceIte]
      · simp only [h2, ↓reduceIte]
        by_cases h3 : 0xE0 ≤ x.toNat ∧ x.toNat ≤ 0xEF
        · simp only [h3]
          rcases hb : byteAt a (i + 1) with _ | b
          · rfl
          · rcases hc : byteAt a (i + 2) with _ | c
            · rfl
            · simp only []
              by_cases h4 : Second3 x b ∧ Tail c <;> simp only [h4, and_self, ↓reduceIte]
        · simp only [h3]
          by_cases h4 : 0xF0 ≤ x.toNat ∧ x.toNat ≤ 0xF4
          · simp only [h4, ↓reduceIte]
            rcases hb : byteAt a (i + 1) with _ | b
            · rfl
            · rcases hc : byteAt a (i + 2) with _ | c
              · rfl
              · rcases hd : byteAt a (i + 3) with _ | e
                · rfl
                · simp only []
                  by_cases h5 : Second4 x b ∧ Tail c ∧ Tail e <;> simp only [h5, and_self, ↓reduceIte]
          · simp only [h4, ↓reduceIte]

theorem decodeUK_eq {β : Type} (a : ByteArray) (i : Nat) (k : Nat → Nat → β) (d : β) :
    decodeUK a i k d = (match decodeUA a i with | some (n, j) => k n j | none => d) := by
  unfold decodeUK decodeUA
  rcases hn : hex4At a i with _ | n
  · rfl
  · simp only []
    by_cases h1 : n < 0xD800 ∨ 0xE000 ≤ n
    · simp only [h1, ↓reduceIte]
    · simp only [h1, ↓reduceIte]
      by_cases h2 : n < 0xDC00
      · simp only [h2, ↓reduceIte]
        by_cases h3 : (byteIs a (i + 4) 0x5C && byteIs a (i + 5) 0x75) = true
        · simp only [h3, ↓reduceIte]
          rcases hl : hex4At a (i + 6) with _ | lo
          · rfl
          · simp only []
            by_cases h4 : 0xDC00 ≤ lo ∧ lo < 0xE000 <;> simp only [h4, and_self, ↓reduceIte]
        · simp only [h3, Bool.false_eq_true, ↓reduceIte]
      · simp only [h2, ↓reduceIte]

theorem decodeCharK_eq {β : Type} (a : ByteArray) (i : Nat) (k : Nat → Nat → β) (d : β) :
    decodeCharK a i k d = (match decodeCharA a i with | some (n, j) => k n j | none => d) := by
  unfold decodeCharK decodeCharA
  by_cases h1 : byteIs a i 0x5C = true
  · simp only [h1, ↓reduceIte]
    rcases hb : byteAt a (i + 1) with _ | b
    · rfl
    · simp only []
      by_cases h2 : (b == 0x75) = true
      · simp only [h2, ↓reduceIte]; exact decodeUK_eq a (i + 2) k d
      · simp only [h2, Bool.false_eq_true, ↓reduceIte]
        rcases hs : simpleEsc b with _ | n <;> rfl
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    rw [decodeUtf8K_eq]
    rcases hu : decodeUtf8A a i with _ | ⟨n, j⟩
    · rfl
    · simp only []
      by_cases h3 : 0x20 ≤ n ∧ n ≠ 0x22 ∧ n ≠ 0x5C <;> simp [h3]

/-! ## A multi-byte character is copied as its bytes

`pushChar` of the scalar that `decodeUtf8A` reads is the bytes it read (`pushChar_2`, `pushChar_3`, `pushChar_4`: the UTF-8 encoding of the decoding of a well-formed sequence is the sequence), so a run of plain ASCII bytes and well-formed
multi-byte characters is copied (`strBytes_run`) and `strBytes` never has to decode it. -/


theorem ofNat_val2 {n : Nat} (h : n < 0xD800 ∨ (0xE000 ≤ n ∧ n < 0x110000)) : (Char.ofNat n).val.toNat = n := by
  have : n.isValidChar := by unfold Nat.isValidChar; omega
  simp [Char.ofNat, this, Char.ofNatAux]

theorem or_mask (y t q : Nat) : ((y &&& (2 ^ t - 1)) ||| (2 ^ t * q)) = 2 ^ t * q + y % 2 ^ t := by
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.or_comm]
  exact (Nat.two_pow_add_eq_or_of_lt (Nat.mod_lt _ (Nat.two_pow_pos t)) q).symm

theorem byte_enc (v s : UInt32) (hs : s.toNat < 32) (m k : UInt8) (t q : Nat) (hm : m.toNat = 2 ^ t - 1) (hk : k.toNat = 2 ^ t * q) :
    (((v >>> s).toUInt8 &&& m) ||| k).toNat = 2 ^ t * q + (v.toNat / 2 ^ s.toNat % 256) % 2 ^ t := by
  rw [UInt8.toNat_or, UInt8.toNat_and, hm, hk, or_mask, UInt32.toNat_toUInt8, UInt32.toNat_shiftRight, Nat.mod_eq_of_lt hs, Nat.shiftRight_eq_div_pow]

theorem byte_enc0 (v : UInt32) (m k : UInt8) (t q : Nat) (hm : m.toNat = 2 ^ t - 1) (hk : k.toNat = 2 ^ t * q) :
    ((v.toUInt8 &&& m) ||| k).toNat = 2 ^ t * q + (v.toNat % 256) % 2 ^ t := by
  rw [UInt8.toNat_or, UInt8.toNat_and, hm, hk, or_mask, UInt32.toNat_toUInt8]

theorem pushChar_2 (b : ByteArray) (x y : UInt8) (h1 : 0xC2 ≤ x.toNat) (h2 : x.toNat ≤ 0xDF) (h3 : 0x80 ≤ y.toNat) (h4 : y.toNat ≤ 0xBF) :
    pushChar b (Char.ofNat ((x.toNat - 0xC0) * 64 + (y.toNat - 0x80))) = (b.push x).push y := by
  have hv := ofNat_val2 (n := (x.toNat - 0xC0) * 64 + (y.toNat - 0x80)) (Or.inl (by omega))
  unfold pushChar
  generalize (Char.ofNat ((x.toNat - 0xC0) * 64 + (y.toNat - 0x80))).val = v at hv ⊢
  have c1 : ¬ v ≤ 0x7f := by rw [UInt32.le_iff_toNat_le, hv]; show ¬ _ ≤ 127; omega
  have c2 : v ≤ 0x7ff := by rw [UInt32.le_iff_toNat_le, hv]; show _ ≤ 2047; omega
  simp only [c1, c2, ↓reduceIte]
  have e1 : (v >>> 6).toUInt8 &&& 0x1f ||| 0xc0 = x := by
    apply UInt8.toNat_inj.mp
    rw [byte_enc v 6 (by decide) 0x1f 0xc0 5 6 (by decide) (by decide), hv]
    show 2 ^ 5 * 6 + (_ / 2 ^ 6 % 256) % 2 ^ 5 = _
    omega
  have e2 : v.toUInt8 &&& 0x3f ||| 0x80 = y := by
    apply UInt8.toNat_inj.mp
    rw [byte_enc0 v 0x3f 0x80 6 2 (by decide) (by decide), hv]
    omega
  rw [e1, e2]


theorem pushChar_3 (b : ByteArray) (x y z : UInt8) (h1 : 0xE0 ≤ x.toNat) (h2 : x.toNat ≤ 0xEF) (h3 : 0x80 ≤ y.toNat ∧ y.toNat ≤ 0xBF) (h4 : x.toNat = 0xE0 → 0xA0 ≤ y.toNat)
    (h5 : x.toNat = 0xED → y.toNat ≤ 0x9F) (h6 : 0x80 ≤ z.toNat ∧ z.toNat ≤ 0xBF) :
    pushChar b (Char.ofNat ((x.toNat - 0xE0) * 4096 + (y.toNat - 0x80) * 64 + (z.toNat - 0x80))) = ((b.push x).push y).push z := by
  have hv := ofNat_val2 (n := (x.toNat - 0xE0) * 4096 + (y.toNat - 0x80) * 64 + (z.toNat - 0x80)) (by omega)
  unfold pushChar
  generalize (Char.ofNat ((x.toNat - 0xE0) * 4096 + (y.toNat - 0x80) * 64 + (z.toNat - 0x80))).val = v at hv ⊢
  have c1 : ¬ v ≤ 0x7f := by rw [UInt32.le_iff_toNat_le, hv]; show ¬ _ ≤ 127; omega
  have c2 : ¬ v ≤ 0x7ff := by rw [UInt32.le_iff_toNat_le, hv]; show ¬ _ ≤ 2047; omega
  have c3 : v ≤ 0xffff := by rw [UInt32.le_iff_toNat_le, hv]; show _ ≤ 65535; omega
  simp only [c1, c2, c3, ↓reduceIte]
  have e1 : (v >>> 12).toUInt8 &&& 0x0f ||| 0xe0 = x := by
    apply UInt8.toNat_inj.mp
    rw [byte_enc v 12 (by decide) 0x0f 0xe0 4 14 (by decide) (by decide), hv]
    show 2 ^ 4 * 14 + (_ / 2 ^ 12 % 256) % 2 ^ 4 = _
    omega
  have e2 : (v >>> 6).toUInt8 &&& 0x3f ||| 0x80 = y := by
    apply UInt8.toNat_inj.mp
    rw [byte_enc v 6 (by decide) 0x3f 0x80 6 2 (by decide) (by decide), hv]
    show 2 ^ 6 * 2 + (_ / 2 ^ 6 % 256) % 2 ^ 6 = _
    omega
  have e3 : v.toUInt8 &&& 0x3f ||| 0x80 = z := by
    apply UInt8.toNat_inj.mp
    rw [byte_enc0 v 0x3f 0x80 6 2 (by decide) (by decide), hv]
    omega
  rw [e1, e2, e3]

theorem pushChar_4 (b : ByteArray) (x y z w : UInt8) (h1 : 0xF0 ≤ x.toNat) (h2 : x.toNat ≤ 0xF4) (h3 : 0x80 ≤ y.toNat ∧ y.toNat ≤ 0xBF) (h4 : x.toNat = 0xF0 → 0x90 ≤ y.toNat)
    (h5 : x.toNat = 0xF4 → y.toNat ≤ 0x8F) (h6 : 0x80 ≤ z.toNat ∧ z.toNat ≤ 0xBF) (h7 : 0x80 ≤ w.toNat ∧ w.toNat ≤ 0xBF) :
    pushChar b (Char.ofNat ((x.toNat - 0xF0) * 262144 + (y.toNat - 0x80) * 4096 + (z.toNat - 0x80) * 64 + (w.toNat - 0x80))) = (((b.push x).push y).push z).push w := by
  have hv := ofNat_val2 (n := (x.toNat - 0xF0) * 262144 + (y.toNat - 0x80) * 4096 + (z.toNat - 0x80) * 64 + (w.toNat - 0x80)) (by omega)
  unfold pushChar
  generalize (Char.ofNat ((x.toNat - 0xF0) * 262144 + (y.toNat - 0x80) * 4096 + (z.toNat - 0x80) * 64 + (w.toNat - 0x80))).val = v at hv ⊢
  have c1 : ¬ v ≤ 0x7f := by rw [UInt32.le_iff_toNat_le, hv]; show ¬ _ ≤ 127; omega
  have c2 : ¬ v ≤ 0x7ff := by rw [UInt32.le_iff_toNat_le, hv]; show ¬ _ ≤ 2047; omega
  have c3 : ¬ v ≤ 0xffff := by rw [UInt32.le_iff_toNat_le, hv]; show ¬ _ ≤ 65535; omega
  simp only [c1, c2, c3, ↓reduceIte]
  have e1 : (v >>> 18).toUInt8 &&& 0x07 ||| 0xf0 = x := by
    apply UInt8.toNat_inj.mp
    rw [byte_enc v 18 (by decide) 0x07 0xf0 3 30 (by decide) (by decide), hv]
    show 2 ^ 3 * 30 + (_ / 2 ^ 18 % 256) % 2 ^ 3 = _
    omega
  have e2 : (v >>> 12).toUInt8 &&& 0x3f ||| 0x80 = y := by
    apply UInt8.toNat_inj.mp
    rw [byte_enc v 12 (by decide) 0x3f 0x80 6 2 (by decide) (by decide), hv]
    show 2 ^ 6 * 2 + (_ / 2 ^ 12 % 256) % 2 ^ 6 = _
    omega
  have e3 : (v >>> 6).toUInt8 &&& 0x3f ||| 0x80 = z := by
    apply UInt8.toNat_inj.mp
    rw [byte_enc v 6 (by decide) 0x3f 0x80 6 2 (by decide) (by decide), hv]
    show 2 ^ 6 * 2 + (_ / 2 ^ 6 % 256) % 2 ^ 6 = _
    omega
  have e4 : v.toUInt8 &&& 0x3f ||| 0x80 = w := by
    apply UInt8.toNat_inj.mp
    rw [byte_enc0 v 0x3f 0x80 6 2 (by decide) (by decide), hv]
    omega
  rw [e1, e2, e3, e4]


theorem byteAt_some {a : ByteArray} {i : Nat} {x : UInt8} (h : byteAt a i = some x) : ∃ hi : i < a.size, a[i] = x := by
  by_cases hi : i < a.size
  · simp only [byteAt, hi, ↓reduceDIte, Option.some.injEq] at h
    exact ⟨hi, h⟩
  · simp [byteAt, hi] at h

theorem push_two (b a : ByteArray) (p : Nat) (hp : p + 2 ≤ a.size) : b ++ a.extract p (p + 2) = (b.push a[p]).push a[p + 1] := by
  rw [← push_extract b a p (p + 2) (by omega) (by omega), ← push_extract (b.push a[p]) a (p + 1) (p + 2) (by omega) (by omega)]
  rw [show p + 1 + 1 = p + 2 by omega, ByteArray.extract_same, ByteArray.append_empty]

theorem push_three (b a : ByteArray) (p : Nat) (hp : p + 3 ≤ a.size) : b ++ a.extract p (p + 3) = ((b.push a[p]).push a[p + 1]).push a[p + 2] := by
  rw [← push_extract b a p (p + 3) (by omega) (by omega), ← push_extract (b.push a[p]) a (p + 1) (p + 3) (by omega) (by omega),
    ← push_extract ((b.push a[p]).push a[p + 1]) a (p + 1 + 1) (p + 3) (by omega) (by omega)]
  rw [show p + 1 + 1 + 1 = p + 3 by omega, ByteArray.extract_same, ByteArray.append_empty]

theorem push_four (b a : ByteArray) (p : Nat) (hp : p + 4 ≤ a.size) : b ++ a.extract p (p + 4) = (((b.push a[p]).push a[p + 1]).push a[p + 2]).push a[p + 3] := by
  rw [← push_extract b a p (p + 4) (by omega) (by omega), ← push_extract (b.push a[p]) a (p + 1) (p + 4) (by omega) (by omega),
    ← push_extract ((b.push a[p]).push a[p + 1]) a (p + 1 + 1) (p + 4) (by omega) (by omega),
    ← push_extract (((b.push a[p]).push a[p + 1]).push a[p + 1 + 1]) a (p + 1 + 1 + 1) (p + 4) (by omega) (by omega)]
  rw [show p + 1 + 1 + 1 + 1 = p + 4 by omega, ByteArray.extract_same, ByteArray.append_empty]

/-- A multi-byte character that decodes: its scalar is at least `0x80`, it ends after its start, inside the input, and `pushChar` of the scalar appends the bytes read. -/
theorem dec_multi (a : ByteArray) (p n e : Nat) (b : ByteArray) (h : decodeUtf8A a p = some (n, e)) (x : UInt8) (hxa : byteAt a p = some x) (hx : 0x80 ≤ x.toNat) :
    0x80 ≤ n ∧ p < e ∧ e ≤ a.size ∧ pushChar b (Char.ofNat n) = b ++ a.extract p e := by
  obtain ⟨hpa, ea⟩ := byteAt_some hxa
  unfold decodeUtf8A at h
  rw [hxa] at h
  simp only [] at h
  by_cases h1 : x.toNat < 0x80
  · omega
  · simp only [h1, ↓reduceIte] at h
    by_cases h2 : 0xC2 ≤ x.toNat ∧ x.toNat ≤ 0xDF
    · simp only [h2, and_self, ↓reduceIte] at h
      rcases hb : byteAt a (p + 1) with _ | y
      · rw [hb] at h; simp at h
      · rw [hb] at h
        simp only [] at h
        by_cases h3 : Tail y
        · simp only [h3, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hn, he⟩ := h
          obtain ⟨hp1, eb⟩ := byteAt_some hb
          have h3' := h3
          unfold Tail at h3'
          refine ⟨by omega, by omega, by omega, ?_⟩
          rw [← hn, pushChar_2 b x y (by omega) (by omega) h3'.1 h3'.2, ← he, push_two b a p (by omega), ea, eb]
        · simp [h3] at h
    · simp only [h2, ↓reduceIte] at h
      by_cases h3 : 0xE0 ≤ x.toNat ∧ x.toNat ≤ 0xEF
      · simp only [h3, and_self, ↓reduceIte] at h
        rcases hb : byteAt a (p + 1) with _ | y
        · rw [hb] at h; simp at h
        · rcases hc : byteAt a (p + 2) with _ | z
          · rw [hb, hc] at h; simp at h
          · rw [hb, hc] at h
            simp only [] at h
            by_cases h4 : Second3 x y ∧ Tail z
            · simp only [h4, and_self, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨hn, he⟩ := h
              obtain ⟨hp1, eb⟩ := byteAt_some hb
              obtain ⟨hp2, ec⟩ := byteAt_some hc
              obtain ⟨⟨s1, s2, s3⟩, t2⟩ := h4
              unfold Tail at s1 t2
              refine ⟨by omega, by omega, by omega, ?_⟩
              rw [← hn, pushChar_3 b x y z h3.1 h3.2 s1 s2 s3 t2, ← he, push_three b a p (by omega), ea, eb, ec]
            · simp [h4] at h
      · simp only [h3, ↓reduceIte] at h
        by_cases h4 : 0xF0 ≤ x.toNat ∧ x.toNat ≤ 0xF4
        · simp only [h4, and_self, ↓reduceIte] at h
          rcases hb : byteAt a (p + 1) with _ | y
          · rw [hb] at h; simp at h
          · rcases hc : byteAt a (p + 2) with _ | z
            · rw [hb, hc] at h; simp at h
            · rcases hd : byteAt a (p + 3) with _ | w
              · rw [hb, hc, hd] at h; simp at h
              · rw [hb, hc, hd] at h
                simp only [] at h
                by_cases h5 : Second4 x y ∧ Tail z ∧ Tail w
                · simp only [h5, and_self, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨hn, he⟩ := h
                  obtain ⟨hp1, eb⟩ := byteAt_some hb
                  obtain ⟨hp2, ec⟩ := byteAt_some hc
                  obtain ⟨hp3, ed⟩ := byteAt_some hd
                  obtain ⟨⟨s1, s2, s3⟩, t2, t3⟩ := h5
                  unfold Tail at s1 t2 t3
                  refine ⟨by omega, by omega, by omega, ?_⟩
                  rw [← hn, pushChar_4 b x y z w h4.1 h4.2 s1 s2 s3 t2 t3, ← he, push_four b a p (by omega), ea, eb, ec, ed]
                · simp [h5] at h
        · simp only [h4, ↓reduceIte] at h
          simp at h

theorem mbRun_run (a : ByteArray) (hs : a.size < 2 ^ 31) : ∀ d q b, a.size - q = d →
    strBytes a q b = strBytes a (mbRun a q) (b ++ a.extract q (mbRun a q)) := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
    intro q b hd
    have triv : mbRun a q = q → strBytes a q b = strBytes a (mbRun a q) (b ++ a.extract q (mbRun a q)) := fun h => by
      rw [h, ByteArray.extract_same, ByteArray.append_empty]
    by_cases h : q < a.size
    · by_cases h2 : a[q].toNat < 0x80
      · exact triv (by rw [mbRun]; simp [h, h2])
      · have hm : mbRun a q = (match decodeUtf8A a q with | some (n, e) => if q < e then mbRun a (e + plainOff a e 0) else q | none => q) := by
          rw [mbRun]
          simp only [h, h2, ↓reduceDIte, ↓reduceIte]
          exact decodeUtf8K_eq _ _ _ _
        have hxa : byteAt a q = some a[q] := by simp [byteAt, h]
        cases hdec : decodeUtf8A a q with
        | none => exact triv (by rw [hm, hdec])
        | some ne =>
          obtain ⟨n, e⟩ := ne
          obtain ⟨hn80, hqe, hea, hpc⟩ := dec_multi a q n e b hdec a[q] hxa (by omega)
          have hm' : mbRun a q = mbRun a (e + plainOff a e 0) := by rw [hm, hdec]; simp [hqe]
          have s1 : strBytes a q b = strBytes a e (b ++ a.extract q e) := by
            rw [strBytes]
            simp only [h, ↓reduceDIte]
            have hq22 : (a[q] == 0x22) = false := by
              simp only [beq_eq_false_iff_ne, ne_eq]
              intro heq
              have : a[q].toNat = 0x22 := by rw [heq]; rfl
              omega
            have hpl : plainAscii a[q] = false := by unfold plainAscii; simp [h2]
            have h5c : byteIs a q 0x5C = false := by
              unfold byteIs
              simp only [h, ↓reduceDIte, beq_eq_false_iff_ne, ne_eq]
              intro heq
              have : a[q].toNat = 0x5C := by rw [heq]; rfl
              omega
            have hdc : decodeCharA a q = some (n, e) := by
              unfold decodeCharA
              simp only [h5c, Bool.false_eq_true, ↓reduceIte]
              rw [hdec]
              have : 0x20 ≤ n ∧ n ≠ 0x22 ∧ n ≠ 0x5C := by omega
              simp [this]
            simp only [hq22, hpl, Bool.false_eq_true, ↓reduceIte, hdc, hqe, hpc]
          have hrun := plainOff_run a hs _ e rfl
          have s2 : strBytes a e (b ++ a.extract q e) = strBytes a (e + plainOff a e 0) (b ++ a.extract q e ++ a.extract e (e + plainOff a e 0)) :=
            strBytes_plain a _ e _ _ rfl (by omega) hrun
          have s3 := ih (a.size - (e + plainOff a e 0)) (by omega) (e + plainOff a e 0) (b ++ a.extract q e ++ a.extract e (e + plainOff a e 0)) rfl
          have hge := mbRun_ge a _ (e + plainOff a e 0) rfl
          rw [s1, s2, s3, hm']
          generalize mbRun a (e + plainOff a e 0) = m at hge ⊢
          congr 1
          rw [ByteArray.extract_eq_extract_append_extract (i := q) (k := m) e (by omega) (by omega),
            ByteArray.extract_eq_extract_append_extract (i := e) (k := m) (e + plainOff a e 0) (by omega) hge]
          simp only [ByteArray.append_assoc]
    · exact triv (by rw [mbRun]; simp [h])

/-- The run of plain ASCII bytes and well-formed multi-byte characters at `i` is copied: `strBytes` over `a[i, runEnd a i)` appends it. -/
theorem strBytes_run (a : ByteArray) (hs : a.size < 2 ^ 31) (i : Nat) (b : ByteArray) :
    strBytes a i b = strBytes a (runEnd a i) (b ++ a.extract i (runEnd a i)) := by
  have hrun := plainOff_run a hs _ i rfl
  have hpl : strBytes a i b = strBytes a (i + plainOff a i 0) (b ++ a.extract i (i + plainOff a i 0)) :=
    strBytes_plain a _ i _ b rfl (by omega) hrun
  unfold runEnd
  by_cases h : i + plainOff a i 0 < a.size
  · simp only [h, ↓reduceDIte]
    by_cases h2 : a[i + plainOff a i 0].toNat < 0x80
    · simp only [h2, ↓reduceIte]; exact hpl
    · simp only [h2, ↓reduceIte]
      rw [hpl, mbRun_run a hs _ (i + plainOff a i 0) _ rfl]
      have hge := mbRun_ge a _ (i + plainOff a i 0) rfl
      generalize mbRun a (i + plainOff a i 0) = m at hge ⊢
      congr 1
      rw [ByteArray.extract_eq_extract_append_extract (i := i) (k := m) (i + plainOff a i 0) (by omega) hge, ByteArray.append_assoc]
  · simp only [h, ↓reduceDIte]; exact hpl

/-- `strBytes` with the runs copied at once is `strBytes`. -/
theorem strBytesW_eq (a : ByteArray) (hs : a.size < 2 ^ 31) : ∀ d i b, a.size - i = d → strBytesW a i b = strBytes a i b := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
    intro i b hd
    have hip := runEnd_ge a i
    have hpl : strBytes a i b = strBytes a (runEnd a i) (b ++ a.extract i (runEnd a i)) := strBytes_run a hs i b
    have hcp0 : a.copySlice i b b.size (runEnd a i - i) false = b ++ a.extract i (runEnd a i) := by
      rw [copy_append, show i + (runEnd a i - i) = runEnd a i by omega]
    have hcp : (if runEnd a i == i then b else a.copySlice i b b.size (runEnd a i - i) false) = b ++ a.extract i (runEnd a i) := by
      by_cases hz : (runEnd a i == i) = true
      · simp only [hz, ↓reduceIte]
        have : runEnd a i = i := by simpa using hz
        rw [this, ByteArray.extract_same, ByteArray.append_empty]
      · simp only [hz, Bool.false_eq_true, ↓reduceIte]; exact hcp0
    rw [strBytesW, hpl]
    simp only [hcp]
    generalize b ++ a.extract i (runEnd a i) = b'
    generalize hp : runEnd a i = p
    rw [hp] at hip
    by_cases hpa : p < a.size
    · simp only [hpa, ↓reduceDIte]
      rw [strBytes]
      simp only [hpa, ↓reduceDIte]
      by_cases hq : (a[p] == 0x22) = true
      · simp only [hq, ↓reduceIte]
      · simp only [hq, Bool.false_eq_true, ↓reduceIte]
        by_cases hpl2 : plainAscii a[p] = true
        · simp only [hpl2, ↓reduceIte]
          exact ih (a.size - (p + 1)) (by omega) (p + 1) _ rfl
        · simp only [hpl2, Bool.false_eq_true, ↓reduceIte]
          rw [decodeCharK_eq]
          cases hdc : decodeCharA a p with
          | none => rfl
          | some nj =>
            obtain ⟨n, j⟩ := nj
            simp only []
            by_cases hpj : p < j
            · simp only [hpj, ↓reduceIte]
              exact ih (a.size - j) (by omega) j _ rfl
            · simp only [hpj, ↓reduceIte]
    · simp only [hpa, ↓reduceDIte]
      rw [strBytes]
      simp [hpa]

theorem scanNumW_eq (a : ByteArray) (hs : a.size < 2 ^ 31) (i : Nat) : scanNumW a i = scanNum a i := by
  have e : ∀ j, scanDigitsW a j = scanDigits a j := fun j => scanDigitsW_eq a hs _ j rfl
  simp only [scanNumW, scanIntW, scanFracW, scanExpW, scanDigits1W, scanNum, scanInt, scanFrac, scanExp, scanDigits1, e]
  rfl

/-- The string leaf of `runW`: when it answers, `strBytes` answers the same, and the string ends at the first structural position after its opening quote. -/
theorem strW_sound (a : ByteArray) (hsz : a.size < 2 ^ 31) (i : Nat) (text text' : ByteArray) (j : Nat)
    (h : strW (stage1 a) a i text = some (text', j)) :
    byteIs a i 0x22 = true ∧ strBytes a (i + 1) text = some (text', j) ∧ skipI (stage1 a) a.size (i + 1) = j - 1 := by
  unfold strW at h
  by_cases hq : byteIs a i 0x22 = true
  · simp only [hq, ↓reduceIte, skipF_eq] at h
    refine ⟨hq, ?_⟩
    obtain ⟨hi, _⟩ := byteIs_spec a i _ hq
    have hfs := skipI_spec a hsz (i + 1) (by omega)
    have hr1 : i + 1 ≤ skipI (stage1 a) a.size (i + 1) := hfs.1
    by_cases hf : (i + 1 + plainOff a (i + 1) 0 == skipI (stage1 a) a.size (i + 1) && byteIs a (skipI (stage1 a) a.size (i + 1)) 0x22) = true
    · simp only [hf, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨ht, hj⟩ := h
      subst ht hj
      simp only [Bool.and_eq_true, beq_iff_eq] at hf
      have hrun : plainRun a (i + 1) (skipI (stage1 a) a.size (i + 1)) = true := by
        rw [← hf.1]; exact plainOff_run a hsz _ (i + 1) rfl
      rw [strBytes_plain a _ (i + 1) _ text rfl hr1 hrun, strBytes_quote a _ _ hf.2, copy_append]
      refine ⟨?_, by omega⟩
      rw [show i + 1 + (skipI (stage1 a) a.size (i + 1) - i - 1) = skipI (stage1 a) a.size (i + 1) by omega]
    · simp only [hf, Bool.false_eq_true, ↓reduceIte, strBytesW_eq a hsz _ _ _ rfl] at h
      cases hb : strBytes a (i + 1) text with
      | none => simp [hb] at h
      | some tj =>
        obtain ⟨t, j0⟩ := tj
        simp only [hb] at h
        by_cases hc : (skipI (stage1 a) a.size (i + 1) == j0 - 1) = true
        · simp only [hc, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨ht, hj⟩ := h
          subst ht hj
          exact ⟨rfl, by simpa using hc⟩
        · simp [hc] at h
  · simp [hq] at h


/-- A number without `E` or `+` is copied: `pushLex` over `a[p, e)` appends it. -/
theorem pushLex_plain (a : ByteArray) : ∀ d p e b, e - p = d → p ≤ e → lexRun a p e = true → pushLex a p e b = b ++ a.extract p e := by
  intro d
  induction d with
  | zero =>
    intro p e b hd hpe _
    have : p = e := by omega
    subst this
    rw [pushLex]; simp [ByteArray.extract_same, ByteArray.append_empty]
  | succ d ih =>
    intro p e b hd hpe hrun
    have hlt : p < e := by omega
    rw [lexRun] at hrun
    simp only [hlt, ↓reduceDIte] at hrun
    by_cases hps : p < a.size
    · simp only [hps, ↓reduceDIte] at hrun
      by_cases hc : (a[p] != 0x45 && a[p] != 0x2B) = true
      · simp only [hc, ↓reduceIte] at hrun
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
        rw [pushLex]
        simp only [hlt, ↓reduceIte, show byteAt a p = some a[p] by simp [byteAt, hps]]
        have h1 : (a[p] == 0x45) = false := by simpa using hc.1
        have h2 : (a[p] == 0x2B) = false := by simpa using hc.2
        simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]
        rw [ih (p + 1) e _ (by omega) (by omega) hrun, push_extract b a p e hlt hps]
      · simp [hc] at hrun
    · simp [hps] at hrun

theorem numText_eq (a : ByteArray) (hs : a.size < 2 ^ 31) (i j : Nat) (hij : i ≤ j) (hj : j ≤ a.size) (text : ByteArray) :
    (if lexOk a i j then a.copySlice i text text.size (j - i) false else pushLex a i j text) = pushLex a i j text := by
  rw [lexOk_eq a hs j hj i]
  by_cases h : lexRun a i j = true
  · simp only [h, ↓reduceIte]
    rw [copy_append, pushLex_plain a _ i j text rfl hij h, show i + (j - i) = j by omega]
  · simp [h]


/-! ## String and number nodes -/

/-- The node of a string or a number: header word and offset word, and the new text. -/
theorem Rel_str {tape tw text tb} (hr : Rel tape tw text tb) (htw : tw + 1 < 2 ^ 32) (kind : Nat) (k : UInt64) (hk : k = UInt64.ofNat kind) (text' : ByteArray) :
    Rel (putNode tape tw (hdrW k (text'.size - text.size)) (UInt64.ofNat text.size)) (tw + 2) text'
      ⟨pushWordFast (pushWordFast tb.tape (UInt64.ofNat (kind + (text'.size - tb.text.size) * 256))) (UInt64.ofNat tb.text.size), text'⟩ := by
  have := Rel_put hr htw (hdrW k (text'.size - text.size)) (UInt64.ofNat text.size) text'
  rw [hk, hdrW_eq] at this ⊢
  rw [hr.tx]
  simpa only [pushWordFast_eq] using this

theorem strNodeI_eq (a : ByteArray) (hsz : a.size < 2 ^ 31) (tb : TapeBuf) (kind i : Nat) (text' : ByteArray) (j : Nat)
    (h : strW (stage1 a) a i tb.text = some (text', j)) :
    tb.strNodeI kind (stage1 a) a i =
      some (⟨pushWordFast (pushWordFast tb.tape (UInt64.ofNat (kind + (text'.size - tb.text.size) * 256))) (UInt64.ofNat tb.text.size), text'⟩, j) := by
  obtain ⟨h1, h2, h3⟩ := strW_sound a hsz i tb.text text' j h
  obtain ⟨tape, text⟩ := tb
  simp only [] at h1 h2 h3 h ⊢
  unfold TapeBuf.strNodeI TapeBuf.strNode
  simp only [h1, ↓reduceIte, h2, h3]
  simp

theorem keyNodeI_eq (a : ByteArray) (hsz : a.size < 2 ^ 31) (tb : TapeBuf) (i : Nat) (text' : ByteArray) (j : Nat)
    (h : strW (stage1 a) a i tb.text = some (text', j)) :
    tb.keyNodeI (stage1 a) a i =
      if byteIs a (skipI (stage1 a) a.size j) 0x3A then
        some (⟨pushWordFast (pushWordFast tb.tape (UInt64.ofNat (kindStr + (text'.size - tb.text.size) * 256))) (UInt64.ofNat tb.text.size), text'⟩, skipI (stage1 a) a.size (skipI (stage1 a) a.size j + 1))
      else none := by
  unfold TapeBuf.keyNodeI
  rw [strNodeI_eq a hsz tb kindStr i text' j h]


/-! ## The simulation -/

/-- Every open container's header is within the words written. -/
def FOk : FStack → Nat → Prop
  | .nil, _ => True
  | .arr at_ _ rest, tw => at_ + 2 ≤ tw ∧ FOk rest tw
  | .obj at_ _ rest, tw => at_ + 2 ≤ tw ∧ FOk rest tw

theorem FOk.mono : ∀ {fst : FStack} {tw tw' : Nat}, tw ≤ tw' → FOk fst tw → FOk fst tw'
  | .nil, _, _, _, _ => trivial
  | .arr _ _ rest, _, _, h, ⟨h1, h2⟩ => ⟨by omega, FOk.mono h h2⟩
  | .obj _ _ rest, _, _, h, ⟨h1, h2⟩ => ⟨by omega, FOk.mono h h2⟩

/-- When `runW` answers, `runI` answers the same bytes. -/
theorem runW_sound (a : ByteArray) (hsz : a.size < 2 ^ 31) : ∀ f i ret tape tw text fst d tb t, tw + 4 * f < 2 ^ 32 → Rel tape tw text tb → FOk fst tw →
    runW (stage1 a) f a i ret tape tw text fst d = some t → runI (stage1 a) f a i ret tb fst d = some t := by
  intro f
  induction f with
  | zero => intro i ret tape tw text fst d tb t _ _ _ h; simp [runW] at h
  | succ f ih =>
    intro i ret tape tw text fst d tb t hb hr hf h
    cases ret with
    | false =>
      rw [runW] at h
      rw [runI]
      cases hbyte : byteAt a i with
      | none => simp [hbyte] at h
      | some b =>
        simp only [hbyte] at h ⊢
        by_cases h5b : (b == 0x5B) = true
        · simp only [h5b, ↓reduceIte] at h ⊢
          by_cases hd : (d == 0) = true
          · simp [hd] at h
          · simp only [hd, Bool.false_eq_true, ↓reduceIte, skipF_eq] at h ⊢
            by_cases h5d : byteIs a (skipI (stage1 a) a.size (i + 1)) 0x5D = true
            · simp only [h5d, ↓reduceIte] at h ⊢
              exact ih _ true _ _ _ _ _ _ t (by omega) (Rel_node hr (by omega) kindArr 5 rfl 0 2) (hf.mono (by omega)) h
            · simp only [h5d, Bool.false_eq_true, ↓reduceIte] at h ⊢
              have hr' := Rel_node hr (by omega) kindArr 5 rfl 0 0
              rw [hr.words]
              exact ih _ false _ _ _ _ _ _ t (by omega) hr' ⟨Nat.le_refl _, hf.mono (by omega)⟩ h
        · simp only [h5b, Bool.false_eq_true, ↓reduceIte] at h ⊢
          by_cases h7b : (b == 0x7B) = true
          · simp only [h7b, ↓reduceIte] at h ⊢
            by_cases hd : (d == 0) = true
            · simp [hd] at h
            · simp only [hd, Bool.false_eq_true, ↓reduceIte, skipF_eq] at h ⊢
              by_cases h7d : byteIs a (skipI (stage1 a) a.size (i + 1)) 0x7D = true
              · simp only [h7d, ↓reduceIte] at h ⊢
                exact ih _ true _ _ _ _ _ _ t (by omega) (Rel_node hr (by omega) kindObj 6 rfl 0 2) (hf.mono (by omega)) h
              · simp only [h7d, Bool.false_eq_true, ↓reduceIte] at h ⊢
                have hr1 := Rel_node hr (by omega) kindObj 6 rfl 0 0
                have hx1 := hr1.tx
                cases hs : strW (stage1 a) a (skipI (stage1 a) a.size (i + 1)) text with
                | none => simp [hs] at h
                | some tj =>
                  obtain ⟨text', j⟩ := tj
                  simp only [hs] at h
                  have hs' : strW (stage1 a) a (skipI (stage1 a) a.size (i + 1)) (tb.node kindObj 0 0).text = some (text', j) := by rw [hx1]; exact hs
                  rw [keyNodeI_eq a hsz _ _ text' j hs']
                  by_cases hc : byteIs a (skipI (stage1 a) a.size j) 0x3A = true
                  · simp only [hc, ↓reduceIte] at h ⊢
                    have hr2 := Rel_str hr1 (by omega) kindStr 4 rfl text'
                    rw [hr.words]
                    exact ih _ false _ _ _ _ _ _ t (by omega) hr2 ⟨by omega, hf.mono (by omega)⟩ h
                  · simp [hc] at h
          · simp only [h7b, Bool.false_eq_true, ↓reduceIte] at h ⊢
            by_cases h22 : (b == 0x22) = true
            · simp only [h22, ↓reduceIte] at h ⊢
              cases hs : strW (stage1 a) a i text with
              | none => simp [hs] at h
              | some tj =>
                obtain ⟨text', j⟩ := tj
                simp only [hs] at h
                have hs' : strW (stage1 a) a i tb.text = some (text', j) := by rw [hr.tx]; exact hs
                rw [strNodeI_eq a hsz tb kindStr i text' j hs']
                exact ih _ true _ _ _ _ _ _ t (by omega) (Rel_str hr (by omega) kindStr 4 rfl text') (hf.mono (by omega)) h
            · simp only [h22, Bool.false_eq_true, ↓reduceIte] at h ⊢
              by_cases h6e : (b == 0x6E) = true
              · simp only [h6e, ↓reduceIte] at h ⊢
                cases hl : litA a (i + 1) [0x75, 0x6C, 0x6C] with
                | none => simp [hl] at h
                | some k =>
                  simp only [hl] at h ⊢
                  by_cases hdl : delimAt a k = true
                  · simp only [hdl, ↓reduceIte] at h ⊢
                    exact ih _ true _ _ _ _ _ _ t (by omega) (Rel_node hr (by omega) kindNull 0 rfl 0 0) (hf.mono (by omega)) h
                  · simp [hdl] at h
              · simp only [h6e, Bool.false_eq_true, ↓reduceIte] at h ⊢
                by_cases h74 : (b == 0x74) = true
                · simp only [h74, ↓reduceIte] at h ⊢
                  cases hl : litA a (i + 1) [0x72, 0x75, 0x65] with
                  | none => simp [hl] at h
                  | some k =>
                    simp only [hl] at h ⊢
                    by_cases hdl : delimAt a k = true
                    · simp only [hdl, ↓reduceIte] at h ⊢
                      exact ih _ true _ _ _ _ _ _ t (by omega) (Rel_node hr (by omega) kindTrue 2 rfl 0 0) (hf.mono (by omega)) h
                    · simp [hdl] at h
                · simp only [h74, Bool.false_eq_true, ↓reduceIte] at h ⊢
                  by_cases h66 : (b == 0x66) = true
                  · simp only [h66, ↓reduceIte] at h ⊢
                    cases hl : litA a (i + 1) [0x61, 0x6C, 0x73, 0x65] with
                    | none => simp [hl] at h
                    | some k =>
                      simp only [hl] at h ⊢
                      by_cases hdl : delimAt a k = true
                      · simp only [hdl, ↓reduceIte] at h ⊢
                        exact ih _ true _ _ _ _ _ _ t (by omega) (Rel_node hr (by omega) kindFalse 1 rfl 0 0) (hf.mono (by omega)) h
                      · simp [hdl] at h
                  · simp only [h66, Bool.false_eq_true, ↓reduceIte, scanNumW_eq a hsz] at h ⊢
                    cases hn : scanNum a i with
                    | none => simp [hn] at h
                    | some k =>
                      simp only [hn] at h ⊢
                      by_cases hdl : delimAt a k = true
                      · simp only [hdl, ↓reduceIte] at h ⊢
                        rw [numText_eq a hsz i k (Nat.le_of_lt (scanNum_adv a i k hn)) ((scanNum_run a i k hn).2.1 (Nat.le_of_lt (byteAt_spec a i b hbyte).1)) text] at h
                        have hnl : tb.numLex a i k = ⟨pushWordFast (pushWordFast tb.tape (UInt64.ofNat (kindNum + ((pushLex a i k text).size - tb.text.size) * 256))) (UInt64.ofNat tb.text.size), pushLex a i k text⟩ := by
                          obtain ⟨tape0, text0⟩ := tb
                          have := hr.tx
                          simp only [] at this
                          subst this
                          rfl
                        rw [hnl]
                        exact ih _ true _ _ _ _ _ _ t (by omega) (Rel_str hr (by omega) kindNum 3 rfl _) (hf.mono (by omega)) h
                      · simp [hdl] at h
    | true =>
      cases fst with
      | nil =>
        rw [runW] at h
        rw [runI]
        simp only [skipF_eq] at h
        by_cases hc : a.size ≤ skipI (stage1 a) a.size i
        · simp only [hc, ↓reduceIte, Option.some.injEq] at h ⊢
          rw [← h, finishW_eq hr]
        · simp [hc] at h
      | arr at_ n rest =>
        rw [runW] at h
        rw [runI]
        simp only [skipF_eq] at h
        by_cases hcomma : byteIs a (skipI (stage1 a) a.size i) 0x2C = true
        · simp only [hcomma, ↓reduceIte] at h ⊢
          exact ih _ false _ _ _ _ _ _ t (by omega) hr ⟨hf.1, hf.2⟩ h
        · simp only [hcomma, Bool.false_eq_true, ↓reduceIte] at h ⊢
          by_cases hclose : byteIs a (skipI (stage1 a) a.size i) 0x5D = true
          · simp only [hclose, ↓reduceIte] at h ⊢
            exact ih _ true _ _ _ _ _ _ t (by omega) (Rel_close hr at_ (by have := hf.1; omega) (by omega) kindArr 5 rfl (n + 1)) hf.2 h
          · simp [hclose] at h
      | obj at_ n rest =>
        rw [runW] at h
        rw [runI]
        simp only [skipF_eq] at h
        by_cases hcomma : byteIs a (skipI (stage1 a) a.size i) 0x2C = true
        · simp only [hcomma, ↓reduceIte] at h ⊢
          cases hs : strW (stage1 a) a (skipI (stage1 a) a.size (skipI (stage1 a) a.size i + 1)) text with
          | none => simp [hs] at h
          | some tj =>
            obtain ⟨text', j⟩ := tj
            simp only [hs] at h
            have hs' : strW (stage1 a) a (skipI (stage1 a) a.size (skipI (stage1 a) a.size i + 1)) tb.text = some (text', j) := by rw [hr.tx]; exact hs
            rw [keyNodeI_eq a hsz _ _ text' j hs']
            by_cases hc : byteIs a (skipI (stage1 a) a.size j) 0x3A = true
            · simp only [hc, ↓reduceIte] at h ⊢
              exact ih _ false _ _ _ _ _ _ t (by omega) (Rel_str hr (by omega) kindStr 4 rfl text') ⟨by have := hf.1; omega, hf.2.mono (by omega)⟩ h
            · simp [hc] at h
        · simp only [hcomma, Bool.false_eq_true, ↓reduceIte] at h ⊢
          by_cases hclose : byteIs a (skipI (stage1 a) a.size i) 0x7D = true
          · simp only [hclose, ↓reduceIte] at h ⊢
            exact ih _ true _ _ _ _ _ _ t (by omega) (Rel_close hr at_ (by have := hf.1; omega) (by omega) kindObj 6 rfl (n + 1)) hf.2 h
          · simp [hclose] at h

end LeanJsonProofs
