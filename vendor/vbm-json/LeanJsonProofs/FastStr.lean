import LeanJsonProofs.FastTape
import LeanJsonProofs.FastLeaf
/-! # F2: the string scan writes the UTF-8 of the string `strLoop` builds

`strBytes_eq`: reading the same characters, `strBytes` ends at the same index as `strLoop` and the text it has written is the text it started with plus the UTF-8 of the string `strLoop` returns.
`strNode_eq`: the node written for a string is `TapeBuf.leaf kindStr` of the string `parseStrA` reads (and there is no node exactly when there is no string). -/
set_option linter.unusedSimpArgs false
namespace LeanJson

theorem ofNat_val {n : Nat} (h : n < 0xD800) : (Char.ofNat n).val.toNat = n := by
  have : n.isValidChar := Or.inl h
  simp [Char.ofNat, this, Char.ofNatAux]
theorem enc_ascii (x : UInt8) (h : x.toNat < 0x80) : String.utf8EncodeChar (Char.ofNat x.toNat) = [x] := by
  have hv := ofNat_val (n := x.toNat) (by omega)
  have hs : (Char.ofNat x.toNat).utf8Size = 1 := by
    rw [Char.utf8Size_eq_one_iff, UInt32.le_iff_toNat_le]
    simp only [hv]; simp; omega
  rw [String.utf8EncodeChar_eq_singleton hs]
  congr 1
  apply UInt8.toNat_inj.mp
  rw [UInt32.toNat_toUInt8, hv]
  omega

theorem pushChar_list (b : ByteArray) (c : Char) : (pushChar b c).data.toList = b.data.toList ++ String.utf8EncodeChar c := by
  rw [String.utf8EncodeChar_eq_utf8EncodeCharFast]
  unfold pushChar String.utf8EncodeCharFast
  dsimp only
  split <;> (try split) <;> (try split) <;> simp [push_list]

theorem push_toUTF8 (s : String) (c : Char) : (s.push c).toUTF8.data.toList = s.toUTF8.data.toList ++ String.utf8EncodeChar c := by
  simp [String.toUTF8_eq_toByteArray, String.toByteArray_push, List.utf8Encode_singleton]

theorem empty_toUTF8 : "".toUTF8.data.toList = [] := by
  simp [String.toUTF8_eq_toByteArray]

theorem strBytes_eq (a : ByteArray) (i : Nat) (s : String) (b : ByteArray) (P : List UInt8) (hb : b.data.toList = P ++ s.toUTF8.data.toList) :
    (strBytes a i b).map (fun p => (p.1.data.toList, p.2)) = (strLoop a i s).map (fun p => (P ++ p.1.toUTF8.data.toList, p.2)) := by
  induction i, s using strLoop.induct a generalizing b with
  | case1 i s h h22 => rw [strLoop, strBytes]; simp [h, h22, hb]
  | case2 i s h h22 hp ih =>
    rw [strLoop, strBytes]
    simp only [h, h22, hp, ite_true, dite_true]
    have hlt : a[i].toNat < 0x80 := by simp only [plainAscii, Bool.and_eq_true, decide_eq_true_eq] at hp; omega
    exact ih _ (by rw [push_list, push_toUTF8, hb, enc_ascii _ hlt]; simp)
  | case3 i s h h22 hp n j hd hij ih =>
    rw [strLoop, strBytes]
    simp only [h, hij, hp, hd, h22, ite_true, dite_true, Bool.false_eq_true, ite_false]
    exact ih _ (by rw [pushChar_list, push_toUTF8, hb]; simp)
  | case4 i s h h22 hp n j hd hij => exact absurd (decodeCharA_adv hd) hij
  | case5 i s h h22 hp hd => rw [strLoop, strBytes]; simp [h, h22, hp, hd]
  | case6 i s h => rw [strLoop, strBytes]; simp [h]

/-- F2: the string node written from the input is the leaf of the string `parseStrA` reads. -/
theorem strNode_eq (kind : Nat) (a : ByteArray) (i : Nat) (s : TapeBuf) :
    s.strNode kind a i = (parseStrA a i).map (fun p => (s.leaf kind p.1.toUTF8, p.2)) := by
  obtain ⟨tape, text⟩ := s
  unfold TapeBuf.strNode parseStrA
  by_cases hq : byteIs a i 0x22 = true
  · simp only [hq, ite_true]
    have h := strBytes_eq a (i + 1) "" text text.data.toList (by rw [empty_toUTF8]; simp)
    rcases hl : strLoop a (i + 1) "" with _ | ⟨s', j⟩
    · rw [hl] at h
      rcases hb : strBytes a (i + 1) text with _ | ⟨t, j'⟩
      · simp
      · rw [hb] at h; simp at h
    · rw [hl] at h
      rcases hb : strBytes a (i + 1) text with _ | ⟨t, j'⟩
      · rw [hb] at h; simp at h
      · rw [hb] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨h1, h2⟩ := h
        have ht : t = text ++ s'.toUTF8 := by
          apply ByteArray.ext; apply Array.toList_inj.mp
          simp [ByteArray.data_append, h1]
        subst ht h2
        simp only [Option.map_some, TapeBuf.leaf, TapeBuf.node, ByteArray.size_append, Nat.add_sub_cancel_left]
  · simp [hq]

end LeanJson
