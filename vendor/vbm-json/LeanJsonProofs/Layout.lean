import LeanJsonProofs.Tape
/-! # The tape layout as a pure function (the layout theorem)

`encValue` (`LeanJson/Tape.lean`) builds the tape with a stateful `TapeBuf`. Here the layout is stated without it: `tapeV o v` is the bytes of the tape of `v` when its texts start at text offset `o`,
`textV v` is its text region; `wordsV v` is its size in words. `encValue_layout`: for a buffer whose tape is a whole number of words, `encValue v s` is `s` extended by `tapeV s.text.size v` and `textV v`.
That is the layout theorem the ledger claim `tape-encode-decode` wants (the tape of a value is a function of the value alone, up to the text offset), and the lemmas the fused parser's refinement proof
(`docs/perf/fuse-plan.md`) is built from. -/
set_option linter.unusedSimpArgs false
namespace LeanJson

/-- A word, little-endian, as bytes. -/
def wordBytes (w : UInt64) : List UInt8 :=
  [w.toUInt8, (w >>> 8).toUInt8, (w >>> 16).toUInt8, (w >>> 24).toUInt8, (w >>> 32).toUInt8, (w >>> 40).toUInt8, (w >>> 48).toUInt8, (w >>> 56).toUInt8]

/-- The two words of a node. -/
def hdrBytes (kind len aux : Nat) : List UInt8 := wordBytes (UInt64.ofNat (kind + len * 256)) ++ wordBytes (UInt64.ofNat aux)

theorem wordBytes_length (w : UInt64) : (wordBytes w).length = 8 := rfl
theorem hdrBytes_length (kind len aux : Nat) : (hdrBytes kind len aux).length = 16 := by simp [hdrBytes, wordBytes_length]

theorem push_list (b : ByteArray) (x : UInt8) : (b.push x).data.toList = b.data.toList ++ [x] := by
  simp [ByteArray.data_push]

theorem pushWordFast_list (b : ByteArray) (w : UInt64) : (pushWordFast b w).data.toList = b.data.toList ++ wordBytes w := by
  rw [pushWordFast_eq]
  unfold pushWord wordBytes
  simp only [push_list, List.append_assoc, List.cons_append, List.nil_append]

theorem size_list (b : ByteArray) : b.size = b.data.toList.length := (Array.length_toList).symm

theorem pushWordFast_size (b : ByteArray) (w : UInt64) : (pushWordFast b w).size = b.size + 8 := by
  rw [size_list, pushWordFast_list, List.length_append, wordBytes_length, ← size_list]

/-- Store the elements of `xs` at `k`, `k+1`, ... (the shape of `setWord`'s eight stores). -/
def setMany {α : Type} (l : List α) (k : Nat) : List α → List α
  | [] => l
  | x :: xs => setMany (l.set k x) (k + 1) xs

theorem setMany_eq {α : Type} (xs : List α) : ∀ (l : List α) (k : Nat), k + xs.length ≤ l.length →
    setMany l k xs = l.take k ++ xs ++ l.drop (k + xs.length) := by
  induction xs with
  | nil => intro l k _; simp [setMany]
  | cons x xs ih =>
    intro l k h
    simp only [setMany, List.length_cons] at h ⊢
    rw [ih _ _ (by simp; omega), List.set_eq_take_append_cons_drop]
    have hk : (List.take k l).length = k := by simp; omega
    have hlk : k < l.length := by omega
    simp only [hlk, ite_true, List.take_append, List.drop_append, hk, List.length_cons, List.length_take, List.length_drop]
    simp [List.take_add_one]
    have e1 : List.take k (List.take k l) = List.take k l := List.take_of_length_le (by omega)
    have e2 : (List.take k l)[k]? = none := List.getElem?_eq_none (by omega)
    have e3 : List.drop (k + 1 + xs.length) (List.take k l) = [] := List.drop_eq_nil_of_le (by omega)
    have e4 : k + 1 + xs.length - k = xs.length + 1 := by omega
    have e5 : List.drop (xs.length + 1) (x :: List.drop (k + 1) l) = List.drop (k + (xs.length + 1)) l := by
      rw [List.drop_succ_cons, List.drop_drop]; congr 1; omega
    rw [e1, e2, e3, e4, e5]; simp

/-- The eight stores of `setWord` replace the eight bytes of the word. -/
theorem setWord_list (b : ByteArray) (i : Nat) (w : UInt64) (h : 8 * i + 8 ≤ b.size) :
    (setWord b i w).data.toList = b.data.toList.take (8 * i) ++ wordBytes w ++ b.data.toList.drop (8 * i + 8) := by
  have hl : 8 * i + 8 ≤ b.data.toList.length := by rw [← size_list]; exact h
  have e : (setWord b i w).data.toList = setMany b.data.toList (8 * i) (wordBytes w) := by
    simp only [setWord, ByteArray.set!, Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds, wordBytes, setMany]
  rw [e, setMany_eq _ _ _ (by rw [wordBytes_length]; exact hl), wordBytes_length]

theorem setWord_size (b : ByteArray) (i : Nat) (w : UInt64) (h : 8 * i + 8 ≤ b.size) : (setWord b i w).size = b.size := by
  have := congrArg List.length (setWord_list b i w h)
  simp only [List.length_append, List.length_take, List.length_drop, wordBytes_length] at this
  rw [← size_list] at this
  rw [size_list (setWord b i w), size_list b] at *
  omega

mutual
/-- The size of the tape of a value, in words. -/
def wordsV : Value → Nat
  | .arr xs => 2 + wordsL xs
  | .obj ms => 2 + wordsM ms
  | _ => 2
def wordsL : List Value → Nat
  | [] => 0
  | v :: vs => wordsV v + wordsL vs
def wordsM : List (String × Value) → Nat
  | [] => 0
  | (_, v) :: ms => 2 + wordsV v + wordsM ms
end

mutual
/-- The text region of a value: the concatenation of the texts, in document order. -/
def textV : Value → List UInt8
  | .num n => printNumber n
  | .str s => s.toUTF8.data.toList
  | .arr xs => textL xs
  | .obj ms => textM ms
  | _ => []
def textL : List Value → List UInt8
  | [] => []
  | v :: vs => textV v ++ textL vs
def textM : List (String × Value) → List UInt8
  | [] => []
  | (k, v) :: ms => k.toUTF8.data.toList ++ textV v ++ textM ms
end

mutual
/-- The tape of a value, as bytes, when the next text byte goes at offset `o`. -/
def tapeV (o : Nat) : Value → List UInt8
  | .null => hdrBytes kindNull 0 0
  | .bool false => hdrBytes kindFalse 0 0
  | .bool true => hdrBytes kindTrue 0 0
  | .num n => hdrBytes kindNum (printNumber n).length o
  | .str s => hdrBytes kindStr s.toUTF8.size o
  | .arr xs => hdrBytes kindArr xs.length (wordsV (.arr xs)) ++ tapeL o xs
  | .obj ms => hdrBytes kindObj ms.length (wordsV (.obj ms)) ++ tapeM o ms
def tapeL (o : Nat) : List Value → List UInt8
  | [] => []
  | v :: vs => tapeV o v ++ tapeL (o + (textV v).length) vs
def tapeM (o : Nat) : List (String × Value) → List UInt8
  | [] => []
  | (k, v) :: ms => hdrBytes kindStr k.toUTF8.size o ++ tapeV (o + k.toUTF8.size) v ++ tapeM (o + k.toUTF8.size + (textV v).length) ms
end

mutual
theorem tapeV_length (o : Nat) : (v : Value) → (tapeV o v).length = 8 * wordsV v
  | .null => by simp [tapeV, wordsV, hdrBytes_length]
  | .bool false => by simp [tapeV, wordsV, hdrBytes_length]
  | .bool true => by simp [tapeV, wordsV, hdrBytes_length]
  | .num n => by simp [tapeV, wordsV, hdrBytes_length]
  | .str s => by simp [tapeV, wordsV, hdrBytes_length]
  | .arr xs => by simp only [tapeV, wordsV, List.length_append, hdrBytes_length, tapeL_length o xs]; omega
  | .obj ms => by simp only [tapeV, wordsV, List.length_append, hdrBytes_length, tapeM_length o ms]; omega
theorem tapeL_length (o : Nat) : (vs : List Value) → (tapeL o vs).length = 8 * wordsL vs
  | [] => by simp [tapeL, wordsL]
  | v :: vs => by simp only [tapeL, wordsL, List.length_append, tapeV_length o v, tapeL_length (o + (textV v).length) vs]; omega
theorem tapeM_length (o : Nat) : (ms : List (String × Value)) → (tapeM o ms).length = 8 * wordsM ms
  | [] => by simp [tapeM, wordsM]
  | (k, v) :: ms => by
    simp only [tapeM, wordsM, List.length_append, hdrBytes_length, tapeV_length (o + k.toUTF8.size) v, tapeM_length (o + k.toUTF8.size + (textV v).length) ms]; omega
end

theorem node_tape (s : TapeBuf) (kind len aux : Nat) :
    (s.node kind len aux).tape.data.toList = s.tape.data.toList ++ hdrBytes kind len aux := by
  simp [TapeBuf.node, pushWordFast_list, hdrBytes, List.append_assoc]

theorem node_tape_size (s : TapeBuf) (kind len aux : Nat) : (s.node kind len aux).tape.size = s.tape.size + 16 := by
  simp only [TapeBuf.node, pushWordFast_size]

theorem leaf_tape (s : TapeBuf) (kind : Nat) (t : ByteArray) :
    (s.leaf kind t).tape.data.toList = s.tape.data.toList ++ hdrBytes kind t.size s.text.size := by
  simp [TapeBuf.leaf, node_tape]

theorem leaf_text (s : TapeBuf) (kind : Nat) (t : ByteArray) :
    (s.leaf kind t).text.data.toList = s.text.data.toList ++ t.data.toList := by
  simp [TapeBuf.leaf, TapeBuf.node]

theorem leaf_tape_size (s : TapeBuf) (kind : Nat) (t : ByteArray) : (s.leaf kind t).tape.size = s.tape.size + 16 := by
  simp only [TapeBuf.leaf, TapeBuf.node, pushWordFast_size]

/-- The subtree-size word of a closed node. -/
theorem close_list (s : TapeBuf) (at_ : Nat) (h : 8 * (at_ + 1) + 8 ≤ s.tape.size) :
    (s.close at_).tape.data.toList = s.tape.data.toList.take (8 * (at_ + 1)) ++ wordBytes (UInt64.ofNat (s.words - at_)) ++ s.tape.data.toList.drop (8 * (at_ + 1) + 8) := by
  exact setWord_list s.tape (at_ + 1) _ h

theorem close_text (s : TapeBuf) (at_ : Nat) : (s.close at_).text = s.text := by simp only [TapeBuf.close]

theorem patch_aux (P H1 H2 W C : List UInt8) (k : Nat) (hP : P.length = 8 * k) (h1 : H1.length = 8) (h2 : H2.length = 8) :
    (P ++ (H1 ++ H2) ++ C).take (8 * (k + 1)) ++ W ++ (P ++ (H1 ++ H2) ++ C).drop (8 * (k + 1) + 8) = P ++ (H1 ++ W) ++ C := by
  have e1 : P ++ (H1 ++ H2) ++ C = (P ++ H1) ++ (H2 ++ C) := by simp
  have e2 : P ++ (H1 ++ H2) ++ C = ((P ++ H1) ++ H2) ++ C := by simp
  rw [e2, List.drop_left' (by simp [hP, h1, h2]; omega)]
  rw [← e2, e1, List.take_left' (by simp [hP, h1]; omega)]
  simp

/-- A buffer is well formed when its tape is a whole number of words. -/
abbrev TapeBuf.WF (s : TapeBuf) : Prop := s.tape.size % 8 = 0

theorem node_wf {s : TapeBuf} (h : s.WF) (kind len aux : Nat) : (s.node kind len aux).WF := by
  unfold TapeBuf.WF at *; rw [node_tape_size]; omega

theorem leaf_wf {s : TapeBuf} (h : s.WF) (kind : Nat) (t : ByteArray) : (s.leaf kind t).WF := by
  unfold TapeBuf.WF at *; rw [leaf_tape_size]; omega

theorem leaf_text_size (s : TapeBuf) (kind : Nat) (t : ByteArray) : (s.leaf kind t).text.size = s.text.size + t.size := by
  simp [TapeBuf.leaf, TapeBuf.node, ByteArray.size_append]

theorem node_text (s : TapeBuf) (kind len aux : Nat) : (s.node kind len aux).text = s.text := by simp only [TapeBuf.node]

theorem size_mk (l : List UInt8) : (ByteArray.mk l.toArray).size = l.length := by simp [ByteArray.size]

theorem words_wf {s : TapeBuf} (hs : s.WF) : 8 * s.words = s.tape.size := by
  unfold TapeBuf.WF at hs; unfold TapeBuf.words; omega

theorem wf_ext {s t : TapeBuf} (hs : s.WF) {T : List UInt8} (h : t.tape.data.toList = s.tape.data.toList ++ T) (hT : T.length % 8 = 0) : t.WF := by
  unfold TapeBuf.WF at *
  rw [size_list t.tape, h, size_list s.tape] at *
  simp only [List.length_append]; omega

/-- Closing a container: the node's header words are patched; the layout is the closed node's. `C` is what was written after the (placeholder) header. -/
theorem close_layout (s r : TapeBuf) (kind n : Nat) (C : List UInt8) (hs : s.WF) (hC : C.length % 8 = 0)
    (hr : r.tape.data.toList = s.tape.data.toList ++ hdrBytes kind n 0 ++ C) :
    (r.close s.words).tape.data.toList = s.tape.data.toList ++ hdrBytes kind n (2 + C.length / 8) ++ C := by
  have hk := words_wf hs
  have hsz : r.tape.size = s.tape.size + 16 + C.length := by
    rw [size_list r.tape, hr, size_list s.tape]; simp [hdrBytes_length]; omega
  have hsl : s.tape.data.toList.length = 8 * s.words := by rw [← size_list]; omega
  have hw : r.words - s.words = 2 + C.length / 8 := by unfold TapeBuf.words at *; omega
  rw [close_list r s.words (by omega), hr, hw]
  unfold hdrBytes
  rw [patch_aux _ _ _ _ _ s.words hsl (wordBytes_length _) (wordBytes_length _)]

mutual
/-- The layout theorem, for a value: the tape is the old tape and `tapeV`, the text region is the old one and `textV`. -/
theorem encValue_layout : (v : Value) → (s : TapeBuf) → s.WF →
    (encValue v s).tape.data.toList = s.tape.data.toList ++ tapeV s.text.size v ∧ (encValue v s).text.data.toList = s.text.data.toList ++ textV v
  | .null, s, _ => by simp [encValue, tapeV, textV, node_tape, node_text]
  | .bool false, s, _ => by simp [encValue, tapeV, textV, node_tape, node_text]
  | .bool true, s, _ => by simp [encValue, tapeV, textV, node_tape, node_text]
  | .num n, s, _ => by
    rw [encValue, TapeBuf.num_eq]
    simp [tapeV, textV, leaf_tape, leaf_text, size_mk]
  | .str t, s, _ => by
    rw [encValue]
    simp [tapeV, textV, leaf_tape, leaf_text]
  | .arr xs, s, hs => by
    have ht := node_wf hs kindArr xs.length 0
    obtain ⟨h1, h2⟩ := encList_layout xs (s.node kindArr xs.length 0) ht
    rw [node_tape, node_text] at h1
    rw [node_text] at h2
    have hC : (tapeL s.text.size xs).length = 8 * wordsL xs := tapeL_length _ _
    rw [encValue]
    refine ⟨?_, ?_⟩
    · rw [close_layout s _ kindArr xs.length _ hs (by omega) h1, hC]
      simp [tapeV, wordsV]
    · simpa [close_text, node_text, textV] using h2
  | .obj ms, s, hs => by
    have ht := node_wf hs kindObj ms.length 0
    obtain ⟨h1, h2⟩ := encMembers_layout ms (s.node kindObj ms.length 0) ht
    rw [node_tape, node_text] at h1
    rw [node_text] at h2
    have hC : (tapeM s.text.size ms).length = 8 * wordsM ms := tapeM_length _ _
    rw [encValue]
    refine ⟨?_, ?_⟩
    · rw [close_layout s _ kindObj ms.length _ hs (by omega) h1, hC]
      simp [tapeV, wordsV]
    · simpa [close_text, node_text, textV] using h2
theorem encList_layout : (vs : List Value) → (s : TapeBuf) → s.WF →
    (encList vs s).tape.data.toList = s.tape.data.toList ++ tapeL s.text.size vs ∧ (encList vs s).text.data.toList = s.text.data.toList ++ textL vs
  | [], s, _ => by simp [encList, tapeL, textL]
  | v :: vs, s, hs => by
    obtain ⟨h1, h2⟩ := encValue_layout v s hs
    have hs' : (encValue v s).WF := wf_ext hs h1 (by rw [tapeV_length]; omega)
    obtain ⟨h3, h4⟩ := encList_layout vs (encValue v s) hs'
    have hsz : (encValue v s).text.size = s.text.size + (textV v).length := by
      rw [size_list (encValue v s).text, h2, List.length_append, ← size_list s.text]
    rw [encList]
    refine ⟨?_, ?_⟩
    · rw [h3, h1, hsz]; simp [tapeL]
    · rw [h4, h2]; simp [textL]
theorem encMembers_layout : (ms : List (String × Value)) → (s : TapeBuf) → s.WF →
    (encMembers ms s).tape.data.toList = s.tape.data.toList ++ tapeM s.text.size ms ∧ (encMembers ms s).text.data.toList = s.text.data.toList ++ textM ms
  | [], s, _ => by simp [encMembers, tapeM, textM]
  | (k, v) :: ms, s, hs => by
    have hl := leaf_wf hs kindStr k.toUTF8
    obtain ⟨h1, h2⟩ := encValue_layout v (s.leaf kindStr k.toUTF8) hl
    have hu : (encValue v (s.leaf kindStr k.toUTF8)).WF := wf_ext hl h1 (by rw [tapeV_length]; omega)
    rw [leaf_tape, leaf_text_size] at h1
    rw [leaf_text] at h2
    obtain ⟨h3, h4⟩ := encMembers_layout ms _ hu
    have hsz : (encValue v (s.leaf kindStr k.toUTF8)).text.size = s.text.size + k.toUTF8.size + (textV v).length := by
      rw [size_list (encValue v (s.leaf kindStr k.toUTF8)).text, h2, List.length_append, List.length_append, ← size_list s.text, ← size_list k.toUTF8]
    rw [encMembers]
    refine ⟨?_, ?_⟩
    · rw [h3, h1, hsz]; simp [tapeM]
    · rw [h4, h2]; simp [textM]
end

theorem empty_size : ByteArray.empty.size = 0 := rfl
theorem empty_list : ByteArray.empty.data.toList = [] := rfl

theorem empty_wf : (⟨.empty, .empty⟩ : TapeBuf).WF := by
  show ByteArray.empty.size % 8 = 0
  rw [empty_size]

/-- The tape of a whole value, from empty buffers: a function of the value alone (`tapeV 0`, `textV`). -/
theorem encValue_empty (v : Value) :
    (encValue v ⟨.empty, .empty⟩).tape.data.toList = tapeV 0 v ∧ (encValue v ⟨.empty, .empty⟩).text.data.toList = textV v := by
  have h := encValue_layout v ⟨.empty, .empty⟩ empty_wf
  simp only [empty_size, empty_list, List.nil_append] at h
  exact h

end LeanJson
