import LeanJson.Tape
import LeanJsonProofs.Layout
/-! # The fused parser refines the tape of the value (slice by slice)

`docs/perf/fuse-plan.md`. F3: closing a container by patching its two header words is the closed node of the layout (`closeNode_arr`, `closeNode_obj`, `node_empty_arr`, `node_empty_obj`). -/
set_option linter.unusedSimpArgs false
namespace LeanJson

theorem TapeBuf.ext_list {s t : TapeBuf} (h1 : s.tape.data.toList = t.tape.data.toList) (h2 : s.text.data.toList = t.text.data.toList) : s = t := by
  obtain ⟨⟨a⟩, ⟨b⟩⟩ := s
  obtain ⟨⟨c⟩, ⟨d⟩⟩ := t
  simp only [TapeBuf.mk.injEq, ByteArray.mk.injEq]
  exact ⟨Array.toList_inj.mp h1, Array.toList_inj.mp h2⟩

/-- A store of one word into a buffer whose bytes are `P ++ X ++ R`, with `P` `k` words long and `X` one word: it replaces `X`. -/
theorem setWord_at (b : ByteArray) (P X R : List UInt8) (k : Nat) (w : UInt64) (hb : b.data.toList = P ++ X ++ R) (hP : P.length = 8 * k) (hX : X.length = 8) :
    (setWord b k w).data.toList = P ++ wordBytes w ++ R := by
  have hsz : 8 * k + 8 ≤ b.size := by rw [size_list, hb]; simp; omega
  have e1 : (P ++ X ++ R).take (8 * k) = P := by rw [List.append_assoc, ← hP, List.take_left]
  have e2 : (P ++ X ++ R).drop (8 * k + 8) = R := by
    rw [show 8 * k + 8 = (P ++ X).length by simp [hP, hX]]; exact List.drop_left
  rw [setWord_list b k w hsz, hb, e1, e2]

theorem closeNode_text (r : TapeBuf) (kind at_ n : Nat) : (r.closeNode kind at_ n).text = r.text := by
  obtain ⟨t, x⟩ := r; rfl

/-- Closing by patching both header words: the tape is the closed node's (`hdrBytes kind n (2 + words of what followed)`). -/
theorem closeNode_list (s r : TapeBuf) (kind n : Nat) (C : List UInt8) (hs : s.WF) (hC : C.length % 8 = 0)
    (hr : r.tape.data.toList = s.tape.data.toList ++ hdrBytes kind 0 0 ++ C) :
    (r.closeNode kind s.words n).tape.data.toList = s.tape.data.toList ++ hdrBytes kind n (2 + C.length / 8) ++ C := by
  have hk := words_wf hs
  have hsl : s.tape.data.toList.length = 8 * s.words := by rw [← size_list]; omega
  have hsz : r.tape.size = s.tape.size + 16 + C.length := by
    rw [size_list r.tape, hr, size_list s.tape]; simp [hdrBytes_length]; omega
  have hw : r.tape.size / 8 - s.words = 2 + C.length / 8 := by unfold TapeBuf.words at *; omega
  obtain ⟨t, x⟩ := r
  simp only [TapeBuf.closeNode]
  simp only at hr hw
  rw [hw]
  unfold hdrBytes at hr ⊢
  have h1 := setWord_at t s.tape.data.toList (wordBytes (UInt64.ofNat (kind + 0 * 256))) (wordBytes (UInt64.ofNat 0) ++ C) s.words (UInt64.ofNat (kind + n * 256))
    (by rw [hr]; simp) hsl (wordBytes_length _)
  have h2 := setWord_at (setWord t s.words (UInt64.ofNat (kind + n * 256))) (s.tape.data.toList ++ wordBytes (UInt64.ofNat (kind + n * 256))) (wordBytes (UInt64.ofNat 0)) C (s.words + 1)
    (UInt64.ofNat (2 + C.length / 8)) (by rw [h1]; simp) (by simp [hsl, wordBytes_length]; omega) (wordBytes_length _)
  rw [h2]; simp

/-- F3: the open/close discipline of an array: header with placeholders, the elements, then the patch, is the array's `encValue`. -/
theorem closeNode_arr (xs : List Value) (s : TapeBuf) (hs : s.WF) :
    (encList xs (s.node kindArr 0 0)).closeNode kindArr s.words xs.length = encValue (.arr xs) s := by
  have ht := node_wf hs kindArr 0 0
  obtain ⟨h1, h2⟩ := encList_layout xs (s.node kindArr 0 0) ht
  rw [node_tape, node_text] at h1
  rw [node_text] at h2
  have hC : (tapeL s.text.size xs).length = 8 * wordsL xs := tapeL_length _ _
  obtain ⟨h3, h4⟩ := encValue_layout (.arr xs) s hs
  apply TapeBuf.ext_list
  · rw [closeNode_list s _ kindArr xs.length _ hs (by omega) h1, h3, hC]
    simp [tapeV, wordsV]
  · rw [closeNode_text, h4, h2]; simp [textV]

theorem closeNode_obj (ms : List (String × Value)) (s : TapeBuf) (hs : s.WF) :
    (encMembers ms (s.node kindObj 0 0)).closeNode kindObj s.words ms.length = encValue (.obj ms) s := by
  have ht := node_wf hs kindObj 0 0
  obtain ⟨h1, h2⟩ := encMembers_layout ms (s.node kindObj 0 0) ht
  rw [node_tape, node_text] at h1
  rw [node_text] at h2
  have hC : (tapeM s.text.size ms).length = 8 * wordsM ms := tapeM_length _ _
  obtain ⟨h3, h4⟩ := encValue_layout (.obj ms) s hs
  apply TapeBuf.ext_list
  · rw [closeNode_list s _ kindObj ms.length _ hs (by omega) h1, h3, hC]
    simp [tapeV, wordsV]
  · rw [closeNode_text, h4, h2]; simp [textV]

/-- An empty array or object is one header, already closed. -/
theorem node_empty_arr (s : TapeBuf) (hs : s.WF) : s.node kindArr 0 2 = encValue (.arr []) s := by
  rw [← closeNode_arr [] s hs]
  have ht := node_wf hs kindArr 0 0
  apply TapeBuf.ext_list
  · simp only [encList, List.length_nil]
    rw [closeNode_list s (s.node kindArr 0 0) kindArr 0 [] hs (by simp) (by rw [node_tape]; simp), node_tape]
    simp [hdrBytes]
  · rw [closeNode_text]; simp [encList, node_text]

theorem node_empty_obj (s : TapeBuf) (hs : s.WF) : s.node kindObj 0 2 = encValue (.obj []) s := by
  rw [← closeNode_obj [] s hs]
  apply TapeBuf.ext_list
  · simp only [encMembers, List.length_nil]
    rw [closeNode_list s (s.node kindObj 0 0) kindObj 0 [] hs (by simp) (by rw [node_tape]; simp), node_tape]
    simp [hdrBytes]
  · rw [closeNode_text]; simp [encMembers, node_text]

end LeanJson
