import LeanJson.Tape
import LeanJsonProofs.Print
/-! # The tape builder against its definitions

The code builds the tape with `pushWordFast` and `pushNumber`; the layout is defined by `pushWord` and `printNumber`. Here the fast forms are equal to the definitions
(`pushWordFast_eq`, `pushNumber_eq`, `TapeBuf.num_eq`), so any statement about the layout (the layout theorem is a later slice) is about what the exports run. -/
namespace LeanJson

theorem set_push (arr : Array UInt8) (i : Nat) (x v : UInt8) :
    (arr.push x).setIfInBounds i v = if i < arr.size then (arr.setIfInBounds i v).push x else if i = arr.size then arr.push v else arr.push x := by
  apply Array.ext_getElem?
  intro j
  by_cases h1 : i < arr.size
  · simp only [h1, ite_true, Array.getElem?_setIfInBounds, Array.getElem?_push, Array.size_push, Array.size_setIfInBounds]
    split <;> (try split) <;> (try split) <;> simp_all <;> omega
  · by_cases h2 : i = arr.size
    · subst h2
      simp only [Nat.lt_irrefl, ite_true, ite_false, Array.getElem?_setIfInBounds, Array.getElem?_push, Array.size_push]
      split <;> (try split) <;> simp_all
    · simp only [h1, h2, ite_false, Array.getElem?_setIfInBounds, Array.getElem?_push, Array.size_push]
      split <;> (try split) <;> simp_all <;> omega

theorem pushWordFast_eq (b : ByteArray) (w : UInt64) : pushWordFast b w = pushWord b w := by
  obtain ⟨arr⟩ := b
  apply ByteArray.ext
  have hz : arr ++ zero8.data = (((((((arr.push 0).push 0).push 0).push 0).push 0).push 0).push 0).push 0 := by
    apply Array.toList_inj.mp; simp [zero8, ByteArray.empty, ByteArray.emptyWithCapacity]
    rfl
  simp only [pushWordFast, pushWord, ByteArray.set!, ByteArray.size, ByteArray.data_push, ByteArray.data_append, Array.set!_eq_setIfInBounds, hz]
  simp +arith only [set_push, Array.size_push, ite_true, ite_false]

/-- The bytes of a list, as a `ByteArray`. -/
theorem data_mk (l : List UInt8) : (ByteArray.mk l.toArray).data = l.toArray := rfl

theorem pushDigits_eq (ds : List Digit) (b : ByteArray) : pushDigits b ds = b ++ ⟨(ds.map digitByte).toArray⟩ := by
  induction ds generalizing b with
  | nil => apply ByteArray.ext; simp [pushDigits, ByteArray.data_append]
  | cons d ds ih =>
    rw [pushDigits, ih]
    apply ByteArray.ext
    simp [ByteArray.data_append, ByteArray.data_push]

theorem pushNumber_eq (b : ByteArray) (n : Number) : pushNumber b n = b ++ ⟨(printNumber n).toArray⟩ := by
  obtain ⟨neg, ip, fr, ex⟩ := n
  apply ByteArray.ext
  rcases ip with _ | ⟨l, rest⟩ <;> rcases fr with _ | ⟨⟨fd, fds⟩⟩ <;> rcases ex with _ | ⟨⟨_ | _, ed, eds⟩⟩ <;> cases neg <;>
    simp [pushNumber, printNumber, printMinus, printInt, printFrac, printExp, pushDigits_eq, ByteArray.data_append, ByteArray.data_push]
  all_goals (apply Array.toList_inj.mp; simp)

/-- A number node written straight into the buffers is the node of the printed lexeme. -/
theorem TapeBuf.num_eq (s : TapeBuf) (n : Number) : s.num n = s.leaf kindNum ⟨(printNumber n).toArray⟩ := by
  obtain ⟨tape, text⟩ := s
  have hs : (ByteArray.mk (printNumber n).toArray).size = (printNumber n).length := by simp [ByteArray.size]
  simp only [TapeBuf.num, TapeBuf.leaf, TapeBuf.node, pushNumber_eq, ByteArray.size_append, hs, Nat.add_sub_cancel_left]

end LeanJson
