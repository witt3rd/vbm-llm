import LeanJsonProofs.Layout
/-! # The byte printer against the reference printer

`printBytes_eq`: the bytes of `printBytes v` are `print v`, for every value. `escapeString_eq`: `escapeString` of the UTF-8 of a string is `printString` of it. The string case is the one with work in it: the reference
escapes the characters of the string, the code escapes the bytes of its UTF-8, and a byte of a multi-byte sequence is at least 0x80 so no escape touches it (`escByte_ge`); the UTF-8 of a character is the
core's `String.utf8EncodeChar` and is the printer's `encodeUtf8` (`enc_eq`). The number case is `pushNumber_eq` (`LeanJsonProofs/Tape.lean`). -/
set_option linter.unusedSimpArgs false
namespace LeanJson

theorem L1' : ∀ n : Fin 256, (UInt8.ofNat n.val) &&& 0x3f ||| 0x80 = 0x80 + (UInt8.ofNat n.val) % 64 := by decide +kernel
theorem L1 (y : UInt8) : y &&& 0x3f ||| 0x80 = 0x80 + y % 64 := by
  have h := L1' ⟨y.toNat, y.toNat_lt⟩; simpa using h
theorem L2' : ∀ n : Fin 256, (UInt8.ofNat n.val) &&& 0x1f ||| 0xc0 = 0xc0 + (UInt8.ofNat n.val) % 32 := by decide +kernel
theorem L2 (y : UInt8) : y &&& 0x1f ||| 0xc0 = 0xc0 + y % 32 := by
  have h := L2' ⟨y.toNat, y.toNat_lt⟩; simpa using h
theorem L3' : ∀ n : Fin 256, (UInt8.ofNat n.val) &&& 0x0f ||| 0xe0 = 0xe0 + (UInt8.ofNat n.val) % 16 := by decide +kernel
theorem L3 (y : UInt8) : y &&& 0x0f ||| 0xe0 = 0xe0 + y % 16 := by
  have h := L3' ⟨y.toNat, y.toNat_lt⟩; simpa using h
theorem L4' : ∀ n : Fin 256, (UInt8.ofNat n.val) &&& 0x07 ||| 0xf0 = 0xf0 + (UInt8.ofNat n.val) % 8 := by decide +kernel
theorem L4 (y : UInt8) : y &&& 0x07 ||| 0xf0 = 0xf0 + y % 8 := by
  have h := L4' ⟨y.toNat, y.toNat_lt⟩; simpa using h

theorem enc_eq (c : Char) : String.utf8EncodeChar c = encodeUtf8 c.toNat := by
  have hv := c.valid
  have hc : c.toNat = c.val.toNat := rfl
  have hv' : c.val.toNat < 0xd800 ∨ (0xdfff < c.val.toNat ∧ c.val.toNat < 0x110000) := by
    unfold UInt32.isValidChar Nat.isValidChar at hv; omega
  rw [hc]
  have h1 := @String.utf8EncodeChar_eq_singleton c
  have h2 := @String.utf8EncodeChar_eq_cons_cons c
  have h3 := @String.utf8EncodeChar_eq_cons_cons_cons c
  have h4 := @String.utf8EncodeChar_eq_cons_cons_cons_cons c
  unfold Char.utf8Size at h1 h2 h3 h4
  generalize c.val = x at *
  have hx8 : x.toUInt8.toNat = x.toNat % 256 := by simp
  have s6 : (x >>> 6).toUInt8.toNat = x.toNat / 64 % 256 := by simp [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  have s12 : (x >>> 12).toUInt8.toNat = x.toNat / 4096 % 256 := by simp [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  have s18 : (x >>> 18).toUInt8.toNat = x.toNat / 262144 % 256 := by simp [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  unfold encodeUtf8
  by_cases a : x.toNat < 0x80
  · have : x ≤ 0x7f := by simpa [UInt32.le_iff_toNat_le] using (by omega : x.toNat ≤ 0x7f)
    rw [h1 (by simp [this])]
    simp only [a, ite_true]
    simp only [List.cons.injEq, and_true]
    apply UInt8.toNat_inj.mp
    simp [hx8] <;> omega
  by_cases b : x.toNat < 0x800
  · have : ¬ x ≤ 0x7f := by simp [UInt32.le_iff_toNat_le]; omega
    have h : x ≤ 0x7ff := by simpa [UInt32.le_iff_toNat_le] using (by omega : x.toNat ≤ 0x7ff)
    rw [h2 (by simp [this, h])]
    simp only [a, b, ite_true, ite_false]
    rw [L2, L1]
    simp only [List.cons.injEq, and_true]
    repeat' apply And.intro
    all_goals (apply UInt8.toNat_inj.mp; simp [hx8, s6, s12, s18, UInt8.toNat_add] <;> omega)
  by_cases d : x.toNat < 0x10000
  · have : ¬ x ≤ 0x7f := by simp [UInt32.le_iff_toNat_le]; omega
    have : ¬ x ≤ 0x7ff := by simp [UInt32.le_iff_toNat_le]; omega
    have h : x ≤ 0xffff := by simpa [UInt32.le_iff_toNat_le] using (by omega : x.toNat ≤ 0xffff)
    rw [h3 (by simp [*])]
    simp only [a, b, d, ite_true, ite_false]
    rw [L3, L1, L1]
    simp only [List.cons.injEq, and_true]
    repeat' apply And.intro
    all_goals (apply UInt8.toNat_inj.mp; simp [hx8, s6, s12, s18, UInt8.toNat_add] <;> omega)
  · have : ¬ x ≤ 0x7f := by simp [UInt32.le_iff_toNat_le]; omega
    have : ¬ x ≤ 0x7ff := by simp [UInt32.le_iff_toNat_le]; omega
    have : ¬ x ≤ 0xffff := by simp [UInt32.le_iff_toNat_le]; omega
    rw [h4 (by simp [*])]
    simp only [a, b, d, ite_false]
    rw [L4, L1, L1, L1]
    simp only [List.cons.injEq, and_true]
    repeat' apply And.intro
    all_goals (apply UInt8.toNat_inj.mp; simp [hx8, s6, s12, s18, UInt8.toNat_add] <;> omega)

/-- The bytes of a list, as a `ByteArray`. -/
abbrev ba (l : List UInt8) : ByteArray := ⟨l.toArray⟩

theorem push_ba (b : ByteArray) (x : UInt8) : b.push x = b ++ ba [x] := by
  apply ByteArray.ext; simp [ByteArray.data_push, ByteArray.data_append]

theorem app_ba (b : ByteArray) (l m : List UInt8) : (b ++ ba l) ++ ba m = b ++ ba (l ++ m) := by
  apply ByteArray.ext; simp [ByteArray.data_append]

theorem ba_nil (b : ByteArray) : b ++ ba [] = b := by
  apply ByteArray.ext; simp [ByteArray.data_append]

theorem toNat_byte' {n : Nat} (h : n < 256) : (UInt8.ofNat n).toNat = n := toNat_byte h

/-- `escByte` is `printScalar` on the bytes below 0x80. -/
theorem escByte_ascii {n : Nat} (h : n < 0x80) : escByte (UInt8.ofNat n) = printScalar n := by
  have e : (UInt8.ofNat n).toNat = n := toNat_byte (by omega)
  unfold escByte printScalar
  simp only [e]
  by_cases h1 : n = 0x22
  · simp [h1]
  by_cases h2 : n = 0x5C
  · simp [h2]
  by_cases h3 : n < 0x20
  · have : ¬ 0x20 ≤ n := by omega
    simp only [h1, h2, this, h3, ite_false, ite_true]
  · have : 0x20 ≤ n := by omega
    have h8 : n ≠ 0x08 := by omega
    have h9 : n ≠ 0x0C := by omega
    have h10 : n ≠ 0x0A := by omega
    have h11 : n ≠ 0x0D := by omega
    have h12 : n ≠ 0x09 := by omega
    simp only [h1, h2, h3, h8, h9, h10, h11, h12, this, ite_false, ite_true]
    unfold encodeUtf8
    simp only [show n < 0x80 from h, ite_true]

/-- A byte of a multi-byte sequence is at least 0x80, and passes through. -/
theorem escByte_ge {x : UInt8} (h : 0x80 ≤ x.toNat) : escByte x = [x] := by
  unfold escByte
  have a : ¬ x.toNat = 0x22 := by omega
  have b : ¬ x.toNat = 0x5C := by omega
  have c : 0x20 ≤ x.toNat := by omega
  simp only [a, b, c, ite_false, ite_true]

theorem encode_ge {n : Nat} (h : 0x80 ≤ n) (hn : n < 0x110000) : ∀ x ∈ encodeUtf8 n, 0x80 ≤ x.toNat := by
  intro x hx
  unfold encodeUtf8 at hx
  by_cases a : n < 0x80
  · omega
  by_cases b : n < 0x800
  · simp only [a, b, ite_false, ite_true, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · rw [toNat_byte (by omega)]; omega
    · rw [toNat_byte (by omega)]; omega
  by_cases d : n < 0x10000
  · simp only [a, b, d, ite_false, ite_true, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> (rw [toNat_byte (by omega)]; omega)
  · simp only [a, b, d, ite_false, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> (rw [toNat_byte (by omega)]; omega)

theorem flatMap_esc_ge {l : List UInt8} (h : ∀ x ∈ l, 0x80 ≤ x.toNat) : l.flatMap escByte = l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.flatMap_cons, escByte_ge (h x (by simp))]
    rw [ih (fun y hy => h y (by simp [hy]))]; rfl

/-- The reference escapes a character; the code escapes the bytes of its UTF-8: the same. -/
theorem printChar_flatMap (c : Char) : (String.utf8EncodeChar c).flatMap escByte = printChar c := by
  rw [enc_eq]
  have hs := char_scalar c
  unfold Scalar at hs
  by_cases a : c.toNat < 0x80
  · have e : encodeUtf8 c.toNat = [UInt8.ofNat c.toNat] := by unfold encodeUtf8; simp [a]
    rw [e, List.flatMap_cons, List.flatMap_nil, List.append_nil, escByte_ascii a]; rfl
  · unfold printChar printScalar
    have h1 : ¬ c.toNat = 0x22 := by omega
    have h2 : ¬ c.toNat = 0x5C := by omega
    have h3 : ¬ c.toNat = 0x08 := by omega
    have h4 : ¬ c.toNat = 0x0C := by omega
    have h5 : ¬ c.toNat = 0x0A := by omega
    have h6 : ¬ c.toNat = 0x0D := by omega
    have h7 : ¬ c.toNat = 0x09 := by omega
    have h8 : ¬ c.toNat < 0x20 := by omega
    simp only [h1, h2, h3, h4, h5, h6, h7, h8, ite_false]
    exact flatMap_esc_ge (encode_ge (by omega) (by omega))

theorem toByteArray_list (s : String) : s.toByteArray.data.toList = s.toList.flatMap String.utf8EncodeChar := by
  have h := String.utf8Encode_toList (b := s)
  rw [← h]; unfold List.utf8Encode; simp

theorem printString_bytes (s : String) : printString s = 0x22 :: (s.toByteArray.data.toList.flatMap escByte ++ [0x22]) := by
  rw [toByteArray_list, List.flatMap_assoc]
  unfold printString
  have : s.toList.flatMap printChar = s.toList.flatMap (fun c => (String.utf8EncodeChar c).flatMap escByte) := by
    congr 1; funext c; exact (printChar_flatMap c).symm
  rw [this]

theorem pushEsc_eq (b : ByteArray) (x : UInt8) : pushEsc b x = b ++ ba (escByte x) := by
  unfold pushEsc escByte
  repeat' split
  all_goals simp [push_ba, app_ba]

theorem escLoop_eq (a : ByteArray) (i : Nat) (b : ByteArray) : escLoop a i b = b ++ ba ((a.data.toList.drop i).flatMap escByte) := by
  unfold escLoop
  split
  · rename_i h
    rw [escLoop_eq a (i + 1) (pushEsc b a[i]), pushEsc_eq, app_ba]
    have : a.data.toList.drop i = a[i] :: a.data.toList.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using h)]; simp <;> rfl
    rw [this, List.flatMap_cons]
  · rename_i h
    have : a.data.toList.drop i = [] := List.drop_eq_nil_of_le (by simpa using h)
    rw [this]; simp [ba_nil]
termination_by a.size - i

theorem escLoopS_eq (s : String) (i : Nat) (b : ByteArray) : escLoopS s i b = b ++ ba ((s.toByteArray.data.toList.drop i).flatMap escByte) := by
  unfold escLoopS
  split
  · rename_i h
    have hs : i < s.toByteArray.size := by simpa [String.size_toByteArray] using h
    rw [escLoopS_eq s (i + 1) _, pushEsc_eq, app_ba]
    have : s.toByteArray.data.toList.drop i = s.toByteArray[i] :: s.toByteArray.data.toList.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hs)]; simp <;> rfl
    rw [this, List.flatMap_cons, String.getUTF8Byte_eq_getElem]
  · rename_i h
    have : s.toByteArray.data.toList.drop i = [] := List.drop_eq_nil_of_le (by simpa [String.size_toByteArray] using h)
    rw [this]; simp [ba_nil]
termination_by s.utf8ByteSize - i

theorem pushString_eq (b : ByteArray) (s : String) : pushString b s = b ++ ba (printString s) := by
  unfold pushString
  rw [escLoopS_eq, printString_bytes]
  simp [push_ba, app_ba]

/-- The string literal of the UTF-8 of a string is what the reference prints for it. -/
theorem escapeString_eq (s : String) : escapeString s.toUTF8 = ba (printString s) := by
  unfold escapeString
  rw [escLoop_eq, printString_bytes]
  have : s.toUTF8 = s.toByteArray := rfl
  rw [this]
  simp [push_ba, app_ba, ByteArray.emptyWithCapacity]
  apply ByteArray.ext; simp [ByteArray.data_append] <;> rfl

mutual
theorem pushVal_eq (b : ByteArray) : (v : Value) → pushVal b v = b ++ ba (print v)
  | .null => by simp [pushVal, print, push_ba, app_ba]
  | .bool true => by simp [pushVal, print, push_ba, app_ba]
  | .bool false => by simp [pushVal, print, push_ba, app_ba]
  | .num n => by simp [pushVal, print, pushNumber_eq]
  | .str s => by simp [pushVal, print, pushString_eq]
  | .arr xs => by
    simp only [pushVal, print, pushElems_eq, push_ba, app_ba]; simp
  | .obj ms => by
    simp only [pushVal, print, pushMembers_eq, push_ba, app_ba]; simp
theorem pushElems_eq (b : ByteArray) : (xs : List Value) → pushElems b xs = b ++ ba (printElems xs)
  | [] => by simp [pushElems, printElems, ba_nil]
  | [v] => by simp [pushElems, printElems, pushVal_eq]
  | v :: w :: ws => by
    rw [pushElems, pushElems_eq _ (w :: ws), pushVal_eq, push_ba, app_ba, app_ba]
    · simp [printElems]
    · intro h; cases h
theorem pushMembers_eq (b : ByteArray) : (ms : List (String × Value)) → pushMembers b ms = b ++ ba (printMembers ms)
  | [] => by simp [pushMembers, printMembers, ba_nil]
  | [(k, v)] => by simp [pushMembers, printMembers, pushVal_eq, pushString_eq, push_ba, app_ba]
  | (k, v) :: m :: ms => by
    rw [pushMembers, pushMembers_eq _ (m :: ms), pushVal_eq, pushString_eq, push_ba, push_ba, app_ba, app_ba, app_ba, app_ba]
    · simp [printMembers]
    · intro h; cases h
end

/-- The byte printer is the reference printer. -/
theorem printBytes_eq (v : Value) : printBytes v = ba (print v) := by
  unfold printBytes
  rw [pushVal_eq]
  apply ByteArray.ext; simp [ByteArray.data_append, ByteArray.emptyWithCapacity] <;> rfl

theorem wordsum (u : UInt64) :
    u.toUInt8.toUInt64 + ((u >>> 8).toUInt8.toUInt64 <<< 8) + ((u >>> 16).toUInt8.toUInt64 <<< 16) + ((u >>> 24).toUInt8.toUInt64 <<< 24) +
    ((u >>> 32).toUInt8.toUInt64 <<< 32) + ((u >>> 40).toUInt8.toUInt64 <<< 40) + ((u >>> 48).toUInt8.toUInt64 <<< 48) + ((u >>> 56).toUInt8.toUInt64 <<< 56) = u := by
  apply UInt64.toNat_inj.mp
  have h := u.toNat_lt
  simp [UInt64.toNat_add, UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  omega

end LeanJson
