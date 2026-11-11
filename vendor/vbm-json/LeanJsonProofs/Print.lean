import LeanJsonProofs.Parse
import LeanJsonProofs.Grammar
/-! # The printer against the grammar

`print_json`: the printer's output is derivable in the grammar, for every value (no depth condition: the grammar has none). `print_roundtrip`: the reference reads it back, when the value is within `maxDepth`.
About the specification; nothing here is the code the exports run. -/
namespace LeanJson

theorem toNat_byte {n : Nat} (h : n < 256) : (UInt8.ofNat n).toNat = n := by
  rw [UInt8.toNat_ofNat']; omega


theorem digitVal_digitByte (d : Digit) : digitVal (digitByte d) = some d := by
  have h := d.isLt
  have hb : (digitByte d).toNat = 0x30 + d.val := by
    unfold digitByte; rw [toNat_byte (by omega)]
  unfold digitVal
  split
  · simp only [Option.some.injEq]; apply Fin.ext; simp only [hb]; omega
  · rename_i hh; exfalso; apply hh; omega

theorem digit19_byte (l : Fin 9) : digit19 (UInt8.ofNat (0x31 + l.val)) = some l := by
  have h := l.isLt
  have hb : (UInt8.ofNat (0x31 + l.val)).toNat = 0x31 + l.val := by
    rw [toNat_byte (by omega)]
  unfold digit19
  split
  · simp only [Option.some.injEq]; apply Fin.ext; simp only [hb]; omega
  · rename_i hh; exfalso; apply hh; omega

theorem digits_print (ds : List Digit) : Digits (ds.map digitByte) ds := by
  induction ds with
  | nil => exact .nil
  | cons d ds ih => exact .cons (digitVal_digitByte d) ih

theorem num_print (n : Number) : Num (printNumber n) n := by
  obtain ⟨neg, ip, fr, ex⟩ := n
  have hm : Minus (printMinus neg) neg := by cases neg <;> simp [printMinus] <;> constructor
  have hi : IntP (printInt ip) ip := by
    cases ip with
    | zero => exact .zero
    | nz l rest => exact .nz (digit19_byte l) (digits_print rest)
  have hf : FracP (printFrac fr) fr := by
    cases fr with
    | none => exact .none
    | some p => obtain ⟨d, ds⟩ := p; exact .some (digitVal_digitByte d) (digits_print ds)
  have he : ExpP (printExp ex) ex := by
    cases ex with
    | none => exact .none
    | some p =>
      obtain ⟨neg, d, ds⟩ := p
      refine .some (Or.inl rfl) ?_ (digitVal_digitByte d) (digits_print ds)
      cases neg <;> simp [printMinus] <;> constructor
  exact .mk hm hi hf he

theorem utf8_encode {n : Nat} (hs : Scalar n) : Utf8 (encodeUtf8 n) n := by
  unfold Scalar at hs
  unfold encodeUtf8
  split
  · rename_i h
    have ha : (UInt8.ofNat n).toNat = n := toNat_byte (by omega)
    have := Utf8.u1 (a := UInt8.ofNat n) (by omega)
    rwa [ha] at this
  · split
    · rename_i h1 h2
      have ha : (UInt8.ofNat (0xC0 + n / 64)).toNat = 0xC0 + n / 64 := toNat_byte (by omega)
      have hb : (UInt8.ofNat (0x80 + n % 64)).toNat = 0x80 + n % 64 := toNat_byte (by omega)
      have h := Utf8.u2 (a := UInt8.ofNat (0xC0 + n / 64)) (b := UInt8.ofNat (0x80 + n % 64)) (by omega) (by omega) (by unfold Tail; omega)
      have e : ((UInt8.ofNat (0xC0 + n / 64)).toNat - 0xC0) * 64 + ((UInt8.ofNat (0x80 + n % 64)).toNat - 0x80) = n := by omega
      rwa [e] at h
    · split
      · rename_i h1 h2 h3
        have ha : (UInt8.ofNat (0xE0 + n / 4096)).toNat = 0xE0 + n / 4096 := toNat_byte (by omega)
        have hb : (UInt8.ofNat (0x80 + n / 64 % 64)).toNat = 0x80 + n / 64 % 64 := toNat_byte (by omega)
        have hc : (UInt8.ofNat (0x80 + n % 64)).toNat = 0x80 + n % 64 := toNat_byte (by omega)
        have h := Utf8.u3 (a := UInt8.ofNat (0xE0 + n / 4096)) (b := UInt8.ofNat (0x80 + n / 64 % 64)) (c := UInt8.ofNat (0x80 + n % 64))
          (by omega) (by omega) (by unfold Second3 Tail; omega) (by unfold Tail; omega)
        have e : ((UInt8.ofNat (0xE0 + n / 4096)).toNat - 0xE0) * 4096 + ((UInt8.ofNat (0x80 + n / 64 % 64)).toNat - 0x80) * 64 + ((UInt8.ofNat (0x80 + n % 64)).toNat - 0x80) = n := by omega
        rwa [e] at h
      · rename_i h1 h2 h3
        have ha : (UInt8.ofNat (0xF0 + n / 262144)).toNat = 0xF0 + n / 262144 := toNat_byte (by omega)
        have hb : (UInt8.ofNat (0x80 + n / 4096 % 64)).toNat = 0x80 + n / 4096 % 64 := toNat_byte (by omega)
        have hc : (UInt8.ofNat (0x80 + n / 64 % 64)).toNat = 0x80 + n / 64 % 64 := toNat_byte (by omega)
        have hd : (UInt8.ofNat (0x80 + n % 64)).toNat = 0x80 + n % 64 := toNat_byte (by omega)
        have h := Utf8.u4 (a := UInt8.ofNat (0xF0 + n / 262144)) (b := UInt8.ofNat (0x80 + n / 4096 % 64)) (c := UInt8.ofNat (0x80 + n / 64 % 64)) (d := UInt8.ofNat (0x80 + n % 64))
          (by omega) (by omega) (by unfold Second4 Tail; omega) (by unfold Tail; omega) (by unfold Tail; omega)
        have e : ((UInt8.ofNat (0xF0 + n / 262144)).toNat - 0xF0) * 262144 + ((UInt8.ofNat (0x80 + n / 4096 % 64)).toNat - 0x80) * 4096 + ((UInt8.ofNat (0x80 + n / 64 % 64)).toNat - 0x80) * 64 + ((UInt8.ofNat (0x80 + n % 64)).toNat - 0x80) = n := by omega
        rwa [e] at h

theorem hexVal_hexDigit {k : Nat} (hk : k < 16) : hexVal (hexDigit k) = some k := by
  unfold hexDigit
  split
  · rename_i h
    have ht : (UInt8.ofNat (0x30 + k)).toNat = 0x30 + k := toNat_byte (by omega)
    unfold hexVal; rw [ht]
    split
    · simp
    · omega
  · rename_i h
    have ht : (UInt8.ofNat (0x61 + (k - 10))).toNat = 0x61 + (k - 10) := toNat_byte (by omega)
    unfold hexVal; rw [ht]
    split
    · omega
    · split
      · omega
      · split
        · simp; omega
        · omega

theorem char_scalar (c : Char) : Scalar c.toNat := by
  have h := c.valid
  unfold Scalar
  unfold UInt32.isValidChar Nat.isValidChar at h
  have : c.toNat = c.val.toNat := rfl
  omega

theorem strChar_scalar_print {n : Nat} (hs : Scalar n) : StrChar (printScalar n) n := by
  unfold printScalar
  by_cases h1 : n = 0x22
  · subst h1; simp only [ite_true]; exact .esc (.simple (b := 0x22) rfl)
  by_cases h2 : n = 0x5C
  · subst h2; simp [h1]; exact .esc (.simple (b := 0x5C) rfl)
  by_cases h3 : n = 0x08
  · subst h3; simp; exact .esc (.simple (b := 0x62) rfl)
  by_cases h4 : n = 0x0C
  · subst h4; simp; exact .esc (.simple (b := 0x66) rfl)
  by_cases h5 : n = 0x0A
  · subst h5; simp; exact .esc (.simple (b := 0x6E) rfl)
  by_cases h6 : n = 0x0D
  · subst h6; simp; exact .esc (.simple (b := 0x72) rfl)
  by_cases h7 : n = 0x09
  · subst h7; simp; exact .esc (.simple (b := 0x74) rfl)
  simp only [h1, h2, h3, h4, h5, h6, h7, ite_false]
  by_cases h8 : n < 0x20
  · simp only [h8, ite_true]
    refine .esc (.uni (h := [0x30, 0x30, hexDigit (n / 16), hexDigit (n % 16)]) ?_ (by omega))
    have := Hex4.mk (a := 0x30) (b := 0x30) (c := hexDigit (n / 16)) (d := hexDigit (n % 16)) (w := 0) (x := 0) (y := n / 16) (z := n % 16)
      (by decide) (by decide) (hexVal_hexDigit (by omega)) (hexVal_hexDigit (by omega))
    have e : 0 * 4096 + 0 * 256 + n / 16 * 16 + n % 16 = n := by omega
    rwa [e] at this
  · simp only [h8, ite_false]
    exact .plain (utf8_encode hs) (by omega) h1 h2

theorem chars_print (l : List Char) : Chars (l.flatMap printChar) (l.map Char.toNat) := by
  induction l with
  | nil => exact .nil
  | cons c l ih => exact .cons (strChar_scalar_print (char_scalar c)) ih

theorem str_print (s : String) : Str (printString s) s := by
  have h := Str.mk (chars_print s.toList)
  have e : String.ofList ((s.toList.map Char.toNat).map Char.ofNat) = s := by
    simp [List.map_map, Function.comp_def]
  rw [e] at h
  exact h

mutual
theorem print_val : ∀ v : Value, Val (print v) v
  | .null => .null
  | .bool true => .true
  | .bool false => .false
  | .num n => .num (num_print n)
  | .str s => .str (str_print s)
  | .arr xs => by
    cases xs with
    | nil => simpa [print, printElems] using Val.arr0 (w := []) .nil
    | cons v vs =>
      have := Val.arr .nil (printElems_elems (v :: vs) (by simp)) .nil
      simpa [print] using this
  | .obj ms => by
    cases ms with
    | nil => simpa [print, printMembers] using Val.obj0 (w := []) .nil
    | cons kv kvs =>
      have := Val.obj .nil (printMembers_members (kv :: kvs) (by simp)) .nil
      simpa [print] using this

theorem printElems_elems : ∀ xs : List Value, xs ≠ [] → Elems (printElems xs) xs
  | [], h => absurd rfl h
  | [v], _ => by simpa [printElems] using Elems.one (print_val v)
  | v :: w :: ws, _ => by
    have := Elems.cons (print_val v) .nil .nil (printElems_elems (w :: ws) (by simp))
    simpa [printElems] using this

theorem printMembers_members : ∀ ms : List (String × Value), ms ≠ [] → Members (printMembers ms) ms
  | [], h => absurd rfl h
  | [(k, v)], _ => by
    have := Members.one (Member.mk (str_print k) .nil .nil (print_val v))
    simpa [printMembers] using this
  | (k, v) :: m :: ms, _ => by
    have := Members.cons (Member.mk (str_print k) .nil .nil (print_val v)) .nil .nil (printMembers_members (m :: ms) (by simp))
    simpa [printMembers] using this
end

/-- The printer's output is derivable in the grammar, for every value. -/
theorem print_json (v : Value) : Json (print v) v := by
  simpa using Json.mk .nil (print_val v) .nil

/-- The reference reads back what the printer wrote (a value deeper than `maxDepth` is the one exception: it is printed and then refused with the `depth` code). -/
theorem print_roundtrip {v : Value} (h : v.depth ≤ maxDepth) : parse (print v) = .ok v := parse_complete (print_json v) h

/-- Canonicalising is stable: what the reference accepts, printed and read again, is the same value. -/
theorem print_canonical {bs : Bytes} {v : Value} (h : parse bs = .ok v) : parse (print v) = .ok v :=
  print_roundtrip (parse_sound h).2

end LeanJson
