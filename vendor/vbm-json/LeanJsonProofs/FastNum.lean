import LeanJsonProofs.FastTape
import LeanJsonProofs.FastLeaf
import LeanJsonProofs.Leaf
/-! # F1: the number scan and the lexeme copy are `parseNumA` and `TapeBuf.num`

`scanNum_eq`: the scan returns the end index `parseNumA` returns. `pushLex_eq`: when `parseNumA a i = some (n, j)`, copying `a[i..j)` canonically is `pushNumber b n` (the printed lexeme).
`numLex_eq`: the node written from the input bytes is `TapeBuf.num n`. -/
set_option linter.unusedSimpArgs false
namespace LeanJson

theorem digitsAcc_snd (a : ByteArray) (i : Nat) (acc : List Digit) : (digitsAcc a i acc).2 = scanDigits a i := by
  fun_induction digitsAcc a i acc with
  | case1 i acc h d hd ih => rw [scanDigits]; simp [h, hd, ih]
  | case2 i acc h hd => rw [scanDigits]; simp [h, hd]
  | case3 i acc h => rw [scanDigits]; simp [h]

theorem scanDigits_eq (a : ByteArray) (i : Nat) : scanDigits a i = (digitsA a i).2 := by
  simp [digitsA, digitsAcc_snd]

theorem scanDigits1_eq (a : ByteArray) (i : Nat) : scanDigits1 a i = (digits1A a i).map (·.2) := by
  unfold scanDigits1 digits1A
  rcases byteAt a i with _ | b
  · rfl
  · rcases hd : digitVal b with _ | d
    · simp [hd]
    · simp [hd, scanDigits_eq]

theorem scanInt_eq (a : ByteArray) (i : Nat) : scanInt a i = (parseIntA a i).map (·.2) := by
  unfold scanInt parseIntA
  rcases byteAt a i with _ | b
  · rfl
  · by_cases h0 : b = 0x30
    · simp [h0]
    · rcases hd : digit19 b with _ | l
      · simp [h0, hd]
      · simp [h0, hd, scanDigits_eq]

theorem scanFrac_eq (a : ByteArray) (i : Nat) : scanFrac a i = (parseFracA a i).map (·.2) := by
  unfold scanFrac parseFracA
  split
  · rw [scanDigits1_eq]; cases digits1A a (i + 1) <;> simp
  · simp

theorem scanExp_eq (a : ByteArray) (i : Nat) : scanExp a i = (parseExpA a i).map (·.2) := by
  unfold scanExp parseExpA
  split
  · simp only [scanDigits1_eq]
    cases digits1A a (if byteIs a (i + 1) 0x2B || byteIs a (i + 1) 0x2D then i + 2 else i + 1) <;> simp
  · simp

theorem scanNum_eq (a : ByteArray) (i : Nat) : scanNum a i = (parseNumA a i).map (·.2) := by
  unfold scanNum parseNumA
  rw [scanInt_eq]
  rcases hI : parseIntA a (if byteIs a i 0x2D then i + 1 else i) with _ | ⟨ip, i1⟩
  · simp [hI]
  · simp only [Option.map_some]
    rw [scanFrac_eq]
    rcases hF : parseFracA a i1 with _ | ⟨fr, i2⟩
    · simp [hI, hF]
    · simp only [Option.map_some]
      rw [scanExp_eq]
      rcases hE : parseExpA a i2 with _ | ⟨ex, i3⟩ <;> simp [hI, hF, hE]

/-- The canonical form of one input byte of a number: `E` as `e`, `+` dropped. -/
def lexConv (c : UInt8) : Option UInt8 := if c == 0x45 then some 0x65 else if c == 0x2B then none else some c

def lexMap (xs : List UInt8) : List UInt8 := xs.filterMap lexConv

theorem lexMap_append (xs ys : List UInt8) : lexMap (xs ++ ys) = lexMap xs ++ lexMap ys := by simp [lexMap, List.filterMap_append]

theorem pushLex_list (a : ByteArray) (i j : Nat) (b : ByteArray) :
    (pushLex a i j b).data.toList = b.data.toList ++ lexMap (((L a).drop i).take (j - i)) := by
  fun_induction pushLex a i j b with
  | case1 i b hij hn => rw [drop_of_none hn]; simp [lexMap]
  | case2 i b hij c hc ih =>
    simp only [dite_eq_ite] at ih
    rw [ih, drop_of_some hc, show j - i = (j - (i + 1)) + 1 by omega, List.take_succ_cons]
    by_cases h1 : c = 0x45
    · subst h1; simp [lexMap, lexConv, push_list]
    · by_cases h2 : c = 0x2B
      · subst h2; simp [lexMap, lexConv]
      · simp [lexMap, lexConv, h1, h2, push_list]
  | case3 i b hij => rw [show j - i = 0 by omega]; simp [lexMap]

theorem digitByte_of_val {b : UInt8} {d : Digit} (h : digitVal b = some d) : digitByte d = b := by
  unfold digitVal at h
  split at h
  · rename_i hh
    simp only [Option.some.injEq] at h
    subst h
    unfold digitByte
    apply UInt8.toNat_inj.mp
    simp only [Fin.val_mk]
    rw [toNat_byte (by omega)]; omega
  · simp at h

theorem byte_of_digit19 {b : UInt8} {l : Fin 9} (h : digit19 b = some l) : UInt8.ofNat (0x31 + l.val) = b := by
  unfold digit19 at h
  split at h
  · rename_i hh
    simp only [Option.some.injEq] at h
    subst h
    apply UInt8.toNat_inj.mp
    simp only [Fin.val_mk]
    rw [toNat_byte (by omega)]; omega
  · simp at h

theorem lexConv_digit (d : Digit) : lexConv (digitByte d) = some (digitByte d) := by
  have hd := d.isLt
  have hb : (digitByte d).toNat = 0x30 + d.val := by unfold digitByte; rw [toNat_byte (by omega)]
  have h1 : (digitByte d == 0x45) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro h; have := congrArg UInt8.toNat h; simp [hb] at this; omega
  have h2 : (digitByte d == 0x2B) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro h; have := congrArg UInt8.toNat h; simp [hb] at this; omega
  simp [lexConv, h1, h2]

theorem digits_lex {ds : Bytes} {rest : List Digit} (h : Digits ds rest) : lexMap ds = rest.map digitByte := by
  induction h with
  | nil => rfl
  | cons hd _ ih =>
    rw [← digitByte_of_val hd]
    simp [lexMap, List.filterMap_cons, lexConv_digit] at ih ⊢
    exact ih

theorem digits1_lex {b : UInt8} {d : Digit} {ds : Bytes} {rest : List Digit} (hd : digitVal b = some d) (hds : Digits ds rest) :
    lexMap (b :: ds) = digitByte d :: rest.map digitByte := by
  have := digits_lex hds
  rw [← digitByte_of_val hd]
  unfold lexMap at this ⊢
  rw [List.filterMap_cons, lexConv_digit]
  simp only [this]

theorem num_lex {pre : Bytes} {n : Number} (h : Num pre n) : lexMap pre = printNumber n := by
  cases h with
  | mk hm hi hf he =>
    rename_i m i f e neg ip fr ex
    simp only [lexMap_append]
    have e1 : lexMap m = printMinus neg := by cases hm <;> rfl
    have e2 : lexMap i = printInt ip := by
      cases hi with
      | zero => rfl
      | nz hb hd =>
        rename_i b l ds rest
        have := digits_lex hd
        have hl : lexConv b = some b := by
          have hb' := byte_of_digit19 hb
          have hl' := l.isLt
          have hv : b.toNat = 0x31 + l.val := by rw [← hb', toNat_byte (by omega)]
          have h1 : (b == 0x45) = false := by
            simp only [beq_eq_false_iff_ne, ne_eq]; intro h; have := congrArg UInt8.toNat h; simp [hv] at this; omega
          have h2 : (b == 0x2B) = false := by
            simp only [beq_eq_false_iff_ne, ne_eq]; intro h; have := congrArg UInt8.toNat h; simp [hv] at this; omega
          simp [lexConv, h1, h2]
        rw [← byte_of_digit19 hb] at hl ⊢
        simp only [lexMap, List.filterMap_cons, hl] at this ⊢
        simp [printInt, ← this, byte_of_digit19 hb]
    have e3 : lexMap f = printFrac fr := by
      cases hf with
      | none => rfl
      | some hd hds =>
        rename_i b d ds rest
        have h2 := digits1_lex hd hds
        show (lexConv 0x2E).toList ++ lexMap (b :: ds) = _
        rw [h2]; rfl
    have e4 : lexMap e = printExp ex := by
      cases he with
      | none => rfl
      | some hee hsg hd hds =>
        rename_i ee sg neg' b d ds rest
        have h2 := digits1_lex hd hds
        have hsg' : lexMap sg = printMinus neg' := by cases hsg <;> rfl
        have hee' : lexConv ee = some 0x65 := by rcases hee with rfl | rfl <;> rfl
        rw [show ee :: (sg ++ b :: ds) = [ee] ++ (sg ++ (b :: ds)) by simp]
        simp only [lexMap_append, hsg']
        have h1 : lexMap [ee] = [0x65] := by simp [lexMap, hee']
        simp [h1, h2, printExp]
    rw [e1, e2, e3, e4]; simp [printNumber]

/-- The bytes `parseNumA` consumed, in canonical form, are the printed lexeme of the number it returns. -/
theorem lexSlice_eq {a : ByteArray} {i j : Nat} {n : Number} (hp : parseNumA a i = some (n, j)) : lexMap (((L a).drop i).take (j - i)) = printNumber n := by
  have h := parseNumA_eq a i
  rw [hp] at h
  simp only [mapDrop, Option.map_some] at h
  obtain ⟨pre, hpre, hN⟩ := parseNum_sound h
  have hij := parseNumA_adv hp
  have e : (L a).drop j = ((L a).drop i).drop (j - i) := by rw [List.drop_drop]; congr 1; omega
  have hs : pre = ((L a).drop i).take (j - i) := by
    have h1 : ((L a).drop i).take (j - i) ++ (L a).drop j = (L a).drop i := by
      have := List.take_append_drop (j - i) ((L a).drop i)
      rwa [← e] at this
    exact (List.append_cancel_right (h1.trans hpre)).symm
  rw [← hs]
  exact num_lex hN

theorem pushLex_eq {a : ByteArray} {i j : Nat} {n : Number} (hp : parseNumA a i = some (n, j)) (b : ByteArray) : pushLex a i j b = pushNumber b n := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [pushLex_list, lexSlice_eq hp, pushNumber_eq]
  simp

/-- F1: the node written from the input bytes is the number's node. -/
theorem numLex_eq {a : ByteArray} {i j : Nat} {n : Number} (hp : parseNumA a i = some (n, j)) (s : TapeBuf) : s.numLex a i j = s.num n := by
  obtain ⟨tape, text⟩ := s
  simp only [TapeBuf.numLex, TapeBuf.num, pushLex_eq hp]

end LeanJson
