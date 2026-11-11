import LeanJsonProofs.Parse
/-! # The fast leaves against the reference leaves

`L a` is the array as a list. Each leaf of `LeanJson/Parse.lean` (`...A`, an index into the array) is shown equal to its reference leaf of `Reference.lean` on the list that starts at the
index: `ref (drop i (L a)) = (fast a i).map (fun (x, j) => (x, drop j (L a)))`: the same verdict, the same value, and the rest the reference leaves is the list that starts where the fast leaf stops. -/
set_option linter.unusedSimpArgs false
namespace LeanJson

def L (a : ByteArray) : Bytes := a.data.toList

theorem byteAt_eq (a : ByteArray) (i : Nat) : byteAt a i = (L a)[i]? := by
  unfold byteAt L
  rw [Array.getElem?_toList]
  by_cases h : i < a.size
  · have h' : i < a.data.size := by rwa [← ByteArray.size_data] at h
    simp [h, ByteArray.getElem_eq_getElem_data]
  · have h' : ¬ i < a.data.size := by rwa [← ByteArray.size_data] at h
    simp [h]

theorem drop_of_some {a : ByteArray} {i : Nat} {x : UInt8} (h : byteAt a i = some x) : (L a).drop i = x :: (L a).drop (i + 1) := by
  rw [byteAt_eq] at h
  obtain ⟨hl, hx⟩ := List.getElem?_eq_some_iff.mp h
  rw [List.drop_eq_getElem_cons hl, hx]

theorem drop_of_none {a : ByteArray} {i : Nat} (h : byteAt a i = none) : (L a).drop i = [] := by
  rw [byteAt_eq] at h
  exact List.drop_eq_nil_of_le (List.getElem?_eq_none_iff.mp h)

theorem byteIs_eq (a : ByteArray) (i : Nat) (c : UInt8) : byteIs a i c = decide (byteAt a i = some c) := by
  unfold byteIs byteAt
  split <;> simp_all <;> rfl


/-- A byte test is a statement about the list. -/
theorem skipWs_eq (a : ByteArray) (i : Nat) : skipWs ((L a).drop i) = (L a).drop (skipWsA a i) := by
  fun_induction skipWsA a i with
  | case1 i h hws ih =>
    rw [drop_of_some (x := a[i]) (by simp [byteAt, h])]
    simp [skipWs, hws, ih]
  | case2 i h hws =>
    rw [drop_of_some (x := a[i]) (by simp [byteAt, h])]
    simp [skipWs, hws]
  | case3 i h =>
    rw [drop_of_none (by simp [byteAt, h])]
    simp [skipWs]

theorem skipWsA_ge (a : ByteArray) (i : Nat) : i ≤ skipWsA a i := by
  fun_induction skipWsA a i with
  | case1 i h hws ih => omega
  | case2 i h hws => omega
  | case3 i h => omega


theorem digitsAcc_eq (a : ByteArray) (i : Nat) (acc : List Digit) :
    (digitsAcc a i acc).1 = (digits ((L a).drop i)).1.reverse ++ acc ∧ (L a).drop (digitsAcc a i acc).2 = (digits ((L a).drop i)).2 := by
  fun_induction digitsAcc a i acc with
  | case1 i acc h d hd ih =>
    rw [drop_of_some (x := a[i]) (by simp [byteAt, h])]
    simp [digits, hd, ih.1, ih.2]
  | case2 i acc h hd =>
    rw [drop_of_some (x := a[i]) (by simp [byteAt, h])]
    simp [digits, hd]
  | case3 i acc h =>
    rw [drop_of_none (by simp [byteAt, h])]
    simp [digits]

theorem digitsAcc_ge (a : ByteArray) (i : Nat) (acc : List Digit) : i ≤ (digitsAcc a i acc).2 := by
  fun_induction digitsAcc a i acc with
  | case1 i acc h d hd ih => omega
  | case2 i acc h hd => omega
  | case3 i acc h => omega

/-- `*DIGIT`. -/
theorem digitsA_eq (a : ByteArray) (i : Nat) :
    digits ((L a).drop i) = ((digitsA a i).1, (L a).drop (digitsA a i).2) := by
  have h := digitsAcc_eq a i []
  simp only [digitsA]
  ext
  · simp [h.1]
  · simp [h.2]

/-- `1*DIGIT`. -/
theorem digits1A_eq (a : ByteArray) (i : Nat) :
    digits1 ((L a).drop i) = (digits1A a i).map fun p => (p.1, (L a).drop p.2) := by
  unfold digits1A
  rcases hb : byteAt a i with _ | b
  · simp [digits1, drop_of_none hb]
  · rw [drop_of_some hb]
    simp only [digits1]
    rcases hd : digitVal b with _ | d
    · simp
    · simp [digitsA_eq]


/-- A `Rel` is how every leaf below is stated. -/
abbrev mapDrop (a : ByteArray) {α : Type} (f : Option (α × Nat)) : Option (α × Bytes) := f.map fun p => (p.1, (L a).drop p.2)

theorem parseIntA_eq (a : ByteArray) (i : Nat) : parseInt ((L a).drop i) = mapDrop a (parseIntA a i) := by
  unfold parseIntA
  rcases hb : byteAt a i with _ | b
  · simp [parseInt, drop_of_none hb]
  · rw [drop_of_some hb]
    by_cases h0 : b = 0x30
    · simp [parseInt, h0, mapDrop]
    · simp only [parseInt, beq_iff_eq, h0, ite_false]
      rcases hd : digit19 b with _ | l
      · simp [h0, hd, mapDrop]
      · simp [h0, hd, mapDrop, digitsA_eq]

theorem parseFracA_eq (a : ByteArray) (i : Nat) : parseFrac ((L a).drop i) = mapDrop a (parseFracA a i) := by
  unfold parseFracA
  rw [byteIs_eq]
  rcases hb : byteAt a i with _ | b
  · simp [parseFrac, drop_of_none hb, mapDrop]
  · by_cases h2 : b = 0x2E
    · subst h2
      simp only [drop_of_some hb, parseFrac, beq_self_eq_true, ite_true, decide_true]
      rw [digits1A_eq]
      cases digits1A a (i + 1) <;> simp [mapDrop]
    · have : decide (some b = some (0x2E : UInt8)) = false := by simp [h2]
      simp [drop_of_some hb, parseFrac, h2, mapDrop, this]

theorem parseESign_eq (a : ByteArray) (i : Nat) :
    parseESign ((L a).drop i) = (byteIs a i 0x2D, (L a).drop (if byteIs a i 0x2B || byteIs a i 0x2D then i + 1 else i)) := by
  rw [byteIs_eq, byteIs_eq]
  rcases hb : byteAt a i with _ | c
  · simp [parseESign, drop_of_none hb]
  · by_cases h1 : c = 0x2B
    · subst h1; simp [parseESign, drop_of_some hb]
    · by_cases h2 : c = 0x2D
      · subst h2; simp [parseESign, drop_of_some hb]
      · simp [parseESign, drop_of_some hb, h1, h2]

theorem parseExpA_eq (a : ByteArray) (i : Nat) : parseExp ((L a).drop i) = mapDrop a (parseExpA a i) := by
  unfold parseExpA
  rw [byteIs_eq, byteIs_eq]
  rcases hb : byteAt a i with _ | e
  · simp [parseExp, drop_of_none hb, mapDrop]
  · by_cases he : e = 0x65 ∨ e = 0x45
    · have : (decide (some e = some (0x65 : UInt8)) || decide (some e = some (0x45 : UInt8))) = true := by
        rcases he with rfl | rfl <;> simp
      have h' : (e == 0x65 || e == 0x45) = true := by rcases he with rfl | rfl <;> simp
      simp only [parseExp, drop_of_some hb, h', this, ite_true, parseExpBody, parseESign_eq, digits1A_eq]
      have e2 : i + 1 + 1 = i + 2 := rfl
      simp only [e2]
      cases digits1A a (if byteIs a (i + 1) 0x2B || byteIs a (i + 1) 0x2D then i + 2 else i + 1) <;> simp [mapDrop]
    · have he1 : e ≠ 0x65 := fun h => he (.inl h)
      have he2 : e ≠ 0x45 := fun h => he (.inr h)
      simp [parseExp, drop_of_some hb, he1, he2, mapDrop]

theorem parseMinus_eq (a : ByteArray) (i : Nat) :
    parseMinus ((L a).drop i) = (byteIs a i 0x2D, (L a).drop (if byteIs a i 0x2D then i + 1 else i)) := by
  rw [byteIs_eq]
  rcases hb : byteAt a i with _ | c
  · simp [parseMinus, drop_of_none hb]
  · by_cases h : c = 0x2D
    · subst h; simp [parseMinus, drop_of_some hb]
    · simp [parseMinus, drop_of_some hb, h]

/-- `number`. -/
theorem parseNumA_eq (a : ByteArray) (i : Nat) : parseNum ((L a).drop i) = mapDrop a (parseNumA a i) := by
  unfold parseNum parseNumA
  simp only [parseMinus_eq, parseIntA_eq]
  rcases hI : parseIntA a (if byteIs a i 0x2D then i + 1 else i) with _ | ⟨ip, i1⟩
  · simp [mapDrop]
  · simp only [mapDrop, Option.map_some]
    simp only [parseFracA_eq]
    rcases hF : parseFracA a i1 with _ | ⟨fr, i2⟩
    · simp [mapDrop]
    · simp only [mapDrop, Option.map_some]
      simp only [parseExpA_eq]
      rcases hE : parseExpA a i2 with _ | ⟨ex, i3⟩ <;> simp [mapDrop]

theorem digitsA_ge (a : ByteArray) (i : Nat) : i ≤ (digitsA a i).2 := by
  simpa [digitsA] using digitsAcc_ge a i []

theorem digits1A_adv {a : ByteArray} {i j : Nat} {p} (h : digits1A a i = some (p, j)) : i < j := by
  unfold digits1A at h
  rcases hb : byteAt a i with _ | b
  · simp [hb] at h
  · rcases hd : digitVal b with _ | d
    · simp [hb, hd] at h
    · simp only [hb, hd, Option.some.injEq, Prod.mk.injEq] at h
      have := digitsA_ge a (i + 1)
      omega

theorem parseIntA_adv {a : ByteArray} {i j : Nat} {p} (h : parseIntA a i = some (p, j)) : i < j := by
  unfold parseIntA at h
  rcases hb : byteAt a i with _ | b
  · simp [hb] at h
  · by_cases h0 : b = 0x30
    · simp [hb, h0] at h; omega
    · rcases hd : digit19 b with _ | d
      · simp [hb, h0, hd] at h
      · simp only [hb, hd, beq_iff_eq, h0, ite_false, Option.some.injEq, Prod.mk.injEq] at h
        have := digitsA_ge a (i + 1)
        omega

theorem parseFracA_ge {a : ByteArray} {i j : Nat} {p} (h : parseFracA a i = some (p, j)) : i ≤ j := by
  unfold parseFracA at h
  split at h
  · rcases hd : digits1A a (i + 1) with _ | ⟨f, j'⟩
    · simp [hd] at h
    · have := digits1A_adv hd
      simp [hd] at h; omega
  · simp at h; omega

theorem parseExpA_ge {a : ByteArray} {i j : Nat} {p} (h : parseExpA a i = some (p, j)) : i ≤ j := by
  unfold parseExpA at h
  split at h
  · simp only at h
    split at h
    · rename_i hd
      have := digits1A_adv hd
      simp at h
      split at this <;> omega
    · simp at h
  · simp at h; omega

theorem parseNumA_adv {a : ByteArray} {i j : Nat} {p} (h : parseNumA a i = some (p, j)) : i < j := by
  unfold parseNumA at h
  rcases hI : parseIntA a (if byteIs a i 0x2D = true then i + 1 else i) with _ | ⟨ip, i1⟩
  · simp [hI] at h
  · rcases hF : parseFracA a i1 with _ | ⟨fr, i2⟩
    · simp [hI, hF] at h
    · rcases hE : parseExpA a i2 with _ | ⟨ex, i3⟩
      · simp [hI, hF, hE] at h
      · simp only [hI, hF, hE, Option.some.injEq, Prod.mk.injEq] at h
        have h1 := parseIntA_adv hI
        have h2 := parseFracA_ge hF
        have h3 := parseExpA_ge hE
        split at h1 <;> omega

theorem drop1_of_some {a : ByteArray} {i : Nat} {x : UInt8} (h : byteAt a (i + 1) = some x) : (L a).drop (i + 1) = x :: (L a).drop (i + 2) := drop_of_some h
theorem drop1_of_none {a : ByteArray} {i : Nat} (h : byteAt a (i + 1) = none) : (L a).drop (i + 1) = [] := drop_of_none h
theorem drop2_of_some {a : ByteArray} {i : Nat} {x : UInt8} (h : byteAt a (i + 2) = some x) : (L a).drop (i + 2) = x :: (L a).drop (i + 3) := drop_of_some h
theorem drop2_of_none {a : ByteArray} {i : Nat} (h : byteAt a (i + 2) = none) : (L a).drop (i + 2) = [] := drop_of_none h
theorem drop3_of_some {a : ByteArray} {i : Nat} {x : UInt8} (h : byteAt a (i + 3) = some x) : (L a).drop (i + 3) = x :: (L a).drop (i + 4) := drop_of_some h
theorem drop3_of_none {a : ByteArray} {i : Nat} (h : byteAt a (i + 3) = none) : (L a).drop (i + 3) = [] := drop_of_none h
theorem drop4_of_some {a : ByteArray} {i : Nat} {x : UInt8} (h : byteAt a (i + 4) = some x) : (L a).drop (i + 4) = x :: (L a).drop (i + 5) := drop_of_some h
theorem drop4_of_none {a : ByteArray} {i : Nat} (h : byteAt a (i + 4) = none) : (L a).drop (i + 4) = [] := drop_of_none h
theorem drop5_of_some {a : ByteArray} {i : Nat} {x : UInt8} (h : byteAt a (i + 5) = some x) : (L a).drop (i + 5) = x :: (L a).drop (i + 6) := drop_of_some h
theorem drop5_of_none {a : ByteArray} {i : Nat} (h : byteAt a (i + 5) = none) : (L a).drop (i + 5) = [] := drop_of_none h
theorem drop6_of_some {a : ByteArray} {i : Nat} {x : UInt8} (h : byteAt a (i + 6) = some x) : (L a).drop (i + 6) = x :: (L a).drop (i + 7) := drop_of_some h
theorem drop6_of_none {a : ByteArray} {i : Nat} (h : byteAt a (i + 6) = none) : (L a).drop (i + 6) = [] := drop_of_none h
theorem drop7_of_some {a : ByteArray} {i : Nat} {x : UInt8} (h : byteAt a (i + 7) = some x) : (L a).drop (i + 7) = x :: (L a).drop (i + 8) := drop_of_some h
theorem drop7_of_none {a : ByteArray} {i : Nat} (h : byteAt a (i + 7) = none) : (L a).drop (i + 7) = [] := drop_of_none h
theorem drop8_of_some {a : ByteArray} {i : Nat} {x : UInt8} (h : byteAt a (i + 8) = some x) : (L a).drop (i + 8) = x :: (L a).drop (i + 9) := drop_of_some h
theorem drop8_of_none {a : ByteArray} {i : Nat} (h : byteAt a (i + 8) = none) : (L a).drop (i + 8) = [] := drop_of_none h
theorem drop9_of_some {a : ByteArray} {i : Nat} {x : UInt8} (h : byteAt a (i + 9) = some x) : (L a).drop (i + 9) = x :: (L a).drop (i + 10) := drop_of_some h
theorem drop9_of_none {a : ByteArray} {i : Nat} (h : byteAt a (i + 9) = none) : (L a).drop (i + 9) = [] := drop_of_none h

theorem decodeUtf8A_eq (a : ByteArray) (i : Nat) : decodeUtf8 ((L a).drop i) = mapDrop a (decodeUtf8A a i) := by
  unfold decodeUtf8A
  rcases hb : byteAt a i with _ | x
  · simp [decodeUtf8, drop_of_none hb, mapDrop]
  · simp only [drop_of_some hb, decodeUtf8]
    by_cases h1 : x.toNat < 0x80
    · simp [h1, mapDrop]
    · by_cases h2 : 0xC2 ≤ x.toNat ∧ x.toNat ≤ 0xDF
      · simp only [h1, h2, ite_false, and_self, ite_true]
        rcases hb1 : byteAt a (i + 1) with _ | b
        · simp [drop1_of_none hb1, mapDrop]
        · simp only [drop1_of_some hb1]
          split <;> simp [mapDrop]
      · by_cases h3 : 0xE0 ≤ x.toNat ∧ x.toNat ≤ 0xEF
        · simp only [h1, h2, h3, ite_false, and_self, ite_true]
          rcases hb1 : byteAt a (i + 1) with _ | b
          · simp [drop1_of_none hb1, mapDrop]
          · rcases hb2 : byteAt a (i + 2) with _ | c
            · simp [drop1_of_some hb1, drop2_of_none hb2, mapDrop]
            · simp only [drop1_of_some hb1, drop2_of_some hb2]
              split <;> simp [mapDrop]
        · by_cases h4 : 0xF0 ≤ x.toNat ∧ x.toNat ≤ 0xF4
          · simp only [h1, h2, h3, h4, ite_false, and_self, ite_true]
            rcases hb1 : byteAt a (i + 1) with _ | b
            · simp [drop1_of_none hb1, mapDrop]
            · rcases hb2 : byteAt a (i + 2) with _ | c
              · simp [drop1_of_some hb1, drop2_of_none hb2, mapDrop]
              · rcases hb3 : byteAt a (i + 3) with _ | d
                · simp [drop1_of_some hb1, drop2_of_some hb2, drop3_of_none hb3, mapDrop]
                · simp only [drop1_of_some hb1, drop2_of_some hb2, drop3_of_some hb3]
                  split <;> simp [mapDrop]
          · simp [h1, h2, h3, h4, mapDrop]

theorem hex4At_eq (a : ByteArray) (i : Nat) : hex4At a i = match (L a).drop i with | w :: x :: y :: z :: _ => hex4 w x y z | _ => none := by
  unfold hex4At
  rcases hb0 : byteAt a i with _ | w
  · simp [drop_of_none hb0]
  · rcases hb1 : byteAt a (i + 1) with _ | x
    · simp [drop_of_some hb0, drop1_of_none hb1]
    · rcases hb2 : byteAt a (i + 2) with _ | y
      · simp [drop_of_some hb0, drop1_of_some hb1, drop2_of_none hb2]
      · rcases hb3 : byteAt a (i + 3) with _ | z
        · simp [drop_of_some hb0, drop1_of_some hb1, drop2_of_some hb2, drop3_of_none hb3]
        · simp [drop_of_some hb0, drop1_of_some hb1, drop2_of_some hb2, drop3_of_some hb3]

theorem decodeUA_eq (a : ByteArray) (i : Nat) : decodeU ((L a).drop i) = mapDrop a (decodeUA a i) := by
  unfold decodeUA
  simp only [hex4At_eq, byteIs_eq]
  rcases hb0 : byteAt a i with _ | w
  · simp [decodeU, drop_of_none hb0, mapDrop]
  · rcases hb1 : byteAt a (i + 1) with _ | x
    · simp [decodeU, drop_of_some hb0, drop1_of_none hb1, mapDrop]
    · rcases hb2 : byteAt a (i + 2) with _ | y
      · simp [decodeU, drop_of_some hb0, drop1_of_some hb1, drop2_of_none hb2, mapDrop]
      · rcases hb3 : byteAt a (i + 3) with _ | z
        · simp [decodeU, drop_of_some hb0, drop1_of_some hb1, drop2_of_some hb2, drop3_of_none hb3, mapDrop]
        · simp only [decodeU, drop_of_some hb0, drop1_of_some hb1, drop2_of_some hb2, drop3_of_some hb3]
          rcases hh : hex4 w x y z with _ | n
          · simp [mapDrop]
          · by_cases hn : n < 0xD800 ∨ 0xE000 ≤ n
            · simp [hn, mapDrop]
            · by_cases hn2 : n < 0xDC00
              · simp only [hn, hn2, ite_true, ite_false]
                rcases hb4 : byteAt a (i + 4) with _ | e
                · simp [drop4_of_none hb4, mapDrop]
                · rcases hb5 : byteAt a (i + 5) with _ | f
                  · simp [drop4_of_some hb4, drop5_of_none hb5, mapDrop]
                  · rcases hb6 : byteAt a (i + 6) with _ | a'
                    · simp [drop4_of_some hb4, drop5_of_some hb5, drop6_of_none hb6, mapDrop]
                    · rcases hb7 : byteAt a (i + 7) with _ | b'
                      · simp [drop4_of_some hb4, drop5_of_some hb5, drop6_of_some hb6, drop7_of_none hb7, mapDrop]
                      · rcases hb8 : byteAt a (i + 8) with _ | c'
                        · simp [drop4_of_some hb4, drop5_of_some hb5, drop6_of_some hb6, drop7_of_some hb7, drop8_of_none hb8, mapDrop]
                        · rcases hb9 : byteAt a (i + 9) with _ | d'
                          · simp [drop4_of_some hb4, drop5_of_some hb5, drop6_of_some hb6, drop7_of_some hb7, drop8_of_some hb8, drop9_of_none hb9, mapDrop]
                          · simp only [drop4_of_some hb4, drop5_of_some hb5, drop6_of_some hb6, drop7_of_some hb7, drop8_of_some hb8, drop9_of_some hb9]
                            by_cases hef : e = 92 ∧ f = 117
                            · simp only [hef, and_self, ite_true]
                              rcases hh2 : hex4 a' b' c' d' with _ | lo
                              · simp [mapDrop]
                              · by_cases hlo : 56320 ≤ lo ∧ lo < 57344 <;> simp [hlo, mapDrop]
                            · simp [hef, mapDrop]
              · simp [hn, hn2, mapDrop]

/-- The decoders move forward. -/
theorem decodeUtf8A_adv {a : ByteArray} {i n j : Nat} (h : decodeUtf8A a i = some (n, j)) : i < j := by
  unfold decodeUtf8A at h
  repeat' split at h
  all_goals first | (simp at h; omega) | skip
  all_goals simp_all <;> omega

theorem decodeUA_adv {a : ByteArray} {i n j : Nat} (h : decodeUA a i = some (n, j)) : i < j := by
  unfold decodeUA at h
  repeat' split at h
  all_goals first | (simp at h; omega) | skip
  all_goals simp_all <;> omega

theorem decodeCharA_adv {a : ByteArray} {i n j : Nat} (h : decodeCharA a i = some (n, j)) : i < j := by
  unfold decodeCharA at h
  repeat' split at h
  all_goals first | (simp at h; done) | skip
  · have := decodeUA_adv h; omega
  · simp at h; omega
  · simp at h
    obtain ⟨-, rfl⟩ := h
    exact decodeUtf8A_adv ‹_›


theorem decodeCharA_eq (a : ByteArray) (i : Nat) : decodeChar ((L a).drop i) = mapDrop a (decodeCharA a i) := by
  unfold decodeCharA
  rw [byteIs_eq]
  rcases hb : byteAt a i with _ | x
  · simp [decodeChar, drop_of_none hb, mapDrop, decodeUtf8A, hb]
  · by_cases h92 : x = 0x5C
    · subst h92
      simp only [decodeChar, drop_of_some hb, beq_self_eq_true, ite_true, decide_true]
      rcases hb1 : byteAt a (i + 1) with _ | b
      · simp [decodeEsc, drop1_of_none hb1, mapDrop]
      · simp only [decodeEsc, drop1_of_some hb1]
        by_cases hu : b = 0x75
        · subst hu
          simp [decodeUA_eq, mapDrop]
        · simp [hu, mapDrop]
          cases simpleEsc b <;> simp
    · have h1 : (x == 0x5C) = false := by simpa using h92
      have h2 : decide (some x = some (0x5C : UInt8)) = false := by simpa using h92
      have hu := decodeUtf8A_eq a i
      rw [drop_of_some hb] at hu
      simp only [decodeChar, drop_of_some hb, h1, h2, hu]
      simp only [Bool.false_eq_true, ite_false, decide_false]
      rcases decodeUtf8A a i with _ | ⟨n, j⟩
      · simp [mapDrop]
      · by_cases hc : 0x20 ≤ n ∧ n ≠ 0x22 ∧ n ≠ 0x5C <;> simp [hc, mapDrop]

/-- A plain ASCII byte (not `"`) is one character, itself: the fast path of `strLoop` is `decodeCharA`'s answer without the call. -/
theorem decodeCharA_plain {a : ByteArray} {i : Nat} (h : i < a.size) (h22 : ¬ (a[i] == 0x22) = true) (hp : plainAscii a[i] = true) :
    decodeCharA a i = some (a[i].toNat, i + 1) := by
  have hb : byteAt a i = some a[i] := by simp [byteAt, h]
  simp only [plainAscii, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hp
  obtain ⟨⟨h1, h2⟩, h3⟩ := hp
  have h3' : a[i].toNat ≠ 0x5C := fun e => h3 (UInt8.toNat_inj.mp e)
  have h22' : a[i].toNat ≠ 0x22 := fun e => h22 (by simp [UInt8.toNat_inj.mp (show a[i].toNat = (34 : UInt8).toNat from e)])
  have h5 : byteIs a i 0x5C = false := by
    simp only [byteIs, h, dite_true, beq_eq_false_iff_ne, ne_eq]; exact h3
  simp [decodeCharA, h5, decodeUtf8A, hb, h2, h1, h3', h22']

theorem str_push (s : String) (c : Char) (l : List Char) : s ++ String.ofList (c :: l) = s.push c ++ String.ofList l := by
  apply String.toList_injective
  simp

/-- A step of `strLoop` that consumes one decoded character: `decodeCharA a i = some (n, j)` is what the reference's `parseChars` reads, so the two agree when they agree on the rest. -/
theorem strLoop_step {a : ByteArray} {i : Nat} {s : String} {n j k' : Nat} (h : i < a.size) (h22 : ¬ (a[i] == 0x22) = true) (hd : decodeCharA a i = some (n, j))
    (ih : (parseChars k' ((L a).drop j)).map (fun p => (s.push (Char.ofNat n) ++ String.ofList (p.1.map Char.ofNat), p.2)) = mapDrop a (strLoop a j (s.push (Char.ofNat n)))) :
    (parseChars (k' + 1) ((L a).drop i)).map (fun p => (s ++ String.ofList (p.1.map Char.ofNat), p.2)) = mapDrop a (strLoop a j (s.push (Char.ofNat n))) := by
  have hb : byteAt a i = some a[i] := by simp [byteAt, h]
  have h22' : ¬ a[i] = 34 := by simpa using h22
  have hc := decodeCharA_eq a i
  rw [hd] at hc
  rw [drop_of_some hb] at hc ⊢
  simp only [parseChars, h22', beq_iff_eq, ite_false, hc]
  simp only [mapDrop, Option.map_some, Bool.false_eq_true, ite_false]
  rcases hp : parseChars k' ((L a).drop j) with _ | ⟨cs, r⟩
  · rw [hp] at ih
    simpa [mapDrop] using ih
  · rw [hp] at ih
    simp only [Option.map_some, mapDrop] at ih ⊢
    rw [← ih, List.map_cons, str_push]

/-- The string read so far plus the scalars: what the reference builds in one go. -/
theorem strLoop_eq (a : ByteArray) (i : Nat) (s : String) (k : Nat) (hk : a.size - i + 1 ≤ k) :
    (parseChars k ((L a).drop i)).map (fun p => (s ++ String.ofList (p.1.map Char.ofNat), p.2)) = mapDrop a (strLoop a i s) := by
  induction i, s using strLoop.induct a generalizing k with
  | case1 i s h h22 =>
    have hb : byteAt a i = some a[i] := by simp [byteAt, h]
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [beq_iff_eq] at h22
    rw [strLoop]
    simp [drop_of_some hb, h22, h, parseChars, mapDrop]
  | case2 i s h h22 hp ih =>
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [strLoop]
    simp only [h, hp, ite_true, h22, dite_true]
    exact strLoop_step h h22 (decodeCharA_plain h h22 hp) (ih k' (by omega))
  | case3 i s h h22 hp n j hd hij ih =>
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [strLoop]
    simp only [h, hij, hp, ite_true, h22, dite_true, hd, Bool.false_eq_true, ite_false]
    exact strLoop_step h h22 hd (ih k' (by omega))
  | case4 i s h h22 hp n j hd hij => exact absurd (decodeCharA_adv hd) hij
  | case5 i s h h22 hp hd =>
    have hb : byteAt a i = some a[i] := by simp [byteAt, h]
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have h22' : ¬ a[i] = 34 := by simpa using h22
    have hc := decodeCharA_eq a i
    rw [hd] at hc
    rw [drop_of_some hb] at hc
    rw [strLoop]
    simp [h, h22, hp, hd, drop_of_some hb, parseChars, h22', hc, mapDrop]
  | case6 i s h =>
    have hb : byteAt a i = none := by simp [byteAt, h]
    rw [strLoop]
    cases k <;> simp [h, drop_of_none hb, parseChars, mapDrop]

theorem strLoop_adv (a : ByteArray) (i : Nat) (s : String) {s' : String} {j : Nat} (h : strLoop a i s = some (s', j)) : i < j := by
  induction i, s using strLoop.induct a generalizing s' j with
  | case1 i s h1 h22 => rw [strLoop] at h; simp [h1, h22] at h; omega
  | case2 i s h1 h22 hp ih =>
    rw [strLoop] at h
    simp only [h1, h22, hp, ite_true, dite_true] at h
    have := ih h
    omega
  | case3 i s h1 h22 hp n j' hd hij ih =>
    rw [strLoop] at h
    simp only [h1, h22, hp, hd, hij, ite_true, dite_true, Bool.false_eq_true, ite_false] at h
    have := ih h
    omega
  | case4 i s h1 h22 hp n j' hd hij => exact absurd (decodeCharA_adv hd) hij
  | case5 i s h1 h22 hp hd => rw [strLoop] at h; simp [h1, h22, hp, hd] at h
  | case6 i s h1 => rw [strLoop] at h; simp [h1] at h

theorem match_map (q : Option (List Nat × Bytes)) :
    (match q with | some (ns, r') => some (String.ofList (ns.map Char.ofNat), r') | none => none) =
      q.map (fun p => (String.ofList (p.1.map Char.ofNat), p.2)) := by
  rcases q with _ | ⟨ns, r⟩ <;> rfl

theorem parseStrA_eq (a : ByteArray) (i : Nat) : parseStr ((L a).drop i) = mapDrop a (parseStrA a i) := by
  unfold parseStrA
  rw [byteIs_eq]
  rcases hb : byteAt a i with _ | x
  · simp [parseStr, drop_of_none hb, mapDrop]
  · by_cases h : x = 0x22
    · subst h
      simp only [parseStr, drop_of_some hb, beq_self_eq_true, ite_true, decide_true]
      have := strLoop_eq a (i + 1) "" (((L a).drop (i + 1)).length + 1) (by simp [L])
      simp only [String.empty_append] at this
      rw [← this]
      exact match_map _
    · simp [parseStr, drop_of_some hb, h, mapDrop]

theorem parseStrA_adv {a : ByteArray} {i j : Nat} {p} (h : parseStrA a i = some (p, j)) : i < j := by
  unfold parseStrA at h
  split at h
  · rcases hs : strLoop a (i + 1) "" with _ | ⟨s', j'⟩
    · simp [hs] at h
    · have := strLoop_adv a (i + 1) "" hs
      simp [hs] at h; omega
  · simp at h

/-- The reference's key leaves the rest after the colon (the caller skips whitespace); the fast key has already skipped it. -/
theorem parseKeyA_eq (a : ByteArray) (i : Nat) :
    (parseKey ((L a).drop i)).map (fun p => (p.1, skipWs p.2)) = mapDrop a (parseKeyA a i) := by
  unfold parseKey parseKeyA
  rw [parseStrA_eq]
  rcases parseStrA a i with _ | ⟨s, j⟩
  · simp [mapDrop]
  · simp only [mapDrop, Option.map_some, skipWs_eq]
    rw [byteIs_eq]
    rcases hb : byteAt a (skipWsA a j) with _ | c
    · simp [drop_of_none hb]
    · by_cases hc : c = 0x3A
      · subst hc
        simp [drop_of_some hb, skipWs_eq]
      · simp [drop_of_some hb, hc]

theorem parseKeyA_adv {a : ByteArray} {i j : Nat} {p} (h : parseKeyA a i = some (p, j)) : i < j := by
  unfold parseKeyA at h
  rcases hs : parseStrA a i with _ | ⟨s, j1⟩
  · simp [hs] at h
  · have h1 := parseStrA_adv hs
    have h2 := skipWsA_ge a j1
    have h3 := skipWsA_ge a (skipWsA a j1 + 1)
    simp only [hs] at h
    split at h
    · simp at h; omega
    · simp at h

theorem litA_eq (a : ByteArray) (l : Bytes) (i : Nat) : lit l ((L a).drop i) = (litA a i l).map fun j => (L a).drop j := by
  induction l generalizing i with
  | nil => simp [lit, litA]
  | cons x xs ih =>
    unfold litA
    rw [byteIs_eq]
    rcases hb : byteAt a i with _ | y
    · simp [lit, drop_of_none hb]
    · by_cases h : x = y
      · subst h; simp [lit, drop_of_some hb, ih]
      · have h' : ¬ y = x := fun e => h e.symm
        simp [lit, drop_of_some hb, h, h']

theorem litA_ge (a : ByteArray) (l : Bytes) (i j : Nat) (h : litA a i l = some j) : i ≤ j ∧ (l ≠ [] → i < j) := by
  induction l generalizing i with
  | nil => simp [litA] at h; subst h; simp
  | cons x xs ih =>
    unfold litA at h
    split at h
    · have := ih (i + 1) h
      exact ⟨by omega, fun _ => by omega⟩
    · simp at h

end LeanJson
