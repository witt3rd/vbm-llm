import LeanJsonProofs.Leaf
/-! # The reference against the grammar: UTF-8, escapes, strings

A character is a prefix-free code (the first byte fixes its length and kind), so `*_complete` holds whatever follows: no follow condition is needed here. -/
namespace LeanJson

theorem utf8_sound {bs : Bytes} {n r} (h : decodeUtf8 bs = some (n, r)) : ∃ pre, bs = pre ++ r ∧ Utf8 pre n := by
  cases bs with
  | nil => simp [decodeUtf8] at h
  | cons a rs =>
    by_cases h1 : a.toNat < 0x80
    · simp [decodeUtf8, h1] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨[a], rfl, .u1 h1⟩
    have e1 : (a.toNat < 0x80) = False := eq_false h1
    by_cases h2 : 0xC2 ≤ a.toNat ∧ a.toNat ≤ 0xDF
    · cases rs with
      | nil => simp [decodeUtf8, e1, h2] at h
      | cons b r' =>
        by_cases ht : Tail b
        · simp [decodeUtf8, e1, h2, ht] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨[a, b], rfl, .u2 h2.1 h2.2 ht⟩
        · simp [decodeUtf8, e1, h2, ht] at h
    have e2 : (0xC2 ≤ a.toNat ∧ a.toNat ≤ 0xDF) = False := eq_false h2
    by_cases h3 : 0xE0 ≤ a.toNat ∧ a.toNat ≤ 0xEF
    · match rs, h with
      | [], h => simp [decodeUtf8, e1, e2, h3] at h
      | [_], h => simp [decodeUtf8, e1, e2, h3] at h
      | b :: c :: r', h =>
        by_cases ht : Second3 a b ∧ Tail c
        · simp [decodeUtf8, e1, e2, h3, ht] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨[a, b, c], rfl, .u3 h3.1 h3.2 ht.1 ht.2⟩
        · simp [decodeUtf8, e1, e2, h3, ht] at h
    have e3 : (0xE0 ≤ a.toNat ∧ a.toNat ≤ 0xEF) = False := eq_false h3
    by_cases h4 : 0xF0 ≤ a.toNat ∧ a.toNat ≤ 0xF4
    · match rs, h with
      | [], h => simp [decodeUtf8, e1, e2, e3, h4] at h
      | [_], h => simp [decodeUtf8, e1, e2, e3, h4] at h
      | [_, _], h => simp [decodeUtf8, e1, e2, e3, h4] at h
      | b :: c :: d :: r', h =>
        by_cases ht : Second4 a b ∧ Tail c ∧ Tail d
        · simp [decodeUtf8, e1, e2, e3, h4, ht] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨[a, b, c, d], rfl, .u4 h4.1 h4.2 ht.1 ht.2.1 ht.2.2⟩
        · simp [decodeUtf8, e1, e2, e3, h4, ht] at h
    · have e4 : (0xF0 ≤ a.toNat ∧ a.toNat ≤ 0xF4) = False := eq_false h4
      simp [decodeUtf8, e1, e2, e3, e4] at h

theorem utf8_complete {pre : Bytes} {n : Nat} (h : Utf8 pre n) (rest : Bytes) : decodeUtf8 (pre ++ rest) = some (n, rest) := by
  cases h with
  | u1 ha => simp [decodeUtf8, ha]
  | @u2 a b ha hb ht =>
    have e1 : (a.toNat < 0x80) = False := eq_false (by omega)
    simp [decodeUtf8, e1, ha, hb, ht]
  | @u3 a b c ha hb hs ht =>
    have e1 : (a.toNat < 0x80) = False := eq_false (by omega)
    have e2 : (0xC2 ≤ a.toNat ∧ a.toNat ≤ 0xDF) = False := eq_false (by omega)
    simp [decodeUtf8, e1, e2, ha, hb, hs, ht]
  | @u4 a b c d ha hb hs ht hu =>
    have e1 : (a.toNat < 0x80) = False := eq_false (by omega)
    have e2 : (0xC2 ≤ a.toNat ∧ a.toNat ≤ 0xDF) = False := eq_false (by omega)
    have e3 : (0xE0 ≤ a.toNat ∧ a.toNat ≤ 0xEF) = False := eq_false (by omega)
    simp [decodeUtf8, e1, e2, e3, ha, hb, hs, ht, hu]

/-- The first byte of a UTF-8 character: a single byte stands for itself; a lead byte is not an ASCII byte. -/
theorem utf8_head {pre : Bytes} {n : Nat} (h : Utf8 pre n) : ∃ a r, pre = a :: r ∧ (a.toNat < 0x80 → n = a.toNat) := by
  cases h with
  | u1 ha => exact ⟨_, [], rfl, fun _ => rfl⟩
  | u2 ha hb ht => exact ⟨_, _, rfl, fun h => by omega⟩
  | u3 ha hb hs ht => exact ⟨_, _, rfl, fun h => by omega⟩
  | u4 ha hb hs ht hu => exact ⟨_, _, rfl, fun h => by omega⟩

theorem hex4_sound {a b c d : UInt8} {n : Nat} (h : hex4 a b c d = some n) : Hex4 [a, b, c, d] n := by
  unfold hex4 at h
  split at h
  · rename_i w x y z ha hb hc hd; simp at h; subst h; exact .mk ha hb hc hd
  · simp at h

theorem hex4_complete {a b c d : UInt8} {n : Nat} (h : Hex4 [a, b, c, d] n) : hex4 a b c d = some n := by
  cases h with
  | mk ha hb hc hd => simp [hex4, ha, hb, hc, hd]

theorem decodeU_sound {bs : Bytes} {n r} (h : decodeU bs = some (n, r)) : ∃ pre, bs = pre ++ r ∧ Esc (0x5C :: 0x75 :: pre) n := by
  match bs, h with
  | [], h => simp [decodeU] at h
  | [_], h => simp [decodeU] at h
  | [_, _], h => simp [decodeU] at h
  | [_, _, _], h => simp [decodeU] at h
  | a :: b :: c :: d :: rs, h =>
    unfold decodeU at h
    cases hh : hex4 a b c d with
    | none => simp [hh] at h
    | some n0 =>
      have H1 := hex4_sound hh
      by_cases hs : n0 < 0xD800 ∨ 0xE000 ≤ n0
      · simp [hh, hs] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨[a, b, c, d], rfl, .uni H1 hs⟩
      · have hlo : n0 < 0xDC00 := by
          by_cases hlo : n0 < 0xDC00
          · exact hlo
          · exfalso; simp [hh, hs, hlo] at h
        have hhi : 0xD800 ≤ n0 := by omega
        simp only [hh, hs, hlo] at h
        simp only [ite_false, ite_true] at h
        match rs, h with
        | [], h => simp at h
        | [_], h => simp at h
        | [_, _], h => simp at h
        | [_, _, _], h => simp at h
        | [_, _, _, _], h => simp at h
        | [_, _, _, _, _], h => simp at h
        | e :: f :: a' :: b' :: c' :: d' :: r', h =>
          by_cases hef : (e == 0x5C && f == 0x75) = true
          · have hef' := hef; simp at hef'; obtain ⟨rfl, rfl⟩ := hef'
            simp only [hef, ite_true] at h
            cases hl : hex4 a' b' c' d' with
            | none => simp [hl] at h
            | some lo =>
              by_cases hl2 : 0xDC00 ≤ lo ∧ lo < 0xE000
              · simp [hl, hl2] at h; obtain ⟨rfl, rfl⟩ := h
                exact ⟨[a, b, c, d, 0x5C, 0x75, a', b', c', d'], rfl, .pair H1 (hex4_sound hl) hhi hlo hl2.1 hl2.2⟩
              · simp [hl, hl2] at h
          · simp [hef] at h

theorem hex4_shape {h : Bytes} {n : Nat} (H : Hex4 h n) : ∃ a b c d, h = [a, b, c, d] := by
  cases H with
  | mk => exact ⟨_, _, _, _, rfl⟩

theorem decodeU_complete {h : Bytes} {n : Nat} (he : Esc (0x5C :: 0x75 :: h) n) (rest : Bytes) : decodeU (h ++ rest) = some (n, rest) := by
  cases he with
  | simple hs => simp [simpleEsc] at hs
  | uni hh hn =>
    obtain ⟨a, b, c, d, rfl⟩ := hex4_shape hh
    simp [decodeU, hex4_complete hh, hn]
  | @pair h1 h2 hi lo H1 H2 a b c d =>
    obtain ⟨a1, b1, c1, d1, rfl⟩ := hex4_shape H1
    obtain ⟨a2, b2, c2, d2, rfl⟩ := hex4_shape H2
    have n1 : ¬ (hi < 0xD800 ∨ 0xE000 ≤ hi) := by omega
    simp [decodeU, hex4_complete H1, hex4_complete H2, n1, b, c, d]

theorem decodeEsc_sound {bs : Bytes} {n r} (h : decodeEsc bs = some (n, r)) : ∃ pre, bs = pre ++ r ∧ Esc (0x5C :: pre) n := by
  cases bs with
  | nil => simp [decodeEsc] at h
  | cons b rs =>
    by_cases hb : b = 0x75
    · subst hb
      simp only [decodeEsc, beq_self_eq_true, ite_true] at h
      obtain ⟨pre, hp, he⟩ := decodeU_sound h
      exact ⟨0x75 :: pre, by simp [hp], he⟩
    · simp only [decodeEsc, beq_iff_eq, hb, ite_false] at h
      cases hs : simpleEsc b with
      | none => simp [hs] at h
      | some m => simp [hs] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨[b], rfl, .simple hs⟩

theorem decodeChar_sound {bs : Bytes} {n r} (h : decodeChar bs = some (n, r)) : ∃ pre, bs = pre ++ r ∧ StrChar pre n := by
  cases bs with
  | nil => simp [decodeChar] at h
  | cons a rs =>
    by_cases ha : a = 0x5C
    · subst ha
      simp only [decodeChar, beq_self_eq_true, ite_true] at h
      obtain ⟨pre, hp, he⟩ := decodeEsc_sound h
      exact ⟨0x5C :: pre, by simp [hp], .esc he⟩
    · simp only [decodeChar, beq_iff_eq, ha, ite_false] at h
      cases hu : decodeUtf8 (a :: rs) with
      | none => simp [hu] at h
      | some p =>
        obtain ⟨m, r1⟩ := p
        by_cases hc : 0x20 ≤ m ∧ m ≠ 0x22 ∧ m ≠ 0x5C
        · simp [hu, hc] at h; obtain ⟨rfl, rfl⟩ := h
          obtain ⟨pre, hp, hU⟩ := utf8_sound hu
          exact ⟨pre, hp, .plain hU hc.1 hc.2.1 hc.2.2⟩
        · simp [hu, hc] at h

theorem strChar_head {pre : Bytes} {n : Nat} (h : StrChar pre n) : ∃ a r, pre = a :: r ∧ a ≠ 0x22 := by
  cases h with
  | plain hu h20 h22 h5c =>
    obtain ⟨a, r, rfl, hh⟩ := utf8_head hu
    refine ⟨a, r, rfl, fun e => h22 (hh (by subst e; decide) ▸ by subst e; rfl)⟩
  | esc he => cases he <;> exact ⟨_, _, rfl, by decide⟩

theorem decodeChar_complete {pre : Bytes} {n : Nat} (h : StrChar pre n) (rest : Bytes) : decodeChar (pre ++ rest) = some (n, rest) := by
  cases h with
  | plain hu h20 h22 h5c =>
    obtain ⟨a, r, rfl, hh⟩ := utf8_head hu
    have ha : a ≠ 0x5C := fun e => h5c (hh (by subst e; decide) ▸ by subst e; rfl)
    have hU := utf8_complete hu rest
    simp only [List.cons_append] at hU ⊢
    simp [decodeChar, ha, hU, h20, h22, h5c]
  | esc he =>
    cases he with
    | @simple b m hs =>
      have hb : b ≠ 0x75 := by intro e; subst e; simp [simpleEsc] at hs
      simp [decodeChar, decodeEsc, hb, hs]
    | uni hh hn => simp [decodeChar, decodeEsc, decodeU_complete (.uni hh hn)]
    | pair h1 h2 a b c d =>
      have hU := decodeU_complete (.pair h1 h2 a b c d) rest
      simp only [List.append_assoc, List.cons_append] at hU ⊢
      simp [decodeChar, decodeEsc]; exact hU

theorem parseChars_sound (k : Nat) : ∀ {bs : Bytes} {ns r}, parseChars k bs = some (ns, r) → ∃ cs, bs = cs ++ 0x22 :: r ∧ Chars cs ns := by
  induction k with
  | zero => intro bs ns r h; simp [parseChars] at h
  | succ k ih =>
    intro bs ns r h
    cases bs with
    | nil => simp [parseChars] at h
    | cons a rs =>
      by_cases ha : a = 0x22
      · subst ha; simp [parseChars] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨[], rfl, .nil⟩
      · simp only [parseChars, beq_iff_eq, ha, ite_false] at h
        cases hd : decodeChar (a :: rs) with
        | none => simp [hd] at h
        | some p =>
          obtain ⟨c, r1⟩ := p
          simp only [hd] at h
          cases hr : parseChars k r1 with
          | none => simp [hr] at h
          | some q =>
            obtain ⟨cs, r2⟩ := q
            simp [hr] at h; obtain ⟨rfl, rfl⟩ := h
            obtain ⟨pc, hpc, hS⟩ := decodeChar_sound hd
            obtain ⟨cs', hcs, hC⟩ := ih hr
            exact ⟨pc ++ cs', by rw [hpc, hcs]; simp, .cons hS hC⟩

theorem strChar_ne_nil {pre : Bytes} {n : Nat} (h : StrChar pre n) : 0 < pre.length := by
  obtain ⟨a, r, rfl, _⟩ := strChar_head h; simp

theorem parseChars_complete {cs : Bytes} {ns : List Nat} (h : Chars cs ns) (rest : Bytes) :
    ∀ k, cs.length < k → parseChars k (cs ++ 0x22 :: rest) = some (ns, rest) := by
  induction h with
  | nil => intro k hk; cases k with
    | zero => omega
    | succ k => simp [parseChars]
  | @cons b bs n ns hS hC ih =>
    intro k hk
    have hl := strChar_ne_nil hS
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at hk; omega⟩
    obtain ⟨a, r, rfl, ha⟩ := strChar_head hS
    have := decodeChar_complete hS (bs ++ 0x22 :: rest)
    have ih' := ih (k := k) (by simp at hk ⊢; omega)
    simp only [List.cons_append] at this ⊢
    simp [parseChars, ha, this, ih']

theorem parseStr_sound {bs : Bytes} {s r} (h : parseStr bs = some (s, r)) : ∃ pre, bs = pre ++ r ∧ Str pre s := by
  cases bs with
  | nil => simp [parseStr] at h
  | cons a rs =>
    by_cases ha : a = 0x22
    · subst ha
      simp only [parseStr, beq_self_eq_true, ite_true] at h
      cases hc : parseChars (rs.length + 1) rs with
      | none => simp [hc] at h
      | some q =>
        obtain ⟨ns, r1⟩ := q
        simp [hc] at h; obtain ⟨rfl, rfl⟩ := h
        obtain ⟨cs, hcs, hC⟩ := parseChars_sound _ hc
        exact ⟨0x22 :: (cs ++ [0x22]), by simp [hcs], .mk hC⟩
    · simp [parseStr, ha] at h

theorem parseStr_complete {pre : Bytes} {s : String} (h : Str pre s) (rest : Bytes) : parseStr (pre ++ rest) = some (s, rest) := by
  cases h with
  | @mk cs ns hC =>
    have := parseChars_complete hC rest ((cs ++ 0x22 :: rest).length + 1) (by simp; omega)
    have e : (0x22 :: (cs ++ [0x22]) ++ rest) = 0x22 :: (cs ++ 0x22 :: rest) := by simp
    rw [e]
    simp only [parseStr, beq_self_eq_true, ite_true]
    rw [this]

end LeanJson
