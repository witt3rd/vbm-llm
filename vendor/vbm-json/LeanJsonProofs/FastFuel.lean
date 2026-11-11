import LeanJsonProofs.Parse
/-! # The reference's fuel does not matter

`parseVal`, `parseElems` and `parseMembers` spend one unit of fuel per nested call. Every call that succeeds consumes at least one byte, so `2 * length + 2` units are more than enough, and
more fuel changes nothing: the result is the same for every fuel from that bound up (`parseVal_fuel`, `parseElems_fuel`, `parseMembers_fuel`). The refinement proof compares the fast parser with the
reference at its canonical fuel (`pv`, `pe`, `pm`) and needs the reference's own recursive calls, which have less, to agree with it. -/
namespace LeanJson

theorem parseVal_len {d n : Nat} {bs : Bytes} {v : Value} {r : Bytes} (h : parseVal d n bs = .ok (v, r)) : r.length < bs.length := by
  obtain ⟨⟨pre, hp, hV⟩, _⟩ := (parse_sound_aux n).1 d bs v r h
  have := val_ne_nil hV
  subst hp; simp; omega

theorem parseElems_len {d n : Nat} {bs : Bytes} {vs : List Value} {r : Bytes} (h : parseElems d n bs = .ok (vs, r)) : r.length < bs.length := by
  obtain ⟨⟨pre, hp, hV⟩, _⟩ := (parse_sound_aux n).2.1 d bs vs r h
  obtain ⟨b, r', hb, _⟩ := elems_head hV
  subst hp; subst hb; simp; omega

theorem parseMembers_len {d n : Nat} {bs : Bytes} {kvs : List (String × Value)} {r : Bytes} (h : parseMembers d n bs = .ok (kvs, r)) : r.length < bs.length := by
  obtain ⟨⟨pre, hp, hV⟩, _⟩ := (parse_sound_aux n).2.2 d bs kvs r h
  obtain ⟨b, r', hb, _⟩ := members_head hV
  subst hp; subst hb; simp; omega

theorem parseKey_len {bs : Bytes} {k : String} {r : Bytes} (h : parseKey bs = some (k, r)) : r.length < bs.length := by
  obtain ⟨kb, w, r', hbs, hK, _, rfl⟩ := parseKey_sound h
  cases hK with
  | mk => subst hbs; simp; omega

theorem skipWs_len (bs : Bytes) : (skipWs bs).length ≤ bs.length := by
  obtain ⟨w, hw, _⟩ := skipWs_sound bs
  conv => rhs; rw [hw]
  simp

theorem fuel_succ (n : Nat) :
    (∀ d bs, 2 * bs.length + 1 ≤ n → parseVal d (n + 1) bs = parseVal d n bs) ∧
    (∀ d bs, 2 * bs.length + 2 ≤ n → parseElems d (n + 1) bs = parseElems d n bs) ∧
    (∀ d bs, 2 * bs.length + 2 ≤ n → parseMembers d (n + 1) bs = parseMembers d n bs) := by
  induction n with
  | zero => refine ⟨?_, ?_, ?_⟩ <;> intro d bs h <;> omega
  | succ m ih =>
    obtain ⟨ihV, ihE, ihM⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · intro d bs hn
      cases bs with
      | nil => simp [parseVal]
      | cons b r0 =>
        by_cases hb1 : b = 0x5B
        · subst hb1
          simp only [parseVal, beq_self_eq_true, ite_true]
          cases d with
          | zero => rfl
          | succ d' =>
            cases hs : skipWs r0 with
            | nil => rfl
            | cons c r' =>
              have hl := skipWs_len r0
              rw [hs] at hl
              by_cases hc : c = 0x5D
              · subst hc; rfl
              · simp only [beq_iff_eq, hc, ite_false]
                rw [ihE d' (c :: r') (by simp at hl hn ⊢; omega)]
        · by_cases hb2 : b = 0x7B
          · subst hb2
            simp only [parseVal, show ((0x7B : UInt8) == 0x5B) = false by decide, beq_self_eq_true, ite_true, ite_false, Bool.false_eq_true]
            cases d with
            | zero => rfl
            | succ d' =>
              cases hs : skipWs r0 with
              | nil => rfl
              | cons c r' =>
                have hl := skipWs_len r0
                rw [hs] at hl
                by_cases hc : c = 0x7D
                · subst hc; rfl
                · simp only [beq_iff_eq, hc, ite_false]
                  rw [ihM d' (c :: r') (by simp at hl hn ⊢; omega)]
          · simp [parseVal, hb1, hb2]
    · intro d bs hn
      rw [parseElems.eq_2 d bs (m + 1), parseElems.eq_2 d bs m]
      rw [ihV d bs (by omega)]
      cases hv : parseVal d m bs with
      | error e => rfl
      | ok p =>
        obtain ⟨v, r1⟩ := p
        have hl := parseVal_len hv
        simp only
        cases hs : skipWs r1 with
        | nil => rfl
        | cons c r' =>
          have hl2 := skipWs_len r1
          rw [hs] at hl2
          have hl3 := skipWs_len r'
          simp only
          by_cases hc : c = 0x2C
          · subst hc
            simp only [beq_self_eq_true, ite_true]
            rw [ihE d (skipWs r') (by simp at hl2; omega)]
          · simp [hc]
    · intro d bs hn
      rw [parseMembers.eq_2 d bs (m + 1), parseMembers.eq_2 d bs m]
      cases hk : parseKey bs with
      | none => rfl
      | some p =>
        obtain ⟨k, r0⟩ := p
        have hkl := parseKey_len hk
        have hl0 := skipWs_len r0
        simp only
        rw [ihV d (skipWs r0) (by omega)]
        cases hv : parseVal d m (skipWs r0) with
        | error e => rfl
        | ok q =>
          obtain ⟨v, r1⟩ := q
          have hl := parseVal_len hv
          simp only
          cases hs : skipWs r1 with
          | nil => rfl
          | cons c r' =>
            have hl2 := skipWs_len r1
            rw [hs] at hl2
            have hl3 := skipWs_len r'
            simp only
            by_cases hc : c = 0x2C
            · subst hc
              simp only [beq_self_eq_true, ite_true]
              rw [ihM d (skipWs r') (by simp at hl2; omega)]
            · simp [hc]

/-- More fuel changes nothing, from the bound up. -/
theorem parseVal_fuel_add (d : Nat) (bs : Bytes) (n k : Nat) (hn : 2 * bs.length + 1 ≤ n) : parseVal d (n + k) bs = parseVal d n bs := by
  induction k with
  | zero => rfl
  | succ k ih => rw [← ih]; exact (fuel_succ (n + k)).1 d bs (by omega)

theorem parseElems_fuel_add (d : Nat) (bs : Bytes) (n k : Nat) (hn : 2 * bs.length + 2 ≤ n) : parseElems d (n + k) bs = parseElems d n bs := by
  induction k with
  | zero => rfl
  | succ k ih => rw [← ih]; exact (fuel_succ (n + k)).2.1 d bs (by omega)

theorem parseMembers_fuel_add (d : Nat) (bs : Bytes) (n k : Nat) (hn : 2 * bs.length + 2 ≤ n) : parseMembers d (n + k) bs = parseMembers d n bs := by
  induction k with
  | zero => rfl
  | succ k ih => rw [← ih]; exact (fuel_succ (n + k)).2.2 d bs (by omega)

/-- The reference at its canonical fuel. -/
def pv (d : Nat) (bs : Bytes) : Except Error (Value × Bytes) := parseVal d (2 * bs.length + 2) bs
def pe (d : Nat) (bs : Bytes) : Except Error (List Value × Bytes) := parseElems d (2 * bs.length + 2) bs
def pm (d : Nat) (bs : Bytes) : Except Error (List (String × Value) × Bytes) := parseMembers d (2 * bs.length + 2) bs

theorem parseVal_canon {d n : Nat} {bs : Bytes} (hn : 2 * bs.length + 1 ≤ n) : parseVal d n bs = pv d bs := by
  have h1 := parseVal_fuel_add d bs (2 * bs.length + 1) (n - (2 * bs.length + 1)) (Nat.le_refl _)
  rw [show 2 * bs.length + 1 + (n - (2 * bs.length + 1)) = n by omega] at h1
  have h2 := parseVal_fuel_add d bs (2 * bs.length + 1) 1 (Nat.le_refl _)
  rw [h1]
  simpa [pv] using h2.symm

theorem parseElems_canon {d n : Nat} {bs : Bytes} (hn : 2 * bs.length + 2 ≤ n) : parseElems d n bs = pe d bs := by
  have h1 := parseElems_fuel_add d bs (2 * bs.length + 2) (n - (2 * bs.length + 2)) (Nat.le_refl _)
  rw [show 2 * bs.length + 2 + (n - (2 * bs.length + 2)) = n by omega] at h1
  rw [h1]; rfl

theorem parseMembers_canon {d n : Nat} {bs : Bytes} (hn : 2 * bs.length + 2 ≤ n) : parseMembers d n bs = pm d bs := by
  have h1 := parseMembers_fuel_add d bs (2 * bs.length + 2) (n - (2 * bs.length + 2)) (Nat.le_refl _)
  rw [show 2 * bs.length + 2 + (n - (2 * bs.length + 2)) = n by omega] at h1
  rw [h1]; rfl

end LeanJson
