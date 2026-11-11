import LeanJsonProofs.Str
/-! # The reference against the grammar: values, arrays, objects, and the whole text

`parse_sound`: an accepted input is derivable and within `maxDepth`. The completeness half and unambiguity are in `LeanJsonProofs/ReferenceComplete.lean`. -/
namespace LeanJson

theorem lit_sound {l bs : Bytes} {r : Bytes} (h : lit l bs = some r) : bs = l ++ r := by
  induction l generalizing bs with
  | nil => simp [lit] at h; subst h; rfl
  | cons x xs ih =>
    cases bs with
    | nil => simp [lit] at h
    | cons y ys =>
      by_cases hxy : x = y
      · subst hxy; simp [lit] at h; simp [ih h]
      · simp [lit, hxy] at h

theorem lit_complete (l rest : Bytes) : lit l (l ++ rest) = some rest := by
  induction l with
  | nil => simp [lit]
  | cons x xs ih => simp [lit, ih]

theorem parseKey_sound {bs : Bytes} {s r} (h : parseKey bs = some (s, r)) :
    ∃ k w₁ r', bs = k ++ w₁ ++ 0x3A :: r' ∧ Str k s ∧ Ws w₁ ∧ r' = r := by
  unfold parseKey at h
  cases hp : parseStr bs with
  | none => simp [hp] at h
  | some p =>
    obtain ⟨s0, r0⟩ := p
    simp only [hp] at h
    obtain ⟨k, hk, hK⟩ := parseStr_sound hp
    cases hw : skipWs r0 with
    | nil => simp [hw] at h
    | cons c r1 =>
      simp only [hw] at h
      by_cases hc : c = 0x3A
      · subst hc; simp at h; obtain ⟨rfl, rfl⟩ := h
        obtain ⟨w, hw', hW⟩ := skipWs_sound r0
        rw [hw] at hw'
        exact ⟨k, w, r1, by rw [hk, hw']; simp, hK, hW, rfl⟩
      · simp [hc] at h

theorem parse_sound_aux (n : Nat) :
    (∀ d bs v r, parseVal d n bs = .ok (v, r) → (∃ pre, bs = pre ++ r ∧ Val pre v) ∧ v.depth ≤ d) ∧
    (∀ d bs vs r, parseElems d n bs = .ok (vs, r) → (∃ pre, bs = pre ++ r ∧ Elems pre vs) ∧ depthList vs ≤ d) ∧
    (∀ d bs kvs r, parseMembers d n bs = .ok (kvs, r) → (∃ pre, bs = pre ++ r ∧ Members pre kvs) ∧ depthMembers kvs ≤ d) := by
  induction n with
  | zero => refine ⟨?_, ?_, ?_⟩ <;> intro d bs _ _ h <;> simp [parseVal, parseElems, parseMembers] at h
  | succ n ih =>
    obtain ⟨ihV, ihE, ihM⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · intro d bs v r h
      cases bs with
      | nil => simp [parseVal] at h
      | cons b r0 =>
        simp only [parseVal] at h
        by_cases hb1 : b = 0x5B
        · subst hb1
          simp only [beq_self_eq_true, ite_true] at h
          cases d with
          | zero => simp at h
          | succ d' =>
            cases hs : skipWs r0 with
            | nil => simp [hs] at h
            | cons c r' =>
              simp only [hs] at h
              obtain ⟨w1, hw1, hW1⟩ := skipWs_sound r0
              rw [hs] at hw1
              by_cases hc : c = 0x5D
              · subst hc; simp at h; obtain ⟨rfl, rfl⟩ := h
                exact ⟨⟨_, by rw [hw1]; simp, .arr0 hW1⟩, by simp [Value.depth, depthList]⟩
              · simp only [beq_iff_eq, hc, ite_false] at h
                cases he : parseElems d' n (c :: r') with
                | error e => simp [he] at h
                | ok p =>
                  obtain ⟨vs, r2⟩ := p
                  simp only [he] at h
                  obtain ⟨⟨es, hes, hE⟩, hdep⟩ := ihE d' _ _ _ he
                  obtain ⟨w2, hw2, hW2⟩ := skipWs_sound r2
                  cases hs2 : skipWs r2 with
                  | nil => simp [hs2] at h
                  | cons c' r3 =>
                    simp only [hs2] at h
                    by_cases hc' : c' = 0x5D
                    · subst hc'; simp at h; obtain ⟨rfl, rfl⟩ := h
                      rw [hs2] at hw2
                      refine ⟨⟨_, ?_, .arr hW1 hE hW2⟩, by simp [Value.depth]; omega⟩
                      rw [hw1, hes, hw2]; simp
                    · simp [hc'] at h
        · by_cases hb2 : b = 0x7B
          · subst hb2
            simp only [beq_self_eq_true, ite_true, show ((0x7B : UInt8) == 0x5B) = false by decide] at h
            cases d with
            | zero => simp at h
            | succ d' =>
              cases hs : skipWs r0 with
              | nil => simp [hs] at h
              | cons c r' =>
                simp only [hs] at h
                obtain ⟨w1, hw1, hW1⟩ := skipWs_sound r0
                rw [hs] at hw1
                by_cases hc : c = 0x7D
                · subst hc; simp at h; obtain ⟨rfl, rfl⟩ := h
                  exact ⟨⟨_, by rw [hw1]; simp, .obj0 hW1⟩, by simp [Value.depth, depthMembers]⟩
                · simp only [beq_iff_eq, hc, ite_false] at h
                  cases he : parseMembers d' n (c :: r') with
                  | error e => simp [he] at h
                  | ok p =>
                    obtain ⟨kvs, r2⟩ := p
                    simp only [he] at h
                    obtain ⟨⟨es, hes, hE⟩, hdep⟩ := ihM d' _ _ _ he
                    obtain ⟨w2, hw2, hW2⟩ := skipWs_sound r2
                    cases hs2 : skipWs r2 with
                    | nil => simp [hs2] at h
                    | cons c' r3 =>
                      simp only [hs2] at h
                      by_cases hc' : c' = 0x7D
                      · subst hc'; simp at h; obtain ⟨rfl, rfl⟩ := h
                        rw [hs2] at hw2
                        refine ⟨⟨_, ?_, .obj hW1 hE hW2⟩, by simp [Value.depth]; omega⟩
                        rw [hw1, hes, hw2]; simp
                      · simp [hc'] at h
          · by_cases hb3 : b = 0x22
            · subst hb3
              simp only [beq_self_eq_true, ite_true, show ((0x22 : UInt8) == 0x5B) = false by decide, show ((0x22 : UInt8) == 0x7B) = false by decide] at h
              cases hp : parseStr (0x22 :: r0) with
              | none => simp [hp] at h
              | some p =>
                obtain ⟨s, r1⟩ := p
                simp only [hp] at h
                simp at h; obtain ⟨rfl, rfl⟩ := h
                obtain ⟨pre, hpre, hS⟩ := parseStr_sound hp
                exact ⟨⟨pre, hpre, .str hS⟩, by simp [Value.depth]⟩
            · by_cases hb4 : b = 0x6E
              · subst hb4
                simp only [show ((0x6E : UInt8) == 0x5B) = false by decide, show ((0x6E : UInt8) == 0x7B) = false by decide, show ((0x6E : UInt8) == 0x22) = false by decide, beq_self_eq_true, ite_true] at h
                cases hl : lit [0x75, 0x6C, 0x6C] r0 with
                | none => simp [hl] at h
                | some r1 => simp [hl] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨⟨_, by simp [lit_sound hl], .null⟩, by simp [Value.depth]⟩
              · by_cases hb5 : b = 0x74
                · subst hb5
                  simp only [show ((0x74 : UInt8) == 0x5B) = false by decide, show ((0x74 : UInt8) == 0x7B) = false by decide, show ((0x74 : UInt8) == 0x22) = false by decide, show ((0x74 : UInt8) == 0x6E) = false by decide, beq_self_eq_true, ite_true] at h
                  cases hl : lit [0x72, 0x75, 0x65] r0 with
                  | none => simp [hl] at h
                  | some r1 => simp [hl] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨⟨_, by simp [lit_sound hl], .true⟩, by simp [Value.depth]⟩
                · by_cases hb6 : b = 0x66
                  · subst hb6
                    simp only [show ((0x66 : UInt8) == 0x5B) = false by decide, show ((0x66 : UInt8) == 0x7B) = false by decide, show ((0x66 : UInt8) == 0x22) = false by decide, show ((0x66 : UInt8) == 0x6E) = false by decide, show ((0x66 : UInt8) == 0x74) = false by decide, beq_self_eq_true, ite_true] at h
                    cases hl : lit [0x61, 0x6C, 0x73, 0x65] r0 with
                    | none => simp [hl] at h
                    | some r1 => simp [hl] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨⟨_, by simp [lit_sound hl], .false⟩, by simp [Value.depth]⟩
                  · simp only [beq_iff_eq, hb1, hb2, hb3, hb4, hb5, hb6, ite_false] at h
                    cases hn : parseNum (b :: r0) with
                    | none => simp [hn] at h
                    | some p =>
                      obtain ⟨m, r1⟩ := p
                      simp [hn] at h; obtain ⟨rfl, rfl⟩ := h
                      obtain ⟨pre, hpre, hN⟩ := parseNum_sound hn
                      exact ⟨⟨pre, hpre, .num hN⟩, by simp [Value.depth]⟩
    · intro d bs vs r h
      simp only [parseElems] at h
      cases hv : parseVal d n bs with
      | error e => simp [hv] at h
      | ok p =>
        obtain ⟨v, r1⟩ := p
        simp only [hv] at h
        obtain ⟨⟨pre, hpre, hV⟩, hdep⟩ := ihV d _ _ _ hv
        cases hs : skipWs r1 with
        | nil => simp [hs] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨⟨pre, hpre, .one hV⟩, by simp [depthList]; exact hdep⟩
        | cons c r' =>
          simp only [hs] at h
          by_cases hc : c = 0x2C
          · subst hc
            simp only [beq_self_eq_true, ite_true] at h
            cases he : parseElems d n (skipWs r') with
            | error e => simp [he] at h
            | ok q =>
              obtain ⟨vs', r2⟩ := q
              simp [he] at h; obtain ⟨rfl, rfl⟩ := h
              obtain ⟨⟨es, hes, hE⟩, hdep'⟩ := ihE d _ _ _ he
              obtain ⟨w1, hw1, hW1⟩ := skipWs_sound r1
              rw [hs] at hw1
              obtain ⟨w2, hw2, hW2⟩ := skipWs_sound r'
              rw [hes] at hw2
              exact ⟨⟨pre ++ w1 ++ 0x2C :: (w2 ++ es), by rw [hpre, hw1, hw2]; simp, .cons hV hW1 hW2 hE⟩, by simp [depthList]; omega⟩
          · simp [hc] at h; obtain ⟨rfl, rfl⟩ := h
            exact ⟨⟨pre, hpre, .one hV⟩, by simp [depthList]; exact hdep⟩
    · intro d bs kvs r h
      simp only [parseMembers] at h
      cases hk : parseKey bs with
      | none => simp [hk] at h
      | some p =>
        obtain ⟨k, r0⟩ := p
        simp only [hk] at h
        obtain ⟨kb, w0, r', hbs, hK, hW0, rfl⟩ := parseKey_sound hk
        cases hv : parseVal d n (skipWs r') with
        | error e => simp [hv] at h
        | ok p =>
          obtain ⟨v, r1⟩ := p
          simp only [hv] at h
          obtain ⟨⟨vb, hvb, hV⟩, hdep⟩ := ihV d _ _ _ hv
          obtain ⟨wv, hwv, hWv⟩ := skipWs_sound r'
          rw [hvb] at hwv
          have hmem : Member (kb ++ w0 ++ 0x3A :: (wv ++ vb)) (k, v) := .mk hK hW0 hWv hV
          cases hs : skipWs r1 with
          | nil =>
            simp [hs] at h; obtain ⟨rfl, rfl⟩ := h
            exact ⟨⟨_, by rw [hbs, hwv]; simp, .one hmem⟩, by simp [depthMembers]; exact hdep⟩
          | cons c r2 =>
            simp only [hs] at h
            by_cases hc : c = 0x2C
            · subst hc
              simp only [beq_self_eq_true, ite_true] at h
              cases he : parseMembers d n (skipWs r2) with
              | error e => simp [he] at h
              | ok q =>
                obtain ⟨kvs', r3⟩ := q
                simp [he] at h; obtain ⟨rfl, rfl⟩ := h
                obtain ⟨⟨ms, hms, hM⟩, hdep'⟩ := ihM d _ _ _ he
                obtain ⟨w1, hw1, hW1⟩ := skipWs_sound r1
                rw [hs] at hw1
                obtain ⟨w2, hw2, hW2⟩ := skipWs_sound r2
                rw [hms] at hw2
                exact ⟨⟨(kb ++ w0 ++ 0x3A :: (wv ++ vb)) ++ w1 ++ 0x2C :: (w2 ++ ms), by rw [hbs, hwv, hw1, hw2]; simp, .cons hmem hW1 hW2 hM⟩, by simp [depthMembers]; omega⟩
            · simp [hc] at h; obtain ⟨rfl, rfl⟩ := h
              exact ⟨⟨_, by rw [hbs, hwv]; simp, .one hmem⟩, by simp [depthMembers]; exact hdep⟩

theorem parse_sound {bs : Bytes} {v : Value} (h : parse bs = .ok v) : Json bs v ∧ v.depth ≤ maxDepth := by
  unfold parse at h
  cases hp : parseVal maxDepth (2 * bs.length + 2) (skipWs bs) with
  | error e => simp [hp] at h
  | ok p =>
    obtain ⟨v', r⟩ := p
    simp only [hp] at h
    by_cases hr : (skipWs r).isEmpty = true
    · simp [hr] at h; subst h
      obtain ⟨⟨pre, hpre, hV⟩, hdep⟩ := (parse_sound_aux _).1 _ _ _ _ hp
      obtain ⟨w1, hw1, hW1⟩ := skipWs_sound bs
      obtain ⟨w2, hw2, hW2⟩ := skipWs_sound r
      have hnil : skipWs r = [] := by simpa using hr
      rw [hnil] at hw2
      exact ⟨by rw [hw1, hpre, hw2]; simpa using Json.mk hW1 hV hW2, hdep⟩
    · simp [hr] at h

end LeanJson
