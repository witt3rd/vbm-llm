import LeanJsonProofs.ReferenceComplete
/-! # The reference parser: the verdict, in full

`parse_ok_iff`: the reference accepts exactly what the grammar derives within `maxDepth`, and returns the derivation's value. From it: `parse_sound`, `parse_complete`,
`json_unique` (the grammar determines the value: unambiguity at the level of values), and the verdict on everything else. About the specification (the grammar and the
reference); nothing here is the code the exports run. -/
namespace LeanJson

/-- With whitespace skipped, any depth budget that fits the value and the fuel `2 * length + 2` read a derivable text whole. -/
theorem json_parseVal {bs : Bytes} {v : Value} (h : Json bs v) {d : Nat} (hd : v.depth ≤ d) :
    ∃ r, parseVal d (2 * bs.length + 2) (skipWs bs) = .ok (v, r) ∧ skipWs r = [] := by
  cases h with
  | @mk w1 b w2 v hW1 hV hW2 =>
    obtain ⟨c, r', hb, hc⟩ := val_head hV
    have hsk := skipWs_complete hW1 (rest := b ++ w2) (by rw [hb]; exact H_cons hc.1 _)
    have hv := val_complete hV d (2 * (w1 ++ b ++ w2).length + 2) w2 hd (by simp; omega) (H_mono (fun x hx => by simp [stopB, hx]) (ws_head hW2))
    simp only [List.append_assoc] at hv ⊢
    rw [hsk]
    exact ⟨w2, hv, skipWs_nil_of hW2⟩

theorem parse_complete {bs : Bytes} {v : Value} (h : Json bs v) (hd : v.depth ≤ maxDepth) : parse bs = .ok v := by
  obtain ⟨r, hr, hs⟩ := json_parseVal h hd
  simp [parse, hr, hs]

theorem parse_ok_iff {bs : Bytes} {v : Value} : parse bs = .ok v ↔ Json bs v ∧ v.depth ≤ maxDepth :=
  ⟨parse_sound, fun ⟨h, hd⟩ => parse_complete h hd⟩

/-- The grammar relates a byte string to at most one value. -/
theorem json_unique {bs : Bytes} {v v' : Value} (h : Json bs v) (h' : Json bs v') : v = v' := by
  obtain ⟨r, hr, _⟩ := json_parseVal h (Nat.le_max_left v.depth v'.depth)
  obtain ⟨r', hr', _⟩ := json_parseVal h' (Nat.le_max_right v.depth v'.depth)
  rw [hr] at hr'
  simp at hr'
  exact hr'.1

/-- Every input gets a verdict: a value the grammar derives within the limit, or an error. (Totality itself is the function's type: Lean checks the recursion terminates.) -/
theorem parse_total (bs : Bytes) : (∃ v, parse bs = .ok v ∧ Json bs v ∧ v.depth ≤ maxDepth) ∨ ∃ e, parse bs = .error e := by
  cases h : parse bs with
  | ok v => exact .inl ⟨v, rfl, parse_sound h⟩
  | error e => exact .inr ⟨e, rfl⟩

/-- An error is exactly the absence of an accepted derivation. -/
theorem parse_error_iff {bs : Bytes} : (∃ e, parse bs = .error e) ↔ ¬ ∃ v, Json bs v ∧ v.depth ≤ maxDepth := by
  constructor
  · rintro ⟨e, he⟩ ⟨v, hv, hd⟩
    rw [parse_complete hv hd] at he; cases he
  · intro hn
    cases h : parse bs with
    | ok v => exact absurd ⟨v, parse_sound h⟩ hn
    | error e => exact ⟨e, rfl⟩

/-- Nesting past the bound is never accepted: a derivable text whose value is deeper than `maxDepth` is an error. -/
theorem parse_too_deep {bs : Bytes} {v : Value} (h : Json bs v) (hd : maxDepth < v.depth) : ∃ e, parse bs = .error e := by
  cases hp : parse bs with
  | ok w => have := parse_sound hp; have := json_unique h this.1; subst this; omega
  | error e => exact ⟨e, rfl⟩

end LeanJson
