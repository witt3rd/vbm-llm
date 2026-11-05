import VbmLlm.Wire
/-! # Proofs about reading a parsed value (`VbmLlm/Wire.lean`)

* **A key finds its last binding, or null** (`lookup_snoc`, `lookup_absent`, `lookup_eq`): a duplicate key is not an error, the later one wins; an absent key reads as `null`.
* **A count is a plain natural** (`natOf_neg`, `natOf_frac`, `natOf_exp`, `natOf_zero`, `natOf_nz`): a sign, a fraction or an exponent is not a count. -/
namespace VbmLlm
open LeanJson

theorem go_append : ∀ (a b : List (String × Value)) (k : String) (acc : Value), go (a ++ b) k acc = go b k (go a k acc)
  | [], b, k, acc => by simp [go]
  | (k', v) :: rest, b, k, acc => by simp [go, go_append rest b k]

/-- A later binding of a key wins. -/
theorem lookup_snoc (ms : List (String × Value)) (k : String) (v : Value) : lookup (ms ++ [(k, v)]) k = v := by
  simp [lookup, go_append, go]

theorem go_absent : ∀ (ms : List (String × Value)) (k : String) (acc : Value), (∀ p ∈ ms, p.1 ≠ k) → go ms k acc = acc
  | [], k, acc, _ => by simp [go]
  | (k', v) :: rest, k, acc, h => by
    have hk : (k' == k) = false := by simpa using h (k', v) (by simp)
    simp [go, hk]
    exact go_absent rest k acc (fun p hp => h p (List.mem_cons_of_mem _ hp))

/-- An absent key reads as `null`. -/
theorem lookup_absent {ms : List (String × Value)} {k : String} (h : ∀ p ∈ ms, p.1 ≠ k) : lookup ms k = .null := go_absent ms k .null h

theorem go_eq : ∀ (ms : List (String × Value)) (k : String) (acc : Value), go ms k acc = acc ∨ ∃ v, (k, v) ∈ ms ∧ go ms k acc = v
  | [], k, acc => by simp [go]
  | (k', v) :: rest, k, acc => by
    rcases go_eq rest k (if k' == k then v else acc) with h | ⟨w, hw, h⟩
    · by_cases hk : k' = k
      · subst hk; right; exact ⟨v, by simp, by simpa [go] using h⟩
      · have : (k' == k) = false := by simpa using hk
        left; simpa [go, this] using h
    · right; exact ⟨w, List.mem_cons_of_mem _ hw, by simpa [go] using h⟩

/-- A lookup finds nothing (null), or a value some member of that key holds. -/
theorem lookup_eq (ms : List (String × Value)) (k : String) : lookup ms k = .null ∨ ∃ v, (k, v) ∈ ms ∧ lookup ms k = v := go_eq ms k .null

theorem get_nonobj {v : Value} (h : ∀ ms, v ≠ .obj ms) (k : String) : get v k = .null := by
  cases v <;> simp [get] <;> exact absurd rfl (h _)

theorem get_obj (ms : List (String × Value)) (k : String) : get (.obj ms) k = lookup ms k := rfl

theorem natOf_neg (n : Number) (h : n.neg = true) : natOf n = none := by simp [natOf, h]
theorem natOf_frac (n : Number) (d : Digit × List Digit) (h : n.frac = some d) : natOf n = none := by simp [natOf, h]
theorem natOf_exp (n : Number) (e : Bool × Digit × List Digit) (h : n.exp = some e) : natOf n = none := by simp [natOf, h]
theorem natOf_zero : natOf ⟨false, .zero, none, none⟩ = some 0 := by simp [natOf]
theorem natOf_nz (lead : Fin 9) (rest : List Digit) : natOf ⟨false, .nz lead rest, none, none⟩ = some (digitsVal rest (lead.val + 1)) := by simp [natOf]
/-- The lexeme `120` is the natural 120. -/
theorem natOf_120 : natOf ⟨false, .nz 0 [2, 0], none, none⟩ = some 120 := by decide

theorem nat?_nonnum {v : Value} (h : ∀ n, v ≠ .num n) : nat? v = none := by
  cases v <;> simp [nat?] <;> exact absurd rfl (h _)

/-- Two lists related member by member (the index of a member never matters to what a decoder yields, only to the name of a fault). -/
inductive Each {α β : Type} (R : α → β → Prop) : List α → List β → Prop where
  | nil : Each R [] []
  | cons {a : α} {b : β} {as : List α} {bs : List β} : R a b → Each R as bs → Each R (a :: as) (b :: bs)

theorem each_nil_iff {α β : Type} (R : α → β → Prop) (bs : List β) : Each R [] bs ↔ bs = [] := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .nil

theorem each_cons_iff {α β : Type} (R : α → β → Prop) (a : α) (as : List α) (bs : List β) :
    Each R (a :: as) bs ↔ ∃ b bs', bs = b :: bs' ∧ R a b ∧ Each R as bs' := by
  constructor
  · intro h; cases h with | cons h1 h2 => exact ⟨_, _, rfl, h1, h2⟩
  · rintro ⟨b, bs', rfl, h1, h2⟩; exact .cons h1 h2

end VbmLlm
