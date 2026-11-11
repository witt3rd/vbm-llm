import LeanJsonProofs.Parse
/-! # The pinned policies as checked examples (PROPOSED: docs/decisions/0001-vbm-json.md section 5)

Each is a closed statement about the reference, checked by evaluation in the kernel (`rfl`, no `native_decide`), so it is a theorem that the specification says this, and the
same inputs are in the shared vectors. About the specification, not the code the exports run. -/
namespace LeanJson

set_option maxRecDepth 100000

/-- `"\uD800"`: a lone high surrogate escape is rejected. -/
theorem lone_high_surrogate_rejected : parse [0x22, 0x5C, 0x75, 0x44, 0x38, 0x30, 0x30, 0x22] = .error .syntax := rfl

/-- `"\uDC00"`: a lone low surrogate escape is rejected. -/
theorem lone_low_surrogate_rejected : parse [0x22, 0x5C, 0x75, 0x44, 0x43, 0x30, 0x30, 0x22] = .error .syntax := rfl

/-- `"` C0 80 `"`: an overlong UTF-8 form is rejected. -/
theorem overlong_utf8_rejected : parse [0x22, 0xC0, 0x80, 0x22] = .error .syntax := rfl

/-- `"` ED A0 80 `"`: a UTF-8 encoded surrogate is rejected. -/
theorem utf8_surrogate_rejected : parse [0x22, 0xED, 0xA0, 0x80, 0x22] = .error .syntax := rfl

/-- `"\uD83D\uDE00"`: a surrogate pair is one scalar (U+1F600). -/
theorem surrogate_pair_is_one_scalar :
    parse [0x22, 0x5C, 0x75, 0x44, 0x38, 0x33, 0x44, 0x5C, 0x75, 0x44, 0x45, 0x30, 0x30, 0x22] = .ok (.str (String.singleton (Char.ofNat 0x1F600))) := rfl

/-- `1.50E+2` is the lexeme: sign, `1`, fraction `5 0`, exponent `+ 2` (the trailing zero is kept). -/
theorem number_is_a_lexeme :
    parse [0x31, 0x2E, 0x35, 0x30, 0x45, 0x2B, 0x32] = .ok (.num ⟨false, .nz 0 [], some (5, [0]), some (false, 2, [])⟩) := rfl

/-- `01` is not a number: no leading zero. -/
theorem leading_zero_rejected : parse [0x30, 0x31] = .error .syntax := rfl

/-- `{"a":1,"a":2}`: both members are kept, in input order. -/
theorem duplicate_keys_kept_in_order :
    parse [0x7B, 0x22, 0x61, 0x22, 0x3A, 0x31, 0x2C, 0x22, 0x61, 0x22, 0x3A, 0x32, 0x7D] =
      .ok (.obj [("a", .num ⟨false, .nz 0 [], none, none⟩), ("a", .num ⟨false, .nz 1 [], none, none⟩)]) := rfl

/-- Nesting to `maxDepth` (512) is accepted. -/
theorem depth_at_limit_accepted : (parse (List.replicate maxDepth 0x5B ++ List.replicate maxDepth 0x5D)).isOk = true := rfl

/-- One more is the error code `depth`. -/
theorem depth_past_limit_is_error_code : parse (List.replicate (maxDepth + 1) 0x5B ++ List.replicate (maxDepth + 1) 0x5D) = .error .depth := rfl

/-- The depth error is reported as soon as it is seen, before any later syntax error: 600 opening brackets and nothing else. -/
theorem depth_error_comes_first : parse (List.replicate 600 0x5B) = .error .depth := rfl

/-- `skipWs` leaves a text that starts with `[` alone. -/
theorem skipWs_open_bracket (r : Bytes) : skipWs (0x5B :: r) = 0x5B :: r := by
  simp [skipWs, isWs]

/-- The structural core of stack safety: with a budget of `d` levels and fuel `n > 2 * d`, a text that begins with more than `d` opening brackets is the error `depth`, whatever follows.
Each level spends one budget unit and two fuel units (`parseVal`, `parseElems`), so the budget runs out first. Stated for every depth, so the proof is an induction and the kernel never
evaluates a 100000-long list (the first version did, by `decide +kernel`, and the exported proof term overflowed the external checker's stack). -/
theorem parseVal_open_brackets (d : Nat) : ∀ (k n : Nat) (rest : Bytes), d < k → 2 * d < n →
    parseVal d n (List.replicate k 0x5B ++ rest) = .error .depth := by
  induction d with
  | zero =>
    intro k n rest hk hn
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp [List.replicate_succ, parseVal]
  | succ d ih =>
    intro k n rest hk hn
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    obtain ⟨k'', rfl⟩ : ∃ k'', k' = k'' + 1 := ⟨k' - 1, by omega⟩
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    obtain ⟨m, rfl⟩ : ∃ m, n' = m + 1 := ⟨n' - 1, by omega⟩
    have hrec := ih (k'' + 1) m rest (by omega) (by omega)
    simp only [List.replicate_succ, List.cons_append] at hrec ⊢
    simp [parseVal, skipWs_open_bracket, parseElems, hrec]

/-- A text with more than `maxDepth` opening brackets at the front is the error `depth`, whatever follows (the reference's fuel `2 * length + 2` is ample). -/
theorem parse_open_brackets_is_depth (k : Nat) (rest : Bytes) (hk : maxDepth < k) :
    parse (List.replicate k 0x5B ++ rest) = .error .depth := by
  have hlen : k ≤ (List.replicate k (0x5B : UInt8) ++ rest).length := by simp
  have hs : skipWs (List.replicate k 0x5B ++ rest) = List.replicate k 0x5B ++ rest := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by unfold maxDepth at hk; omega⟩
    rw [List.replicate_succ, List.cons_append]; exact skipWs_open_bracket _
  unfold parse
  rw [hs, parseVal_open_brackets maxDepth k _ rest hk (by omega)]

/-- 100000 deep is the same error code (the budget runs out after `maxDepth` levels, whatever follows). -/
theorem depth_100000_is_error_code : parse (List.replicate 100000 0x5B ++ List.replicate 100000 0x5D) = .error .depth :=
  parse_open_brackets_is_depth 100000 _ (by unfold maxDepth; omega)

end LeanJson
