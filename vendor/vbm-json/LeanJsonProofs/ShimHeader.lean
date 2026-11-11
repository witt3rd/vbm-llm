/-! # The shim's result-header check: two mutants of it are equivalent (docs/mutants.md)

`abi/vbm_json.c` (trusted C, T09) accepts the Lean export's result only when its header is exact (line 54): the status is 0 and
`nw <= (n - 24) / 8 && nt <= n && 24 + 8 * nw + nt == n`, where `n` is the byte size of the result and `nw`, `nt` are `size_t` (arithmetic modulo 2^64, as in C).
The first two conjuncts only guard the third against wrapping. The scorecard's operator swaps `-` to `+` in `(n - 24) / 8` and `<=` to `<` in `nt <= n`
survive every test, and cannot be killed: they are equivalent. Here the check is modelled on `Nat` with the wrap spelled out, and the two mutants are proved to
accept exactly the same headers, for every `n` between 24 and 2^62 and every `nw`, `nt` (the byte size of a Lean array in memory; the size bound of the Lean runtime is 2^63). -/
namespace LeanJsonProofs.ShimHeader

/-- `size_t` arithmetic: the result of every operation is taken modulo 2^64. -/
def W : Nat := 2 ^ 64

/-- the shim's check as written: `nw <= (n - 24) / 8 && nt <= n && 24 + 8 * nw + nt == n` (the `n >= 24` branch guard is in the hypotheses of the theorems). -/
def ok (n nw nt : Nat) : Prop := nw ≤ (n - 24) / 8 ∧ nt ≤ n ∧ ((24 + 8 * nw % W) % W + nt) % W = n

/-- the mutant of line 54 column 39: `(n + 24) / 8`. -/
def okPlus (n nw nt : Nat) : Prop := nw ≤ (n + 24) / 8 ∧ nt ≤ n ∧ ((24 + 8 * nw % W) % W + nt) % W = n

/-- the mutant of line 54 column 55: `nt < n`. -/
def okLt (n nw nt : Nat) : Prop := nw ≤ (n - 24) / 8 ∧ nt < n ∧ ((24 + 8 * nw % W) % W + nt) % W = n

theorem plus_equiv (n nw nt : Nat) (hn : 24 ≤ n) (hn' : n < 2 ^ 62) :
    okPlus n nw nt ↔ ok n nw nt := by
  unfold okPlus ok W at *
  constructor <;> rintro ⟨h1, h2, h3⟩ <;> refine ⟨?_, h2, h3⟩ <;> omega

theorem lt_equiv (n nw nt : Nat) (hn : 24 ≤ n) (hn' : n < 2 ^ 62) :
    okLt n nw nt ↔ ok n nw nt := by
  unfold okLt ok W at *
  constructor <;> rintro ⟨h1, h2, h3⟩ <;> refine ⟨h1, ?_, h3⟩ <;> omega

/-- negative self-test: the method does tell a killable mutant from an equivalent one. `nw < (n - 24) / 8` (line 54 column 33, KILLED by the tests) is not equivalent:
an exact header of two words and no text is accepted by the code and refused by the mutant. -/
def okLtWords (n nw nt : Nat) : Prop := nw < (n - 24) / 8 ∧ nt ≤ n ∧ ((24 + 8 * nw % W) % W + nt) % W = n

theorem ltWords_not_equiv : ¬ ∀ n nw nt : Nat, 24 ≤ n → n < 2 ^ 62 → (okLtWords n nw nt ↔ ok n nw nt) := by
  intro h
  have := (h 40 2 0 (by omega) (by omega)).2 (by unfold ok W; omega)
  unfold okLtWords at this
  omega

end LeanJsonProofs.ShimHeader
