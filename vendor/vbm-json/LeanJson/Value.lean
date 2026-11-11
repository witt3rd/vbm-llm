/-! # `LeanJson.Value`: the JSON value, and the byte alphabet

Imports nothing but `Init`, like every module under `LeanJson/`. The type is built so that every inhabitant is a legal JSON value (no side proofs to carry):
- **numbers are lexemes**, never floats (policy `policy-numbers-are-lexemes`): a sign, an integer part (`0`, or a non-zero digit then digits: so no leading zero),
  an optional fraction (at least one digit), an optional exponent (a sign and at least one digit). The `e`/`E` and an explicit `+` are not kept;
- **strings are `String`**: a sequence of Unicode scalar values, so a lone surrogate or invalid UTF-8 cannot be represented (policy `policy-no-lone-surrogates-no-invalid-utf8`);
- **objects are ordered key/value lists**, duplicates kept in input order (policy `policy-duplicate-keys-kept-in-order`). -/
namespace LeanJson

/-- The input and output of every codec function is a list of bytes (the reference is a specification, not the fast code). -/
abbrev Bytes := List UInt8

abbrev Digit := Fin 10

/-- The integer part of a number: `0`, or a non-zero first digit (`lead` is the digit minus one) then any digits. A leading zero cannot be written. -/
inductive IntPart where
  | zero
  | nz (lead : Fin 9) (rest : List Digit)
  deriving DecidableEq, Repr

/-- A JSON number as a lexeme: sign, integer part, optional fraction (first digit, rest), optional exponent (negative?, first digit, rest). -/
structure Number where
  neg  : Bool
  int  : IntPart
  frac : Option (Digit × List Digit)
  exp  : Option (Bool × Digit × List Digit)
  deriving DecidableEq, Repr

inductive Value where
  | null
  | bool (b : Bool)
  | num (n : Number)
  | str (s : String)
  | arr (xs : List Value)
  | obj (members : List (String × Value))
  deriving Repr, Inhabited, BEq

mutual
/-- Nesting depth: a scalar is 0; an array or object is one more than its deepest member (so `[]` is 1). The policy limit `maxDepth` bounds it. -/
def Value.depth : Value → Nat
  | .arr xs => depthList xs + 1
  | .obj ms => depthMembers ms + 1
  | _ => 0
def depthList : List Value → Nat
  | [] => 0
  | v :: vs => max v.depth (depthList vs)
def depthMembers : List (String × Value) → Nat
  | [] => 0
  | (_, v) :: ms => max v.depth (depthMembers ms)
end

end LeanJson
