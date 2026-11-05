import LeanJson.Value
/-! # Reading a parsed JSON value: keys, naturals, strings

Every decoder of this library reads a `LeanJson.Value` (the value type of the pinned library `vbm-json`; the parse itself is `LeanJson.parseFast`, proved in that library to equal the RFC 8259
reference). The reading rules are stated once, here, and proved in `VbmLlmProofs/Wire.lean`:

* **A key finds its last binding, or null.** A duplicate key is not an error: the later one wins (the policy `vbm-json` states for duplicates: kept in input order). An absent key reads as `null`.
* **`null` and an absent key are the same: "not there".** A field the convention marks nullable is never told apart from an absent one.
* **A count is a plain natural.** A sign, a fraction or an exponent is not a count. Never a float.

The functions are written as scans that carry their answer (no list is rebuilt, no `Option` is allocated on the success path): a decoder built from them allocates no more than the code it replaces. -/
namespace VbmLlm
open LeanJson

/-- The last binding of `k` among an object's members, else `acc`. -/
def go : List (String × Value) → String → Value → Value
  | [], _, acc => acc
  | (k', v) :: rest, k, acc => go rest k (if k' == k then v else acc)

/-- The last binding of `k`, else `null`. -/
def lookup (ms : List (String × Value)) (k : String) : Value := go ms k .null

/-- A member of an object value; anything that is not an object has none (null). -/
def get (v : Value) (k : String) : Value :=
  match v with
  | .obj ms => lookup ms k
  | _ => .null

/-- The value of a digit list read onto an accumulator. -/
def digitsVal (ds : List Digit) (acc : Nat) : Nat := ds.foldl (fun a d => a * 10 + d.val) acc

/-- A natural from a number lexeme: no sign, no fraction, no exponent (the integer part is `0`, or a first digit `lead + 1` and more digits). -/
def natOf (n : Number) : Option Nat :=
  if n.neg || n.frac.isSome || n.exp.isSome then none
  else some (match n.int with
    | .zero => 0
    | .nz lead rest => digitsVal rest (lead.val + 1))

/-- A natural from a value: a number that is a plain natural. -/
def nat? (v : Value) : Option Nat :=
  match v with
  | .num n => natOf n
  | _ => none

/-- A string from a value. -/
def str? (v : Value) : Option String :=
  match v with
  | .str s => some s
  | _ => none

/-- The value is `null` (a key that is absent reads as `null`). -/
def isNull : Value → Bool
  | .null => true
  | _ => false

end VbmLlm
