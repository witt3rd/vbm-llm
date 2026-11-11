/-! # `LeanJson.Policy`: the pinned policies (PROPOSED, pending the owner's ratification)

`docs/decisions/0001-vbm-json.md` section 5. A policy change is a spec change: it is made here and in the ledger, never in code. Where a policy lives:
- strict text (no lone-surrogate escapes, no invalid UTF-8): `Value.str` holds a `String` (scalar values only), and the grammar (`Grammar.lean`) derives no byte string for either;
- numbers are lexemes: `Number` in `Value.lean`; duplicate keys kept in input order: `Value.obj` is a list;
- `maxDepth` and the error codes: below. -/
namespace LeanJson

/-- The nesting limit (proposed default 512), a named limit: an array or object nested deeper is rejected with `Error.depth`, never a crash. -/
def maxDepth : Nat := 512

/-- Why an input is rejected. The numeric codes are part of the vector format (`vbm-json-vectors-1`) and of the future ABI. -/
inductive Error where
  /-- not derivable in the grammar (bad byte, bad escape, lone surrogate, invalid UTF-8, trailing bytes, truncated input). -/
  | syntax
  /-- nesting past `maxDepth`. -/
  | depth
  deriving DecidableEq, Repr

def Error.code : Error → Nat
  | .syntax => 1
  | .depth => 2

def Error.name : Error → String
  | .syntax => "syntax"
  | .depth => "depth"

end LeanJson
