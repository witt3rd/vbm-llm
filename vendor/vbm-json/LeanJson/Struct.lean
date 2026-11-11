import LeanJson.Grammar
/-! # `LeanJson.Struct`: the structural index, as a byte-at-a-time machine (the specification of stage 1 of the bit-parallel parser)

`docs/perf/simd-plan.md`. The bit-parallel stage 1 (`LeanJson.Stage1`, proved against this file) classifies 64 bytes at a time into one mask of the *structural* positions; stage 2 walks those positions instead of scanning
bytes. This file says, one byte at a time, which positions are structural. It is internal: the user-visible behaviour is anchored by the end-to-end theorem against the reference tape, so a mistake in this machine can cost speed
or make the fast path decline, never change a result.

The state before a byte: `esc` (the previous byte is a backslash that is not itself escaped: tracked everywhere, in a string or not), `str` (inside a string: the opening quote counts as inside, the closing quote does not),
`scal` (the previous byte continues or starts a scalar). The byte `c`:
- `q`, an **unescaped quote**: `c` is `"` and not `esc`;
- `nq`, a **scalar byte**: not an operator, not whitespace and not `q` (so a letter, a digit, a backslash, an *escaped* quote outside a string...);
- **structural**: an operator outside a string, or `q` (both quotes of a string are in the index), or the first scalar byte of a run outside a string (`nq`, not `scal`, not `str`).
The state after: `esc` is `c = \` and not `esc`; `str` flips on `q`; `scal` is `nq`.

Two decisions that shape the code and are worth the owner's attention: both quotes of a string are indexed (stage 2 reads a string's extent from the index), and escapes are tracked outside strings too (a backslash outside a
string is a syntax error that stage 2 sees as a scalar token and rejects; this is what the word-parallel kernel computes without a branch). -/
namespace LeanJson

/-- `{ } [ ] : ,`. -/
@[inline] def isOp (c : UInt8) : Bool := c == 0x7B || c == 0x7D || c == 0x5B || c == 0x5D || c == 0x3A || c == 0x2C

/-- The machine's state before a byte. -/
structure SState where
  esc : Bool
  str : Bool
  scal : Bool

/-- The state before the first byte. -/
def SState.init : SState := ⟨false, false, false⟩

/-- An unescaped quote. -/
def isQ (s : SState) (c : UInt8) : Bool := c == 0x22 && !s.esc

/-- A scalar byte: not an operator, whitespace, or unescaped quote. -/
def isNq (s : SState) (c : UInt8) : Bool := !(isOp c || isWs c || isQ s c)

/-- One step: the state after byte `c`, and whether `c` is structural. -/
def sStep (s : SState) (c : UInt8) : SState × Bool :=
  (⟨c == 0x5C && !s.esc, s.str != isQ s c, isNq s c⟩, (isOp c && !s.str) || isQ s c || (isNq s c && !s.scal && !s.str))

/-- The byte at `k`, `0` past the end (only the specification reads past the end). -/
def byteD (a : ByteArray) (k : Nat) : UInt8 := a.data.getD k 0

/-- The state before byte `k`: the machine run over the first `k` bytes. -/
def sAt (a : ByteArray) : Nat → SState
  | 0 => SState.init
  | k + 1 => (sStep (sAt a k) (byteD a k)).1

/-- Is byte `k` structural? -/
def isStruct (a : ByteArray) (k : Nat) : Bool := (sStep (sAt a k) (byteD a k)).2

/-- The structural index: the positions of the structural bytes, in order. -/
def specIndex (a : ByteArray) : List Nat := (List.range a.size).filter (isStruct a)

end LeanJson
