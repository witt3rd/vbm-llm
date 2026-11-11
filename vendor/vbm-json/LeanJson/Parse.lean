import LeanJson.Reference
/-! # `LeanJson.Parse`: the fast parser (PR 2)

The code the exports run. `parseFast` reads a `ByteArray` with an index and an explicit stack of open containers (`Stack`): no recursion except tail calls (each loop is a
self tail call, so it compiles to a loop), no list of the input, no per-token allocation beyond the output (the stack cell of a container is reused in place when it is
unshared; a string is built with `String.push`; the element lists are built reversed and reversed once in place). It returns the same `Except Error Value` as the reference
`parse`: the statement is `LeanJsonProofs/Fast.lean` (`parseFast_eq_parse`). The nesting limit `maxDepth` is enforced by the budget `d`, which the stack's depth spends.

Every leaf below (`...A`) is the reference leaf of `Reference.lean` with the list replaced by the pair (array, index): same case order, same results, so the two can be compared
one leaf at a time. -/
namespace LeanJson

/-- The byte at `i`, if there is one. -/
@[inline] def byteAt (a : ByteArray) (i : Nat) : Option UInt8 := if h : i < a.size then some a[i] else none

/-- Is the byte at `i` exactly `c`? -/
@[inline] def byteIs (a : ByteArray) (i : Nat) (c : UInt8) : Bool := if h : i < a.size then a[i] == c else false

/-- `ws`: the index of the first byte at or after `i` that is not whitespace. -/
def skipWsA (a : ByteArray) (i : Nat) : Nat :=
  if h : i < a.size then (if isWs a[i] then skipWsA a (i + 1) else i) else i
termination_by a.size - i

/-- `*DIGIT`, read onto an accumulator (the digits before, reversed): the digits reversed and the index after them. -/
def digitsAcc (a : ByteArray) (i : Nat) (acc : List Digit) : List Digit × Nat :=
  if h : i < a.size then
    match digitVal a[i] with
    | some d => digitsAcc a (i + 1) (d :: acc)
    | none => (acc, i)
  else (acc, i)
termination_by a.size - i

/-- `*DIGIT`, in order. -/
@[inline] def digitsA (a : ByteArray) (i : Nat) : List Digit × Nat :=
  let r := digitsAcc a i []
  (r.1.reverse, r.2)

/-- `1*DIGIT`. -/
@[inline] def digits1A (a : ByteArray) (i : Nat) : Option ((Digit × List Digit) × Nat) :=
  match byteAt a i with
  | some b => match digitVal b with
    | some d => let r := digitsA a (i + 1); some ((d, r.1), r.2)
    | none => none
  | none => none

/-- `int = zero / ( digit1-9 *DIGIT )`. -/
@[inline] def parseIntA (a : ByteArray) (i : Nat) : Option (IntPart × Nat) :=
  match byteAt a i with
  | none => none
  | some b =>
    if b == 0x30 then some (.zero, i + 1)
    else match digit19 b with
      | some l => let r := digitsA a (i + 1); some (.nz l r.1, r.2)
      | none => none

/-- `[ frac ]`. -/
@[inline] def parseFracA (a : ByteArray) (i : Nat) : Option (Option (Digit × List Digit) × Nat) :=
  if byteIs a i 0x2E then (match digits1A a (i + 1) with | some (f, j) => some (some f, j) | none => none)
  else some (none, i)

/-- `[ exp ]`: the sign of the exponent, then `1*DIGIT`. -/
@[inline] def parseExpA (a : ByteArray) (i : Nat) : Option (Option (Bool × Digit × List Digit) × Nat) :=
  if byteIs a i 0x65 || byteIs a i 0x45 then
    let neg := byteIs a (i + 1) 0x2D
    let i1 := if byteIs a (i + 1) 0x2B || neg then i + 2 else i + 1
    match digits1A a i1 with
    | some ((d, ds), j) => some (some (neg, d, ds), j)
    | none => none
  else some (none, i)

/-- `number = [ minus ] int [ frac ] [ exp ]`. -/
def parseNumA (a : ByteArray) (i : Nat) : Option (Number × Nat) :=
  let neg := byteIs a i 0x2D
  match parseIntA a (if neg then i + 1 else i) with
  | none => none
  | some (ip, i1) => match parseFracA a i1 with
    | none => none
    | some (fr, i2) => match parseExpA a i2 with
      | none => none
      | some (ex, i3) => some (⟨neg, ip, fr, ex⟩, i3)

/-- `UTF8-char` (RFC 3629): the scalar and the index after it. -/
@[inline] def decodeUtf8A (a : ByteArray) (i : Nat) : Option (Nat × Nat) :=
  match byteAt a i with
  | none => none
  | some x =>
    if x.toNat < 0x80 then some (x.toNat, i + 1)
    else if 0xC2 ≤ x.toNat ∧ x.toNat ≤ 0xDF then
      match byteAt a (i + 1) with
      | some b => if Tail b then some ((x.toNat - 0xC0) * 64 + (b.toNat - 0x80), i + 2) else none
      | none => none
    else if 0xE0 ≤ x.toNat ∧ x.toNat ≤ 0xEF then
      match byteAt a (i + 1), byteAt a (i + 2) with
      | some b, some c => if Second3 x b ∧ Tail c then some ((x.toNat - 0xE0) * 4096 + (b.toNat - 0x80) * 64 + (c.toNat - 0x80), i + 3) else none
      | _, _ => none
    else if 0xF0 ≤ x.toNat ∧ x.toNat ≤ 0xF4 then
      match byteAt a (i + 1), byteAt a (i + 2), byteAt a (i + 3) with
      | some b, some c, some d =>
        if Second4 x b ∧ Tail c ∧ Tail d then some ((x.toNat - 0xF0) * 262144 + (b.toNat - 0x80) * 4096 + (c.toNat - 0x80) * 64 + (d.toNat - 0x80), i + 4) else none
      | _, _, _ => none
    else none

/-- `4HEXDIG` at `i`. -/
@[inline] def hex4At (a : ByteArray) (i : Nat) : Option Nat :=
  match byteAt a i, byteAt a (i + 1), byteAt a (i + 2), byteAt a (i + 3) with
  | some w, some x, some y, some z => hex4 w x y z
  | _, _, _, _ => none

/-- The part of a `\\uXXXX` escape after the `\\u` (a scalar, or a surrogate pair), and the index after it. -/
@[inline] def decodeUA (a : ByteArray) (i : Nat) : Option (Nat × Nat) :=
  match hex4At a i with
  | none => none
  | some n =>
    if n < 0xD800 ∨ 0xE000 ≤ n then some (n, i + 4)
    else if n < 0xDC00 then
      if byteIs a (i + 4) 0x5C && byteIs a (i + 5) 0x75 then
        match hex4At a (i + 6) with
        | some lo => if 0xDC00 ≤ lo ∧ lo < 0xE000 then some (0x10000 + (n - 0xD800) * 0x400 + (lo - 0xDC00), i + 10) else none
        | none => none
      else none
    else none

/-- `char`: one unescaped character or escape (the byte at `i` exists). -/
@[inline] def decodeCharA (a : ByteArray) (i : Nat) : Option (Nat × Nat) :=
  if byteIs a i 0x5C then
    match byteAt a (i + 1) with
    | none => none
    | some b => if b == 0x75 then decodeUA a (i + 2) else match simpleEsc b with | some n => some (n, i + 2) | none => none
  else match decodeUtf8A a i with
    | some (n, j) => if 0x20 ≤ n ∧ n ≠ 0x22 ∧ n ≠ 0x5C then some (n, j) else none
    | none => none

/-- A plain ASCII byte inside a string: `0x20 ≤ x < 0x80`, not `"` (the caller has tested that) and not `\\`. Such a byte is one character, itself (`decodeCharA_plain`, `LeanJsonProofs/FastLeaf.lean`). -/
@[inline] def plainAscii (x : UInt8) : Bool := 0x20 ≤ x.toNat && x.toNat < 0x80 && x != 0x5C

/-- `*char quotation-mark`: the string so far (the test `i < j` always holds, `decodeCharA_adv` in `LeanJsonProofs/FastLeaf.lean`; it is what makes the loop terminate), then characters up to the closing quote; the index after the quote.
A plain ASCII byte is pushed at once, with no decoder call and so no `Option (Nat × Nat)` per character (the profile, `docs/perf/profile.md`: one heap object per text byte); the rest goes through `decodeCharA`. -/
def strLoop (a : ByteArray) (i : Nat) (s : String) : Option (String × Nat) :=
  if h : i < a.size then
    if a[i] == 0x22 then some (s, i + 1)
    else if plainAscii a[i] then strLoop a (i + 1) (s.push (Char.ofNat a[i].toNat))
    else match decodeCharA a i with
      | some (n, j) => if i < j then strLoop a j (s.push (Char.ofNat n)) else none
      | none => none
  else none
termination_by a.size - i

/-- `string`. -/
@[inline] def parseStrA (a : ByteArray) (i : Nat) : Option (String × Nat) :=
  if byteIs a i 0x22 then strLoop a (i + 1) "" else none

/-- `string`, `name-separator`, whitespace: the key and the index of what follows (the next value). -/
@[inline] def parseKeyA (a : ByteArray) (i : Nat) : Option (String × Nat) :=
  match parseStrA a i with
  | some (s, j) => let j1 := skipWsA a j; if byteIs a j1 0x3A then some (s, skipWsA a (j1 + 1)) else none
  | none => none

/-- A literal: strip `l` from the front. -/
def litA (a : ByteArray) (i : Nat) : Bytes → Option Nat
  | [] => some i
  | x :: xs => if byteIs a i x then litA a (i + 1) xs else none

/-- The open containers, innermost first: the elements (or members) read so far, newest first, and for a member the key still waiting for its value. -/
inductive Stack where
  | nil
  | arr (acc : List Value) (rest : Stack)
  | obj (acc : List (String × Value)) (key : String) (rest : Stack)

/-- The loop. `fuel` only bounds the steps (each step consumes input, so `a.size + 2` is enough: `run_sound` in `LeanJsonProofs/Fast.lean`). With `ret = false` a value starts at `i` (whitespace already skipped);
with `ret = true` the value `v` has just been read up to `i` and is handed to the innermost open container. `d` is the nesting budget left. -/
def run : Nat → ByteArray → Nat → Bool → Value → Stack → Nat → Except Error Value
  | 0, _, _, _, _, _, _ => .error .syntax
  | f + 1, a, i, false, _, st, d =>
    match byteAt a i with
    | none => .error .syntax
    | some b =>
      if b == 0x5B then
        if d == 0 then .error .depth
        else
          let i1 := skipWsA a (i + 1)
          if byteIs a i1 0x5D then run f a (i1 + 1) true (.arr []) st d
          else run f a i1 false .null (.arr [] st) (d - 1)
      else if b == 0x7B then
        if d == 0 then .error .depth
        else
          let i1 := skipWsA a (i + 1)
          if byteIs a i1 0x7D then run f a (i1 + 1) true (.obj []) st d
          else match parseKeyA a i1 with
            | some (k, j) => run f a j false .null (.obj [] k st) (d - 1)
            | none => .error .syntax
      else if b == 0x22 then
        match parseStrA a i with
        | some (s, j) => run f a j true (.str s) st d
        | none => .error .syntax
      else if b == 0x6E then
        match litA a (i + 1) [0x75, 0x6C, 0x6C] with | some j => run f a j true .null st d | none => .error .syntax
      else if b == 0x74 then
        match litA a (i + 1) [0x72, 0x75, 0x65] with | some j => run f a j true (.bool true) st d | none => .error .syntax
      else if b == 0x66 then
        match litA a (i + 1) [0x61, 0x6C, 0x73, 0x65] with | some j => run f a j true (.bool false) st d | none => .error .syntax
      else
        match parseNumA a i with
        | some (n, j) => run f a j true (.num n) st d
        | none => .error .syntax
  | _ + 1, a, i, true, v, .nil, _ => if a.size ≤ skipWsA a i then .ok v else .error .syntax
  | f + 1, a, i, true, v, .arr acc rest, d =>
    let i1 := skipWsA a i
    if byteIs a i1 0x2C then run f a (skipWsA a (i1 + 1)) false .null (.arr (v :: acc) rest) d
    else if byteIs a i1 0x5D then run f a (i1 + 1) true (.arr (v :: acc).reverse) rest (d + 1)
    else .error .syntax
  | f + 1, a, i, true, v, .obj acc k rest, d =>
    let i1 := skipWsA a i
    if byteIs a i1 0x2C then
      match parseKeyA a (skipWsA a (i1 + 1)) with
      | some (k', j) => run f a j false .null (.obj ((k, v) :: acc) k' rest) d
      | none => .error .syntax
    else if byteIs a i1 0x7D then run f a (i1 + 1) true (.obj ((k, v) :: acc).reverse) rest (d + 1)
    else .error .syntax

/-- The fast parser: the entry point of the closure gate. -/
def parseFast (a : ByteArray) : Except Error Value :=
  run (a.size + 2) a (skipWsA a 0) false .null .nil maxDepth

end LeanJson
