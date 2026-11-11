import LeanJson.PrintBytes
/-! # `LeanJson.PrintTape`: the compact JSON of a tape (the code of `vbm_json_print_tape`) and the checked string literal (`vbm_json_escape_string`)

`printTape w x` reads the tape `w` (the words, as `parseTape` writes them: `LeanJson/Tape.lean`) and its text region `x`, and writes the compact form straight into one buffer: no `Value`, no list.
It is a function of the tape alone and reads only what it checks: every word read is inside `w` (a word past the end reads as zero and the node is refused), a text range is inside `x`, a container's `aux` is the size of what it
holds, the nesting is at most `maxDepth`, the whole tape is consumed. A string's bytes must be valid UTF-8 (`utf8Range`), a number's bytes a number lexeme (`numLex`). `none` is a refused tape.
`printTape_encode` (`LeanJsonProofs/PrintTape.lean`): for the tape of a value (`encValue`), within `maxDepth` and the sizes the format holds, the result is `print v`. A tape the library did not write is memory-safe to print; what it
prints is JSON-shaped (structure, strings' UTF-8 and number characters are checked) but only a tape from `parseTape` is claimed to print to the value it stands for.
`escapeChecked a` is `escapeString a` when `a` is valid UTF-8 and `none` otherwise. -/
namespace LeanJson

/-- The little-endian word at word index `i`: eight loads after one bounds test (`0` when the word is not inside `a`; the printer tests before it reads). -/
def ldw (a : ByteArray) (i : Nat) : UInt64 :=
  let k := 8 * i
  if h : k + 8 ≤ a.size then
    (a[k]'(by omega)).toUInt64 + ((a[k + 1]'(by omega)).toUInt64 <<< 8) + ((a[k + 2]'(by omega)).toUInt64 <<< 16) + ((a[k + 3]'(by omega)).toUInt64 <<< 24) +
    ((a[k + 4]'(by omega)).toUInt64 <<< 32) + ((a[k + 5]'(by omega)).toUInt64 <<< 40) + ((a[k + 6]'(by omega)).toUInt64 <<< 48) + ((a[k + 7]'(by omega)).toUInt64 <<< 56)
  else 0

/-- The bytes `x[i:e]` are valid UTF-8 (RFC 3629), each sequence inside the range. -/
def utf8Range (x : ByteArray) (i e : Nat) : Bool :=
  if _h : i < e then
    match byteAt x i with
    | some c =>
      if c < 0x80 then utf8Range x (i + 1) e
      else match decodeUtf8A x i with
        | some (_, j) => if i < j ∧ j ≤ e then utf8Range x j e else false
        | none => false
    | none => false
  else true
termination_by e - i

/-- The index after the digits of `x` from `i`, none past `e`. -/
def scanDig (x : ByteArray) (i e : Nat) : Nat :=
  if _h : i < e then
    match byteAt x i with
    | some c => if 0x30 ≤ c ∧ c ≤ 0x39 then scanDig x (i + 1) e else i
    | none => i
  else i
termination_by e - i

/-- The index after an optional `-` at `i` (the number starts there). -/
@[inline] def numSign (x : ByteArray) (i e : Nat) : Nat := if i < e && byteIs x i 0x2D then i + 1 else i

/-- The index after the integer part at `i` (`0`, or a non-zero digit and digits); `0` when there is none. -/
@[inline] def numInt (x : ByteArray) (i e : Nat) : Nat :=
  if i < e then
    (match byteAt x i with
     | some c => if c == 0x30 then i + 1 else if 0x31 ≤ c.toNat ∧ c.toNat ≤ 0x39 then scanDig x (i + 1) e else 0
     | none => 0)
  else 0

/-- The index after an optional fraction (`.` and at least one digit) at `i`; `0` for a `.` with no digit. -/
@[inline] def numFrac (x : ByteArray) (i e : Nat) : Nat :=
  if i < e && byteIs x i 0x2E then
    (if i + 1 < e && (match byteAt x (i + 1) with | some c => 0x30 ≤ c.toNat ∧ c.toNat ≤ 0x39 | none => false) then scanDig x (i + 2) e else 0)
  else i

/-- The index after an optional exponent (`e` or `E`, an optional sign, at least one digit) at `i`; `0` for an exponent with no digit. -/
@[inline] def numExp (x : ByteArray) (i e : Nat) : Nat :=
  if i < e && (byteIs x i 0x65 || byteIs x i 0x45) then
    (let j := if i + 1 < e && (byteIs x (i + 1) 0x2B || byteIs x (i + 1) 0x2D) then i + 2 else i + 1
     if j < e && (match byteAt x j with | some c => 0x30 ≤ c.toNat ∧ c.toNat ≤ 0x39 | none => false) then scanDig x (j + 1) e else 0)
  else i

/-- `x[i:e]` is a number lexeme (RFC 8259: `-`, `0` or a non-zero digit and digits, `.` and at least one digit, `e` or `E`, `+` or `-`, at least one digit), nothing more and nothing less. -/
def numLex (x : ByteArray) (i e : Nat) : Bool :=
  let i2 := numInt x (numSign x i e) e
  if i2 == 0 then false else
  let i3 := numFrac x i2 e
  if i3 == 0 then false else
  let i4 := numExp x i3 e
  i4 != 0 && i4 == e

/-- The end of the run of bytes from `i` that need no escape (not a control, `"` or `\`), at most `e` and at most the end of `x`. -/
def plainEnd (x : ByteArray) (i e : Nat) : Nat :=
  if _h : i < e then
    if h' : i < x.size then
      if x[i] < 0x20 || x[i] == 0x22 || x[i] == 0x5C then i else plainEnd x (i + 1) e
    else i
  else i
termination_by e - i

/-- The bytes `x[i:e]` (those inside `x`), escaped, appended to `b`: a run that needs no escape is appended with one copy, an escape byte by `pushEsc`. -/
def escLoopR (x : ByteArray) (i e : Nat) (b : ByteArray) : ByteArray :=
  if _h : i < e then
    let j := plainEnd x i e
    let b := if i < j then x.copySlice i b b.size (j - i) false else b
    if h' : i ≤ j ∧ j < e ∧ j < x.size then escLoopR x (j + 1) e (pushEsc b (x[j]'h'.2.2)) else b   -- `i ≤ j` always holds (`plainEnd`); the test is what makes the loop terminate
  else b
termination_by e - i

/-- A scalar or string node (kind 0 to 4) with the words `h`, `aux`, written to `b`; no bytes at all for a node that is refused (what is written is never empty). A container has kind 5 or 6: refused here. -/
def pleaf (x : ByteArray) (h aux : UInt64) (b : ByteArray) : ByteArray :=
  let len := (h >>> 8).toNat
  let k := h % 256
  if k == 0 then (if len == 0 && aux == 0 then (((b.push 0x6E).push 0x75).push 0x6C).push 0x6C else ByteArray.empty)
  else if k == 1 then (if len == 0 && aux == 0 then ((((b.push 0x66).push 0x61).push 0x6C).push 0x73).push 0x65 else ByteArray.empty)
  else if k == 2 then (if len == 0 && aux == 0 then (((b.push 0x74).push 0x72).push 0x75).push 0x65 else ByteArray.empty)
  else if k == 3 then
    if aux < 0x4000000000000000 then
      let off := aux.toNat
      if off + len ≤ x.size && numLex x off (off + len) then escLoopR x off (off + len) b else ByteArray.empty
    else ByteArray.empty
  else if k == 4 then
    if aux < 0x4000000000000000 then
      let off := aux.toNat
      if off + len ≤ x.size && utf8Range x off (off + len) then (escLoopR x off (off + len) (b.push 0x22)).push 0x22 else ByteArray.empty
    else ByteArray.empty
  else ByteArray.empty

mutual
/-- The printer is generic in the word load `ld` and the leaf writer `lf` (`ldw`, `pleaf` here; a faster pair with the proved equations in `LeanJsonSimd/PrintSimd.lean`): the code is the same. The container (kind 5 or 6) at word `i` with the words `h`, `aux`, written to `b`, with `d` levels of nesting left; the buffer (no bytes: refused) and the index of the next word. A container's `aux` must be the size of what it holds. -/
@[specialize] def pnode (ld : ByteArray → Nat → UInt64) (lf : ByteArray → UInt64 → UInt64 → ByteArray → ByteArray) (w x : ByteArray) : Nat → Nat → UInt64 → UInt64 → ByteArray → ByteArray × Nat
  | 0, _, _, _, _ => (ByteArray.empty, 0)
  | d + 1, i, h, aux, b =>
    let len := (h >>> 8).toNat
    let k := h % 256
    if k == 5 then
      match pelems ld lf w x d (i + 2) len true (b.push 0x5B) with
      | (b', j) => if b'.size != 0 && aux == UInt64.ofNat (j - i) then (b'.push 0x5D, j) else (ByteArray.empty, 0)
    else if k == 6 then
      match pmembers ld lf w x d (i + 2) len true (b.push 0x7B) with
      | (b', j) => if b'.size != 0 && aux == UInt64.ofNat (j - i) then (b'.push 0x7D, j) else (ByteArray.empty, 0)
    else (ByteArray.empty, 0)
  termination_by d => (d, 0, 0)

/-- `n` more elements from word `i`; a comma before each but the first. A scalar or string element is written in place, a container by `pnode`. -/
@[specialize] def pelems (ld : ByteArray → Nat → UInt64) (lf : ByteArray → UInt64 → UInt64 → ByteArray → ByteArray) (w x : ByteArray) (d i : Nat) : Nat → Bool → ByteArray → ByteArray × Nat
  | 0, _, b => (b, i)
  | n + 1, first, b =>
    if 8 * i + 16 ≤ w.size then
      let h := ld w i
      let aux := ld w (i + 1)
      let b := if first then b else b.push 0x2C
      if h % 256 ≤ 4 then
        let r := lf x h aux b
        if r.size == 0 then (ByteArray.empty, 0) else pelems ld lf w x d (i + 2) n false r
      else
        match pnode ld lf w x d i h aux b with
        | (b', j) => if b'.size == 0 then (ByteArray.empty, 0) else pelems ld lf w x d j n false b'
    else (ByteArray.empty, 0)
  termination_by n => (d, 1, n)

/-- `n` more members (a string node, its value) from word `i`; a comma before each but the first. -/
@[specialize] def pmembers (ld : ByteArray → Nat → UInt64) (lf : ByteArray → UInt64 → UInt64 → ByteArray → ByteArray) (w x : ByteArray) (d i : Nat) : Nat → Bool → ByteArray → ByteArray × Nat
  | 0, _, b => (b, i)
  | n + 1, first, b =>
    if 8 * i + 32 ≤ w.size then
      let h := ld w i
      let aux := ld w (i + 1)
      let b := if first then b else b.push 0x2C
      if h % 256 == 4 then
        let r := lf x h aux b
        if r.size == 0 then (ByteArray.empty, 0) else
        let b1 := r.push 0x3A
        let h2 := ld w (i + 2)
        let aux2 := ld w (i + 3)
        if h2 % 256 ≤ 4 then
          let r2 := lf x h2 aux2 b1
          if r2.size == 0 then (ByteArray.empty, 0) else pmembers ld lf w x d (i + 4) n false r2
        else
          match pnode ld lf w x d (i + 2) h2 aux2 b1 with
          | (b', j) => if b'.size == 0 then (ByteArray.empty, 0) else pmembers ld lf w x d j n false b'
      else (ByteArray.empty, 0)
    else (ByteArray.empty, 0)
  termination_by n => (d, 1, n)
end

/-- The compact JSON of the tape `(w, x)`, or `none` for a tape that is refused (generic in the load and the leaf writer, as `pnode`). -/
@[specialize] def printTapeG (ld : ByteArray → Nat → UInt64) (lf : ByteArray → UInt64 → UInt64 → ByteArray → ByteArray) (w x : ByteArray) : Option ByteArray :=
  if 16 ≤ w.size then
    let h := ld w 0
    let aux := ld w 1
    let b := ByteArray.emptyWithCapacity (x.size + w.size / 4 + 16)
    if h % 256 ≤ 4 then
      let r := lf x h aux b
      if r.size != 0 && w.size == 16 then some r else none
    else
      match pnode ld lf w x maxDepth 0 h aux b with
      | (r, j) => if r.size != 0 && 8 * j == w.size then some r else none
  else none

/-- The compact JSON of the tape `(w, x)` with the reference load and leaf writer. -/
def printTape (w x : ByteArray) : Option ByteArray := printTapeG ldw pleaf w x

/-- The string literal of `a`, when `a` is valid UTF-8. -/
def escapeChecked (a : ByteArray) : Option ByteArray :=
  if utf8Range a 0 a.size then some (escapeString a) else none

end LeanJson
