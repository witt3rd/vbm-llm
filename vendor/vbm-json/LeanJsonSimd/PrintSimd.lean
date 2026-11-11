import LeanJson.PrintTape
import LeanJsonSimd.ParseSimd
import VbmSimd.Shims
/-! # `LeanJsonSimd.PrintSimd`: the tape printer with the word load of vbm-simd (the code of `vbm_json_print_tape`)

`LeanJson.printTapeG` (`LeanJson/PrintTape.lean`) is the printer, generic in the load of a tape word and in the writer of a scalar or string node. Here it is run with `ldwS`: the word is one `ld64` (a single 8-byte load, `VbmSimd.ld64`)
when the word is inside the tape and the tape is below 4 GiB (`size / 65536 < 65536`: a literal of 2^32 would be a big number to the compiler) (so that the byte offset is exact on 32 bits), the reference `ldw` otherwise. `ldwS_eq` (`LeanJsonProofs/PrintSimd.lean`): `ldwS = ldw`, so `printTapeS_eq`: `printTapeS = printTape`,
and everything proved of `printTape` (`printTape_encode`) holds of the export. -/
namespace LeanJson
open VbmSimd

/-- `ldw`, by one load. The word is inside the tape (`i + 1 ≤ size / 8`, tested without a multiplication) and its byte offset is below 2^31, so it is exact on 32 bits. -/
@[inline] def ldwS (a : ByteArray) (i : Nat) : UInt64 :=
  if i < 268435456 ∧ i + 1 ≤ a.size >>> 3 then ld64 a (8 * i).toUSize else ldw a i

/-! ## The leaves: a text read a word at a time

`runS flag tl x i e` is the end of the run of bytes `x[i:e]` that `flag` does not flag, found eight bytes at a time (`ld64`, the first flagged lane by `ctz`; the word may extend past `e` or past the end of `x`: those lanes
read as zero, which both flags report, and the result is at most `e`); outside the guard (`e` past the end of `x`, a text of 4 GiB or more) it is `tl`, the byte-at-a-time function. `plainEndS` is `plainEnd`
(a run with no control, quote or backslash), `scanDigS` is `scanDig` (a run of digits), `utf8RangeS` is `utf8Range` (eight ASCII bytes are skipped at once), `escLoopRS`, `numLexS` and `pleafS` are `escLoopR`, `numLex`, `pleaf` with those. -/

/-- `0x80` in every lane of `w` that is a control below `0x20`, a quote or a backslash (`escFlag_lane`). -/
@[inline] def escFlag (w : UInt64) : UInt64 :=
  (~~~((w &&& cLo7) + 0x6060606060606060) &&& ~~~w &&& cHi) ||| eqLanes cBslash w ||| eqLanes cQuote w

/-- The end of the run of bytes of `x[i:e]` that `flag` leaves unflagged (see above). -/
@[specialize] def runS (flag : UInt64 → UInt64) (tl : ByteArray → Nat → Nat → Nat) (x : ByteArray) (i e : Nat) : Nat :=
  if h : i < e ∧ e ≤ x.size ∧ x.size / 65536 < 65536 then
    let f := flag (ld64 x i.toUSize)
    if f == 0 then (if i + 8 < e then runS flag tl x (i + 8) e else e)
    else (let j := i + (ctz f).toNat / 8; if j < e then j else e)
  else tl x i e
termination_by e - i

/-- `plainEnd`, a word at a time. -/
@[inline] def plainEndS (x : ByteArray) (i e : Nat) : Nat := runS escFlag plainEnd x i e
/-- `scanDig`, a word at a time. -/
@[inline] def scanDigS (x : ByteArray) (i e : Nat) : Nat := runS ndFlags scanDig x i e

/-- `utf8Range`, with eight ASCII bytes skipped at once. -/
def utf8RangeS (x : ByteArray) (i e : Nat) : Bool :=
  if _h : i < e then
    if i + 8 ≤ e ∧ e ≤ x.size ∧ x.size / 65536 < 65536 ∧ (ld64 x i.toUSize &&& cHi) == 0 then utf8RangeS x (i + 8) e
    else
    match byteAt x i with
    | some c =>
      if c < 0x80 then utf8RangeS x (i + 1) e
      else match decodeUtf8A x i with
        | some (_, j) => if i < j ∧ j ≤ e then utf8RangeS x j e else false
        | none => false
    | none => false
  else true
termination_by e - i

/-- `numInt`, `numFrac`, `numExp`, `numLex` with `scanDigS`. -/
@[inline] def numIntS (x : ByteArray) (i e : Nat) : Nat :=
  if i < e then
    (match byteAt x i with
     | some c => if c == 0x30 then i + 1 else if 0x31 ≤ c.toNat ∧ c.toNat ≤ 0x39 then scanDigS x (i + 1) e else 0
     | none => 0)
  else 0
@[inline] def numFracS (x : ByteArray) (i e : Nat) : Nat :=
  if i < e && byteIs x i 0x2E then
    (if i + 1 < e && (match byteAt x (i + 1) with | some c => 0x30 ≤ c.toNat ∧ c.toNat ≤ 0x39 | none => false) then scanDigS x (i + 2) e else 0)
  else i
@[inline] def numExpS (x : ByteArray) (i e : Nat) : Nat :=
  if i < e && (byteIs x i 0x65 || byteIs x i 0x45) then
    (let j := if i + 1 < e && (byteIs x (i + 1) 0x2B || byteIs x (i + 1) 0x2D) then i + 2 else i + 1
     if j < e && (match byteAt x j with | some c => 0x30 ≤ c.toNat ∧ c.toNat ≤ 0x39 | none => false) then scanDigS x (j + 1) e else 0)
  else i
def numLexS (x : ByteArray) (i e : Nat) : Bool :=
  let i2 := numIntS x (numSign x i e) e
  if i2 == 0 then false else
  let i3 := numFracS x i2 e
  if i3 == 0 then false else
  let i4 := numExpS x i3 e
  i4 != 0 && i4 == e

/-- `escLoopR`, with `plainEndS`. -/
def escLoopRS (x : ByteArray) (i e : Nat) (b : ByteArray) : ByteArray :=
  if _h : i < e then
    let j := plainEndS x i e
    let b := if i < j then x.copySlice i b b.size (j - i) false else b
    if h' : i ≤ j ∧ j < e ∧ j < x.size then escLoopRS x (j + 1) e (pushEsc b (x[j]'h'.2.2)) else b
  else b
termination_by e - i

/-- `pleaf`, with the word-at-a-time leaves; a lexeme that passed `numLexS` holds no byte to escape (`numLex_allC`), so it is copied whole. -/
def pleafS (x : ByteArray) (h aux : UInt64) (b : ByteArray) : ByteArray :=
  let len := (h >>> 8).toNat
  let k := h % 256
  if k == 0 then (if len == 0 && aux == 0 then (((b.push 0x6E).push 0x75).push 0x6C).push 0x6C else ByteArray.empty)
  else if k == 1 then (if len == 0 && aux == 0 then ((((b.push 0x66).push 0x61).push 0x6C).push 0x73).push 0x65 else ByteArray.empty)
  else if k == 2 then (if len == 0 && aux == 0 then (((b.push 0x74).push 0x72).push 0x75).push 0x65 else ByteArray.empty)
  else if k == 3 then
    if aux < 0x4000000000000000 then
      let off := aux.toNat
      if off + len ≤ x.size && numLexS x off (off + len) then x.copySlice off b b.size len false else ByteArray.empty
    else ByteArray.empty
  else if k == 4 then
    if aux < 0x4000000000000000 then
      let off := aux.toNat
      if off + len ≤ x.size && utf8RangeS x off (off + len) then (escLoopRS x off (off + len) (b.push 0x22)).push 0x22 else ByteArray.empty
    else ByteArray.empty
  else ByteArray.empty

/-- The string literal of `a` when `a` is valid UTF-8 (`escapeChecked`), the check and the escape a word at a time. -/
def escapeCheckedS (a : ByteArray) : Option ByteArray :=
  if utf8RangeS a 0 a.size then some ((escLoopRS a 0 a.size ((ByteArray.emptyWithCapacity (a.size + 2)).push 0x22)).push 0x22) else none

/-- The export `vbm_json_lean_escape_string` (called by `vbm_json_escape_string`): the string literal, or no bytes for text that is not valid UTF-8 (a literal is never empty). -/
@[export vbm_json_lean_escape_string]
def escapeStringExport (a : ByteArray) : ByteArray := (escapeCheckedS a).getD ByteArray.empty

/-- The compact JSON of the tape `(w, x)` (`printTape`), the words read by `ld64`, the texts a word at a time. -/
def printTapeS (w x : ByteArray) : Option ByteArray := printTapeG ldwS pleafS w x

/-- The export `vbm_json_lean_print_tape` (called by `vbm_json_print_tape` in `abi/vbm_json.c`): the JSON bytes, or no bytes for a refused tape (printed JSON is never empty). -/
@[export vbm_json_lean_print_tape]
def printTapeExport (w x : ByteArray) : ByteArray := (printTapeS w x).getD ByteArray.empty

end LeanJson
