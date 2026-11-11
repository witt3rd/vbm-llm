import LeanJson.Print
import LeanJson.Parse
/-! # `LeanJson.Tape`: the flat tape, and the one function the C ABI calls (`vbm_json_parse_tape`)

The tape is the `Value` flattened in document order, so that a caller in any language reads it with no knowledge of Lean's object layout. It is built here, in Lean, and the C edge
(`abi/vbm_json.c`) only moves the bytes: **the boundary never decides**. Layout (version 1; every word is a little-endian `u64`):
- a node is two words: `head = kind | len << 8` and `aux`;
- kinds: `0` null, `1` false, `2` true, `3` number, `4` string, `5` array, `6` object;
- null, false, true: `len = 0`, `aux = 0`;
- number, string: `len` bytes of the text region starting at `aux`. A number's text is the printed lexeme (`printNumber`: `-`, digits, `.digits`, `e[-]digits`); a string's text is its UTF-8, unescaped;
- array: `len` elements follow, each a node; object: `len` members follow, each a string node (the key) then a node (the value); `aux` is the number of words of the whole subtree
  including the two of this node, so a reader skips it in one step;
- the tape is the root node and what it contains; the text region is the concatenation of all texts, in document order.

`parseTape` is the result a C caller gets, as bytes: `status` (`0`, or `Error.code`), `words`, `text` (the lengths in words and in bytes of the two regions), then the tape, then the text.
Where a string is already in the input without escapes, a later slice may point into the input instead (the ABI does not promise either); today every text is copied into the text region.
The layout is proved (`encValue_layout`, `LeanJsonProofs/Layout.lean`); the open claim is the reader; the tests in `scripts/test_abi.sh` read the tape back and compare it with the reference's canonical form. -/
namespace LeanJson

/-- The word `w`, little-endian: the definition of the layout (eight pushes). The code runs `pushWordFast`, equal to it (`pushWordFast_eq`, `LeanJsonProofs/Tape.lean`). -/
def pushWord (b : ByteArray) (w : UInt64) : ByteArray :=
  (((((((b.push w.toUInt8).push (w >>> 8).toUInt8).push (w >>> 16).toUInt8).push (w >>> 24).toUInt8).push (w >>> 32).toUInt8).push (w >>> 40).toUInt8).push (w >>> 48).toUInt8).push (w >>> 56).toUInt8

/-- Eight zero bytes (a constant, built with `push`: the freestanding runtime has no `lean_mk_array`). -/
def zero8 : ByteArray := ((((((((ByteArray.empty.push 0).push 0).push 0).push 0).push 0).push 0).push 0).push 0)

/-- `pushWord`, with one append of zeros (one runtime call, capacity doubling) and eight in-place byte stores instead of eight `push` calls (the profile: `lean_byte_array_push` is 5 to 13% of the time). -/
def pushWordFast (b : ByteArray) (w : UInt64) : ByteArray :=
  let k := b.size
  ((((((((b ++ zero8).set! k w.toUInt8).set! (k + 1) (w >>> 8).toUInt8).set! (k + 2) (w >>> 16).toUInt8).set! (k + 3) (w >>> 24).toUInt8).set! (k + 4) (w >>> 32).toUInt8).set! (k + 5) (w >>> 40).toUInt8).set! (k + 6) (w >>> 48).toUInt8).set! (k + 7) (w >>> 56).toUInt8

/-- Overwrite the word at word index `i` (an in-place update when `b` is unshared). -/
def setWord (b : ByteArray) (i : Nat) (w : UInt64) : ByteArray :=
  let k := 8 * i
  ((((((((b.set! k w.toUInt8).set! (k + 1) (w >>> 8).toUInt8).set! (k + 2) (w >>> 16).toUInt8).set! (k + 3) (w >>> 24).toUInt8).set! (k + 4) (w >>> 32).toUInt8).set! (k + 5) (w >>> 40).toUInt8).set! (k + 6) (w >>> 48).toUInt8).set! (k + 7) (w >>> 56).toUInt8)

/-- The tape and the text region under construction. -/
structure TapeBuf where
  tape : ByteArray
  text : ByteArray

def kindNull : Nat := 0
def kindFalse : Nat := 1
def kindTrue : Nat := 2
def kindNum : Nat := 3
def kindStr : Nat := 4
def kindArr : Nat := 5
def kindObj : Nat := 6

/-- A node: its two words. -/
def TapeBuf.node (s : TapeBuf) (kind len aux : Nat) : TapeBuf :=
  { s with tape := pushWordFast (pushWordFast s.tape (UInt64.ofNat (kind + len * 256))) (UInt64.ofNat aux) }

/-- `l` appended to `b` as digit bytes. -/
def pushDigits (b : ByteArray) : List Digit → ByteArray
  | [] => b
  | d :: ds => pushDigits (b.push (digitByte d)) ds

/-- `printNumber n` appended to `b`: straight into the buffer, no list, no `ByteArray.mk` (`pushNumber_eq`, `LeanJsonProofs/Tape.lean`). -/
def pushNumber (b : ByteArray) (n : Number) : ByteArray :=
  let b := if n.neg then b.push 0x2D else b
  let b := match n.int with
    | .zero => b.push 0x30
    | .nz l rest => pushDigits (b.push (UInt8.ofNat (0x31 + l.val))) rest
  let b := match n.frac with
    | none => b
    | some (d, ds) => pushDigits ((b.push 0x2E).push (digitByte d)) ds
  match n.exp with
  | none => b
  | some (neg, d, ds) => pushDigits ((if neg then (b.push 0x65).push 0x2D else b.push 0x65).push (digitByte d)) ds

/-- A number node: its lexeme goes to the end of the text region. -/
def TapeBuf.num (s : TapeBuf) (n : Number) : TapeBuf :=
  match s with
  | ⟨tape, text⟩ =>
    let o := text.size
    let t := pushNumber text n
    ⟨pushWordFast (pushWordFast tape (UInt64.ofNat (kindNum + (t.size - o) * 256))) (UInt64.ofNat o), t⟩

/-- A number or string node: the text goes to the end of the text region. -/
def TapeBuf.leaf (s : TapeBuf) (kind : Nat) (t : ByteArray) : TapeBuf :=
  let s' := s.node kind t.size s.text.size
  { s' with text := s'.text ++ t }

/-- The number of words written so far. -/
def TapeBuf.words (s : TapeBuf) : Nat := s.tape.size / 8

/-- Close a container whose first word index is `at`: its `aux` is the size of its subtree. -/
def TapeBuf.close (s : TapeBuf) (at_ : Nat) : TapeBuf := { s with tape := setWord s.tape (at_ + 1) (UInt64.ofNat (s.words - at_)) }

mutual
def encValue : Value → TapeBuf → TapeBuf
  | .null, s => s.node kindNull 0 0
  | .bool false, s => s.node kindFalse 0 0
  | .bool true, s => s.node kindTrue 0 0
  | .num n, s => s.num n
  | .str t, s => s.leaf kindStr t.toUTF8
  | .arr xs, s => let at_ := s.words; (encList xs (s.node kindArr xs.length 0)).close at_
  | .obj ms, s => let at_ := s.words; (encMembers ms (s.node kindObj ms.length 0)).close at_
def encList : List Value → TapeBuf → TapeBuf
  | [], s => s
  | v :: vs, s => encList vs (encValue v s)
def encMembers : List (String × Value) → TapeBuf → TapeBuf
  | [], s => s
  | (k, v) :: ms, s => encMembers ms (encValue v (s.leaf kindStr k.toUTF8))
end

/-- The specification of the result of `vbm_json_parse_tape` as bytes: `status`, `words`, `text`, the tape, the text (see the module comment). The export is `parseTapeSimd` (`LeanJsonSimd/ParseSimd.lean`), equal to `parseTapeFast` (below),
which returns these bytes without building the `Value` (`parseTapeFast_eq`, `LeanJsonProofs/FastLoop.lean`). -/
def parseTape (a : ByteArray) : ByteArray :=
  match parseFast a with
  | .error e => pushWordFast (pushWordFast (pushWordFast .empty (UInt64.ofNat e.code)) 0) 0
  | .ok v =>
    let s := encValue v ⟨.empty, .empty⟩
    (pushWordFast (pushWordFast (pushWordFast .empty 0) (UInt64.ofNat s.words)) (UInt64.ofNat s.text.size) ++ s.tape) ++ s.text


/-! ## The fused parser (parse and tape in one pass): `parseTapeFast`, the fallback of the export

`docs/perf/fuse-plan.md`. `parseTapeFast` runs the loop of `run` (`LeanJson/Parse.lean`) writing the tape and the text region as it reads, and never builds a `Value`; the theorem
`parseTapeFast_eq : parseTapeFast a = parseTape a` (`LeanJsonProofs/FastLoop.lean`) is what lets the export `vbm_json_parse_tape` (`parseTapeSimd`, which falls back to this function) be proved equal to the specification. `parseTape` (the tape of the value) and `parseFast`
(the oracle) stay as the specification and are not run by the export. -/

/-- The open containers of the fused loop, innermost first: the word index of the container's header on the tape, and the number of elements (members) completed in it so far. -/
inductive FStack where
  | nil
  | arr (at_ n : Nat) (rest : FStack)
  | obj (at_ n : Nat) (rest : FStack)

/-- Close a container: the header was written with placeholders (`TapeBuf.node kind 0 0`) when it opened; now its count and its subtree size are known. The words are read apart first,
so the tape stays unshared (the in-place path). -/
def TapeBuf.closeNode (s : TapeBuf) (kind at_ n : Nat) : TapeBuf :=
  match s with
  | ⟨tape, text⟩ =>
    let w := UInt64.ofNat (tape.size / 8 - at_)
    ⟨setWord (setWord tape at_ (UInt64.ofNat (kind + n * 256))) (at_ + 1) w, text⟩

/-! ## F1: numbers are scanned, then copied from the input

`scanNum a i` is `parseNumA` without its value: the end index of the number at `i`, if there is one (no digit lists). `TapeBuf.numLex` then writes the node and the canonical lexeme of the bytes
`a[i..j)` into the text region: `e` for `E`, no `+`; everything else as it is (`numLex_eq`, `LeanJsonProofs/FastTape.lean`: it is `TapeBuf.num` of the number `parseNumA` reads). -/

/-- `*DIGIT`: the index after the digits. -/
def scanDigits (a : ByteArray) (i : Nat) : Nat :=
  if h : i < a.size then (if (digitVal a[i]).isSome then scanDigits a (i + 1) else i) else i
termination_by a.size - i

/-- `1*DIGIT`. -/
@[inline] def scanDigits1 (a : ByteArray) (i : Nat) : Option Nat :=
  match byteAt a i with
  | some b => if (digitVal b).isSome then some (scanDigits a (i + 1)) else none
  | none => none

/-- The end of `int`. -/
@[inline] def scanInt (a : ByteArray) (i : Nat) : Option Nat :=
  match byteAt a i with
  | none => none
  | some b => if b == 0x30 then some (i + 1) else if (digit19 b).isSome then some (scanDigits a (i + 1)) else none

/-- The end of `[ frac ]`. -/
@[inline] def scanFrac (a : ByteArray) (i : Nat) : Option Nat :=
  if byteIs a i 0x2E then scanDigits1 a (i + 1) else some i

/-- The end of `[ exp ]`. -/
@[inline] def scanExp (a : ByteArray) (i : Nat) : Option Nat :=
  if byteIs a i 0x65 || byteIs a i 0x45 then scanDigits1 a (if byteIs a (i + 1) 0x2B || byteIs a (i + 1) 0x2D then i + 2 else i + 1)
  else some i

/-- The end of `number = [ minus ] int [ frac ] [ exp ]` at `i`. -/
def scanNum (a : ByteArray) (i : Nat) : Option Nat :=
  match scanInt a (if byteIs a i 0x2D then i + 1 else i) with
  | none => none
  | some i1 => match scanFrac a i1 with
    | none => none
    | some i2 => scanExp a i2

/-- The bytes `a[i..j)` appended to `b`, in the canonical lexeme: `E` as `e`, `+` dropped. -/
def pushLex (a : ByteArray) (i j : Nat) (b : ByteArray) : ByteArray :=
  if i < j then
    match byteAt a i with
    | none => b
    | some c => pushLex a (i + 1) j (if c == 0x45 then b.push 0x65 else if c == 0x2B then b else b.push c)
  else b
termination_by j - i

/-- A number node whose lexeme is `a[i..j)`: the tape words and the text, written in place (the same shape as `TapeBuf.num`). -/
def TapeBuf.numLex (s : TapeBuf) (a : ByteArray) (i j : Nat) : TapeBuf :=
  match s with
  | ⟨tape, text⟩ =>
    let o := text.size
    let t := pushLex a i j text
    ⟨pushWordFast (pushWordFast tape (UInt64.ofNat (kindNum + (t.size - o) * 256))) (UInt64.ofNat o), t⟩

/-! ## F2: strings are scanned straight into the text region

`strBytes` is `strLoop` (`LeanJson/Parse.lean`) writing UTF-8 bytes where `strLoop` pushes characters: the same case analysis, the same decoder, the same stops. A plain ASCII byte is one byte; any other
character goes through `decodeCharA` and is appended as `String.utf8EncodeChar` writes it (`pushChar` is that function's body with `push` for the list; `pushChar_eq` in `LeanJsonProofs/FastTape.lean`).
`TapeBuf.strNode` writes the node (`kind` is a string, or a key) and the text of the string that starts with the quote at `i`. -/

/-- The UTF-8 bytes of `c` appended to `b` (the body of `String.utf8EncodeCharFast`, on a `ByteArray`). -/
def pushChar (b : ByteArray) (c : Char) : ByteArray :=
  let v := c.val
  if v ≤ 0x7f then b.push v.toUInt8
  else if v ≤ 0x7ff then (b.push ((v >>> 6).toUInt8 &&& 0x1f ||| 0xc0)).push (v.toUInt8 &&& 0x3f ||| 0x80)
  else if v ≤ 0xffff then ((b.push ((v >>> 12).toUInt8 &&& 0x0f ||| 0xe0)).push ((v >>> 6).toUInt8 &&& 0x3f ||| 0x80)).push (v.toUInt8 &&& 0x3f ||| 0x80)
  else (((b.push ((v >>> 18).toUInt8 &&& 0x07 ||| 0xf0)).push ((v >>> 12).toUInt8 &&& 0x3f ||| 0x80)).push ((v >>> 6).toUInt8 &&& 0x3f ||| 0x80)).push (v.toUInt8 &&& 0x3f ||| 0x80)

/-- `strLoop`, onto a byte buffer: the text of the characters read so far is `b`. -/
def strBytes (a : ByteArray) (i : Nat) (b : ByteArray) : Option (ByteArray × Nat) :=
  if h : i < a.size then
    if a[i] == 0x22 then some (b, i + 1)
    else if plainAscii a[i] then strBytes a (i + 1) (b.push a[i])
    else match decodeCharA a i with
      | some (n, j) => if i < j then strBytes a j (pushChar b (Char.ofNat n)) else none
      | none => none
  else none
termination_by a.size - i

/-- A string node (a value or a key) from the string whose opening quote is at `i`: the header words and the text, written in place; the index after the closing quote. -/
def TapeBuf.strNode (s : TapeBuf) (kind : Nat) (a : ByteArray) (i : Nat) : Option (TapeBuf × Nat) :=
  match s with
  | ⟨tape, text⟩ =>
    if byteIs a i 0x22 then
      let o := text.size
      match strBytes a (i + 1) text with
      | some (t, j) => some (⟨pushWordFast (pushWordFast tape (UInt64.ofNat (kind + (t.size - o) * 256))) (UInt64.ofNat o), t⟩, j)
      | none => none
    else none

/-! ## F4: the loop

`runT` is `run` (`LeanJson/Parse.lean`) with the `Value` and the element lists replaced by the tape and the open containers' header positions: the same branches in the same order, the same errors. A
container's header is written with placeholders when it opens and patched when it closes (`TapeBuf.closeNode`); a key is written when it is read. Every `let` below that reads `tb` is before the call that
consumes it: the tape and the text region stay unshared (the in-place path). The refinement statement is `parseTapeFast_eq` (`LeanJsonProofs/FastLoop.lean`). -/

/-- The result of `vbm_json_parse_tape` on an error: the status and two zero words (`parseTape`'s error case). -/
def tapeErr (e : Error) : ByteArray := pushWordFast (pushWordFast (pushWordFast .empty (UInt64.ofNat e.code)) 0) 0

/-- The result on success: status 0, the sizes, the tape, the text (`parseTape`'s ok case). -/
def tapeOk (s : TapeBuf) : ByteArray :=
  (pushWordFast (pushWordFast (pushWordFast .empty 0) (UInt64.ofNat s.words)) (UInt64.ofNat s.text.size) ++ s.tape) ++ s.text

/-- A key and its colon: the key node written, the index of the value after the whitespace (`parseKeyA`). -/
def TapeBuf.keyNode (s : TapeBuf) (a : ByteArray) (i : Nat) : Option (TapeBuf × Nat) :=
  match s.strNode kindStr a i with
  | some (s', j) => let j1 := skipWsA a j; if byteIs a j1 0x3A then some (s', skipWsA a (j1 + 1)) else none
  | none => none

/-- The loop. With `ret = false` a value starts at `i`; with `ret = true` one has just been completed and the tape ends with it. `fst` is the open containers, `d` the nesting budget left. -/
def runT : Nat → ByteArray → Nat → Bool → TapeBuf → FStack → Nat → ByteArray
  | 0, _, _, _, _, _, _ => tapeErr .syntax
  | f + 1, a, i, false, tb, fst, d =>
    match byteAt a i with
    | none => tapeErr .syntax
    | some b =>
      if b == 0x5B then
        if d == 0 then tapeErr .depth
        else
          let i1 := skipWsA a (i + 1)
          if byteIs a i1 0x5D then runT f a (i1 + 1) true (tb.node kindArr 0 2) fst d
          else
            let at_ := tb.words
            runT f a i1 false (tb.node kindArr 0 0) (.arr at_ 0 fst) (d - 1)
      else if b == 0x7B then
        if d == 0 then tapeErr .depth
        else
          let i1 := skipWsA a (i + 1)
          if byteIs a i1 0x7D then runT f a (i1 + 1) true (tb.node kindObj 0 2) fst d
          else
            let at_ := tb.words
            match (tb.node kindObj 0 0).keyNode a i1 with
            | some (tb', j) => runT f a j false tb' (.obj at_ 0 fst) (d - 1)
            | none => tapeErr .syntax
      else if b == 0x22 then
        match tb.strNode kindStr a i with
        | some (tb', j) => runT f a j true tb' fst d
        | none => tapeErr .syntax
      else if b == 0x6E then
        match litA a (i + 1) [0x75, 0x6C, 0x6C] with | some j => runT f a j true (tb.node kindNull 0 0) fst d | none => tapeErr .syntax
      else if b == 0x74 then
        match litA a (i + 1) [0x72, 0x75, 0x65] with | some j => runT f a j true (tb.node kindTrue 0 0) fst d | none => tapeErr .syntax
      else if b == 0x66 then
        match litA a (i + 1) [0x61, 0x6C, 0x73, 0x65] with | some j => runT f a j true (tb.node kindFalse 0 0) fst d | none => tapeErr .syntax
      else
        match scanNum a i with
        | some j => runT f a j true (tb.numLex a i j) fst d
        | none => tapeErr .syntax
  | _ + 1, a, i, true, tb, .nil, _ => if a.size ≤ skipWsA a i then tapeOk tb else tapeErr .syntax
  | f + 1, a, i, true, tb, .arr at_ n rest, d =>
    let i1 := skipWsA a i
    if byteIs a i1 0x2C then runT f a (skipWsA a (i1 + 1)) false tb (.arr at_ (n + 1) rest) d
    else if byteIs a i1 0x5D then runT f a (i1 + 1) true (tb.closeNode kindArr at_ (n + 1)) rest (d + 1)
    else tapeErr .syntax
  | f + 1, a, i, true, tb, .obj at_ n rest, d =>
    let i1 := skipWsA a i
    if byteIs a i1 0x2C then
      match tb.keyNode a (skipWsA a (i1 + 1)) with
      | some (tb', j) => runT f a j false tb' (.obj at_ (n + 1) rest) d
      | none => tapeErr .syntax
    else if byteIs a i1 0x7D then runT f a (i1 + 1) true (tb.closeNode kindObj at_ (n + 1)) rest (d + 1)
    else tapeErr .syntax

/-- The fused parser: the tape of `parseTape`, without the `Value`: the bytes are `parseTape`'s on every input (`parseTapeFast_eq`). It is the fallback of the export `vbm_json_parse_tape`, `LeanJson.parseTapeSimd` (`LeanJsonSimd/ParseSimd.lean`, equal to it: `parseTapeSimd_eq`). -/
def parseTapeFast (a : ByteArray) : ByteArray :=
  runT (a.size + 2) a (skipWsA a 0) false ⟨.empty, .empty⟩ .nil maxDepth

end LeanJson
