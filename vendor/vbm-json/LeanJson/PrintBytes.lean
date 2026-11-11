import LeanJson.Tape
/-! # `LeanJson.PrintBytes`: the byte printer

`printBytes v` is the compact form of `v` (`print v`, `LeanJson/Print.lean`) as a `ByteArray`, written straight into one buffer: no list of the output, no intermediate string, a buffer pushed byte by byte
(the runtime doubles its capacity). `printBytes_eq` (`LeanJsonProofs/PrintBytes.lean`) is the statement: it is `⟨(print v).toArray⟩`, so everything proved of `print` holds of these bytes.
`escapeString a` is the quoted, escaped JSON string of the UTF-8 text `a` (what `printString` writes for the string `a` encodes): an encoder that already holds a string as bytes builds an object around it with this.
What is escaped is the printer's policy (`printScalar`), unchanged: `"` `\` the controls below 0x20 (`\b \f \n \r \t` or `\u00xx`); every other byte, `/` and DEL included, goes through. -/
namespace LeanJson

/-- One byte of the UTF-8 of a string, as the printer writes it. A byte of a multi-byte sequence is at least 0x80: it passes through. (`printScalar`, byte by byte: `printChar_flatMap`, `LeanJsonProofs/PrintBytes.lean`.) -/
def escByte (x : UInt8) : Bytes :=
  if x.toNat = 0x22 then [0x5C, 0x22] else if x.toNat = 0x5C then [0x5C, 0x5C]
  else if 0x20 ≤ x.toNat then [x]
  else if x.toNat = 0x08 then [0x5C, 0x62] else if x.toNat = 0x0C then [0x5C, 0x66] else if x.toNat = 0x0A then [0x5C, 0x6E]
  else if x.toNat = 0x0D then [0x5C, 0x72] else if x.toNat = 0x09 then [0x5C, 0x74]
  else [0x5C, 0x75, 0x30, 0x30, hexDigit (x.toNat / 16), hexDigit (x.toNat % 16)]

/-- `escByte x` appended to `b`: straight into the buffer (`pushEsc_eq`). -/
@[inline] def pushEsc (b : ByteArray) (x : UInt8) : ByteArray :=
  if x.toNat = 0x22 then (b.push 0x5C).push 0x22 else if x.toNat = 0x5C then (b.push 0x5C).push 0x5C
  else if 0x20 ≤ x.toNat then b.push x
  else if x.toNat = 0x08 then (b.push 0x5C).push 0x62 else if x.toNat = 0x0C then (b.push 0x5C).push 0x66 else if x.toNat = 0x0A then (b.push 0x5C).push 0x6E
  else if x.toNat = 0x0D then (b.push 0x5C).push 0x72 else if x.toNat = 0x09 then (b.push 0x5C).push 0x74
  else (((((b.push 0x5C).push 0x75).push 0x30).push 0x30).push (hexDigit (x.toNat / 16))).push (hexDigit (x.toNat % 16))

/-- The bytes `a[i:]`, escaped, appended to `b`. -/
def escLoop (a : ByteArray) (i : Nat) (b : ByteArray) : ByteArray :=
  if h : i < a.size then escLoop a (i + 1) (pushEsc b a[i]) else b
termination_by a.size - i

/-- The bytes of `s` from `i`, escaped, appended to `b`: the bytes are read in place (`String.getUTF8Byte`), the string is not copied. -/
def escLoopS (s : String) (i : Nat) (b : ByteArray) : ByteArray :=
  if h : i < s.utf8ByteSize then escLoopS s (i + 1) (pushEsc b (s.getUTF8Byte ⟨i⟩ (by simpa [String.Pos.Raw.lt_iff] using h))) else b
termination_by s.utf8ByteSize - i

/-- The string literal of the UTF-8 text `a`: a quote, the escaped bytes, a quote. The buffer has room for the text and the two quotes at the start (an escape grows it). -/
def escapeString (a : ByteArray) : ByteArray :=
  (escLoop a 0 ((ByteArray.emptyWithCapacity (a.size + 2)).push 0x22)).push 0x22

/-- The string literal of `s`, appended to `b`. -/
@[inline] def pushString (b : ByteArray) (s : String) : ByteArray := (escLoopS s 0 (b.push 0x22)).push 0x22

mutual
/-- `print v` appended to `b`. -/
def pushVal (b : ByteArray) : Value → ByteArray
  | .null => (((b.push 0x6E).push 0x75).push 0x6C).push 0x6C
  | .bool true => (((b.push 0x74).push 0x72).push 0x75).push 0x65
  | .bool false => ((((b.push 0x66).push 0x61).push 0x6C).push 0x73).push 0x65
  | .num n => pushNumber b n
  | .str s => pushString b s
  | .arr xs => (pushElems (b.push 0x5B) xs).push 0x5D
  | .obj ms => (pushMembers (b.push 0x7B) ms).push 0x7D

def pushElems (b : ByteArray) : List Value → ByteArray
  | [] => b
  | [v] => pushVal b v
  | v :: vs => pushElems ((pushVal b v).push 0x2C) vs

def pushMembers (b : ByteArray) : List (String × Value) → ByteArray
  | [] => b
  | [(k, v)] => pushVal ((pushString b k).push 0x3A) v
  | (k, v) :: ms => pushMembers ((pushVal ((pushString b k).push 0x3A) v).push 0x2C) ms
end

/-- The compact form of `v`, as bytes. -/
def printBytes (v : Value) : ByteArray := pushVal (ByteArray.emptyWithCapacity 256) v

end LeanJson
