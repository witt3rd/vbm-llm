import LeanJson.Value
/-! # `LeanJson.Print`: the printer

The compact form: no whitespace, `e` for the exponent with no `+`, strings escaped minimally (`\"`, `\\`, `\b \f \n \r \t`, other controls as lowercase `\u00xx`, everything else as UTF-8;
`/` and DEL are not escaped). Specified in the same terms as the grammar: `LeanJsonProofs/Print.lean` proves its output is derivable and that the reference reads it back. The byte-equality of this
form with `Lean.Json.compress` (policy `print-reproduces-lean-compress`) is a one-time differential run, not a theorem. -/
namespace LeanJson

def digitByte (d : Digit) : UInt8 := UInt8.ofNat (0x30 + d.val)

def printMinus (neg : Bool) : Bytes := if neg then [0x2D] else []

def printInt : IntPart → Bytes
  | .zero => [0x30]
  | .nz l rest => UInt8.ofNat (0x31 + l.val) :: rest.map digitByte

def printFrac : Option (Digit × List Digit) → Bytes
  | none => []
  | some (d, ds) => 0x2E :: digitByte d :: ds.map digitByte

def printExp : Option (Bool × Digit × List Digit) → Bytes
  | none => []
  | some (neg, d, ds) => 0x65 :: (printMinus neg ++ digitByte d :: ds.map digitByte)

def printNumber (n : Number) : Bytes := printMinus n.neg ++ printInt n.int ++ printFrac n.frac ++ printExp n.exp

/-- The UTF-8 encoding of a scalar value. -/
def encodeUtf8 (n : Nat) : Bytes :=
  if n < 0x80 then [UInt8.ofNat n]
  else if n < 0x800 then [UInt8.ofNat (0xC0 + n / 64), UInt8.ofNat (0x80 + n % 64)]
  else if n < 0x10000 then [UInt8.ofNat (0xE0 + n / 4096), UInt8.ofNat (0x80 + n / 64 % 64), UInt8.ofNat (0x80 + n % 64)]
  else [UInt8.ofNat (0xF0 + n / 262144), UInt8.ofNat (0x80 + n / 4096 % 64), UInt8.ofNat (0x80 + n / 64 % 64), UInt8.ofNat (0x80 + n % 64)]

/-- A lowercase hexadecimal digit (`k < 16`). -/
def hexDigit (k : Nat) : UInt8 := if k < 10 then UInt8.ofNat (0x30 + k) else UInt8.ofNat (0x61 + (k - 10))

/-- One scalar value inside a string. -/
def printScalar (n : Nat) : Bytes :=
  if n = 0x22 then [0x5C, 0x22] else if n = 0x5C then [0x5C, 0x5C]
  else if n = 0x08 then [0x5C, 0x62] else if n = 0x0C then [0x5C, 0x66] else if n = 0x0A then [0x5C, 0x6E]
  else if n = 0x0D then [0x5C, 0x72] else if n = 0x09 then [0x5C, 0x74]
  else if n < 0x20 then [0x5C, 0x75, 0x30, 0x30, hexDigit (n / 16), hexDigit (n % 16)]
  else encodeUtf8 n

def printChar (c : Char) : Bytes := printScalar c.toNat

def printString (s : String) : Bytes := 0x22 :: (s.toList.flatMap printChar ++ [0x22])

mutual
def print : Value → Bytes
  | .null => [0x6E, 0x75, 0x6C, 0x6C]
  | .bool true => [0x74, 0x72, 0x75, 0x65]
  | .bool false => [0x66, 0x61, 0x6C, 0x73, 0x65]
  | .num n => printNumber n
  | .str s => printString s
  | .arr xs => 0x5B :: (printElems xs ++ [0x5D])
  | .obj ms => 0x7B :: (printMembers ms ++ [0x7D])

def printElems : List Value → Bytes
  | [] => []
  | [v] => print v
  | v :: vs => print v ++ 0x2C :: printElems vs

def printMembers : List (String × Value) → Bytes
  | [] => []
  | [(k, v)] => printString k ++ 0x3A :: print v
  | (k, v) :: ms => printString k ++ 0x3A :: print v ++ 0x2C :: printMembers ms
end

end LeanJson
