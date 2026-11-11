import LeanJson.Value
/-! # `LeanJson.Grammar`: RFC 8259 as an inductive relation over bytes

`Json bs v` says the byte string `bs` is a JSON-text (RFC 8259 section 2) and denotes `v`. Each production of the ABNF is a relation; a constructor is one
alternative, its premises are the parts, and the concatenation in its conclusion is the ABNF sequence. Where RFC 8259 places `ws` inside `begin-array`, `end-array`,
`name-separator` and `value-separator`, adjacent `ws` are merged (`ws ws` derives the same language as `ws`), so each constructor names the `ws` it needs once.
The strict-text policy (`Policy.lean`) is part of the relation: there is no derivation for a lone surrogate escape or for invalid UTF-8 (RFC 3629 table), because
no `String` value denotes them. The relation is stated here and checked against the RFC by review (ledger slug `grammar-is-rfc8259`: a prose standard has no machine check);
`Reference.lean` is the executable reading of it and the theorems in `LeanJsonProofs` tie the two. Nothing in this file is run. -/
namespace LeanJson

/-! ## Byte classes (the terminals) -/

/-- `ws = *( %x20 / %x09 / %x0A / %x0D )`: one whitespace byte. -/
@[inline] def isWs (b : UInt8) : Bool := b == 0x20 || b == 0x09 || b == 0x0A || b == 0x0D

/-- `DIGIT`: the digit a byte denotes. -/
@[inline] def digitVal (b : UInt8) : Option Digit :=
  if h : 0x30 ≤ b.toNat ∧ b.toNat ≤ 0x39 then some ⟨b.toNat - 0x30, by omega⟩ else none

/-- `digit1-9`: the digit minus one. -/
@[inline] def digit19 (b : UInt8) : Option (Fin 9) :=
  if h : 0x31 ≤ b.toNat ∧ b.toNat ≤ 0x39 then some ⟨b.toNat - 0x31, by omega⟩ else none

/-- `HEXDIG` (RFC 5234: upper or lower case). -/
@[inline] def hexVal (b : UInt8) : Option Nat :=
  if 0x30 ≤ b.toNat ∧ b.toNat ≤ 0x39 then some (b.toNat - 0x30)
  else if 0x41 ≤ b.toNat ∧ b.toNat ≤ 0x46 then some (b.toNat - 0x41 + 10)
  else if 0x61 ≤ b.toNat ∧ b.toNat ≤ 0x66 then some (b.toNat - 0x61 + 10)
  else none

/-- The one-character escapes `\" \\ \/ \b \f \n \r \t`: the byte after the backslash and the scalar it stands for. -/
@[inline] def simpleEsc (b : UInt8) : Option Nat :=
  if b == 0x22 then some 0x22 else if b == 0x5C then some 0x5C else if b == 0x2F then some 0x2F
  else if b == 0x62 then some 0x08 else if b == 0x66 then some 0x0C else if b == 0x6E then some 0x0A
  else if b == 0x72 then some 0x0D else if b == 0x74 then some 0x09 else none

/-- `ws`. -/
inductive Ws : Bytes → Prop
  | nil : Ws []
  | cons {b : UInt8} {bs : Bytes} : isWs b = true → Ws bs → Ws (b :: bs)

/-- `*DIGIT`. -/
inductive Digits : Bytes → List Digit → Prop
  | nil : Digits [] []
  | cons {b : UInt8} {d : Digit} {bs : Bytes} {ds : List Digit} : digitVal b = some d → Digits bs ds → Digits (b :: bs) (d :: ds)

/-! ## Numbers: `number = [ minus ] int [ frac ] [ exp ]` -/

/-- `[ minus ]`. -/
inductive Minus : Bytes → Bool → Prop
  | none : Minus [] false
  | minus : Minus [0x2D] true

/-- `int = zero / ( digit1-9 *DIGIT )`. -/
inductive IntP : Bytes → IntPart → Prop
  | zero : IntP [0x30] .zero
  | nz {b : UInt8} {l : Fin 9} {ds : Bytes} {rest : List Digit} : digit19 b = some l → Digits ds rest → IntP (b :: ds) (.nz l rest)

/-- `[ frac ]`, `frac = decimal-point 1*DIGIT`. -/
inductive FracP : Bytes → Option (Digit × List Digit) → Prop
  | none : FracP [] none
  | some {b : UInt8} {d : Digit} {ds : Bytes} {rest : List Digit} : digitVal b = some d → Digits ds rest → FracP (0x2E :: b :: ds) (some (d, rest))

/-- `[ minus / plus ]` inside an exponent: negative or not. -/
inductive ESign : Bytes → Bool → Prop
  | none : ESign [] false
  | plus : ESign [0x2B] false
  | minus : ESign [0x2D] true

/-- `[ exp ]`, `exp = e [ minus / plus ] 1*DIGIT` (`e = %x65 / %x45`). -/
inductive ExpP : Bytes → Option (Bool × Digit × List Digit) → Prop
  | none : ExpP [] none
  | some {e : UInt8} {sg : Bytes} {neg : Bool} {b : UInt8} {d : Digit} {ds : Bytes} {rest : List Digit} :
      (e = 0x65 ∨ e = 0x45) → ESign sg neg → digitVal b = some d → Digits ds rest → ExpP (e :: (sg ++ b :: ds)) (some (neg, d, rest))

inductive Num : Bytes → Number → Prop
  | mk {m i f e : Bytes} {neg : Bool} {ip : IntPart} {fr : Option (Digit × List Digit)} {ex : Option (Bool × Digit × List Digit)} :
      Minus m neg → IntP i ip → FracP f fr → ExpP e ex → Num (m ++ i ++ f ++ e) ⟨neg, ip, fr, ex⟩

/-! ## Strings: `string = quotation-mark *char quotation-mark` -/

/-- `UTF8-tail = %x80-BF`. -/
def Tail (b : UInt8) : Prop := 0x80 ≤ b.toNat ∧ b.toNat ≤ 0xBF
instance : DecidablePred Tail := fun b => inferInstanceAs (Decidable (0x80 ≤ b.toNat ∧ b.toNat ≤ 0xBF))

/-- The second byte of `UTF8-3` (RFC 3629): `E0` needs `A0-BF`, `ED` needs `80-9F` (no surrogates), else a tail byte. -/
def Second3 (a b : UInt8) : Prop := Tail b ∧ (a.toNat = 0xE0 → 0xA0 ≤ b.toNat) ∧ (a.toNat = 0xED → b.toNat ≤ 0x9F)
instance : DecidableRel Second3 := fun a b => inferInstanceAs (Decidable (Tail b ∧ (a.toNat = 0xE0 → 0xA0 ≤ b.toNat) ∧ (a.toNat = 0xED → b.toNat ≤ 0x9F)))

/-- The second byte of `UTF8-4`: `F0` needs `90-BF`, `F4` needs `80-8F` (nothing past U+10FFFF), else a tail byte. -/
def Second4 (a b : UInt8) : Prop := Tail b ∧ (a.toNat = 0xF0 → 0x90 ≤ b.toNat) ∧ (a.toNat = 0xF4 → b.toNat ≤ 0x8F)
instance : DecidableRel Second4 := fun a b => inferInstanceAs (Decidable (Tail b ∧ (a.toNat = 0xF0 → 0x90 ≤ b.toNat) ∧ (a.toNat = 0xF4 → b.toNat ≤ 0x8F)))

/-- `UTF8-char` (RFC 3629): the well-formed encodings of one Unicode scalar value, the scalar as a number. Overlong forms, surrogates and values past U+10FFFF have none. -/
inductive Utf8 : Bytes → Nat → Prop
  | u1 {a : UInt8} : a.toNat < 0x80 → Utf8 [a] a.toNat
  | u2 {a b : UInt8} : 0xC2 ≤ a.toNat → a.toNat ≤ 0xDF → Tail b → Utf8 [a, b] ((a.toNat - 0xC0) * 64 + (b.toNat - 0x80))
  | u3 {a b c : UInt8} : 0xE0 ≤ a.toNat → a.toNat ≤ 0xEF → Second3 a b → Tail c →
      Utf8 [a, b, c] ((a.toNat - 0xE0) * 4096 + (b.toNat - 0x80) * 64 + (c.toNat - 0x80))
  | u4 {a b c d : UInt8} : 0xF0 ≤ a.toNat → a.toNat ≤ 0xF4 → Second4 a b → Tail c → Tail d →
      Utf8 [a, b, c, d] ((a.toNat - 0xF0) * 262144 + (b.toNat - 0x80) * 4096 + (c.toNat - 0x80) * 64 + (d.toNat - 0x80))

/-- `4HEXDIG`, the number it spells. -/
inductive Hex4 : Bytes → Nat → Prop
  | mk {a b c d : UInt8} {w x y z : Nat} : hexVal a = some w → hexVal b = some x → hexVal c = some y → hexVal d = some z →
      Hex4 [a, b, c, d] (w * 4096 + x * 256 + y * 16 + z)

/-- `escape ( ... )`: the scalar an escape stands for. A `\uXXXX` that is a surrogate has no derivation alone; a high surrogate followed by a low one is the pair (RFC 8259 section 7). -/
inductive Esc : Bytes → Nat → Prop
  | simple {b : UInt8} {n : Nat} : simpleEsc b = some n → Esc [0x5C, b] n
  | uni {h : Bytes} {n : Nat} : Hex4 h n → (n < 0xD800 ∨ 0xE000 ≤ n) → Esc (0x5C :: 0x75 :: h) n
  | pair {h₁ h₂ : Bytes} {hi lo : Nat} : Hex4 h₁ hi → Hex4 h₂ lo → 0xD800 ≤ hi → hi < 0xDC00 → 0xDC00 ≤ lo → lo < 0xE000 →
      Esc (0x5C :: 0x75 :: (h₁ ++ 0x5C :: 0x75 :: h₂)) (0x10000 + (hi - 0xD800) * 0x400 + (lo - 0xDC00))

/-- `char = unescaped / escape (...)`, `unescaped = %x20-21 / %x23-5B / %x5D-10FFFF` read as UTF-8: the scalar. -/
inductive StrChar : Bytes → Nat → Prop
  | plain {bs : Bytes} {n : Nat} : Utf8 bs n → 0x20 ≤ n → n ≠ 0x22 → n ≠ 0x5C → StrChar bs n
  | esc {bs : Bytes} {n : Nat} : Esc bs n → StrChar bs n

/-- `*char`. -/
inductive Chars : Bytes → List Nat → Prop
  | nil : Chars [] []
  | cons {b bs : Bytes} {n : Nat} {ns : List Nat} : StrChar b n → Chars bs ns → Chars (b ++ bs) (n :: ns)

inductive Str : Bytes → String → Prop
  | mk {cs : Bytes} {ns : List Nat} : Chars cs ns → Str (0x22 :: (cs ++ [0x22])) (String.ofList (ns.map Char.ofNat))

/-! ## Values, arrays, objects -/

mutual
/-- `value = false / null / true / object / array / number / string`. -/
inductive Val : Bytes → Value → Prop
  | null : Val [0x6E, 0x75, 0x6C, 0x6C] .null
  | true : Val [0x74, 0x72, 0x75, 0x65] (.bool true)
  | false : Val [0x66, 0x61, 0x6C, 0x73, 0x65] (.bool false)
  | num {bs : Bytes} {n : Number} : Num bs n → Val bs (.num n)
  | str {bs : Bytes} {s : String} : Str bs s → Val bs (.str s)
  /-- `begin-array end-array`. -/
  | arr0 {w : Bytes} : Ws w → Val (0x5B :: (w ++ [0x5D])) (.arr [])
  /-- `begin-array value *( value-separator value ) end-array`. -/
  | arr {w₁ es w₂ : Bytes} {vs : List Value} : Ws w₁ → Elems es vs → Ws w₂ → Val (0x5B :: (w₁ ++ es ++ w₂ ++ [0x5D])) (.arr vs)
  | obj0 {w : Bytes} : Ws w → Val (0x7B :: (w ++ [0x7D])) (.obj [])
  /-- `begin-object member *( value-separator member ) end-object`. -/
  | obj {w₁ ms w₂ : Bytes} {kvs : List (String × Value)} : Ws w₁ → Members ms kvs → Ws w₂ → Val (0x7B :: (w₁ ++ ms ++ w₂ ++ [0x7D])) (.obj kvs)

/-- `value *( value-separator value )`, `value-separator = ws %x2C ws`. -/
inductive Elems : Bytes → List Value → Prop
  | one {b : Bytes} {v : Value} : Val b v → Elems b [v]
  | cons {b w₁ w₂ es : Bytes} {v : Value} {vs : List Value} : Val b v → Ws w₁ → Ws w₂ → Elems es vs → Elems (b ++ w₁ ++ 0x2C :: (w₂ ++ es)) (v :: vs)

/-- `member *( value-separator member )`. -/
inductive Members : Bytes → List (String × Value) → Prop
  | one {b : Bytes} {kv : String × Value} : Member b kv → Members b [kv]
  | cons {b w₁ w₂ ms : Bytes} {kv : String × Value} {kvs : List (String × Value)} :
      Member b kv → Ws w₁ → Ws w₂ → Members ms kvs → Members (b ++ w₁ ++ 0x2C :: (w₂ ++ ms)) (kv :: kvs)

/-- `member = string name-separator value`, `name-separator = ws %x3A ws`. -/
inductive Member : Bytes → String × Value → Prop
  | mk {k w₁ w₂ b : Bytes} {s : String} {v : Value} : Str k s → Ws w₁ → Ws w₂ → Val b v → Member (k ++ w₁ ++ 0x3A :: (w₂ ++ b)) (s, v)
end

/-- `JSON-text = ws value ws`. -/
inductive Json : Bytes → Value → Prop
  | mk {w₁ b w₂ : Bytes} {v : Value} : Ws w₁ → Val b v → Ws w₂ → Json (w₁ ++ b ++ w₂) v

end LeanJson
