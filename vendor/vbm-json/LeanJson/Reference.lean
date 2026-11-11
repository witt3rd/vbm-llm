import LeanJson.Grammar
import LeanJson.Policy
/-! # `LeanJson.Reference`: the slow reference parser, read straight off the grammar

One function per nonterminal of `Grammar.lean`, in the same order, each deterministic: the next byte decides the alternative. It is a specification of the
verdict, not the code that ships: it is slow (lists), recursive, and total by **fuel** (every nested call spends one unit; `parse` starts with enough) and by a **depth budget**
(each array or object spends one; at zero the verdict is `Error.depth`, reported as soon as it is seen, before any later syntax error). `LeanJsonProofs/Reference.lean`
proves it sound and complete against the relation. Vectors are generated from `parse` and from nothing else. -/
namespace LeanJson

/-- `ws`: drop leading whitespace. -/
def skipWs : Bytes → Bytes
  | [] => []
  | b :: bs => if isWs b then skipWs bs else b :: bs

/-- `*DIGIT`: the longest run of digits and what follows it. -/
def digits : Bytes → List Digit × Bytes
  | [] => ([], [])
  | b :: bs => match digitVal b with
    | some d => ((d :: (digits bs).1), (digits bs).2)
    | none => ([], b :: bs)

/-- `1*DIGIT`. -/
def digits1 (bs : Bytes) : Option ((Digit × List Digit) × Bytes) :=
  match bs with
  | b :: r => match digitVal b with
    | some d => some ((d, (digits r).1), (digits r).2)
    | none => none
  | [] => none

/-- `[ minus ]`. -/
def parseMinus : Bytes → Bool × Bytes
  | [] => (false, [])
  | b :: r => if b == 0x2D then (true, r) else (false, b :: r)

/-- `int = zero / ( digit1-9 *DIGIT )`. -/
def parseInt : Bytes → Option (IntPart × Bytes)
  | [] => none
  | b :: r =>
    if b == 0x30 then some (.zero, r)
    else match digit19 b with
      | some l => some (.nz l (digits r).1, (digits r).2)
      | none => none

/-- `[ frac ]`: a dot is always followed by at least one digit. -/
def parseFrac : Bytes → Option (Option (Digit × List Digit) × Bytes)
  | [] => some (none, [])
  | b :: r =>
    if b == 0x2E then (match digits1 r with | some (f, r') => some (some f, r') | none => none)
    else some (none, b :: r)

/-- the optional sign of an exponent: negative or not. -/
def parseESign : Bytes → Bool × Bytes
  | [] => (false, [])
  | c :: r => if c == 0x2B then (false, r) else if c == 0x2D then (true, r) else (false, c :: r)

/-- the optional sign of an exponent, then `1*DIGIT`. -/
def parseExpBody (r : Bytes) : Option (Option (Bool × Digit × List Digit) × Bytes) :=
  let sg := parseESign r
  match digits1 sg.2 with
  | some ((d, ds), r') => some (some (sg.1, d, ds), r')
  | none => none

/-- `[ exp ]`. -/
def parseExp : Bytes → Option (Option (Bool × Digit × List Digit) × Bytes)
  | [] => some (none, [])
  | e :: r => if e == 0x65 || e == 0x45 then parseExpBody r else some (none, e :: r)

/-- `number = [ minus ] int [ frac ] [ exp ]`. -/
def parseNum (bs : Bytes) : Option (Number × Bytes) :=
  let m := parseMinus bs
  match parseInt m.2 with
  | none => none
  | some (ip, r1) => match parseFrac r1 with
    | none => none
    | some (fr, r2) => match parseExp r2 with
      | none => none
      | some (ex, r3) => some (⟨m.1, ip, fr, ex⟩, r3)

/-- `UTF8-char` (RFC 3629): the scalar and what follows it. -/
def decodeUtf8 : Bytes → Option (Nat × Bytes)
  | [] => none
  | a :: r =>
    if a.toNat < 0x80 then some (a.toNat, r)
    else if 0xC2 ≤ a.toNat ∧ a.toNat ≤ 0xDF then
      match r with
      | b :: r' => if Tail b then some ((a.toNat - 0xC0) * 64 + (b.toNat - 0x80), r') else none
      | _ => none
    else if 0xE0 ≤ a.toNat ∧ a.toNat ≤ 0xEF then
      match r with
      | b :: c :: r' => if Second3 a b ∧ Tail c then some ((a.toNat - 0xE0) * 4096 + (b.toNat - 0x80) * 64 + (c.toNat - 0x80), r') else none
      | _ => none
    else if 0xF0 ≤ a.toNat ∧ a.toNat ≤ 0xF4 then
      match r with
      | b :: c :: d :: r' =>
        if Second4 a b ∧ Tail c ∧ Tail d then some ((a.toNat - 0xF0) * 262144 + (b.toNat - 0x80) * 4096 + (c.toNat - 0x80) * 64 + (d.toNat - 0x80), r') else none
      | _ => none
    else none

/-- `4HEXDIG`. -/
@[inline] def hex4 (a b c d : UInt8) : Option Nat :=
  match hexVal a, hexVal b, hexVal c, hexVal d with
  | some w, some x, some y, some z => some (w * 4096 + x * 256 + y * 16 + z)
  | _, _, _, _ => none

/-- The part of a `\\uXXXX` escape after the `\\u`: a scalar, or the pair of a high and a low surrogate escape. -/
def decodeU : Bytes → Option (Nat × Bytes)
  | a :: b :: c :: d :: r =>
    match hex4 a b c d with
    | none => none
    | some n =>
      if n < 0xD800 ∨ 0xE000 ≤ n then some (n, r)
      else if n < 0xDC00 then
        match r with
        | e :: f :: a' :: b' :: c' :: d' :: r' =>
          if e == 0x5C && f == 0x75 then
            match hex4 a' b' c' d' with
            | some lo => if 0xDC00 ≤ lo ∧ lo < 0xE000 then some (0x10000 + (n - 0xD800) * 0x400 + (lo - 0xDC00), r') else none
            | none => none
          else none
        | _ => none
      else none
  | _ => none

/-- `escape (...)`: what follows the backslash. -/
def decodeEsc : Bytes → Option (Nat × Bytes)
  | [] => none
  | b :: r => if b == 0x75 then decodeU r else match simpleEsc b with | some n => some (n, r) | none => none

/-- `char`: one unescaped character or escape, as a scalar, and what follows it. -/
def decodeChar : Bytes → Option (Nat × Bytes)
  | [] => none
  | a :: r =>
    if a == 0x5C then decodeEsc r
    else match decodeUtf8 (a :: r) with
      | some (n, r') => if 0x20 ≤ n ∧ n ≠ 0x22 ∧ n ≠ 0x5C then some (n, r') else none
      | none => none

/-- `*char quotation-mark`: the closing quote is consumed. Fuel: one unit per character. -/
def parseChars : Nat → Bytes → Option (List Nat × Bytes)
  | 0, _ => none
  | _, [] => none
  | n + 1, a :: r =>
    if a == 0x22 then some ([], r)
    else match decodeChar (a :: r) with
      | some (c, r') => match parseChars n r' with
        | some (cs, r'') => some (c :: cs, r'')
        | none => none
      | none => none

/-- `string`. -/
def parseStr : Bytes → Option (String × Bytes)
  | [] => none
  | a :: r =>
    if a == 0x22 then
      match parseChars (r.length + 1) r with
      | some (ns, r') => some (String.ofList (ns.map Char.ofNat), r')
      | none => none
    else none

/-- `string` then `name-separator`'s colon: the key and what follows the colon (leading whitespace not yet skipped). -/
def parseKey (bs : Bytes) : Option (String × Bytes) :=
  match parseStr bs with
  | some (s, r) => match skipWs r with
    | c :: r' => if c == 0x3A then some (s, r') else none
    | [] => none
  | none => none

/-- A literal: strip `l` from the front. -/
def lit : Bytes → Bytes → Option Bytes
  | [], r => some r
  | x :: xs, y :: ys => if x == y then lit xs ys else none
  | _ :: _, [] => none

mutual
/-- `value`. `d` is the nesting budget left, `n` the fuel. Returns the value and the unread rest. -/
def parseVal : Nat → Nat → Bytes → Except Error (Value × Bytes)
  | _, 0, _ => .error .syntax
  | _, _ + 1, [] => .error .syntax
  | d, n + 1, b :: r =>
    if b == 0x5B then
      match d with
      | 0 => .error .depth
      | d' + 1 => match skipWs r with
        | [] => .error .syntax
        | c :: r' =>
          if c == 0x5D then .ok (.arr [], r')
          else match parseElems d' n (c :: r') with
            | .error e => .error e
            | .ok (vs, r2) => match skipWs r2 with
              | c' :: r3 => if c' == 0x5D then .ok (.arr vs, r3) else .error .syntax
              | [] => .error .syntax
    else if b == 0x7B then
      match d with
      | 0 => .error .depth
      | d' + 1 => match skipWs r with
        | [] => .error .syntax
        | c :: r' =>
          if c == 0x7D then .ok (.obj [], r')
          else match parseMembers d' n (c :: r') with
            | .error e => .error e
            | .ok (kvs, r2) => match skipWs r2 with
              | c' :: r3 => if c' == 0x7D then .ok (.obj kvs, r3) else .error .syntax
              | [] => .error .syntax
    else if b == 0x22 then
      match parseStr (b :: r) with
      | some (s, r') => .ok (.str s, r')
      | none => .error .syntax
    else if b == 0x6E then
      match lit [0x75, 0x6C, 0x6C] r with | some r' => .ok (.null, r') | none => .error .syntax
    else if b == 0x74 then
      match lit [0x72, 0x75, 0x65] r with | some r' => .ok (.bool true, r') | none => .error .syntax
    else if b == 0x66 then
      match lit [0x61, 0x6C, 0x73, 0x65] r with | some r' => .ok (.bool false, r') | none => .error .syntax
    else
      match parseNum (b :: r) with
      | some (num, r') => .ok (.num num, r')
      | none => .error .syntax

/-- `value *( value-separator value )`. -/
def parseElems : Nat → Nat → Bytes → Except Error (List Value × Bytes)
  | _, 0, _ => .error .syntax
  | d, n + 1, bs =>
    match parseVal d n bs with
    | .error e => .error e
    | .ok (v, r) => match skipWs r with
      | [] => .ok ([v], r)
      | c :: r' =>
        if c == 0x2C then
          match parseElems d n (skipWs r') with
          | .error e => .error e
          | .ok (vs, r'') => .ok (v :: vs, r'')
        else .ok ([v], r)

/-- `member *( value-separator member )`. -/
def parseMembers : Nat → Nat → Bytes → Except Error (List (String × Value) × Bytes)
  | _, 0, _ => .error .syntax
  | d, n + 1, bs =>
    match parseKey bs with
    | none => .error .syntax
    | some (k, r0) => match parseVal d n (skipWs r0) with
      | .error e => .error e
      | .ok (v, r) => match skipWs r with
        | [] => .ok ([(k, v)], r)
        | c :: r' =>
          if c == 0x2C then
            match parseMembers d n (skipWs r') with
            | .error e => .error e
            | .ok (kvs, r'') => .ok ((k, v) :: kvs, r'')
          else .ok ([(k, v)], r)
end

/-- `JSON-text`: the verdict on a whole input. The fuel `2 * bs.length + 2` is enough for every derivable input (proved); it is also more than the bytes can spend, so fuel never decides which error is reported. -/
def parse (bs : Bytes) : Except Error Value :=
  match parseVal maxDepth (2 * bs.length + 2) (skipWs bs) with
  | .error e => .error e
  | .ok (v, r) => if (skipWs r).isEmpty then .ok v else .error .syntax

end LeanJson
