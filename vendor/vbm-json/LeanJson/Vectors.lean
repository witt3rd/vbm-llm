import LeanJson.Print
import LeanJson.Reference
/-! # `LeanJson.Vectors`: the shared test vectors, `vbm-json-vectors-1`

Every row is computed by the REFERENCE (`parse`) and the printer, and by nothing else: the fast parser, the C artifact and every binding are checked against these rows, never the
other way round. A row is one JSON object per line: `set`, `id`, `input` (hex of the bytes), `verdict` (`ok` or `err`), then `canonical` (hex of `print v`) for `ok` or `code` (the
`Error` name) for `err`. Sets: `enum` (every byte string up to a length over a 12-byte alphabet), `number`, `escape`, `utf8`, `depth`, `misc`. Pure functions only (`Init`);
the executable `vectors/Main.lean` writes the files. -/
namespace LeanJson

structure Row where
  set : String
  input : Bytes
  result : Except Error Bytes

/-- The reference's verdict on `input`, with the canonical form when it is accepted. -/
def Row.make (set : String) (input : Bytes) : Row :=
  { set, input, result := match parse input with | .ok v => .ok (print v) | .error e => .error e }

def hexNibble (k : Nat) : Char := if k < 10 then Char.ofNat (0x30 + k) else Char.ofNat (0x61 + (k - 10))

def hex (bs : Bytes) : String := String.ofList (bs.flatMap fun b => [hexNibble (b.toNat / 16), hexNibble (b.toNat % 16)])

def Row.json (r : Row) (id : Nat) : String :=
  let head := "{\"set\":\"" ++ r.set ++ "\",\"id\":" ++ toString id ++ ",\"input\":\"" ++ hex r.input ++ "\","
  match r.result with
  | .ok c => head ++ "\"verdict\":\"ok\",\"canonical\":\"" ++ hex c ++ "\"}"
  | .error e => head ++ "\"verdict\":\"err\",\"code\":\"" ++ e.name ++ "\"}"

/-- A row is consistent when the reference reproduces it, and an accepted row's canonical form is a fixed point of parse then print. -/
def Row.check (r : Row) : Bool :=
  match r.result, parse r.input with
  | .ok c, .ok v => print v == c && (match parse c with | .ok v' => print v' == c | .error _ => false)
  | .error e, .error e' => e == e'
  | _, _ => false

/-- All byte strings of exactly length `k` over the alphabet, in lexicographic order of the alphabet. -/
def exactly (alpha : List UInt8) : Nat → List Bytes
  | 0 => [[]]
  | k + 1 => alpha.flatMap fun a => (exactly alpha k).map (a :: ·)

/-- Every byte string of length at most `n`. -/
def enumAll (alpha : List UInt8) (n : Nat) : List Bytes := (List.range (n + 1)).flatMap (exactly alpha)

/-- The 12-byte alphabet of the exhaustive set: `[ ] { } , : "` space `0 1 - .` and `e`... chosen so that arrays, objects, strings, numbers with sign, fraction and exponent are all reachable. -/
def enumAlphabet : List UInt8 := [0x5B, 0x5D, 0x7B, 0x7D, 0x2C, 0x3A, 0x22, 0x20, 0x30, 0x31, 0x2D, 0x2E]

def bytesOf (s : String) : Bytes := s.toUTF8.toList

def quoted (inner : Bytes) : Bytes := 0x22 :: (inner ++ [0x22])

/-- Numbers: every string of length at most 5 over `0 1 - + . e E`. -/
def numberSet : List Bytes := enumAll [0x30, 0x31, 0x2D, 0x2B, 0x2E, 0x65, 0x45] 5

/-- Escapes: every `\X` for every byte `X`; `\uXXXX` and pairs of them at the surrogate and range boundaries; upper and lower case hex; truncations. -/
def escapeSet : List Bytes :=
  let simple := (List.range 256).map fun x => quoted [0x5C, UInt8.ofNat x]
  let us := ["0000", "001f", "0020", "d7ff", "D800", "dbff", "DBFF", "dc00", "DFFF", "e000", "ffff", "FFFF", "12", "12g4", "00e9"]
  let one := us.map fun h => quoted (bytesOf ("\\u" ++ h))
  let pairs := us.flatMap fun a => us.map fun b => quoted (bytesOf ("\\u" ++ a ++ "\\u" ++ b))
  let tail := [quoted [0x5C], quoted (bytesOf "\\u"), quoted (bytesOf "\\ud83d"), [0x22, 0x5C], bytesOf "\"\\ud83d\\ude00\"", bytesOf "\"\\uD83D\\uDE00x\""]
  simple ++ one ++ pairs ++ tail

/-- UTF-8: the boundary encodings of RFC 3629 (valid, overlong, surrogate, too large, truncated, stray continuation), and every raw byte inside a string. -/
def utf8Set : List Bytes :=
  let seqs : List Bytes := [[0x7F], [0xC2, 0x80], [0xDF, 0xBF], [0xC0, 0x80], [0xC1, 0xBF], [0xE0, 0x9F, 0xBF], [0xE0, 0xA0, 0x80], [0xED, 0x9F, 0xBF],
    [0xED, 0xA0, 0x80], [0xED, 0xBF, 0xBF], [0xEE, 0x80, 0x80], [0xEF, 0xBF, 0xBF], [0xF0, 0x8F, 0xBF, 0xBF], [0xF0, 0x90, 0x80, 0x80], [0xF4, 0x8F, 0xBF, 0xBF],
    [0xF4, 0x90, 0x80, 0x80], [0xF5, 0x80, 0x80, 0x80], [0xC2], [0xE0, 0xA0], [0xF0, 0x90, 0x80], [0x80], [0xBF], [0xFE], [0xFF], [0xC2, 0x41], [0xE2, 0x82], [0xE2, 0x82, 0xAC, 0xAC]]
  (seqs.map quoted) ++ ((List.range 256).map fun x => quoted [UInt8.ofNat x]) ++ seqs

/-- Depth: arrays, objects and a mix nested to just under, at and just over `maxDepth`, closed and not, with trailing bytes, and 100000 deep (arrays and objects closed, arrays not closed: the stack-safety rows, `depth` from a bounded loop). -/
def depthSet : List Bytes :=
  let arr (k : Nat) : Bytes := List.replicate k 0x5B ++ List.replicate k 0x5D
  let obj (k : Nat) : Bytes := (List.replicate k (bytesOf "{\"a\":")).flatten ++ [0x30] ++ List.replicate k 0x7D
  let ks := [0, 1, 2, maxDepth - 1, maxDepth, maxDepth + 1, maxDepth + 2, 2 * maxDepth]
  ks.map arr ++ ks.map obj ++ [List.replicate (maxDepth + 1) 0x5B, List.replicate maxDepth 0x5B, arr maxDepth ++ [0x2C], arr (maxDepth + 1) ++ [0x78], List.replicate 600 0x5B ++ [0x78],
    arr 100000, obj 100000, List.replicate 100000 0x5B]

/-- Hand-picked texts: the literals, whitespace, trailing data, the classics. -/
def miscSet : List Bytes := (["", " ", "null", "true", "false", "nul", "nulll", "truE", " null ", "\tnull\n", "\r\n[ ]\r\n", "[]", "{}", "[1,2,3]", "[1,]", "[,1]", "[1 2]", "{\"a\":1}",
    "{\"a\":1,}", "{\"a\"}", "{\"a\":}", "{1:2}", "{\"a\":1,\"a\":2}", "[[],{}]", "\"\"", "\"a\"", "\"a", "a\"", "1 2", "[1]x", "\u00a0null", "\x00", "-", "-0", "0", "00", "1e5", "1E+5", "1.5e-3",
    "[true,false,null]", "{\"k\":[{\"k\":[]}]}", "[\"\\u00e9\",\"\u00e9\"]", "\"\\/\\b\\f\\n\\r\\t\"", " [ 1 , { \"a\" : \"b\" } ] "].map bytesOf)

/-- Every set, in order. -/
def allRows (enumN : Nat) : List Row :=
  (enumAll enumAlphabet enumN).map (Row.make "enum") ++ numberSet.map (Row.make "number") ++ escapeSet.map (Row.make "escape") ++
  utf8Set.map (Row.make "utf8") ++ depthSet.map (Row.make "depth") ++ miscSet.map (Row.make "misc")

/-- FNV-1a, 64 bits, over the bytes of the rows file (the manifest's hash). -/
def fnv1a (bs : ByteArray) : UInt64 := bs.foldl (fun h b => (h ^^^ b.toUInt64) * 0x100000001b3) 0xcbf29ce484222325

def hex64 (h : UInt64) : String := hex ((List.range 8).reverse.map fun i => (h >>> (UInt64.ofNat (8 * i))).toUInt8)

end LeanJson
