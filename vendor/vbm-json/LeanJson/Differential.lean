import LeanJson.Parse
import LeanJson.Vectors
import LeanJson.Tape
/-! # `LeanJson.Differential`: the fast parser against the reference, row by row

The check that stood alone before the refinement proof existed and stays as its executable cross-check (the proof is `LeanJsonProofs/Fast.lean`): for every input of the shared
vector sets (the exhaustive enumeration of every byte string up to a length over the 12-byte alphabet, and the number, escape, UTF-8, depth and hand-picked sets) the fast
parser must return exactly the reference's `Except Error Value`: the same verdict, the same error code, the same value. Not reachable from any export. -/
namespace LeanJson

/-- Same verdict, same error code, same value. -/
def sameResult : Except Error Value → Except Error Value → Bool
  | .ok v, .ok w => v == w
  | .error e, .error f => e == f
  | _, _ => false

def asArray (bs : Bytes) : ByteArray := ⟨bs.toArray⟩

/-- Does `f` agree with the reference on this input? -/
def agrees (f : ByteArray → Except Error Value) (bs : Bytes) : Bool := sameResult (f (asArray bs)) (parse bs)

/-- The rows on which `f` and the reference differ. -/
def disagreements (f : ByteArray → Except Error Value) (rows : List Row) : List Row := rows.filter fun r => !agrees f r.input

/-- A richer alphabet than the enumeration's: the structural bytes, escapes and hex digits, the literals' letters, ASCII controls, and the bytes of valid and invalid UTF-8. -/
def fuzzAlphabet : Array UInt8 :=
  "[]{},:\" \\/0129-+.eEtrufalsnbdDABx".toUTF8.data ++ #[0x00, 0x1F, 0x20, 0x09, 0x0A, 0xC3, 0xA9, 0xE2, 0x82, 0xAC, 0xED, 0xA0, 0xF0, 0x9F, 0x98, 0x80, 0xBF, 0xC0, 0xF4, 0x90, 0xFF]

/-- Pseudo-random inputs (a fixed linear congruential generator, so a failure is reproducible): `count` strings of length at most `maxLen` over `fuzzAlphabet`. -/
def fuzzInputs (seed count maxLen : Nat) : List Bytes := Id.run do
  let mut st := seed
  let mut out : List Bytes := []
  for _ in [0:count] do
    st := (st * 6364136223846793005 + 1442695040888963407) % 18446744073709551616
    let len := (st / 65536) % (maxLen + 1)
    let mut bs : Bytes := []
    for _ in [0:len] do
      st := (st * 6364136223846793005 + 1442695040888963407) % 18446744073709551616
      bs := fuzzAlphabet[(st / 65536) % fuzzAlphabet.size]! :: bs
    out := bs :: out
  return out

/-- Valid documents to mutate: the accepted hand-picked texts, an object of every value kind, a string with every escape and a multi-byte character, and arrays and objects at the depth limit. -/
def mutationSeeds : List Bytes :=
  (miscSet.filter fun b => match parse b with | .ok _ => true | _ => false) ++
  [bytesOf "{\"a\":[1,-2.5e+3,true,false,null,\"s\\u00e9\\ud83d\\ude00\\n\"],\"b\":{\"c\":[]},\"d\":{}} ", bytesOf " [ [ [ 0 ] , { \"k\" : [ ] } ] ] ",
   (List.replicate (maxDepth - 1) 0x5B) ++ [0x30] ++ List.replicate (maxDepth - 1) 0x5D, List.replicate (maxDepth + 1) 0x5B ++ List.replicate (maxDepth + 1) 0x5D]

/-- `count` pseudo-random texts, each a seed document with one to three edits (a byte replaced, deleted, inserted or a stretch duplicated). -/
def fuzzMutated (seed count : Nat) : List Bytes := Id.run do
  let mut st := seed
  let mut out : List Bytes := []
  let seeds := mutationSeeds.toArray
  let next (s : Nat) := (s * 6364136223846793005 + 1442695040888963407) % 18446744073709551616
  for _ in [0:count] do
    st := next st
    let mut bs := seeds[(st / 65536) % seeds.size]!
    st := next st
    for _ in [0:1 + (st / 65536) % 3] do
      st := next st
      let pos := (st / 65536) % (bs.length + 1)
      st := next st
      let b := fuzzAlphabet[(st / 65536) % fuzzAlphabet.size]!
      st := next st
      bs := match (st / 65536) % 4 with
        | 0 => bs.take pos ++ [b] ++ bs.drop (pos + 1)
        | 1 => bs.take pos ++ bs.drop (pos + 1)
        | 2 => bs.take pos ++ [b] ++ bs.drop pos
        | _ => bs.take pos ++ (bs.drop pos).take 7 ++ bs.drop pos
    out := bs :: out
  return out

/-- Two wrong parsers, for the negative self-test (the differential must be able to fail): one drops the last byte, one swaps the error codes. -/
def mutantDropLast (a : ByteArray) : Except Error Value := parseFast (a.extract 0 (a.size - 1))
def mutantSwapCodes (a : ByteArray) : Except Error Value :=
  match parseFast a with | .error .syntax => .error .depth | .error .depth => .error .syntax | .ok v => .ok v

/-- A parser without the nesting bound (the budget is effectively unlimited): the negative self-test of the depth policy, it must differ from the reference on the deep rows. -/
def mutantNoBound (a : ByteArray) : Except Error Value := run (a.size + 2) a (skipWsA a 0) false .null .nil (maxDepth * 1000000000000)

/-! ## The fused tape parser against the tape of the reference value (`docs/perf/fuse-plan.md`)

The same differential for `parseTapeFast`: its bytes must be `parseTape`'s on every input (the equation is `parseTapeFast_eq`, `LeanJsonProofs/FastTape.lean`; until it is proved this is the only evidence, and
it stays as the cross-check after). Three wrong fused parsers show the check can fail. Not reachable from any export. -/

/-- The same bytes? -/
def sameTape (x y : ByteArray) : Bool := x.data == y.data

/-- The rows on which the tape function `f` and `parseTape` differ. -/
def tapeDisagreements (f : ByteArray → ByteArray) (rows : List Row) : List Row := rows.filter fun r => !sameTape (f (asArray r.input)) (parseTape (asArray r.input))

/-- Does `f` give `parseTape`'s bytes on this input? -/
def tapeAgreesBA (f : ByteArray → ByteArray) (a : ByteArray) : Bool := sameTape (f a) (parseTape a)
def tapeAgrees (f : ByteArray → ByteArray) (bs : Bytes) : Bool := tapeAgreesBA f (asArray bs)

/-- Wrong fused parsers: one reads one byte less, one changes the last byte of its output, one changes the status word (the error code or the success). -/
def mutantTapeDropLast (a : ByteArray) : ByteArray := parseTapeFast (a.extract 0 (a.size - 1))
def mutantTapeLastByte (a : ByteArray) : ByteArray :=
  let r := parseTapeFast a
  if r.size == 0 then r else r.set! (r.size - 1) (r.get! (r.size - 1) + 1)
def mutantTapeStatus (a : ByteArray) : ByteArray :=
  let r := parseTapeFast a
  if r.size == 0 then r else r.set! 0 (r.get! 0 + 1)

end LeanJson
