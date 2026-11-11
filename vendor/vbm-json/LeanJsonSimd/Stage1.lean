import LeanJson.Struct
import VbmSimd.Lanes
import VbmSimd.Escape
import VbmSimd.PrefixXor
import VbmSimd.Shims
import VbmSimd.Bytes
import VbmSimd.Find
import VbmSimd.Inset
import VbmSimd.Classify
/-! # `LeanJsonSimd.Stage1`: the bit-parallel structural stage (64 bytes at a time)

`docs/perf/simd-plan.md`. For each block of 64 bytes the kernel loads eight words, classifies them with `VbmSimd.eqLanes` and `pack8` into four masks (quotes, backslashes, operators, whitespace), finds the unescaped quotes (the
add-with-carry trick, `VbmSimd.escaped`), the inside-a-string mask (`VbmSimd.prefixXorC`) and the scalar-run starts, and stores one word: the structural mask of the block. The state handed to the next block is three bits
(escape, string, scalar). `LeanJsonProofs/Stage1.lean` proves, for every input, that bit `p` of word `k` is `isStruct a (64 k + p)`, the byte-at-a-time machine of `LeanJson.Struct`.
Byte-lane constants are named `@[inline]` literals (a computed constant is initialised at start-up and read from memory by the emitted C, not folded to an immediate). -/
namespace LeanJson
open VbmSimd

@[inline] def cQuote : UInt64 := 0x2222222222222222
@[inline] def cBslash : UInt64 := 0x5c5c5c5c5c5c5c5c
@[inline] def cLbrace : UInt64 := 0x7b7b7b7b7b7b7b7b
@[inline] def cRbrace : UInt64 := 0x7d7d7d7d7d7d7d7d
@[inline] def cColon : UInt64 := 0x3a3a3a3a3a3a3a3a
@[inline] def cComma : UInt64 := 0x2c2c2c2c2c2c2c2c
@[inline] def cSpace : UInt64 := 0x2020202020202020
@[inline] def cTab : UInt64 := 0x0909090909090909
@[inline] def cLf : UInt64 := 0x0a0a0a0a0a0a0a0a
@[inline] def cCr : UInt64 := 0x0d0d0d0d0d0d0d0d

/-- The eight bits of one word that are operator bytes: `{ } [ ] : ,` (`[` and `]` are `{` and `}` with bit 5 cleared, so one `or` with `0x20..` folds the four brackets into two compares). -/
@[inline] def opWord (w : UInt64) : UInt64 :=
  let wo := w ||| cSpace
  pack8 (eqLanes cLbrace wo ||| eqLanes cRbrace wo ||| eqLanes cColon w ||| eqLanes cComma w)

/-- The eight bits of one word that are whitespace bytes. -/
@[inline] def wsWord (w : UInt64) : UInt64 := pack8 (eqLanes cSpace w ||| eqLanes cTab w ||| eqLanes cLf w ||| eqLanes cCr w)

/-- From the four class masks of a block (quotes, backslashes, operators, whitespace) and the three carries in (`esc`, `str`, `scal`, each `0` or `1`): the structural mask and the three carries out. -/
@[inline] def maskOut (q b o ws esc str scal : UInt64) : UInt64 × UInt64 × UInt64 × UInt64 :=
  let e := escaped b esc
  let qq := q &&& ~~~e
  let inStr := prefixXorC qq str
  let nq := ~~~(o ||| ws ||| qq)
  let follows := (nq <<< 1) ||| scal
  ((o &&& ~~~inStr) ||| qq ||| (nq &&& ~~~follows &&& ~~~inStr), escOut b esc, inStr >>> 63, nq >>> 63)

/-- `maskOut`, with the escape computation skipped for a block with no backslash (`maskOutF_eq`, `LeanJsonProofs/Stage1Avx.lean`: with `b = 0` the escaped mask is the carry in and the carry out is 0): most blocks have none, and the escape carry chain is
a third of the arithmetic of a block. -/
@[inline] def maskOutF (q b o ws esc str scal : UInt64) : UInt64 × UInt64 × UInt64 × UInt64 :=
  let e := if b == 0 then esc else escaped b esc
  let qq := q &&& ~~~e
  let inStr := prefixXorC qq str
  let nq := ~~~(o ||| ws ||| qq)
  let follows := (nq <<< 1) ||| scal
  ((o &&& ~~~inStr) ||| qq ||| (nq &&& ~~~follows &&& ~~~inStr), if b == 0 then 0 else escOut b esc, inStr >>> 63, nq >>> 63)

/-- One block: the structural mask and the three carries out, from the eight words and the three carries in. -/
@[inline] def blockOut (w0 w1 w2 w3 w4 w5 w6 w7 esc str scal : UInt64) : UInt64 × UInt64 × UInt64 × UInt64 :=
  maskOut (eqMask64 cQuote w0 w1 w2 w3 w4 w5 w6 w7) (eqMask64 cBslash w0 w1 w2 w3 w4 w5 w6 w7) (mask8 opWord w0 w1 w2 w3 w4 w5 w6 w7) (mask8 wsWord w0 w1 w2 w3 w4 w5 w6 w7) esc str scal

/-- Stage 1 over the blocks `k .. n - 1` of `a` (whose size is at least `64 n`): the structural mask of block `k` goes to word `k` of `out`, which must have room for `n` words (`st64` writes nothing past the end). -/
def stage1Loop (a out : ByteArray) (k n : Nat) (esc str scal : UInt64) : ByteArray :=
  if k < n then
    let i := 64 * k
    match blockOut (ld64 a i.toUSize) (ld64 a (i + 8).toUSize) (ld64 a (i + 16).toUSize) (ld64 a (i + 24).toUSize) (ld64 a (i + 32).toUSize) (ld64 a (i + 40).toUSize)
      (ld64 a (i + 48).toUSize) (ld64 a (i + 56).toUSize) esc str scal with
    | (s, esc', str', scal') => stage1Loop a (st64 out k.toUSize s) (k + 1) n esc' str' scal'
  else out
termination_by n - k

/-- Stage 1: the structural mask of `a`, one word per block of 64 bytes (the last block may be partial: bytes past the end read as zero and the bits past the end are cleared). `a` must be smaller than `2^31` bytes
(`stage1_spec`; larger inputs take the scalar parser). -/
def stage1 (a : ByteArray) : ByteArray :=
  let n := (a.size + 63) / 64
  let out := stage1Loop a (zeroBytes (8 * n)) 0 n 0 0 0
  if a.size % 64 == 0 then out
  else st64 out (n - 1).toUSize (ld64 out (8 * (n - 1)).toUSize &&& (((1 : UInt64) <<< (a.size % 64).toUInt64) - 1))

/-! ## The vector classifier (AVX2, NEON)

Where the CPU has AVX2, or on aarch64 (NEON, vbm-simd T15), the four class masks of a block (quotes, backslashes, operators, white space) come from `VbmSimd.inset64`, the trusted shim of vbm-simd (clause VS-12, trust ledger T12: a vector search whose Lean body, the model, is the
per-byte machine `insetSpec`), instead of from the word-at-a-time `blockOut`; everything after the masks (`maskOut`: the escape carry, the string state, the scalar starts) is the same proved Lean. `stage1Fast` takes the shim only where
`hasAvx2 () || hasNeon ()` and runs the portable `stage1` otherwise; `stage1Fast_eq` (`LeanJsonProofs/Stage1Avx.lean`) says `stage1Fast a = stage1 a` for either answer of the CPU test, by the model of the shim. -/

/-- The nibble tables of the JSON byte classes (`VbmSimd.classByte`): the class bits of a byte are `lo[byte & 15] & hi[byte >> 4]`: bit 0 the quote, bit 1 the backslash, bits 2 to 4 the operators (`[ ] { }`, `:`, `,`),
bits 5 and 6 the white space (tab, LF, CR; space). `classTbl_*` (`LeanJsonProofs/Stage1Avx.lean`) say that the four masks of `classMs` are exactly the four portable classes. -/
def classTbl : ByteArray :=
  ByteArray.mk #[0x40, 0, 0x01, 0, 0, 0, 0, 0, 0, 0x20, 0x28, 0x04, 0x12, 0x24, 0, 0,   0x20, 0, 0x51, 0x08, 0, 0x06, 0, 0x04, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The mask bytes of the four classes, in the order `maskOut` takes them: quote `0x01`, backslash `0x02`, operators `0x1C`, white space `0x60`. -/
@[inline] def classMs : UInt32 := 0x601C0201

/-- Stage 1 over the blocks `k .. n - 1`, the four class masks of a block from one call of the AVX2 class shim (`classify64`, whose words 0 to 3 of the scratch array `cls` are the quote, backslash, operator and white space masks). -/
def stage1LoopB (a cls out : ByteArray) (k n : USize) (esc str scal : UInt64) : ByteArray :=
  if _h : k < n then
    let cls := classify64 a (k <<< 6) classTbl classMs cls
    match maskOutF (ld64 cls 0) (ld64 cls 8) (ld64 cls 16) (ld64 cls 24) esc str scal with
    | (s, esc', str', scal') => stage1LoopB a cls (st64 out k s) (k + 1) n esc' str' scal'
  else out
termination_by n.toNat - k.toNat
decreasing_by
  have h : k < n := ‹_›
  have h3 := USize.lt_iff_toNat_lt.1 h
  have h7 := USize.toNat_lt_size n
  have h1 : (1 : USize).toNat = 1 := USize.toNat_ofNat_of_lt_32 (by decide)
  have h8 : (k + 1).toNat = k.toNat + 1 := by
    have h9 : k.toNat + 1 < USize.size := by omega
    rw [USize.toNat_add, h1]; exact Nat.mod_eq_of_lt h9
  rw [h8]
  omega

/-- `stage1` with the AVX2 classifier: the same masks, the same last-block clearing. -/
def stage1A (a : ByteArray) : ByteArray :=
  let n := (a.size + 63) / 64
  let out := stage1LoopB a (zeroBytes 32) (zeroBytes (8 * n)) 0 n.toUSize 0 0 0
  if a.size % 64 == 0 then out
  else st64 out (n - 1).toUSize (ld64 out (8 * (n - 1)).toUSize &&& (((1 : UInt64) <<< (a.size % 64).toUInt64) - 1))

/-- The structural mask the parser uses: the vector classifier on a CPU that has AVX2 (and the OS support: `hasAvx2`) or on aarch64 (NEON: `hasNeon`, a compile-time fact), the portable `stage1` otherwise. -/
def stage1Fast (a : ByteArray) : ByteArray := if hasAvx2 () || hasNeon () then stage1A a else stage1 a

end LeanJson
