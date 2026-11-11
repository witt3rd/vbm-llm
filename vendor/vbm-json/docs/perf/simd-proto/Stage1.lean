/-! # docs/perf/simd-proto/Stage1.lean: PROTOTYPE of the SWAR stage-1 classifier, in Lean (`Init` only), to be compiled by Lean's C emitter and measured (`run.sh`).

It is the same arithmetic as the `swar` variant of `classify.c`, written the way a library module would be (UInt64 operations only, a tail-recursive loop over 64-byte blocks, the
carried state in unboxed arguments, the masks written into a caller-supplied `ByteArray` in place). Nothing here is proved or exported by the library: this file exists to answer
"what C does the Lean emitter produce for it, and how fast is that". The specification and the proofs of the pieces are in `Stage1Proof.lean`.
`lcProof` (an unsafe constant of `Init`) stands in for the bounds proofs a library version would carry, so the prototype's functions are `unsafe` (a library version is not). -/
namespace Stage1

-- NB: byte-lane constants are written as literals (0x2222...): `rep c := c.toUInt64 * 0x0101...` is a closed term, which the emitter initialises once at start-up and reads from memory, not an immediate (measured).

@[inline] def lo7 : UInt64 := 0x7f7f7f7f7f7f7f7f
/-- `0x80` in each byte lane of `x` that is zero (exact: no lane borrows from its neighbour). -/
@[inline] def zl (x : UInt64) : UInt64 := ~~~(((x &&& lo7) + lo7) ||| x ||| lo7)
/-- the `0x80` lanes packed to 8 bits (lane i to bit i). -/
@[inline] def pack8 (m : UInt64) : UInt64 := ((m >>> 7) * 0x0102040810204080) >>> 56

/-- little-endian u64 at byte offset `i` (the caller guarantees `i + 8 ≤ a.size`). -/
@[inline] unsafe def ld (a : @& ByteArray) (i : USize) : UInt64 :=
  (a.uget i lcProof).toUInt64 ||| ((a.uget (i + 1) lcProof).toUInt64 <<< 8) ||| ((a.uget (i + 2) lcProof).toUInt64 <<< 16) ||| ((a.uget (i + 3) lcProof).toUInt64 <<< 24) |||
  ((a.uget (i + 4) lcProof).toUInt64 <<< 32) ||| ((a.uget (i + 5) lcProof).toUInt64 <<< 40) ||| ((a.uget (i + 6) lcProof).toUInt64 <<< 48) ||| ((a.uget (i + 7) lcProof).toUInt64 <<< 56)

@[inline] def qM (w : UInt64) : UInt64 := pack8 (zl (w ^^^ 0x2222222222222222))
@[inline] def bM (w : UInt64) : UInt64 := pack8 (zl (w ^^^ 0x5c5c5c5c5c5c5c5c))
@[inline] def oM (w : UInt64) : UInt64 :=
  let wo := w ||| 0x2020202020202020
  pack8 (zl (wo ^^^ 0x7b7b7b7b7b7b7b7b) ||| zl (wo ^^^ 0x7d7d7d7d7d7d7d7d) ||| zl (w ^^^ 0x3a3a3a3a3a3a3a3a) ||| zl (w ^^^ 0x2c2c2c2c2c2c2c2c))
@[inline] def wM (w : UInt64) : UInt64 := pack8 (zl (w ^^^ 0x2020202020202020) ||| zl (w ^^^ 0x0909090909090909) ||| zl (w ^^^ 0x0a0a0a0a0a0a0a0a) ||| zl (w ^^^ 0x0d0d0d0d0d0d0d0d))
@[inline] def cM (w : UInt64) : UInt64 := pack8 (zl (w &&& 0xe0e0e0e0e0e0e0e0))

/-- the mask of one class over the eight words of a block, from the per-word function `f`. -/
@[inline] def mask8 (f : UInt64 → UInt64) (w0 w1 w2 w3 w4 w5 w6 w7 : UInt64) : UInt64 :=
  f w0 ||| (f w1 <<< 8) ||| (f w2 <<< 16) ||| (f w3 <<< 24) ||| (f w4 <<< 32) ||| (f w5 <<< 40) ||| (f w6 <<< 48) ||| (f w7 <<< 56)

@[inline] def prefixXor (x : UInt64) : UInt64 :=
  let x := x ^^^ (x <<< 1); let x := x ^^^ (x <<< 2); let x := x ^^^ (x <<< 4); let x := x ^^^ (x <<< 8); let x := x ^^^ (x <<< 16); x ^^^ (x <<< 32)

def evenBits : UInt64 := 0x5555555555555555
def oddBits : UInt64 := 0xAAAAAAAAAAAAAAAA

/-- the escaped positions of the block: byte i is escaped iff it follows an odd run of backslashes (a run that begins in the previous block counts through `prev`). -/
@[inline] def escaped (b prev : UInt64) : UInt64 :=
  let bs := b &&& ~~~prev
  let starts := bs &&& ~~~(bs <<< 1)
  let endsEv := (bs + (starts &&& evenBits)) &&& ~~~bs
  let endsOd := (bs + (starts &&& oddBits)) &&& ~~~bs
  (endsEv &&& oddBits) ||| (endsOd &&& evenBits) ||| prev

/-- the carry out of bit 63 of the odd-start addition: an odd run reaches the end of the block, so the first byte of the next block is escaped. -/
@[inline] def escOut (b prev : UInt64) : UInt64 :=
  let bs := b &&& ~~~prev
  let starts := bs &&& ~~~(bs <<< 1)
  if bs + (starts &&& oddBits) < bs then 1 else 0

/-- UTF-8 DFA state after one byte (0 accept, 1..3 continuations owed, 4 after E0, 5 after ED, 6 after F0, 7 after F4, 8 error). -/
@[inline] def u8step (s b : UInt64) : UInt64 :=
  if s == 0 then
    (if b < 0x80 then 0 else if b < 0xC2 then 8 else if b < 0xE0 then 1 else if b == 0xE0 then 4 else if b == 0xED then 5 else if b < 0xF0 then 2
     else if b == 0xF0 then 6 else if b < 0xF4 then 3 else if b == 0xF4 then 7 else 8)
  else if s < 4 then (if 0x80 ≤ b && b < 0xC0 then s - 1 else 8)
  else if s == 4 then (if 0xA0 ≤ b && b < 0xC0 then 1 else 8)
  else if s == 5 then (if 0x80 ≤ b && b < 0xA0 then 1 else 8)
  else if s == 6 then (if 0x90 ≤ b && b < 0xC0 then 2 else 8)
  else if s == 7 then (if 0x80 ≤ b && b < 0x90 then 2 else 8)
  else 8

/-- the DFA over the bytes `[i, i + 64)` (a block with a non-ASCII byte). -/
unsafe def u8block (a : @& ByteArray) (i : USize) (j : USize) (s : UInt64) : UInt64 :=
  if j == 64 then s else u8block a i (j + 1) (u8step s (a.uget (i + j) lcProof).toUInt64)

@[inline] unsafe def putW (out : ByteArray) (k : USize) (w : UInt64) : ByteArray :=
  let i := k * 8
  let out := out.uset i w.toUInt8 lcProof
  let out := out.uset (i + 1) (w >>> 8).toUInt8 lcProof
  let out := out.uset (i + 2) (w >>> 16).toUInt8 lcProof
  let out := out.uset (i + 3) (w >>> 24).toUInt8 lcProof
  let out := out.uset (i + 4) (w >>> 32).toUInt8 lcProof
  let out := out.uset (i + 5) (w >>> 40).toUInt8 lcProof
  let out := out.uset (i + 6) (w >>> 48).toUInt8 lcProof
  out.uset (i + 7) (w >>> 56).toUInt8 lcProof

/-- the loop over `n` blocks; the carried state is `esc str scal` (bits), the ctrl-byte error `err` and the UTF-8 state `u8`; the masks go to `out`, the two errors to the two words after them. -/
unsafe def loop (a : @& ByteArray) (out : ByteArray) (k n : USize) (esc str scal err u8 : UInt64) (useUtf8 : Bool) : ByteArray :=
  if k == n then putW (putW out n err) (n + 1) u8
  else
    let i := k * 64
    let w0 := ld a i; let q := qM w0; let b := bM w0; let o := oM w0; let w := wM w0; let c := cM w0; let ors := w0
    let w1 := ld a (i + 8); let q := q ||| (qM w1 <<< 8); let b := b ||| (bM w1 <<< 8); let o := o ||| (oM w1 <<< 8); let w := w ||| (wM w1 <<< 8); let c := c ||| (cM w1 <<< 8); let ors := ors ||| w1
    let w2 := ld a (i + 16); let q := q ||| (qM w2 <<< 16); let b := b ||| (bM w2 <<< 16); let o := o ||| (oM w2 <<< 16); let w := w ||| (wM w2 <<< 16); let c := c ||| (cM w2 <<< 16); let ors := ors ||| w2
    let w3 := ld a (i + 24); let q := q ||| (qM w3 <<< 24); let b := b ||| (bM w3 <<< 24); let o := o ||| (oM w3 <<< 24); let w := w ||| (wM w3 <<< 24); let c := c ||| (cM w3 <<< 24); let ors := ors ||| w3
    let w4 := ld a (i + 32); let q := q ||| (qM w4 <<< 32); let b := b ||| (bM w4 <<< 32); let o := o ||| (oM w4 <<< 32); let w := w ||| (wM w4 <<< 32); let c := c ||| (cM w4 <<< 32); let ors := ors ||| w4
    let w5 := ld a (i + 40); let q := q ||| (qM w5 <<< 40); let b := b ||| (bM w5 <<< 40); let o := o ||| (oM w5 <<< 40); let w := w ||| (wM w5 <<< 40); let c := c ||| (cM w5 <<< 40); let ors := ors ||| w5
    let w6 := ld a (i + 48); let q := q ||| (qM w6 <<< 48); let b := b ||| (bM w6 <<< 48); let o := o ||| (oM w6 <<< 48); let w := w ||| (wM w6 <<< 48); let c := c ||| (cM w6 <<< 48); let ors := ors ||| w6
    let w7 := ld a (i + 56); let q := q ||| (qM w7 <<< 56); let b := b ||| (bM w7 <<< 56); let o := o ||| (oM w7 <<< 56); let w := w ||| (wM w7 <<< 56); let c := c ||| (cM w7 <<< 56); let ors := ors ||| w7
    let u8' :=
      if useUtf8 then
        (if ors &&& 0x8080808080808080 == 0 then (if u8 != 0 then 8 else 0) else u8block a i 0 u8)
      else u8
    let esc' := escOut b esc
    let e := escaped b esc
    let qq := q &&& ~~~e
    let inStr := prefixXor qq ^^^ (0 - str)
    let nq := ~~~(o ||| w ||| qq)
    let follows := (nq <<< 1) ||| scal
    let s := (o &&& ~~~inStr) ||| qq ||| (nq &&& ~~~follows &&& ~~~inStr)
    loop a (putW out k s) (k + 1) n esc' (inStr >>> 63) (nq >>> 63) (err ||| (c &&& inStr)) u8' useUtf8

/-- MODEL of the shim primitive `s1_ld64` (one 8-byte little-endian load): the Lean body is the specification, the C function (`s1_shim.h`) is what runs. -/
@[extern "s1_ld64"] unsafe def ld64 (a : @& ByteArray) (i : USize) : UInt64 := ld a i
/-- MODEL of `s1_st64` (one 8-byte little-endian store at word index `k`, in place when `out` is unshared). -/
@[extern "s1_st64"] unsafe def st64 (out : ByteArray) (k : USize) (w : UInt64) : ByteArray := putW out k w

/-- `loop` with the two memory primitives (`ld64`, `st64`) as trusted-shim externs (the Lean bodies are their models); the carried state is `esc str scal` (bits), the ctrl-byte error `err` and the UTF-8 state `u8`; the masks go to `out`, the two errors to the two words after them. -/
unsafe def loopX (a : @& ByteArray) (out : ByteArray) (k n : USize) (esc str scal err u8 : UInt64) (useUtf8 : Bool) : ByteArray :=
  if k == n then st64 (st64 out n err) (n + 1) u8
  else
    let i := k * 64
    let w0 := ld64 a i; let w1 := ld64 a (i + 8); let w2 := ld64 a (i + 16); let w3 := ld64 a (i + 24); let w4 := ld64 a (i + 32); let w5 := ld64 a (i + 40); let w6 := ld64 a (i + 48); let w7 := ld64 a (i + 56)
    let q := mask8 qM w0 w1 w2 w3 w4 w5 w6 w7; let b := mask8 bM w0 w1 w2 w3 w4 w5 w6 w7; let o := mask8 oM w0 w1 w2 w3 w4 w5 w6 w7
    let w := mask8 wM w0 w1 w2 w3 w4 w5 w6 w7; let c := mask8 cM w0 w1 w2 w3 w4 w5 w6 w7; let ors := w0 ||| w1 ||| w2 ||| w3 ||| w4 ||| w5 ||| w6 ||| w7
    let u8' :=
      if useUtf8 then
        (if ors &&& 0x8080808080808080 == 0 then (if u8 != 0 then 8 else 0) else u8block a i 0 u8)
      else u8
    let esc' := escOut b esc
    let e := escaped b esc
    let qq := q &&& ~~~e
    let inStr := prefixXor qq ^^^ (0 - str)
    let nq := ~~~(o ||| w ||| qq)
    let follows := (nq <<< 1) ||| scal
    let s := (o &&& ~~~inStr) ||| qq ||| (nq &&& ~~~follows &&& ~~~inStr)
    loopX a (st64 out k s) (k + 1) n esc' (inStr >>> 63) (nq >>> 63) (err ||| (c &&& inStr)) u8' useUtf8

/-- the entry: `n` blocks of `a` (the caller pads), masks into `out` (capacity for `n + 2` words, size `8 * (n + 2)`). -/
@[export s1_lean] unsafe def run (a : ByteArray) (out : ByteArray) (n : USize) (useUtf8 : Bool) : ByteArray :=
  loop a out 0 n 0 0 0 0 0 useUtf8


/-- the same entry with the shim primitives: `n` blocks of `a` (the caller pads), masks into `out` (capacity for `n + 2` words, size `8 * (n + 2)`). -/
@[export s1_lean_x] unsafe def runX (a : ByteArray) (out : ByteArray) (n : USize) (useUtf8 : Bool) : ByteArray :=
  loopX a out 0 n 0 0 0 0 0 useUtf8

end Stage1
