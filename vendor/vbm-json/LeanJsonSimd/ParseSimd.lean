import LeanJson.Tape
import LeanJsonSimd.Stage1
import VbmSimd.Cursor
import VbmSimd.Append
/-! # `LeanJsonSimd.ParseSimd`: the index-driven parser (stage 2 of the bit-parallel parser), with a verified-sound fallback

`docs/perf/simd-plan.md`. `runI` is `runT` (`LeanJson/Tape.lean`) with one change: the whitespace between tokens is not scanned byte by byte but skipped by asking the structural mask of stage 1 (`LeanJson.Stage1.stage1`) for the next
structural position (`skipI`, one masked word and a `ctz`). Everything else (the tape, the text region, the nesting budget, the leaves) is `runT`'s, so the proof is a simulation. Where the index cannot be trusted
to agree with the leaf that just ran, `runI` *declines* (returns `none`): a string must end at the first structural position after its opening quote, and a number or literal must be followed by a delimiter. Any error also
declines: `parseTapeSimd` then runs the scalar parser, so an invalid document gets its error code from `parseTapeFast`, unchanged. `LeanJsonProofs/ParseSimd.lean` proves `parseTapeSimd_eq : parseTapeSimd a = parseTapeFast a`:
only soundness of the fast path is proved (when it answers, the answer is the scalar parser's), never completeness (a declined document is merely slower). -/
namespace LeanJson
open VbmSimd

/-- The first structural position at or after `j`, or the end of the input (`size`) when there is none. -/
@[inline] def skipI (m : ByteArray) (size j : Nat) : Nat := let r := nextSet m j; if r < size then r else size

/-- The end of a scalar: the input ends, or the next byte is whitespace, an operator or a quote. -/
@[inline] def delimAt (a : ByteArray) (j : Nat) : Bool :=
  match byteAt a j with
  | none => true
  | some b => isWs b || isOp b || b == 0x22

/-- A string node (value or key) from the string whose opening quote is at `i`, declining unless the string ends at the first structural position after its opening quote (the index agrees with the leaf). -/
def TapeBuf.strNodeI (s : TapeBuf) (kind : Nat) (m : ByteArray) (a : ByteArray) (i : Nat) : Option (TapeBuf × Nat) :=
  match s.strNode kind a i with
  | some (s', j) => if skipI m a.size (i + 1) == j - 1 then some (s', j) else none
  | none => none

/-- A key and its colon (`TapeBuf.keyNode`), with the index skip. -/
def TapeBuf.keyNodeI (s : TapeBuf) (m : ByteArray) (a : ByteArray) (i : Nat) : Option (TapeBuf × Nat) :=
  match s.strNodeI kindStr m a i with
  | some (s', j) => let j1 := skipI m a.size j; if byteIs a j1 0x3A then some (s', skipI m a.size (j1 + 1)) else none
  | none => none

/-- `runT` with the index skip and with every error and disagreement declined (`none`). -/
def runI (m : ByteArray) : Nat → ByteArray → Nat → Bool → TapeBuf → FStack → Nat → Option ByteArray
  | 0, _, _, _, _, _, _ => none
  | f + 1, a, i, false, tb, fst, d =>
    match byteAt a i with
    | none => none
    | some b =>
      if b == 0x5B then
        if d == 0 then none
        else
          let i1 := skipI m a.size (i + 1)
          if byteIs a i1 0x5D then runI m f a (i1 + 1) true (tb.node kindArr 0 2) fst d
          else
            let at_ := tb.words
            runI m f a i1 false (tb.node kindArr 0 0) (.arr at_ 0 fst) (d - 1)
      else if b == 0x7B then
        if d == 0 then none
        else
          let i1 := skipI m a.size (i + 1)
          if byteIs a i1 0x7D then runI m f a (i1 + 1) true (tb.node kindObj 0 2) fst d
          else
            let at_ := tb.words
            match (tb.node kindObj 0 0).keyNodeI m a i1 with
            | some (tb', j) => runI m f a j false tb' (.obj at_ 0 fst) (d - 1)
            | none => none
      else if b == 0x22 then
        match tb.strNodeI kindStr m a i with
        | some (tb', j) => runI m f a j true tb' fst d
        | none => none
      else if b == 0x6E then
        match litA a (i + 1) [0x75, 0x6C, 0x6C] with
        | some j => if delimAt a j then runI m f a j true (tb.node kindNull 0 0) fst d else none
        | none => none
      else if b == 0x74 then
        match litA a (i + 1) [0x72, 0x75, 0x65] with
        | some j => if delimAt a j then runI m f a j true (tb.node kindTrue 0 0) fst d else none
        | none => none
      else if b == 0x66 then
        match litA a (i + 1) [0x61, 0x6C, 0x73, 0x65] with
        | some j => if delimAt a j then runI m f a j true (tb.node kindFalse 0 0) fst d else none
        | none => none
      else
        match scanNum a i with
        | some j => if delimAt a j then runI m f a j true (tb.numLex a i j) fst d else none
        | none => none
  | _ + 1, a, i, true, tb, .nil, _ => if a.size ≤ skipI m a.size i then some (tapeOk tb) else none
  | f + 1, a, i, true, tb, .arr at_ n rest, d =>
    let i1 := skipI m a.size i
    if byteIs a i1 0x2C then runI m f a (skipI m a.size (i1 + 1)) false tb (.arr at_ (n + 1) rest) d
    else if byteIs a i1 0x5D then runI m f a (i1 + 1) true (tb.closeNode kindArr at_ (n + 1)) rest (d + 1)
    else none
  | f + 1, a, i, true, tb, .obj at_ n rest, d =>
    let i1 := skipI m a.size i
    if byteIs a i1 0x2C then
      match tb.keyNodeI m a (skipI m a.size (i1 + 1)) with
      | some (tb', j) => runI m f a j false tb' (.obj at_ (n + 1) rest) d
      | none => none
    else if byteIs a i1 0x7D then runI m f a (i1 + 1) true (tb.closeNode kindObj at_ (n + 1)) rest (d + 1)
    else none

/-! ## `runW`: `runI` with the tape written in place

`runI` carries the tape and the text region in a `TapeBuf` and appends to them with `ByteArray` runtime calls (the profile of `docs/perf/results.md`: the tape words alone are a third of the time). `runW` keeps the same
control flow and carries three plain values instead: `tape` (a byte array that is *longer* than what has been written, zero-filled beyond), `tw` (the number of words written) and `text` (exactly the text region). A node's two
words are stored with `st64` (`ensureTape` first makes room: 4096 zero bytes at a time, so the zeros are written into cache that the stores use at once); a plain string, and a number without `E` or `+`, are copied from
the input by one `copySlice`; `skipF` is `skipI` with the first word of the mask read inline; the literals and the leaves that decline are `runI`'s. `LeanJsonProofs/ParseW.lean`: `runW` answers `t` only when `runI` answers `t`. -/

/-- The first structural position at or after `j` (or `size`): `skipI` with the word that holds `j` read in line (a shift and `USize` arithmetic, no `Nat` multiplication or left shift, which are slow: `skipF_eq`). The guard keeps the offsets far below `USize`. -/
@[inline] def skipF (m : ByteArray) (size j : Nat) : Nat :=
  if j < 1073741824 then
    let k := (j >>> 6).toUSize
    let w := ld64 m (k <<< 3) &&& ((~~~(0 : UInt64)) <<< (j &&& 63).toUInt64)
    if w != 0 then (let r := (k <<< 6).toNat + (ctz w).toNat; if r < size then r else size) else skipI m size j
  else skipI m size j

/-- 4096 zero bytes: the growth step of the tape. A closed term, built once at start-up. -/
def zeros4k : ByteArray := zeroBytes 4096

/-- The tape with 4096 more zero bytes. -/
@[noinline] def growTape (t : ByteArray) : ByteArray := zeros4k.copySlice 0 t t.size 4096 false

/-- The tape, with room for the two words at word index `w`. -/
@[inline] def ensureTape (t : ByteArray) (w : Nat) : ByteArray := if w + 2 ≤ t.size / 8 then t else growTape t

/-- The header word of a node: `kind` (a literal below 256) and `len` (`pushWord` of `kind + len * 256`, `hdrW_eq`). -/
@[inline] def hdrW (kind : UInt64) (len : Nat) : UInt64 := UInt64.ofNat len * 256 + kind

/-- `hdrW`, with the count as a word. -/
@[inline] def hdrWu (kind : UInt64) (len : UInt64) : UInt64 := len * 256 + kind

/-- The two stores that close a container whose header is at word `at_`: its header word `h` (kind and count) and its subtree size, `tw - at_` words (`0` if `at_` is past `tw`, as `Nat` subtraction is). -/
@[inline] def closeU (tape : ByteArray) (at_ tw : USize) (h : UInt64) : ByteArray :=
  st64 (st64 tape at_ h) (at_ + 1) (if at_ ≤ tw then (tw - at_).toUInt64 else 0)

/-- The two words of a node stored at word index `w` of the tape. -/
@[inline] def putNode (t : ByteArray) (w : Nat) (h x : UInt64) : ByteArray := st64 (st64 (ensureTape t w) w.toUSize h) (w + 1).toUSize x

/-- Every byte of `a[p, e)` is a plain ASCII byte other than the quote. -/
def plainRun (a : ByteArray) (p e : Nat) : Bool :=
  if h : p < e then (if h2 : p < a.size then (if plainAscii a[p] && a[p] != 0x22 then plainRun a (p + 1) e else false) else false) else true
termination_by e - p

/-- No byte of `a[p, e)` is `E` or `+` (so the canonical lexeme is the input). -/
def lexRun (a : ByteArray) (p e : Nat) : Bool :=
  if h : p < e then (if h2 : p < a.size then (if a[p] != 0x45 && a[p] != 0x2B then lexRun a (p + 1) e else false) else false) else true
termination_by e - p

/-! ## Word-parallel leaves

Eight bytes of the input are tested at once (`ld64`, then `SWAR` byte-lane tests whose every addition is carry-free: no lane's sum reaches 256, so the lanes do not interact: `LeanJsonProofs/Swar.lean`). `plainBad` flags (`0x80` in the lane) the bytes of a string
that are not plain: below `0x20`, `0x80` or above, `\`, `"`. `ndFlags` flags the bytes that are not an ASCII digit. The first flagged lane is found by `ctz`. Only whole words inside the input are read; the last
(at most seven) bytes of a document are done a byte at a time by the leaf these replace (`plainOff_run`, `scanDigitsW_eq`). -/

@[inline] def cHi : UInt64 := 0x8080808080808080
@[inline] def cLo7 : UInt64 := 0x7f7f7f7f7f7f7f7f

/-- `0x80` in every lane of `w` that is not a plain string byte (`plainBad_lane`). -/
@[inline] def plainBad (w : UInt64) : UInt64 :=
  ((~~~((w &&& cLo7) + 0x6060606060606060) ||| w) &&& cHi) ||| eqLanes cBslash w ||| eqLanes cQuote w

/-- The number of bytes at `p` that are plain (below the first flagged lane), by whole words while eight bytes remain, added to `acc` (a tail call: a string of a hundred thousand bytes is a loop, not a stack: `plainOff_acc`). -/
def plainOff (a : ByteArray) (p acc : Nat) : Nat :=
  if h : p + 8 ≤ a.size then
    let f := plainBad (ld64 a p.toUSize)
    if f == 0 then plainOff a (p + 8) (acc + 8) else acc + (ctz f).toNat / 8
  else acc
termination_by a.size - p

/-- `0x80` in every lane of `w` that is not an ASCII digit (`ndFlags_lane`). -/
@[inline] def ndFlags (w : UInt64) : UInt64 :=
  let x := w ^^^ 0x3030303030303030
  (((x &&& cLo7) + 0x7676767676767676) ||| x) &&& cHi

/-- `scanDigits` by whole words: the index after the digits at `i`. -/
def scanDigitsW (a : ByteArray) (i : Nat) : Nat :=
  if h : i + 8 ≤ a.size then
    let f := ndFlags (ld64 a i.toUSize)
    if f == 0 then scanDigitsW a (i + 8) else i + (ctz f).toNat / 8
  else scanDigits a i
termination_by a.size - i

/-- `scanDigits1`, with `scanDigitsW`. -/
@[inline] def scanDigits1W (a : ByteArray) (i : Nat) : Option Nat :=
  match byteAt a i with
  | some b => if (digitVal b).isSome then some (scanDigitsW a (i + 1)) else none
  | none => none

/-- `scanInt`, with `scanDigitsW`. -/
@[inline] def scanIntW (a : ByteArray) (i : Nat) : Option Nat :=
  match byteAt a i with
  | none => none
  | some b => if b == 0x30 then some (i + 1) else if (digit19 b).isSome then some (scanDigitsW a (i + 1)) else none

/-- `scanFrac`, with `scanDigitsW`. -/
@[inline] def scanFracW (a : ByteArray) (i : Nat) : Option Nat :=
  if byteIs a i 0x2E then scanDigits1W a (i + 1) else some i

/-- `scanExp`, with `scanDigitsW`. -/
@[inline] def scanExpW (a : ByteArray) (i : Nat) : Option Nat :=
  if byteIs a i 0x65 || byteIs a i 0x45 then scanDigits1W a (if byteIs a (i + 1) 0x2B || byteIs a (i + 1) 0x2D then i + 2 else i + 1)
  else some i

/-- `scanNum`, with `scanDigitsW` (`scanNumW_eq`). -/
@[inline] def scanNumW (a : ByteArray) (i : Nat) : Option Nat :=
  match scanIntW a (if byteIs a i 0x2D then i + 1 else i) with
  | none => none
  | some i1 => match scanFracW a i1 with
    | none => none
    | some i2 => scanExpW a i2


/-- `decodeUtf8A`, in continuation-passing style: the continuation `k` takes the scalar and the index after it (no `Option` and no pair is built). -/
@[inline] def decodeUtf8K {β : Type} (a : ByteArray) (i : Nat) (k : Nat → Nat → β) (d : β) : β :=
  match byteAt a i with
  | none => d
  | some x =>
    if x.toNat < 0x80 then k x.toNat (i + 1)
    else if 0xC2 ≤ x.toNat ∧ x.toNat ≤ 0xDF then
      match byteAt a (i + 1) with
      | some b => if Tail b then k ((x.toNat - 0xC0) * 64 + (b.toNat - 0x80)) (i + 2) else d
      | none => d
    else if 0xE0 ≤ x.toNat ∧ x.toNat ≤ 0xEF then
      match byteAt a (i + 1), byteAt a (i + 2) with
      | some b, some c => if Second3 x b ∧ Tail c then k ((x.toNat - 0xE0) * 4096 + (b.toNat - 0x80) * 64 + (c.toNat - 0x80)) (i + 3) else d
      | _, _ => d
    else if 0xF0 ≤ x.toNat ∧ x.toNat ≤ 0xF4 then
      match byteAt a (i + 1), byteAt a (i + 2), byteAt a (i + 3) with
      | some b, some c, some e =>
        if Second4 x b ∧ Tail c ∧ Tail e then k ((x.toNat - 0xF0) * 262144 + (b.toNat - 0x80) * 4096 + (c.toNat - 0x80) * 64 + (e.toNat - 0x80)) (i + 4) else d
      | _, _, _ => d
    else d

/-- `decodeUA`, in continuation-passing style. -/
@[inline] def decodeUK {β : Type} (a : ByteArray) (i : Nat) (k : Nat → Nat → β) (d : β) : β :=
  match hex4At a i with
  | none => d
  | some n =>
    if n < 0xD800 ∨ 0xE000 ≤ n then k n (i + 4)
    else if n < 0xDC00 then
      if byteIs a (i + 4) 0x5C && byteIs a (i + 5) 0x75 then
        match hex4At a (i + 6) with
        | some lo => if 0xDC00 ≤ lo ∧ lo < 0xE000 then k (0x10000 + (n - 0xD800) * 0x400 + (lo - 0xDC00)) (i + 10) else d
        | none => d
      else d
    else d

/-- `decodeCharA`, in continuation-passing style. -/
@[inline] def decodeCharK {β : Type} (a : ByteArray) (i : Nat) (k : Nat → Nat → β) (d : β) : β :=
  if byteIs a i 0x5C then
    match byteAt a (i + 1) with
    | none => d
    | some b => if b == 0x75 then decodeUK a (i + 2) k d else match simpleEsc b with | some n => k n (i + 2) | none => d
  else decodeUtf8K a i (fun n j => if 0x20 ≤ n ∧ n ≠ 0x22 ∧ n ≠ 0x5C then k n j else d) d

/-- From a position `q` where a run of plain ASCII bytes (by words, `plainOff`) stopped: the end of the run continued over well-formed multi-byte characters (a validity check by `decodeUtf8K`, whose scalar is not used) and the plain bytes
after them. The bytes of the run are what `strBytes` writes for it (`strBytes_run`). -/
def mbRun (a : ByteArray) (q : Nat) : Nat :=
  if h : q < a.size then
    if a[q].toNat < 0x80 then q
    else decodeUtf8K a q (fun _ e => if q < e then mbRun a (e + plainOff a e 0) else q) q
  else q
termination_by a.size - q
decreasing_by
  all_goals simp_wf
  all_goals omega

/-- Whatever the continuation and the default are, a property of both is a property of `decodeUtf8K`'s answer. -/
theorem decodeUtf8K_mono {β : Type} (a : ByteArray) (i : Nat) (k : Nat → Nat → β) (d : β) (P : β → Prop) (hk : ∀ n e, P (k n e)) (hd : P d) :
    P (decodeUtf8K a i k d) := by
  unfold decodeUtf8K
  repeat' split
  all_goals first | exact hk _ _ | exact hd

theorem mbRun_ge (a : ByteArray) : ∀ d q, a.size - q = d → q ≤ mbRun a q := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
    intro q hd
    rw [mbRun]
    by_cases h : q < a.size
    · simp only [h, ↓reduceDIte]
      by_cases h2 : a[q].toNat < 0x80
      · simp only [h2, ↓reduceIte]; omega
      · simp only [h2, ↓reduceIte]
        apply decodeUtf8K_mono a _ _ _ (fun r => q ≤ r) _ (by omega)
        intro n e
        by_cases h3 : q < e
        · simp only [h3, ↓reduceIte]
          have := ih (a.size - (e + plainOff a e 0)) (by omega) (e + plainOff a e 0) rfl
          omega
        · simp only [h3, ↓reduceIte]; omega
    · simp only [h, ↓reduceDIte]; omega

/-- The end of the run at `i` of plain ASCII bytes and well-formed multi-byte characters: the plain bytes by words, then `mbRun` only where the byte that stopped them is not ASCII. -/
@[inline] def runEnd (a : ByteArray) (i : Nat) : Nat :=
  let q := i + plainOff a i 0
  if h : q < a.size then (if a[q].toNat < 0x80 then q else mbRun a q) else q

theorem runEnd_ge (a : ByteArray) (i : Nat) : i ≤ runEnd a i := by
  unfold runEnd
  by_cases h : i + plainOff a i 0 < a.size
  · simp only [h, ↓reduceDIte]
    by_cases h2 : a[i + plainOff a i 0].toNat < 0x80
    · simp only [h2, ↓reduceIte]; omega
    · simp only [h2, ↓reduceIte]
      have := mbRun_ge a _ (i + plainOff a i 0) rfl
      omega
  · simp only [h, ↓reduceDIte]; omega

/-- `strBytes`, with the run (plain ASCII bytes and well-formed multi-byte characters) at each position copied by one `copySlice` (`strBytesW_eq`). -/
def strBytesW (a : ByteArray) (i : Nat) (b : ByteArray) : Option (ByteArray × Nat) :=
  let p := runEnd a i
  let b := if p == i then b else a.copySlice i b b.size (p - i) false
  if h : p < a.size then
    if a[p] == 0x22 then some (b, p + 1)
    else if plainAscii a[p] then strBytesW a (p + 1) (b.push a[p])
    else decodeCharK a p (fun n j => if p < j then strBytesW a j (pushChar b (Char.ofNat n)) else none) none
  else none
termination_by a.size - i
decreasing_by all_goals (have := runEnd_ge a i; omega)

/-- `0x80` in every lane of `w` that is `E` or `+` (`lexBad_lane`). -/
@[inline] def lexBad (w : UInt64) : UInt64 := eqLanes 0x4545454545454545 w ||| eqLanes 0x2b2b2b2b2b2b2b2b w

/-- `lexRun`, eight bytes at a time; the last, partial word has its lanes past `e` cleared (`lexOk_eq`). -/
def lexOk (a : ByteArray) (p e : Nat) : Bool :=
  if h : p + 8 ≤ e then (if lexBad (ld64 a p.toUSize) == 0 then lexOk a (p + 8) e else false)
  else if p < e then (lexBad (ld64 a p.toUSize) &&& (((1 : UInt64) <<< (8 * (e - p).toUInt64)) - 1)) == 0
  else true
termination_by e - p

/-- The text of the string whose opening quote is at `i` appended to `text`, and the index after its closing quote: `TapeBuf.strNodeI` without the tape. A string with no escape and no non-ASCII byte is one copy. -/
@[inline] def strW (m : ByteArray) (a : ByteArray) (i : Nat) (text : ByteArray) : Option (ByteArray × Nat) :=
  if byteIs a i 0x22 then
    let r := skipF m a.size (i + 1)
    if i + 1 + plainOff a (i + 1) 0 == r && byteIs a r 0x22 then some (a.copySlice (i + 1) text text.size (r - i - 1) false, r + 1)
    else match strBytesW a (i + 1) text with
      | some (t, j) => if r == j - 1 then some (t, j) else none
      | none => none
  else none

/-- The result bytes of a finished parse from the in-place tape and text: the three header words, the tape, the text (`finishW_eq`). -/
def finishW (tape text : ByteArray) (tw : Nat) : ByteArray :=
  let h := pushWordFast (pushWordFast (pushWordFast (ByteArray.emptyWithCapacity (24 + 8 * tw + text.size)) 0) (UInt64.ofNat tw)) (UInt64.ofNat text.size)
  let r := tape.copySlice 0 h 24 (8 * tw) false
  text.copySlice 0 r r.size text.size false

/-- `runI`, with the tape and the text written in place. -/
def runW (m : ByteArray) : Nat → ByteArray → Nat → Bool → ByteArray → Nat → ByteArray → FStack → Nat → Option ByteArray
  | 0, _, _, _, _, _, _, _, _ => none
  | f + 1, a, i, false, tape, tw, text, fst, d =>
    match byteAt a i with
    | none => none
    | some b =>
      if b == 0x5B then
        if d == 0 then none
        else
          let i1 := skipF m a.size (i + 1)
          if byteIs a i1 0x5D then runW m f a (i1 + 1) true (putNode tape tw (hdrW 5 0) 2) (tw + 2) text fst d
          else runW m f a i1 false (putNode tape tw (hdrW 5 0) 0) (tw + 2) text (.arr tw 0 fst) (d - 1)
      else if b == 0x7B then
        if d == 0 then none
        else
          let i1 := skipF m a.size (i + 1)
          if byteIs a i1 0x7D then runW m f a (i1 + 1) true (putNode tape tw (hdrW 6 0) 2) (tw + 2) text fst d
          else
            let tape := putNode tape tw (hdrW 6 0) 0
            let o := text.size
            match strW m a i1 text with
            | some (text', j) =>
              let j1 := skipF m a.size j
              if byteIs a j1 0x3A then
                runW m f a (skipF m a.size (j1 + 1)) false (putNode tape (tw + 2) (hdrW 4 (text'.size - o)) (UInt64.ofNat o)) (tw + 4) text' (.obj tw 0 fst) (d - 1)
              else none
            | none => none
      else if b == 0x22 then
        let o := text.size
        match strW m a i text with
        | some (text', j) => runW m f a j true (putNode tape tw (hdrW 4 (text'.size - o)) (UInt64.ofNat o)) (tw + 2) text' fst d
        | none => none
      else if b == 0x6E then
        match litA a (i + 1) [0x75, 0x6C, 0x6C] with
        | some j => if delimAt a j then runW m f a j true (putNode tape tw (hdrW 0 0) 0) (tw + 2) text fst d else none
        | none => none
      else if b == 0x74 then
        match litA a (i + 1) [0x72, 0x75, 0x65] with
        | some j => if delimAt a j then runW m f a j true (putNode tape tw (hdrW 2 0) 0) (tw + 2) text fst d else none
        | none => none
      else if b == 0x66 then
        match litA a (i + 1) [0x61, 0x6C, 0x73, 0x65] with
        | some j => if delimAt a j then runW m f a j true (putNode tape tw (hdrW 1 0) 0) (tw + 2) text fst d else none
        | none => none
      else
        match scanNumW a i with
        | some j =>
          if delimAt a j then
            let o := text.size
            let text' := if lexOk a i j then a.copySlice i text o (j - i) false else pushLex a i j text
            runW m f a j true (putNode tape tw (hdrW 3 (text'.size - o)) (UInt64.ofNat o)) (tw + 2) text' fst d
          else none
        | none => none
  | _ + 1, a, i, true, tape, tw, text, .nil, _ => if a.size ≤ skipF m a.size i then some (finishW tape text tw) else none
  | f + 1, a, i, true, tape, tw, text, .arr at_ n rest, d =>
    let i1 := skipF m a.size i
    if byteIs a i1 0x2C then runW m f a (skipF m a.size (i1 + 1)) false tape tw text (.arr at_ (n + 1) rest) d
    else if byteIs a i1 0x5D then runW m f a (i1 + 1) true (st64 (st64 tape at_.toUSize (hdrW 5 (n + 1))) (at_ + 1).toUSize (UInt64.ofNat (tw - at_))) tw text rest (d + 1)
    else none
  | f + 1, a, i, true, tape, tw, text, .obj at_ n rest, d =>
    let i1 := skipF m a.size i
    if byteIs a i1 0x2C then
      let o := text.size
      match strW m a (skipF m a.size (i1 + 1)) text with
      | some (text', j) =>
        let j1 := skipF m a.size j
        if byteIs a j1 0x3A then
          runW m f a (skipF m a.size (j1 + 1)) false (putNode tape tw (hdrW 4 (text'.size - o)) (UInt64.ofNat o)) (tw + 2) text' (.obj at_ (n + 1) rest) d
        else none
      | none => none
    else if byteIs a i1 0x7D then runW m f a (i1 + 1) true (st64 (st64 tape at_.toUSize (hdrW 6 (n + 1))) (at_ + 1).toUSize (UInt64.ofNat (tw - at_))) tw text rest (d + 1)
    else none

/-! ## `runU`: `runW` with every position, count and the fuel as `USize`

The profile of `runW` (`docs/perf/results.md`): a quarter of the time is checked `Nat` arithmetic on positions (every `Nat` is a boxed scalar with a tag test and an overflow check per operation, a `lean_dec` after each, a conversion
at every `ld64` and `st64`). `runU` is `runW` with the positions (`i`, `tw`, the leaf results), the nesting budget and the fuel as `USize`, a byte read as `uget` after one `USize` comparison against `a.usize`, and the literals unrolled.
The text region keeps `Nat` sizes (its length is not bounded by the input size in the types). `LeanJsonProofs/ParseU.lean`: `runU` answers `t` only when `runW` answers `t`, for inputs below `simdLimit` (no `USize` operation
overflows there, on 32 bits as on 64). -/

theorem usize_toNat_le (a : ByteArray) : a.usize.toNat ≤ a.size := by
  have h2 : a.usize.toNat = a.size % 2 ^ System.Platform.numBits := rfl
  have h3 := Nat.mod_le a.size (2 ^ System.Platform.numBits)
  omega

theorem ugetOk (a : ByteArray) (i : USize) (h : i < a.usize) : i.toNat < a.size := by
  have h1 := USize.lt_iff_toNat_lt.1 h
  have h3 := usize_toNat_le a
  omega

theorem usize_lit (n : Nat) (h : n < 4294967296) : (OfNat.ofNat n : USize).toNat = n := USize.toNat_ofNat_of_lt_32 h

theorem usize_add_lt (x y : USize) (h : x.toNat + y.toNat < USize.size) : (x + y).toNat = x.toNat + y.toNat := by
  rw [USize.toNat_add]
  exact Nat.mod_eq_of_lt h

theorem usize_add_lit (x : USize) (n : Nat) (hn : n < 4294967296) (h : x.toNat + n < USize.size) : (x + (OfNat.ofNat n : USize)).toNat = x.toNat + n := by
  rw [usize_add_lt x _ (by rw [usize_lit n hn]; exact h), usize_lit n hn]

theorem fuel_dec (f : USize) (h : ¬ (f == 0) = true) : (f - 1).toNat < f.toNat := by
  have h1 : f ≠ 0 := by simpa using h
  have h2 : 0 < f.toNat := by
    rcases Nat.eq_zero_or_pos f.toNat with h3 | h3
    · exact absurd (USize.toNat_inj.mp (by rw [h3]; rfl)) h1
    · exact h3
  have h3 : (1 : USize) ≤ f := by
    rw [USize.le_iff_toNat_le, usize_lit 1 (by decide)]; omega
  rw [USize.toNat_sub_of_le f 1 h3, usize_lit 1 (by decide)]
  omega

/-- `byteIs`, at a `USize` position. -/
@[inline] def byteIsU (a : ByteArray) (i : USize) (c : UInt8) : Bool := if h : i < a.usize then a.uget i (ugetOk a i h) == c else false

/-- `delimAt`, at a `USize` position. -/
@[inline] def delimAtU (a : ByteArray) (j : USize) : Bool :=
  if h : j < a.usize then (let b := a.uget j (ugetOk a j h); isWs b || isOp b || b == 0x22) else true

/-- `skipF`, in `USize`: `size` is the input's size (`a.usize`). The slow walk (no bit in the word of `j`) is `skipI`'s. -/
@[inline] def skipU (m : ByteArray) (size j : USize) : USize :=
  let k := j >>> 6
  let w := ld64 m (k <<< 3) &&& ((~~~(0 : UInt64)) <<< (j &&& 63).toUInt64)
  if w != 0 then (let r := (k <<< 6) + (ctz w).toUSize; if r < size then r else size) else (skipI m size.toNat j.toNat).toUSize

/-- `ensureTape`, in `USize`. -/
@[inline] def ensureTapeU (t : ByteArray) (w : USize) : ByteArray := if w + 2 ≤ (t.usize >>> (3 : USize)) then t else growTape t

/-- `putNode`, at a `USize` word index. -/
@[inline] def putNodeU (t : ByteArray) (w : USize) (h x : UInt64) : ByteArray := st64 (st64 (ensureTapeU t w) w h) (w + 1) x

/-- `plainOff`, in `USize` (the guard `p ≤ a.usize ∧ 8 ≤ a.usize - p` cannot wrap). -/
def plainOffU (a : ByteArray) (p acc : USize) : USize :=
  if h : p ≤ a.usize ∧ 8 ≤ a.usize - p then
    let f := plainBad (ld64 a p)
    if f == 0 then plainOffU a (p + 8) (acc + 8) else acc + (ctz f).toUSize / 8
  else acc
termination_by a.size - p.toNat
decreasing_by
  obtain ⟨h1, h2⟩ := h
  have h3 := USize.le_iff_toNat_le.1 h1
  have h4 := USize.le_iff_toNat_le.1 h2
  have h5 := usize_toNat_le a
  have h6 := USize.toNat_sub_of_le _ _ h1
  rw [usize_lit 8 (by decide)] at h4
  rw [usize_add_lit p 8 (by decide) (by have := USize.toNat_lt_size a.usize; omega)]
  omega

/-- `scanDigits`, a byte at a time, in `USize`. -/
def scanDigitsB (a : ByteArray) (i : USize) : USize :=
  if h : i < a.usize then (if (digitVal (a.uget i (ugetOk a i h))).isSome then scanDigitsB a (i + 1) else i) else i
termination_by a.size - i.toNat
decreasing_by
  have h1 := ugetOk a i h
  have h3 := USize.lt_iff_toNat_lt.1 h
  rw [usize_add_lit i 1 (by decide) (by have := USize.toNat_lt_size a.usize; omega)]
  omega

/-- `scanDigitsW`, in `USize`. -/
def scanDigitsU (a : ByteArray) (i : USize) : USize :=
  if h : i ≤ a.usize ∧ 8 ≤ a.usize - i then
    let f := ndFlags (ld64 a i)
    if f == 0 then scanDigitsU a (i + 8) else i + (ctz f).toUSize / 8
  else scanDigitsB a i
termination_by a.size - i.toNat
decreasing_by
  obtain ⟨h1, h2⟩ := h
  have h3 := USize.le_iff_toNat_le.1 h1
  have h4 := USize.le_iff_toNat_le.1 h2
  have h5 := usize_toNat_le a
  have h6 := USize.toNat_sub_of_le _ _ h1
  rw [usize_lit 8 (by decide)] at h4
  rw [usize_add_lit i 8 (by decide) (by have := USize.toNat_lt_size a.usize; omega)]
  omega

/-- `scanDigits1W`, in `USize`; `0` for none (a result is past its start). -/
@[inline] def scanDigits1U (a : ByteArray) (i : USize) : USize :=
  if h : i < a.usize then (if (digitVal (a.uget i (ugetOk a i h))).isSome then scanDigitsU a (i + 1) else 0) else 0

/-- `scanIntW`, in `USize`; `0` for none. -/
@[inline] def scanIntU (a : ByteArray) (i : USize) : USize :=
  if h : i < a.usize then
    let b := a.uget i (ugetOk a i h)
    if b == 0x30 then i + 1 else if (digit19 b).isSome then scanDigitsU a (i + 1) else 0
  else 0

/-- `scanFracW`, in `USize`; `0` for none. -/
@[inline] def scanFracU (a : ByteArray) (i : USize) : USize := if byteIsU a i 0x2E then scanDigits1U a (i + 1) else i

/-- `scanExpW`, in `USize`; `0` for none. -/
@[inline] def scanExpU (a : ByteArray) (i : USize) : USize :=
  if byteIsU a i 0x65 || byteIsU a i 0x45 then scanDigits1U a (if byteIsU a (i + 1) 0x2B || byteIsU a (i + 1) 0x2D then i + 2 else i + 1) else i

/-- `scanNumW`, in `USize`; `0` for no number (a number ends after its first byte). -/
@[inline] def scanNumU (a : ByteArray) (i : USize) : USize :=
  let r1 := scanIntU a (if byteIsU a i 0x2D then i + 1 else i)
  if r1 == 0 then 0 else
  let r2 := scanFracU a r1
  if r2 == 0 then 0 else scanExpU a r2

/-- `scanNumU` with a flag, in continuation-passing style: `k` takes the end (`0` for no number) and whether the lexeme has an `E` or a `+` (so that its canonical form is not the input). Those bytes can only be in the exponent: the
exponent letter is `E`, or it is `e` and the byte after it is `+`; the flag is read from those two bytes at the end of the fraction, and only when an exponent was consumed (`r3 != r2`: a number without one, the common case, reads no byte), not by a second pass over the lexeme (`scanNumK_spec`, `LeanJsonProofs/NumFlag.lean`). -/
@[inline] def scanNumK {β : Type} (a : ByteArray) (i : USize) (k : USize → Bool → β) : β :=
  let r1 := scanIntU a (if byteIsU a i 0x2D then i + 1 else i)
  if r1 == 0 then k 0 false else
  let r2 := scanFracU a r1
  if r2 == 0 then k 0 false else
  let r3 := scanExpU a r2
  k r3 (r3 != r2 && (byteIsU a r2 0x45 || (byteIsU a r2 0x65 && byteIsU a (r2 + 1) 0x2B)))

/-- `lexOk`, in `USize`. -/
def lexOkU (a : ByteArray) (p e : USize) : Bool :=
  if h : p ≤ e ∧ 8 ≤ e - p then (if lexBad (ld64 a p) == 0 then lexOkU a (p + 8) e else false)
  else if p < e then (lexBad (ld64 a p) &&& (((1 : UInt64) <<< (8 * (e - p).toUInt64)) - 1)) == 0
  else true
termination_by e.toNat - p.toNat
decreasing_by
  obtain ⟨h1, h2⟩ := h
  have h3 := USize.le_iff_toNat_le.1 h1
  have h4 := USize.le_iff_toNat_le.1 h2
  have h6 := USize.toNat_sub_of_le _ _ h1
  have h7 := USize.toNat_lt_size e
  rw [usize_lit 8 (by decide)] at h4
  rw [usize_add_lit p 8 (by decide) (by omega)]
  omega

/-! ## The string leaf on `USize`

`strBytesW` and the multi-byte check it uses (`mbRun`, `runEnd`) work on boxed `Nat` positions and test each byte of a multi-byte character through a non-inlined `Prop` predicate: a third of the instructions of text with
non-ASCII characters (the profile of `docs/perf/results.md`, round four). `strBytesV` is `strBytesW` with the run end `runEndU` (plain ASCII words, then well-formed multi-byte characters, all on `USize` with `Bool` tests
for the continuation bytes), and the run copied by `appendBytes`; `strBytesV_eq` (`LeanJsonProofs/StrU.lean`) says it is `strBytesW`. A byte read past the end of the input is `0` (`getU`), which is no continuation byte, so a
character that runs past the end is invalid exactly as `decodeUtf8A` says. -/

/-- `Tail`, as a `Bool` (`tailB_eq`). -/
@[inline] def tailB (b : UInt8) : Bool := 0x80 ≤ b && b ≤ 0xBF

/-- `Second3`, as a `Bool` (`second3B_eq`). -/
@[inline] def second3B (a b : UInt8) : Bool := tailB b && (a != 0xE0 || 0xA0 ≤ b) && (a != 0xED || b ≤ 0x9F)

/-- `Second4`, as a `Bool` (`second4B_eq`). -/
@[inline] def second4B (a b : UInt8) : Bool := tailB b && (a != 0xF0 || 0x90 ≤ b) && (a != 0xF4 || b ≤ 0x8F)

/-- Byte `i` of `a`, `0` past the end. -/
@[inline] def getU (a : ByteArray) (i : USize) : UInt8 := if h : i < a.usize then a.uget i (ugetOk a i h) else 0

/-- The length of the well-formed multi-byte character at `q` whose first byte is `x` (at least `0x80`), `0` when there is none (`mbLenU_eq`). -/
@[inline] def mbLenU (a : ByteArray) (q : USize) (x : UInt8) : USize :=
  if 0xC2 ≤ x && x ≤ 0xDF then (if tailB (getU a (q + 1)) then 2 else 0)
  else if 0xE0 ≤ x && x ≤ 0xEF then (if second3B x (getU a (q + 1)) && tailB (getU a (q + 2)) then 3 else 0)
  else if 0xF0 ≤ x && x ≤ 0xF4 then (if second4B x (getU a (q + 1)) && tailB (getU a (q + 2)) && tailB (getU a (q + 3)) then 4 else 0)
  else 0

/-- `mbRun`, on `USize`: from `q`, where a run of plain ASCII bytes stopped, over well-formed multi-byte characters and the plain bytes after them. The guard `q < e ∧ e ≤ q2` (always true when the character is valid: `mbRunU_eq`)
is what makes the recursion terminate without a proof about the word loop. -/
def mbRunU (a : ByteArray) (q : USize) : USize :=
  if h : q < a.usize then
    if a.uget q (ugetOk a q h) < 0x80 then q
    else
      if mbLenU a q (a.uget q (ugetOk a q h)) == 0 then q
      else
        if _h2 : q < q + mbLenU a q (a.uget q (ugetOk a q h)) ∧ q + mbLenU a q (a.uget q (ugetOk a q h)) ≤ q + mbLenU a q (a.uget q (ugetOk a q h)) + plainOffU a (q + mbLenU a q (a.uget q (ugetOk a q h))) 0 then
          mbRunU a (q + mbLenU a q (a.uget q (ugetOk a q h)) + plainOffU a (q + mbLenU a q (a.uget q (ugetOk a q h))) 0)
        else q
  else q
termination_by a.size - q.toNat
decreasing_by
  have h1 := USize.lt_iff_toNat_lt.1 (‹_ ∧ _›.1)
  have h2 := USize.le_iff_toNat_le.1 (‹_ ∧ _›.2)
  have h5 := ugetOk a q h
  omega

/-- `runEnd`, on `USize`. -/
@[inline] def runEndU (a : ByteArray) (i : USize) : USize :=
  let q := i + plainOffU a i 0
  if h : q < a.usize then (if a.uget q (ugetOk a q h) < 0x80 then q else mbRunU a q) else q

/-! ### The escapes on `USize`

`decodeCharK` decodes an escape (`\n`, `\"`, `\uXXXX`, a surrogate pair) on boxed `Nat` values through `Option`-valued hex digits; `escK` is the same decoder on `USize` and `UInt32` in continuation-passing style: a hex digit is a word below 16
(`hexU`, 16 for none), a hex quad is a word below `0x10000` (`hex4U`, `0x10000` for none), the one-character escapes a word (`simpleEscU`, 0 for none); a byte past the end reads as `0` (`getU`), which is no hex digit and no escape.
`escK_eq` (`LeanJsonProofs/StrU.lean`) says it is `decodeCharK` at a backslash. -/

/-- `hexVal`, as a word: the digit, or 16 (`hexU_eq`). -/
@[inline] def hexU (b : UInt8) : UInt32 :=
  if 0x30 ≤ b && b ≤ 0x39 then (b - 0x30).toUInt32
  else if 0x41 ≤ b && b ≤ 0x46 then (b - 0x41).toUInt32 + 10
  else if 0x61 ≤ b && b ≤ 0x66 then (b - 0x61).toUInt32 + 10
  else 16

/-- `hex4At`, as a word: the four digits at `i`, or `0x10000` (`hex4U_eq`). -/
@[inline] def hex4U (a : ByteArray) (i : USize) : UInt32 :=
  let h0 := hexU (getU a i)
  let h1 := hexU (getU a (i + 1))
  let h2 := hexU (getU a (i + 2))
  let h3 := hexU (getU a (i + 3))
  if h0 < 16 && h1 < 16 && h2 < 16 && h3 < 16 then h0 * 4096 + h1 * 256 + h2 * 16 + h3 else 0x10000

/-- `simpleEsc`, as a word: the scalar, or 0 (`simpleEscU_eq`). -/
@[inline] def simpleEscU (b : UInt8) : UInt32 :=
  if b == 0x22 then 0x22 else if b == 0x5C then 0x5C else if b == 0x2F then 0x2F
  else if b == 0x62 then 0x08 else if b == 0x66 then 0x0C else if b == 0x6E then 0x0A
  else if b == 0x72 then 0x0D else if b == 0x74 then 0x09 else 0

/-- `decodeCharK` at a backslash (the byte at `p`), on `USize`: the scalar and the position after the escape go to `k`, `d` when the escape is not well formed (`escK_eq`). -/
@[inline] def escK {β : Type} (a : ByteArray) (p : USize) (k : UInt32 → USize → β) (d : β) : β :=
  let b1 := getU a (p + 1)
  if b1 == 0x75 then
    let n := hex4U a (p + 2)
    if n == 0x10000 then d
    else if n < 0xD800 || 0xE000 ≤ n then k n (p + 6)
    else if n < 0xDC00 then
      if getU a (p + 6) == 0x5C && getU a (p + 7) == 0x75 then
        let lo := hex4U a (p + 8)
        if 0xDC00 ≤ lo && lo < 0xE000 then k ((0x10000 : UInt32) + ((n - 0xD800) * 1024) + (lo - 0xDC00)) (p + 12) else d
      else d
    else d
  else
    let e := simpleEscU b1
    if e == 0 then d else k e (p + 2)

/-- `pushChar`, on the scalar's word (`pushChar_eq`). -/
def pushCharU (b : ByteArray) (v : UInt32) : ByteArray :=
  if v ≤ 0x7f then b.push v.toUInt8
  else if v ≤ 0x7ff then (b.push ((v >>> 6).toUInt8 &&& 0x1f ||| 0xc0)).push (v.toUInt8 &&& 0x3f ||| 0x80)
  else if v ≤ 0xffff then ((b.push ((v >>> 12).toUInt8 &&& 0x0f ||| 0xe0)).push ((v >>> 6).toUInt8 &&& 0x3f ||| 0x80)).push (v.toUInt8 &&& 0x3f ||| 0x80)
  else (((b.push ((v >>> 18).toUInt8 &&& 0x07 ||| 0xf0)).push ((v >>> 12).toUInt8 &&& 0x3f ||| 0x80)).push ((v >>> 6).toUInt8 &&& 0x3f ||| 0x80)).push (v.toUInt8 &&& 0x3f ||| 0x80)

/-- The end of the run at `i` (`i ≤ a.size`; any other `i` is an empty run): `runEndU`, never before `i` (`runEndG_eq`). -/
@[inline] def endG (i p0 : Nat) : Nat := if i ≤ p0 then p0 else i

theorem endG_ge (i p0 : Nat) : i ≤ endG i p0 := by
  unfold endG
  split <;> omega

@[inline, irreducible] def runEndG (a : ByteArray) (i : Nat) : Nat := endG i (if i ≤ a.size then (runEndU a i.toUSize).toNat else i)

theorem runEndG_ge (a : ByteArray) (i : Nat) : i ≤ runEndG a i := by
  unfold runEndG
  exact endG_ge _ _

/-- `strBytesW`, with the run end `runEndG`. -/
def strBytesV (a : ByteArray) (i : Nat) (b : ByteArray) : Option (ByteArray × Nat) :=
  let p := runEndG a i
  let b := if p == i then b else a.copySlice i b b.size (p - i) false
  if h : p < a.size then
    if a[p] == 0x22 then some (b, p + 1)
    else if plainAscii a[p] then strBytesV a (p + 1) (b.push a[p])
    else if a[p] == 0x5C then escK a p.toUSize (fun n j => if p < j.toNat then strBytesV a j.toNat (pushCharU b n) else none) none
    else decodeCharK a p (fun n j => if p < j then strBytesV a j (pushChar b (Char.ofNat n)) else none) none
  else none
termination_by a.size - i
decreasing_by all_goals (have := runEndG_ge a i; omega)

/-- `strW`, in `USize`. -/
@[inline] def strU (m : ByteArray) (a : ByteArray) (i : USize) (text : ByteArray) : Option (ByteArray × USize) :=
  if byteIsU a i 0x22 then
    let r := skipU m a.usize (i + 1)
    if i + 1 + plainOffU a (i + 1) 0 == r && byteIsU a r 0x22 then some (a.copySlice (i + 1).toNat text text.size (r - i - 1).toNat false, r + 1)
    else match strBytesW a (i + 1).toNat text with
      | some (t, j) => if r.toNat == j - 1 then some (t, j.toUSize) else none
      | none => none
  else none

/-- `runW`, with `USize` positions, nesting budget and fuel. -/
def runU (m : ByteArray) (f : USize) (a : ByteArray) (i : USize) (ret : Bool) (tape : ByteArray) (tw : USize) (text : ByteArray) (fst : FStack) (d : USize) : Option ByteArray :=
  if f == 0 then none else
  let f1 := f - 1
  match ret, fst with
  | false, fst =>
    if h : i < a.usize then
      let b := a.uget i (ugetOk a i h)
      if b == 0x5B then
        if d == 0 then none
        else
          let i1 := skipU m a.usize (i + 1)
          if byteIsU a i1 0x5D then runU m f1 a (i1 + 1) true (putNodeU tape tw (hdrW 5 0) 2) (tw + 2) text fst d
          else runU m f1 a i1 false (putNodeU tape tw (hdrW 5 0) 0) (tw + 2) text (.arr tw.toNat 0 fst) (d - 1)
      else if b == 0x7B then
        if d == 0 then none
        else
          let i1 := skipU m a.usize (i + 1)
          if byteIsU a i1 0x7D then runU m f1 a (i1 + 1) true (putNodeU tape tw (hdrW 6 0) 2) (tw + 2) text fst d
          else
            let tape := putNodeU tape tw (hdrW 6 0) 0
            let o := text.size
            match strU m a i1 text with
            | some (text', j) =>
              let j1 := skipU m a.usize j
              if byteIsU a j1 0x3A then
                runU m f1 a (skipU m a.usize (j1 + 1)) false (putNodeU tape (tw + 2) (hdrW 4 (text'.size - o)) (UInt64.ofNat o)) (tw + 4) text' (.obj tw.toNat 0 fst) (d - 1)
              else none
            | none => none
      else if b == 0x22 then
        let o := text.size
        match strU m a i text with
        | some (text', j) => runU m f1 a j true (putNodeU tape tw (hdrW 4 (text'.size - o)) (UInt64.ofNat o)) (tw + 2) text' fst d
        | none => none
      else if b == 0x6E then
        if byteIsU a (i + 1) 0x75 && byteIsU a (i + 2) 0x6C && byteIsU a (i + 3) 0x6C then
          if delimAtU a (i + 4) then runU m f1 a (i + 4) true (putNodeU tape tw (hdrW 0 0) 0) (tw + 2) text fst d else none
        else none
      else if b == 0x74 then
        if byteIsU a (i + 1) 0x72 && byteIsU a (i + 2) 0x75 && byteIsU a (i + 3) 0x65 then
          if delimAtU a (i + 4) then runU m f1 a (i + 4) true (putNodeU tape tw (hdrW 2 0) 0) (tw + 2) text fst d else none
        else none
      else if b == 0x66 then
        if byteIsU a (i + 1) 0x61 && byteIsU a (i + 2) 0x6C && byteIsU a (i + 3) 0x73 && byteIsU a (i + 4) 0x65 then
          if delimAtU a (i + 5) then runU m f1 a (i + 5) true (putNodeU tape tw (hdrW 1 0) 0) (tw + 2) text fst d else none
        else none
      else
        let j := scanNumU a i
        if j == 0 then none
        else if delimAtU a j then
          let o := text.size
          let text' := if lexOkU a i j then a.copySlice i.toNat text o (j - i).toNat false else pushLex a i.toNat j.toNat text
          runU m f1 a j true (putNodeU tape tw (hdrW 3 (text'.size - o)) (UInt64.ofNat o)) (tw + 2) text' fst d
        else none
    else none
  | true, .nil => if a.usize ≤ skipU m a.usize i then some (finishW tape text tw.toNat) else none
  | true, .arr at_ n rest =>
    let i1 := skipU m a.usize i
    if byteIsU a i1 0x2C then runU m f1 a (skipU m a.usize (i1 + 1)) false tape tw text (.arr at_ (n + 1) rest) d
    else if byteIsU a i1 0x5D then runU m f1 a (i1 + 1) true (st64 (st64 tape at_.toUSize (hdrW 5 (n + 1))) (at_ + 1).toUSize (UInt64.ofNat (tw.toNat - at_))) tw text rest (d + 1)
    else none
  | true, .obj at_ n rest =>
    let i1 := skipU m a.usize i
    if byteIsU a i1 0x2C then
      let o := text.size
      match strU m a (skipU m a.usize (i1 + 1)) text with
      | some (text', j) =>
        let j1 := skipU m a.usize j
        if byteIsU a j1 0x3A then
          runU m f1 a (skipU m a.usize (j1 + 1)) false (putNodeU tape tw (hdrW 4 (text'.size - o)) (UInt64.ofNat o)) (tw + 2) text' (.obj at_ (n + 1) rest) d
        else none
      | none => none
    else if byteIsU a i1 0x7D then runU m f1 a (i1 + 1) true (st64 (st64 tape at_.toUSize (hdrW 6 (n + 1))) (at_ + 1).toUSize (UInt64.ofNat (tw.toNat - at_))) tw text rest (d + 1)
    else none
termination_by f.toNat
decreasing_by all_goals exact fuel_dec f ‹_›

/-! ## `runC`: `runU` with the structural mask carried as a cursor

`skipU` answers "the first structural position at or after `j`" from nothing but `j`: every call loads the mask word, bounds-tests it and shifts by a variable count. `runC` carries the mask as a cursor instead (`VbmSimd.Cursor`):
the index `w` of a word and `b`, the bits of that word not yet consumed. The position of the next structural byte is `curPosU` (`64 * w + ctz b`, or the size when `b` is empty), consuming it is `clearLowest`, and an empty word is left
for the next non-empty one (`nextWordU`). A token ends exactly at a structural position (the opening quote of a string, an operator) or runs from one (a number, a literal: the next structural position must lie at or after the end of the
lexeme, else `runC` declines), so the next structural position after a token is the next bit of the cursor. `LeanJsonProofs/ParseC.lean`: `runC` answers `t` only when `runU` answers `t`. -/

/-- The position the cursor stands at: `64 * w + ctz b`, or `size` when no bit is left. -/
@[inline] def curPosU (size w : USize) (b : UInt64) : USize := if b == 0 then size else (w <<< 6) + (ctz b).toUSize

/-- The first word after `w` that is not empty, or `n` (the number of words) when there is none (`w` below `n`; the guard `w < w + 1` is for a wrapped `USize`, which no input reaches). -/
def nextWordU (m : ByteArray) (n w : USize) : USize :=
  let w1 := w + 1
  if _h : w < w1 ∧ w1 < n then (if ld64 m (w1 <<< 3) != 0 then w1 else nextWordU m n w1) else n
termination_by n.toNat - w.toNat
decreasing_by
  obtain ⟨h1, h2⟩ : w < w + 1 ∧ w + 1 < n := ‹_›
  have h3 : w.toNat < (w + 1).toNat := USize.lt_iff_toNat_lt.1 h1
  have h4 : (w + 1).toNat < n.toNat := USize.lt_iff_toNat_lt.1 h2
  show n.toNat - (w + 1).toNat < n.toNat - w.toNat
  omega

/-- The cursor after consuming the bit at `curPosU`, passed to `k` as the word index, the remaining bits and the position they stand at (CPS: nothing is built, `k` is inlined). -/
@[inline] def advK {β : Type} (m : ByteArray) (size : USize) (w : USize) (b : UInt64) (k : USize → UInt64 → USize → β) : β :=
  let b1 := clearLowest b
  if b1 != 0 then k w b1 ((w <<< 6) + (ctz b1).toUSize)
  else (let w1 := nextWordU m ((m.usize + 7) >>> 3) w; let b2 := ld64 m (w1 <<< 3); k w1 b2 (curPosU size w1 b2))

/-- The cursor at the first structural position of the input. -/
@[inline] def startK {β : Type} (m : ByteArray) (size : USize) (k : USize → UInt64 → USize → β) : β :=
  let b0 := ld64 m 0
  if b0 != 0 then k 0 b0 (curPosU size 0 b0)
  else (let w1 := nextWordU m ((m.usize + 7) >>> 3) 0; let b2 := ld64 m (w1 <<< 3); k w1 b2 (curPosU size w1 b2))

/-- `strU` with the position `r` of the first structural byte after the opening quote given (the cursor's). -/
@[inline] def strC (a : ByteArray) (i r : USize) (text : ByteArray) : Option (ByteArray × USize) :=
  if byteIsU a i 0x22 then
    if i + 1 + plainOffU a (i + 1) 0 == r && byteIsU a r 0x22 then some (appendBytes text a (i + 1) (r - i - 1), r + 1)
    else match strBytesV a (i + 1).toNat text with
      | some (t, j) => if r.toNat == j - 1 then some (t, j.toUSize) else none
      | none => none
  else none

/-- `runU` with the cursor `(w, b)` in place of the position (`i` is the position it stands at: `curPosU`). -/
def runC (m : ByteArray) (f : USize) (a : ByteArray) (w : USize) (b : UInt64) (i : USize) (ret : Bool) (tape : ByteArray) (tw : USize) (text : ByteArray) (stk : ByteArray) (sp : USize) (d : USize) : Option ByteArray :=
  if f == 0 then none else
  let f1 := f - 1
  let sz := a.usize
  match ret with
  | false =>
    if h : i < a.usize then
      let c := a.uget i (ugetOk a i h)
      if c == 0x5B then
        if d == 0 then none
        else
          advK m sz w b fun w1 b1 i1 =>
          if byteIsU a i1 0x5D then advK m sz w1 b1 fun w2 b2 i2 => runC m f1 a w2 b2 i2 true (putNodeU tape tw (hdrW 5 0) 2) (tw + 2) text stk sp d
          else runC m f1 a w1 b1 i1 false (putNodeU tape tw (hdrW 5 0) 0) (tw + 2) text (putNodeU stk (sp <<< 1) (tw.toUInt64 * 2) 0) (sp + 1) (d - 1)
      else if c == 0x7B then
        if d == 0 then none
        else
          advK m sz w b fun w1 b1 i1 =>
          if byteIsU a i1 0x7D then advK m sz w1 b1 fun w2 b2 i2 => runC m f1 a w2 b2 i2 true (putNodeU tape tw (hdrW 6 0) 2) (tw + 2) text stk sp d
          else
            let tape := putNodeU tape tw (hdrW 6 0) 0
            let o := text.size
            advK m sz w1 b1 fun w2 b2 i2 =>
            match strC a i1 i2 text with
            | some (text', _) =>
              advK m sz w2 b2 fun w3 b3 i3 =>
              if byteIsU a i3 0x3A then
                advK m sz w3 b3 fun w4 b4 i4 => runC m f1 a w4 b4 i4 false (putNodeU tape (tw + 2) (hdrW 4 (text'.size - o)) (UInt64.ofNat o)) (tw + 4) text' (putNodeU stk (sp <<< 1) (tw.toUInt64 * 2 + 1) 0) (sp + 1) (d - 1)
              else none
            | none => none
      else if c == 0x22 then
        let o := text.size
        advK m sz w b fun w1 b1 i1 =>
        match strC a i i1 text with
        | some (text', _) => advK m sz w1 b1 fun w2 b2 i2 => runC m f1 a w2 b2 i2 true (putNodeU tape tw (hdrW 4 (text'.size - o)) (UInt64.ofNat o)) (tw + 2) text' stk sp d
        | none => none
      else if c == 0x6E then
        if byteIsU a (i + 1) 0x75 && byteIsU a (i + 2) 0x6C && byteIsU a (i + 3) 0x6C then
          if delimAtU a (i + 4) then advK m sz w b fun w1 b1 i1 => if i1 < i + 4 then none else runC m f1 a w1 b1 i1 true (putNodeU tape tw (hdrW 0 0) 0) (tw + 2) text stk sp d else none
        else none
      else if c == 0x74 then
        if byteIsU a (i + 1) 0x72 && byteIsU a (i + 2) 0x75 && byteIsU a (i + 3) 0x65 then
          if delimAtU a (i + 4) then advK m sz w b fun w1 b1 i1 => if i1 < i + 4 then none else runC m f1 a w1 b1 i1 true (putNodeU tape tw (hdrW 2 0) 0) (tw + 2) text stk sp d else none
        else none
      else if c == 0x66 then
        if byteIsU a (i + 1) 0x61 && byteIsU a (i + 2) 0x6C && byteIsU a (i + 3) 0x73 && byteIsU a (i + 4) 0x65 then
          if delimAtU a (i + 5) then advK m sz w b fun w1 b1 i1 => if i1 < i + 5 then none else runC m f1 a w1 b1 i1 true (putNodeU tape tw (hdrW 1 0) 0) (tw + 2) text stk sp d else none
        else none
      else
        scanNumK a i fun j bad =>
        if j == 0 then none
        else if delimAtU a j then
          let o := text.size
          let text' := if bad then pushLex a i.toNat j.toNat text else appendBytes text a i (j - i)
          advK m sz w b fun w1 b1 i1 => if i1 < j then none else
          runC m f1 a w1 b1 i1 true (putNodeU tape tw (hdrW 3 (text'.size - o)) (UInt64.ofNat o)) (tw + 2) text' stk sp d
        else none
    else none
  | true =>
    if sp == 0 then (if a.usize ≤ i then some (finishW tape text tw.toNat) else none)
    else
      let top := (sp - 1) <<< 1
      let w0 := ld64 stk (top <<< 3)
      let n := ld64 stk ((top + 1) <<< 3)
      if (w0 &&& 1) == 0 then
        if byteIsU a i 0x2C then advK m sz w b fun w1 b1 i1 => runC m f1 a w1 b1 i1 false tape tw text (st64 stk (top + 1) (n + 1)) sp d
        else if byteIsU a i 0x5D then advK m sz w b fun w1 b1 i1 => runC m f1 a w1 b1 i1 true (closeU tape (w0 >>> 1).toUSize tw (hdrWu 5 (n + 1))) tw text stk (sp - 1) (d + 1)
        else none
      else
        if byteIsU a i 0x2C then
          let o := text.size
          advK m sz w b fun w1 b1 i1 =>
          advK m sz w1 b1 fun w2 b2 i2 =>
          match strC a i1 i2 text with
          | some (text', _) =>
            advK m sz w2 b2 fun w3 b3 i3 =>
            if byteIsU a i3 0x3A then
              advK m sz w3 b3 fun w4 b4 i4 => runC m f1 a w4 b4 i4 false (putNodeU tape tw (hdrW 4 (text'.size - o)) (UInt64.ofNat o)) (tw + 2) text' (st64 stk (top + 1) (n + 1)) sp d
            else none
          | none => none
        else if byteIsU a i 0x7D then advK m sz w b fun w1 b1 i1 => runC m f1 a w1 b1 i1 true (closeU tape (w0 >>> 1).toUSize tw (hdrWu 6 (n + 1))) tw text stk (sp - 1) (d + 1)
        else none
termination_by f.toNat
decreasing_by all_goals exact fuel_dec f ‹_›

/-- The number of set bits of a word (the usual shift, mask and add chain). -/
@[inline] def popcnt64 (x : UInt64) : UInt64 :=
  let x := x - ((x >>> 1) &&& (0x5555555555555555 : UInt64))
  let x := (x &&& (0x3333333333333333 : UInt64)) + ((x >>> 2) &&& (0x3333333333333333 : UInt64))
  let x := (x + (x >>> 4)) &&& (0x0f0f0f0f0f0f0f0f : UInt64)
  (x * (0x0101010101010101 : UInt64)) >>> 56

/-- The number of set bits in the words `k .. n - 1` of the mask array, added to `acc` (a capacity hint: no theorem depends on its value; the tape holds at most two words per node and every node starts at a set bit of the structural mask).
A tail call over `USize` (the first version counted in `Nat`: about 70 instructions per word). Counting four words at a time with one reduction (byte counts added before the horizontal sum) measured no better. -/
def popLoopU (m : ByteArray) (k n acc : USize) : USize :=
  if _h : k < n then popLoopU m (k + 1) n (acc + (popcnt64 (ld64 m (k <<< 3))).toUSize) else acc
termination_by n.toNat - k.toNat
decreasing_by
  have h : k < n := ‹_›
  have h3 := USize.lt_iff_toNat_lt.1 h
  have h7 := USize.toNat_lt_size n
  rw [usize_add_lit k 1 (by decide) (by omega)]
  omega

/-- The capacity hint of the tape: 16 bytes per set bit of the mask, and 4096. -/
def tapeHint (m : ByteArray) : Nat := 16 * (popLoopU m 0 (m.usize >>> 3) 0).toNat + 4096

/-- The starting tape: 4096 zero bytes in an array with room for `cap` bytes, so that the tape grows in place (`growTape` appends within the capacity) instead of by the runtime's doubling copy. The capacity is a hint that no theorem depends on. -/
def initTape (cap : Nat) : ByteArray :=
  let e := ByteArray.emptyWithCapacity cap
  zeros4k.copySlice 0 e e.size 4096 false

/-- Inputs of this many bytes (64 MiB) or more take the scalar parser: below it the tape (at most four words, 32 bytes, per fuel step, and one step per input byte plus two) and every position fit `USize` on every platform, 32 bits included (`runU_sound`). -/
@[inline] def simdLimit : Nat := 67108864

/-- The index-driven parser: the structural mask of the input (stage 1, `stage1Fast`: the AVX2 classifier where the CPU has it), then `runU`; on any decline, or an input of `simdLimit` or more, the scalar fused parser. The bytes are `parseTapeFast`'s (`parseTapeSimd_eq`, `LeanJsonProofs/ParseU.lean`, through `runU_sound` and `runW_sound`). This is the export `vbm_json_parse_tape`: it lives in this module because the C edge initialises `LeanJsonSimd.ParseSimd` (`abi/vbm_json.c`), which initialises everything it imports. -/
@[export vbm_json_parse_tape] def parseTapeSimd (a : ByteArray) : ByteArray :=
  if a.size < simdLimit then
    let m := stage1Fast a
    match (startK m a.usize fun w0 b0 i0 => runC m (a.usize + 2) a w0 b0 i0 false (initTape (tapeHint m)) 0 (ByteArray.emptyWithCapacity a.size) (initTape 8192) 0 maxDepth.toUSize) with
    | some t => t
    | none => parseTapeFast a
  else parseTapeFast a

/-- The same with `runU` (and the stateless skip), the step between `runI` and `runC` (`parseTapeU_eq`, `LeanJsonProofs/ParseU.lean`): not run by any export. -/
def parseTapeU (a : ByteArray) : ByteArray :=
  if a.size < simdLimit then
    let m := stage1Fast a
    match runU m (a.usize + 2) a (skipU m a.usize 0) false (initTape (tapeHint m)) 0 (ByteArray.emptyWithCapacity a.size) .nil maxDepth.toUSize with
    | some t => t
    | none => parseTapeFast a
  else parseTapeFast a

/-- The same with `runI`, the step between `runT` and `runW` (`parseTapeI_eq`, `LeanJsonProofs/ParseSimd.lean`): not run by any export. -/
def parseTapeI (a : ByteArray) : ByteArray :=
  if a.size < simdLimit then
    let m := stage1 a
    match runI m (a.size + 2) a (skipI m a.size 0) false ⟨.empty, .empty⟩ .nil maxDepth with
    | some t => t
    | none => parseTapeFast a
  else parseTapeFast a

end LeanJson
