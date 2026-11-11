import LeanJsonSimd.ParseSimd
import LeanJsonProofs.Stage1
import LeanJsonProofs.FastLoop
/-! # Proof: the index-driven parser is sound (`parseTapeSimd_eq`)

`docs/perf/simd-plan.md`, slices S5 to S7. `runI` is `runT` with `skipWsA` replaced by a lookup in the structural mask (`skipI`) and every error or disagreement declined. The proof is a simulation:
at every state the position `i` is *good* (`Good`): the structural machine of `LeanJson.Struct` is not inside an escape or a string there, and a scalar run does not continue into it. At a good position the first structural
position at or after it is where the whitespace skip stops (`skip_good`), and the mask of stage 1 says where that is (`skipI_eq`, from `stage1_spec` and `VbmSimdProofs.nextSet_spec`). After each token the position is good again:
after an operator (`good_op`), after a string that ends at the first structural position after its opening quote (`good_string`), after a scalar followed by a delimiter (`good_scalar`). -/
namespace LeanJsonProofs
open LeanJson VbmSimd VbmSimdProofs

/-! ## Bytes -/

theorem byteD_eq (a : ByteArray) (k : Nat) (h : k < a.size) : byteD a k = a[k] := by
  unfold byteD
  show a.data.getD k 0 = a.data[k]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h]; rfl

theorem ws_facts : ∀ c : UInt8, isWs c = true → isOp c = false ∧ (c == 0x22) = false ∧ (c == 0x5c) = false := u8_forall _ (by decide)
theorem op_facts : ∀ c : UInt8, isOp c = true → isWs c = false ∧ (c == 0x22) = false ∧ (c == 0x5c) = false := u8_forall _ (by decide)

/-! ## The good positions and the first structural position -/

/-- The machine is outside an escape and a string at `j`, and a scalar run does not continue into the byte there. (Vacuous at the end of the input.) -/
def Good (a : ByteArray) (j : Nat) : Prop :=
  j < a.size → (sAt a j).esc = false ∧ (sAt a j).str = false ∧ ((sAt a j).scal = false ∨ isNq (sAt a j) (byteD a j) = false)

/-- `r` is the first structural position at or after `j`, or the end of the input. -/
def FirstStruct (a : ByteArray) (j r : Nat) : Prop :=
  j ≤ r ∧ r ≤ a.size ∧ (∀ k, j ≤ k → k < r → isStruct a k = false) ∧ (r = a.size ∨ isStruct a r = true)

theorem sAt_succ (a : ByteArray) (k : Nat) : sAt a (k + 1) = (sStep (sAt a k) (byteD a k)).1 := rfl

theorem isStruct_ws (a : ByteArray) (k : Nat) (h : isWs (byteD a k) = true) : isStruct a k = false := by
  obtain ⟨h1, h2, h3⟩ := ws_facts _ h
  simp [isStruct, sStep, isNq, isQ, h, h1, h2]

/-- The whitespace skip stops at the first structural position, from a good position; and that position is good. -/
theorem skip_good (a : ByteArray) : ∀ d j r, a.size - j = d → j ≤ a.size → Good a j → FirstStruct a j r → skipWsA a j = r ∧ Good a r := by
  intro d
  induction d with
  | zero =>
    intro j r hd hj hg hf
    have hjr : r = j := by obtain ⟨h1, h2, _, _⟩ := hf; omega
    subst hjr
    refine ⟨?_, hg⟩
    rw [skipWsA]; simp only [show ¬ r < a.size by omega, ↓reduceDIte]
  | succ d ih =>
    intro j r hd hj hg hf
    have hjs : j < a.size := by omega
    obtain ⟨hf1, hf2, hf3, hf4⟩ := hf
    obtain ⟨he, hs, hsc⟩ := hg hjs
    rw [skipWsA]; simp only [hjs, ↓reduceDIte]
    rw [← byteD_eq a j hjs]
    by_cases hw : isWs (byteD a j) = true
    · simp only [hw, ↓reduceIte]
      have hnj : isStruct a j = false := isStruct_ws a j hw
      have hrj : j + 1 ≤ r := by
        rcases Nat.lt_or_eq_of_le hf1 with h | h
        · omega
        · subst h
          rcases hf4 with h4 | h4
          · omega
          · rw [hnj] at h4; exact absurd h4 (by simp)
      obtain ⟨hw1, hw2, hw3⟩ := ws_facts _ hw
      refine ih (j + 1) r (by omega) (by omega) ?_ ⟨hrj, hf2, fun k hk hk' => hf3 k (by omega) hk', hf4⟩
      intro _
      rw [sAt_succ]
      simp only [sStep, he, hs, isNq, isQ, hw, hw1, hw2, hw3]
      simp
    · have hw' : isWs (byteD a j) = false := by simpa using hw
      simp only [hw, Bool.false_eq_true, ↓reduceIte]
      have hst : isStruct a j = true := by
        unfold isStruct
        simp only [sStep, he, hs]
        by_cases ho : isOp (byteD a j) = true
        · simp [ho]
        · have ho' : isOp (byteD a j) = false := by simpa using ho
          by_cases hq : (byteD a j == 0x22) = true
          · simp [isQ, hq, he]
          · have hq' : (byteD a j == 0x22) = false := by simpa using hq
            have hnq : isNq (sAt a j) (byteD a j) = true := by simp [isNq, isQ, he, ho', hw', hq']
            have hsc' : (sAt a j).scal = false := by
              rcases hsc with h | h
              · exact h
              · rw [hnq] at h; exact absurd h (by simp)
            simp [isQ, hq', hnq, hsc', he]
      have hrj : r = j := by
        refine Classical.byContradiction fun hne => ?_
        have := hf3 j (Nat.le_refl _) (by omega)
        rw [hst] at this; exact absurd this (by simp)
      subst hrj
      exact ⟨rfl, fun _ => ⟨he, hs, hsc⟩⟩

/-! ## After a token the position is good again -/

/-- After an operator byte. -/
theorem good_op (a : ByteArray) (i : Nat) (hg : Good a i) (hi : i < a.size) (ho : isOp (byteD a i) = true) : Good a (i + 1) := by
  intro _
  obtain ⟨he, hs, _⟩ := hg hi
  obtain ⟨h1, h2, h3⟩ := op_facts _ ho
  rw [sAt_succ]
  simp only [sStep, he, hs, isNq, isQ, ho, h1, h2, h3]
  simp

/-- After a string: its opening quote is at `i` and the first structural position after it, `r`, is its closing quote. -/
theorem good_string (a : ByteArray) (i r : Nat) (hg : Good a i) (hi : i < a.size) (hq : byteD a i = 0x22) (hf : FirstStruct a (i + 1) r) (hr : r < a.size) : Good a (r + 1) := by
  obtain ⟨he, hs, _⟩ := hg hi
  obtain ⟨hf1, hf2, hf3, hf4⟩ := hf
  -- the state after the opening quote: in a string
  have hS : (sAt a (i + 1)).str = true := by
    rw [sAt_succ]; simp [sStep, he, hs, isQ, hq]
  -- no structural position before `r`: the string stays open
  have hrun : ∀ t, i + 1 + t ≤ r → (sAt a (i + 1 + t)).str = true := by
    intro t
    induction t with
    | zero => intro _; exact hS
    | succ t ih =>
      intro ht
      have ih' := ih (by omega)
      have hns := hf3 (i + 1 + t) (by omega) (by omega)
      have hnq : isQ (sAt a (i + 1 + t)) (byteD a (i + 1 + t)) = false := by
        refine Classical.byContradiction fun hh => ?_
        have hh' : isQ (sAt a (i + 1 + t)) (byteD a (i + 1 + t)) = true := by simpa using hh
        have : isStruct a (i + 1 + t) = true := by simp [isStruct, sStep, hh']
        rw [hns] at this; exact absurd this (by simp)
      rw [show i + 1 + (t + 1) = (i + 1 + t) + 1 by omega, sAt_succ]
      simp [sStep, ih', hnq]
  have hstr := hrun (r - (i + 1)) (by omega)
  rw [show i + 1 + (r - (i + 1)) = r by omega] at hstr
  have hst : isStruct a r = true := by
    rcases hf4 with h | h
    · omega
    · exact h
  have hq' : isQ (sAt a r) (byteD a r) = true := by
    unfold isStruct at hst
    simp only [sStep, hstr] at hst
    simpa using hst
  intro _
  rw [sAt_succ]
  have hq2 : (byteD a r == 0x22) = true := by simp [isQ] at hq'; simpa using hq'.1
  have hq3 : (byteD a r == 0x5c) = false := by
    have : byteD a r = 0x22 := by simpa using hq2
    rw [this]; decide
  simp only [sStep, hstr, hq', hq3, isNq]
  simp

/-- The bytes a scalar token may consist of: not whitespace, not an operator, not a quote, not a backslash. -/
def scalByte (c : UInt8) : Bool := !(isWs c || isOp c || c == 0x22 || c == 0x5c)

/-- After a scalar `a[i..j)` that is followed by a delimiter. -/
theorem good_scalar (a : ByteArray) (i j : Nat) (hg : Good a i) (hij : i < j) (hj : j ≤ a.size) (hb : ∀ p, i ≤ p → p < j → scalByte (byteD a p) = true)
    (hd : delimAt a j = true) : Good a j := by
  have hrun : ∀ t, i + 1 + t ≤ j → (sAt a (i + 1 + t)).esc = false ∧ (sAt a (i + 1 + t)).str = false ∧ (sAt a (i + 1 + t)).scal = true := by
    intro t
    induction t with
    | zero =>
      intro _
      obtain ⟨he, hs, _⟩ := hg (by omega)
      have hc := hb i (Nat.le_refl _) hij
      simp only [scalByte, Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hc
      obtain ⟨⟨⟨hw, ho⟩, h22⟩, h5c⟩ := hc
      rw [sAt_succ]
      simp [sStep, he, hs, isNq, isQ, hw, ho, h22, h5c]
    | succ t ih =>
      intro ht
      obtain ⟨he, hs, hsc⟩ := ih (by omega)
      have hc := hb (i + 1 + t) (by omega) (by omega)
      simp only [scalByte, Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hc
      obtain ⟨⟨⟨hw, ho⟩, h22⟩, h5c⟩ := hc
      rw [show i + 1 + (t + 1) = (i + 1 + t) + 1 by omega, sAt_succ]
      simp [sStep, he, hs, isNq, isQ, hw, ho, h22, h5c]
  intro hjs
  have := hrun (j - (i + 1)) (by omega)
  rw [show i + 1 + (j - (i + 1)) = j by omega] at this
  obtain ⟨he, hs, _⟩ := this
  refine ⟨he, hs, Or.inr ?_⟩
  unfold delimAt at hd
  rw [show byteAt a j = some a[j] from by simp [byteAt, hjs]] at hd
  simp only [Bool.or_eq_true] at hd
  rw [byteD_eq a j hjs]
  simp only [isNq, isQ, he]
  rcases hd with (h | h) | h
  · simp [h]
  · simp [h]
  · simp [h]

/-! ## The skip, from the mask -/

/-- `skipI` of the mask of stage 1 is the first structural position at or after `j` (or the end). -/
theorem skipI_spec (a : ByteArray) (h : a.size < 2 ^ 31) (j : Nat) (hj : j ≤ a.size) : FirstStruct a j (skipI (stage1 a) a.size j) := by
  obtain ⟨hsz, hbit⟩ := stage1_spec a h
  have hwc : wordCount (stage1 a) = (a.size + 63) / 64 := by unfold wordCount; rw [hsz]; omega
  have hbp : ∀ k, k < 64 * wordCount (stage1 a) → bitPos (wordAt (stage1 a)) k = (isStruct a k && decide (k < a.size)) := by
    intro k hk
    have hl : wordAt (stage1 a) (k / 64) = ld64Model (stage1 a) (8 * (k / 64)) := ld64_toUSize _ _ (by omega)
    unfold bitPos
    rw [hl, hbit (k / 64) (by omega) (k % 64) (by omega), show 64 * (k / 64) + k % 64 = k by omega]
  obtain ⟨n1, n2, n3, n4⟩ := nextSet_spec (stage1 a) j (by omega)
  unfold skipI
  simp only []
  by_cases hr : nextSet (stage1 a) j < a.size
  · simp only [hr, ↓reduceIte]
    refine ⟨n1, by omega, fun k hk hk' => ?_, Or.inr ?_⟩
    · have := n3 k hk hk'
      rw [hbp k (by omega)] at this
      have hks : decide (k < a.size) = true := by simp; omega
      rw [hks] at this; simpa using this
    · rcases n4 with h4 | h4
      · omega
      · rw [hbp _ (by omega)] at h4; exact (by simpa using h4 : _ ∧ _).1
  · simp only [hr, ↓reduceIte]
    refine ⟨by omega, Nat.le_refl _, fun k hk hk' => ?_, Or.inl rfl⟩
    have := n3 k hk (by omega)
    rw [hbp k (by omega)] at this
    have hks : decide (k < a.size) = true := by simp; omega
    rw [hks] at this; simpa using this

theorem skip_spec (a : ByteArray) (h : a.size < 2 ^ 31) (j : Nat) (hj : j ≤ a.size) (hg : Good a j) :
    skipWsA a j = skipI (stage1 a) a.size j ∧ Good a (skipI (stage1 a) a.size j) ∧ j ≤ skipI (stage1 a) a.size j ∧ skipI (stage1 a) a.size j ≤ a.size := by
  have hf := skipI_spec a h j hj
  obtain ⟨h1, h2⟩ := skip_good a _ j _ rfl hj hg hf
  exact ⟨h1, h2, hf.1, hf.2.1⟩

/-! ## The leaves: where they end, and what they consumed -/

theorem strBytes_end (a : ByteArray) : ∀ d i b b' j, a.size - i = d → strBytes a i b = some (b', j) → 0 < j ∧ j - 1 < a.size := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
    intro i b b' j hd h
    rw [strBytes] at h
    by_cases hi : i < a.size
    · simp only [hi, ↓reduceDIte] at h
      by_cases h22 : (a[i] == 0x22) = true
      · simp only [h22, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
        omega
      · simp only [h22, Bool.false_eq_true, ↓reduceIte] at h
        by_cases hp : plainAscii a[i] = true
        · simp only [hp, ↓reduceIte] at h
          exact ih (a.size - (i + 1)) (by omega) (i + 1) _ b' j rfl h
        · simp only [hp, Bool.false_eq_true, ↓reduceIte] at h
          cases hd' : decodeCharA a i with
          | none => simp [hd'] at h
          | some nj =>
            obtain ⟨n, j'⟩ := nj
            simp only [hd'] at h
            by_cases hij : i < j'
            · simp only [hij, ↓reduceIte] at h
              by_cases hj' : j' ≤ a.size
              · exact ih (a.size - j') (by omega) j' _ b' j rfl h
              · have : strBytes a j' (pushChar b (Char.ofNat n)) = none := by rw [strBytes]; simp [show ¬ j' < a.size by omega]
                rw [this] at h; exact absurd h (by simp)
            · simp [hij] at h
    · simp [hi] at h

theorem strNode_end (s : TapeBuf) (kind : Nat) (a : ByteArray) (i : Nat) (s' : TapeBuf) (j : Nat) (h : s.strNode kind a i = some (s', j)) :
    byteIs a i 0x22 = true ∧ 0 < j ∧ j - 1 < a.size := by
  obtain ⟨tape, text⟩ := s
  unfold TapeBuf.strNode at h
  by_cases hq : byteIs a i 0x22 = true
  · simp only [hq, ↓reduceIte] at h
    cases hb : strBytes a (i + 1) text with
    | none => simp [hb] at h
    | some tj =>
      obtain ⟨t, j'⟩ := tj
      simp only [hb, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, hj⟩ := h
      subst hj
      exact ⟨hq, strBytes_end a _ (i + 1) text t j' rfl hb⟩
  · simp [hq] at h

theorem litA_bytes (a : ByteArray) (l : Bytes) : ∀ i j, i ≤ a.size → litA a i l = some j → j ≤ a.size ∧ ∀ p, i ≤ p → p < j → byteD a p ∈ l := by
  induction l with
  | nil =>
    intro i j hi h
    simp only [litA, Option.some.injEq] at h
    subst h
    exact ⟨hi, fun p h1 h2 => by omega⟩
  | cons x xs ih =>
    intro i j hi h
    simp only [litA] at h
    by_cases hx : byteIs a i x = true
    · simp only [hx, ↓reduceIte] at h
      have hlt : i < a.size := by
        unfold byteIs at hx
        by_cases hh : i < a.size
        · exact hh
        · simp [hh] at hx
      have hax : a[i] = x := by
        unfold byteIs at hx
        simp only [hlt, ↓reduceDIte, beq_iff_eq] at hx
        exact hx
      obtain ⟨hj, hp⟩ := ih (i + 1) j (by omega) h
      refine ⟨hj, fun p hp1 hp2 => ?_⟩
      by_cases hpi : p = i
      · subst hpi; rw [byteD_eq a p hlt, hax]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hp p (by omega) hp2)
    · simp [hx] at h

/-! ## Numbers: the bytes a number consumes are number bytes -/

/-- The bytes of a number: digits, `-`, `+`, `.`, `e`, `E`. -/
def numByte (c : UInt8) : Bool := (decide (0x30 ≤ c.toNat) && decide (c.toNat ≤ 0x39)) || c == 0x2D || c == 0x2B || c == 0x2E || c == 0x65 || c == 0x45

theorem numByte_scal : ∀ c : UInt8, numByte c = true → scalByte c = true := u8_forall _ (by decide)

/-- `[i, j)` is a stretch of number bytes within the input (when `i` is). -/
def NumRun (a : ByteArray) (i j : Nat) : Prop := i ≤ j ∧ (i ≤ a.size → j ≤ a.size) ∧ ∀ p, i ≤ p → p < j → numByte (byteD a p) = true

theorem NumRun.refl (a : ByteArray) (i : Nat) : NumRun a i i := ⟨Nat.le_refl _, id, fun p h1 h2 => by omega⟩

theorem NumRun.trans {a : ByteArray} {i j k : Nat} (h1 : NumRun a i j) (h2 : NumRun a j k) : NumRun a i k :=
  ⟨Nat.le_trans h1.1 h2.1, fun hi => h2.2.1 (h1.2.1 hi), fun p hp1 hp2 => by
    by_cases hp : p < j
    · exact h1.2.2 p hp1 hp
    · exact h2.2.2 p (by omega) hp2⟩

theorem NumRun.one {a : ByteArray} {i : Nat} (hi : i < a.size) (hb : numByte (byteD a i) = true) : NumRun a i (i + 1) :=
  ⟨by omega, fun _ => by omega, fun p h1 h2 => by
    have : p = i := by omega
    subst this; exact hb⟩

theorem byteIs_spec (a : ByteArray) (i : Nat) (c : UInt8) (h : byteIs a i c = true) : i < a.size ∧ byteD a i = c := by
  unfold byteIs at h
  by_cases hi : i < a.size
  · simp only [hi, ↓reduceDIte, beq_iff_eq] at h
    exact ⟨hi, by rw [byteD_eq a i hi]; exact h⟩
  · simp [hi] at h

theorem byteAt_spec (a : ByteArray) (i : Nat) (b : UInt8) (h : byteAt a i = some b) : i < a.size ∧ byteD a i = b := by
  unfold byteAt at h
  by_cases hi : i < a.size
  · simp only [hi, ↓reduceDIte, Option.some.injEq] at h
    exact ⟨hi, by rw [byteD_eq a i hi]; exact h⟩
  · simp [hi] at h

theorem digit_numByte (c : UInt8) (h : (digitVal c).isSome = true) : numByte c = true := by
  unfold digitVal at h
  by_cases hh : 0x30 ≤ c.toNat ∧ c.toNat ≤ 0x39
  · simp [numByte, hh.1, hh.2]
  · simp [hh] at h

theorem digit19_numByte (c : UInt8) (h : (digit19 c).isSome = true) : numByte c = true := by
  unfold digit19 at h
  by_cases hh : 0x31 ≤ c.toNat ∧ c.toNat ≤ 0x39
  · simp [numByte, show 0x30 ≤ c.toNat by omega, hh.2]
  · simp [hh] at h

theorem scanDigits_run (a : ByteArray) : ∀ d i, a.size - i = d → NumRun a i (scanDigits a i) := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
    intro i hd
    rw [scanDigits]
    by_cases hi : i < a.size
    · simp only [hi, ↓reduceDIte]
      by_cases hdig : (digitVal a[i]).isSome = true
      · simp only [hdig, ↓reduceIte]
        have hb : numByte (byteD a i) = true := by rw [byteD_eq a i hi]; exact digit_numByte _ hdig
        exact (NumRun.one hi hb).trans (ih (a.size - (i + 1)) (by omega) (i + 1) rfl)
      · simp only [hdig, Bool.false_eq_true, ↓reduceIte]
        exact NumRun.refl a i
    · simp only [hi, ↓reduceDIte]
      exact NumRun.refl a i

theorem scanDigits1_run (a : ByteArray) (i j : Nat) (h : scanDigits1 a i = some j) : NumRun a i j := by
  unfold scanDigits1 at h
  cases hb : byteAt a i with
  | none => simp [hb] at h
  | some b =>
    simp only [hb] at h
    by_cases hdig : (digitVal b).isSome = true
    · simp only [hdig, ↓reduceIte, Option.some.injEq] at h
      subst h
      obtain ⟨hi, hbi⟩ := byteAt_spec a i b hb
      have hnb : numByte (byteD a i) = true := by rw [hbi]; exact digit_numByte _ hdig
      exact (NumRun.one hi hnb).trans (scanDigits_run a _ (i + 1) rfl)
    · simp [hdig] at h

theorem scanInt_run (a : ByteArray) (i j : Nat) (h : scanInt a i = some j) : NumRun a i j := by
  unfold scanInt at h
  cases hb : byteAt a i with
  | none => simp [hb] at h
  | some b =>
    simp only [hb] at h
    obtain ⟨hi, hbi⟩ := byteAt_spec a i b hb
    by_cases h0 : (b == 0x30) = true
    · simp only [h0, ↓reduceIte, Option.some.injEq] at h
      subst h
      have : b = 0x30 := by simpa using h0
      exact NumRun.one hi (by rw [hbi, this]; decide)
    · simp only [h0, Bool.false_eq_true, ↓reduceIte] at h
      by_cases h19 : (digit19 b).isSome = true
      · simp only [h19, ↓reduceIte, Option.some.injEq] at h
        subst h
        exact (NumRun.one hi (by rw [hbi]; exact digit19_numByte _ h19)).trans (scanDigits_run a _ (i + 1) rfl)
      · simp [h19] at h

theorem scanFrac_run (a : ByteArray) (i j : Nat) (h : scanFrac a i = some j) : NumRun a i j := by
  unfold scanFrac at h
  by_cases hd : byteIs a i 0x2E = true
  · simp only [hd, ↓reduceIte] at h
    obtain ⟨hi, hbi⟩ := byteIs_spec a i _ hd
    exact (NumRun.one hi (by rw [hbi]; decide)).trans (scanDigits1_run a _ j h)
  · simp only [hd, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
    subst h; exact NumRun.refl a i

theorem scanExp_run (a : ByteArray) (i j : Nat) (h : scanExp a i = some j) : NumRun a i j := by
  unfold scanExp at h
  by_cases hd : (byteIs a i 0x65 || byteIs a i 0x45) = true
  · simp only [hd, ↓reduceIte] at h
    have hi : i < a.size ∧ numByte (byteD a i) = true := by
      rcases Bool.or_eq_true_iff.mp hd with h1 | h1
      · obtain ⟨x, y⟩ := byteIs_spec a i _ h1; exact ⟨x, by rw [y]; decide⟩
      · obtain ⟨x, y⟩ := byteIs_spec a i _ h1; exact ⟨x, by rw [y]; decide⟩
    refine (NumRun.one hi.1 hi.2).trans ?_
    by_cases hs : (byteIs a (i + 1) 0x2B || byteIs a (i + 1) 0x2D) = true
    · simp only [hs, ↓reduceIte] at h
      have hs' : i + 1 < a.size ∧ numByte (byteD a (i + 1)) = true := by
        rcases Bool.or_eq_true_iff.mp hs with h1 | h1
        · obtain ⟨x, y⟩ := byteIs_spec a (i + 1) _ h1; exact ⟨x, by rw [y]; decide⟩
        · obtain ⟨x, y⟩ := byteIs_spec a (i + 1) _ h1; exact ⟨x, by rw [y]; decide⟩
      exact (NumRun.one hs'.1 hs'.2).trans (scanDigits1_run a _ j h)
    · simp only [hs, Bool.false_eq_true, ↓reduceIte] at h
      exact scanDigits1_run a _ j h
  · simp only [hd, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
    subst h; exact NumRun.refl a i

theorem scanNum_run (a : ByteArray) (i j : Nat) (h : scanNum a i = some j) : NumRun a i j := by
  unfold scanNum at h
  have hm : NumRun a i (if byteIs a i 0x2D then i + 1 else i) := by
    by_cases hd : byteIs a i 0x2D = true
    · simp only [hd, ↓reduceIte]
      obtain ⟨hi, hbi⟩ := byteIs_spec a i _ hd
      exact NumRun.one hi (by rw [hbi]; decide)
    · simp only [hd, Bool.false_eq_true, ↓reduceIte]; exact NumRun.refl a i
  cases h1 : scanInt a (if byteIs a i 0x2D then i + 1 else i) with
  | none => simp [h1] at h
  | some i1 =>
    simp only [h1] at h
    cases h2 : scanFrac a i1 with
    | none => simp [h2] at h
    | some i2 =>
      simp only [h2] at h
      exact ((hm.trans (scanInt_run a _ _ h1)).trans (scanFrac_run a _ _ h2)).trans (scanExp_run a _ _ h)

/-! ## The tokens, against the machine -/

/-- The invariant at every state of the simulation: the position is inside the input and good. -/
def Inv (a : ByteArray) (i : Nat) : Prop := i ≤ a.size ∧ Good a i

theorem scanNum_adv (a : ByteArray) (i j : Nat) (h : scanNum a i = some j) : i < j := by
  have := scanNum_eq a i
  rw [h] at this
  obtain ⟨⟨p, k⟩, hp, e⟩ := Option.map_eq_some_iff.mp this.symm
  simp only at e
  subst e
  exact parseNumA_adv hp

theorem good_num (a : ByteArray) (i j : Nat) (hi : i < a.size) (hg : Good a i) (hs : scanNum a i = some j) (hd : delimAt a j = true) : j ≤ a.size ∧ Good a j := by
  obtain ⟨r1, r2, r3⟩ := scanNum_run a i j (by simpa using hs)
  have hj := r2 (by omega)
  exact ⟨hj, good_scalar a i j hg (scanNum_adv a i j hs) hj (fun p hp1 hp2 => numByte_scal _ (r3 p hp1 hp2)) hd⟩

theorem lit_scal (l : Bytes) (hl : ∀ c, c ∈ l → scalByte c = true) (a : ByteArray) (i j : Nat) (hi : i < a.size) (hx : scalByte (byteD a i) = true) (hg : Good a i)
    (hs : litA a (i + 1) l = some j) (hd : delimAt a j = true) : j ≤ a.size ∧ Good a j := by
  obtain ⟨hj, hb⟩ := litA_bytes a l (i + 1) j (by omega) hs
  have hadv := (litA_ge a l (i + 1) j hs).1
  by_cases hnil : l = []
  · subst hnil
    simp only [litA, Option.some.injEq] at hs
    subst hs
    exact ⟨hj, good_scalar a i (i + 1) hg (by omega) hj (fun p hp1 hp2 => by
      have : p = i := by omega
      subst this; exact hx) hd⟩
  · have hlt : i + 1 < j := (litA_ge a l (i + 1) j hs).2 hnil
    exact ⟨hj, good_scalar a i j hg (by omega) hj (fun p hp1 hp2 => by
      by_cases hpi : p = i
      · subst hpi; exact hx
      · exact hl _ (hb p (by omega) hp2)) hd⟩

theorem strNodeI_sound (a : ByteArray) (hsz : a.size < 2 ^ 31) (s : TapeBuf) (kind i : Nat) (hv : Inv a i) (s' : TapeBuf) (j : Nat)
    (h : s.strNodeI kind (stage1 a) a i = some (s', j)) : s.strNode kind a i = some (s', j) ∧ Inv a j := by
  unfold TapeBuf.strNodeI at h
  cases hn : s.strNode kind a i with
  | none => simp [hn] at h
  | some sj =>
    obtain ⟨s'', j0⟩ := sj
    simp only [hn] at h
    by_cases hc : (skipI (stage1 a) a.size (i + 1) == j0 - 1) = true
    · simp only [hc, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hs'', hj0⟩ := h
      subst hs'' hj0
      refine ⟨rfl, ?_⟩
      obtain ⟨hq, hpos, hlt⟩ := strNode_end s kind a i s'' j0 hn
      obtain ⟨hi1, hq'⟩ := byteIs_spec a i _ hq
      have hfs := skipI_spec a hsz (i + 1) (by omega)
      have hr : skipI (stage1 a) a.size (i + 1) = j0 - 1 := by simpa using hc
      rw [hr] at hfs
      exact ⟨by omega, good_string a i (j0 - 1) hv.2 hi1 hq' hfs hlt |> fun g => by rwa [show j0 - 1 + 1 = j0 by omega] at g⟩
    · simp [hc] at h

theorem keyNodeI_sound (a : ByteArray) (hsz : a.size < 2 ^ 31) (s : TapeBuf) (i : Nat) (hv : Inv a i) (s' : TapeBuf) (k : Nat)
    (h : s.keyNodeI (stage1 a) a i = some (s', k)) : s.keyNode a i = some (s', k) ∧ Inv a k := by
  unfold TapeBuf.keyNodeI at h
  cases hn : s.strNodeI kindStr (stage1 a) a i with
  | none => simp [hn] at h
  | some sj =>
    obtain ⟨s'', j⟩ := sj
    simp only [hn] at h
    obtain ⟨hn1, hj⟩ := strNodeI_sound a hsz s kindStr i hv s'' j hn
    obtain ⟨e1, e2, e3, e4⟩ := skip_spec a hsz j hj.1 hj.2
    by_cases hc : byteIs a (skipI (stage1 a) a.size j) 0x3A = true
    · simp only [hc, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hs'', hk⟩ := h
      subst hs'' hk
      obtain ⟨hj1, hbj1⟩ := byteIs_spec a _ _ hc
      have hop : isOp (byteD a (skipI (stage1 a) a.size j)) = true := by rw [hbj1]; decide
      have hg2 := good_op a _ e2 hj1 hop
      obtain ⟨f1, f2, f3, f4⟩ := skip_spec a hsz (skipI (stage1 a) a.size j + 1) (by omega) hg2
      refine ⟨?_, f4, f2⟩
      unfold TapeBuf.keyNode
      rw [hn1]
      simp only [e1, hc, ↓reduceIte, f1]
    · simp [hc] at h

/-! ## The simulation -/

theorem lit_null : ∀ c, c ∈ ([0x75, 0x6C, 0x6C] : Bytes) → scalByte c = true := by decide
theorem lit_true : ∀ c, c ∈ ([0x72, 0x75, 0x65] : Bytes) → scalByte c = true := by decide
theorem lit_false : ∀ c, c ∈ ([0x61, 0x6C, 0x73, 0x65] : Bytes) → scalByte c = true := by decide

theorem isOp_of_beq (b c : UInt8) (hc : isOp c = true) (h : (b == c) = true) : isOp b = true := by
  have : b = c := by simpa using h
  rw [this]; exact hc

/-- When `runI` answers, `runT` gives the same bytes. -/
theorem runI_sound (a : ByteArray) (hsz : a.size < 2 ^ 31) : ∀ f i ret tb fst d t, Inv a i → runI (stage1 a) f a i ret tb fst d = some t → runT f a i ret tb fst d = t := by
  intro f
  induction f with
  | zero => intro i ret tb fst d t _ h; simp [runI] at h
  | succ f ih =>
    intro i ret tb fst d t hv h
    cases ret with
    | false =>
      rw [runI] at h
      rw [runT]
      cases hb : byteAt a i with
      | none => simp [hb] at h
      | some b =>
        simp only [hb] at h ⊢
        obtain ⟨hi, hbi⟩ := byteAt_spec a i b hb
        by_cases h5b : (b == 0x5B) = true
        · simp only [h5b, ↓reduceIte] at h ⊢
          have hop : isOp (byteD a i) = true := by rw [hbi]; exact isOp_of_beq b 0x5B (by decide) h5b
          by_cases hd : (d == 0) = true
          · simp [hd] at h
          · simp only [hd, Bool.false_eq_true, ↓reduceIte] at h ⊢
            obtain ⟨e1, e2, e3, e4⟩ := skip_spec a hsz (i + 1) (by omega) (good_op a i hv.2 hi hop)
            rw [← e1] at e2 e3 e4 h
            by_cases h5d : byteIs a (skipWsA a (i + 1)) 0x5D = true
            · simp only [h5d, ↓reduceIte] at h ⊢
              obtain ⟨hl, hb5⟩ := byteIs_spec a _ _ h5d
              exact ih _ true _ _ _ t ⟨by omega, good_op a _ e2 hl (by rw [hb5]; decide)⟩ h
            · simp only [h5d, Bool.false_eq_true, ↓reduceIte] at h ⊢
              exact ih _ false _ _ _ t ⟨e4, e2⟩ h
        · simp only [h5b, Bool.false_eq_true, ↓reduceIte] at h ⊢
          by_cases h7b : (b == 0x7B) = true
          · simp only [h7b, ↓reduceIte] at h ⊢
            have hop : isOp (byteD a i) = true := by rw [hbi]; exact isOp_of_beq b 0x7B (by decide) h7b
            by_cases hd : (d == 0) = true
            · simp [hd] at h
            · simp only [hd, Bool.false_eq_true, ↓reduceIte] at h ⊢
              obtain ⟨e1, e2, e3, e4⟩ := skip_spec a hsz (i + 1) (by omega) (good_op a i hv.2 hi hop)
              rw [← e1] at e2 e3 e4 h
              by_cases h7d : byteIs a (skipWsA a (i + 1)) 0x7D = true
              · simp only [h7d, ↓reduceIte] at h ⊢
                obtain ⟨hl, hb7⟩ := byteIs_spec a _ _ h7d
                exact ih _ true _ _ _ t ⟨by omega, good_op a _ e2 hl (by rw [hb7]; decide)⟩ h
              · simp only [h7d, Bool.false_eq_true, ↓reduceIte] at h ⊢
                cases hk : (tb.node kindObj 0 0).keyNodeI (stage1 a) a (skipWsA a (i + 1)) with
                | none => simp [hk] at h
                | some tj =>
                  obtain ⟨tb', j⟩ := tj
                  obtain ⟨hk1, hk2⟩ := keyNodeI_sound a hsz _ _ ⟨e4, e2⟩ tb' j hk
                  simp only [hk, hk1] at h ⊢
                  exact ih _ false _ _ _ t hk2 h
          · simp only [h7b, Bool.false_eq_true, ↓reduceIte] at h ⊢
            by_cases h22 : (b == 0x22) = true
            · simp only [h22, ↓reduceIte] at h ⊢
              cases hs : tb.strNodeI kindStr (stage1 a) a i with
              | none => simp [hs] at h
              | some tj =>
                obtain ⟨tb', j⟩ := tj
                obtain ⟨hs1, hs2⟩ := strNodeI_sound a hsz _ kindStr i hv tb' j hs
                simp only [hs, hs1] at h ⊢
                exact ih _ true _ _ _ t hs2 h
            · simp only [h22, Bool.false_eq_true, ↓reduceIte] at h ⊢
              have hlit : ∀ (c : UInt8) (l : Bytes) (k : Nat), b = c → scalByte c = true → (∀ x, x ∈ l → scalByte x = true) → litA a (i + 1) l = some k →
                  delimAt a k = true → k ≤ a.size ∧ Good a k := by
                intro c l k hbc hsc hl hk hdl
                exact lit_scal l hl a i k hi (by rw [hbi, hbc]; exact hsc) hv.2 hk hdl
              by_cases h6e : (b == 0x6E) = true
              · simp only [h6e, ↓reduceIte] at h ⊢
                cases hl : litA a (i + 1) [0x75, 0x6C, 0x6C] with
                | none => simp [hl] at h
                | some k =>
                  simp only [hl] at h ⊢
                  by_cases hdl : delimAt a k = true
                  · simp only [hdl, ↓reduceIte] at h
                    exact ih _ true _ _ _ t (hlit 0x6E _ k (by simpa using h6e) (by decide) lit_null hl hdl) h
                  · simp [hdl] at h
              · simp only [h6e, Bool.false_eq_true, ↓reduceIte] at h ⊢
                by_cases h74 : (b == 0x74) = true
                · simp only [h74, ↓reduceIte] at h ⊢
                  cases hl : litA a (i + 1) [0x72, 0x75, 0x65] with
                  | none => simp [hl] at h
                  | some k =>
                    simp only [hl] at h ⊢
                    by_cases hdl : delimAt a k = true
                    · simp only [hdl, ↓reduceIte] at h
                      exact ih _ true _ _ _ t (hlit 0x74 _ k (by simpa using h74) (by decide) lit_true hl hdl) h
                    · simp [hdl] at h
                · simp only [h74, Bool.false_eq_true, ↓reduceIte] at h ⊢
                  by_cases h66 : (b == 0x66) = true
                  · simp only [h66, ↓reduceIte] at h ⊢
                    cases hl : litA a (i + 1) [0x61, 0x6C, 0x73, 0x65] with
                    | none => simp [hl] at h
                    | some k =>
                      simp only [hl] at h ⊢
                      by_cases hdl : delimAt a k = true
                      · simp only [hdl, ↓reduceIte] at h
                        exact ih _ true _ _ _ t (hlit 0x66 _ k (by simpa using h66) (by decide) lit_false hl hdl) h
                      · simp [hdl] at h
                  · simp only [h66, Bool.false_eq_true, ↓reduceIte] at h ⊢
                    cases hn : scanNum a i with
                    | none => simp [hn] at h
                    | some k =>
                      simp only [hn] at h ⊢
                      by_cases hdl : delimAt a k = true
                      · simp only [hdl, ↓reduceIte] at h
                        exact ih _ true _ _ _ t (good_num a i k hi hv.2 hn hdl) h
                      · simp [hdl] at h
    | true =>
      cases fst with
      | nil =>
        rw [runI] at h
        rw [runT]
        obtain ⟨e1, _, _, _⟩ := skip_spec a hsz i hv.1 hv.2
        rw [← e1] at h
        by_cases hc : a.size ≤ skipWsA a i
        · simp only [hc, ↓reduceIte, Option.some.injEq] at h ⊢
          exact h
        · simp [hc] at h
      | arr at_ n rest =>
        rw [runI] at h
        rw [runT]
        obtain ⟨e1, e2, e3, e4⟩ := skip_spec a hsz i hv.1 hv.2
        rw [← e1] at e2 e3 e4 h
        by_cases hcomma : byteIs a (skipWsA a i) 0x2C = true
        · simp only [hcomma, ↓reduceIte] at h ⊢
          obtain ⟨hl, hb2⟩ := byteIs_spec a _ _ hcomma
          obtain ⟨f1, f2, f3, f4⟩ := skip_spec a hsz (skipWsA a i + 1) (by omega) (good_op a _ e2 hl (by rw [hb2]; decide))
          rw [← f1] at f2 f3 f4 h
          exact ih _ false _ _ _ t ⟨f4, f2⟩ h
        · simp only [hcomma, Bool.false_eq_true, ↓reduceIte] at h ⊢
          by_cases hclose : byteIs a (skipWsA a i) 0x5D = true
          · simp only [hclose, ↓reduceIte] at h ⊢
            obtain ⟨hl, hb5⟩ := byteIs_spec a _ _ hclose
            exact ih _ true _ _ _ t ⟨by omega, good_op a _ e2 hl (by rw [hb5]; decide)⟩ h
          · simp [hclose] at h
      | obj at_ n rest =>
        rw [runI] at h
        rw [runT]
        obtain ⟨e1, e2, e3, e4⟩ := skip_spec a hsz i hv.1 hv.2
        rw [← e1] at e2 e3 e4 h
        by_cases hcomma : byteIs a (skipWsA a i) 0x2C = true
        · simp only [hcomma, ↓reduceIte] at h ⊢
          obtain ⟨hl, hb2⟩ := byteIs_spec a _ _ hcomma
          obtain ⟨f1, f2, f3, f4⟩ := skip_spec a hsz (skipWsA a i + 1) (by omega) (good_op a _ e2 hl (by rw [hb2]; decide))
          rw [← f1] at f2 f3 f4 h
          cases hk : tb.keyNodeI (stage1 a) a (skipWsA a (skipWsA a i + 1)) with
          | none => simp [hk] at h
          | some tj =>
            obtain ⟨tb', j⟩ := tj
            obtain ⟨hk1, hk2⟩ := keyNodeI_sound a hsz _ _ ⟨f4, f2⟩ tb' j hk
            simp only [hk, hk1] at h ⊢
            exact ih _ false _ _ _ t hk2 h
        · simp only [hcomma, Bool.false_eq_true, ↓reduceIte] at h ⊢
          by_cases hclose : byteIs a (skipWsA a i) 0x7D = true
          · simp only [hclose, ↓reduceIte] at h ⊢
            obtain ⟨hl, hb7⟩ := byteIs_spec a _ _ hclose
            exact ih _ true _ _ _ t ⟨by omega, good_op a _ e2 hl (by rw [hb7]; decide)⟩ h
          · simp [hclose] at h

/-- The `runI` parser returns exactly what the scalar fused parser returns. -/
theorem parseTapeI_eq (a : ByteArray) : parseTapeI a = parseTapeFast a := by
  unfold parseTapeI
  by_cases hsz : a.size < simdLimit
  · simp only [hsz, ↓reduceIte]
    have hsz' : a.size < 2 ^ 31 := by unfold simdLimit at hsz; omega
    have hg : Good a 0 := fun _ => ⟨rfl, rfl, Or.inl rfl⟩
    obtain ⟨e1, e2, e3, e4⟩ := skip_spec a hsz' 0 (by omega) hg
    cases hr : runI (stage1 a) (a.size + 2) a (skipI (stage1 a) a.size 0) false ⟨.empty, .empty⟩ .nil maxDepth with
    | none => rfl
    | some t =>
      have := runI_sound a hsz' _ _ false _ _ _ t ⟨e4, e2⟩ hr
      unfold parseTapeFast
      rw [e1]
      exact this.symm
  · simp [hsz]

end LeanJsonProofs
