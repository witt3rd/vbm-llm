import LeanJsonProofs.PrintTape
import LeanJsonProofs.Stage1
import LeanJsonProofs.Swar
import LeanJsonSimd.PrintSimd
/-! # Proof: the tape printer with the `ld64` load is the tape printer (`printTapeS_eq`)

`ldwS_eq`: the load of a tape word by `ld64` is `ldw`. Then the leaves (`runS_eq`: a run found a word at a time is the byte-at-a-time run, for any flag whose lanes are exact; `plainEndS_eq`, `scanDigS_eq`, `utf8RangeS_eq`, `numLexS_eq`, `escLoopRS_eq`, `pleafS_eq`). In range, `ld64Model` is the little-endian word of the eight bytes with `|||`; `ldw` adds the same eight shifted bytes; the byte lanes do not overlap, so the two agree (`ors_eq`: each step is `or_add`, `Nat.shiftLeft_add_eq_or_of_lt`). -/
namespace LeanJsonProofs
open LeanJson VbmSimd

theorem bnd (y : UInt8) (s : Nat) (hs : s ≤ 56) : y.toNat * 2 ^ s + 2 ^ s ≤ 2 ^ 64 := by
  have hy := y.toNat_lt
  have h1 : (y.toNat + 1) * 2 ^ s ≤ 2 ^ 8 * 2 ^ s := Nat.mul_le_mul_right _ (by omega)
  have h2 : 2 ^ 8 * 2 ^ s = 2 ^ (8 + s) := (Nat.pow_add 2 8 s).symm
  have h3 : 2 ^ (8 + s) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) (by omega)
  have h4 : (y.toNat + 1) * 2 ^ s = y.toNat * 2 ^ s + 2 ^ s := by rw [Nat.add_mul, Nat.one_mul]
  omega
theorem sh_toNat (y : UInt8) (s : Nat) (hs : s ≤ 56) : (y.toUInt64 <<< s.toUInt64).toNat = y.toNat * 2 ^ s := by
  have h1 : s.toUInt64.toNat = s := by simp [Nat.toUInt64]; omega
  have hb := bnd y s hs
  have hp : 0 < 2 ^ s := Nat.two_pow_pos s
  rw [UInt64.toNat_shiftLeft, h1, Nat.mod_eq_of_lt (show s < 64 by omega)]
  simp only [UInt8.toNat_toUInt64, Nat.shiftLeft_eq]
  apply Nat.mod_eq_of_lt
  omega
theorem or_add (x : UInt64) (y : UInt8) (s : Nat) (hs : s ≤ 56) (hx : x.toNat < 2 ^ s) :
    x ||| (y.toUInt64 <<< s.toUInt64) = x + (y.toUInt64 <<< s.toUInt64) := by
  apply UInt64.toNat_inj.mp
  have h := sh_toNat y s hs
  have hb := bnd y s hs
  have h64 := x.toNat_lt
  rw [UInt64.toNat_or, UInt64.toNat_add, h]
  have e : y.toNat * 2 ^ s = y.toNat <<< s := by rw [Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (by omega)]
  rw [e, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hx, Nat.add_comm]
theorem step (x : UInt64) (y : UInt8) (s : Nat) (hs : s ≤ 56) (hx : x.toNat < 2 ^ s) :
    (x + (y.toUInt64 <<< s.toUInt64)).toNat < 2 ^ (s + 8) := by
  have h := sh_toNat y s hs
  have hb := bnd y s hs
  have hy := y.toNat_lt
  have h2 : 2 ^ (s + 8) = 2 ^ s * 2 ^ 8 := Nat.pow_add 2 s 8
  have h3 : (y.toNat + 1) * 2 ^ s ≤ 2 ^ 8 * 2 ^ s := Nat.mul_le_mul_right _ (by omega)
  have h4 : (y.toNat + 1) * 2 ^ s = y.toNat * 2 ^ s + 2 ^ s := by rw [Nat.add_mul, Nat.one_mul]
  have h5 : 2 ^ (s + 8) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) (by omega)
  rw [UInt64.toNat_add, h, Nat.mod_eq_of_lt (by omega)]
  omega
theorem ors_eq (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) :
    b0.toUInt64 ||| (b1.toUInt64 <<< 8) ||| (b2.toUInt64 <<< 16) ||| (b3.toUInt64 <<< 24) ||| (b4.toUInt64 <<< 32) ||| (b5.toUInt64 <<< 40) ||| (b6.toUInt64 <<< 48) ||| (b7.toUInt64 <<< 56) =
    b0.toUInt64 + (b1.toUInt64 <<< 8) + (b2.toUInt64 <<< 16) + (b3.toUInt64 <<< 24) + (b4.toUInt64 <<< 32) + (b5.toUInt64 <<< 40) + (b6.toUInt64 <<< 48) + (b7.toUInt64 <<< 56) := by
  have p1 : b0.toUInt64.toNat < 2 ^ 8 := by simpa using b0.toNat_lt
  have c1 := or_add _ b1 8 (by omega) p1
  have p2 := step _ b1 8 (by omega) p1
  have c2 := or_add _ b2 16 (by omega) p2
  have p3 := step _ b2 16 (by omega) p2
  have c3 := or_add _ b3 24 (by omega) p3
  have p4 := step _ b3 24 (by omega) p3
  have c4 := or_add _ b4 32 (by omega) p4
  have p5 := step _ b4 32 (by omega) p4
  have c5 := or_add _ b5 40 (by omega) p5
  have p6 := step _ b5 40 (by omega) p5
  have c6 := or_add _ b6 48 (by omega) p6
  have p7 := step _ b6 48 (by omega) p6
  have c7 := or_add _ b7 56 (by omega) p7
  simp only [show (8:Nat).toUInt64 = 8 from rfl, show (16:Nat).toUInt64 = 16 from rfl, show (24:Nat).toUInt64 = 24 from rfl, show (32:Nat).toUInt64 = 32 from rfl, show (40:Nat).toUInt64 = 40 from rfl, show (48:Nat).toUInt64 = 48 from rfl, show (56:Nat).toUInt64 = 56 from rfl] at c1 c2 c3 c4 c5 c6 c7
  rw [c1, c2, c3, c4, c5, c6, c7]

theorem ldwS_eq (a : ByteArray) (i : Nat) : ldwS a i = ldw a i := by
  unfold ldwS
  by_cases h : i < 268435456 ∧ i + 1 ≤ a.size >>> 3
  · have h8 : 8 * i + 8 ≤ a.size := by have := h.2; rw [Nat.shiftRight_eq_div_pow] at this; omega
    simp only [h, and_self, ↓reduceIte]
    rw [ld64_toUSize a (8 * i) (by omega)]
    unfold ldw ld64Model byteAt0
    simp only [h8, ↓reduceDIte]
    rw [ors_eq]
    have g : ∀ k (hk : k < a.size), a.data.getD k 0 = a[k] := by
      intro k hk; simp [hk]; rfl
    rw [g _ (by omega), g _ (by omega), g _ (by omega), g _ (by omega), g _ (by omega), g _ (by omega), g _ (by omega), g _ (by omega)]
  · simp only [h, ↓reduceIte]

/-! ## The leaves -/

/-- A byte that needs no escape. -/
def pPlain (b : UInt8) : Bool := !(b < 0x20 || b == 0x22 || b == 0x5C)

/-- The lane of `escFlag`. -/
def escLane (x : UInt8) : UInt8 := ((~~~(((x &&& 0x7f) + 0x60)) &&& ~~~x) &&& 0x80) ||| (if x == 0x5c then 0x80 else 0) ||| (if x == 0x22 then 0x80 else 0)

theorem escLane_spec : ∀ x : UInt8, escLane x = if pPlain x = true then 0 else 0x80 :=
  u8_forall _ (by decide)

theorem escFlag_lane (w : UInt64) (k : Nat) (hk : k < 8) : u8 (escFlag w) k = if pPlain (u8 w k) = true then 0 else 0x80 := by
  have hadd : ∀ j, j < 8 → (u8 (w &&& cLo7) j).toNat + (u8 0x6060606060606060 j).toNat < 256 := by
    intro j hj
    rw [u8_and, u8_cLo7 j hj, u8_c60 j hj]
    generalize u8 w j = x
    revert x
    exact u8_forall _ (by decide)
  unfold escFlag
  rw [u8_or, u8_or, u8_and, u8_and, u8_not _ _ hk, u8_not _ _ hk, u8_add _ _ hadd k hk, u8_and, u8_cHi k hk, u8_cLo7 k hk, u8_c60 k hk,
    u8_eqLanes _ _ _ hk, u8_eqLanes _ _ _ hk, u8_cBslash ⟨k, hk⟩, u8_cQuote ⟨k, hk⟩]
  have := escLane_spec (u8 w k)
  unfold escLane at this
  exact this

/-- The end of the run of bytes of `x[i:e]` (inside `x`) with `P`. -/
def runEnd (P : UInt8 → Bool) (x : ByteArray) (i e : Nat) : Nat :=
  if h : i < e ∧ i < x.size then (if P x[i] = true then runEnd P x (i + 1) e else i) else i
termination_by e - i

theorem plainEnd_eq (x : ByteArray) (i e : Nat) : plainEnd x i e = runEnd pPlain x i e := by
  rw [plainEnd, runEnd]
  by_cases h1 : i < e <;> by_cases h2 : i < x.size <;> simp only [h1, h2, and_self, ↓reduceDIte, and_true, and_false]
  have ih := plainEnd_eq x (i + 1) e
  by_cases hb : (x[i] < 0x20 || x[i] == 0x22 || x[i] == 0x5C) = true
  · simp [pPlain, hb]
  · simp [pPlain, hb, ih]
termination_by e - i

theorem scanDig_eq (x : ByteArray) (i e : Nat) : scanDig x i e = runEnd isDig x i e := by
  rw [scanDig, runEnd]
  by_cases h1 : i < e <;> by_cases h2 : i < x.size <;> simp only [h1, h2, and_self, ↓reduceDIte, and_true, and_false, byteAt]
  have ih := scanDig_eq x (i + 1) e
  by_cases hb : 0x30 ≤ x[i] ∧ x[i] ≤ 0x39
  · have : isDig x[i] = true := by simp only [isDig, decide_eq_true_eq, UInt8.le_iff_toNat_le] at hb ⊢; simpa using hb
    simp [hb, this, ih]
  · have : ¬ isDig x[i] = true := by simp only [isDig, decide_eq_true_eq, UInt8.le_iff_toNat_le] at hb ⊢; simpa using hb
    simp [hb, this]
termination_by e - i

theorem runEnd_stop (P : UInt8 → Bool) (x : ByteArray) (i e : Nat) (h : ¬ (i < e ∧ i < x.size)) : runEnd P x i e = i := by
  rw [runEnd]; simp only [h, ↓reduceDIte]

theorem runEnd_skip (P : UInt8 → Bool) (x : ByteArray) (e : Nat) : ∀ k i, (∀ m, m < k → ∃ h : i + m < x.size, P x[i + m] = true) → i + k ≤ e →
    runEnd P x i e = runEnd P x (i + k) e := by
  intro k
  induction k with
  | zero => intro i _ _; rfl
  | succ k ih =>
    intro i hd hk
    obtain ⟨h0, hp0⟩ := hd 0 (by omega)
    rw [runEnd]
    have h1 : i < e ∧ i < x.size := ⟨by omega, by simpa using h0⟩
    simp only [h1, and_self, ↓reduceDIte]
    have hp : P x[i] = true := by simpa using hp0
    simp only [hp, ↓reduceIte]
    rw [ih (i + 1) (fun m hm => by
          obtain ⟨h, hh⟩ := hd (m + 1) (by omega)
          exact ⟨by omega, by simpa [Nat.add_assoc, Nat.add_comm 1 m] using hh⟩) (by omega)]
    rw [Nat.add_assoc, Nat.add_comm 1 k]

theorem runS_eq (flag : UInt64 → UInt64) (tl : ByteArray → Nat → Nat → Nat) (P : UInt8 → Bool)
    (hlane : ∀ w k, k < 8 → u8 (flag w) k = if P (u8 w k) = true then 0 else 0x80) (hP0 : P 0 = false)
    (htl : ∀ x i e, tl x i e = runEnd P x i e) (x : ByteArray) : ∀ n i e, e - i = n → runS flag tl x i e = runEnd P x i e := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro i e hn
    rw [runS]
    by_cases hg : i < e ∧ e ≤ x.size ∧ x.size / 65536 < 65536
    · simp only [hg, and_self, ↓reduceDIte]
      have hl : ∀ k, k < 8 → u8 (flag (ld64 x i.toUSize)) k = if P (byteAt0 x (i + k)) = true then 0 else 0x80 := by
        intro k hk
        rw [hlane _ k hk, ld64_toUSize x i (by omega), u8_ld64Model x i k hk]
      have hv : ∀ k, k < 8 → u8 (flag (ld64 x i.toUSize)) k = 0 ∨ u8 (flag (ld64 x i.toUSize)) k = 0x80 := by
        intro k hk
        rw [hl k hk]
        by_cases hq : P (byteAt0 x (i + k)) = true <;> simp [hq]
      have hin : ∀ k, k < 8 → u8 (flag (ld64 x i.toUSize)) k = 0 → ∃ h : i + k < x.size, P x[i + k] = true := by
        intro k hk h0
        rw [hl k hk] at h0
        by_cases hq : P (byteAt0 x (i + k)) = true
        · by_cases hk' : i + k < x.size
          · exact ⟨hk', by rw [byteAt0_lt x _ hk'] at hq; exact hq⟩
          · have : byteAt0 x (i + k) = 0 := by unfold byteAt0; simp [Array.getD]; intro h; exact absurd h hk'
            rw [this, hP0] at hq; exact absurd hq (by simp)
        · simp [hq] at h0
      by_cases hz : (flag (ld64 x i.toUSize) == 0) = true
      · have hf0 : flag (ld64 x i.toUSize) = 0 := by simpa using hz
        simp only [hz, ↓reduceIte]
        have hall : ∀ m, m < 8 → ∃ h : i + m < x.size, P x[i + m] = true := fun m hm => hin m hm (by rw [hf0, u8_zero])
        by_cases h8 : i + 8 < e
        · simp only [h8, ↓reduceIte]
          rw [ih (e - (i + 8)) (by omega) (i + 8) e rfl, runEnd_skip P x e 8 i hall (by omega)]
        · simp only [h8, ↓reduceIte]
          rw [runEnd_skip P x e (e - i) i (fun m hm => hall m (by omega)) (by omega), Nat.add_sub_cancel' (by omega), runEnd_stop P x e e (by omega)]
      · have hne : flag (ld64 x i.toUSize) ≠ 0 := by simpa using hz
        simp only [hz, Bool.false_eq_true, ↓reduceIte]
        obtain ⟨hlt, hfl, hbef⟩ := first_flag _ hne hv
        have hbef' : ∀ q, q < (ctz (flag (ld64 x i.toUSize))).toNat / 8 → ∃ h : i + q < x.size, P x[i + q] = true := fun q hq => hin q (by omega) (hbef q hq)
        generalize (ctz (flag (ld64 x i.toUSize))).toNat / 8 = m at hlt hfl hbef hbef' ⊢
        by_cases hj : i + m < e
        · simp only [hj, ↓reduceIte]
          rw [runEnd_skip P x e m i hbef' (by omega)]
          have hflag : P (byteAt0 x (i + m)) = false := by
            have := hl m hlt
            rw [hfl] at this
            by_cases hq : P (byteAt0 x (i + m)) = true
            · simp [hq] at this
            · simpa using hq
          rw [runEnd]
          by_cases hs : i + m < x.size
          · have hpf : P x[i + m] = false := by rw [byteAt0_lt x _ hs] at hflag; exact hflag
            simp [hj, hs, hpf]
          · simp [hs]
        · simp only [hj, ↓reduceIte]
          rw [runEnd_skip P x e (e - i) i (fun q hq => hbef' q (by omega)) (by omega), Nat.add_sub_cancel' (by omega), runEnd_stop P x e e (by omega)]
    · simp only [hg, ↓reduceDIte]
      exact htl x i e

theorem plainEndS_eq (x : ByteArray) (i e : Nat) : plainEndS x i e = plainEnd x i e := by
  unfold plainEndS
  rw [runS_eq escFlag plainEnd pPlain escFlag_lane (by decide) (fun x i e => plainEnd_eq x i e) x _ i e rfl, plainEnd_eq]

theorem scanDigS_eq (x : ByteArray) (i e : Nat) : scanDigS x i e = scanDig x i e := by
  unfold scanDigS
  rw [runS_eq ndFlags scanDig isDig ndFlags_lane (by decide) (fun x i e => scanDig_eq x i e) x _ i e rfl, scanDig_eq]

theorem numLexS_eq (x : ByteArray) (i e : Nat) : numLexS x i e = numLex x i e := by
  unfold numLexS numIntS numFracS numExpS numLex numInt numFrac numExp
  simp only [scanDigS_eq]
  rfl

theorem utf8Range_ascii (x : ByteArray) (i e : Nat) (hi : i < e) (hx : i < x.size) (hc : x[i] < 0x80) : utf8Range x i e = utf8Range x (i + 1) e := by
  rw [utf8Range]
  simp only [hi, ↓reduceDIte, byteAt, hx, hc, ↓reduceIte]

theorem utf8Range_skip8 (x : ByteArray) (i e : Nat) (h8 : i + 8 ≤ e) (hall : ∀ m, m < 8 → ∃ h : i + m < x.size, x[i + m] < 0x80) :
    utf8Range x i e = utf8Range x (i + 8) e := by
  have step : ∀ k, k < 8 → utf8Range x (i + k) e = utf8Range x (i + k + 1) e := fun k hk => by
    obtain ⟨h, hc⟩ := hall k hk
    exact utf8Range_ascii x (i + k) e (by omega) h hc
  have s0 : utf8Range x i e = utf8Range x (i + 1) e := step 0 (by omega)
  have s1 : utf8Range x (i + 1) e = utf8Range x (i + 2) e := step 1 (by omega)
  have s2 : utf8Range x (i + 2) e = utf8Range x (i + 3) e := step 2 (by omega)
  have s3 : utf8Range x (i + 3) e = utf8Range x (i + 4) e := step 3 (by omega)
  have s4 : utf8Range x (i + 4) e = utf8Range x (i + 5) e := step 4 (by omega)
  have s5 : utf8Range x (i + 5) e = utf8Range x (i + 6) e := step 5 (by omega)
  have s6 : utf8Range x (i + 6) e = utf8Range x (i + 7) e := step 6 (by omega)
  have s7 : utf8Range x (i + 7) e = utf8Range x (i + 8) e := step 7 (by omega)
  rw [s0, s1, s2, s3, s4, s5, s6, s7]

theorem utf8RangeS_eq (x : ByteArray) (e : Nat) : ∀ n i, e - i = n → utf8RangeS x i e = utf8Range x i e := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro i hn
    rw [utf8RangeS]
    by_cases h : i < e
    · have ih' : ∀ j, i < j → utf8RangeS x j e = utf8Range x j e := fun j hj => ih (e - j) (by omega) j rfl
      simp only [h, ↓reduceDIte]
      by_cases hf : i + 8 ≤ e ∧ e ≤ x.size ∧ x.size / 65536 < 65536 ∧ (ld64 x i.toUSize &&& cHi) == 0
      · obtain ⟨h8, hs, hs2, hz⟩ := hf
        simp only [h8, hs, hs2, hz, and_self, ↓reduceIte]
        rw [ih' (i + 8) (by omega)]
        have hz' : ld64 x i.toUSize &&& cHi = 0 := by simpa using hz
        symm
        apply utf8Range_skip8 x i e h8
        intro m hm
        have hlt : i + m < x.size := by omega
        refine ⟨hlt, ?_⟩
        have := congrArg (fun w => u8 w m) hz'
        simp only [u8_and, u8_cHi m hm, u8_zero] at this
        rw [ld64_toUSize x i (by omega), u8_ld64Model x i m hm, byteAt0_lt x _ hlt] at this
        revert this
        generalize x[i + m] = c
        revert c
        exact u8_forall _ (by decide)
      · simp only [hf, ↓reduceIte]
        rw [utf8Range]
        simp only [h, ↓reduceDIte]
        cases hb : byteAt x i with
        | none => rfl
        | some c =>
          simp only []
          by_cases hc : c < 0x80
          · simp only [hc, ↓reduceIte, ih' (i + 1) (by omega)]
          · simp only [hc, ↓reduceIte]
            cases hd : decodeUtf8A x i with
            | none => rfl
            | some r =>
              obtain ⟨a, j⟩ := r
              simp only []
              by_cases hij : i < j ∧ j ≤ e
              · simp only [hij, and_self, ↓reduceIte, ih' j hij.1]
              · simp only [hij, ↓reduceIte]
    · rw [utf8Range]
      simp only [h, ↓reduceDIte]

theorem escLoopRS_eq (x : ByteArray) (e : Nat) : ∀ n i b, e - i = n → escLoopRS x i e b = escLoopR x i e b := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro i b hn
    rw [escLoopRS, escLoopR]
    by_cases h : i < e
    · simp only [h, ↓reduceDIte, plainEndS_eq]
      split
      · rename_i h'
        rw [ih (e - (plainEnd x i e + 1)) (by omega) _ _ rfl]
      · rfl
    · simp only [h, ↓reduceDIte]

/-! ### A number lexeme needs no escape -/

/-- A byte a number lexeme may hold. -/
def numC (b : UInt8) : Bool := isDig b || b == 0x2D || b == 0x2B || b == 0x2E || b == 0x65 || b == 0x45

theorem numC_plain : ∀ b : UInt8, numC b = true → pPlain b = true := u8_forall _ (by decide)
theorem isDig_numC : ∀ b : UInt8, isDig b = true → numC b = true := u8_forall _ (by decide)

/-- Every byte of `x[a:b]` is inside `x` and may be in a number lexeme. -/
def AllC (x : ByteArray) (a b : Nat) : Prop := ∀ q, a ≤ q → q < b → ∃ h : q < x.size, numC x[q] = true

theorem AllC_trans (x : ByteArray) (a b c : Nat) (h1 : AllC x a b) (h2 : AllC x b c) : AllC x a c := by
  intro q hq1 hq2
  by_cases hq : q < b
  · exact h1 q hq1 hq
  · exact h2 q (by omega) hq2

theorem AllC_nil (x : ByteArray) (a b : Nat) (h : b ≤ a) : AllC x a b := fun q h1 h2 => absurd h2 (by omega)

theorem AllC_one (x : ByteArray) (a : Nat) (h : a < x.size) (hc : numC x[a] = true) : AllC x a (a + 1) := by
  intro q h1 h2
  have : q = a := by omega
  subst this
  exact ⟨h, hc⟩

theorem runEnd_props (P : UInt8 → Bool) (x : ByteArray) (e : Nat) : ∀ n i, e - i = n →
    i ≤ runEnd P x i e ∧ (i ≤ e → runEnd P x i e ≤ e) ∧ ∀ q, i ≤ q → q < runEnd P x i e → ∃ h : q < x.size, P x[q] = true := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro i hn
    rw [runEnd]
    by_cases h : i < e ∧ i < x.size
    · simp only [h, and_self, ↓reduceDIte]
      by_cases hp : P x[i] = true
      · simp only [hp, ↓reduceIte]
        obtain ⟨a, b, c⟩ := ih (e - (i + 1)) (by omega) (i + 1) rfl
        refine ⟨by omega, fun _ => b (by omega), fun q hq1 hq2 => ?_⟩
        by_cases hq : q = i
        · subst hq; exact ⟨h.2, hp⟩
        · exact c q (by omega) hq2
      · simp only [hp, Bool.false_eq_true, ↓reduceIte]
        exact ⟨Nat.le_refl _, fun _ => by omega, fun q h1 h2 => absurd h2 (by omega)⟩
    · simp only [h, ↓reduceDIte]
      exact ⟨Nat.le_refl _, fun h' => by omega, fun q h1 h2 => absurd h2 (by omega)⟩

theorem scanDig_props (x : ByteArray) (i e : Nat) : i ≤ scanDig x i e ∧ (i ≤ e → scanDig x i e ≤ e) ∧ AllC x i (scanDig x i e) := by
  rw [scanDig_eq]
  obtain ⟨a, b, c⟩ := runEnd_props isDig x e _ i rfl
  exact ⟨a, b, fun q h1 h2 => by obtain ⟨h, hd⟩ := c q h1 h2; exact ⟨h, isDig_numC _ hd⟩⟩

theorem byteIs_ex (x : ByteArray) (i : Nat) (c : UInt8) : byteIs x i c = true ↔ ∃ h : i < x.size, x[i] = c := by
  unfold byteIs
  by_cases hs : i < x.size
  · simp [hs]
  · simp [hs]

theorem dig_iff (x : ByteArray) (j : Nat) :
    (match byteAt x j with | some c => decide (0x30 ≤ c.toNat ∧ c.toNat ≤ 0x39) | none => false) = true ↔ ∃ h : j < x.size, 0x30 ≤ x[j].toNat ∧ x[j].toNat ≤ 0x39 := by
  unfold byteAt
  by_cases hs : j < x.size
  · simp [hs]
  · simp [hs]

theorem numSign_props (x : ByteArray) (i e : Nat) : i ≤ numSign x i e ∧ numSign x i e ≤ i + 1 ∧ AllC x i (numSign x i e) := by
  unfold numSign
  by_cases h : i < e ∧ byteIs x i 0x2D = true
  · have h' : (decide (i < e) && byteIs x i 0x2D) = true := by simp [h.1, h.2]
    simp only [h', ↓reduceIte]
    obtain ⟨hs, hx⟩ := (byteIs_ex x i _).1 h.2
    refine ⟨by omega, by omega, AllC_one x i hs ?_⟩
    rw [hx]; decide
  · have h' : ¬ ((decide (i < e) && byteIs x i 0x2D) = true) := by
      intro hh; apply h; simpa using hh
    simp only [h', Bool.false_eq_true, ↓reduceIte]
    exact ⟨Nat.le_refl _, by omega, AllC_nil x _ _ (Nat.le_refl _)⟩

theorem numInt_props (x : ByteArray) (i e : Nat) (h0 : numInt x i e ≠ 0) : i < numInt x i e ∧ AllC x i (numInt x i e) := by
  unfold numInt at h0 ⊢
  by_cases hi : i < e
  · simp only [hi, ↓reduceIte] at h0 ⊢
    by_cases hb : i < x.size
    · simp only [byteAt, hb, ↓reduceDIte] at h0 ⊢
      by_cases hz : (x[i] == 0x30) = true
      · simp only [hz, ↓reduceIte]
        refine ⟨by omega, AllC_one x i hb ?_⟩
        have : x[i] = 0x30 := by simpa using hz
        rw [this]; decide
      · simp only [hz, Bool.false_eq_true, ↓reduceIte] at h0 ⊢
        by_cases hd : 0x31 ≤ x[i].toNat ∧ x[i].toNat ≤ 0x39
        · simp only [hd, and_self, ↓reduceIte]
          obtain ⟨a, _, c⟩ := scanDig_props x (i + 1) e
          refine ⟨by omega, AllC_trans x i (i + 1) _ (AllC_one x i hb ?_) c⟩
          have : isDig x[i] = true := by simp only [isDig, decide_eq_true_eq]; omega
          exact isDig_numC _ this
        · simp [hd] at h0
    · simp [byteAt, hb] at h0
  · simp [hi] at h0

theorem numFrac_props (x : ByteArray) (i e : Nat) (h0 : numFrac x i e ≠ 0) : i ≤ numFrac x i e ∧ AllC x i (numFrac x i e) := by
  by_cases hd : i < e ∧ byteIs x i 0x2E = true
  · have hd' : (decide (i < e) && byteIs x i 0x2E) = true := by simp [hd.1, hd.2]
    have e1 : numFrac x i e = if (decide (i + 1 < e) && match byteAt x (i + 1) with | some c => decide (0x30 ≤ c.toNat ∧ c.toNat ≤ 0x39) | none => false) = true then scanDig x (i + 2) e else 0 := by
      unfold numFrac; simp only [hd', ↓reduceIte]; rfl
    rw [e1] at h0 ⊢
    obtain ⟨hs0, hx0⟩ := (byteIs_ex x i _).1 hd.2
    by_cases hg : (decide (i + 1 < e) && match byteAt x (i + 1) with | some c => decide (0x30 ≤ c.toNat ∧ c.toNat ≤ 0x39) | none => false) = true
    · simp only [hg, ↓reduceIte]
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
      obtain ⟨hs1, hdg⟩ := (dig_iff x (i + 1)).1 hg.2
      obtain ⟨a, _, c⟩ := scanDig_props x (i + 2) e
      refine ⟨by omega, ?_⟩
      have hd1 : AllC x i (i + 1) := AllC_one x i hs0 (by rw [hx0]; decide)
      have hd2 : AllC x (i + 1) (i + 2) := AllC_one x (i + 1) hs1 (isDig_numC _ (by simp only [isDig, decide_eq_true_eq]; exact hdg))
      exact AllC_trans x i (i + 1) _ hd1 (AllC_trans x (i + 1) (i + 2) _ hd2 c)
    · simp only [hg, Bool.false_eq_true, ↓reduceIte] at h0
      exact absurd rfl h0
  · have hd' : ¬ ((decide (i < e) && byteIs x i 0x2E) = true) := by
      intro hh; apply hd; simpa using hh
    have e1 : numFrac x i e = i := by unfold numFrac; simp only [hd', Bool.false_eq_true, ↓reduceIte]
    rw [e1]
    exact ⟨Nat.le_refl _, AllC_nil x _ _ (Nat.le_refl _)⟩

theorem numExp_props (x : ByteArray) (i e : Nat) (h0 : numExp x i e ≠ 0) : i ≤ numExp x i e ∧ AllC x i (numExp x i e) := by
  by_cases hd : i < e ∧ (byteIs x i 0x65 || byteIs x i 0x45) = true
  · have hd' : (decide (i < e) && (byteIs x i 0x65 || byteIs x i 0x45)) = true := by simp [hd.1, hd.2]
    have e1 : numExp x i e = (let j := if (decide (i + 1 < e) && (byteIs x (i + 1) 0x2B || byteIs x (i + 1) 0x2D)) = true then i + 2 else i + 1
        if (decide (j < e) && match byteAt x j with | some c => decide (0x30 ≤ c.toNat ∧ c.toNat ≤ 0x39) | none => false) = true then scanDig x (j + 1) e else 0) := by
      unfold numExp; simp only [hd', ↓reduceIte]; rfl
    rw [e1] at h0 ⊢
    simp only [] at h0 ⊢
    obtain ⟨hs0, hx0⟩ : ∃ h : i < x.size, (x[i] = 0x65 ∨ x[i] = 0x45) := by
      have := hd.2
      simp only [Bool.or_eq_true] at this
      rcases this with h | h
      · obtain ⟨a, b⟩ := (byteIs_ex x i _).1 h; exact ⟨a, Or.inl b⟩
      · obtain ⟨a, b⟩ := (byteIs_ex x i _).1 h; exact ⟨a, Or.inr b⟩
    have hdE : AllC x i (i + 1) := AllC_one x i hs0 (by rcases hx0 with h | h <;> rw [h] <;> decide)
    -- the sign
    have hj : ∃ j, (j = i + 1 ∨ (j = i + 2 ∧ i + 1 < e)) ∧ AllC x i j ∧
        (if (decide (i + 1 < e) && (byteIs x (i + 1) 0x2B || byteIs x (i + 1) 0x2D)) = true then i + 2 else i + 1) = j := by
      by_cases hg : (decide (i + 1 < e) && (byteIs x (i + 1) 0x2B || byteIs x (i + 1) 0x2D)) = true
      · simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at hg
        refine ⟨i + 2, Or.inr ⟨rfl, hg.1⟩, ?_, by simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true]; simp [hg]⟩
        have hsg : AllC x (i + 1) (i + 2) := by
          rcases hg.2 with h | h
          · obtain ⟨a, b⟩ := (byteIs_ex x (i + 1) _).1 h; exact AllC_one x (i + 1) a (by rw [b]; decide)
          · obtain ⟨a, b⟩ := (byteIs_ex x (i + 1) _).1 h; exact AllC_one x (i + 1) a (by rw [b]; decide)
        exact AllC_trans x i (i + 1) _ hdE hsg
      · exact ⟨i + 1, Or.inl rfl, hdE, by simp only [hg, Bool.false_eq_true, ↓reduceIte]⟩
    obtain ⟨j, hjc, hAj, hjeq⟩ := hj
    rw [hjeq] at h0 ⊢
    by_cases hg : (decide (j < e) && match byteAt x j with | some c => decide (0x30 ≤ c.toNat ∧ c.toNat ≤ 0x39) | none => false) = true
    · simp only [hg, ↓reduceIte]
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
      obtain ⟨hs1, hdg⟩ := (dig_iff x j).1 hg.2
      obtain ⟨a, _, c⟩ := scanDig_props x (j + 1) e
      refine ⟨by omega, ?_⟩
      have hd2 : AllC x j (j + 1) := AllC_one x j hs1 (isDig_numC _ (by simp only [isDig, decide_eq_true_eq]; exact hdg))
      exact AllC_trans x i j _ hAj (AllC_trans x j (j + 1) _ hd2 c)
    · simp only [hg, Bool.false_eq_true, ↓reduceIte] at h0
      exact absurd rfl h0
  · have hd' : ¬ ((decide (i < e) && (byteIs x i 0x65 || byteIs x i 0x45)) = true) := by
      intro hh; apply hd; simpa using hh
    have e1 : numExp x i e = i := by unfold numExp; simp only [hd', Bool.false_eq_true, ↓reduceIte]
    rw [e1]
    exact ⟨Nat.le_refl _, AllC_nil x _ _ (Nat.le_refl _)⟩

/-- A lexeme that passes `numLex` has only bytes a number lexeme may hold. -/
theorem numLex_allC (x : ByteArray) (i e : Nat) (h : numLex x i e = true) : i < e ∧ AllC x i e := by
  unfold numLex at h
  simp only [] at h
  obtain ⟨s1, s2, s3⟩ := numSign_props x i e
  by_cases h2 : numInt x (numSign x i e) e = 0
  · simp [h2] at h
  · by_cases h3 : numFrac x (numInt x (numSign x i e) e) e = 0
    · simp [h2, h3] at h
    · have hexp := h
      simp only [h2, h3, beq_iff_eq, ↓reduceIte, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hexp
      obtain ⟨h4, h5⟩ := hexp
      obtain ⟨i1, a1⟩ := numInt_props x _ e h2
      obtain ⟨f1, a2⟩ := numFrac_props x _ e h3
      obtain ⟨x1, a3⟩ := numExp_props x _ e h4
      rw [h5] at a3 x1
      exact ⟨by omega, AllC_trans x i _ _ s3 (AllC_trans x _ _ _ a1 (AllC_trans x _ _ _ a2 a3))⟩

/-- A run of bytes of `x[i:e]` that all need no escape is copied whole by `escLoopR`. -/
theorem escLoopR_plain (x : ByteArray) (i e : Nat) (b : ByteArray) (hi : i < e) (h : AllC x i e) :
    escLoopR x i e b = x.copySlice i b b.size (e - i) false := by
  have hall : ∀ m, m < e - i → ∃ hh : i + m < x.size, pPlain x[i + m] = true := fun m hm => by
    obtain ⟨hh, hc⟩ := h (i + m) (by omega) (by omega)
    exact ⟨hh, numC_plain _ hc⟩
  have hend : plainEnd x i e = e := by
    rw [plainEnd_eq, runEnd_skip pPlain x e (e - i) i hall (by omega), Nat.add_sub_cancel' (by omega), runEnd_stop pPlain x e e (by omega)]
  rw [escLoopR]
  simp only [hi, ↓reduceDIte, hend]
  have : ¬ (i ≤ e ∧ e < e ∧ e < x.size) := by omega
  simp only [this, ↓reduceDIte, ↓reduceIte]

theorem pleafS_eq (x : ByteArray) (h aux : UInt64) (b : ByteArray) : pleafS x h aux b = pleaf x h aux b := by
  unfold pleafS pleaf
  have hE : ∀ i e b, escLoopRS x i e b = escLoopR x i e b := fun i e b => escLoopRS_eq x e _ i b rfl
  have hU : ∀ i e, utf8RangeS x i e = utf8Range x i e := fun i e => utf8RangeS_eq x e _ i rfl
  have hN : ∀ off len, (if (decide (off + len ≤ x.size) && numLex x off (off + len)) = true then x.copySlice off b b.size len false else ByteArray.empty) =
      (if (decide (off + len ≤ x.size) && numLex x off (off + len)) = true then escLoopR x off (off + len) b else ByteArray.empty) := by
    intro off len
    by_cases hc : (decide (off + len ≤ x.size) && numLex x off (off + len)) = true
    · simp only [hc, ↓reduceIte]
      have hl : numLex x off (off + len) = true := by simpa using (by simpa using hc : _ ∧ numLex x off (off + len) = true).2
      obtain ⟨hlt, hall⟩ := numLex_allC x off (off + len) hl
      rw [escLoopR_plain x off (off + len) b hlt hall, Nat.add_sub_cancel_left]
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
  simp only [numLexS_eq, hE, hU, hN]

theorem printTapeS_eq (w x : ByteArray) : printTapeS w x = printTape w x := by
  have : ldwS = ldw := funext fun a => funext fun i => ldwS_eq a i
  have h2 : pleafS = pleaf := funext fun x => funext fun h => funext fun aux => funext fun b => pleafS_eq x h aux b
  unfold printTapeS printTape
  rw [this, h2]


theorem escapeCheckedS_eq (a : ByteArray) : escapeCheckedS a = escapeChecked a := by
  unfold escapeCheckedS escapeChecked escapeString
  have hU : utf8RangeS a 0 a.size = utf8Range a 0 a.size := utf8RangeS_eq a a.size a.size 0 (by simp)
  have hE := fun b => escLoopRS_eq a a.size a.size 0 b (by simp)
  have hR := fun b => escLoopR_eq a a.size (Nat.le_refl _) a.size 0 b (by simp)
  have hL := fun b => escLoop_eq a 0 b
  have hT : ((L a).drop 0).take (a.size - 0) = a.data.toList.drop 0 := by
    rw [Nat.sub_zero, List.drop_zero, List.drop_zero, size_L, List.take_length]; rfl
  simp only [hU, hE, hR, hL, hT]

end LeanJsonProofs
