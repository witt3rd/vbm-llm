import LeanJsonProofs.ParseU
/-! # Proof: a number whose exponent letter is not `E` and has no `+` has a canonical lexeme equal to the input (`scanNumK_spec`)

`scanNumK` (`LeanJsonSimd/ParseSimd.lean`) says whether the lexeme of a number has an `E` or a `+` from two bytes at the end of the fraction, so that `runC` need not check every byte of the lexeme (`lexOkU`, a second pass). The
integer and fraction parts are digits, `-` and `.` (`scanInt_lex`, `scanFrac_lex`: no `E`, no `+`); the exponent part is the letter, an optional sign and digits. `scanNumK_spec`: the flag is false exactly when `lexOkU` is true. -/
namespace LeanJsonProofs
open LeanJson VbmSimd VbmSimdProofs

/-- The bytes of a number before its exponent: digits, `-`, `.`. -/
def lexByte (c : UInt8) : Bool := (decide (0x30 ≤ c.toNat) && decide (c.toNat ≤ 0x39)) || c == 0x2D || c == 0x2E

theorem lexByte_ne : ∀ c : UInt8, lexByte c = true → c ≠ 0x45 ∧ c ≠ 0x2B := u8_forall _ (by decide)

/-- `[i, j)` is a stretch of number bytes within the input (when `i` is). -/
def LexRun (a : ByteArray) (i j : Nat) : Prop := i ≤ j ∧ (i ≤ a.size → j ≤ a.size) ∧ ∀ p, i ≤ p → p < j → lexByte (byteD a p) = true

theorem LexRun.refl (a : ByteArray) (i : Nat) : LexRun a i i := ⟨Nat.le_refl _, id, fun p h1 h2 => by omega⟩

theorem LexRun.trans {a : ByteArray} {i j k : Nat} (h1 : LexRun a i j) (h2 : LexRun a j k) : LexRun a i k :=
  ⟨Nat.le_trans h1.1 h2.1, fun hi => h2.2.1 (h1.2.1 hi), fun p hp1 hp2 => by
    by_cases hp : p < j
    · exact h1.2.2 p hp1 hp
    · exact h2.2.2 p (by omega) hp2⟩

theorem LexRun.one {a : ByteArray} {i : Nat} (hi : i < a.size) (hb : lexByte (byteD a i) = true) : LexRun a i (i + 1) :=
  ⟨by omega, fun _ => by omega, fun p h1 h2 => by
    have : p = i := by omega
    subst this; exact hb⟩


theorem digit_lexByte (c : UInt8) (h : (digitVal c).isSome = true) : lexByte c = true := by
  unfold digitVal at h
  by_cases hh : 0x30 ≤ c.toNat ∧ c.toNat ≤ 0x39
  · simp [lexByte, hh.1, hh.2]
  · simp [hh] at h

theorem digit19_lexByte (c : UInt8) (h : (digit19 c).isSome = true) : lexByte c = true := by
  unfold digit19 at h
  by_cases hh : 0x31 ≤ c.toNat ∧ c.toNat ≤ 0x39
  · simp [lexByte, show 0x30 ≤ c.toNat by omega, hh.2]
  · simp [hh] at h


theorem scanDigits_lex (a : ByteArray) : ∀ d i, a.size - i = d → LexRun a i (scanDigits a i) := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
    intro i hd
    rw [scanDigits]
    by_cases hi : i < a.size
    · simp only [hi, ↓reduceDIte]
      by_cases hdig : (digitVal a[i]).isSome = true
      · simp only [hdig, ↓reduceIte]
        have hb : lexByte (byteD a i) = true := by rw [byteD_eq a i hi]; exact digit_lexByte _ hdig
        exact (LexRun.one hi hb).trans (ih (a.size - (i + 1)) (by omega) (i + 1) rfl)
      · simp only [hdig, Bool.false_eq_true, ↓reduceIte]
        exact LexRun.refl a i
    · simp only [hi, ↓reduceDIte]
      exact LexRun.refl a i

theorem scanDigits1_lex (a : ByteArray) (i j : Nat) (h : scanDigits1 a i = some j) : LexRun a i j := by
  unfold scanDigits1 at h
  cases hb : byteAt a i with
  | none => simp [hb] at h
  | some b =>
    simp only [hb] at h
    by_cases hdig : (digitVal b).isSome = true
    · simp only [hdig, ↓reduceIte, Option.some.injEq] at h
      subst h
      obtain ⟨hi, hbi⟩ := byteAt_spec a i b hb
      have hnb : lexByte (byteD a i) = true := by rw [hbi]; exact digit_lexByte _ hdig
      exact (LexRun.one hi hnb).trans (scanDigits_lex a _ (i + 1) rfl)
    · simp [hdig] at h

theorem scanInt_lex (a : ByteArray) (i j : Nat) (h : scanInt a i = some j) : LexRun a i j := by
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
      exact LexRun.one hi (by rw [hbi, this]; decide)
    · simp only [h0, Bool.false_eq_true, ↓reduceIte] at h
      by_cases h19 : (digit19 b).isSome = true
      · simp only [h19, ↓reduceIte, Option.some.injEq] at h
        subst h
        exact (LexRun.one hi (by rw [hbi]; exact digit19_lexByte _ h19)).trans (scanDigits_lex a _ (i + 1) rfl)
      · simp [h19] at h

theorem scanFrac_lex (a : ByteArray) (i j : Nat) (h : scanFrac a i = some j) : LexRun a i j := by
  unfold scanFrac at h
  by_cases hd : byteIs a i 0x2E = true
  · simp only [hd, ↓reduceIte] at h
    obtain ⟨hi, hbi⟩ := byteIs_spec a i _ hd
    exact (LexRun.one hi (by rw [hbi]; decide)).trans (scanDigits1_lex a _ j h)
  · simp only [hd, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
    subst h; exact LexRun.refl a i


/-! ## `lexRun` as a statement about every byte -/

theorem lexRun_forall (a : ByteArray) : ∀ d p e, e - p = d → (lexRun a p e = true ↔ ∀ k, p ≤ k → k < e → k < a.size ∧ byteD a k ≠ 0x45 ∧ byteD a k ≠ 0x2B) := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
    intro p e hd
    rw [lexRun]
    by_cases hpe : p < e
    · simp only [hpe, ↓reduceDIte]
      by_cases hps : p < a.size
      · simp only [hps, ↓reduceDIte]
        by_cases hc : (a[p] != 0x45 && a[p] != 0x2B) = true
        · simp only [hc, ↓reduceIte]
          rw [ih (e - (p + 1)) (by omega) (p + 1) e rfl]
          have hb : byteD a p ≠ 0x45 ∧ byteD a p ≠ 0x2B := by
            rw [byteD_eq a p hps]
            simpa only [Bool.and_eq_true, bne_iff_ne, ne_eq] using hc
          constructor
          · intro h k hk1 hk2
            by_cases hkp : k = p
            · subst hkp; exact ⟨hps, hb⟩
            · exact h k (by omega) hk2
          · intro h k hk1 hk2; exact h k (by omega) hk2
        · simp only [hc, Bool.false_eq_true, ↓reduceIte]
          constructor
          · intro h; exact absurd h (by simp)
          · intro h
            have := h p (Nat.le_refl _) hpe
            rw [byteD_eq a p hps] at this
            exact absurd (by simp [this.2.1, this.2.2]) hc
      · simp only [hps, ↓reduceDIte]
        constructor
        · intro h; exact absurd h (by simp)
        · intro h; exact absurd (h p (Nat.le_refl _) hpe).1 hps
    · simp only [hpe, ↓reduceDIte]
      constructor
      · intro _ k hk1 hk2; omega
      · intro _; trivial

theorem byteIs_iff (a : ByteArray) (i : Nat) (c : UInt8) : byteIs a i c = true ↔ i < a.size ∧ byteD a i = c :=
  ⟨byteIs_spec a i c, fun ⟨h1, h2⟩ => by
    unfold byteIs
    simp only [h1, ↓reduceDIte, beq_iff_eq]
    rw [← byteD_eq a i h1]; exact h2⟩

theorem scanDigits1_first (a : ByteArray) (s j : Nat) (h : scanDigits1 a s = some j) : s < a.size ∧ s + 1 ≤ j ∧ lexByte (byteD a s) = true := by
  unfold scanDigits1 at h
  cases hb : byteAt a s with
  | none => simp [hb] at h
  | some b =>
    simp only [hb] at h
    by_cases hdig : (digitVal b).isSome = true
    · simp only [hdig, ↓reduceIte, Option.some.injEq] at h
      subst h
      obtain ⟨hi, hbi⟩ := byteAt_spec a s b hb
      have := (scanDigits_bd a _ (s + 1) rfl).1
      exact ⟨hi, this, by rw [hbi]; exact digit_lexByte _ hdig⟩
    · simp [hdig] at h

/-- The exponent part: `a[r2, j)` has no `E` and no `+` exactly when the flag read at `r2` is false. -/
theorem exp_lex (a : ByteArray) (r2 j : Nat) (hr2 : r2 ≤ a.size) (h : scanExp a r2 = some j) :
    lexRun a r2 j = true ↔ (byteIs a r2 0x45 || (byteIs a r2 0x65 && byteIs a (r2 + 1) 0x2B)) = false := by
  rw [lexRun_forall a _ r2 j rfl]
  have hfl : ((byteIs a r2 0x45 || (byteIs a r2 0x65 && byteIs a (r2 + 1) 0x2B)) = false) ↔
      ¬ (r2 < a.size ∧ byteD a r2 = 0x45) ∧ ¬ (r2 < a.size ∧ byteD a r2 = 0x65 ∧ r2 + 1 < a.size ∧ byteD a (r2 + 1) = 0x2B) := by
    have e1 := byteIs_iff a r2 0x45
    have e2 := byteIs_iff a r2 0x65
    have e3 := byteIs_iff a (r2 + 1) 0x2B
    cases h1 : byteIs a r2 0x45 <;> cases h2 : byteIs a r2 0x65 <;> cases h3 : byteIs a (r2 + 1) 0x2B <;> simp_all
  rw [hfl]
  unfold scanExp at h
  by_cases hd : (byteIs a r2 0x65 || byteIs a r2 0x45) = true
  · simp only [hd, ↓reduceIte] at h
    have hlt : r2 < a.size ∧ (byteD a r2 = 0x65 ∨ byteD a r2 = 0x45) := by
      rcases Bool.or_eq_true_iff.mp hd with h1 | h1
      · obtain ⟨x, y⟩ := byteIs_spec a r2 _ h1; exact ⟨x, Or.inl y⟩
      · obtain ⟨x, y⟩ := byteIs_spec a r2 _ h1; exact ⟨x, Or.inr y⟩
    by_cases hs : (byteIs a (r2 + 1) 0x2B || byteIs a (r2 + 1) 0x2D) = true
    · simp only [hs, ↓reduceIte] at h
      have hdl := scanDigits1_lex a (r2 + 2) j h
      have hs1 : r2 + 1 < a.size ∧ (byteD a (r2 + 1) = 0x2B ∨ byteD a (r2 + 1) = 0x2D) := by
        rcases Bool.or_eq_true_iff.mp hs with h1 | h1
        · obtain ⟨x, y⟩ := byteIs_spec a (r2 + 1) _ h1; exact ⟨x, Or.inl y⟩
        · obtain ⟨x, y⟩ := byteIs_spec a (r2 + 1) _ h1; exact ⟨x, Or.inr y⟩
      have hj2 := hdl.1
      have hbig : ∀ k, r2 + 2 ≤ k → k < j → k < a.size ∧ byteD a k ≠ 0x45 ∧ byteD a k ≠ 0x2B := by
        intro k hk1 hk2
        have hj := hdl.2.1 (by omega)
        exact ⟨by omega, (lexByte_ne _ (hdl.2.2 k hk1 hk2)).1, (lexByte_ne _ (hdl.2.2 k hk1 hk2)).2⟩
      constructor
      · intro hall
        have h0 := hall r2 (Nat.le_refl _) (by omega)
        have h1 := hall (r2 + 1) (by omega) (by omega)
        exact ⟨fun ⟨_, e⟩ => h0.2.1 e, fun ⟨_, _, _, e2⟩ => h1.2.2 e2⟩
      · intro ⟨hn1, hn2⟩ k hk1 hk2
        by_cases hk0 : k = r2
        · subst hk0
          refine ⟨hlt.1, fun e => hn1 ⟨hlt.1, e⟩, ?_⟩
          rcases hlt.2 with e | e <;> simp [e]
        · by_cases hk1' : k = r2 + 1
          · subst hk1'
            refine ⟨hs1.1, ?_, ?_⟩
            · rcases hs1.2 with e | e <;> simp [e]
            · intro e
              rcases hlt.2 with e0 | e0
              · exact hn2 ⟨hlt.1, e0, hs1.1, e⟩
              · exact hn1 ⟨hlt.1, e0⟩
          · exact hbig k (by omega) hk2
    · simp only [hs, Bool.false_eq_true, ↓reduceIte] at h
      have hdl := scanDigits1_lex a (r2 + 1) j h
      obtain ⟨hf1, hf2, hf3⟩ := scanDigits1_first a (r2 + 1) j h
      have hbig : ∀ k, r2 + 1 ≤ k → k < j → k < a.size ∧ byteD a k ≠ 0x45 ∧ byteD a k ≠ 0x2B := by
        intro k hk1 hk2
        have hj := hdl.2.1 (by omega)
        exact ⟨by omega, (lexByte_ne _ (hdl.2.2 k hk1 hk2)).1, (lexByte_ne _ (hdl.2.2 k hk1 hk2)).2⟩
      have hnp : byteD a (r2 + 1) ≠ 0x2B := (lexByte_ne _ hf3).2
      constructor
      · intro hall
        have h0 := hall r2 (Nat.le_refl _) (by omega)
        exact ⟨fun ⟨_, e⟩ => h0.2.1 e, fun ⟨_, _, _, e2⟩ => hnp e2⟩
      · intro ⟨hn1, hn2⟩ k hk1 hk2
        by_cases hk0 : k = r2
        · subst hk0
          refine ⟨hlt.1, fun e => hn1 ⟨hlt.1, e⟩, ?_⟩
          rcases hlt.2 with e | e <;> simp [e]
        · exact hbig k (by omega) hk2
  · simp only [hd, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
    subst h
    have hn65 : byteIs a r2 0x65 = false := by cases hh : byteIs a r2 0x65 <;> simp_all
    have hn45 : byteIs a r2 0x45 = false := by cases hh : byteIs a r2 0x45 <;> simp_all
    constructor
    · intro _
      refine ⟨fun ⟨x, e⟩ => ?_, fun ⟨x, e, _⟩ => ?_⟩
      · have := (byteIs_iff a r2 0x45).2 ⟨x, e⟩; simp_all
      · have := (byteIs_iff a r2 0x65).2 ⟨x, e⟩; simp_all
    · intro _ k hk1 hk2; omega

/-! ## The flag of `scanNumK` -/

/-- Every byte of `a[i, j)` is not `E` and not `+` and inside the input, when `a[i, j)` is a run of `lexByte` bytes within the input. -/
theorem lexRun_of_LexRun (a : ByteArray) (i j : Nat) (h : LexRun a i j) (hj : j ≤ a.size) : ∀ k, i ≤ k → k < j → k < a.size ∧ byteD a k ≠ 0x45 ∧ byteD a k ≠ 0x2B :=
  fun k hk1 hk2 => ⟨by omega, (lexByte_ne _ (h.2.2 k hk1 hk2)).1, (lexByte_ne _ (h.2.2 k hk1 hk2)).2⟩

theorem scanNumK_spec (a : ByteArray) (hs : a.size < 2 ^ 31) (i : USize) (hi : i.toNat ≤ a.size) :
    ∃ bad : Bool, (∀ (β : Type) (k : USize → Bool → β), scanNumK a i k = k (scanNumU a i) bad) ∧
      (¬ (scanNumU a i == 0) = true → (lexOkU a i (scanNumU a i) = true ↔ bad = false)) := by
  have hs32 : a.size < 4294967296 := by omega
  have eD : ∀ j, scanDigitsW a j = scanDigits a j := fun j => scanDigitsW_eq a hs _ j rfl
  have eInt : ∀ x, scanIntW a x = scanInt a x := fun x => by simp only [scanIntW, scanInt, eD]; rfl
  have eFrac : ∀ x, scanFracW a x = scanFrac a x := fun x => by simp only [scanFracW, scanFrac, scanDigits1W, scanDigits1, eD]; rfl
  have eExp : ∀ x, scanExpW a x = scanExp a x := fun x => by simp only [scanExpW, scanExp, scanDigits1W, scanDigits1, eD]; rfl
  generalize hi1d : (if byteIsU a i 0x2D then i + 1 else i) = i1
  have hi1le : i1.toNat ≤ a.size := by
    rw [← hi1d]
    by_cases hm : byteIsU a i 0x2D = true
    · simp only [hm, ↓reduceIte]
      rw [byteIsU_eq a hs32] at hm
      have := (byteIs_spec a _ _ hm).1
      rw [succ_toNat a hs i hi]; omega
    · simp only [hm, Bool.false_eq_true, ↓reduceIte]; exact hi
  have hLm : LexRun a i.toNat i1.toNat := by
    rw [← hi1d]
    by_cases hm : byteIsU a i 0x2D = true
    · simp only [hm, ↓reduceIte]
      rw [byteIsU_eq a hs32] at hm
      obtain ⟨hlt, hbi⟩ := byteIs_spec a _ _ hm
      rw [succ_toNat a hs i hi]
      exact LexRun.one hlt (by rw [hbi]; decide)
    · simp only [hm, Bool.false_eq_true, ↓reduceIte]; exact LexRun.refl a _
  by_cases h1 : (scanIntU a i1 == 0) = true
  · refine ⟨false, fun β k => ?_, fun hne => ?_⟩
    · unfold scanNumK scanNumU; simp only [hi1d, h1, ↓reduceIte]
    · exfalso; apply hne; unfold scanNumU; simp only [hi1d, h1, ↓reduceIte]; rfl
  · rcases scanIntU_eq a hs i1 hi1le with ⟨z, -⟩ | ⟨n1, ho1, hr1, hp1, hb1⟩
    · exact absurd ((usize_beq_zero _).2 z) h1
    · have hn1 : scanInt a i1.toNat = some n1 := by rw [← eInt]; exact ho1
      by_cases h2 : (scanFracU a (scanIntU a i1) == 0) = true
      · refine ⟨false, fun β k => ?_, fun hne => ?_⟩
        · unfold scanNumK scanNumU; simp only [hi1d, h1, h2, Bool.false_eq_true, ↓reduceIte]
        · exfalso; apply hne; unfold scanNumU; simp only [hi1d, h1, h2, Bool.false_eq_true, ↓reduceIte]; rfl
      · rcases scanFracU_eq a hs (scanIntU a i1) (by omega) (by omega) with ⟨z, -⟩ | ⟨n2, ho2, hr2, hp2, hb2⟩
        · exact absurd ((usize_beq_zero _).2 z) h2
        · have hn2 : scanFrac a n1 = some n2 := by rw [← eFrac, ← hr1]; exact ho2
          refine ⟨scanExpU a (scanFracU a (scanIntU a i1)) != scanFracU a (scanIntU a i1) && (byteIsU a (scanFracU a (scanIntU a i1)) 0x45 || (byteIsU a (scanFracU a (scanIntU a i1)) 0x65 && byteIsU a (scanFracU a (scanIntU a i1) + 1) 0x2B)), fun β k => ?_, fun hne => ?_⟩
          · unfold scanNumK scanNumU; simp only [hi1d, h1, h2, Bool.false_eq_true, ↓reduceIte]
          · unfold scanNumU at hne ⊢
            simp only [hi1d, h1, h2, Bool.false_eq_true, ↓reduceIte] at hne ⊢
            generalize hr2d : scanFracU a (scanIntU a i1) = r2 at *
            rcases scanExpU_eq a hs r2 (by omega) (by omega) with ⟨z, -⟩ | ⟨nj, ho3, hrj, hpj, hbj⟩
            · exact absurd ((usize_beq_zero _).2 z) hne
            · have hn3 : scanExp a n2 = some nj := by rw [← eExp, ← hr2]; exact ho3
              have hLint := scanInt_lex a _ _ hn1
              have hLfrac := scanFrac_lex a _ _ hn2
              have hLpre : LexRun a i.toNat n2 := (hLm.trans hLint).trans hLfrac
              have hLm' := hLm
              rw [lexOkU_eq a hs _ (by omega) _ i rfl, lexOk_eq a hs _ (by omega), hrj]
              rw [lexRun_forall a _ i.toNat nj rfl]
              have hn2le : n2 ≤ a.size := hb2
              have hpre := lexRun_of_LexRun a i.toNat n2 hLpre hn2le
              have hexp := exp_lex a n2 nj hn2le hn3
              rw [lexRun_forall a _ n2 nj rfl] at hexp
              have hr2n : (r2 + 1).toNat = r2.toNat + 1 := succ_toNat a hs r2 (by omega)
              have hflag : (byteIsU a r2 0x45 || (byteIsU a r2 0x65 && byteIsU a (r2 + 1) 0x2B)) = (byteIs a n2 0x45 || (byteIs a n2 0x65 && byteIs a (n2 + 1) 0x2B)) := by
                rw [byteIsU_eq a hs32, byteIsU_eq a hs32, byteIsU_eq a hs32, hr2n, hr2]
              have hdet : ((scanExpU a r2 != r2) && (byteIsU a r2 0x45 || (byteIsU a r2 0x65 && byteIsU a (r2 + 1) 0x2B))) = (byteIsU a r2 0x45 || (byteIsU a r2 0x65 && byteIsU a (r2 + 1) 0x2B)) := by
                by_cases hEq : scanExpU a r2 = r2
                · have hnj : nj = n2 := by rw [← hrj, hEq, hr2]
                  have hfl : (byteIs a n2 0x45 || (byteIs a n2 0x65 && byteIs a (n2 + 1) 0x2B)) = false := hexp.1 (fun k h1 h2 => by exfalso; omega)
                  rw [← hflag] at hfl
                  simp only [hEq, bne_self_eq_false, Bool.false_and, hfl]
                · have : (scanExpU a r2 != r2) = true := by simpa using hEq
                  simp only [this, Bool.true_and]
              rw [hdet, hflag, ← hexp]
              constructor
              · intro hall k hk1 hk2; have := hLpre.1; exact hall k (by omega) hk2
              · intro hall k hk1 hk2
                by_cases hk : k < n2
                · exact hpre k hk1 hk
                · exact hall k (by omega) hk2

end LeanJsonProofs
