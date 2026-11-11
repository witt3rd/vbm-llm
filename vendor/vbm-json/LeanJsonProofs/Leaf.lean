import LeanJson
/-! # The reference against the grammar: whitespace, digits, numbers

For each nonterminal, `*_sound` (the function accepts, so the relation holds on what it read) and `*_complete` (the relation holds, so the function reads exactly that, whatever
follows, when what follows cannot extend the production: `Stop`). Maximal munch is the only reason a follow condition exists. -/
namespace LeanJson

/-- What may follow a value: nothing, whitespace, a comma, a closing bracket or brace. None of these can extend a number. -/
def stopB (b : UInt8) : Bool := isWs b || b == 0x2C || b == 0x5D || b == 0x7D

/-- Every first byte of `ys` (there is at most one) satisfies `P`. -/
def H (P : UInt8 → Prop) (ys : Bytes) : Prop := ∀ b r, ys = b :: r → P b

def Stop (ys : Bytes) : Prop := H (fun b => stopB b = true) ys

theorem H_nil {P} : H P [] := by intro b r h; cases h
theorem H_cons {P b} (hb : P b) (r : Bytes) : H P (b :: r) := by
  intro b' r' h; cases h; exact hb

theorem H_append {P xs} (ys : Bytes) (hx : xs = [] → H P ys) (hc : ∀ x r, xs = x :: r → P x) : H P (xs ++ ys) := by
  cases xs with
  | nil => exact hx rfl
  | cons x r => intro b r' h; simp at h; obtain ⟨rfl, _⟩ := h; exact hc _ _ rfl

theorem H_mono {P Q : UInt8 → Prop} (h : ∀ b, P b → Q b) {ys} (hy : H P ys) : H Q ys := fun b r e => h b (hy b r e)

/-! ## whitespace -/

theorem skipWs_sound (bs : Bytes) : ∃ w, bs = w ++ skipWs bs ∧ Ws w := by
  induction bs with
  | nil => exact ⟨[], rfl, .nil⟩
  | cons b bs ih =>
    by_cases h : isWs b = true
    · obtain ⟨w, hw, hws⟩ := ih
      refine ⟨b :: w, ?_, .cons h hws⟩
      simp only [skipWs, h, ite_true, List.cons_append]; rw [← hw]
    · exact ⟨[], by simp [skipWs, h], .nil⟩

theorem skipWs_head (bs : Bytes) : H (fun b => isWs b = false) (skipWs bs) := by
  induction bs with
  | nil => exact H_nil
  | cons b bs ih =>
    by_cases h : isWs b = true
    · simpa [skipWs, h] using ih
    · simp only [skipWs, h]; simp at h; exact H_cons h _

theorem skipWs_complete {w : Bytes} (h : Ws w) {rest : Bytes} (hr : H (fun b => isWs b = false) rest) : skipWs (w ++ rest) = rest := by
  induction h with
  | nil => cases rest with
    | nil => rfl
    | cons b r => simp [skipWs, hr b r rfl]
  | cons hb _ ih => simp [skipWs, hb, ih]

theorem skipWs_nil_of {w : Bytes} (h : Ws w) : skipWs w = [] := by
  simpa using skipWs_complete h (rest := []) H_nil

/-! ## digits -/

theorem digits_sound (bs : Bytes) : ∃ pre, bs = pre ++ (digits bs).2 ∧ Digits pre (digits bs).1 := by
  induction bs with
  | nil => exact ⟨[], rfl, .nil⟩
  | cons b bs ih =>
    cases hd : digitVal b with
    | none => exact ⟨[], by simp [digits, hd], by simpa [digits, hd] using Digits.nil⟩
    | some d =>
      obtain ⟨pre, hp, hdg⟩ := ih
      refine ⟨b :: pre, ?_, ?_⟩
      · simp only [digits, hd, List.cons_append]; rw [← hp]
      · simp only [digits, hd]; exact .cons hd hdg

theorem digits_complete {pre : Bytes} {ds : List Digit} (h : Digits pre ds) {rest : Bytes} (hr : H (fun b => digitVal b = none) rest) :
    digits (pre ++ rest) = (ds, rest) := by
  induction h with
  | nil => cases rest with
    | nil => rfl
    | cons b r => simp [digits, hr b r rfl]
  | cons hb _ ih => simp [digits, hb, ih]

theorem digits1_sound {bs : Bytes} {x r} (h : digits1 bs = some (x, r)) : ∃ pre, bs = pre ++ r ∧ Digits pre (x.1 :: x.2) := by
  unfold digits1 at h
  cases bs with
  | nil => simp at h
  | cons b bs =>
    simp only at h
    cases hd : digitVal b with
    | none => simp [hd] at h
    | some d =>
      simp only [hd, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨pre, hp, hdg⟩ := digits_sound bs
      exact ⟨b :: pre, by simp [← hp], .cons hd hdg⟩

theorem digits1_complete {pre : Bytes} {ds : List Digit} (h : Digits pre ds) (hne : ds ≠ []) {rest : Bytes} (hr : H (fun b => digitVal b = none) rest) :
    digits1 (pre ++ rest) = some ((ds.head hne, ds.tail), rest) := by
  cases h with
  | nil => exact absurd rfl hne
  | cons hb hd => simp [digits1, hb, digits_complete hd hr]

/-! ## numbers -/

theorem stop_cases {b : UInt8} (h : stopB b = true) : b = 0x20 ∨ b = 0x09 ∨ b = 0x0A ∨ b = 0x0D ∨ b = 0x2C ∨ b = 0x5D ∨ b = 0x7D := by
  simp [stopB, isWs] at h
  rcases h with ((((((h | h) | h) | h) | h) | h) | h) <;> simp [h]

theorem stop_not_number {b : UInt8} (h : stopB b = true) : digitVal b = none ∧ b ≠ 0x2D ∧ b ≠ 0x2E ∧ b ≠ 0x65 ∧ b ≠ 0x45 := by
  rcases stop_cases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Nothing that could extend a number follows. -/
def NS (ys : Bytes) : Prop := H (fun b => digitVal b = none ∧ b ≠ 0x2D ∧ b ≠ 0x2E ∧ b ≠ 0x65 ∧ b ≠ 0x45) ys

theorem NS_of_stop {ys : Bytes} (h : Stop ys) : NS ys := H_mono (fun _ hb => stop_not_number hb) h

theorem parseMinus_sound (bs : Bytes) : ∃ pre, bs = pre ++ (parseMinus bs).2 ∧ Minus pre (parseMinus bs).1 := by
  cases bs with
  | nil => exact ⟨[], rfl, .none⟩
  | cons b r =>
    by_cases h : b = 0x2D
    · subst h; exact ⟨[0x2D], rfl, by simpa [parseMinus] using Minus.minus⟩
    · exact ⟨[], by simp [parseMinus, h], by simpa [parseMinus, h] using Minus.none⟩

theorem parseMinus_complete {pre : Bytes} {neg : Bool} (h : Minus pre neg) {rest : Bytes} (hr : H (fun b => b ≠ 0x2D) rest) :
    parseMinus (pre ++ rest) = (neg, rest) := by
  cases h with
  | none => cases rest with
    | nil => rfl
    | cons b r => simp [parseMinus, hr b r rfl]
  | minus => simp [parseMinus]

theorem parseInt_sound {bs : Bytes} {ip r} (h : parseInt bs = some (ip, r)) : ∃ pre, bs = pre ++ r ∧ IntP pre ip := by
  cases bs with
  | nil => simp [parseInt] at h
  | cons b bs =>
    by_cases hz : b = 0x30
    · subst hz; simp [parseInt] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨[0x30], rfl, .zero⟩
    · simp only [parseInt, beq_iff_eq, hz, ite_false] at h
      cases hl : digit19 b with
      | none => simp [hl] at h
      | some l =>
        simp only [hl, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨pre, hp, hdg⟩ := digits_sound bs
        exact ⟨b :: pre, by simp [← hp], .nz hl hdg⟩

theorem digit19_ne {b : UInt8} {l : Fin 9} (h : digit19 b = some l) : b ≠ 0x30 := by
  intro e; subst e; simp [digit19] at h

theorem parseInt_complete {pre : Bytes} {ip : IntPart} (h : IntP pre ip) {rest : Bytes} (hr : H (fun b => digitVal b = none) rest) :
    parseInt (pre ++ rest) = some (ip, rest) := by
  cases h with
  | zero => simp [parseInt]
  | @nz b l ds rs hb hd => simp [parseInt, digit19_ne hb, hb, digits_complete hd hr]

theorem parseFrac_sound {bs : Bytes} {fr r} (h : parseFrac bs = some (fr, r)) : ∃ pre, bs = pre ++ r ∧ FracP pre fr := by
  cases bs with
  | nil => simp [parseFrac] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨[], rfl, .none⟩
  | cons b bs =>
    by_cases hd : b = 0x2E
    · subst hd
      simp only [parseFrac, beq_self_eq_true, ite_true] at h
      cases h1 : digits1 bs with
      | none => simp [h1] at h
      | some p =>
        obtain ⟨x, r1⟩ := p
        simp only [h1, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨pre, hp, hdg⟩ := digits1_sound h1
        cases hdg with
        | cons hb hd' => exact ⟨0x2E :: _ :: _, by simp [hp], .some hb hd'⟩
    · simp [parseFrac, hd] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨[], rfl, .none⟩

theorem parseFrac_complete {f : Bytes} {fr} (hf : FracP f fr) {e : Bytes} {ex} (he : ExpP e ex) {rest : Bytes} (hr : NS rest) :
    parseFrac (f ++ (e ++ rest)) = some (fr, e ++ rest) := by
  have hne : H (fun b => digitVal b = none ∧ b ≠ 0x2E) (e ++ rest) := by
    cases he with
    | none => exact H_mono (fun b hb => ⟨hb.1, hb.2.2.1⟩) hr
    | some h1 _ _ _ => rename_i e'; apply H_cons; rcases h1 with rfl | rfl <;> decide
  cases hf with
  | none => cases hx : e ++ rest with
    | nil => simp [parseFrac]
    | cons b r => simp [parseFrac, (hne b r hx).2]
  | @some b d ds rs hb hd =>
    have h1 := digits1_complete (.cons hb hd) (by simp) (H_mono (fun b h => h.1) hne)
    simp only [List.cons_append] at h1 ⊢
    simp [parseFrac, h1]

theorem digitVal_not_sign {b : UInt8} {d : Digit} (h : digitVal b = some d) : b ≠ 0x2B ∧ b ≠ 0x2D := by
  constructor <;> (intro e; subst e; simp [digitVal] at h)

theorem parseESign_sound (bs : Bytes) : ∃ pre, bs = pre ++ (parseESign bs).2 ∧ ESign pre (parseESign bs).1 := by
  cases bs with
  | nil => exact ⟨[], rfl, .none⟩
  | cons c r =>
    by_cases h1 : c = 0x2B
    · subst h1; exact ⟨[0x2B], rfl, by simpa [parseESign] using ESign.plus⟩
    · by_cases h2 : c = 0x2D
      · subst h2; exact ⟨[0x2D], rfl, by simpa [parseESign] using ESign.minus⟩
      · exact ⟨[], by simp [parseESign, h1, h2], by simpa [parseESign, h1, h2] using ESign.none⟩

theorem parseESign_complete {pre : Bytes} {neg : Bool} (h : ESign pre neg) {rest : Bytes} (hr : H (fun b => b ≠ 0x2B ∧ b ≠ 0x2D) rest) :
    parseESign (pre ++ rest) = (neg, rest) := by
  cases h with
  | none => cases rest with
    | nil => rfl
    | cons b r => simp [parseESign, (hr b r rfl).1, (hr b r rfl).2]
  | plus => simp [parseESign]
  | minus => simp [parseESign]

theorem parseExp_sound {bs : Bytes} {ex r} (h : parseExp bs = some (ex, r)) : ∃ pre, bs = pre ++ r ∧ ExpP pre ex := by
  cases bs with
  | nil => simp [parseExp] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨[], rfl, .none⟩
  | cons e rs =>
    by_cases he : (e == 0x65 || e == 0x45) = true
    · simp only [parseExp, he, ite_true] at h
      unfold parseExpBody at h
      obtain ⟨sgb, hsg, hesign⟩ := parseESign_sound rs
      cases h1 : digits1 (parseESign rs).2 with
      | none => simp [h1] at h
      | some p =>
        obtain ⟨⟨d, dl⟩, r1⟩ := p
        simp only [h1, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨pre, hp, hdg⟩ := digits1_sound h1
        cases hdg with
        | @cons b d' bs' ds' hb hd' =>
          have hrs : rs = sgb ++ (b :: bs' ++ r1) := by
            calc rs = sgb ++ (parseESign rs).2 := hsg
              _ = sgb ++ (b :: bs' ++ r1) := by rw [hp]
          refine ⟨e :: (sgb ++ b :: bs'), ?_, ?_⟩
          · simp [hrs]
          · exact .some (by simpa using he) hesign hb hd'
    · simp [parseExp, he] at h; obtain ⟨rfl, rfl⟩ := h
      exact ⟨[], rfl, .none⟩

theorem parseExp_complete {e : Bytes} {ex} (he : ExpP e ex) {rest : Bytes} (hr : NS rest) : parseExp (e ++ rest) = some (ex, rest) := by
  cases he with
  | none => cases rest with
    | nil => rfl
    | cons b r => have := hr b r rfl; simp [parseExp, this.2.2.2.1, this.2.2.2.2]
  | @some e' sg neg b d ds rs h1 hs hb hd =>
    have hS := parseESign_complete hs (rest := b :: (ds ++ rest)) (H_cons (digitVal_not_sign hb) _)
    have hD := digits1_complete (.cons hb hd) (by simp) (rest := rest) (H_mono (fun b h => h.1) hr)
    simp only [List.cons_append] at hD
    have he' : (e' == 0x65 || e' == 0x45) = true := by rcases h1 with rfl | rfl <;> decide
    simp [parseExp, he', parseExpBody, hS, hD]

theorem parseNum_sound {bs : Bytes} {n r} (h : parseNum bs = some (n, r)) : ∃ pre, bs = pre ++ r ∧ Num pre n := by
  unfold parseNum at h
  simp only at h
  obtain ⟨pm, hpm, hM⟩ := parseMinus_sound bs
  cases h1 : parseInt (parseMinus bs).2 with
  | none => simp [h1] at h
  | some p1 =>
    obtain ⟨ip, r1⟩ := p1
    simp only [h1] at h
    cases h2 : parseFrac r1 with
    | none => simp [h2] at h
    | some p2 =>
      obtain ⟨fr, r2⟩ := p2
      simp only [h2] at h
      cases h3 : parseExp r2 with
      | none => simp [h3] at h
      | some p3 =>
        obtain ⟨ex, r3⟩ := p3
        simp only [h3, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨pi, hpi, hI⟩ := parseInt_sound h1
        obtain ⟨pf, hpf, hF⟩ := parseFrac_sound h2
        obtain ⟨pe, hpe, hE⟩ := parseExp_sound h3
        refine ⟨pm ++ pi ++ pf ++ pe, ?_, .mk hM hI hF hE⟩
        calc bs = pm ++ (parseMinus bs).2 := hpm
          _ = pm ++ (pi ++ r1) := by rw [hpi]
          _ = pm ++ (pi ++ (pf ++ r2)) := by rw [hpf]
          _ = pm ++ (pi ++ (pf ++ (pe ++ r3))) := by rw [hpe]
          _ = _ := by simp

theorem digit19_not_minus {b : UInt8} {l : Fin 9} (h : digit19 b = some l) : b ≠ 0x2D := by
  intro e; subst e; simp [digit19] at h

theorem parseNum_complete {pre : Bytes} {n : Number} (h : Num pre n) {rest : Bytes} (hr : NS rest) :
    parseNum (pre ++ rest) = some (n, rest) := by
  cases h with
  | @mk m i f e neg ip fr ex hm hi hf he =>
    have hE : H (fun b => digitVal b = none) (f ++ (e ++ rest)) := by
      apply H_append
      · intro hf0
        cases he with
        | none => exact H_mono (fun b hb => hb.1) hr
        | some h1 _ _ _ => apply H_cons; rcases h1 with rfl | rfl <;> decide
      · intro x r hx
        cases hf with
        | none => cases hx
        | some => simp at hx; obtain ⟨rfl, _⟩ := hx; decide
    have hMn : H (fun b => b ≠ 0x2D) (i ++ (f ++ (e ++ rest))) := by
      cases hi with
      | zero => apply H_cons; decide
      | nz hb _ => apply H_cons; exact digit19_not_minus hb
    have e1 := parseMinus_complete hm hMn
    have e2 := parseInt_complete hi hE
    have e3 := parseFrac_complete hf he hr
    have e4 := parseExp_complete he hr
    simp only [List.append_assoc]
    simp [parseNum, e1, e2, e3, e4]

end LeanJson
