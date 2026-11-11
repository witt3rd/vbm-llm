import LeanJsonProofs.Reference
/-! # The reference against the grammar: completeness and unambiguity

`val_complete`: a derivation gives the verdict `ok`, whatever follows (when what follows is a `Stop`: it cannot extend a number), given enough fuel and depth budget. -/
namespace LeanJson

/-- A byte that can start a value or a member: not whitespace, not a closing bracket or brace. -/
def HeadOK (b : UInt8) : Prop := isWs b = false ∧ b ≠ 0x5D ∧ b ≠ 0x7D
instance : DecidablePred HeadOK := fun b => inferInstanceAs (Decidable (isWs b = false ∧ b ≠ 0x5D ∧ b ≠ 0x7D))

theorem digit19_ne_lit {b : UInt8} {l : Fin 9} (h : digit19 b = some l) (k : UInt8) (hk : k.toNat < 0x31 ∨ 0x39 < k.toNat) : b ≠ k := by
  intro e; subst e
  simp only [digit19] at h
  split at h
  · omega
  · simp at h

theorem num_head {bs : Bytes} {n : Number} (h : Num bs n) :
    ∃ b r, bs = b :: r ∧ (b = 0x2D ∨ b = 0x30 ∨ ∃ l, digit19 b = some l) := by
  cases h with
  | mk hm hi hf he =>
    cases hm with
    | minus => exact ⟨0x2D, _, rfl, .inl rfl⟩
    | none =>
      cases hi with
      | zero => exact ⟨0x30, _, rfl, .inr (.inl rfl)⟩
      | nz hb _ => exact ⟨_, _, rfl, .inr (.inr ⟨_, hb⟩)⟩

theorem val_head {bs : Bytes} {v : Value} (h : Val bs v) : ∃ b r, bs = b :: r ∧ HeadOK b := by
  cases h with
  | null => exact ⟨_, _, rfl, by decide⟩
  | true => exact ⟨_, _, rfl, by decide⟩
  | false => exact ⟨_, _, rfl, by decide⟩
  | num hN =>
    obtain ⟨b, r, rfl, hb⟩ := num_head hN
    refine ⟨b, r, rfl, ?_⟩
    rcases hb with rfl | rfl | ⟨l, hl⟩
    · decide
    · decide
    · have h1 := digit19_ne_lit hl 0x5D (by decide)
      have h2 := digit19_ne_lit hl 0x7D (by decide)
      refine ⟨?_, h1, h2⟩
      simp only [isWs, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
      exact ⟨⟨⟨digit19_ne_lit hl 0x20 (by decide), digit19_ne_lit hl 0x09 (by decide)⟩, digit19_ne_lit hl 0x0A (by decide)⟩, digit19_ne_lit hl 0x0D (by decide)⟩
  | str hS => cases hS with | mk => exact ⟨_, _, rfl, by decide⟩
  | arr0 => exact ⟨_, _, rfl, by decide⟩
  | arr => exact ⟨_, _, rfl, by decide⟩
  | obj0 => exact ⟨_, _, rfl, by decide⟩
  | obj => exact ⟨_, _, rfl, by decide⟩

theorem elems_head {es : Bytes} {vs : List Value} (h : Elems es vs) : ∃ b r, es = b :: r ∧ HeadOK b := by
  cases h with
  | one hV => exact val_head hV
  | cons hV _ _ _ =>
    obtain ⟨b, r, rfl, hb⟩ := val_head hV
    exact ⟨b, _, rfl, hb⟩

theorem member_head {b : Bytes} {kv : String × Value} (h : Member b kv) : ∃ c r, b = c :: r ∧ HeadOK c := by
  cases h with
  | mk hK => cases hK with | mk => exact ⟨_, _, rfl, by decide⟩

theorem members_head {ms : Bytes} {kvs : List (String × Value)} (h : Members ms kvs) : ∃ b r, ms = b :: r ∧ HeadOK b := by
  cases h with
  | one hM => exact member_head hM
  | cons hM _ _ _ =>
    obtain ⟨b, r, rfl, hb⟩ := member_head hM
    exact ⟨b, _, rfl, hb⟩

/-- After the elements there is no comma. -/
def NC (rest : Bytes) : Prop := H (fun c => c ≠ 0x2C) (skipWs rest)

theorem ws_head {w : Bytes} (h : Ws w) : H (fun b => isWs b = true) w := by
  cases h with
  | nil => exact H_nil
  | cons hb _ => exact H_cons hb _

theorem val_ne_nil {b : Bytes} {v : Value} (h : Val b v) : 0 < b.length := by
  obtain ⟨c, r, rfl, _⟩ := val_head h; simp

theorem parseKey_complete {k w : Bytes} {s : String} (hK : Str k s) (hW : Ws w) (Y : Bytes) :
    parseKey (k ++ (w ++ 0x3A :: Y)) = some (s, Y) := by
  have h1 := parseStr_complete hK (w ++ 0x3A :: Y)
  have h2 := skipWs_complete hW (rest := 0x3A :: Y) (H_cons (by decide) _)
  simp [parseKey, h1, h2]

theorem stop_ws_append {w : Bytes} (hW : Ws w) (c : UInt8) (hc : stopB c = true) (r : Bytes) : Stop (w ++ c :: r) :=
  H_append _ (fun _ => H_cons hc _) (fun x r' hx => by
    have := ws_head hW x r' hx; simp [stopB, this])

mutual
theorem val_complete {pre : Bytes} {v : Value} (h : Val pre v) (d n : Nat) (rest : Bytes) (hd : v.depth ≤ d) (hn : 2 * pre.length < n)
    (hs : Stop rest) : parseVal d n (pre ++ rest) = .ok (v, rest) := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  cases h with
  | null => simp [parseVal, lit]
  | true => simp [parseVal, lit]
  | false => simp [parseVal, lit]
  | num hN =>
    obtain ⟨b, r, rfl, hb⟩ := num_head hN
    have hN' := parseNum_complete hN (NS_of_stop hs)
    simp only [List.cons_append] at hN' ⊢
    have hne : ∀ k : UInt8, k ≠ 0x2D → k ≠ 0x30 → (k.toNat < 0x31 ∨ 0x39 < k.toNat) → (b == k) = false := by
      intro k h1 h2 h3
      rcases hb with rfl | rfl | ⟨l, hl⟩
      · simpa using Ne.symm h1
      · simpa using Ne.symm h2
      · simp; exact digit19_ne_lit hl k h3
    simp [parseVal, hne 0x5B (by decide) (by decide) (by decide), hne 0x7B (by decide) (by decide) (by decide), hne 0x22 (by decide) (by decide) (by decide), hne 0x6E (by decide) (by decide) (by decide), hne 0x74 (by decide) (by decide) (by decide), hne 0x66 (by decide) (by decide) (by decide), hN']
  | str hS =>
    cases hS with
    | mk hC =>
      have hS' := parseStr_complete (.mk hC) rest
      simp only [List.cons_append, List.append_assoc, List.nil_append] at hS' ⊢
      simp [parseVal, hS']
  | arr0 hW =>
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by simp [Value.depth] at hd; omega⟩
    have hSk := skipWs_complete hW (rest := 0x5D :: rest) (H_cons (by decide) _)
    simp only [List.cons_append, List.append_assoc] at hSk ⊢
    simp [parseVal, hSk]
  | @arr w1 es w2 vs hW1 hE hW2 =>
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by simp [Value.depth] at hd; omega⟩
    obtain ⟨c, r', rfl, hc⟩ := elems_head hE
    have hdep : depthList vs ≤ d' := by simp [Value.depth] at hd; omega
    have hsk2 := skipWs_complete hW2 (rest := 0x5D :: rest) (H_cons (by decide) _)
    have hnc : NC (w2 ++ 0x5D :: rest) := by unfold NC; rw [hsk2]; exact H_cons (by decide) _
    have hEc := elems_complete hE d' n' (w2 ++ 0x5D :: rest) hdep (by simp at hn ⊢; omega) (stop_ws_append hW2 0x5D (by decide) rest) hnc
    have hsk1 := skipWs_complete hW1 (rest := c :: (r' ++ (w2 ++ 0x5D :: rest))) (H_cons hc.1 _)
    simp only [List.cons_append, List.append_assoc] at hEc hsk1 hsk2 ⊢
    simp [parseVal, hsk1, hc.2.1, hEc, hsk2]
  | obj0 hW =>
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by simp [Value.depth] at hd; omega⟩
    have hSk := skipWs_complete hW (rest := 0x7D :: rest) (H_cons (by decide) _)
    simp only [List.cons_append, List.append_assoc] at hSk ⊢
    simp [parseVal, hSk]
  | @obj w1 ms w2 kvs hW1 hM hW2 =>
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by simp [Value.depth] at hd; omega⟩
    obtain ⟨c, r', rfl, hc⟩ := members_head hM
    have hdep : depthMembers kvs ≤ d' := by simp [Value.depth] at hd; omega
    have hsk2 := skipWs_complete hW2 (rest := 0x7D :: rest) (H_cons (by decide) _)
    have hnc : NC (w2 ++ 0x7D :: rest) := by unfold NC; rw [hsk2]; exact H_cons (by decide) _
    have hEc := members_complete hM d' n' (w2 ++ 0x7D :: rest) hdep (by simp at hn ⊢; omega) (stop_ws_append hW2 0x7D (by decide) rest) hnc
    have hsk1 := skipWs_complete hW1 (rest := c :: (r' ++ (w2 ++ 0x7D :: rest))) (H_cons hc.1 _)
    simp only [List.cons_append, List.append_assoc] at hEc hsk1 hsk2 ⊢
    simp [parseVal, hsk1, hc.2.2, hEc, hsk2]

theorem elems_complete {es : Bytes} {vs : List Value} (h : Elems es vs) (d n : Nat) (rest : Bytes) (hd : depthList vs ≤ d)
    (hn : 2 * es.length + 2 < n) (hs : Stop rest) (hnc : NC rest) : parseElems d n (es ++ rest) = .ok (vs, rest) := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  cases h with
  | one hV =>
    have hv := val_complete hV d n' rest (by simpa [depthList] using hd) (by omega) hs
    cases hsr : skipWs rest with
    | nil => simp [parseElems, hv, hsr]
    | cons c r' => simp [parseElems, hv, hsr, hnc c r' hsr]
  | @cons b w1 w2 es' v vs' hV hW1 hW2 hE =>
    have hbl := val_ne_nil hV
    have hd1 : v.depth ≤ d := by unfold depthList at hd; omega
    have hd2 : depthList vs' ≤ d := by unfold depthList at hd; omega
    have hv := val_complete hV d n' (w1 ++ 0x2C :: (w2 ++ (es' ++ rest))) hd1 (by simp at hn; omega) (stop_ws_append hW1 0x2C (by decide) _)
    have hsk1 := skipWs_complete hW1 (rest := 0x2C :: (w2 ++ (es' ++ rest))) (H_cons (by decide) _)
    obtain ⟨c, r', hes, hc⟩ := elems_head hE
    have hsk2 := skipWs_complete hW2 (rest := es' ++ rest) (by rw [hes]; exact H_cons hc.1 _)
    have hrec := elems_complete hE d n' rest hd2 (by simp at hn; omega) hs hnc
    simp only [List.cons_append, List.append_assoc] at hv hsk1 hsk2 hrec ⊢
    simp [parseElems, hv, hsk1, hsk2, hrec]

theorem members_complete {ms : Bytes} {kvs : List (String × Value)} (h : Members ms kvs) (d n : Nat) (rest : Bytes) (hd : depthMembers kvs ≤ d)
    (hn : 2 * ms.length + 2 < n) (hs : Stop rest) (hnc : NC rest) : parseMembers d n (ms ++ rest) = .ok (kvs, rest) := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  cases h with
  | one hM =>
    cases hM with
    | @mk k w1 w2 b s v hK hW1 hW2 hV =>
      have hbl := val_ne_nil hV
      simp [depthMembers] at hd
      have hk := parseKey_complete hK hW1 (w2 ++ (b ++ rest))
      obtain ⟨c, r', hb, hc⟩ := val_head hV
      have hsk2 := skipWs_complete hW2 (rest := b ++ rest) (by rw [hb]; exact H_cons hc.1 _)
      have hv := val_complete hV d n' rest hd (by simp at hn; omega) hs
      cases hsr : skipWs rest with
      | nil =>
        simp only [List.cons_append, List.append_assoc] at hk hsk2 hv ⊢
        simp [parseMembers, hk, hsk2, hv, hsr]
      | cons c' r'' =>
        simp only [List.cons_append, List.append_assoc] at hk hsk2 hv ⊢
        simp [parseMembers, hk, hsk2, hv, hsr, hnc c' r'' hsr]
  | @cons b w1 w2 ms' kv kvs' hM hW1 hW2 hMs =>
    cases hM with
    | @mk k wa wb vb s v hK hWa hWb hV =>
      have hd1 : v.depth ≤ d := by unfold depthMembers at hd; omega
      have hd2 : depthMembers kvs' ≤ d := by unfold depthMembers at hd; omega
      have hk := parseKey_complete hK hWa (wb ++ (vb ++ (w1 ++ 0x2C :: (w2 ++ (ms' ++ rest)))))
      obtain ⟨c, r', hb, hc⟩ := val_head hV
      have hsk2 := skipWs_complete hWb (rest := vb ++ (w1 ++ 0x2C :: (w2 ++ (ms' ++ rest)))) (by rw [hb]; exact H_cons hc.1 _)
      have hv := val_complete hV d n' (w1 ++ 0x2C :: (w2 ++ (ms' ++ rest))) hd1 (by simp at hn; omega) (stop_ws_append hW1 0x2C (by decide) _)
      have hsk1 := skipWs_complete hW1 (rest := 0x2C :: (w2 ++ (ms' ++ rest))) (H_cons (by decide) _)
      obtain ⟨c2, r2, hes, hc2⟩ := members_head hMs
      have hsk3 := skipWs_complete hW2 (rest := ms' ++ rest) (by rw [hes]; exact H_cons hc2.1 _)
      have hrec := members_complete hMs d n' rest hd2 (by simp at hn; omega) hs hnc
      simp only [List.cons_append, List.append_assoc] at hk hsk2 hv hsk1 hsk3 hrec ⊢
      simp [parseMembers, hk, hsk2, hv, hsk1, hsk3, hrec]
end

end LeanJson
