import LeanJsonProofs.FastLeaf
import LeanJsonProofs.FastFuel
import LeanJsonProofs.Print
import LeanJsonProofs.Policy
/-! # The fast parser refines the reference

`parseFast_eq_parse`: for every input the fast parser returns exactly what the reference `parse` returns, the same value or the same error code (`syntax` or `depth`).

How it is proved. The fast loop `run` and the reference's recursion are two ways to walk the same text. What the enclosing reference calls would still do with a value just read is the function
`kont`, written by structural recursion over the explicit stack (the stack IS the reference's chain of suspended calls, defunctionalised). Two statements, proved together by induction on the fuel:
`run_val` (a value starts at `i`: `run` returns the reference's `pv` on the text from `i`, handed to `kont`) and `run_ret` (a value was just read: `run` returns `kont` of it). The leaves are
`FastLeaf.lean`, the reference's fuel is `FastFuel.lean`. -/
set_option linter.unusedSimpArgs false
namespace LeanJson

/-- After a value in an array: the rest of the elements (the reference's `parseElems`, past its first value). -/
def elemsFrom (d : Nat) (v : Value) (r : Bytes) : Except Error (List Value × Bytes) :=
  match skipWs r with
  | [] => .ok ([v], r)
  | c :: r' =>
    if c == 0x2C then
      match pe d (skipWs r') with
      | .error e => .error e
      | .ok (vs, r'') => .ok (v :: vs, r'')
    else .ok ([v], r)

/-- The same for an object: the first member's key and value are given. -/
def membersFrom (d : Nat) (k : String) (v : Value) (r : Bytes) : Except Error (List (String × Value) × Bytes) :=
  match skipWs r with
  | [] => .ok ([(k, v)], r)
  | c :: r' =>
    if c == 0x2C then
      match pm d (skipWs r') with
      | .error e => .error e
      | .ok (kvs, r'') => .ok ((k, v) :: kvs, r'')
    else .ok ([(k, v)], r)

/-- What the reference does with a value `v` read just before `r`, inside the containers of `st` (innermost first), with nesting budget `d` in the innermost. -/
def kont : Stack → Nat → Value → Bytes → Except Error Value
  | .nil, _, v, r => if (skipWs r).isEmpty then .ok v else .error .syntax
  | .arr acc rest, d, v, r =>
    match elemsFrom d v r with
    | .error e => .error e
    | .ok (vs, r2) =>
      match skipWs r2 with
      | c' :: r3 => if c' == 0x5D then kont rest (d + 1) (.arr (acc.reverse ++ vs)) r3 else .error .syntax
      | [] => .error .syntax
  | .obj acc k rest, d, v, r =>
    match membersFrom d k v r with
    | .error e => .error e
    | .ok (kvs, r2) =>
      match skipWs r2 with
      | c' :: r3 => if c' == 0x7D then kont rest (d + 1) (.obj (acc.reverse ++ kvs)) r3 else .error .syntax
      | [] => .error .syntax

/-- `r >>= k` for the reference's result type. -/
def thenK (r : Except Error (Value × Bytes)) (k : Value → Bytes → Except Error Value) : Except Error Value :=
  match r with
  | .error e => .error e
  | .ok (v, r) => k v r

theorem pe_eq (d : Nat) (bs : Bytes) : pe d bs = (match pv d bs with | .error e => .error e | .ok (v, r) => elemsFrom d v r) := by
  unfold pe
  show parseElems d (2 * bs.length + 1 + 1) bs = _
  rw [parseElems.eq_2 d bs (2 * bs.length + 1)]
  have hv : parseVal d (2 * bs.length + 1) bs = pv d bs := parseVal_canon (Nat.le_refl _)
  rw [← hv]
  rcases hq : parseVal d (2 * bs.length + 1) bs with e | ⟨v, r1⟩
  · rfl
  · have hl : r1.length < bs.length := parseVal_len hq
    simp only [elemsFrom]
    have hl1 := skipWs_len r1
    rcases hs : skipWs r1 with _ | ⟨c, r'⟩
    · rfl
    · rw [hs] at hl1
      have hl2 := skipWs_len r'
      by_cases hc : c = 0x2C
      · simp only [hc, beq_self_eq_true, ite_true]
        rw [parseElems_canon (by simp at hl1; omega)]
        rfl
      · simp [hc]

theorem pm_eq (d : Nat) (bs : Bytes) : pm d bs = (match parseKey bs with
    | none => .error .syntax
    | some (k, r0) => match pv d (skipWs r0) with | .error e => .error e | .ok (v, r) => membersFrom d k v r) := by
  unfold pm
  show parseMembers d (2 * bs.length + 1 + 1) bs = _
  rw [parseMembers.eq_2 d bs (2 * bs.length + 1)]
  rcases hk : parseKey bs with _ | ⟨k, r0⟩
  · rfl
  · have hkl := parseKey_len hk
    have hl0 := skipWs_len r0
    simp only
    have hv : parseVal d (2 * bs.length + 1) (skipWs r0) = pv d (skipWs r0) := parseVal_canon (by omega)
    rw [← hv]
    rcases hq : parseVal d (2 * bs.length + 1) (skipWs r0) with e | ⟨v, r1⟩
    · rfl
    · have hl : r1.length < (skipWs r0).length := parseVal_len hq
      simp only [membersFrom]
      have hl1 := skipWs_len r1
      rcases hs : skipWs r1 with _ | ⟨c, r'⟩
      · rfl
      · rw [hs] at hl1
        have hl2 := skipWs_len r'
        by_cases hc : c = 0x2C
        · simp only [hc, beq_self_eq_true, ite_true]
          rw [parseMembers_canon (by simp at hl1; omega)]
          rfl
        · simp [hc]

theorem pv_arr (d' : Nat) (r : Bytes) : pv (d' + 1) (0x5B :: r) = (match skipWs r with
    | [] => .error .syntax
    | c :: r' =>
      if c == 0x5D then .ok (.arr [], r')
      else match pe d' (c :: r') with
        | .error e => .error e
        | .ok (vs, r2) => match skipWs r2 with
          | c' :: r3 => if c' == 0x5D then .ok (.arr vs, r3) else .error .syntax
          | [] => .error .syntax) := by
  unfold pv
  show parseVal (d' + 1) (2 * (r.length + 1) + 1 + 1) (0x5B :: r) = _
  rw [parseVal.eq_4]
  simp only [beq_self_eq_true, ite_true]
  rcases hs : skipWs r with _ | ⟨c, r'⟩
  · rfl
  · have hl := skipWs_len r
    rw [hs] at hl
    by_cases hc : c = 0x5D
    · subst hc; rfl
    · simp only [beq_iff_eq, hc, ite_false]
      rw [parseElems_canon (d := d') (bs := c :: r') (by simp at hl ⊢; omega)]
      rfl

theorem pv_obj (d' : Nat) (r : Bytes) : pv (d' + 1) (0x7B :: r) = (match skipWs r with
    | [] => .error .syntax
    | c :: r' =>
      if c == 0x7D then .ok (.obj [], r')
      else match pm d' (c :: r') with
        | .error e => .error e
        | .ok (kvs, r2) => match skipWs r2 with
          | c' :: r3 => if c' == 0x7D then .ok (.obj kvs, r3) else .error .syntax
          | [] => .error .syntax) := by
  unfold pv
  show parseVal (d' + 1) (2 * (r.length + 1) + 1 + 1) (0x7B :: r) = _
  rw [parseVal.eq_4]
  simp only [show ((0x7B : UInt8) == 0x5B) = false by decide, beq_self_eq_true, ite_true, ite_false, Bool.false_eq_true]
  rcases hs : skipWs r with _ | ⟨c, r'⟩
  · rfl
  · have hl := skipWs_len r
    rw [hs] at hl
    by_cases hc : c = 0x7D
    · subst hc; rfl
    · simp only [beq_iff_eq, hc, ite_false]
      rw [parseMembers_canon (d := d') (bs := c :: r') (by simp at hl ⊢; omega)]
      rfl

theorem pv_depth_arr (r : Bytes) : pv 0 (0x5B :: r) = .error .depth := by
  unfold pv
  show parseVal 0 (2 * (r.length + 1) + 1 + 1) (0x5B :: r) = _
  rw [parseVal.eq_3]; simp

theorem pv_depth_obj (r : Bytes) : pv 0 (0x7B :: r) = .error .depth := by
  unfold pv
  show parseVal 0 (2 * (r.length + 1) + 1 + 1) (0x7B :: r) = _
  rw [parseVal.eq_3]; simp

/-- A value that is not a container: the reference's result does not depend on the budget. -/
def scalarRef (b : UInt8) (r : Bytes) : Except Error (Value × Bytes) :=
  if b == 0x22 then (match parseStr (b :: r) with | some (s, r') => .ok (.str s, r') | none => .error .syntax)
  else if b == 0x6E then (match lit [0x75, 0x6C, 0x6C] r with | some r' => .ok (.null, r') | none => .error .syntax)
  else if b == 0x74 then (match lit [0x72, 0x75, 0x65] r with | some r' => .ok (.bool true, r') | none => .error .syntax)
  else if b == 0x66 then (match lit [0x61, 0x6C, 0x73, 0x65] r with | some r' => .ok (.bool false, r') | none => .error .syntax)
  else (match parseNum (b :: r) with | some (num, r') => .ok (.num num, r') | none => .error .syntax)

theorem pv_scalar (d : Nat) (b : UInt8) (r : Bytes) (h1 : b ≠ 0x5B) (h2 : b ≠ 0x7B) : pv d (b :: r) = scalarRef b r := by
  unfold pv
  show parseVal d (2 * (r.length + 1) + 1 + 1) (b :: r) = _
  cases d with
  | zero => rw [parseVal.eq_3]; simp only [beq_iff_eq, h1, h2, ite_false, scalarRef]; rfl
  | succ d' => rw [parseVal.eq_4]; simp only [beq_iff_eq, h1, h2, ite_false, scalarRef]; rfl

/-- The array's closing: after the elements, a `]`, then the enclosing context continues. -/
def closeA (st : Stack) (d : Nat) (acc : List Value) : Except Error (List Value × Bytes) → Except Error Value
  | .error e => .error e
  | .ok (vs, r2) =>
    match skipWs r2 with
    | c' :: r3 => if c' == 0x5D then kont st (d + 1) (.arr (acc.reverse ++ vs)) r3 else .error .syntax
    | [] => .error .syntax

def closeO (st : Stack) (d : Nat) (acc : List (String × Value)) : Except Error (List (String × Value) × Bytes) → Except Error Value
  | .error e => .error e
  | .ok (kvs, r2) =>
    match skipWs r2 with
    | c' :: r3 => if c' == 0x7D then kont st (d + 1) (.obj (acc.reverse ++ kvs)) r3 else .error .syntax
    | [] => .error .syntax

theorem kont_arr (acc rest d v r) : kont (.arr acc rest) d v r = closeA rest d acc (elemsFrom d v r) := by
  unfold kont; cases elemsFrom d v r <;> rfl

theorem kont_obj (acc k rest d v r) : kont (.obj acc k rest) d v r = closeO rest d acc (membersFrom d k v r) := by
  unfold kont; cases membersFrom d k v r <;> rfl

theorem closeA_pe (st : Stack) (d : Nat) (acc : List Value) (bs : Bytes) :
    closeA st d acc (pe d bs) = thenK (pv d bs) (kont (.arr acc st) d) := by
  rw [pe_eq]
  rcases pv d bs with e | ⟨v, r⟩
  · rfl
  · simp only [thenK, kont_arr]

theorem closeO_pm (st : Stack) (d : Nat) (acc : List (String × Value)) (bs : Bytes) :
    closeO st d acc (pm d bs) = (match parseKey bs with
      | none => .error .syntax
      | some (k, r0) => thenK (pv d (skipWs r0)) (kont (.obj acc k st) d)) := by
  rw [pm_eq]
  rcases parseKey bs with _ | ⟨k, r0⟩
  · rfl
  · simp only
    rcases pv d (skipWs r0) with e | ⟨v, r⟩
    · rfl
    · simp only [thenK, kont_obj]

theorem closeA_cons (st : Stack) (d : Nat) (acc : List Value) (v : Value) (res : Except Error (List Value × Bytes)) :
    closeA st d acc (match res with | .error e => .error e | .ok (vs, r'') => .ok (v :: vs, r'')) = closeA st d (v :: acc) res := by
  rcases res with e | ⟨vs, r⟩ <;> simp [closeA]

theorem closeO_cons (st : Stack) (d : Nat) (acc : List (String × Value)) (k : String) (v : Value) (res : Except Error (List (String × Value) × Bytes)) :
    closeO st d acc (match res with | .error e => .error e | .ok (kvs, r'') => .ok ((k, v) :: kvs, r'')) = closeO st d ((k, v) :: acc) res := by
  rcases res with e | ⟨vs, r⟩ <;> simp [closeO]

theorem L_length (a : ByteArray) : (L a).length = a.size := by simp [L]

theorem byteAt_lt {a : ByteArray} {i : Nat} {x : UInt8} (h : byteAt a i = some x) : i < a.size := by
  unfold byteAt at h; split at h
  · assumption
  · simp at h

theorem pv_nil (d : Nat) : pv d [] = .error .syntax := by
  unfold pv
  show parseVal d (2 * 0 + 1 + 1) [] = _
  rw [parseVal.eq_2]

theorem thenK_arr (st : Stack) (d' : Nat) (res : Except Error (List Value × Bytes)) :
    thenK (match res with
      | .error e => .error e
      | .ok (vs, r2) => match skipWs r2 with
        | c' :: r3 => if c' == 0x5D then .ok (.arr vs, r3) else .error .syntax
        | [] => .error .syntax) (kont st (d' + 1)) = closeA st d' [] res := by
  rcases res with e | ⟨vs, r2⟩
  · rfl
  · simp only [closeA, List.reverse_nil, List.nil_append]
    rcases skipWs r2 with _ | ⟨c', r3⟩
    · rfl
    · by_cases h : c' == 0x5D <;> simp [thenK, h]

theorem thenK_obj (st : Stack) (d' : Nat) (res : Except Error (List (String × Value) × Bytes)) :
    thenK (match res with
      | .error e => .error e
      | .ok (kvs, r2) => match skipWs r2 with
        | c' :: r3 => if c' == 0x7D then .ok (.obj kvs, r3) else .error .syntax
        | [] => .error .syntax) (kont st (d' + 1)) = closeO st d' [] res := by
  rcases res with e | ⟨vs, r2⟩
  · rfl
  · simp only [closeO, List.reverse_nil, List.nil_append]
    rcases skipWs r2 with _ | ⟨c', r3⟩
    · rfl
    · by_cases h : c' == 0x7D <;> simp [thenK, h]

theorem run_sound (a : ByteArray) (f : Nat) :
    (∀ i v st d, a.size - i + 2 ≤ f → run f a i false v st d = thenK (pv d ((L a).drop i)) (kont st d)) ∧
    (∀ i v st d, a.size - i + 2 ≤ f → run f a i true v st d = kont st d v ((L a).drop i)) := by
  induction f with
  | zero => constructor <;> intros <;> omega
  | succ f ih =>
    obtain ⟨ihV, ihR⟩ := ih
    constructor
    · intro i v st d hf
      rw [run.eq_2]
      rcases hb : byteAt a i with _ | b
      · simp [drop_of_none hb, pv_nil, thenK]
      · have hi := byteAt_lt hb
        rw [drop_of_some hb]
        by_cases h91 : b = 0x5B
        · subst h91
          simp only [beq_self_eq_true, ite_true]
          by_cases hd : d = 0
          · subst hd; simp [pv_depth_arr, thenK]
          · obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
            have hd0 : (d' + 1 == 0) = false := by simp
            simp only [hd0, Bool.false_eq_true, ite_false, Nat.add_sub_cancel, pv_arr, skipWs_eq]
            have hge := skipWsA_ge a (i + 1)
            rcases hb1 : byteAt a (skipWsA a (i + 1)) with _ | c
            · have hb2 : byteIs a (skipWsA a (i + 1)) 0x5D = false := by rw [byteIs_eq]; simp [hb1]
              simp only [hb2, Bool.false_eq_true, ite_false]
              rw [ihV _ _ _ _ (by omega), drop_of_none hb1]
              simp [pv_nil, thenK]
            · have hlt := byteAt_lt hb1
              rw [drop_of_some hb1]
              by_cases h5d : c = 0x5D
              · subst h5d
                have hb2 : byteIs a (skipWsA a (i + 1)) 0x5D = true := by rw [byteIs_eq]; simp [hb1]
                simp only [hb2, ite_true, beq_self_eq_true]
                rw [ihR _ _ _ _ (by omega)]
                rfl
              · have hb2 : byteIs a (skipWsA a (i + 1)) 0x5D = false := by rw [byteIs_eq]; simp [hb1, h5d]
                have h5d' : (c == 0x5D) = false := by simpa using h5d
                simp only [hb2, Bool.false_eq_true, ite_false, h5d']
                rw [ihV _ _ _ _ (by omega), drop_of_some hb1, thenK_arr, closeA_pe]
        · by_cases h7b : b = 0x7B
          · subst h7b
            simp only [show ((0x7B : UInt8) == 0x5B) = false by decide, Bool.false_eq_true, ite_false, beq_self_eq_true, ite_true]
            by_cases hd : d = 0
            · subst hd; simp [pv_depth_obj, thenK]
            · obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
              have hd0 : (d' + 1 == 0) = false := by simp
              simp only [hd0, Bool.false_eq_true, ite_false, Nat.add_sub_cancel, pv_obj, skipWs_eq]
              have hge := skipWsA_ge a (i + 1)
              rcases hb1 : byteAt a (skipWsA a (i + 1)) with _ | c
              · have hb2 : byteIs a (skipWsA a (i + 1)) 0x7D = false := by rw [byteIs_eq]; simp [hb1]
                have hk := parseKeyA_eq a (skipWsA a (i + 1))
                have hpk : parseKeyA a (skipWsA a (i + 1)) = none := by
                  unfold parseKeyA parseStrA; simp [byteIs_eq, hb1]
                simp only [hb2, Bool.false_eq_true, ite_false, hpk]
                rw [drop_of_none hb1]
                simp [thenK]
              · have hlt := byteAt_lt hb1
                by_cases h7d : c = 0x7D
                · subst h7d
                  have hb2 : byteIs a (skipWsA a (i + 1)) 0x7D = true := by rw [byteIs_eq]; simp [hb1]
                  simp only [hb2, ite_true]
                  rw [ihR _ _ _ _ (by omega), drop_of_some hb1]
                  simp [thenK]
                · have hb2 : byteIs a (skipWsA a (i + 1)) 0x7D = false := by rw [byteIs_eq]; simp [hb1, h7d]
                  have h7d' : (c == 0x7D) = false := by simpa using h7d
                  simp only [hb2, Bool.false_eq_true, ite_false]
                  rw [drop_of_some hb1]
                  simp only [h7d', Bool.false_eq_true, ite_false]
                  rw [thenK_obj, closeO_pm, ← drop_of_some hb1]
                  have hk := parseKeyA_eq a (skipWsA a (i + 1))
                  rcases hpk : parseKeyA a (skipWsA a (i + 1)) with _ | ⟨k', j⟩
                  · rw [hpk] at hk
                    rcases hq : parseKey ((L a).drop (skipWsA a (i + 1))) with _ | ⟨k0, r0⟩
                    · simp [hq]
                    · simp [hq, mapDrop] at hk
                  · have hadv := parseKeyA_adv hpk
                    rw [hpk] at hk
                    rcases hq : parseKey ((L a).drop (skipWsA a (i + 1))) with _ | ⟨k0, r0⟩
                    · simp [hq, mapDrop] at hk
                    · simp only [hq, mapDrop, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
                      obtain ⟨rfl, hr0⟩ := hk
                      simp only [hr0]
                      rw [ihV _ _ _ _ (by omega)]
          · have h1 : (b == 0x5B) = false := by simpa using h91
            have h2 : (b == 0x7B) = false := by simpa using h7b
            simp only [h1, h2, Bool.false_eq_true, ite_false]
            rw [pv_scalar d b _ h91 h7b]
            unfold scalarRef
            by_cases h22 : b = 0x22
            · have e : (b == 0x22) = true := by simp [h22]
              simp only [e, ite_true]
              have hs := parseStrA_eq a i
              rw [drop_of_some hb] at hs
              rw [hs]
              rcases hp : parseStrA a i with _ | ⟨s, j⟩
              · simp [thenK]
              · have := parseStrA_adv hp
                simp only [mapDrop, Option.map_some, thenK]
                rw [ihR _ _ _ _ (by omega)]
            · have e : (b == 0x22) = false := by simpa using h22
              simp only [e, Bool.false_eq_true, ite_false]
              by_cases h6e : b = 0x6E
              · have e : (b == 0x6E) = true := by simp [h6e]
                simp only [e, ite_true]
                have hl := litA_eq a [0x75, 0x6C, 0x6C] (i + 1)
                rw [hl]
                rcases hp : litA a (i + 1) [0x75, 0x6C, 0x6C] with _ | j
                · simp [thenK]
                · have := (litA_ge a _ _ _ hp).2 (by simp)
                  simp only [Option.map_some, thenK]
                  rw [ihR _ _ _ _ (by omega)]
              · have e : (b == 0x6E) = false := by simpa using h6e
                simp only [e, Bool.false_eq_true, ite_false]
                by_cases h74 : b = 0x74
                · have e : (b == 0x74) = true := by simp [h74]
                  simp only [e, ite_true]
                  have hl := litA_eq a [0x72, 0x75, 0x65] (i + 1)
                  rw [hl]
                  rcases hp : litA a (i + 1) [0x72, 0x75, 0x65] with _ | j
                  · simp [thenK]
                  · have := (litA_ge a _ _ _ hp).2 (by simp)
                    simp only [Option.map_some, thenK]
                    rw [ihR _ _ _ _ (by omega)]
                · have e : (b == 0x74) = false := by simpa using h74
                  simp only [e, Bool.false_eq_true, ite_false]
                  by_cases h66 : b = 0x66
                  · have e : (b == 0x66) = true := by simp [h66]
                    simp only [e, ite_true]
                    have hl := litA_eq a [0x61, 0x6C, 0x73, 0x65] (i + 1)
                    rw [hl]
                    rcases hp : litA a (i + 1) [0x61, 0x6C, 0x73, 0x65] with _ | j
                    · simp [thenK]
                    · have := (litA_ge a _ _ _ hp).2 (by simp)
                      simp only [Option.map_some, thenK]
                      rw [ihR _ _ _ _ (by omega)]
                  · have e : (b == 0x66) = false := by simpa using h66
                    simp only [e, Bool.false_eq_true, ite_false]
                    have hs := parseNumA_eq a i
                    rw [drop_of_some hb] at hs
                    rw [hs]
                    rcases hp : parseNumA a i with _ | ⟨n, j⟩
                    · simp [thenK]
                    · have := parseNumA_adv hp
                      simp only [mapDrop, Option.map_some, thenK]
                      rw [ihR _ _ _ _ (by omega)]
    · intro i v st d hf
      cases st with
      | nil =>
        rw [run.eq_3, kont, skipWs_eq]
        by_cases h : a.size ≤ skipWsA a i
        · simp [h, List.drop_eq_nil_iff, L_length]
        · simp [h, List.drop_eq_nil_iff, L_length]
      | arr acc rest =>
        rw [run.eq_4, kont_arr]
        unfold elemsFrom
        rw [skipWs_eq]
        try simp only []
        have hge := skipWsA_ge a i
        rcases hb : byteAt a (skipWsA a i) with _ | c
        · simp [byteIs_eq, hb, closeA, skipWs_eq, drop_of_none hb]
        · have hlt := byteAt_lt hb
          rw [drop_of_some hb]
          by_cases h2c : c = 0x2C
          · subst h2c
            have hb' : byteIs a (skipWsA a i) 0x2C = true := by rw [byteIs_eq]; simp [hb]
            have hge2 := skipWsA_ge a (skipWsA a i + 1)
            simp only [hb', ite_true]
            rw [ihV _ _ _ _ (by omega), ← skipWs_eq]
            simp only [beq_self_eq_true, ite_true]
            rw [closeA_cons, closeA_pe]
          · by_cases h5d : c = 0x5D
            · subst h5d
              have hb1 : byteIs a (skipWsA a i) 0x2C = false := by
                rw [byteIs_eq]; simp [hb, h2c]
              have hb2 : byteIs a (skipWsA a i) 0x5D = true := by rw [byteIs_eq]; simp [hb]
              simp only [hb1, hb2, Bool.false_eq_true, ite_true, ite_false]
              rw [ihR _ _ _ _ (by omega)]
              simp [closeA, skipWs_eq, drop_of_some hb]
            · have hb1 : byteIs a (skipWsA a i) 0x2C = false := by
                rw [byteIs_eq]; simp [hb, h2c]
              have hb2 : byteIs a (skipWsA a i) 0x5D = false := by
                rw [byteIs_eq]; simp [hb, h5d]
              simp only [hb1, hb2, Bool.false_eq_true, ite_false]
              simp [closeA, skipWs_eq, drop_of_some hb, h2c, h5d]
      | obj acc k rest =>
        rw [run.eq_5, kont_obj]
        unfold membersFrom
        rw [skipWs_eq]
        try simp only []
        have hge := skipWsA_ge a i
        rcases hb : byteAt a (skipWsA a i) with _ | c
        · simp [byteIs_eq, hb, closeO, skipWs_eq, drop_of_none hb]
        · have hlt := byteAt_lt hb
          rw [drop_of_some hb]
          by_cases h2c : c = 0x2C
          · subst h2c
            have hb' : byteIs a (skipWsA a i) 0x2C = true := by rw [byteIs_eq]; simp [hb]
            have hge2 := skipWsA_ge a (skipWsA a i + 1)
            simp only [hb', ite_true, beq_self_eq_true]
            rw [closeO_cons, closeO_pm, skipWs_eq]
            have hk := parseKeyA_eq a (skipWsA a (skipWsA a i + 1))
            rcases hpk : parseKeyA a (skipWsA a (skipWsA a i + 1)) with _ | ⟨k', j⟩
            · rw [hpk] at hk
              rcases hq : parseKey ((L a).drop (skipWsA a (skipWsA a i + 1))) with _ | ⟨k0, r0⟩
              · simp [hq]
              · simp [hq, mapDrop] at hk
            · have hadv := parseKeyA_adv hpk
              rw [hpk] at hk
              rcases hq : parseKey ((L a).drop (skipWsA a (skipWsA a i + 1))) with _ | ⟨k0, r0⟩
              · simp [hq, mapDrop] at hk
              · simp only [hq, mapDrop, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
                obtain ⟨rfl, hr0⟩ := hk
                simp only [hr0]
                rw [ihV _ _ _ _ (by omega)]
          · by_cases h7d : c = 0x7D
            · subst h7d
              have hb1 : byteIs a (skipWsA a i) 0x2C = false := by
                rw [byteIs_eq]; simp [hb, h2c]
              have hb2 : byteIs a (skipWsA a i) 0x7D = true := by rw [byteIs_eq]; simp [hb]
              simp only [hb1, hb2, Bool.false_eq_true, ite_true, ite_false]
              rw [ihR _ _ _ _ (by omega)]
              simp [closeO, skipWs_eq, drop_of_some hb]
            · have hb1 : byteIs a (skipWsA a i) 0x2C = false := by
                rw [byteIs_eq]; simp [hb, h2c]
              have hb2 : byteIs a (skipWsA a i) 0x7D = false := by
                rw [byteIs_eq]; simp [hb, h7d]
              simp only [hb1, hb2, Bool.false_eq_true, ite_false]
              simp [closeO, skipWs_eq, drop_of_some hb, h2c, h7d]

/-- The fast parser is the reference, on every input: the same value or the same error code. -/
theorem parseFast_eq_parse (a : ByteArray) : parseFast a = parse (L a) := by
  unfold parseFast
  rw [(run_sound a (a.size + 2)).1 _ _ _ _ (by omega)]
  have h0 := skipWs_eq a 0
  rw [List.drop_zero] at h0
  unfold parse
  rw [h0, parseVal_canon (d := maxDepth) (n := 2 * (L a).length + 2) (bs := (L a).drop (skipWsA a 0)) (by simp [L_length]; omega)]
  rcases pv maxDepth ((L a).drop (skipWsA a 0)) with e | ⟨v, r⟩ <;> simp [thenK, kont]

theorem parseFast_list (bs : Bytes) : parseFast ⟨bs.toArray⟩ = parse bs := by
  rw [parseFast_eq_parse]; simp [L]

/-! ## What the reference proves, for the code the exports run

Everything proved of `parse` transfers through `parseFast_eq_parse`. The grammar statements (`parse_ok_iff`, `json_unique`) and the policy examples are restated for `parseFast`. -/

theorem parseFast_sound {a : ByteArray} {v : Value} (h : parseFast a = .ok v) : Json (L a) v ∧ v.depth ≤ maxDepth := by
  rw [parseFast_eq_parse] at h; exact parse_sound h

theorem parseFast_complete {a : ByteArray} {v : Value} (h : Json (L a) v) (hd : v.depth ≤ maxDepth) : parseFast a = .ok v := by
  rw [parseFast_eq_parse]; exact parse_complete h hd

theorem parseFast_ok_iff {a : ByteArray} {v : Value} : parseFast a = .ok v ↔ Json (L a) v ∧ v.depth ≤ maxDepth :=
  ⟨parseFast_sound, fun ⟨h, hd⟩ => parseFast_complete h hd⟩

/-- An error is exactly the absence of an accepted derivation. -/
theorem parseFast_error_iff {a : ByteArray} : (∃ e, parseFast a = .error e) ↔ ¬ ∃ v, Json (L a) v ∧ v.depth ≤ maxDepth := by
  rw [parseFast_eq_parse]; exact parse_error_iff

/-- Every input gets a value the grammar derives within the limit, or an error code. -/
theorem parseFast_total (a : ByteArray) : (∃ v, parseFast a = .ok v ∧ Json (L a) v ∧ v.depth ≤ maxDepth) ∨ ∃ e, parseFast a = .error e := by
  rw [parseFast_eq_parse]; exact parse_total (L a)

/-- The printer's output is read back by the fast parser (for every value within the limit). -/
theorem parseFast_print {v : Value} (h : v.depth ≤ maxDepth) : parseFast ⟨(print v).toArray⟩ = .ok v := by
  rw [parseFast_list]; exact print_roundtrip h

theorem parseFast_lone_high_surrogate_rejected : parseFast ⟨#[0x22, 0x5C, 0x75, 0x44, 0x38, 0x30, 0x30, 0x22]⟩ = .error .syntax := by
  rw [parseFast_eq_parse]; exact lone_high_surrogate_rejected

theorem parseFast_lone_low_surrogate_rejected : parseFast ⟨#[0x22, 0x5C, 0x75, 0x44, 0x43, 0x30, 0x30, 0x22]⟩ = .error .syntax := by
  rw [parseFast_eq_parse]; exact lone_low_surrogate_rejected

theorem parseFast_overlong_utf8_rejected : parseFast ⟨#[0x22, 0xC0, 0x80, 0x22]⟩ = .error .syntax := by
  rw [parseFast_eq_parse]; exact overlong_utf8_rejected

theorem parseFast_utf8_surrogate_rejected : parseFast ⟨#[0x22, 0xED, 0xA0, 0x80, 0x22]⟩ = .error .syntax := by
  rw [parseFast_eq_parse]; exact utf8_surrogate_rejected

theorem parseFast_surrogate_pair_is_one_scalar :
    parseFast ⟨#[0x22, 0x5C, 0x75, 0x44, 0x38, 0x33, 0x44, 0x5C, 0x75, 0x44, 0x45, 0x30, 0x30, 0x22]⟩ = .ok (.str (String.singleton (Char.ofNat 0x1F600))) := by
  rw [parseFast_eq_parse]; exact surrogate_pair_is_one_scalar

theorem parseFast_number_is_a_lexeme :
    parseFast ⟨#[0x31, 0x2E, 0x35, 0x30, 0x45, 0x2B, 0x32]⟩ = .ok (.num ⟨false, .nz 0 [], some (5, [0]), some (false, 2, [])⟩) := by
  rw [parseFast_eq_parse]; exact number_is_a_lexeme

theorem parseFast_leading_zero_rejected : parseFast ⟨#[0x30, 0x31]⟩ = .error .syntax := by
  rw [parseFast_eq_parse]; exact leading_zero_rejected

theorem parseFast_duplicate_keys_kept_in_order :
    parseFast ⟨#[0x7B, 0x22, 0x61, 0x22, 0x3A, 0x31, 0x2C, 0x22, 0x61, 0x22, 0x3A, 0x32, 0x7D]⟩ =
      .ok (.obj [("a", .num ⟨false, .nz 0 [], none, none⟩), ("a", .num ⟨false, .nz 1 [], none, none⟩)]) := by
  rw [parseFast_eq_parse]; exact duplicate_keys_kept_in_order

theorem parseFast_depth_at_limit_accepted :
    (parseFast ⟨(List.replicate maxDepth (0x5B : UInt8) ++ List.replicate maxDepth 0x5D).toArray⟩).isOk = true := by
  rw [parseFast_list]; exact depth_at_limit_accepted

theorem parseFast_depth_past_limit_is_error_code :
    parseFast ⟨(List.replicate (maxDepth + 1) (0x5B : UInt8) ++ List.replicate (maxDepth + 1) 0x5D).toArray⟩ = .error .depth := by
  rw [parseFast_list]; exact depth_past_limit_is_error_code

theorem parseFast_too_deep {a : ByteArray} {v : Value} (h : Json (L a) v) (hd : maxDepth < v.depth) : ∃ e, parseFast a = .error e := by
  rw [parseFast_eq_parse]; exact parse_too_deep h hd

theorem parseFast_depth_100000_is_error_code :
    parseFast ⟨(List.replicate 100000 (0x5B : UInt8) ++ List.replicate 100000 0x5D).toArray⟩ = .error .depth := by
  rw [parseFast_list]; exact depth_100000_is_error_code

theorem parseFast_depth_error_comes_first : parseFast ⟨(List.replicate 600 (0x5B : UInt8)).toArray⟩ = .error .depth := by
  rw [parseFast_list]; exact depth_error_comes_first

end LeanJson
