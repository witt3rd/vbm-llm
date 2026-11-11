import LeanJsonProofs.FastNum
import LeanJsonProofs.FastStr
import LeanJsonProofs.Fast
/-! # The fused loop against `run`, step by step (F4 helpers, F5)

`runT` (`LeanJson/Tape.lean`) and `run` (`LeanJson/Parse.lean`) are two loops over the same text with the same branches. The simulation runs them in lock step:
the fused state is `tb` (the tape and text so far) and `fst` (header positions and counts of the open containers), `run`'s is the value `v` and the `Stack` of what the open containers have read.
`openTape st` is the tape `st` stands for: the open containers' headers (with placeholders) and the elements finished so far, in order, and for an object the key waiting for its value.
`FRel st fst` says the fused containers' positions and counts are those of `st`. -/
set_option linter.unusedSimpArgs false
namespace LeanJson

/-- The empty buffers the fused parser starts from. -/
def s0 : TapeBuf := ⟨.empty, .empty⟩

/-- The tape of the open containers: outermost first; a container's header has placeholders; an object's waiting key is the last node. -/
def openTape : Stack → TapeBuf → TapeBuf
  | .nil, s => s
  | .arr acc rest, s => encList acc.reverse ((openTape rest s).node kindArr 0 0)
  | .obj acc k rest, s => (encMembers acc.reverse ((openTape rest s).node kindObj 0 0)).leaf kindStr k.toUTF8

/-- The fused containers' header positions and counts are those of `run`'s stack. -/
def FRel : Stack → FStack → Prop
  | .nil, .nil => True
  | .arr acc rest, .arr at_ n fr => at_ = (openTape rest s0).words ∧ n = acc.length ∧ FRel rest fr
  | .obj acc _ rest, .obj at_ n fr => at_ = (openTape rest s0).words ∧ n = acc.length ∧ FRel rest fr
  | _, _ => False

/-- What the fused parser returns for what `run` returns. -/
def finT : Except Error Value → ByteArray
  | .ok v => tapeOk (encValue v s0)
  | .error e => tapeErr e

theorem encList_append (xs ys : List Value) (s : TapeBuf) : encList (xs ++ ys) s = encList ys (encList xs s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, encList, ih]

theorem encMembers_append (xs ys : List (String × Value)) (s : TapeBuf) : encMembers (xs ++ ys) s = encMembers ys (encMembers xs s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => obtain ⟨k, v⟩ := x; simp only [List.cons_append, encMembers, ih]

theorem encList_snoc (acc : List Value) (v : Value) (s : TapeBuf) : encList (v :: acc).reverse s = encValue v (encList acc.reverse s) := by
  simp [encList_append, encList]

theorem encMembers_snoc (acc : List (String × Value)) (k : String) (v : Value) (s : TapeBuf) :
    encMembers ((k, v) :: acc).reverse s = encValue v ((encMembers acc.reverse s).leaf kindStr k.toUTF8) := by
  simp [encMembers_append, encMembers]

theorem encValue_wf {s : TapeBuf} (hs : s.WF) (v : Value) : (encValue v s).WF :=
  wf_ext hs (encValue_layout v s hs).1 (by rw [tapeV_length]; omega)

theorem encList_wf {s : TapeBuf} (hs : s.WF) (xs : List Value) : (encList xs s).WF :=
  wf_ext hs (encList_layout xs s hs).1 (by rw [tapeL_length]; omega)

theorem encMembers_wf {s : TapeBuf} (hs : s.WF) (ms : List (String × Value)) : (encMembers ms s).WF :=
  wf_ext hs (encMembers_layout ms s hs).1 (by rw [tapeM_length]; omega)

theorem openTape_wf {s : TapeBuf} (hs : s.WF) : ∀ st : Stack, (openTape st s).WF
  | .nil => hs
  | .arr _ rest => encList_wf (node_wf (openTape_wf hs rest) _ _ _) _
  | .obj _ _ rest => leaf_wf (encMembers_wf (node_wf (openTape_wf hs rest) _ _ _) _) _ _

/-- F4: a key and its colon, written, is the leaf of the key `parseKeyA` reads. -/
theorem keyNode_eq (s : TapeBuf) (a : ByteArray) (i : Nat) :
    s.keyNode a i = (parseKeyA a i).map (fun p => (s.leaf kindStr p.1.toUTF8, p.2)) := by
  unfold TapeBuf.keyNode parseKeyA
  rw [strNode_eq]
  rcases parseStrA a i with _ | ⟨k, j⟩
  · rfl
  · simp only [Option.map_some]
    split <;> simp

theorem s0_wf : s0.WF := empty_wf

theorem runT_sim (a : ByteArray) (f : Nat) :
    (∀ i v st fst tb d, FRel st fst → tb = openTape st s0 → runT f a i false tb fst d = finT (run f a i false v st d)) ∧
    (∀ i v st fst tb d, FRel st fst → tb = encValue v (openTape st s0) → runT f a i true tb fst d = finT (run f a i true v st d)) := by
  induction f with
  | zero => constructor <;> intros <;> rfl
  | succ f ih =>
    obtain ⟨ihV, ihR⟩ := ih
    constructor
    · intro i v st fst tb d hF hT
      subst hT
      have hW := openTape_wf s0_wf st
      rw [run.eq_2, runT.eq_2]
      rcases hb : byteAt a i with _ | b
      · simp [finT]
      · simp only []
        by_cases h91 : b = 0x5B
        · subst h91
          simp only [beq_self_eq_true, ite_true]
          by_cases hd : d = 0
          · subst hd; simp [finT]
          · have hd0 : (d == 0) = false := by simpa using hd
            simp only [hd0, Bool.false_eq_true, ite_false]
            by_cases hi : byteIs a (skipWsA a (i + 1)) 0x5D = true
            · simp only [hi, ite_true]
              exact ihR _ _ _ _ _ _ hF (by rw [node_empty_arr _ hW])
            · simp only [hi, ite_false]
              exact ihV _ _ _ _ _ _ ⟨rfl, rfl, hF⟩ rfl
        · by_cases h7b : b = 0x7B
          · subst h7b
            simp only [show ((0x7B : UInt8) == 0x5B) = false by decide, Bool.false_eq_true, ite_false, beq_self_eq_true, ite_true]
            by_cases hd : d = 0
            · subst hd; simp [finT]
            · have hd0 : (d == 0) = false := by simpa using hd
              simp only [hd0, Bool.false_eq_true, ite_false]
              by_cases hi : byteIs a (skipWsA a (i + 1)) 0x7D = true
              · simp only [hi, ite_true]
                exact ihR _ _ _ _ _ _ hF (by rw [node_empty_obj _ hW])
              · simp only [hi, ite_false]
                rw [keyNode_eq]
                rcases hk : parseKeyA a (skipWsA a (i + 1)) with _ | ⟨k, j⟩
                · simp [finT]
                · simp only [Option.map_some]
                  exact ihV _ _ _ _ _ _ ⟨rfl, rfl, hF⟩ rfl
          · have e1 : (b == 0x5B) = false := by simpa using h91
            have e2 : (b == 0x7B) = false := by simpa using h7b
            simp only [e1, e2, Bool.false_eq_true, ite_false]
            by_cases h22 : b = 0x22
            · have e : (b == 0x22) = true := by simp [h22]
              simp only [e, ite_true]
              rw [strNode_eq]
              rcases parseStrA a i with _ | ⟨str, j⟩
              · simp [finT]
              · simp only [Option.map_some]
                exact ihR _ _ _ _ _ _ hF rfl
            · have e : (b == 0x22) = false := by simpa using h22
              simp only [e, Bool.false_eq_true, ite_false]
              by_cases h6e : b = 0x6E
              · have e : (b == 0x6E) = true := by simp [h6e]
                simp only [e, ite_true]
                rcases litA a (i + 1) [0x75, 0x6C, 0x6C] with _ | j
                · simp [finT]
                · exact ihR _ _ _ _ _ _ hF rfl
              · have e : (b == 0x6E) = false := by simpa using h6e
                simp only [e, Bool.false_eq_true, ite_false]
                by_cases h74 : b = 0x74
                · have e : (b == 0x74) = true := by simp [h74]
                  simp only [e, ite_true]
                  rcases litA a (i + 1) [0x72, 0x75, 0x65] with _ | j
                  · simp [finT]
                  · exact ihR _ _ _ _ _ _ hF rfl
                · have e : (b == 0x74) = false := by simpa using h74
                  simp only [e, Bool.false_eq_true, ite_false]
                  by_cases h66 : b = 0x66
                  · have e : (b == 0x66) = true := by simp [h66]
                    simp only [e, ite_true]
                    rcases litA a (i + 1) [0x61, 0x6C, 0x73, 0x65] with _ | j
                    · simp [finT]
                    · exact ihR _ _ _ _ _ _ hF rfl
                  · have e : (b == 0x66) = false := by simpa using h66
                    simp only [e, Bool.false_eq_true, ite_false]
                    rw [scanNum_eq]
                    rcases hp : parseNumA a i with _ | ⟨n, j⟩
                    · simp [finT]
                    · simp only [Option.map_some]
                      rw [numLex_eq hp]
                      exact ihR _ _ _ _ _ _ hF rfl
    · intro i v st fst tb d hF hT
      cases st with
      | nil =>
        cases fst with
        | nil =>
          rw [run.eq_3, runT.eq_3]
          by_cases h : a.size ≤ skipWsA a i
          · simp [h, finT, hT, openTape]
          · simp [h, finT]
        | arr _ _ _ => exact absurd hF id
        | obj _ _ _ => exact absurd hF id
      | arr acc rest =>
        cases fst with
        | nil => exact absurd hF id
        | obj _ _ _ => exact absurd hF id
        | arr at_ n fr =>
          obtain ⟨hat, hn, hF'⟩ := hF
          have hW := openTape_wf s0_wf rest
          rw [run.eq_4, runT.eq_4]
          by_cases hc : byteIs a (skipWsA a i) 0x2C = true
          · simp only [hc, ite_true]
            refine ihV _ _ _ _ _ _ ⟨hat, by simp [hn], hF'⟩ ?_
            show tb = encList (v :: acc).reverse _
            rw [encList_snoc]; exact hT
          · simp only [hc, ite_false]
            by_cases hq : byteIs a (skipWsA a i) 0x5D = true
            · simp only [hq, ite_true]
              refine ihR _ _ _ _ _ _ hF' ?_
              rw [← closeNode_arr _ _ hW, hat, hT]
              simp only [openTape, encList_snoc, List.length_reverse, List.length_cons, hn]
            · simp only [hq, ite_false]; simp [finT]
      | obj acc k rest =>
        cases fst with
        | nil => exact absurd hF id
        | arr _ _ _ => exact absurd hF id
        | obj at_ n fr =>
          obtain ⟨hat, hn, hF'⟩ := hF
          have hW := openTape_wf s0_wf rest
          rw [run.eq_5, runT.eq_5]
          by_cases hc : byteIs a (skipWsA a i) 0x2C = true
          · simp only [hc, ite_true]
            rw [keyNode_eq]
            rcases hk : parseKeyA a (skipWsA a (skipWsA a i + 1)) with _ | ⟨k', j⟩
            · simp [finT]
            · simp only [Option.map_some]
              refine ihV _ _ _ _ _ _ ⟨hat, by simp [hn], hF'⟩ ?_
              show _ = (encMembers ((k, v) :: acc).reverse _).leaf kindStr k'.toUTF8
              rw [encMembers_snoc, hT]; rfl
          · simp only [hc, ite_false]
            by_cases hq : byteIs a (skipWsA a i) 0x7D = true
            · simp only [hq, ite_true]
              refine ihR _ _ _ _ _ _ hF' ?_
              rw [← closeNode_obj _ _ hW, hat, hT]
              simp only [openTape, encMembers_snoc, List.length_reverse, List.length_cons, hn]
            · simp only [hq, ite_false]; simp [finT]

theorem parseTape_eq_finT (a : ByteArray) : parseTape a = finT (parseFast a) := by
  unfold parseTape
  cases parseFast a <;> rfl

/-- F6: the fused parser returns exactly the bytes of `parseTape`: the tape of the value `parseFast` builds, or the error words. -/
theorem parseTapeFast_eq (a : ByteArray) : parseTapeFast a = parseTape a := by
  rw [parseTape_eq_finT, parseFast]
  exact (runT_sim a (a.size + 2)).1 _ .null .nil .nil s0 maxDepth trivial rfl

/-- What the exported tape is, in terms of the reference: on an accepted text the layout of the reference's value (`tapeV`, `textV`, `encValue_layout`), on a rejected one the error words. -/
theorem parseTapeFast_ok {a : ByteArray} {v : Value} (h : parse (L a) = .ok v) : parseTapeFast a = tapeOk (encValue v s0) := by
  rw [parseTapeFast_eq, parseTape_eq_finT, parseFast_eq_parse, h]; rfl

theorem parseTapeFast_error {a : ByteArray} {e : Error} (h : parse (L a) = .error e) : parseTapeFast a = tapeErr e := by
  rw [parseTapeFast_eq, parseTape_eq_finT, parseFast_eq_parse, h]; rfl

end LeanJson
