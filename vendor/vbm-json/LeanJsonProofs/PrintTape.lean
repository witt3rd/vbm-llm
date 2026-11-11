import LeanJsonProofs.PrintBytes
import LeanJsonProofs.FastLeaf
import LeanJsonProofs.Str
/-! # The tape printer against the reference printer

`printTape_encode`: for a value within `maxDepth` whose tape and text fit the format (the words and the text offsets below 2^50: the head word holds a length below 2^56 and an offset is a word), the tape that
`encValue` writes prints to `print v`. So the export `vbm_json_print_tape` of a tape the parser wrote is the reference printer's bytes. (Not claimed here: that a forged tape prints to a document the parser accepts; the
checks that make that true are tested, `tests/abi_test.c`.) -/
set_option linter.unusedSimpArgs false
namespace LeanJson

/-! ## Reading words and bytes -/

theorem size_L (a : ByteArray) : a.size = (L a).length := size_list a

theorem getElem_L (a : ByteArray) (n : Nat) (h : n < a.size) : a[n] = (L a)[n]'(by rw [← size_L]; exact h) := by
  unfold L
  rw [ByteArray.getElem_eq_getElem_data, Array.getElem_toList]

/-- A list laid out as `P ++ M ++ Q` has `M`'s `j`th element at `P.length + j`. -/
theorem getElem_mid {P M Q : List UInt8} {j : Nat} (hj : j < M.length) (n : Nat) (hn : n = P.length + j) (h : n < (P ++ M ++ Q).length) :
    (P ++ M ++ Q)[n] = M[j] := by
  subst hn
  have h2 : (P ++ M ++ Q)[P.length + j]? = some M[j] := by
    rw [List.append_assoc, List.getElem?_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left]
    rw [List.getElem?_append_left hj, List.getElem?_eq_getElem hj]
  rw [List.getElem?_eq_getElem h] at h2
  exact Option.some.inj h2

theorem ldw_eq (a : ByteArray) (i : Nat) (P Q : List UInt8) (u : UInt64) (h : L a = P ++ wordBytes u ++ Q) (hP : P.length = 8 * i) : ldw a i = u := by
  have hs : a.size = P.length + 8 + Q.length := by rw [size_L, h]; simp [wordBytes_length]; omega
  unfold ldw
  have hb : 8 * i + 8 ≤ a.size := by omega
  simp only [hb, ↓reduceDIte]
  have g : ∀ j (hj : j < 8) (hn : 8 * i + j < a.size), a[8 * i + j] = (wordBytes u)[j]'(by rw [wordBytes_length]; exact hj) := by
    intro j hj hn
    rw [getElem_L]
    have := @getElem_mid P (wordBytes u) Q j (by rw [wordBytes_length]; exact hj) (8 * i + j) (by omega) (by rw [← h, ← size_L]; exact hn)
    simpa [h] using this
  have e0 := g 0 (by omega) (by omega)
  have e1 := g 1 (by omega) (by omega)
  have e2 := g 2 (by omega) (by omega)
  have e3 := g 3 (by omega) (by omega)
  have e4 := g 4 (by omega) (by omega)
  have e5 := g 5 (by omega) (by omega)
  have e6 := g 6 (by omega) (by omega)
  have e7 := g 7 (by omega) (by omega)
  simp only [wordBytes, Nat.add_zero] at e0 e1 e2 e3 e4 e5 e6 e7
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at e0 e1 e2 e3 e4 e5 e6 e7
  rw [e0, e1, e2, e3, e4, e5, e6, e7]
  exact wordsum u

/-! ## The header words of a value's node -/

def vKind : Value → Nat
  | .null => 0 | .bool false => 1 | .bool true => 2 | .num _ => 3 | .str _ => 4 | .arr _ => 5 | .obj _ => 6
def vLen : Value → Nat
  | .num n => (printNumber n).length | .str s => s.toUTF8.size | .arr xs => xs.length | .obj ms => ms.length | _ => 0
def vAux (o : Nat) : Value → Nat
  | .num _ => o | .str _ => o | .arr xs => wordsV (.arr xs) | .obj ms => wordsV (.obj ms) | _ => 0
def vRest (o : Nat) : Value → List UInt8
  | .arr xs => tapeL o xs | .obj ms => tapeM o ms | _ => []

def headW (v : Value) : UInt64 := UInt64.ofNat (vKind v + vLen v * 256)
def auxW (o : Nat) (v : Value) : UInt64 := UInt64.ofNat (vAux o v)

theorem tapeV_eq (o : Nat) (v : Value) : tapeV o v = wordBytes (headW v) ++ wordBytes (auxW o v) ++ vRest o v := by
  cases v with
  | bool b => cases b <;> simp [tapeV, hdrBytes, vRest, headW, auxW, vKind, vLen, vAux, kindFalse, kindTrue]
  | _ => simp [tapeV, hdrBytes, vRest, headW, auxW, vKind, vLen, vAux, kindNull, kindNum, kindStr, kindArr, kindObj, wordsV]

/-- Both header words of the node at word `i` are read back. -/
theorem read_node {w : ByteArray} {i o : Nat} {v : Value} {P Q : List UInt8} (hw : L w = P ++ tapeV o v ++ Q) (hP : P.length = 8 * i) :
    16 + 8 * i ≤ w.size ∧ ldw w i = headW v ∧ ldw w (i + 1) = auxW o v := by
  rw [tapeV_eq] at hw
  have hs : w.size = P.length + 16 + (vRest o v).length + Q.length := by rw [size_L, hw]; simp [wordBytes_length]; omega
  refine ⟨by omega, ?_, ?_⟩
  · exact ldw_eq w i P (wordBytes (auxW o v) ++ vRest o v ++ Q) _ (by rw [hw]; simp) hP
  · exact ldw_eq w (i + 1) (P ++ wordBytes (headW v)) (vRest o v ++ Q) _ (by rw [hw]; simp) (by simp [hP, wordBytes_length]; omega)

theorem head_mod (v : Value) (hl : vLen v < 2 ^ 56) : headW v % 256 = UInt64.ofNat (vKind v) ∧ (headW v >>> 8).toNat = vLen v := by
  have hk : vKind v < 256 := by cases v with | bool b => cases b <;> simp [vKind] | _ => simp [vKind]
  unfold headW
  constructor
  · apply UInt64.toNat_inj.mp
    simp [UInt64.toNat_mod, UInt64.toNat_ofNat]
    omega
  · simp [UInt64.toNat_shiftRight, UInt64.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega

/-! ## Escaping a range of the text -/

theorem data_extract' (x : ByteArray) (i len : Nat) : (x.extract i (i + len)).data = x.data.extract i (i + len) := by
  have e : ByteArray.empty.data = #[] := rfl
  show (x.copySlice i ByteArray.empty 0 (i + len - i)).data = _
  unfold ByteArray.copySlice
  simp only [e, Array.extract_empty, Array.empty_append, Array.size_empty, Nat.add_sub_cancel_left]
  exact Array.append_empty

theorem extract_eq (x : ByteArray) (i len : Nat) : x.extract i (i + len) = ba (((L x).drop i).take len) := by
  apply ByteArray.ext
  rw [data_extract']
  apply Array.toList_inj.mp
  rw [Array.toList_extract, List.extract_eq_take_drop]
  simp
  rfl

/-- A byte the printer escapes (`plainEnd` stops at it). -/
def isEsc (c : UInt8) : Bool := c < 0x20 || c == 0x22 || c == 0x5C

theorem escByte_plain {c : UInt8} (h : isEsc c = false) : escByte c = [c] := by
  unfold isEsc at h
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne, ne_eq, UInt8.not_lt] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have h1' : 0x20 ≤ c.toNat := by simpa [UInt8.le_iff_toNat_le] using h1
  have h2' : c.toNat ≠ 0x22 := fun e => h2 (UInt8.toNat_inj.mp (by simpa using e))
  have h3' : c.toNat ≠ 0x5C := fun e => h3 (UInt8.toNat_inj.mp (by simpa using e))
  unfold escByte
  simp [h2', h3', h1']

theorem escByte_isEsc {c : UInt8} (h : isEsc c = false) : isEsc c = false := h

theorem plainEnd_spec (x : ByteArray) (e : Nat) (he : e ≤ x.size) : ∀ i,
    i ≤ plainEnd x i e ∧ (i ≤ e → plainEnd x i e ≤ e) ∧ (∀ k (hk : k < x.size), i ≤ k → k < plainEnd x i e → isEsc x[k] = false) ∧
    (∀ (h : plainEnd x i e < x.size), plainEnd x i e < e → isEsc x[plainEnd x i e] = true) := by
  have H : ∀ n i, e - i = n → (i ≤ plainEnd x i e ∧ (i ≤ e → plainEnd x i e ≤ e) ∧ (∀ k (hk : k < x.size), i ≤ k → k < plainEnd x i e → isEsc x[k] = false) ∧
      (∀ (h : plainEnd x i e < x.size), plainEnd x i e < e → isEsc x[plainEnd x i e] = true)) := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro i hn
      unfold plainEnd
      by_cases h1 : i < e
      · have h2 : i < x.size := by omega
        simp only [h1, h2, dite_true]
        by_cases h3 : isEsc x[i] = true
        · have h3'' : (x[i] < 0x20 || x[i] == 0x22 || x[i] == 0x5C) = true := h3
          simp only [h3'', ite_true]
          refine ⟨Nat.le_refl _, fun _ => by omega, fun k hk hik hkj => by omega, fun _ _ => h3⟩
        · have h3' : isEsc x[i] = false := by simpa using h3
          have h3'' : (x[i] < 0x20 || x[i] == 0x22 || x[i] == 0x5C) = false := h3'
          simp only [h3'', Bool.false_eq_true, ite_false]
          obtain ⟨a1, a2, a3, a4⟩ := ih (e - (i + 1)) (by omega) (i + 1) rfl
          refine ⟨by omega, fun _ => a2 (by omega), fun k hk hik hkj => ?_, a4⟩
          by_cases hki : k = i
          · subst hki; exact h3'
          · exact a3 k hk (by omega) hkj
      · simp only [h1, dite_false]
        refine ⟨Nat.le_refl _, fun h => h, fun k hk hik hkj => by omega, fun _ h => h.elim⟩
  exact fun i => H _ i rfl

theorem copy_append' (src dest : ByteArray) (o len : Nat) : src.copySlice o dest dest.size len false = dest ++ src.extract o (o + len) := by
  rw [ByteArray.copySlice_eq_append]
  have a1 : dest.extract 0 dest.size = dest := ByteArray.extract_zero_size
  have a3 : dest.extract (dest.size + min len (src.data.size - o)) dest.data.size = ByteArray.empty := by
    apply ByteArray.extract_eq_empty_iff.mpr; show min dest.data.size dest.size ≤ _; omega
  rw [a1, a3, ByteArray.append_empty]

theorem append_ba (b : ByteArray) (l m : List UInt8) : b ++ ba (l ++ m) = (b ++ ba l) ++ ba m := (app_ba b l m).symm

theorem flatMap_esc_plain {l : List UInt8} (h : ∀ c ∈ l, isEsc c = false) : l.flatMap escByte = l := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    simp only [List.flatMap_cons, escByte_plain (h c (by simp))]
    rw [ih (fun y hy => h y (by simp [hy]))]; rfl

/-- The slice of the text `x[i:j)`, when every byte of it is plain, is its own escape. -/
theorem flatMap_plain (x : ByteArray) (i j : Nat) (hj : j ≤ x.size) (h : ∀ k (hk : k < x.size), i ≤ k → k < j → isEsc x[k] = false) :
    (((L x).drop i).take (j - i)).flatMap escByte = ((L x).drop i).take (j - i) := by
  apply flatMap_esc_plain
  intro c hc
  obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp hc
  simp only [List.length_take, List.length_drop, ← size_L] at hm
  have hk : i + m < x.size := by omega
  have := h (i + m) hk (by omega) (by omega)
  simpa [List.getElem_take, List.getElem_drop, getElem_L x (i + m) hk] using this

theorem escLoopR_eq (x : ByteArray) (e : Nat) (he : e ≤ x.size) : ∀ n i b, e - i = n →
    escLoopR x i e b = b ++ ba ((((L x).drop i).take (e - i)).flatMap escByte) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro i b hn
    unfold escLoopR
    by_cases h1 : i < e
    · simp only [h1, dite_true]
      obtain ⟨a1, a2, a3, a4⟩ := plainEnd_spec x e he i
      have a2' := a2 (by omega)
      obtain ⟨j, hjdef⟩ : ∃ j, plainEnd x i e = j := ⟨_, rfl⟩
      simp only [hjdef] at a1 a2' a3 a4 ⊢
      have hrun : (((L x).drop i).take (j - i)).flatMap escByte = ((L x).drop i).take (j - i) := flatMap_plain x i j (by omega) a3
      have hb1 : (if i < j then x.copySlice i b b.size (j - i) false else b) = b ++ ba (((L x).drop i).take (j - i)) := by
        by_cases hij : i < j
        · simp only [hij, ite_true]
          rw [copy_append']
          have : i + (j - i) = j := by omega
          rw [this, ← extract_eq x i (j - i), this]
        · have : j = i := by omega
          subst this
          simp [ba_nil]
      have hsplit : ((L x).drop i).take (e - i) = ((L x).drop i).take (j - i) ++ ((L x).drop j).take (e - j) := by
        have : e - i = (j - i) + (e - j) := by omega
        rw [this, List.take_add, List.drop_drop]
        congr 3 <;> omega
      by_cases h2 : j < e
      · have hjs : j < x.size := by omega
        have hc : i ≤ j ∧ j < e ∧ j < x.size := ⟨a1, h2, hjs⟩
        simp only [hc, and_self, dite_true]
        rw [ih (e - (j + 1)) (by omega) (j + 1) _ rfl, pushEsc_eq, hb1]
        have hcons : ((L x).drop j).take (e - j) = x[j] :: ((L x).drop (j + 1)).take (e - (j + 1)) := by
          have : e - j = (e - (j + 1)) + 1 := by omega
          rw [this, List.drop_eq_getElem_cons (by rw [← size_L]; exact hjs), List.take_succ_cons, ← getElem_L x j hjs]
        rw [hsplit, hcons, List.flatMap_append, hrun, List.flatMap_cons, app_ba, app_ba]
      · have hje : j = e := by omega
        have hc : ¬ (i ≤ j ∧ j < e ∧ j < x.size) := fun h => h2 h.2.1
        simp only [hc, dite_false]
        rw [hb1]
        have : e - i = j - i := by omega
        rw [this, hrun]
    · simp only [h1, dite_false]
      have : e - i = 0 := by omega
      simp [this, ba_nil]

/-! ## UTF-8 of a string passes the check -/

theorem byteAt_lt {a : ByteArray} {k : Nat} {c : UInt8} (h : byteAt a k = some c) : k < a.size := by
  unfold byteAt at h
  split at h
  · assumption
  · simp at h

theorem decodeUtf8A_le {a : ByteArray} {i n j : Nat} (h : decodeUtf8A a i = some (n, j)) : j ≤ a.size := by
  unfold decodeUtf8A at h
  rcases hb0 : byteAt a i with _ | x0
  · rw [hb0] at h; simp at h
  · rw [hb0] at h
    have l0 := byteAt_lt hb0
    simp only at h
    split at h
    · simp at h; omega
    · split at h
      · rcases hb1 : byteAt a (i + 1) with _ | b1
        · rw [hb1] at h; simp at h
        · rw [hb1] at h
          have l1 := byteAt_lt hb1
          simp only at h
          split at h
          · simp at h; omega
          · simp at h
      · split at h
        · rcases hb1 : byteAt a (i + 1) with _ | b1
          · rw [hb1] at h; simp at h
          · rcases hb2 : byteAt a (i + 2) with _ | b2
            · rw [hb1, hb2] at h; simp at h
            · rw [hb1, hb2] at h
              have l1 := byteAt_lt hb1
              have l2 := byteAt_lt hb2
              simp only at h
              split at h
              · simp at h; omega
              · simp at h
        · split at h
          · rcases hb1 : byteAt a (i + 1) with _ | b1
            · rw [hb1] at h; simp at h
            · rcases hb2 : byteAt a (i + 2) with _ | b2
              · rw [hb1, hb2] at h; simp at h
              · rcases hb3 : byteAt a (i + 3) with _ | b3
                · rw [hb1, hb2, hb3] at h; simp at h
                · rw [hb1, hb2, hb3] at h
                  have l1 := byteAt_lt hb1
                  have l2 := byteAt_lt hb2
                  have l3 := byteAt_lt hb3
                  simp only at h
                  split at h
                  · simp at h; omega
                  · simp at h
          · simp at h

theorem decode_enc (x : ByteArray) (i : Nat) (c : Char) (R : List UInt8) (h : (L x).drop i = String.utf8EncodeChar c ++ R) :
    decodeUtf8A x i = some (c.toNat, i + (String.utf8EncodeChar c).length) := by
  have hU : Utf8 (String.utf8EncodeChar c) c.toNat := by rw [enc_eq]; exact utf8_encode (char_scalar c)
  have h1 := decodeUtf8A_eq x i
  rw [h, utf8_complete hU R] at h1
  have hk : i + (String.utf8EncodeChar c).length ≤ x.size := by
    have := congrArg List.length h
    simp only [List.length_drop, List.length_append, ← size_L] at this
    have hpos : 1 ≤ (String.utf8EncodeChar c).length := by rw [String.length_utf8EncodeChar]; exact Char.utf8Size_pos c
    omega
  have hR : (L x).drop (i + (String.utf8EncodeChar c).length) = R := by
    rw [← List.drop_drop, h, List.drop_left]
  cases hd : decodeUtf8A x i with
  | none => rw [hd] at h1; simp [mapDrop] at h1
  | some p =>
    obtain ⟨n', j'⟩ := p
    rw [hd] at h1
    simp only [mapDrop, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨hn, hj⟩ := h1
    have hle := decodeUtf8A_le hd
    have hl1 := congrArg List.length hj
    have hl2 := congrArg List.length hR
    simp only [List.length_drop, ← size_L] at hl1 hl2
    have hjk : j' = i + (String.utf8EncodeChar c).length := by omega
    rw [← hn, hjk]

theorem slice_tail {x : ByteArray} {i e : Nat} {E T : List UInt8} (hsl : ((L x).drop i).take (e - i) = E ++ T) :
    ((L x).drop (i + E.length)).take (e - (i + E.length)) = T := by
  have h := congrArg (List.drop E.length) hsl
  rw [List.drop_take, List.drop_drop, List.drop_left'] at h
  · rw [show e - i - E.length = e - (i + E.length) by omega] at h
    exact h
  · rfl

theorem utf8Range_complete (x : ByteArray) (cs : List Char) : ∀ i e, e = i + (cs.flatMap String.utf8EncodeChar).length → e ≤ x.size →
    ((L x).drop i).take (e - i) = cs.flatMap String.utf8EncodeChar → utf8Range x i e = true := by
  induction cs with
  | nil => intro i e he _ _; unfold utf8Range; simp at he; simp [he]
  | cons c cs ih =>
    intro i e he hes hsl
    simp only [List.flatMap_cons, List.length_append] at he hsl
    have hk : 1 ≤ (String.utf8EncodeChar c).length := by rw [String.length_utf8EncodeChar]; exact Char.utf8Size_pos c
    have hdrop : (L x).drop i = String.utf8EncodeChar c ++ ((cs.flatMap String.utf8EncodeChar) ++ (L x).drop e) := by
      have h0 := List.take_append_drop (e - i) ((L x).drop i)
      rw [hsl, List.drop_drop, show i + (e - i) = e by omega] at h0
      rw [← h0]; simp
    obtain ⟨c0, r, hr⟩ : ∃ c0 r, String.utf8EncodeChar c = c0 :: r := by
      cases hh : String.utf8EncodeChar c with
      | nil => rw [hh] at hk; simp at hk
      | cons c0 r => exact ⟨c0, r, rfl⟩
    have hb : byteAt x i = some c0 := by
      rw [byteAt_eq]
      have : (L x)[i]? = ((L x).drop i)[0]? := by simp [List.getElem?_drop]
      rw [this, hdrop, hr]; simp
    have hi : i < e := by omega
    have hrest := slice_tail (x := x) (i := i) (e := e) hsl
    unfold utf8Range
    simp only [hi, dite_true, hb]
    by_cases ha : c.toNat < 0x80
    · have hen : String.utf8EncodeChar c = [UInt8.ofNat c.toNat] := by rw [enc_eq]; unfold encodeUtf8; simp [ha]
      rw [hen] at hr
      have hc0 : c0 = UInt8.ofNat c.toNat := (List.cons.inj hr.symm).1
      have hlt : c0 < 0x80 := by rw [hc0, UInt8.lt_iff_toNat_lt, toNat_byte (by omega)]; simpa using ha
      simp only [hlt, ite_true]
      rw [hen] at hrest he
      simp only [List.length_singleton] at hrest he
      exact ih (i + 1) e (by omega) hes (by simpa using hrest)
    · have hge : 0x80 ≤ c0.toNat := by
        have := encode_ge (n := c.toNat) (by omega) (by have := char_scalar c; unfold Scalar at this; omega) c0 (by rw [← enc_eq, hr]; simp)
        exact this
      have hnl : ¬ c0 < 0x80 := by rw [UInt8.lt_iff_toNat_lt]; simpa using hge
      simp only [hnl, ite_false]
      have hd := decode_enc x i c (cs.flatMap String.utf8EncodeChar ++ (L x).drop e) hdrop
      rw [hd]
      simp only
      have hc : i < i + (String.utf8EncodeChar c).length ∧ i + (String.utf8EncodeChar c).length ≤ e := ⟨by omega, by omega⟩
      simp only [hc, and_self, ite_true]
      exact ih (i + (String.utf8EncodeChar c).length) e (by omega) hes hrest

/-! ## The lexeme of a number passes the check -/

/-- The bytes of `T` are at `x[i..]`. -/
def At (x : ByteArray) (i : Nat) (T : List UInt8) : Prop := ∀ k (hk : k < T.length), byteAt x (i + k) = some T[k]

theorem At_nil (x : ByteArray) (i : Nat) : At x i [] := fun k hk => by simp at hk

theorem At_cons {x : ByteArray} {i : Nat} {c : UInt8} {T : List UInt8} : At x i (c :: T) ↔ byteAt x i = some c ∧ At x (i + 1) T := by
  constructor
  · intro h
    refine ⟨by have h0 := h 0 (by simp); rw [Nat.add_zero] at h0; exact h0, fun k hk => ?_⟩
    have := h (k + 1) (by simp; omega)
    rw [show i + (k + 1) = i + 1 + k by omega] at this
    simpa using this
  · rintro ⟨h0, h1⟩ k hk
    cases k with
    | zero => simpa using h0
    | succ k =>
      have := h1 k (by simp at hk; omega)
      rw [show i + (k + 1) = i + 1 + k by omega]
      simpa using this

theorem At_append {x : ByteArray} {i : Nat} {A B : List UInt8} : At x i (A ++ B) ↔ At x i A ∧ At x (i + A.length) B := by
  induction A generalizing i with
  | nil => simp [At_nil]
  | cons c A ih =>
    rw [List.cons_append, At_cons, At_cons, ih]
    simp only [List.length_cons]
    rw [show i + (A.length + 1) = i + 1 + A.length by omega]
    exact ⟨fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩, fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩⟩

theorem At_of_slice {x : ByteArray} {i e : Nat} {T : List UInt8} (hsl : ((L x).drop i).take (e - i) = T) : At x i T := by
  intro k hk
  subst hsl
  rw [byteAt_eq]
  have hk2 : i + k < (L x).length := by simp at hk; omega
  rw [List.getElem?_eq_getElem hk2]
  simp [List.getElem_take, List.getElem_drop]

theorem digit_u8 (d : Digit) : (0x30 ≤ digitByte d ∧ digitByte d ≤ 0x39) := by
  have h := d.isLt
  have hb : (digitByte d).toNat = 0x30 + d.val := by unfold digitByte; rw [toNat_byte (by omega)]
  constructor <;> (rw [UInt8.le_iff_toNat_le, hb]; simp <;> omega)

theorem digit_nat (d : Digit) : 0x30 ≤ (digitByte d).toNat ∧ (digitByte d).toNat ≤ 0x39 := by
  have h := d.isLt
  have hb : (digitByte d).toNat = 0x30 + d.val := by unfold digitByte; rw [toNat_byte (by omega)]
  omega

theorem scanDig_run (x : ByteArray) (e : Nat) : ∀ (ds : List Digit) (i : Nat), At x i (ds.map digitByte) → i + ds.length ≤ e →
    (i + ds.length = e ∨ byteAt x (i + ds.length) = some 0x2E ∨ byteAt x (i + ds.length) = some 0x65) → scanDig x i e = i + ds.length := by
  intro ds
  induction ds with
  | nil =>
    intro i _ _ hstop
    unfold scanDig
    simp only [List.length_nil, Nat.add_zero] at hstop ⊢
    rcases hstop with h | h | h
    · simp [h]
    · by_cases hi : i < e
      · simp [hi, h]
      · simp [hi]
    · by_cases hi : i < e
      · simp [hi, h]
      · simp [hi]
  | cons d ds ih =>
    intro i hat hle hstop
    rw [List.map_cons, At_cons] at hat
    obtain ⟨h0, h1⟩ := hat
    simp only [List.length_cons] at hle hstop ⊢
    have hi : i < e := by omega
    unfold scanDig
    simp only [hi, dite_true, h0]
    have hd := digit_u8 d
    simp only [hd.1, hd.2, and_self, ite_true]
    rw [ih (i + 1) h1 (by omega) (by rw [show i + 1 + ds.length = i + (ds.length + 1) by omega]; exact hstop)]
    omega

theorem stop_of_R {x : ByteArray} {j e : Nat} {R : List UInt8} (hR : R = [] ∨ R.head? = some 0x2E ∨ R.head? = some 0x65)
    (hat : At x j R) (he : j + R.length = e) : j = e ∨ byteAt x j = some 0x2E ∨ byteAt x j = some 0x65 := by
  rcases hR with h | h | h
  · subst h; left; simpa using he
  · right; left
    obtain ⟨c, T, rfl⟩ : ∃ c T, R = c :: T := by cases R with | nil => simp at h | cons c T => exact ⟨c, T, rfl⟩
    have := (At_cons.mp hat).1
    have hc : c = 0x2E := by simpa using h
    subst hc; exact this
  · right; right
    obtain ⟨c, T, rfl⟩ : ∃ c T, R = c :: T := by cases R with | nil => simp at h | cons c T => exact ⟨c, T, rfl⟩
    have := (At_cons.mp hat).1
    have hc : c = 0x65 := by simpa using h
    subst hc; exact this

theorem numSign_eq (x : ByteArray) (o e : Nat) (neg : Bool) (R : List UInt8) (hR : ∃ c T, R = c :: T ∧ ¬ c = 0x2D) (hat : At x o (printMinus neg ++ R))
    (he : o + (printMinus neg ++ R).length = e) : numSign x o e = o + (printMinus neg).length := by
  obtain ⟨c, T, rfl, hc⟩ := hR
  unfold numSign
  cases neg with
  | true =>
    have h0 := (At_cons.mp (show At x o (0x2D :: (c :: T)) by simpa [printMinus] using hat)).1
    have hi : o < e := by simp [printMinus] at he; omega
    simp [printMinus, hi, byteIs_eq, h0]
  | false =>
    have h0 := (At_cons.mp (show At x o (c :: T) by simpa [printMinus] using hat)).1
    simp [printMinus, byteIs_eq, h0, hc]

theorem numInt_eq (x : ByteArray) (i e : Nat) (ip : IntPart) (R : List UInt8) (hR : R = [] ∨ R.head? = some 0x2E ∨ R.head? = some 0x65)
    (hat : At x i (printInt ip ++ R)) (he : i + (printInt ip).length + R.length = e) : numInt x i e = i + (printInt ip).length := by
  rw [At_append] at hat
  obtain ⟨hat1, hat2⟩ := hat
  cases ip with
  | zero =>
    have h0 := (At_cons.mp (show At x i [0x30] by simpa [printInt] using hat1)).1
    have hi : i < e := by simp [printInt] at he; omega
    unfold numInt
    simp [printInt, hi, h0]
  | nz l rest =>
    have hrest := At_cons.mp (show At x i (UInt8.ofNat (0x31 + l.val) :: rest.map digitByte) by simpa [printInt] using hat1)
    obtain ⟨h0, h1⟩ := hrest
    have hl := l.isLt
    have hi : i < e := by simp [printInt] at he; omega
    have hc : (UInt8.ofNat (0x31 + l.val)).toNat = 0x31 + l.val := toNat_byte (by omega)
    have hne : ¬ (UInt8.ofNat (0x31 + l.val) == 0x30) = true := by
      intro h
      have := beq_iff_eq.mp h
      have h2 := congrArg UInt8.toNat this
      rw [hc] at h2; simp at h2; omega
    unfold numInt
    simp only [hi, ite_true, h0, hne, Bool.false_eq_true, ite_false, hc]
    have hd : 0x31 ≤ 0x31 + l.val ∧ 0x31 + l.val ≤ 0x39 := by omega
    simp only [hd, and_self, ite_true]
    have hlen : (printInt (.nz l rest)).length = 1 + rest.length := by simp [printInt]; omega
    rw [hlen] at he hat2 ⊢
    have := scanDig_run x e rest (i + 1) (by simpa using h1) (by omega)
      (stop_of_R (j := i + 1 + rest.length) hR (by rw [show i + 1 + rest.length = i + (1 + rest.length) by omega]; exact hat2) (by omega))
    rw [this]; omega

theorem numFrac_eq (x : ByteArray) (i e : Nat) (fr : Option (Digit × List Digit)) (R : List UInt8) (hR : R = [] ∨ R.head? = some 0x65)
    (hat : At x i (printFrac fr ++ R)) (he : i + (printFrac fr).length + R.length = e) : numFrac x i e = i + (printFrac fr).length := by
  rw [At_append] at hat
  obtain ⟨hat1, hat2⟩ := hat
  cases fr with
  | none =>
    unfold numFrac
    simp only [printFrac, List.length_nil, Nat.add_zero] at hat2 he ⊢
    rcases hR with h | h
    · subst h; simp at he; simp [he]
    · obtain ⟨c, T, rfl⟩ : ∃ c T, R = c :: T := by cases R with | nil => simp at h | cons c T => exact ⟨c, T, rfl⟩
      have hc : c = 0x65 := by simpa using h
      subst hc
      have h0 := (At_cons.mp hat2).1
      simp [byteIs_eq, h0]
  | some p =>
    obtain ⟨d, ds⟩ := p
    have hat1' : At x i (0x2E :: digitByte d :: ds.map digitByte) := by simpa [printFrac] using hat1
    obtain ⟨h0, h1⟩ := At_cons.mp hat1'
    obtain ⟨h1a, h1b⟩ := At_cons.mp h1
    have hlen : (printFrac (some (d, ds))).length = 2 + ds.length := by simp [printFrac]; omega
    rw [hlen] at he hat2 ⊢
    have hi : i + 1 < e := by omega
    have hdg := digit_nat d
    unfold numFrac
    have hs := scanDig_run x e ds (i + 2) (by simpa using h1b) (by omega)
      (stop_of_R (j := i + 2 + ds.length) (hR.elim Or.inl (fun h => Or.inr (Or.inr h))) (by rw [show i + 2 + ds.length = i + (2 + ds.length) by omega]; exact hat2) (by omega))
    simp [hi, byteIs_eq, h0, h1a, hdg, hs, show i < e by omega]
    omega

theorem numExp_eq (x : ByteArray) (i e : Nat) (ex : Option (Bool × Digit × List Digit))
    (hat : At x i (printExp ex)) (he : i + (printExp ex).length = e) : numExp x i e = i + (printExp ex).length := by
  cases ex with
  | none =>
    unfold numExp
    simp only [printExp, List.length_nil, Nat.add_zero] at he ⊢
    simp [he]
  | some p =>
    obtain ⟨neg, d, ds⟩ := p
    have hat1 : At x i (0x65 :: (printMinus neg ++ digitByte d :: ds.map digitByte)) := by simpa [printExp] using hat
    obtain ⟨h0, h1⟩ := At_cons.mp hat1
    have hdg := digit_nat d
    unfold numExp
    cases neg with
    | true =>
      have hat2 : At x (i + 1) (0x2D :: digitByte d :: ds.map digitByte) := by simpa [printMinus] using h1
      obtain ⟨h2, h3⟩ := At_cons.mp hat2
      obtain ⟨h3a, h3b⟩ := At_cons.mp h3
      have hlen : (printExp (some (true, d, ds))).length = 3 + ds.length := by simp [printExp, printMinus]; omega
      rw [hlen] at he ⊢
      have hs := scanDig_run x e ds (i + 3) (by simpa using h3b) (by omega) (Or.inl (by omega))
      have hdn : (0x30 ≤ (digitByte d).toNat ∧ (digitByte d).toNat ≤ 0x39) := hdg
      simp [byteIs_eq, h0, h2, h3a, hdn, hs, show i < e by omega, show i + 1 < e by omega, show i + 2 < e by omega]
      omega
    | false =>
      have hat2 : At x (i + 1) (digitByte d :: ds.map digitByte) := by simpa [printMinus] using h1
      obtain ⟨h3a, h3b⟩ := At_cons.mp hat2
      have hlen : (printExp (some (false, d, ds))).length = 2 + ds.length := by simp [printExp, printMinus]; omega
      rw [hlen] at he ⊢
      have hs := scanDig_run x e ds (i + 2) (by simpa using h3b) (by omega) (Or.inl (by omega))
      have hn1 : ¬ (digitByte d = 0x2B) := by intro h; have := digit_nat d; rw [h] at this; revert this; decide
      have hn2 : ¬ (digitByte d = 0x2D) := by intro h; have := digit_nat d; rw [h] at this; revert this; decide
      simp [byteIs_eq, h0, h3a, hdg, hs, hn1, hn2, show i < e by omega, show i + 1 < e by omega]
      omega

theorem printInt_len (ip : IntPart) : 1 ≤ (printInt ip).length := by cases ip <;> simp [printInt]

theorem printInt_head (ip : IntPart) : ∃ c T, printInt ip = c :: T ∧ ¬ c = 0x2D := by
  cases ip with
  | zero => exact ⟨0x30, [], rfl, by decide⟩
  | nz l rest =>
    refine ⟨UInt8.ofNat (0x31 + l.val), rest.map digitByte, rfl, fun h => ?_⟩
    have hl := l.isLt
    have := congrArg UInt8.toNat h
    rw [toNat_byte (by omega)] at this; simp at this; omega

/-- The lexeme the printer wrote for a number, at its offset in the text, passes the check. -/
theorem numLex_complete (x : ByteArray) (o e : Nat) (n : Number) (he : e = o + (printNumber n).length) (hsl : ((L x).drop o).take (e - o) = printNumber n) :
    numLex x o e = true := by
  have hat := At_of_slice hsl
  obtain ⟨neg, ip, fr, ex⟩ := n
  have hS : printNumber ⟨neg, ip, fr, ex⟩ = printMinus neg ++ (printInt ip ++ (printFrac fr ++ printExp ex)) := by
    simp [printNumber, List.append_assoc]
  rw [hS] at hat he
  simp only [List.length_append] at he
  obtain ⟨hatm, hat1⟩ := At_append.mp hat
  obtain ⟨hati, hat2⟩ := At_append.mp hat1
  obtain ⟨hatf, hate⟩ := At_append.mp hat2
  have hint := printInt_len ip
  have hR1 : (printFrac fr ++ printExp ex) = [] ∨ (printFrac fr ++ printExp ex).head? = some 0x2E ∨ (printFrac fr ++ printExp ex).head? = some 0x65 := by
    cases fr with
    | some p => right; left; simp [printFrac]
    | none =>
      cases ex with
      | none => left; simp [printFrac, printExp]
      | some q => right; right; simp [printFrac, printExp]
  have hR2 : printExp ex = [] ∨ (printExp ex).head? = some 0x65 := by
    cases ex with
    | none => left; rfl
    | some q => right; simp [printExp]
  have hsign : numSign x o e = o + (printMinus neg).length :=
    numSign_eq x o e neg (printInt ip ++ (printFrac fr ++ printExp ex)) (by obtain ⟨c, T, h, hc⟩ := printInt_head ip; exact ⟨c, T ++ (printFrac fr ++ printExp ex), by rw [h]; rfl, hc⟩)
      hat (by simp only [List.length_append]; omega)
  have hsi : numInt x (numSign x o e) e = o + (printMinus neg).length + (printInt ip).length := by
    rw [hsign, numInt_eq x _ e ip (printFrac fr ++ printExp ex) hR1 hat1 (by simp only [List.length_append]; omega)]
  have hsf : numFrac x (o + (printMinus neg).length + (printInt ip).length) e = o + (printMinus neg).length + (printInt ip).length + (printFrac fr).length :=
    numFrac_eq x _ e fr (printExp ex) hR2 hat2 (by omega)
  have hse : numExp x (o + (printMinus neg).length + (printInt ip).length + (printFrac fr).length) e = e :=
    by rw [numExp_eq x _ e ex hate (by omega)]; omega
  have hne1 : (o + (printMinus neg).length + (printInt ip).length == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
  have hne2 : (o + (printMinus neg).length + (printInt ip).length + (printFrac fr).length == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
  have hne3 : e ≠ 0 := by omega
  unfold numLex
  simp only [hsi, hsf, hse, hne1, hne2, Bool.false_eq_true, ite_false, bne_iff_ne, ne_eq, hne3, not_false_eq_true, beq_self_eq_true, Bool.and_self]
  simp [hne3]

/-! ## A scalar or string node prints to its value -/

/-- The text region holds `S` at offset `o`. -/
def AtX (x : ByteArray) (o : Nat) (S : List UInt8) : Prop := ∃ X1 X2, L x = X1 ++ S ++ X2 ∧ X1.length = o

theorem AtX_slice {x : ByteArray} {o : Nat} {S : List UInt8} (h : AtX x o S) : ((L x).drop o).take S.length = S ∧ o + S.length ≤ x.size := by
  obtain ⟨X1, X2, hx, h1⟩ := h
  constructor
  · rw [hx, ← h1, List.append_assoc, List.drop_left, List.take_left']
    · rfl
  · rw [size_L, hx]; simp; omega

theorem isEsc_false_iff {c : UInt8} : isEsc c = false ↔ (0x20 ≤ c.toNat ∧ c.toNat ≠ 0x22 ∧ c.toNat ≠ 0x5C) := by
  unfold isEsc
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne, ne_eq, UInt8.not_lt, UInt8.le_iff_toNat_le]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨by simpa using h1, fun e => h2 (UInt8.toNat_inj.mp (by simpa using e)), fun e => h3 (UInt8.toNat_inj.mp (by simpa using e))⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨by simpa using h1, fun e => h2 (by rw [e]; rfl)⟩, fun e => h3 (by rw [e]; rfl)⟩

theorem printNumber_plain (n : Number) : ∀ c ∈ printNumber n, isEsc c = false := by
  obtain ⟨neg, ip, fr, ex⟩ := n
  have hd : ∀ d : Digit, isEsc (digitByte d) = false := fun d => by
    have := digit_nat d
    rw [isEsc_false_iff]; omega
  intro c hc
  simp only [printNumber, List.mem_append] at hc
  rcases hc with ((hc | hc) | hc) | hc
  · cases neg <;> simp [printMinus] at hc <;> subst hc <;> rw [isEsc_false_iff] <;> simp
  · cases ip with
    | zero => simp [printInt] at hc; subst hc; rw [isEsc_false_iff]; simp
    | nz l rest =>
      simp only [printInt, List.mem_cons, List.mem_map] at hc
      rcases hc with rfl | ⟨d, _, rfl⟩
      · have hl := l.isLt
        rw [isEsc_false_iff, toNat_byte (by omega)]; omega
      · exact hd d
  · cases fr with
    | none => simp [printFrac] at hc
    | some p =>
      obtain ⟨d, ds⟩ := p
      simp only [printFrac, List.mem_cons, List.mem_map] at hc
      rcases hc with rfl | rfl | ⟨e, _, rfl⟩
      · rw [isEsc_false_iff]; simp
      · exact hd d
      · exact hd e
  · cases ex with
    | none => simp [printExp] at hc
    | some p =>
      obtain ⟨neg, d, ds⟩ := p
      simp only [printExp, List.mem_cons, List.mem_append, List.mem_map] at hc
      rcases hc with rfl | hc
      · rw [isEsc_false_iff]; simp
      · rcases hc with hc | rfl | ⟨e, _, rfl⟩
        · cases neg <;> simp [printMinus] at hc <;> subst hc <;> rw [isEsc_false_iff] <;> simp
        · exact hd d
        · exact hd e

theorem print_len_pos (v : Value) : 1 ≤ (print v).length := by
  cases v with
  | null => simp [print]
  | bool b => cases b <;> simp [print]
  | num n => simp only [print, printNumber, List.length_append]; have := printInt_len n.int; omega
  | str s => simp [print, printString]
  | arr xs => simp [print]
  | obj ms => simp [print]

theorem size_append_ba (b : ByteArray) (l : List UInt8) : (b ++ ba l).size = b.size + l.length := by
  rw [ByteArray.size_append]
  exact congrArg (b.size + ·) (size_mk l)

theorem lt_2_62 {o : Nat} (ho : o < 2 ^ 50) : UInt64.ofNat o < 0x4000000000000000 ∧ (UInt64.ofNat o).toNat = o := by
  have e : (UInt64.ofNat o).toNat = o := UInt64.toNat_ofNat_of_lt' (by show o < 18446744073709551616; omega)
  refine ⟨?_, e⟩
  rw [UInt64.lt_iff_toNat_lt, e]
  show o < 0x4000000000000000
  omega

theorem textV_str_len (s : String) : (textV (.str s)).length = s.toUTF8.size := (size_list _).symm

theorem pleaf_eq (v : Value) (hv : vKind v ≤ 4) (x : ByteArray) (o : Nat) (hx : AtX x o (textV v)) (ho : o + (textV v).length < 2 ^ 50) (b : ByteArray) :
    pleaf x (headW v) (auxW o v) b = b ++ ba (print v) := by
  cases v with
  | arr _ => simp [vKind] at hv
  | obj _ => simp [vKind] at hv
  | null =>
    obtain ⟨hk, hlen⟩ := head_mod .null (by simp [vLen])
    unfold pleaf; simp only [hk, hlen]
    simp [vKind, vLen, vAux, auxW, print, push_ba, app_ba]
  | bool c =>
    obtain ⟨hk, hlen⟩ := head_mod (.bool c) (by cases c <;> simp [vLen])
    unfold pleaf; simp only [hk, hlen]
    cases c <;> simp [vKind, vLen, vAux, auxW, print, push_ba, app_ba]
  | num n =>
    obtain ⟨hsl, hsz⟩ := AtX_slice hx
    simp only [textV] at hsl hsz ho
    have hn : vLen (.num n) = (printNumber n).length := rfl
    obtain ⟨hk, hlen⟩ := head_mod (.num n) (by rw [hn]; omega)
    obtain ⟨hlt, hoff⟩ := lt_2_62 (o := o) (by omega)
    unfold pleaf; simp only [hk, hlen]
    simp only [vKind, auxW, vAux, hn]
    simp [hlt, hoff, hsz]
    have hsl' : ((L x).drop o).take ((o + (printNumber n).length) - o) = printNumber n := by rw [Nat.add_sub_cancel_left]; exact hsl
    simp only [numLex_complete x o _ n rfl hsl', ↓reduceIte]
    rw [escLoopR_eq x _ hsz _ o b rfl, hsl', flatMap_esc_plain (printNumber_plain n)]
    rfl
  | str s =>
    have hbs : s.toUTF8.size = s.utf8ByteSize := by simp
    have hn : vLen (.str s) = s.utf8ByteSize := by rw [← hbs]; rfl
    have hT : textV (.str s) = s.toList.flatMap String.utf8EncodeChar := by
      simp only [textV]; exact toByteArray_list s
    have hlenT : (textV (.str s)).length = s.utf8ByteSize := by rw [textV_str_len, hbs]
    obtain ⟨hsl, hsz⟩ := AtX_slice hx
    rw [hlenT] at hsl hsz ho
    obtain ⟨hk, hlen⟩ := head_mod (.str s) (by rw [hn]; omega)
    obtain ⟨hlt, hoff⟩ := lt_2_62 (o := o) (by omega)
    unfold pleaf; simp only [hk, hlen]
    simp only [vKind, auxW, vAux, hn]
    simp [hlt, hoff, hsz]
    have hsl' : ((L x).drop o).take ((o + s.utf8ByteSize) - o) = s.toList.flatMap String.utf8EncodeChar := by
      rw [Nat.add_sub_cancel_left, ← hT]; exact hsl
    have hv : utf8Range x o (o + s.utf8ByteSize) = true := by
      apply utf8Range_complete x s.toList o _ _ hsz hsl'
      rw [← hT, hlenT]
    simp only [hv, ↓reduceIte]
    rw [escLoopR_eq x _ hsz _ o _ rfl, hsl', ← hT]
    rw [push_ba, push_ba, app_ba]
    rw [show print (.str s) = 0x22 :: ((textV (.str s)).flatMap escByte ++ [0x22]) from ?_]
    · rw [app_ba]; rfl
    · simp only [print, textV]; exact printString_bytes s

/-! ## Containers -/

/-- The tape holds `T` from word `i` and the text region holds `S` at offset `o`. -/
def TapeOk (w x : ByteArray) (i o : Nat) (T S : List UInt8) : Prop := (∃ P Q, L w = P ++ T ++ Q ∧ P.length = 8 * i) ∧ AtX x o S

theorem TapeOk_split {w x : ByteArray} {i o k : Nat} {T1 T2 S1 S2 : List UInt8} (h : TapeOk w x i o (T1 ++ T2) (S1 ++ S2)) (hk : T1.length = 8 * k) :
    TapeOk w x i o T1 S1 ∧ TapeOk w x (i + k) (o + S1.length) T2 S2 := by
  obtain ⟨⟨P, Q, hw, hP⟩, X1, X2, hx, hX⟩ := h
  refine ⟨⟨⟨P, T2 ++ Q, by rw [hw]; simp, hP⟩, X1, S2 ++ X2, by rw [hx]; simp, hX⟩, ⟨⟨P ++ T1, Q, by rw [hw]; simp, by simp [hP, hk]; omega⟩, X1 ++ S1, X2, by rw [hx]; simp, by simp [hX]⟩⟩

theorem TapeOk_w {w x : ByteArray} {i o : Nat} {T S : List UInt8} (h : TapeOk w x i o T S) : ∃ P Q, L w = P ++ T ++ Q ∧ P.length = 8 * i := h.1
theorem TapeOk_x {w x : ByteArray} {i o : Nat} {T S : List UInt8} (h : TapeOk w x i o T S) : AtX x o S := h.2

def pElemsFrom : Bool → List Value → List UInt8
  | _, [] => []
  | first, v :: vs => (if first then [] else [0x2C]) ++ print v ++ pElemsFrom false vs

def pMembersFrom : Bool → List (String × Value) → List UInt8
  | _, [] => []
  | first, (k, v) :: ms => (if first then [] else [0x2C]) ++ printString k ++ 0x3A :: (print v ++ pMembersFrom false ms)

theorem printElems_from : ∀ vs : List Value, printElems vs = pElemsFrom true vs ∧ (vs ≠ [] → pElemsFrom false vs = 0x2C :: printElems vs)
  | [] => by simp [printElems, pElemsFrom]
  | [v] => by simp [printElems, pElemsFrom]
  | v :: w :: ws => by
    obtain ⟨h1, h2⟩ := printElems_from (w :: ws)
    have e1 : pElemsFrom true (v :: w :: ws) = print v ++ pElemsFrom false (w :: ws) := rfl
    have e2 : pElemsFrom false (v :: w :: ws) = 0x2C :: (print v ++ pElemsFrom false (w :: ws)) := rfl
    have pe : printElems (v :: w :: ws) = print v ++ 0x2C :: printElems (w :: ws) := rfl
    refine ⟨?_, fun _ => ?_⟩
    · rw [e1, h2 (by simp), pe]
    · rw [e2, h2 (by simp), pe]

theorem printMembers_from : ∀ ms : List (String × Value), printMembers ms = pMembersFrom true ms ∧ (ms ≠ [] → pMembersFrom false ms = 0x2C :: printMembers ms)
  | [] => by simp [printMembers, pMembersFrom]
  | [(k, v)] => by simp [printMembers, pMembersFrom]
  | (k, v) :: m :: ms => by
    obtain ⟨h1, h2⟩ := printMembers_from (m :: ms)
    have e1 : pMembersFrom true ((k, v) :: m :: ms) = printString k ++ 0x3A :: (print v ++ pMembersFrom false (m :: ms)) := rfl
    have e2 : pMembersFrom false ((k, v) :: m :: ms) = 0x2C :: (printString k ++ 0x3A :: (print v ++ pMembersFrom false (m :: ms))) := rfl
    have pm : printMembers ((k, v) :: m :: ms) = printString k ++ 0x3A :: (print v ++ 0x2C :: printMembers (m :: ms)) := by simp [printMembers]
    refine ⟨?_, fun _ => ?_⟩
    · rw [e1, h2 (by simp), pm]
    · rw [e2, h2 (by simp), pm]

theorem u64_le4 {k : Nat} (hk : k < 256) : UInt64.ofNat k ≤ 4 ↔ k ≤ 4 := by
  rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' (by show k < 18446744073709551616; omega)]
  show k ≤ 4 ↔ k ≤ 4
  exact Iff.rfl

theorem u64_beq {k m : Nat} (hk : k < 256) (hm : m < 256) : (UInt64.ofNat k == UInt64.ofNat m) = decide (k = m) := by
  have a := UInt64.toNat_ofNat_of_lt' (n := k) (by show k < 18446744073709551616; omega)
  have b := UInt64.toNat_ofNat_of_lt' (n := m) (by show m < 18446744073709551616; omega)
  by_cases h : k = m
  · subst h; simp
  · have : UInt64.ofNat k ≠ UInt64.ofNat m := fun e => h (by rw [← a, ← b, e])
    simp [h, this]

theorem vKind_lt (v : Value) : vKind v < 256 := by cases v with | bool c => cases c <;> simp [vKind] | _ => simp [vKind]

theorem leaf_words (v : Value) (h : vKind v ≤ 4) : wordsV v = 2 := by
  cases v with
  | arr _ => simp [vKind] at h
  | obj _ => simp [vKind] at h
  | _ => simp [wordsV]

theorem depth_leaf (v : Value) (h : vKind v ≤ 4) : v.depth = 0 := by
  cases v with
  | arr _ => simp [vKind] at h
  | obj _ => simp [vKind] at h
  | _ => simp [Value.depth]

theorem words_pos (v : Value) : 2 ≤ wordsV v := by cases v <;> simp [wordsV] <;> omega

theorem len_le_words (xs : List Value) : xs.length ≤ wordsL xs := by
  induction xs with
  | nil => simp [wordsL]
  | cons v vs ih => simp only [List.length_cons, wordsL]; have := words_pos v; omega

theorem len_le_wordsM (ms : List (String × Value)) : ms.length ≤ wordsM ms := by
  induction ms with
  | nil => simp [wordsM]
  | cons m ms ih => obtain ⟨k, v⟩ := m; simp only [List.length_cons, wordsM]; have := words_pos v; omega

theorem vLen_lt (v : Value) (ho : (textV v).length < 2 ^ 50) (hw : wordsV v < 2 ^ 50) : vLen v < 2 ^ 56 := by
  cases v with
  | num n => simp only [vLen, textV] at ho ⊢; omega
  | str s => simp only [vLen]; rw [textV_str_len] at ho; omega
  | arr xs => have := len_le_words xs; simp only [vLen, wordsV] at hw ⊢; omega
  | obj ms => have := len_le_wordsM ms; simp only [vLen, wordsV] at hw ⊢; omega
  | bool c => cases c <;> simp [vLen]
  | null => simp [vLen]

theorem sizeNe (b : ByteArray) (l : List UInt8) (h : 1 ≤ l.length) : ((b ++ ba l).size == 0) = false := by
  rw [size_append_ba]; exact beq_eq_false_iff_ne.mpr (by omega)

theorem comma_eq (first : Bool) (b : ByteArray) : (if first then b else b.push 0x2C) = b ++ ba (if first then [] else [0x2C]) := by
  cases first <;> simp [push_ba, ba_nil]

theorem container_depth (v : Value) (h : 5 ≤ vKind v) : 1 ≤ v.depth := by
  cases v with
  | arr xs => simp [Value.depth]
  | obj ms => simp [Value.depth]
  | bool c => cases c <;> simp [vKind] at h
  | _ => simp [vKind] at h

mutual
theorem pnode_eq : ∀ (v : Value) (d : Nat) (w x : ByteArray) (i o : Nat) (b : ByteArray), 5 ≤ vKind v → v.depth ≤ d + 1 →
    TapeOk w x i o (tapeV o v) (textV v) → wordsV v < 2 ^ 50 → o + (textV v).length < 2 ^ 50 →
    pnode ldw pleaf w x (d + 1) i (headW v) (auxW o v) b = (b ++ ba (print v), i + wordsV v)
  | .arr xs, d, w, x, i, o, b, hk, hd, hT, hw, ho => by
    simp only [Value.depth] at hd
    have hT' : TapeOk w x i o (wordBytes (headW (.arr xs)) ++ wordBytes (auxW o (.arr xs)) ++ tapeL o xs) ([] ++ textL xs) := by
      have := hT; rw [tapeV_eq] at this; simpa [vRest, textV] using this
    obtain ⟨hh, hrest⟩ := TapeOk_split hT' (k := 2) (by simp [wordBytes_length])
    simp only [List.length_nil, Nat.add_zero] at hrest
    simp only [textV] at ho
    have hwa : wordsV (.arr xs) = 2 + wordsL xs := rfl
    have hl := len_le_words xs
    obtain ⟨hk5, hlen⟩ := head_mod (.arr xs) (by simp only [vLen]; omega)
    simp only [vLen] at hlen
    unfold pnode
    rw [hk5]
    simp only [vKind, u64_beq (show 5 < 256 by omega) (show 5 < 256 by omega), decide_true, ite_true]
    rw [hlen]
    rw [pelems_eq xs d w x (i + 2) o true (b.push 0x5B) (by omega) hrest (by omega) (by omega)]
    dsimp only
    have e5 : (UInt64.ofNat 5 == 5) = true := by decide
    have hs : ((b.push 91 ++ ba (pElemsFrom true xs)).size != 0) = true := by
      rw [push_ba, app_ba, size_append_ba]; simp
    have ha : auxW o (.arr xs) = UInt64.ofNat (i + 2 + wordsL xs - i) := by
      simp only [auxW, vAux, wordsV]; congr 1; omega
    simp only [e5, ite_true, hs, ha, beq_self_eq_true, Bool.and_self]
    rw [push_ba, push_ba, app_ba, app_ba, ← List.append_assoc, (printElems_from xs).1.symm]
    simp [print, wordsV] <;> omega
  | .obj ms, d, w, x, i, o, b, hk, hd, hT, hw, ho => by
    simp only [Value.depth] at hd
    have hT' : TapeOk w x i o (wordBytes (headW (.obj ms)) ++ wordBytes (auxW o (.obj ms)) ++ tapeM o ms) ([] ++ textM ms) := by
      have := hT; rw [tapeV_eq] at this; simpa [vRest, textV] using this
    obtain ⟨hh, hrest⟩ := TapeOk_split hT' (k := 2) (by simp [wordBytes_length])
    simp only [List.length_nil, Nat.add_zero] at hrest
    simp only [textV] at ho
    have hwa : wordsV (.obj ms) = 2 + wordsM ms := rfl
    have hl := len_le_wordsM ms
    obtain ⟨hk6, hlen⟩ := head_mod (.obj ms) (by simp only [vLen]; omega)
    simp only [vLen] at hlen
    unfold pnode
    rw [hk6]
    have e65 : (UInt64.ofNat 6 == 5) = false := by decide
    have e66 : (UInt64.ofNat 6 == 6) = true := by decide
    simp only [vKind, e65, e66, Bool.false_eq_true, ↓reduceIte]
    rw [hlen]
    rw [pmembers_eq ms d w x (i + 2) o true (b.push 0x7B) (by omega) hrest (by omega) (by omega)]
    dsimp only
    have hs : ((b.push 123 ++ ba (pMembersFrom true ms)).size != 0) = true := by
      rw [push_ba, app_ba, size_append_ba]; simp
    have ha : auxW o (.obj ms) = UInt64.ofNat (i + 2 + wordsM ms - i) := by
      simp only [auxW, vAux, wordsV]; congr 1; omega
    simp only [hs, ha, beq_self_eq_true, Bool.and_self, ↓reduceIte]
    rw [push_ba, push_ba, app_ba, app_ba, ← List.append_assoc, (printMembers_from ms).1.symm]
    simp [print, wordsV] <;> omega
  | .null, _, _, _, _, _, _, hk, _, _, _, _ => by simp [vKind] at hk
  | .bool c, _, _, _, _, _, _, hk, _, _, _, _ => by cases c <;> simp [vKind] at hk
  | .num _, _, _, _, _, _, _, hk, _, _, _, _ => by simp [vKind] at hk
  | .str _, _, _, _, _, _, _, hk, _, _, _, _ => by simp [vKind] at hk

theorem pelems_eq : ∀ (vs : List Value) (d : Nat) (w x : ByteArray) (i o : Nat) (first : Bool) (b : ByteArray),
    depthList vs ≤ d → TapeOk w x i o (tapeL o vs) (textL vs) → wordsL vs < 2 ^ 50 → o + (textL vs).length < 2 ^ 50 →
    pelems ldw pleaf w x d i vs.length first b = (b ++ ba (pElemsFrom first vs), i + wordsL vs)
  | [], d, w, x, i, o, first, b, _, _, _, _ => by
    simp [pelems, pElemsFrom, wordsL, ba_nil]
  | v :: vs, d, w, x, i, o, first, b, hd, hT, hw, ho => by
    simp only [depthList] at hd
    have hd1 : v.depth ≤ d := Nat.le_trans (Nat.le_max_left _ _) hd
    have hd2 : depthList vs ≤ d := Nat.le_trans (Nat.le_max_right _ _) hd
    simp only [wordsL] at hw ⊢
    simp only [textL, List.length_append] at ho
    have hT' : TapeOk w x i o (tapeV o v ++ tapeL (o + (textV v).length) vs) (textV v ++ textL vs) := hT
    obtain ⟨hv1, hv2⟩ := TapeOk_split hT' (tapeV_length o v)
    obtain ⟨P, Q, hwP, hP⟩ := TapeOk_w hv1
    obtain ⟨hsz, hr1, hr2⟩ := read_node hwP hP
    have hwv := words_pos v
    have hlenv := vLen_lt v (by omega) (by omega)
    obtain ⟨hk, hlen⟩ := head_mod v hlenv
    rw [List.length_cons, pelems]
    simp only [show 8 * i + 16 ≤ w.size by omega, ↓reduceIte, hr1, hr2, hk, comma_eq]
    by_cases hleaf : vKind v ≤ 4
    · have hl2 := leaf_words v hleaf
      simp only [(u64_le4 (vKind_lt v)).mpr hleaf, ↓reduceIte]
      rw [pleaf_eq v hleaf x o (TapeOk_x hv1) (by omega)]
      rw [sizeNe _ _ (print_len_pos v)]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hl2] at hv2
      have := pelems_eq vs d w x (i + 2) (o + (textV v).length) false (b ++ ba (if first then [] else [0x2C]) ++ ba (print v)) hd2 hv2 (by omega) (by omega)
      rw [this, hl2]
      simp only [Prod.mk.injEq]
      refine ⟨?_, by omega⟩
      simp only [app_ba, pElemsFrom, List.append_assoc]
    · have hk5 : 5 ≤ vKind v := by omega
      have hnl : ¬ UInt64.ofNat (vKind v) ≤ 4 := fun h => hleaf ((u64_le4 (vKind_lt v)).mp h)
      simp only [hnl, ↓reduceIte]
      have hdv := container_depth v hk5
      obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
      rw [pnode_eq v d' w x i o _ hk5 hd1 hv1 (by omega) (by omega)]
      dsimp only
      rw [sizeNe _ _ (print_len_pos v)]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have := pelems_eq vs (d' + 1) w x (i + wordsV v) (o + (textV v).length) false (b ++ ba (if first then [] else [0x2C]) ++ ba (print v)) hd2 hv2 (by omega) (by omega)
      rw [this]
      simp only [Prod.mk.injEq]
      refine ⟨?_, by omega⟩
      simp only [app_ba, pElemsFrom, List.append_assoc]


theorem pmembers_eq : ∀ (ms : List (String × Value)) (d : Nat) (w x : ByteArray) (i o : Nat) (first : Bool) (b : ByteArray),
    depthMembers ms ≤ d → TapeOk w x i o (tapeM o ms) (textM ms) → wordsM ms < 2 ^ 50 → o + (textM ms).length < 2 ^ 50 →
    pmembers ldw pleaf w x d i ms.length first b = (b ++ ba (pMembersFrom first ms), i + wordsM ms)
  | [], d, w, x, i, o, first, b, _, _, _, _ => by
    simp [pmembers, pMembersFrom, wordsM, ba_nil]
  | (k, v) :: ms, d, w, x, i, o, first, b, hd, hT, hw, ho => by
    simp only [depthMembers] at hd
    have hd1 : v.depth ≤ d := Nat.le_trans (Nat.le_max_left _ _) hd
    have hd2 : depthMembers ms ≤ d := Nat.le_trans (Nat.le_max_right _ _) hd
    simp only [wordsM] at hw ⊢
    simp only [textM, List.length_append] at ho
    have hwv := words_pos v
    have hwK : wordsV (.str k) = 2 := rfl
    have hKt : textV (.str k) = k.toUTF8.data.toList := rfl
    have hKl : (textV (.str k)).length = k.toUTF8.size := textV_str_len k
    have hKl' : k.toUTF8.data.toList.length = k.toUTF8.size := (size_list _).symm
    have hT' : TapeOk w x i o (tapeV o (.str k) ++ (tapeV (o + (textV (.str k)).length) v ++ tapeM (o + (textV (.str k)).length + (textV v).length) ms))
        (textV (.str k) ++ (textV v ++ textM ms)) := by
      have : tapeM o ((k, v) :: ms) = tapeV o (.str k) ++ (tapeV (o + (textV (.str k)).length) v ++ tapeM (o + (textV (.str k)).length + (textV v).length) ms) := by
        simp only [tapeM, tapeV, hKl, List.append_assoc]
      have h2 : textM ((k, v) :: ms) = textV (.str k) ++ (textV v ++ textM ms) := by simp [textM, hKt]
      rw [this, h2] at hT; exact hT
    obtain ⟨hk1, hrest1⟩ := TapeOk_split hT' (k := 2) (by rw [tapeV_length, hwK])
    obtain ⟨hv1, hrest2⟩ := TapeOk_split hrest1 (k := wordsV v) (tapeV_length _ v)
    obtain ⟨P1, Q1, hw1, hP1⟩ := TapeOk_w hk1
    obtain ⟨hsz1, hr11, hr12⟩ := read_node hw1 hP1
    obtain ⟨P2, Q2, hw2, hP2⟩ := TapeOk_w hv1
    obtain ⟨hsz2, hr21, hr22⟩ := read_node hw2 hP2
    have hlenK := vLen_lt (.str k) (by omega) (by omega)
    obtain ⟨hkk, hlenKK⟩ := head_mod (.str k) hlenK
    have hlenv := vLen_lt v (by omega) (by omega)
    obtain ⟨hkv, hlenvv⟩ := head_mod v hlenv
    have hr22' : ldw w (i + 3) = auxW (o + (textV (.str k)).length) v := hr22
    have e4 : (UInt64.ofNat 4 == 4) = true := by decide
    rw [List.length_cons, pmembers]
    simp only [show 8 * i + 32 ≤ w.size by omega, ↓reduceIte, hr11, hr12, hkk, comma_eq]
    simp only [vKind, e4, ↓reduceIte]
    rw [pleaf_eq (.str k) (by simp [vKind]) x o (TapeOk_x hk1) (by omega)]
    rw [sizeNe _ _ (print_len_pos (.str k))]
    simp only [Bool.false_eq_true, ↓reduceIte, hr21, hr22', hkv]
    have hmf : pMembersFrom first ((k, v) :: ms) = (if first then [] else [0x2C]) ++ printString k ++ 0x3A :: (print v ++ pMembersFrom false ms) := rfl
    have hpk : print (.str k) = printString k := rfl
    by_cases hleaf : vKind v ≤ 4
    · have hl2 := leaf_words v hleaf
      simp only [(u64_le4 (vKind_lt v)).mpr hleaf, ↓reduceIte]
      rw [pleaf_eq v hleaf x _ (TapeOk_x hv1) (by omega)]
      rw [sizeNe _ _ (print_len_pos v)]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hrest2' : TapeOk w x (i + 4) (o + (textV (.str k)).length + (textV v).length) (tapeM (o + (textV (.str k)).length + (textV v).length) ms) (textM ms) := by
        rw [hl2] at hrest2; exact hrest2
      have := pmembers_eq ms d w x (i + 4) _ false ((b ++ ba (if first = true then [] else [44]) ++ ba (print (Value.str k))).push 58 ++ ba (print v)) hd2 hrest2' (by omega) (by omega)
      rw [this]
      simp only [Prod.mk.injEq]
      refine ⟨?_, by omega⟩
      rw [hmf, hpk, push_ba]
      simp only [app_ba, List.append_assoc, List.cons_append, List.singleton_append]
      rfl
    · have hk5 : 5 ≤ vKind v := by omega
      have hnl : ¬ UInt64.ofNat (vKind v) ≤ 4 := fun h => hleaf ((u64_le4 (vKind_lt v)).mp h)
      simp only [hnl, ↓reduceIte]
      have hdv := container_depth v hk5
      obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
      rw [pnode_eq v d' w x (i + 2) _ _ hk5 hd1 hv1 (by omega) (by omega)]
      dsimp only
      rw [sizeNe _ _ (print_len_pos v)]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have := pmembers_eq ms (d' + 1) w x (i + 2 + wordsV v) _ false ((b ++ ba (if first = true then [] else [44]) ++ ba (print (Value.str k))).push 58 ++ ba (print v)) hd2 hrest2 (by omega) (by omega)
      rw [this]
      simp only [Prod.mk.injEq]
      refine ⟨?_, by omega⟩
      rw [hmf, hpk, push_ba]
      simp only [app_ba, List.append_assoc, List.cons_append, List.singleton_append]
      rfl

end

theorem empty_append_ba (c : Nat) (l : List UInt8) : ByteArray.emptyWithCapacity c ++ ba l = ba l := by
  apply ByteArray.ext; simp [ByteArray.data_append, ByteArray.emptyWithCapacity] <;> rfl

/-- The tape that the parser's encoder writes for a value prints to the reference printer's bytes: for a value within `maxDepth` whose tape (in words) and text fit the format (below 2^50: the head word holds a length below
2^56 and an offset is a word below 2^62). -/
theorem printTape_encode (v : Value) (hd : v.depth ≤ maxDepth) (hw : wordsV v < 2 ^ 50) (ht : (textV v).length < 2 ^ 50) :
    printTape (encValue v ⟨.empty, .empty⟩).tape (encValue v ⟨.empty, .empty⟩).text = some (ba (print v)) := by
  obtain ⟨h1, h2⟩ := encValue_empty v
  suffices key : ∀ (w x : ByteArray), L w = tapeV 0 v → L x = textV v → printTape w x = some (ba (print v)) from key _ _ h1 h2
  intro w x hwL hxL
  have hT : TapeOk w x 0 0 (tapeV 0 v) (textV v) := ⟨⟨[], [], by rw [hwL]; simp, rfl⟩, [], [], by rw [hxL]; simp, rfl⟩
  have hws : w.size = 8 * wordsV v := by rw [size_L, hwL, tapeV_length]
  have hwv := words_pos v
  obtain ⟨hsz, hr1, hr2⟩ := read_node (i := 0) (o := 0) (v := v) (P := []) (Q := []) (by rw [hwL]; simp) rfl
  have hlenv := vLen_lt v (by omega) (by omega)
  obtain ⟨hk, hlen⟩ := head_mod v hlenv
  unfold printTape printTapeG
  simp only [show 16 ≤ w.size by omega, ↓reduceIte, hr1, hr2, hk]
  by_cases hleaf : vKind v ≤ 4
  · have hl2 := leaf_words v hleaf
    simp only [(u64_le4 (vKind_lt v)).mpr hleaf, ↓reduceIte]
    rw [pleaf_eq v hleaf x 0 (TapeOk_x hT) (by omega), empty_append_ba]
    have hsn : ((ba (print v)).size != 0) = true := by
      rw [size_mk]; exact bne_iff_ne.mpr (by have := print_len_pos v; omega)
    have hw16 : (w.size == 16) = true := by rw [hws, hl2]; rfl
    simp only [hsn, hw16, Bool.and_self, ↓reduceIte]
  · have hk5 : 5 ≤ vKind v := by omega
    have hnl : ¬ UInt64.ofNat (vKind v) ≤ 4 := fun h => hleaf ((u64_le4 (vKind_lt v)).mp h)
    simp only [hnl, ↓reduceIte]
    have hdv := container_depth v hk5
    have hmd : maxDepth = 511 + 1 := rfl
    rw [hmd]
    rw [pnode_eq v 511 w x 0 0 _ hk5 (by rw [← hmd]; exact hd) hT hw (by omega), empty_append_ba]
    have hsn : ((ba (print v)).size != 0) = true := by
      rw [size_mk]; exact bne_iff_ne.mpr (by have := print_len_pos v; omega)
    have hws' : (8 * (0 + wordsV v) == w.size) = true := by rw [hws]; simp
    simp only [hsn, hws', Bool.and_self, ↓reduceIte]

/-- The checked string literal of the UTF-8 of a string is what the reference prints for it (and is never refused). -/
theorem escapeChecked_eq (s : String) : escapeChecked s.toUTF8 = some (ba (printString s)) := by
  unfold escapeChecked
  have hT : L s.toUTF8 = s.toList.flatMap String.utf8EncodeChar := toByteArray_list s
  have hv : utf8Range s.toUTF8 0 s.toUTF8.size = true := by
    apply utf8Range_complete s.toUTF8 s.toList 0 _ _ (Nat.le_refl _)
    · rw [Nat.sub_zero, List.drop_zero, size_L, List.take_length, hT]
    · rw [Nat.zero_add, show s.toUTF8.size = (L s.toUTF8).length from size_L _, hT]
  simp only [hv, ↓reduceIte, escapeString_eq]

end LeanJson
