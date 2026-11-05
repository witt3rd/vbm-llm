import VbmLlm.Anthropic.Stream
import VbmLlmProofs.Anthropic.Event
/-! # Proofs about the Anthropic stream fold (`VbmLlm/Anthropic/Stream.lean`)

* **Chunk boundaries do not matter** (`Acc.apply_text`, `Acc.apply_json`, `Acc.apply_thinking`, `step_delta_split`): applying two deltas of a kind in a row is applying their concatenation, on a block and on the whole fold's state.
* **The terminal rule** (`foldWith_no_stop`, `foldItems_complete`, `foldItems_after_stop`): a stream with no `message_stop` is never `complete`, `complete` comes only from a `message_stop` that is the last event, an event after it is refused.
* **Order** (`foldItems_before_start`, `foldItems_start_twice`): nothing but `ping` may come before `message_start`, and a second one is refused.
* **An error event stops the fold** with the partial reply (`foldWith_error_event`); no events is `truncated` with nothing received (`foldItems_nil`).
* **Merge** (`step_start_identity`, `step_msgDelta_stop_reason`, `mergeUsage_later`): the usage counts and the stop reason are the last non-null ones. -/
namespace VbmLlm.Anthropic
open LeanJson

/-! ### Chunk boundaries -/

theorem Acc.apply_text (a : Acc) (s t : String) : (a.apply (.text s)).bind (fun a' => a'.apply (.text t)) = a.apply (.text (s ++ t)) := by
  obtain ⟨i, b, j⟩ := a
  cases b <;> simp [Acc.apply, String.append_assoc]

theorem Acc.apply_json (a : Acc) (s t : String) : (a.apply (.json s)).bind (fun a' => a'.apply (.json t)) = a.apply (.json (s ++ t)) := by
  obtain ⟨i, b, j⟩ := a
  cases b <;> simp [Acc.apply, String.append_assoc]

theorem Acc.apply_thinking (a : Acc) (s t : String) : (a.apply (.thinking s)).bind (fun a' => a'.apply (.thinking t)) = a.apply (.thinking (s ++ t)) := by
  obtain ⟨i, b, j⟩ := a
  cases b <;> simp [Acc.apply, String.append_assoc]

theorem Acc.apply_index (a a' : Acc) (d : Delta) (h : a.apply d = some a') : a'.index = a.index := by
  obtain ⟨i, b, j⟩ := a
  cases d <;> cases b <;> simp [Acc.apply] at h <;> subst h <;> rfl

theorem mapM_bind_mapM {α : Type} (f g : α → Option α) : ∀ l : List α, (l.mapM f).bind (fun m => m.mapM g) = l.mapM (fun a => (f a).bind g)
  | [] => rfl
  | x :: xs => by
    have ih := mapM_bind_mapM f g xs
    cases hm : xs.mapM f with
    | none =>
      rw [hm] at ih
      cases hf : f x <;> simp [List.mapM_cons, hf, hm, ← ih]
    | some ys =>
      rw [hm] at ih
      cases hf : f x with
      | none => simp [List.mapM_cons, hf, hm]
      | some y =>
        cases hg : g y with
        | none => simp [List.mapM_cons, hf, hm, hg]
        | some z => simp [List.mapM_cons, hf, hm, hg, ← ih]

theorem mapM_indices (f : Acc → Option Acc) (hf : ∀ a a', f a = some a' → a'.index = a.index) : ∀ (l bs : List Acc), l.mapM f = some bs → bs.map (·.index) = l.map (·.index)
  | [], bs, h => by simp [List.mapM_nil] at h; subst h; rfl
  | x :: xs, bs, h => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff] at h
    obtain ⟨y, hy, ys, hys, hbs⟩ := h
    simp only [pure, Option.some.injEq] at hbs
    subst hbs
    simp [hf x y hy, mapM_indices f hf xs ys hys]

theorem mapM_apply_indices (idx : Nat) (d : Delta) (l bs : List Acc) (h : l.mapM (fun a => if a.index = idx then a.apply d else some a) = some bs) :
    bs.map (·.index) = l.map (·.index) := by
  refine mapM_indices _ ?_ l bs h
  intro a a' ha
  by_cases hb : a.index = idx
  · simp only [hb, ite_true] at ha; exact Acc.apply_index a a' d ha
  · simp only [hb, ite_false, Option.some.injEq] at ha; subst ha; rfl

/-- The two deltas, one after the other, change the state as their concatenation does (whenever the delta pair splits on every block). -/
theorem step_delta_split (i : Nat) (s : State) (idx : Nat) (d1 d2 d12 : Delta) (h : ∀ a : Acc, (a.apply d1).bind (fun a' => a'.apply d2) = a.apply d12) :
    (step i s (.blockDelta idx d1)).bind (fun s' => step i s' (.blockDelta idx d2)) = step i s (.blockDelta idx d12) := by
  cases hs : s.started
  · simp [step, hs, Except.bind]
  · by_cases hx : ∀ x ∈ s.blocks, ¬x.index = idx
    · simp only [step, hs, Bool.false_eq_true, ite_false, Bool.not_true, Except.bind] at *
      split <;> simp_all
    · have key : ∀ (l : List Acc), (l.mapM (fun a => if a.index = idx then a.apply d1 else some a)).bind (fun m => m.mapM (fun a => if a.index = idx then a.apply d2 else some a))
          = l.mapM (fun a => if a.index = idx then a.apply d12 else some a) := by
        intro l
        rw [mapM_bind_mapM]
        congr 1; funext a
        by_cases hi : a.index = idx
        · simp only [hi, ite_true]
          cases ha : a.apply d1 with
          | none => simp [← h a, ha]
          | some a' =>
            have := Acc.apply_index a a' d1 ha
            simp [← h a, ha, this, hi]
        · simp [hi]
      cases hm : s.blocks.mapM (fun a => if a.index = idx then a.apply d1 else some a) with
      | none =>
        have hm12 : s.blocks.mapM (fun a => if a.index = idx then a.apply d12 else some a) = none := by
          rw [← key s.blocks, hm]; rfl
        simp [step, hs, hx, hm, hm12, Except.bind]
      | some bs =>
        have hmap := mapM_apply_indices idx d1 s.blocks bs (by simpa using hm)
        have hbx : ¬ ∀ x ∈ bs, ¬x.index = idx := by
          intro hall
          apply hx
          intro x hxm hxi
          have h1 : idx ∈ bs.map (·.index) := by rw [hmap]; exact List.mem_map.2 ⟨x, hxm, hxi⟩
          obtain ⟨y, hy, hyi⟩ := List.mem_map.1 h1
          exact hall y hy hyi
        have e : bs.mapM (fun a => if a.index = idx then a.apply d2 else some a) = s.blocks.mapM (fun a => if a.index = idx then a.apply d12 else some a) := by
          rw [← key s.blocks, hm]; rfl
        simp [step, hs, hx, hm, hbx, e, Except.bind]

/-! ### The terminal rule -/

/-- An item the fold applies to the state (not a ping, a stop or an error). -/
def Item.Plain : Item → Prop
  | .ping | .stop | .error _ => False
  | _ => True

theorem foldWith_plain {α : Type} (parse : String → Option Value) (dec : Nat → α → Except StreamFault Item) (x : α) (rest : List α) (i : Nat) (s : State) (it : Item)
    (hd : dec i x = .ok it) (hp : it.Plain) : foldWith parse dec (x :: rest) i s =
      (match step i s it with | .error f => .error f | .ok s' => foldWith parse dec rest (i + 1) s') := by
  simp only [foldWith, hd]
  cases it <;> first | exact hp.elim | rfl

/-- **A stream with no `message_stop` is never complete.** -/
theorem foldWith_no_stop {α : Type} (parse : String → Option Value) (dec : Nat → α → Except StreamFault Item) (l : List α) (i : Nat) (s : State) (r : Response)
    (h : ∀ j x, x ∈ l → ¬ (dec j x = .ok Item.stop)) : ¬ (foldWith parse dec l i s = .ok (.complete r)) := by
  induction l generalizing i s with
  | nil => simp [foldWith]
  | cons x rest ih =>
    intro hc
    have hx := h i x (by simp)
    have plain : ∀ it : Item, it.Plain → dec i x = .ok it → False := by
      intro it hp hd'
      rw [foldWith_plain parse dec x rest i s it hd' hp] at hc
      cases hs : step i s it with
      | error f => simp [hs] at hc
      | ok s' => simp only [hs] at hc; exact ih (i + 1) s' (fun j y hy => h j y (by simp [hy])) hc
    cases hd : dec i x with
    | error f => unfold foldWith at hc; simp [hd] at hc
    | ok it =>
      cases it with
      | ping => unfold foldWith at hc; simp only [hd] at hc; exact ih (i + 1) s (fun j y hy => h j y (by simp [hy])) hc
      | stop => exact hx hd
      | error m => unfold foldWith at hc; simp [hd] at hc
      | start a b c => exact plain (.start a b c) trivial hd
      | blockStart k b => exact plain (.blockStart k b) trivial hd
      | blockDelta k d => exact plain (.blockDelta k d) trivial hd
      | blockStop k => exact plain (.blockStop k) trivial hd
      | msgDelta a b c => exact plain (.msgDelta a b c) trivial hd

/-- **`complete` comes only from a `message_stop` that is the last event.** -/
theorem foldItems_complete (parse : String → Option Value) (items : List Item) (r : Response) (h : foldItems parse items = .ok (.complete r)) : ∃ pre, items = pre ++ [.stop] := by
  have gen : ∀ (l : List Item) (i : Nat) (s : State), foldWith parse (fun _ x => .ok x) l i s = .ok (.complete r) → ∃ pre, l = pre ++ [.stop] := by
    intro l
    induction l with
    | nil => intro i s hc; simp [foldWith] at hc
    | cons x rest ih =>
      intro i s hc
      have plain : x.Plain → ∃ pre, x :: rest = pre ++ [.stop] := by
        intro hp
        rw [foldWith_plain parse _ x rest i s x rfl hp] at hc
        cases hs : step i s x with
        | error f => simp [hs] at hc
        | ok s' =>
          simp only [hs] at hc
          obtain ⟨pre, hp'⟩ := ih (i + 1) s' hc
          exact ⟨x :: pre, by simp [hp']⟩
      cases x with
      | ping => simp only [foldWith] at hc; obtain ⟨pre, hp⟩ := ih (i + 1) s hc; exact ⟨.ping :: pre, by simp [hp]⟩
      | stop =>
        simp only [foldWith] at hc
        by_cases hr : rest.isEmpty = true
        · have : rest = [] := by simpa using hr
          exact ⟨[], by simp [this]⟩
        · simp [hr] at hc
      | error m => simp [foldWith] at hc
      | start a b c => exact plain trivial
      | blockStart k b => exact plain trivial
      | blockDelta k d => exact plain trivial
      | blockStop k => exact plain trivial
      | msgDelta a b c => exact plain trivial
  exact gen items 0 State.empty h

/-- An event after `message_stop` is refused. -/
theorem foldItems_after_stop (parse : String → Option Value) (y : Item) (ys : List Item) : foldItems parse (.stop :: y :: ys) = .error (.afterStop 1) := by
  simp [foldItems, foldWith]

/-- No events: truncated, with nothing received. -/
theorem foldItems_nil (parse : String → Option Value) : foldItems parse [] = .ok (.truncated (State.empty.soFar parse)) := rfl

/-- An `error` event stops the fold, whatever follows it, and carries the partial reply. -/
theorem foldWith_error_event {α : Type} (parse : String → Option Value) (dec : Nat → α → Except StreamFault Item) (x : α) (rest : List α) (i : Nat) (s : State) (m : Option String)
    (h : dec i x = .ok (.error m)) : foldWith parse dec (x :: rest) i s = .ok (.errorEvent m (s.soFar parse)) := by
  simp [foldWith, h]

/-! ### Order -/

/-- Nothing but a ping may come before `message_start`. -/
theorem foldItems_before_start (parse : String → Option Value) (idx : Nat) (b : Block) (d : Delta) (sr ss : Option String) (u : Option Usage) (rest : List Item) :
    foldItems parse (.blockStart idx b :: rest) = .error (.order 0) ∧ foldItems parse (.blockDelta idx d :: rest) = .error (.order 0) ∧
    foldItems parse (.blockStop idx :: rest) = .error (.order 0) ∧ foldItems parse (.msgDelta sr ss u :: rest) = .error (.order 0) ∧ foldItems parse (.stop :: []) = .error (.order 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [foldItems, foldWith, step, State.empty]

/-- A second `message_start` is refused. -/
theorem foldItems_start_twice (parse : String → Option Value) (a b : Option String) (u v : Option Usage) (c d : Option String) (rest : List Item) :
    foldItems parse (.start a b u :: .start c d v :: rest) = .error (.order 1) := by
  simp [foldItems, foldWith, step, State.empty]

/-! ### Merge -/

theorem later_some (a : Option Nat) (n : Nat) : later a (some n) = some n := rfl

theorem later_none (a : Option Nat) : later a none = a := rfl

/-- Each usage count is the last non-null one. -/
theorem mergeUsage_later (a b : Usage) : (mergeUsage a b).outputTokens = later a.outputTokens b.outputTokens ∧ (mergeUsage a b).inputTokens = later a.inputTokens b.inputTokens ∧
    (mergeUsage a b).cacheReadTokens = later a.cacheReadTokens b.cacheReadTokens ∧ (mergeUsage a b).cacheCreationTokens = later a.cacheCreationTokens b.cacheCreationTokens := ⟨rfl, rfl, rfl, rfl⟩

/-- `message_start` sets the identity and the first usage. -/
theorem step_start_identity (i : Nat) (id model : Option String) (u : Option Usage) :
    step i State.empty (.start id model u) = .ok { State.empty with id := id, model := model, usage := u, started := true } := rfl

/-- A `message_delta` with a stop reason sets it (the last one wins). -/
theorem step_msgDelta_stop_reason (i : Nat) (s : State) (hs : s.started = true) (r : String) (ss : Option String) (u : Option Usage) :
    ∀ s', step i s (.msgDelta (some r) ss u) = .ok s' → s'.stopReason = some r := by
  intro s' h
  simp [step, hs] at h
  subst h
  rfl

/-- A `message_delta` that carries nothing leaves the state as it was. -/
theorem step_msgDelta_keeps (i : Nat) (s : State) (hs : s.started = true) : step i s (.msgDelta none none none) = .ok s := by
  cases s
  simp_all [step, mergeUsageOpt]

/-! ### A call's input -/

/-- A call whose pieces parse to a value (not `null`) has that value as its input. -/
theorem Acc.final_parsed (parse : String → Option Value) (k : Nat) (id name : String) (inp : Value) (j : String) (v : Value) (hj : j.isEmpty = false) (hp : parse j = some v) (hv : v ≠ .null) :
    Acc.final parse ⟨k, .toolUse id name inp, j⟩ = some (.toolUse id name v) := by
  cases v <;> simp_all [Acc.final]

/-- A call whose pieces do not parse makes the reply not complete (`final` is none), and the partial reply keeps the text received as a string value. -/
theorem Acc.final_unparsed (parse : String → Option Value) (k : Nat) (id name : String) (inp : Value) (j : String) (hj : j.isEmpty = false) (hp : parse j = none) :
    Acc.final parse ⟨k, .toolUse id name inp, j⟩ = none ∧ Acc.partial parse ⟨k, .toolUse id name inp, j⟩ = .toolUse id name (.str j) := by
  simp [Acc.final, Acc.partial, hj, hp]

/-- A call with no pieces keeps the input of its start. -/
theorem Acc.final_no_pieces (parse : String → Option Value) (k : Nat) (id name : String) (inp : Value) :
    Acc.final parse ⟨k, .toolUse id name inp, ""⟩ = some (.toolUse id name inp) := by
  simp [Acc.final]

end VbmLlm.Anthropic
