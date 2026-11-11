import VbmLlm.OpenAI.Stream
import VbmLlmProofs.OpenAI.Response
/-! # Proofs about the stream fold (`VbmLlm/OpenAI/Stream.lean`)

* **The merge rules** (`mergeCall_*`, `applyChoice_*`, `applyChunk_*`): the first `id`, `model` and call `id`/`name` win, `usage` is the last non-null, text and arguments concatenate in order, a fragment with
  no index is refused unless the policy reads it as 0.
* **Chunk boundaries do not matter** (`pieces_content`, `pieces_arguments`): a text or an arguments string split at any points folds to the same reply as the unsplit one.
* **The terminal rule**: a stream with no sentinel is never `complete` (`foldWith_no_done`), `complete` only ever comes from a sentinel that is the last event (`foldItems_complete`), an event after the
  sentinel is refused (`foldItems_after_done`), an error chunk stops the fold with the partial reply (`foldItems_error_chunk`). -/
namespace VbmLlm.OpenAI
open LeanJson

/-! ### Merge rules -/

theorem appendOpt_none_right (a : Option String) : appendOpt a none = a := by cases a <;> rfl
theorem appendOpt_none_left (b : Option String) : appendOpt none b = b := by cases b <;> rfl

theorem appendOpt_assoc_some (o : Option String) (p q : String) : appendOpt (appendOpt o (some p)) (some q) = appendOpt o (some (p ++ q)) := by
  cases o <;> simp [appendOpt, String.append_assoc]

theorem firstOpt_some (a : String) (b : Option String) : firstOpt (some a) b = some a := rfl
theorem firstOpt_none (b : Option String) : firstOpt none b = b := rfl

theorem mergeCall_arguments (c : CallAcc) (d : ToolCallDelta) : (mergeCall c d).arguments = c.arguments ++ d.arguments.getD "" := rfl
/-- The first `id` wins. -/
theorem mergeCall_id_first (c : CallAcc) (d : ToolCallDelta) : (mergeCall c d).id = firstOpt c.id d.id := rfl
/-- The first `name` wins (it is not concatenated). -/
theorem mergeCall_name_first (c : CallAcc) (d : ToolCallDelta) : (mergeCall c d).name = firstOpt c.name d.name := rfl
theorem mergeCall_id_kept (c : CallAcc) (d : ToolCallDelta) (i : String) (h : c.id = some i) : (mergeCall c d).id = some i := by simp [mergeCall, h, firstOpt]
theorem mergeCall_name_kept (c : CallAcc) (d : ToolCallDelta) (n : String) (h : c.name = some n) : (mergeCall c d).name = some n := by simp [mergeCall, h, firstOpt]

/-- A fragment with no `index` is refused by default: the schema requires it. -/
theorem applyCalls_missing_index_refused (calls : List CallAcc) (d : ToolCallDelta) (ds : List ToolCallDelta) (hi : d.index = none) :
    applyCalls {} calls (d :: ds) = none := by
  simp [applyCalls, hi]

/-- ... and is read as index 0 when the policy says so. -/
theorem applyCalls_missing_index_zero (calls : List CallAcc) (d : ToolCallDelta) (hi : d.index = none) :
    applyCalls ⟨true⟩ calls [d] = some (applyCall calls d 0) := by
  simp [applyCalls, hi]

theorem applyChoice_content (pol : Policy) (a a' : ChoiceAcc) (c : ChunkChoice) (h : applyChoice pol a c = some a') :
    a'.content = appendOpt a.content c.delta.content := by
  unfold applyChoice at h; split at h <;> simp_all
  rename_i calls _; rw [← h]

theorem applyChoice_refusal (pol : Policy) (a a' : ChoiceAcc) (c : ChunkChoice) (h : applyChoice pol a c = some a') :
    a'.refusal = appendOpt a.refusal c.delta.refusal := by
  unfold applyChoice at h; split at h <;> simp_all
  rename_i calls _; rw [← h]

/-- The reasoning text concatenates in order, as the content does. -/
theorem applyChoice_reasoning (pol : Policy) (a a' : ChoiceAcc) (c : ChunkChoice) (h : applyChoice pol a c = some a') :
    a'.reasoning = appendOpt a.reasoning c.delta.reasoning := by
  unfold applyChoice at h; split at h <;> simp_all
  rename_i calls _; rw [← h]

/-- The last `finish_reason` seen wins; a chunk with none leaves it. -/
theorem applyChoice_finish (pol : Policy) (a a' : ChoiceAcc) (c : ChunkChoice) (h : applyChoice pol a c = some a') :
    a'.finish = (match c.finishReason with | some f => some f | none => a.finish) := by
  unfold applyChoice at h; split at h <;> simp_all
  rename_i calls _; rw [← h]; rfl

theorem applyChunk_id (pol : Policy) (s s' : State) (c : Chunk) (h : applyChunk pol s c = some s') : s'.id = firstOpt s.id c.id := by
  unfold applyChunk at h; split at h <;> simp_all
  rename_i cs _; rw [← h]

theorem applyChunk_model (pol : Policy) (s s' : State) (c : Chunk) (h : applyChunk pol s c = some s') : s'.model = firstOpt s.model c.model := by
  unfold applyChunk at h; split at h <;> simp_all
  rename_i cs _; rw [← h]

theorem applyChunk_provider (pol : Policy) (s s' : State) (c : Chunk) (h : applyChunk pol s c = some s') : s'.provider = firstOpt s.provider c.provider := by
  unfold applyChunk at h; split at h <;> simp_all
  rename_i cs _; rw [← h]

/-- The last non-null `usage` wins. -/
theorem applyChunk_usage (pol : Policy) (s s' : State) (c : Chunk) (h : applyChunk pol s c = some s') :
    s'.usage = (match c.usage with | some u => some u | none => s.usage) := by
  unfold applyChunk at h; split at h <;> simp_all
  rename_i cs _; rw [← h]; rfl

/-! ### Chunk boundaries do not matter -/

/-- The text of a list of pieces, in order. -/
def joinAll : List String → String
  | [] => ""
  | p :: ps => p ++ joinAll ps

/-- Fold the pieces of a text into an optional text, one chunk at a time. -/
def foldPieces (o : Option String) : List String → Option String
  | [] => o
  | p :: ps => foldPieces (appendOpt o (some p)) ps

theorem foldPieces_eq (o : Option String) (ps : List String) (hne : ps ≠ []) : foldPieces o ps = appendOpt o (some (joinAll ps)) := by
  induction ps generalizing o with
  | nil => exact absurd rfl hne
  | cons p ps ih =>
    cases ps with
    | nil => simp [foldPieces, joinAll]
    | cons q qs =>
      have := ih (appendOpt o (some p)) (by simp)
      rw [foldPieces, this, appendOpt_assoc_some]
      simp [joinAll]

/-- A text split at any points, folded piece by piece, is the same text as the unsplit one (and no piece at all leaves it as it was). -/
theorem pieces_content (a : String) (ps : List String) (hne : ps ≠ []) :
    foldPieces (some a) ps = some (a ++ joinAll ps) := by
  rw [foldPieces_eq _ _ hne]; simp [appendOpt]

/-- The same for the arguments of a tool call: any split of the text folds to the same arguments. -/
def foldArgs (c : CallAcc) : List String → CallAcc
  | [] => c
  | p :: ps => foldArgs (mergeCall c ⟨none, none, none, some p⟩) ps

theorem foldArgs_arguments (c : CallAcc) (ps : List String) : (foldArgs c ps).arguments = c.arguments ++ joinAll ps := by
  induction ps generalizing c with
  | nil => simp [foldArgs, joinAll]
  | cons p ps ih => simp [foldArgs, ih, mergeCall, joinAll, String.append_assoc]

theorem foldArgs_id (c : CallAcc) (ps : List String) : (foldArgs c ps).id = c.id := by
  induction ps generalizing c with
  | nil => rfl
  | cons p ps ih => simp [foldArgs, ih, mergeCall, firstOpt]; cases c.id <;> rfl

theorem foldArgs_name (c : CallAcc) (ps : List String) : (foldArgs c ps).name = c.name := by
  induction ps generalizing c with
  | nil => rfl
  | cons p ps ih => simp [foldArgs, ih, mergeCall, firstOpt]; cases c.name <;> rfl

/-! ### The terminal rule -/

/-- **A stream with no sentinel is never complete**: if no element decodes to the sentinel, the fold is `truncated`, an `errorChunk` or a fault, never `complete`. -/
theorem foldWith_no_done {α : Type} (pol : Policy) (dec : Nat → α → Except StreamFault Item) (l : List α) (i : Nat) (s : State) (r : Response)
    (h : ∀ j x, x ∈ l → dec j x ≠ .ok .done) : foldWith pol dec l i s ≠ .ok (.complete r) := by
  induction l generalizing i s with
  | nil => simp [foldWith]
  | cons x rest ih =>
    intro hc
    have hx := h i x (by simp)
    unfold foldWith at hc
    cases hd : dec i x with
    | error f => simp [hd] at hc
    | ok it =>
      cases it with
      | skip => simp [hd] at hc; exact ih (i + 1) s (fun j y hy => h j y (by simp [hy])) hc
      | done => exact hx hd
      | chunk c =>
        simp only [hd] at hc
        cases hs : applyChunk pol s c with
        | none => simp [hs] at hc
        | some s' =>
          simp only [hs] at hc
          cases he : c.error with
          | some e => simp [he] at hc
          | none => simp [he] at hc; exact ih (i + 1) s' (fun j y hy => h j y (by simp [hy])) hc

/-- **`complete` comes only from a sentinel that is the last event.** -/
theorem foldItems_complete (pol : Policy) (items : List Item) (r : Response) (h : foldItems pol items = .ok (.complete r)) : ∃ pre, items = pre ++ [.done] := by
  have gen : ∀ (l : List Item) (i : Nat) (s : State), foldWith pol (fun _ x => .ok x) l i s = .ok (.complete r) → ∃ pre, l = pre ++ [.done] := by
    intro l
    induction l with
    | nil => intro i s hc; simp [foldWith] at hc
    | cons x rest ih =>
      intro i s hc
      cases x with
      | skip => simp [foldWith] at hc; obtain ⟨pre, hp⟩ := ih (i + 1) s hc; exact ⟨.skip :: pre, by simp [hp]⟩
      | done =>
        simp only [foldWith] at hc
        by_cases hr : rest.isEmpty = true
        · have : rest = [] := by simpa using hr
          exact ⟨[], by simp [this]⟩
        · simp [hr] at hc
      | chunk c =>
        simp only [foldWith] at hc
        cases hs : applyChunk pol s c with
        | none => simp [hs] at hc
        | some s' =>
          simp only [hs] at hc
          cases he : c.error with
          | some e => simp [he] at hc
          | none => simp [he] at hc; obtain ⟨pre, hp⟩ := ih (i + 1) s' hc; exact ⟨.chunk c :: pre, by simp [hp]⟩
  exact gen items 0 State.empty h

/-- **A complete reply always has a choice** (so it is a value the single-shot decode could have produced). -/
theorem foldWith_complete_choices {α : Type} (pol : Policy) (dec : Nat → α → Except StreamFault Item) (l : List α) (i : Nat) (s : State) (r : Response)
    (h : foldWith pol dec l i s = .ok (.complete r)) : r.choices ≠ [] := by
  induction l generalizing i s with
  | nil => simp [foldWith] at h
  | cons x rest ih =>
    unfold foldWith at h
    cases hd : dec i x with
    | error f => simp [hd] at h
    | ok it =>
      cases it with
      | skip => simp [hd] at h; exact ih (i + 1) s h
      | done =>
        simp only [hd] at h
        by_cases hr : rest.isEmpty = true
        · by_cases hc : s.choices.isEmpty = true
          · simp [hr, hc] at h
          · by_cases hk : s.complete? = true
            · simp [hr, hc, hk] at h
              subst h
              intro hne
              apply hc
              have : s.choices = [] := by simpa [State.soFar] using hne
              simp [this]
            · simp [hr, hc, hk] at h
        · simp [hr] at h
      | chunk c =>
        simp only [hd] at h
        cases hs : applyChunk pol s c with
        | none => simp [hs] at h
        | some s' =>
          simp only [hs] at h
          cases he : c.error with
          | some e => simp [he] at h
          | none => simp [he] at h; exact ih (i + 1) s' h

/-- An event after the sentinel is refused. -/
theorem foldItems_after_done (pol : Policy) (y : Item) (ys : List Item) : foldItems pol (.done :: y :: ys) = .error (.afterDone 1) := by
  simp [foldItems, foldWith]

/-- An error chunk stops the fold, whatever follows it, and carries the partial reply. -/
theorem foldItems_error_chunk (pol : Policy) (c : Chunk) (e : ChunkError) (rest : List Item) (s' : State)
    (he : c.error = some e) (hs : applyChunk pol State.empty c = some s') :
    foldItems pol (.chunk c :: rest) = .ok (.errorChunk e.message s'.soFar) := by
  simp [foldItems, foldWith, hs, he]

/-- A chunk whose choice or fragment has no index (and the policy refuses it) is a fault naming the chunk. -/
theorem foldItems_missing_index (pol : Policy) (c : Chunk) (rest : List Item) (hs : applyChunk pol State.empty c = none) :
    foldItems pol (.chunk c :: rest) = .error (.missingIndex 0) := by
  simp [foldItems, foldWith, hs]

/-- No events: truncated, with nothing received. -/
theorem foldItems_nil (pol : Policy) : foldItems pol [] = .ok (.truncated State.empty.soFar) := rfl

/-! ### The reported cost through the fold -/

/-- A chunk with one choice, finishing: the stream of the theorem below. -/
def chunkChoice : Chunk := ⟨some "g", none, [⟨some 0, emptyDelta, some "stop"⟩], none, none, none⟩

/-- The final usage frame of a stream whose provider reported a cost (`1.68e-05`), and no choice. -/
def chunkCost : Chunk := ⟨some "g", none, [], some ⟨none, none, none, none, none, some costLexeme⟩, none, none⟩

/-- The final usage frame of a stream whose provider reported no cost, and no choice. -/
def chunkNoCost : Chunk := ⟨some "g", none, [], some ⟨none, none, none, none, none, none⟩, none, none⟩

/-- (d) **The fold of a stream whose final usage frame carries a cost yields that cost** as the usage of the reply, exactly as the counts reach it. -/
theorem foldItems_cost :
    foldItems {} [.chunk chunkChoice, .chunk chunkCost, .done] =
      .ok (.complete ⟨some "g", none, [⟨some 0, ⟨none, none, [], none⟩, some "stop"⟩], some ⟨none, none, none, none, none, some costLexeme⟩, none⟩) := rfl

/-- (d) **The fold of a stream whose final usage frame carries no cost yields `cost = none`**, the counts as they are. -/
theorem foldItems_no_cost :
    foldItems {} [.chunk chunkChoice, .chunk chunkNoCost, .done] =
      .ok (.complete ⟨some "g", none, [⟨some 0, ⟨none, none, [], none⟩, some "stop"⟩], some ⟨none, none, none, none, none, none⟩, none⟩) := rfl

/-! ### Reading a chunk -/

/-- A fragment of another type than `function` is refused, as a whole tool call is. -/
theorem decodeToolCallDelta_other_type_refused (v : Value) (t : String) (h : get v "type" = .str t) (ht : t ≠ "function") (d : ToolCallDelta) : decodeToolCallDelta v ≠ .ok d := by
  intro hc
  cases v with
  | obj ms =>
    unfold decodeToolCallDelta at hc
    rw [bind_ok_iff] at hc
    obtain ⟨a, ha, _⟩ := hc
    rw [checkType_ok_iff'] at ha
    rcases ha with ha | ha <;> rw [h] at ha <;> simp at ha; exact ht ha
  | _ => simp [decodeToolCallDelta] at hc

/-- A `tool_calls` that is neither absent, null nor an array is refused. -/
theorem decodeDelta_tool_calls_wrong (d : Value) (h : ∀ xs, get d "tool_calls" ≠ .arr xs) (h' : get d "tool_calls" ≠ .null) (r : Delta) : decodeDelta d ≠ .ok r := by
  intro hc
  unfold decodeDelta at hc
  rw [bind_ok_iff] at hc; obtain ⟨_, _, hc⟩ := hc
  rw [bind_ok_iff] at hc; obtain ⟨_, _, hc⟩ := hc
  rw [bind_ok_iff] at hc; obtain ⟨_, _, hc⟩ := hc
  cases hg : get d "tool_calls" with
  | null => exact h' hg
  | arr xs => exact h xs hg
  | _ => simp [hg] at hc

/-- A `delta` that is neither absent, null nor an object is refused. -/
theorem decodeChunkChoice_delta_wrong (c : Value) (h : ∀ ms, get c "delta" ≠ .obj ms) (h' : get c "delta" ≠ .null) (r : ChunkChoice) : decodeChunkChoice c ≠ .ok r := by
  intro hc
  cases c with
  | obj cms =>
    unfold decodeChunkChoice at hc
    rw [bind_ok_iff] at hc; obtain ⟨_, _, hc⟩ := hc
    rw [bind_ok_iff] at hc; obtain ⟨_, _, hc⟩ := hc
    cases hg : get (.obj cms) "delta" with
    | null => exact h' hg
    | obj ms => exact h ms hg
    | _ => simp [hg] at hc
  | _ => simp [decodeChunkChoice] at hc

/-- An absent `delta` reads as an empty one. -/
theorem decodeChunkChoice_no_delta (cms : List (String × Value)) (index : Option Nat) (fin : Option String)
    (hi : optNat (.obj cms) "index" = .ok index) (hf : optStr (.obj cms) "finish_reason" = .ok fin) (hd : get (.obj cms) "delta" = .null) :
    decodeChunkChoice (.obj cms) = .ok ⟨index, emptyDelta, fin⟩ := by
  simp [decodeChunkChoice, bind, Except.bind, hi, hf, hd, pure, Except.pure]

/-! ### Events -/

/-- The sentinel. -/
theorem decodeItem_done (parse : String → Option Value) (i : Nat) (e : Event) (h : e.data = "[DONE]") : decodeItem parse i e = .ok .done := by
  simp [decodeItem, h]

/-- An event with empty data is ignored. -/
theorem decodeItem_empty (parse : String → Option Value) (i : Nat) (e : Event) (h : e.data = "") : decodeItem parse i e = .ok .skip := by
  simp [decodeItem, h]

/-- An event with a type the convention does not use is refused. -/
theorem decodeItem_event_type (parse : String → Option Value) (i : Nat) (e : Event) (h1 : e.data ≠ "[DONE]") (h2 : e.data ≠ "") (h3 : e.type ≠ "") (h4 : e.type ≠ "message") :
    decodeItem parse i e = .error (.eventType i e.type) := by
  simp [decodeItem, h1, h2, h3, h4]

theorem decodeChunk_not_object (v : Value) (h : ∀ ms, v ≠ .obj ms) (c : Chunk) : decodeChunk v ≠ .ok c := by
  intro hc; cases v with
  | obj ms => exact h ms rfl
  | _ => simp [decodeChunk] at hc

/-- A chunk carries an error exactly when its `error` member is present and not null. -/
theorem errorOf_null (v : Value) (h : get v "error" = .null) : errorOf v = none := by simp [errorOf, h]

theorem errorOf_string (v : Value) (s : String) (h : get v "error" = .str s) : errorOf v = some ⟨some s⟩ := by simp [errorOf, h]

theorem errorOf_present (v : Value) (h : get v "error" ≠ .null) : (errorOf v).isSome = true := by
  unfold errorOf; cases hh : get v "error" <;> simp_all

end VbmLlm.OpenAI
