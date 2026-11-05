import VbmLlm.OpenAI.Turn
/-! # Proofs about the tool-call turn machine (`VbmLlm/Turn.lean`, `VbmLlm/OpenAI/Turn.lean`)

* **What is decided** (`pair_orphan`, `pair_unanswered`, `pair_answered`, `pair_newest_wins`, `pair_orphan_after_assistant`): an unanswered call stays in its turn with no answer, a result directly after its call answers it
  (the newest recorded wins), a result whose call is not open in front of it is an orphan.
* **Nothing is lost or reordered** (`pair_calls`, `pair_texts`): the turns come out in the order they went in, each with all its calls in order; the text keeps its order.
* **Prefix stability** (`pair_prefix_stable`, `render_prefix_stable`): extending a conversation by an assistant item leaves everything rendered before as it was, whatever the earlier items were.
* **Every call answered exactly once** (`render_paired`): what OpenAI's shape shows is well paired, whatever was recorded: an assistant message is followed by one `tool` message per call, in call order, with the call's
  id, and there is no other `tool` message. -/
namespace VbmLlm
open OpenAI

/-! ### What the machine decides -/

theorem pair_nil : pair [] = [] := rfl

/-- A result with no turn open in front of it is an orphan: kept as a segment of its own. -/
theorem pair_orphan (i c : String) : pair [.result i c] = [.orphan i c] := rfl

/-- A turn nobody answered stays a turn, every call with no answer. -/
theorem pair_unanswered (c : Option String) (cs : List ToolCall) : pair [.turn c cs] = [.turn c (cs.map fun k => (k, none))] := by
  simp [pair, pairFrom, feed, closeOpt, Open.close]

/-- A result directly after its call is the call's answer. -/
theorem pair_answered (c : Option String) (k : ToolCall) (a : String) : pair [.turn c [k], .result k.id a] = [.turn c [(k, some a)]] := by
  simp [pair, pairFrom, feed, closeOpt, Open.close]

/-- Of two results for one call, the newest wins. -/
theorem pair_newest_wins (c : Option String) (k : ToolCall) (a b : String) : pair [.turn c [k], .result k.id a, .result k.id b] = [.turn c [(k, some b)]] := by
  simp [pair, pairFrom, feed, closeOpt, Open.close]

/-- A result that comes after the next assistant item no longer belongs to the turn before it: it is an orphan, never an answer. -/
theorem pair_orphan_after_assistant (c : Option String) (cs : List ToolCall) (x i a : String) :
    pair [.turn c cs, .text .assistant x, .result i a] = [.turn c (cs.map fun k => (k, none)), .text .assistant x, .orphan i a] := by
  simp [pair, pairFrom, feed, closeOpt, Open.close]

/-! ### Nothing is lost or reordered -/

def Seg.calls : Seg → Option (Option String × List ToolCall)
  | .turn c answers => some (c, answers.map (·.1))
  | _ => none

def Entry.calls : Entry → Option (Option String × List ToolCall)
  | .turn c cs => some (c, cs)
  | _ => none

def Seg.textOf : Seg → Option (Role × String)
  | .text r c => some (r, c)
  | _ => none

def Entry.textOf : Entry → Option (Role × String)
  | .text r c => some (r, c)
  | _ => none

/-- The window holds no turn: only text and orphans. -/
def Open.Sound (o : Open) : Prop := ∀ x ∈ o.kept, x.calls = none

theorem feed_sound (s : Option Open) (hs : ∀ o, s = some o → o.Sound) (it : Entry) : ∀ o, (feed s it).2 = some o → o.Sound := by
  intro o ho
  cases it with
  | turn c cs => simp [feed] at ho; subst ho; simp [Open.Sound]
  | text r c =>
    cases s with
    | none => simp [feed] at ho
    | some o0 =>
      by_cases hr : r = .assistant <;> simp [feed, hr] at ho
      subst ho; intro x hx; rcases List.mem_cons.1 hx with rfl | h
      · rfl
      · exact hs o0 rfl x h
  | result i c =>
    cases s with
    | none => simp [feed] at ho
    | some o0 =>
      by_cases hr : o0.calls.any (·.id == i) = true <;> simp [feed, hr] at ho
      · subst ho; exact hs o0 rfl
      · subst ho; intro x hx; rcases List.mem_cons.1 hx with rfl | h
        · rfl
        · exact hs o0 rfl x h

theorem close_calls (o : Open) (h : o.Sound) : o.close.filterMap Seg.calls = [(o.content, o.calls)] := by
  have : o.kept.reverse.filterMap Seg.calls = [] := by
    rw [List.filterMap_eq_nil_iff]; intro x hx; exact h x (List.mem_reverse.1 hx)
  simp [Open.close, Seg.calls, this, Function.comp_def]

/-- **The turns come out as they went in**, in order, each with all its calls in order (the answers are the machine's to decide, the calls are not). -/
theorem pairFrom_calls : ∀ (items : List Entry) (s : Option Open), (∀ o, s = some o → o.Sound) →
    (pairFrom s items).filterMap Seg.calls = (s.map fun o => (o.content, o.calls)).toList ++ items.filterMap Entry.calls
  | [], s, hs => by
    cases s with
    | none => simp [pairFrom, closeOpt]
    | some o => simp [pairFrom, closeOpt, close_calls o (hs o rfl)]
  | it :: rest, s, hs => by
    have ih := pairFrom_calls rest (feed s it).2 (feed_sound s hs it)
    rw [pairFrom, List.filterMap_append, ih]
    cases it with
    | turn c cs =>
      cases s with
      | none => simp [feed, closeOpt, Entry.calls]
      | some o => simp [feed, closeOpt, close_calls o (hs o rfl), Entry.calls]
    | text r c =>
      cases s with
      | none => simp [feed, Seg.calls, Entry.calls, List.filterMap_cons]
      | some o => by_cases hr : r = .assistant <;> simp [feed, hr, close_calls o (hs o rfl), Seg.calls, Entry.calls, List.filterMap_cons]
    | result i c =>
      cases s with
      | none => simp [feed, Seg.calls, Entry.calls, List.filterMap_cons]
      | some o => by_cases hr : o.calls.any (·.id == i) = true <;> simp [feed, hr, Entry.calls, List.filterMap_cons]

theorem pair_calls (items : List Entry) : (pair items).filterMap Seg.calls = items.filterMap Entry.calls := by
  simpa [pair] using pairFrom_calls items none (by simp)

def Open.texts (o : Open) : List (Role × String) := o.kept.reverse.filterMap Seg.textOf

theorem close_texts (o : Open) : o.close.filterMap Seg.textOf = o.texts := by
  simp [Open.close, Open.texts, List.filterMap_cons, Seg.textOf]

/-- **No text is dropped or reordered** (an orphan is not text; a result consumed as an answer is not either). -/
theorem pairFrom_texts : ∀ (items : List Entry) (s : Option Open),
    (pairFrom s items).filterMap Seg.textOf = (s.map Open.texts).getD [] ++ items.filterMap Entry.textOf
  | [], s => by
    cases s with
    | none => simp [pairFrom, closeOpt]
    | some o => simp [pairFrom, closeOpt, close_texts]
  | it :: rest, s => by
    have ih := pairFrom_texts rest (feed s it).2
    rw [pairFrom, List.filterMap_append, ih]
    cases it with
    | turn c cs =>
      cases s with
      | none => simp [feed, closeOpt, Open.texts, Entry.textOf, List.filterMap_cons]
      | some o => simp [feed, closeOpt, close_texts, Open.texts, Entry.textOf, List.filterMap_cons]
    | text r c =>
      cases s with
      | none => simp [feed, Seg.textOf, Entry.textOf]
      | some o => by_cases hr : r = .assistant <;> simp [feed, hr, close_texts, Seg.textOf, Entry.textOf, Open.texts]
    | result i c =>
      cases s with
      | none => simp [feed, Seg.textOf, Entry.textOf, List.filterMap_cons]
      | some o => by_cases hr : o.calls.any (·.id == i) = true <;> simp [feed, hr, Entry.textOf, Open.texts, Seg.textOf, List.filterMap_cons]

theorem pair_texts (items : List Entry) : (pair items).filterMap Seg.textOf = items.filterMap Entry.textOf := by
  simpa [pair] using pairFrom_texts items none

/-! ### Prefix stability -/

/-- An item that ends every open turn. -/
def Entry.IsAssistant : Entry → Prop
  | .turn .. => True
  | .text r _ => r = .assistant
  | .result .. => False

theorem pairFrom_append_assistant (a : Entry) (ha : a.IsAssistant) (cs : List Entry) :
    ∀ (xs : List Entry) (s : Option Open), pairFrom s (xs ++ a :: cs) = pairFrom s xs ++ pairFrom none (a :: cs)
  | [], s => by
    cases a with
    | turn c k => cases s <;> simp [pairFrom, feed, closeOpt]
    | text r c =>
      simp only [Entry.IsAssistant] at ha; subst ha
      cases s <;> simp [pairFrom, feed, closeOpt]
    | result i c => exact absurd ha id
  | x :: xs, s => by
    have e1 : pairFrom s (x :: (xs ++ a :: cs)) = (feed s x).1 ++ pairFrom (feed s x).2 (xs ++ a :: cs) := rfl
    have e2 : pairFrom s (x :: xs) = (feed s x).1 ++ pairFrom (feed s x).2 xs := rfl
    rw [List.cons_append, e1, e2, pairFrom_append_assistant a ha cs xs (feed s x).2, List.append_assoc]

/-- **A reply never changes what came before it**: extending a conversation by an assistant item (the model's reply) leaves the segments decided so far as they were, whatever the earlier items were. -/
theorem pair_prefix_stable (xs : List Entry) (a : Entry) (ha : a.IsAssistant) (cs : List Entry) : pair xs <+: pair (xs ++ a :: cs) := by
  show pairFrom none xs <+: pairFrom none (xs ++ a :: cs)
  rw [pairFrom_append_assistant a ha cs xs none]
  exact List.prefix_append _ _

end VbmLlm
namespace VbmLlm.OpenAI
open VbmLlm

/-! ### OpenAI's shape: every call answered exactly once -/

/-- A message that is not part of a tool exchange. -/
def RequestMessage.IsPlain : RequestMessage → Prop
  | .system _ | .developer _ | .user _ => True
  | _ => False

/-- A well-paired message list: plain messages anywhere; an assistant message followed directly by one `tool` message per call, in call order, each carrying its call's id. No other `tool` message exists. -/
inductive Paired : List RequestMessage → Prop
  | nil : Paired []
  | plain (m : RequestMessage) (h : m.IsPlain) (rest : List RequestMessage) : Paired rest → Paired (m :: rest)
  | turn (content : Option String) (answers : List (ToolCall × String)) (rest : List RequestMessage) :
      Paired rest → Paired (.assistant content (answers.map (·.1)) :: answers.map (fun a => .tool a.1.id a.2) ++ rest)

theorem seg_render_paired (p : RenderPolicy) (g : Seg) (rest : List RequestMessage) (h : Paired rest) : Paired (g.render p ++ rest) := by
  cases g with
  | text r c =>
    cases r with
    | system => exact .plain (.system c) trivial _ h
    | developer => exact .plain (.developer c) trivial _ h
    | user => exact .plain (.user c) trivial _ h
    | assistant => simpa [Seg.render, Role.message] using Paired.turn (some c) [] rest h
  | orphan i c => exact .plain (.user (p.orphan c)) trivial _ h
  | turn c answers =>
    have := Paired.turn c (answers.map fun a => (a.1, a.2.getD p.placeholder)) rest h
    simpa [Seg.render, Function.comp_def] using this

theorem flatMap_render_paired (p : RenderPolicy) : ∀ segs : List Seg, Paired (segs.flatMap (Seg.render p))
  | [] => .nil
  | g :: gs => by simpa using seg_render_paired p g _ (flatMap_render_paired p gs)

/-- **Every call is answered exactly once, directly after it.** Whatever was recorded, what `render` shows is well paired. -/
theorem render_paired (p : RenderPolicy) (items : List Entry) : Paired (render p items) := flatMap_render_paired p _

/-- **Cache coherence of rendering**: the messages of a conversation are a prefix of the messages of the conversation extended by the model's reply. -/
theorem render_prefix_stable (p : RenderPolicy) (xs : List Entry) (a : Entry) (ha : a.IsAssistant) (cs : List Entry) : render p xs <+: render p (xs ++ a :: cs) := by
  obtain ⟨t, ht⟩ := pair_prefix_stable xs a ha cs
  refine ⟨t.flatMap (Seg.render p), ?_⟩
  simp only [render, ← ht, List.flatMap_append]

/-- A result with no turn in front of it is shown as plain text, never as a `tool` message. -/
theorem render_orphan (p : RenderPolicy) (i c : String) : render p [.result i c] = [.user (p.orphan c)] := rfl

/-- A call nobody answered is shown with the placeholder. -/
theorem render_unanswered (p : RenderPolicy) (c : Option String) (cs : List ToolCall) :
    render p [.turn c cs] = .assistant c cs :: cs.map (fun k => .tool k.id p.placeholder) := by
  simp [render, pair_unanswered, Seg.render, Function.comp_def]

/-- A result right after its call is that call's `tool` message. -/
theorem render_answered (p : RenderPolicy) (c : Option String) (k : ToolCall) (a : String) :
    render p [.turn c [k], .result k.id a] = [.assistant c [k], .tool k.id a] := by
  simp [render, pair_answered, Seg.render]

end VbmLlm.OpenAI
