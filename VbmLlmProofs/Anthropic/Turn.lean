import VbmLlm.Anthropic.Turn
import VbmLlmProofs.Turn
/-! # Proofs about the turn machine in Anthropic's shape (`VbmLlm/Anthropic/Turn.lean`)

* **Every call is answered exactly once, directly after it** (`render_paired`): an assistant message with calls is followed directly by a user message whose first blocks are the results of exactly those calls,
  in call order, each with its call's id, and no other result block exists. Whatever was recorded, what `render` shows is well paired.
* **A reply never changes what came before it** (`render_prefix_stable`): the messages of a conversation are a prefix of the messages of the conversation extended by the model's reply (the cache stays valid).
* The window's user text joins the results message, after them (`render_window_text_joins`); an orphan result is plain text (`render_orphan`); an unanswered call gets the placeholder (`render_unanswered`). -/
namespace VbmLlm.Anthropic
open LeanJson VbmLlm

def isResult : ReqBlock → Bool
  | .toolResult .. => true
  | _ => false

/-- The message holds no result block. -/
def NoResult (m : Message) : Prop := ∀ b ∈ m.content, isResult b = false

/-- The ids of the calls an assistant message makes, in order (a user message makes none). -/
def callIds (m : Message) : List String :=
  match m.role with
  | .assistant => m.content.filterMap fun b => match b with | .toolUse i _ _ => some i | _ => none
  | .user => []

/-- The ids of the leading result blocks, and what follows them. -/
def leadResults : List ReqBlock → List String × List ReqBlock
  | .toolResult i _ _ :: bs => ((leadResults bs).1.cons i, (leadResults bs).2)
  | bs => ([], bs)

/-- The message is a user message that answers exactly `exp`: its first blocks are their results in that order and no other block is a result. -/
def Answers (exp : List String) (m : Message) : Prop :=
  m.role = .user ∧ (leadResults m.content).1 = exp ∧ ∀ b ∈ (leadResults m.content).2, isResult b = false

/-- What the next message must be, given the calls waiting for an answer. -/
def Ok : List String → List Message → Prop
  | exp, [] => exp = []
  | [], m :: rest => NoResult m ∧ Ok (callIds m) rest
  | e :: es, m :: rest => Answers (e :: es) m ∧ Ok [] rest

/-- **Well paired**: plain messages anywhere; an assistant message with calls followed directly by the user message that answers them, in order; no other result block. -/
def Paired (ms : List Message) : Prop := Ok [] ms

theorem leadResults_noresult : ∀ bs : List ReqBlock, (∀ b ∈ bs, isResult b = false) → leadResults bs = ([], bs)
  | [], _ => rfl
  | b :: bs, h => by
    cases b with
    | toolResult i c e => have := h _ List.mem_cons_self; simp [isResult] at this
    | text t => simp [leadResults]
    | toolUse i n inp => simp [leadResults]
    | thinking t sg => simp [leadResults]
    | redactedThinking d => simp [leadResults]

theorem leadResults_resultsOf (p : RenderPolicy) : ∀ (answers : List (OpenAI.ToolCall × Option String)) (ns : List ReqBlock), (∀ b ∈ ns, isResult b = false) →
    leadResults (resultsOf p answers ++ ns) = (answers.map (·.1.id), ns)
  | [], ns, h => by simpa [resultsOf] using leadResults_noresult ns h
  | a :: as, ns, h => by
    have := leadResults_resultsOf p as ns h
    simp only [resultsOf, List.map_cons, List.cons_append, leadResults] at this ⊢
    rw [this]

theorem callIds_asstOf (p : RenderPolicy) (c : Option String) (answers : List (OpenAI.ToolCall × Option String)) : callIds (asstOf p c answers) = answers.map (·.1.id) := by
  cases c <;> simp [callIds, asstOf, List.filterMap_map, Function.comp_def]

theorem noResult_asstOf (p : RenderPolicy) (c : Option String) (answers : List (OpenAI.ToolCall × Option String)) : NoResult (asstOf p c answers) := by
  intro b hb
  simp only [asstOf, List.mem_append, List.mem_map] at hb
  rcases hb with hb | ⟨a, _, rfl⟩
  · cases c with
    | none => simp at hb
    | some t => simp at hb; simp [hb, isResult]
  · rfl

theorem noResult_userText (s : String) : NoResult (userText s) := by
  intro b hb; simp [userText] at hb; simp [hb, isResult]

theorem callIds_userText (s : String) : callIds (userText s) = [] := rfl

theorem answers_of_lead (ids : List String) (cs ns : List ReqBlock) (hl : leadResults cs = (ids, ns)) (hn : ∀ b ∈ ns, isResult b = false) : Answers ids ⟨.user, cs⟩ :=
  ⟨rfl, by rw [hl], by rw [hl]; exact hn⟩

theorem joinUser_ok (p : RenderPolicy) (a : OpenAI.ToolCall × Option String) (as : List (OpenAI.ToolCall × Option String)) (R : List Message) (h : Ok [] R) :
    Ok ((a :: as).map (·.1.id)) (joinUser (resultsOf p (a :: as)) R) := by
  have hl0 : leadResults (resultsOf p (a :: as)) = ((a :: as).map (·.1.id), []) := by simpa using leadResults_resultsOf p (a :: as) [] (by simp)
  cases R with
  | nil => exact ⟨answers_of_lead _ _ _ hl0 (by simp), rfl⟩
  | cons n rest =>
    obtain ⟨hn, hrest⟩ := h
    by_cases hr : n.role = .user
    · have hl := leadResults_resultsOf p (a :: as) n.content hn
      have hc : callIds n = [] := by simp [callIds, hr]
      rw [hc] at hrest
      have : joinUser (resultsOf p (a :: as)) (n :: rest) = ⟨.user, resultsOf p (a :: as) ++ n.content⟩ :: rest := by simp [joinUser, hr]
      rw [this]
      exact ⟨answers_of_lead _ _ _ hl hn, hrest⟩
    · have : joinUser (resultsOf p (a :: as)) (n :: rest) = ⟨.user, resultsOf p (a :: as)⟩ :: n :: rest := by simp [joinUser, hr]
      rw [this]
      exact ⟨answers_of_lead _ _ _ hl0 (by simp), hn, hrest⟩

/-- Every message of a rendering that follows a segment's own messages is as the induction needs: the rendering of segments is well paired. -/
theorem ok_renderSegs (p : RenderPolicy) : ∀ segs : List Seg, Ok [] (renderSegs p segs)
  | [] => rfl
  | .text r c :: rest => by
    have ih := ok_renderSegs p rest
    cases r <;> simp only [renderSegs, Ok, callIds_userText] <;> first | exact ⟨noResult_userText c, ih⟩ | exact ⟨fun b hb => by simp at hb; subst hb; rfl, ih⟩
  | .orphan i c :: rest => by
    have ih := ok_renderSegs p rest
    simp only [renderSegs, Ok, callIds_userText]
    exact ⟨noResult_userText _, ih⟩
  | .turn c [] :: rest => by
    have ih := ok_renderSegs p rest
    simp only [renderSegs, Ok, callIds_asstOf, List.map_nil]
    exact ⟨noResult_asstOf p c [], ih⟩
  | .turn c (a :: as) :: rest => by
    have ih := ok_renderSegs p rest
    simp only [renderSegs, Ok, callIds_asstOf]
    exact ⟨noResult_asstOf p c _, joinUser_ok p a as _ ih⟩

/-- **Every call is answered exactly once, directly after it.** Whatever was recorded, what `render` shows is well paired. -/
theorem render_paired (p : RenderPolicy) (items : List Entry) : Paired (render p items) := ok_renderSegs p _

/-! ### A reply never changes what came before it -/

/-- A segment whose messages start with an assistant message. -/
def _root_.VbmLlm.Seg.AsstLed : Seg → Prop
  | .turn .. => True
  | .text r _ => r = .assistant
  | .orphan .. => False

/-- Segments that are empty or start with an assistant-led segment. -/
def LedBy : List Seg → Prop
  | [] => True
  | g :: _ => g.AsstLed

theorem renderSegs_ne_nil (p : RenderPolicy) (g : Seg) (rest : List Seg) : renderSegs p (g :: rest) ≠ [] := by
  cases g with
  | text r c => cases r <;> simp [renderSegs]
  | orphan i c => simp [renderSegs]
  | turn c as => cases as <;> simp [renderSegs, joinUser] <;> split <;> simp

theorem joinUser_asst (rs : List ReqBlock) (R : List Message) (h : ∀ n ∈ R.head?, n.role = .assistant) : joinUser rs R = ⟨.user, rs⟩ :: R := by
  cases R with
  | nil => rfl
  | cons n rest => simp [joinUser, h n (by simp)]

theorem renderSegs_head_asst (p : RenderPolicy) (r : List Seg) (h : LedBy r) : ∀ n ∈ (renderSegs p r).head?, n.role = .assistant := by
  intro n hn
  cases r with
  | nil => simp [renderSegs] at hn
  | cons g rest =>
    cases g with
    | text r c =>
      cases r with
      | assistant => simp [renderSegs] at hn; subst hn; rfl
      | system => exact absurd h (by simp [LedBy, Seg.AsstLed])
      | developer => exact absurd h (by simp [LedBy, Seg.AsstLed])
      | user => exact absurd h (by simp [LedBy, Seg.AsstLed])
    | orphan i c => exact absurd h id
    | turn c as => cases as <;> simp [renderSegs, joinUser, asstOf] at hn <;> subst hn <;> rfl

theorem joinUser_append (rs : List ReqBlock) (A B : List Message) (hA : A ≠ []) : joinUser rs (A ++ B) = joinUser rs A ++ B := by
  cases A with
  | nil => exact absurd rfl hA
  | cons n A' => by_cases hr : n.role = .user <;> simp [joinUser, hr]

/-- **Rendering distributes over an extension that starts with an assistant segment.** -/
theorem renderSegs_append (p : RenderPolicy) : ∀ (l r : List Seg), LedBy r → renderSegs p (l ++ r) = renderSegs p l ++ renderSegs p r
  | [], r, _ => by simp [renderSegs]
  | g :: l', r, h => by
    have ih := renderSegs_append p l' r h
    cases g with
    | text rl c => cases rl <;> simp [renderSegs, ih]
    | orphan i c => simp [renderSegs, ih]
    | turn c as =>
      cases as with
      | nil => simp [renderSegs, ih]
      | cons a as' =>
        simp only [List.cons_append, renderSegs, ih, List.cons.injEq, true_and]
        cases l' with
        | nil =>
          simp only [List.nil_append, renderSegs] at ih ⊢
          rw [joinUser_asst _ _ (renderSegs_head_asst p r h)]
          rfl
        | cons g' l'' => exact (joinUser_append _ _ _ (renderSegs_ne_nil p g' l''))

theorem ledBy_pairFrom_some : ∀ (cs : List Entry) (o : Open), LedBy (pairFrom (some o) cs)
  | [], o => by simp [pairFrom, closeOpt, Open.close, LedBy, Seg.AsstLed]
  | x :: cs, o => by
    cases x with
    | turn c k => simp [pairFrom, feed, closeOpt, Open.close, LedBy, Seg.AsstLed]
    | text r c =>
      by_cases hr : r = .assistant
      · subst hr; simp [pairFrom, feed, Open.close, LedBy, Seg.AsstLed]
      · simp only [pairFrom, feed, hr, ite_false, List.nil_append]; exact ledBy_pairFrom_some cs _
    | result i c =>
      simp only [pairFrom, feed]
      split <;> simp only [List.nil_append] <;> exact ledBy_pairFrom_some cs _

theorem ledBy_pairFrom_none (a : Entry) (ha : a.IsAssistant) (cs : List Entry) : LedBy (pairFrom none (a :: cs)) := by
  cases a with
  | turn c k => simp only [pairFrom, feed, closeOpt, List.nil_append]; exact ledBy_pairFrom_some cs _
  | text r c =>
    simp only [Entry.IsAssistant] at ha; subst ha
    simp [pairFrom, feed, LedBy, Seg.AsstLed]
  | result i c => exact absurd ha id

/-- **A reply never changes what came before it**: the messages of a conversation are a prefix of the messages of the conversation extended by the model's reply (the cache stays valid). -/
theorem render_prefix_stable (p : RenderPolicy) (xs : List Entry) (a : Entry) (ha : a.IsAssistant) (cs : List Entry) : render p xs <+: render p (xs ++ a :: cs) := by
  have h1 : pair (xs ++ a :: cs) = pair xs ++ pairFrom none (a :: cs) := pairFrom_append_assistant a ha cs xs none
  show renderSegs p (pair xs) <+: renderSegs p (pair (xs ++ a :: cs))
  rw [h1, renderSegs_append p _ _ (ledBy_pairFrom_none a ha cs)]
  exact List.prefix_append _ _

/-! ### What is shown -/

/-- A result with no turn in front of it is shown as plain user text, never as a `tool_result`. -/
theorem render_orphan (p : RenderPolicy) (i c : String) : render p [.result i c] = [userText (p.orphan c)] := by
  simp [render, pair_orphan, renderSegs]

/-- A call nobody answered is shown with the placeholder, in the results message. -/
theorem render_unanswered (p : RenderPolicy) (c : Option String) (k : OpenAI.ToolCall) :
    render p [.turn c [k]] = [asstOf p c [(k, none)], ⟨.user, [.toolResult k.id (some p.placeholder) none]⟩] := by
  simp [render, pair_unanswered, renderSegs, joinUser, resultsOf]

/-- A result right after its call is that call's `tool_result`, the first block of the user message after the turn. -/
theorem render_answered (p : RenderPolicy) (c : Option String) (k : OpenAI.ToolCall) (a : String) :
    render p [.turn c [k], .result k.id a] = [asstOf p c [(k, some a)], ⟨.user, [.toolResult k.id (some a) none]⟩] := by
  simp [render, pair_answered, renderSegs, joinUser, resultsOf]

/-- The user text of the turn's window follows the results, in the same message. -/
theorem render_window_text_joins (p : RenderPolicy) (c : Option String) (k : OpenAI.ToolCall) (a u : String) :
    render p [.turn c [k], .result k.id a, .text .user u] = [asstOf p c [(k, some a)], ⟨.user, [.toolResult k.id (some a) none, .text u]⟩] := by
  simp [render, pair, pairFrom, feed, closeOpt, Open.close, renderSegs, joinUser, resultsOf, userText]

end VbmLlm.Anthropic
