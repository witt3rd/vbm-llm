import VbmLlm.OpenAI.Chunk
import VbmLlm.Sse
/-! # OpenAI chat-completions: folding a stream into one reply

A stream of events folds to **exactly one outcome**; the outcome is never a silent guess:
* `complete`: the terminal event (the sentinel `data: [DONE]`) was seen and nothing followed it. The reply is the same type the single-shot decode gives (`Response`).
* `truncated`: the events ended with no terminal event. The partial reply is available **and typed as partial**: a truncated stream is never presented as a complete one (the stream the first consumer folds today
  accepts it silently).
* `errorChunk`: a chunk carried an `error` (OpenRouter's mid-stream error: HTTP 200, content already received, then an error). The fold stops there and hands over the message **and** the partial reply: whether to
  discard what was received is the consumer's decision, not the library's.

Merge rules (the contract, proved in `VbmLlmProofs/OpenAI/Stream.lean`): the first `id` and `model` seen win; the last non-null `usage` wins; a choice is keyed by its `index`, in order of first appearance;
`content` and `refusal` concatenate in order; a tool call is keyed by its `index` within its choice, the **first** `id` and `name` win and `arguments` concatenate in order; the last `finish_reason` wins.
A tool-call fragment with no `index` is a fault unless the policy reads it as 0 (`Policy.missingIndexIsZero`, off by default: the schema requires it). An event with a type other than the default, or one
that follows the sentinel, is a fault. An event with empty data is ignored. A completed tool call with no `id` or no `name` is a fault, and so is a sentinel that follows no choice at all: a `complete` reply always has a choice, as the single-shot decode requires. -/
namespace VbmLlm.OpenAI
open LeanJson

structure Policy where
  /-- read a tool-call fragment or a choice with no `index` as 0 instead of refusing it -/
  missingIndexIsZero : Bool := false
  deriving DecidableEq, Repr

structure CallAcc where
  index : Nat
  id : Option String
  name : Option String
  arguments : String
  deriving DecidableEq, Repr

structure ChoiceAcc where
  index : Nat
  content : Option String
  refusal : Option String
  calls : List CallAcc
  finish : Option String
  deriving DecidableEq, Repr

structure State where
  id : Option String
  model : Option String
  choices : List ChoiceAcc
  usage : Option Usage
  deriving DecidableEq, Repr

def State.empty : State := ⟨none, none, [], none⟩

/-- Append a piece to an optional text (`none` + piece = the piece). -/
def appendOpt (a : Option String) (b : Option String) : Option String :=
  match a, b with
  | _, none => a
  | none, some y => some y
  | some x, some y => some (x ++ y)

/-- The first `some` wins. -/
def firstOpt (a b : Option String) : Option String :=
  match a with
  | none => b
  | some _ => a

/-- Update the member of an association list whose key is `i` (adding it, built by `mk`, at the end if absent). -/
def upd {α : Type} (key : α → Nat) (xs : List α) (i : Nat) (mk : α) (f : α → α) : List α :=
  match xs with
  | [] => [f mk]
  | a :: rest => if key a == i then f a :: rest else a :: upd key rest i mk f

def mergeCall (c : CallAcc) (d : ToolCallDelta) : CallAcc :=
  { c with id := firstOpt c.id d.id, name := firstOpt c.name d.name, arguments := c.arguments ++ d.arguments.getD "" }

def newCall (i : Nat) : CallAcc := ⟨i, none, none, ""⟩
def newChoice (i : Nat) : ChoiceAcc := ⟨i, none, none, [], none⟩

/-- Apply the tool-call fragments of a delta, one at a time, in order. A fragment with no index is `none`: the caller decides. -/
def applyCall (calls : List CallAcc) (d : ToolCallDelta) (i : Nat) : List CallAcc :=
  upd CallAcc.index calls i (newCall i) (fun c => mergeCall c d)

def applyCalls (pol : Policy) (calls : List CallAcc) : List ToolCallDelta → Option (List CallAcc)
  | [] => some calls
  | d :: ds =>
    match d.index with
    | some i => applyCalls pol (applyCall calls d i) ds
    | none => if pol.missingIndexIsZero then applyCalls pol (applyCall calls d 0) ds else none

def applyChoice (pol : Policy) (a : ChoiceAcc) (c : ChunkChoice) : Option ChoiceAcc :=
  match applyCalls pol a.calls c.delta.toolCalls with
  | none => none
  | some calls =>
    some { a with content := appendOpt a.content c.delta.content, refusal := appendOpt a.refusal c.delta.refusal, calls,
                  finish := match c.finishReason with | some f => some f | none => a.finish }

/-- Why a chunk's choice has no usable index. -/
def choiceIndex (pol : Policy) (c : ChunkChoice) : Option Nat :=
  match c.index with
  | some i => some i
  | none => if pol.missingIndexIsZero then some 0 else none

/-- Fold the choices of a chunk into the state; `none` when a choice or a fragment has no index and the policy refuses it. -/
def applyChoices (pol : Policy) (cs : List ChoiceAcc) : List ChunkChoice → Option (List ChoiceAcc)
  | [] => some cs
  | c :: rest =>
    match choiceIndex pol c with
    | none => none
    | some i =>
      let a := (cs.find? (fun a => a.index == i)).getD (newChoice i)
      match applyChoice pol a c with
      | none => none
      | some a' => applyChoices pol (upd ChoiceAcc.index cs i (newChoice i) (fun _ => a')) rest

/-- One chunk into the state. -/
def applyChunk (pol : Policy) (s : State) (c : Chunk) : Option State :=
  match applyChoices pol s.choices c.choices with
  | none => none
  | some choices =>
    some { id := firstOpt s.id c.id, model := firstOpt s.model c.model, choices,
           usage := match c.usage with | some u => some u | none => s.usage }

/-! ### From the state to a reply -/

def CallAcc.soFar (c : CallAcc) : ToolCall := ⟨c.id.getD "", c.name.getD "", c.arguments⟩

def ChoiceAcc.soFar (a : ChoiceAcc) : Choice :=
  ⟨some a.index, ⟨a.content, a.refusal, a.calls.map CallAcc.soFar⟩, a.finish⟩

/-- The reply so far, with an unnamed tool call read as empty strings: **only for a truncated or errored stream, never to be executed**. -/
def State.soFar (s : State) : Response := ⟨s.id, s.model, s.choices.map ChoiceAcc.soFar, s.usage⟩

/-- A completed call has its identity. -/
def CallAcc.complete? (c : CallAcc) : Bool := c.id.isSome && c.name.isSome

def State.complete? (s : State) : Bool := s.choices.all (fun a => a.calls.all CallAcc.complete?)

/-! ### Events -/

/-- What one event is. -/
inductive Item where
  | chunk (c : Chunk)
  | done
  | skip
  deriving DecidableEq, Repr

inductive StreamFault where
  /-- the data of the i-th event is neither the sentinel nor JSON -/
  | notJson (i : Nat)
  /-- the i-th event has a type the convention does not use -/
  | eventType (i : Nat) (type : String)
  /-- the i-th chunk is malformed -/
  | chunk (i : Nat) (f : Fault)
  /-- the i-th chunk has a choice or a tool-call fragment with no index (and the policy refuses it) -/
  | missingIndex (i : Nat)
  /-- an event follows the sentinel -/
  | afterDone (i : Nat)
  /-- a completed tool call has no id or no name -/
  | callIdentity
  /-- the sentinel came but no chunk ever carried a choice: there is no reply to complete -/
  | noChoices
  deriving DecidableEq, Repr

inductive Outcome where
  | complete (r : Response)
  | truncated (soFar : Response)
  | errorChunk (message : Option String) (soFar : Response)
  deriving DecidableEq, Repr

/-- Fold a list, decoding each element to an item as it is reached (so a fault after an error chunk or after the sentinel is never read): chunks are applied in order, an error chunk stops the fold, the sentinel
ends it, the end of the list with no sentinel is `truncated`. -/
def foldWith {α : Type} (pol : Policy) (dec : Nat → α → Except StreamFault Item) : List α → Nat → State → Except StreamFault Outcome
  | [], _, s => .ok (.truncated s.soFar)
  | x :: rest, i, s =>
    match dec i x with
    | .error f => .error f
    | .ok .skip => foldWith pol dec rest (i + 1) s
    | .ok .done =>
      if !rest.isEmpty then .error (.afterDone (i + 1))
      else if s.choices.isEmpty then .error .noChoices
      else if s.complete? then .ok (.complete s.soFar) else .error .callIdentity
    | .ok (.chunk c) =>
      match applyChunk pol s c with
      | none => .error (.missingIndex i)
      | some s' =>
        match c.error with
        | some e => .ok (.errorChunk e.message s'.soFar)
        | none => foldWith pol dec rest (i + 1) s'

/-- Fold already-decoded items. -/
def foldItems (pol : Policy) (items : List Item) : Except StreamFault Outcome :=
  foldWith pol (fun _ x => .ok x) items 0 State.empty

/-- One event as an item: the sentinel, an ignored empty event, or a chunk decoded from its JSON. -/
def decodeItem (parse : String → Option Value) (i : Nat) (e : Event) : Except StreamFault Item :=
  if e.data == "[DONE]" then .ok .done
  else if e.data.isEmpty then .ok .skip
  else if e.type != "" && e.type != "message" then .error (.eventType i e.type)
  else
    match parse e.data with
    | none => .error (.notJson i)
    | some v =>
      match decodeChunk v with
      | .ok c => .ok (.chunk c)
      | .error f => .error (.chunk i f)

/-- **Fold a stream of events.** `parse` is the pinned parser's `LeanJson.parseFast` on the data's bytes (a parameter so the fold stays a pure function of what it is given). -/
def foldEvents (pol : Policy) (parse : String → Option Value) (es : List Event) : Except StreamFault Outcome :=
  foldWith pol (decodeItem parse) es 0 State.empty

end VbmLlm.OpenAI
