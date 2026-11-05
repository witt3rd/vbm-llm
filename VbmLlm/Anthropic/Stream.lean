import VbmLlm.Anthropic.Event
/-! # Anthropic messages: folding a stream of named events into one reply

A stream folds to **exactly one outcome**, with the same three cases as the OpenAI fold:
* `complete`: `message_start` came first, `message_stop` was seen and nothing followed it. The reply is the same type the single-shot decode gives (`Response`), a call's `input` parsed from the `partial_json`
  pieces it was sent in (a text that does not parse is a fault; none sent means the `input` of the block's start);
* `truncated`: the events ended with no `message_stop`: the partial reply is typed as partial, never presented as a complete one; a call whose pieces do not (yet) parse is kept with its `input` as the text
  received, **as a string value**, never as a half-read object;
* `errorEvent`: an `error` event: the fold stops with its message and the partial reply (whether to discard what was received is the consumer's decision).

Merge rules (proved in `VbmLlmProofs/Anthropic/Stream.lean`): a block is keyed by its `index` and starts as `content_block_start` carries it; `text_delta`, `input_json_delta`, `thinking_delta` and
`signature_delta` **concatenate in order**, so chunk boundaries do not matter; a delta that does not fit its block, a delta or a stop for a block that never started, a block started twice, and any event before
`message_start` or a second `message_start` are faults; the stop reason and sequence of `message_delta` and each usage count are the **last non-null** seen (the counts of a `message_delta` are cumulative). -/
namespace VbmLlm.Anthropic
open LeanJson

/-- A block while it is being built: its start, and the `partial_json` pieces of a call so far. -/
structure Acc where
  index : Nat
  block : Block
  json : String
  deriving Repr

structure State where
  id : Option String
  model : Option String
  blocks : List Acc
  stopReason : Option String
  stopSequence : Option String
  usage : Option Usage
  started : Bool
  deriving Repr

def State.empty : State := ⟨none, none, [], none, none, none, false⟩

def Acc.apply (a : Acc) : Delta → Option Acc
  | .text s => match a.block with | .text t => some { a with block := .text (t ++ s) } | _ => none
  | .json s => match a.block with | .toolUse .. => some { a with json := a.json ++ s } | _ => none
  | .thinking s => match a.block with | .thinking t g => some { a with block := .thinking (t ++ s) g } | _ => none
  | .signature s => match a.block with | .thinking t g => some { a with block := .thinking t (g ++ s) } | _ => none
  | .other => some a

/-- The later count wins when it is there. -/
def later (a b : Option Nat) : Option Nat := match b with | some _ => b | none => a

def mergeUsage (a b : Usage) : Usage := ⟨later a.inputTokens b.inputTokens, later a.outputTokens b.outputTokens, later a.cacheReadTokens b.cacheReadTokens, later a.cacheCreationTokens b.cacheCreationTokens⟩

def mergeUsageOpt : Option Usage → Option Usage → Option Usage
  | a, none => a
  | none, b => b
  | some a, some b => some (mergeUsage a b)

inductive StreamFault where
  | notJson (i : Nat)
  /-- the i-th event is malformed -/
  | event (i : Nat) (f : Fault)
  /-- an event follows `message_stop` -/
  | afterStop (i : Nat)
  /-- the i-th event is not `message_start` and came before it, or is a second `message_start` -/
  | order (i : Nat)
  /-- a delta that does not fit its block, a delta or stop for a block that never started, a block started twice -/
  | block (i : Nat)
  /-- `message_stop` with a call whose pieces do not parse to a JSON value -/
  | badInput (i : Nat)
  deriving DecidableEq, Repr

/-- Apply an item that is not `ping`, `stop` or `error`. -/
def step (i : Nat) (s : State) : Item → Except StreamFault State
  | .start id model usage => if s.started then .error (.order i) else .ok { s with id, model, usage, started := true }
  | .blockStart idx b =>
    if !s.started then .error (.order i)
    else if s.blocks.any (·.index == idx) then .error (.block i) else .ok { s with blocks := s.blocks ++ [⟨idx, b, ""⟩] }
  | .blockDelta idx d =>
    if !s.started then .error (.order i)
    else if !(s.blocks.any (·.index == idx)) then .error (.block i)
    else match s.blocks.mapM (fun a => if a.index == idx then a.apply d else some a) with
      | some bs => .ok { s with blocks := bs }
      | none => .error (.block i)
  | .blockStop idx => if !s.started then .error (.order i) else if s.blocks.any (·.index == idx) then .ok s else .error (.block i)
  | .msgDelta sr ss u =>
    if !s.started then .error (.order i)
    else .ok { s with stopReason := (match sr with | some _ => sr | none => s.stopReason), stopSequence := (match ss with | some _ => ss | none => s.stopSequence), usage := mergeUsageOpt s.usage u }
  | _ => .ok s

/-- A block as the reply holds it: a call's `input` is the value its pieces parse to (none sent: the start's); `none` when they do not parse. -/
def Acc.final (parse : String → Option Value) (a : Acc) : Option Block :=
  match a.block with
  | .toolUse id n inp => if a.json.isEmpty then some (.toolUse id n inp) else match parse a.json with | some .null => none | some v => some (.toolUse id n v) | none => none
  | b => some b

/-- A block as the partial reply holds it: a call whose pieces do not parse keeps them as a string value. -/
def Acc.partial (parse : String → Option Value) (a : Acc) : Block :=
  match a.final parse with
  | some b => b
  | none => match a.block with | .toolUse id n _ => .toolUse id n (.str a.json) | b => b

def State.soFar (parse : String → Option Value) (s : State) : Response := ⟨s.id, s.model, s.blocks.map (·.partial parse), s.stopReason, s.stopSequence, s.usage⟩

def State.finish (parse : String → Option Value) (s : State) : Option Response := do
  let bs ← s.blocks.mapM (·.final parse)
  pure ⟨s.id, s.model, bs, s.stopReason, s.stopSequence, s.usage⟩

inductive Outcome where
  | complete (r : Response)
  | truncated (soFar : Response)
  | errorEvent (message : Option String) (soFar : Response)
  deriving Repr

/-- Fold a list, decoding each element as it is reached (so a fault after an error event or after `message_stop` is never read). -/
def foldWith {α : Type} (parse : String → Option Value) (dec : Nat → α → Except StreamFault Item) : List α → Nat → State → Except StreamFault Outcome
  | [], _, s => .ok (.truncated (s.soFar parse))
  | x :: rest, i, s =>
    match dec i x with
    | .error f => .error f
    | .ok .ping => foldWith parse dec rest (i + 1) s
    | .ok .stop =>
      if !rest.isEmpty then .error (.afterStop (i + 1))
      else if !s.started then .error (.order i)
      else match s.finish parse with
        | some r => .ok (.complete r)
        | none => .error (.badInput i)
    | .ok (.error m) => .ok (.errorEvent m (s.soFar parse))
    | .ok it =>
      match step i s it with
      | .error f => .error f
      | .ok s' => foldWith parse dec rest (i + 1) s'

def foldItems (parse : String → Option Value) (items : List Item) : Except StreamFault Outcome :=
  foldWith parse (fun _ x => .ok x) items 0 State.empty

/-- One event as an item: empty data is ignored (as a ping), anything else is JSON read by `decodeEventData`. -/
def decodeEvent (parse : String → Option Value) (i : Nat) (e : Event) : Except StreamFault Item :=
  if e.data.isEmpty then .ok .ping
  else match parse e.data with
    | none => .error (.notJson i)
    | some v => match decodeEventData e.type v with
      | .ok it => .ok it
      | .error f => .error (.event i f)

/-- **Fold a stream of events.** `parse` is the pinned parser's `LeanJson.parseFast` on the data's bytes (a parameter so the fold stays a pure function of what it is given). -/
def foldEvents (parse : String → Option Value) (es : List Event) : Except StreamFault Outcome :=
  foldWith parse (decodeEvent parse) es 0 State.empty

end VbmLlm.Anthropic
