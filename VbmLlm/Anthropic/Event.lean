import VbmLlm.Anthropic.Response
import VbmLlm.Sse
/-! # Anthropic messages: one streamed event

The wire contract of `RawMessageStreamEvent` (schema pinned in `docs/schemas/anthropic-messages.md`), read from a server-sent event whose data is a JSON object with a `type`. The convention names its
events (`message_start`, `content_block_start`, `content_block_delta`, `content_block_stop`, `message_delta`, `message_stop`, `ping`, `error`): the event's `type` field of the stream, when there is one, must
equal the data's `type` (a mismatch is refused); an event with a data type outside these is refused; `ping` is read and ignored. A block starts as `decodeBlock` reads it, its deltas (`text_delta`,
`input_json_delta`, `thinking_delta`, `signature_delta`; any other delta, a citations delta say, is read and ignored) are merged by the fold. Same reading rules as the reply: a present field of the wrong type
is refused, `null` and absent are the same, a count is a plain natural. -/
namespace VbmLlm.Anthropic
open LeanJson VbmLlm.OpenAI

/-- A delta of a content block. -/
inductive Delta where
  | text (s : String)
  | json (s : String)
  | thinking (s : String)
  | signature (s : String)
  /-- a delta of a type not merged here (kept out of the reply) -/
  | other
  deriving DecidableEq, Repr

/-- What one event is. -/
inductive Item where
  /-- `message_start`: the message's identity and the usage known at the start -/
  | start (id model : Option String) (usage : Option Usage)
  | blockStart (index : Nat) (block : Block)
  | blockDelta (index : Nat) (delta : Delta)
  | blockStop (index : Nat)
  /-- `message_delta`: the stop reason and the usage counts so far -/
  | msgDelta (stopReason stopSequence : Option String) (usage : Option Usage)
  | stop
  | ping
  /-- an `error` event, with its message when it has one -/
  | error (message : Option String)

def decodeDelta (v : Value) : Except Fault Delta :=
  match v with
  | .obj _ => do
    match ← reqStr v "type" with
    | "text_delta" => pure (.text (← reqStr v "text"))
    | "input_json_delta" => pure (.json (← reqStr v "partial_json"))
    | "thinking_delta" => pure (.thinking (← reqStr v "thinking"))
    | "signature_delta" => pure (.signature (← reqStr v "signature"))
    | _ => pure .other
  | _ => .error (Fault.here (.wrongType .object))

/-- The index every block event carries (required). -/
def reqIndex (v : Value) : Except Fault Nat :=
  match optNat v "index" with
  | .ok (some n) => .ok n
  | .ok none => .error { path := [.key "index"], kind := .missing }
  | .error e => .error e

/-- The usage of a `message_delta` (a count is read when present). -/
def decodeDeltaUsage (v : Value) : Except Fault (Option Usage) :=
  match get v "usage" with
  | .null => .ok none
  | .obj ms => do pure (some (← underStep (.key "usage") (decodeUsage (.obj ms))))
  | _ => .error { path := [.key "usage"], kind := .wrongType .object }

/-- The event of the data type `t`. -/
def decodeItemOf (t : String) (v : Value) : Except Fault Item :=
  match t with
  | "message_start" => do
    let m ← reqObj v "message"
    pure (.start (← underStep (.key "message") (optStr m "id")) (← underStep (.key "message") (optStr m "model")) (← underStep (.key "message") (decodeUsageOpt m)))
  | "content_block_start" => do
    let b ← reqObj v "content_block"
    pure (.blockStart (← reqIndex v) (← underStep (.key "content_block") (decodeBlock b)))
  | "content_block_delta" => do
    let d ← reqObj v "delta"
    pure (.blockDelta (← reqIndex v) (← underStep (.key "delta") (decodeDelta d)))
  | "content_block_stop" => do pure (.blockStop (← reqIndex v))
  | "message_delta" => do
    let d ← reqObj v "delta"
    pure (.msgDelta (← underStep (.key "delta") (optStr d "stop_reason")) (← underStep (.key "delta") (optStr d "stop_sequence")) (← decodeDeltaUsage v))
  | "message_stop" => .ok .stop
  | "ping" => .ok .ping
  | "error" => .ok (.error (match get v "error" with | .obj _ => str? (get (get v "error") "message") | _ => none))
  | other => .error { path := [.key "type"], kind := .unsupported other }

/-- **Decode one event's data**: an object with a `type`, which the stream's own event type, when named, must equal. -/
def decodeEventData (evType : String) (v : Value) : Except Fault Item :=
  match v with
  | .obj _ =>
    match reqStr v "type" with
    | .ok t => if evType == "" || evType == t then decodeItemOf t v else .error { path := [.key "type"], kind := .unsupported evType }
    | .error e => .error e
  | _ => .error (Fault.here (.wrongType .object))

end VbmLlm.Anthropic
