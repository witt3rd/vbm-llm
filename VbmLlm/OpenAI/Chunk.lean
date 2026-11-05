import VbmLlm.OpenAI.Response
/-! # OpenAI chat-completions: one streamed chunk

The wire contract of `CreateChatCompletionStreamResponse` (schema pinned in `docs/schemas/openai-chat.md`), read from a parsed `LeanJson.Value`, with the reading rules of `Response.lean`: `null` and absent are the same,
a present field has its type or is refused, unread fields are ignored. Differences a stream has:
* `choices` may be absent or empty (the usage frame of `stream_options.include_usage` has none);
* a choice carries a `delta`, absent reads as an empty delta;
* a tool-call fragment's `index` is **required** by the schema: it is read as `Option` here and the fold decides what a missing one means (`Policy.missingIndexIsZero`);
* an `error` member anywhere makes the chunk an **error chunk** (OpenRouter's mid-stream error arrives after content with HTTP 200): its message is kept when it is a string or an object with a string `message`. -/
namespace VbmLlm.OpenAI
open LeanJson

/-- A fragment of a tool call: merged by `index`; `id` and `name` normally arrive once, `arguments` in pieces. -/
structure ToolCallDelta where
  index : Option Nat
  id : Option String
  name : Option String
  arguments : Option String
  deriving DecidableEq, Repr

structure Delta where
  content : Option String
  refusal : Option String
  toolCalls : List ToolCallDelta
  deriving DecidableEq, Repr

structure ChunkChoice where
  index : Option Nat
  delta : Delta
  finishReason : Option String
  deriving DecidableEq, Repr

/-- An error object carried by a chunk. -/
structure ChunkError where
  message : Option String
  deriving DecidableEq, Repr

structure Chunk where
  id : Option String
  model : Option String
  choices : List ChunkChoice
  usage : Option Usage
  error : Option ChunkError
  deriving DecidableEq, Repr

def decodeToolCallDelta (v : Value) : Except Fault ToolCallDelta :=
  match v with
  | .obj _ => do
    checkType v
    let index ← optNat v "index"
    let id ← optStr v "id"
    match get v "function" with
    | .null => pure { index, id, name := none, arguments := none }
    | .obj fms =>
      let name ← underStep (.key "function") (optStr (.obj fms) "name")
      let arguments ← underStep (.key "function") (optStr (.obj fms) "arguments")
      pure { index, id, name, arguments }
    | _ => .error { path := [.key "function"], kind := .wrongType .object }
  | _ => .error (Fault.here (.wrongType .object))

def decodeToolCallDeltas : List Value → Nat → Except Fault (List ToolCallDelta)
  | [], _ => .ok []
  | v :: vs, i => do
    let c ← underStep (.idx i) (decodeToolCallDelta v)
    let cs ← decodeToolCallDeltas vs (i + 1)
    pure (c :: cs)

def decodeDelta (d : Value) : Except Fault Delta := do
  let content ← optStr d "content"
  let refusal ← optStr d "refusal"
  match get d "tool_calls" with
  | .null => pure { content, refusal, toolCalls := [] }
  | .arr xs =>
    let toolCalls ← underStep (.key "tool_calls") (decodeToolCallDeltas xs 0)
    pure { content, refusal, toolCalls }
  | _ => .error { path := [.key "tool_calls"], kind := .wrongType .array }

def emptyDelta : Delta := { content := none, refusal := none, toolCalls := [] }

def decodeChunkChoice (c : Value) : Except Fault ChunkChoice :=
  match c with
  | .obj _ => do
    let index ← optNat c "index"
    let finishReason ← optStr c "finish_reason"
    match get c "delta" with
    | .null => pure { index, delta := emptyDelta, finishReason }
    | .obj dms =>
      let delta ← underStep (.key "delta") (decodeDelta (.obj dms))
      pure { index, delta, finishReason }
    | _ => .error { path := [.key "delta"], kind := .wrongType .object }
  | _ => .error (Fault.here (.wrongType .object))

def decodeChunkChoices : List Value → Nat → Except Fault (List ChunkChoice)
  | [], _ => .ok []
  | v :: vs, i => do
    let c ← underStep (.idx i) (decodeChunkChoice v)
    let cs ← decodeChunkChoices vs (i + 1)
    pure (c :: cs)

/-- The error member: any present value is an error; its message is a string, or an object's string `message`, else none. -/
def errorOf (v : Value) : Option ChunkError :=
  match get v "error" with
  | .null => none
  | .str s => some ⟨some s⟩
  | e => some ⟨str? (get e "message")⟩

def decodeChunk (v : Value) : Except Fault Chunk :=
  match v with
  | .obj _ => do
    let id ← optStr v "id"
    let model ← optStr v "model"
    let choices ←
      match get v "choices" with
      | .null => pure []
      | .arr xs => underStep (.key "choices") (decodeChunkChoices xs 0)
      | _ => .error { path := [.key "choices"], kind := .wrongType .array }
    let usage ← decodeUsageOpt v
    pure { id, model, choices, usage, error := errorOf v }
  | _ => .error (Fault.here (.wrongType .object))

end VbmLlm.OpenAI
