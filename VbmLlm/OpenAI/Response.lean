import VbmLlm.Wire
import VbmLlm.Fault
/-! # OpenAI chat-completions: the response of one non-streaming call

The wire contract of `CreateChatCompletionResponse` (schema pinned in `docs/schemas/openai-chat.md`), read from a parsed `LeanJson.Value`. **No client behaviour**: nothing here says what to do with a
reply (an answer with no text and no calls is a *policy* of the harness, not a fault of the wire), and no model name or price appears.

Reading rules (the policy, stated once; each is a theorem in `VbmLlmProofs/OpenAI/Response.lean`):
* the reply must be an object with a **non-empty** `choices` array; every choice an object with a `message` object. Nothing else is required: the schema's other required fields (`id`, `created`,
  `model`, `object`) are read when present and ignored when absent, because compatible servers omit them and the decoder reads what a consumer acts on;
* a field that is read and **present** (not `null`) must have its type: a wrong type is refused, never coerced (fail closed);
* `null` and absent are the same (the schema marks `content`, `refusal`, `finish_reason` nullable);
* a tool call is `{id, type?, function: {name, arguments}}`: `id`, `function`, `name` and `arguments` are required, `type` when present must be `"function"` (a `custom` call is a different shape and is
  refused as unsupported, not read as a function call); `arguments` is kept **verbatim as the model wrote it**: JSON text the model may have got wrong, never parsed here (the schema says so itself);
* a finish reason is kept as the provider's text; `FinishClass.ofWire` (`Finish.lean`) classes it;
* usage counts are plain naturals when present (a sign, a fraction, an exponent or a string is refused); absent counts stay absent, they are not 0;
* unread fields (`logprobs`, `system_fingerprint`, `created`, `service_tier`, annotations, audio, ...) are ignored. -/
namespace VbmLlm.OpenAI
open LeanJson

/-- A tool call of an assistant message: the provider's id, the function's name, and its arguments as the text the model wrote. -/
structure ToolCall where
  id : String
  name : String
  arguments : String
  deriving DecidableEq, Repr

/-- The usage report. A count is `none` when the provider did not report it. `promptTokens` **includes** the cached ones (`cachedTokens` is a part of it). -/
structure Usage where
  promptTokens : Option Nat
  completionTokens : Option Nat
  totalTokens : Option Nat
  cachedTokens : Option Nat
  reasoningTokens : Option Nat
  deriving DecidableEq, Repr

/-- The assistant message of a choice. -/
structure Message where
  content : Option String
  refusal : Option String
  toolCalls : List ToolCall
  deriving DecidableEq, Repr

structure Choice where
  index : Option Nat
  message : Message
  /-- the provider's text, `none` when `null` or absent -/
  finishReason : Option String
  deriving DecidableEq, Repr

structure Response where
  id : Option String
  /-- the model the provider says served the call: an opaque string -/
  model : Option String
  choices : List Choice
  usage : Option Usage
  deriving DecidableEq, Repr

/-! ### Field readers: absent or `null` is `none`, a present value must have its type -/

/-- An optional string member. -/
def optStr (o : Value) (k : String) : Except Fault (Option String) :=
  match get o k with
  | .null => .ok none
  | .str s => .ok (some s)
  | _ => .error { path := [.key k], kind := .wrongType .string }

/-- An optional natural member. -/
def optNat (o : Value) (k : String) : Except Fault (Option Nat) :=
  match get o k with
  | .null => .ok none
  | .num n =>
    match natOf n with
    | some m => .ok (some m)
    | none => .error { path := [.key k], kind := .wrongType .natural }
  | _ => .error { path := [.key k], kind := .wrongType .natural }

/-- A required string member. -/
def reqStr (o : Value) (k : String) : Except Fault String :=
  match get o k with
  | .null => .error { path := [.key k], kind := .missing }
  | .str s => .ok s
  | _ => .error { path := [.key k], kind := .wrongType .string }

/-- A required object member (returned as the value). -/
def reqObj (o : Value) (k : String) : Except Fault Value :=
  match get o k with
  | .null => .error { path := [.key k], kind := .missing }
  | .obj ms => .ok (.obj ms)
  | _ => .error { path := [.key k], kind := .wrongType .object }

/-- An optional natural inside an optional detail object (`prompt_tokens_details.cached_tokens`): the detail object `null` or absent means the count is absent; a present non-object is refused. -/
def optDetail (u : Value) (obj k : String) : Except Fault (Option Nat) :=
  match get u obj with
  | .null => .ok none
  | .obj ms => underStep (.key obj) (optNat (.obj ms) k)
  | _ => .error { path := [.key obj], kind := .wrongType .object }

/-! ### Tool calls -/

/-- `type`, when present, must be `"function"`: any other word is a different kind of call (refused as unsupported), a non-string is refused. -/
def checkType (v : Value) : Except Fault Unit :=
  match get v "type" with
  | .null => .ok ()
  | .str "function" => .ok ()
  | .str t => .error { path := [.key "type"], kind := .unsupported t }
  | _ => .error { path := [.key "type"], kind := .wrongType .string }

/-- One tool call: `id`, `function.name`, `function.arguments` are required strings; see `checkType`. -/
def decodeToolCall (v : Value) : Except Fault ToolCall :=
  match v with
  | .obj _ => do
    checkType v
    let id ← reqStr v "id"
    let fn ← reqObj v "function"
    let name ← underStep (.key "function") (reqStr fn "name")
    let arguments ← underStep (.key "function") (reqStr fn "arguments")
    pure { id, name, arguments }
  | _ => .error (Fault.here (.wrongType .object))

/-- The calls of an array, in order; a fault names the index. -/
def decodeToolCalls : List Value → Nat → Except Fault (List ToolCall)
  | [], _ => .ok []
  | v :: vs, i => do
    let c ← underStep (.idx i) (decodeToolCall v)
    let cs ← decodeToolCalls vs (i + 1)
    pure (c :: cs)

/-- `tool_calls`: absent or `null` is no calls; an array is its calls; anything else is refused. -/
def decodeCalls (m : Value) : Except Fault (List ToolCall) :=
  match get m "tool_calls" with
  | .null => .ok []
  | .arr xs => underStep (.key "tool_calls") (decodeToolCalls xs 0)
  | _ => .error { path := [.key "tool_calls"], kind := .wrongType .array }

/-! ### Messages, choices, usage, the reply -/

def decodeMessage (m : Value) : Except Fault Message := do
  let content ← optStr m "content"
  let refusal ← optStr m "refusal"
  let toolCalls ← decodeCalls m
  pure { content, refusal, toolCalls }

def decodeChoice (c : Value) : Except Fault Choice :=
  match c with
  | .obj _ => do
    let index ← optNat c "index"
    let finishReason ← optStr c "finish_reason"
    let m ← reqObj c "message"
    let message ← underStep (.key "message") (decodeMessage m)
    pure { index, message, finishReason }
  | _ => .error (Fault.here (.wrongType .object))

def decodeChoices : List Value → Nat → Except Fault (List Choice)
  | [], _ => .ok []
  | v :: vs, i => do
    let c ← underStep (.idx i) (decodeChoice v)
    let cs ← decodeChoices vs (i + 1)
    pure (c :: cs)

/-- The usage object: counts when present. `prompt_tokens_details.cached_tokens` and `completion_tokens_details.reasoning_tokens` are read from the detail objects when those are present. -/
def decodeUsage (u : Value) : Except Fault Usage := do
  let promptTokens ← optNat u "prompt_tokens"
  let completionTokens ← optNat u "completion_tokens"
  let totalTokens ← optNat u "total_tokens"
  let cachedTokens ← optDetail u "prompt_tokens_details" "cached_tokens"
  let reasoningTokens ← optDetail u "completion_tokens_details" "reasoning_tokens"
  pure { promptTokens, completionTokens, totalTokens, cachedTokens, reasoningTokens }

/-- `usage`: absent or `null` is no report; an object is read; anything else is refused. -/
def decodeUsageOpt (v : Value) : Except Fault (Option Usage) :=
  match get v "usage" with
  | .null => .ok none
  | .obj ms => do
    let u ← underStep (.key "usage") (decodeUsage (.obj ms))
    pure (some u)
  | _ => .error { path := [.key "usage"], kind := .wrongType .object }

/-- The `choices` array: required, and not empty. -/
def decodeChoicesField (v : Value) : Except Fault (List Choice) :=
  match get v "choices" with
  | .null => .error { path := [.key "choices"], kind := .missing }
  | .arr [] => .error { path := [.key "choices"], kind := .empty }
  | .arr xs => underStep (.key "choices") (decodeChoices xs 0)
  | _ => .error { path := [.key "choices"], kind := .wrongType .array }

/-- **Decode one complete chat-completion reply.** -/
def decode (v : Value) : Except Fault Response :=
  match v with
  | .obj _ => do
    let id ← optStr v "id"
    let model ← optStr v "model"
    let choices ← decodeChoicesField v
    let usage ← decodeUsageOpt v
    pure { id, model, choices, usage }
  | _ => .error (Fault.here (.wrongType .object))

end VbmLlm.OpenAI
