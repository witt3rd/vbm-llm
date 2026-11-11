import LeanJson.PrintBytes
import VbmLlm.OpenAI.Response
/-! # OpenAI chat-completions: the request of one call

The wire contract of `CreateChatCompletionRequest` (schema pinned in `docs/schemas/openai-chat.md`) as a **typed request** and its encoding to a `LeanJson.Value` (printing the value to bytes is `Request.encodeBytes`, equal to
`LeanJson.print`, proved in `vbm-json` to parse back to it). The typed request carries what a tool-using agent sends: the model (an opaque string), the messages (system, developer, user and tool
messages as text, assistant messages as text and tool calls), the tool declarations, `tool_choice`, `parallel_tool_calls`, `stream`, `stream_options.include_usage`, the token limits, the two sampling
numbers and the reasoning effort (OpenRouter's and the compatible providers' `reasoning` object, `{"effort": <level>}`: the level is the model's own vocabulary, an opaque string like `model`, never looked at).
Everything else the schema lists is not modelled (`docs/clause-index.txt` says which).

Encoding rules (each a theorem in `VbmLlmProofs/OpenAI/Request.lean`): a member of the request that is `none` (or an empty `tools` list, or an assistant message with no calls and no text) is **left out**, never written as `null`, with one exception: an assistant message that has tool calls and no text is written with `"content": null`;
a tool call's arguments are written verbatim; a count is written as a plain natural. No client behaviour: the model name is not looked at, nothing says which fields a provider honours.

One argument of the encoder is the caller's alone: the **cache marker** (`Request.encodeWith r cacheAt`). Some providers cache a prompt prefix only when one content part carries `cache_control: {"type": "ephemeral"}`, and re-bill the whole prompt without it; the caller names the index of the message to mark (`lastMarkable` gives the last one that can carry it, `markable` asks of one), and that message's content becomes the one-part text array `[{"type": "text", "text": <the text>, "cache_control": {"type": "ephemeral"}}]` with the text unchanged. Every other message is written exactly as before, `encodeWith r none` is `r.encode` byte for byte, and an index that names no message that can carry a marker (an assistant turn of calls only has no content part, an index past the end names no message) writes **no marker at all**: a hint that cannot be honoured is dropped, never refused and never moved elsewhere. At most one message of a request carries it. Reading: `decodeContentStr` accepts that one-part shape back (and refuses any other array, never dropping a part), and `Request.markerAt` reads the index a body carries. -/
namespace VbmLlm.OpenAI
open LeanJson

/-- A message of the conversation: text content only (an array of content parts is not modelled). -/
inductive RequestMessage where
  | system (content : String)
  | developer (content : String)
  | user (content : String)
  /-- the assistant's text (absent when the turn is only calls) and its tool calls, as the provider sent them -/
  | assistant (content : Option String) (toolCalls : List ToolCall)
  /-- the answer to the call `callId` -/
  | tool (callId : String) (content : String)
  deriving DecidableEq, Repr

/-- A function the model may call. `parameters` is the members of the JSON Schema object, as the caller wrote them. -/
structure Tool where
  name : String
  description : Option String := none
  parameters : Option (List (String × Value)) := none
  strict : Option Bool := none
  deriving Repr

inductive ToolChoice where
  /-- `"none"`: no tool call -/
  | never
  | auto
  | required
  /-- a particular function -/
  | named (name : String)
  deriving DecidableEq, Repr

structure Request where
  /-- an opaque string -/
  model : String
  messages : List RequestMessage
  tools : List Tool := []
  toolChoice : Option ToolChoice := none
  parallelToolCalls : Option Bool := none
  stream : Option Bool := none
  /-- `stream_options.include_usage` -/
  includeUsage : Option Bool := none
  maxCompletionTokens : Option Nat := none
  maxTokens : Option Nat := none
  temperature : Option Number := none
  topP : Option Number := none
  /-- the model's own reasoning level (`max`, `xhigh`, `high`, `medium`, `low`, `minimal`, `none`, or another word the provider's model list allows): an opaque string -/
  reasoningEffort : Option String := none
  deriving Repr

/-! ### A count as a number lexeme -/

/-- The first digit (as the lexeme's `lead`, the digit minus one) and the others of a positive natural, written in decimal. -/
def leadRest (n : Nat) : Fin 9 × List Digit :=
  if h : n < 10 then (⟨n - 1, by omega⟩, [])
  else
    let p := leadRest (n / 10)
    (p.1, p.2 ++ [⟨n % 10, Nat.mod_lt _ (by omega)⟩])
termination_by n
decreasing_by omega

/-- The plain-natural lexeme of `n`: no sign, no fraction, no exponent. -/
def natNumber (n : Nat) : Number :=
  if n = 0 then ⟨false, .zero, none, none⟩
  else ⟨false, .nz (leadRest n).1 (leadRest n).2, none, none⟩

/-! ### Encoding -/

/-- A member that is left out when absent. -/
def opt {α : Type} (k : String) (f : α → Value) : Option α → List (String × Value) → List (String × Value)
  | none, rest => rest
  | some a, rest => (k, f a) :: rest

def encodeToolCall (c : ToolCall) : Value :=
  .obj [("id", .str c.id), ("type", .str "function"), ("function", .obj [("name", .str c.name), ("arguments", .str c.arguments)])]

/-- An assistant message's text, or `null` when there is none (a provider may refuse a message with calls and no `content` member). -/
def orNullStr : Option String → Value
  | none => .null
  | some s => .str s

def encodeMessage : RequestMessage → Value
  | .system c => .obj [("role", .str "system"), ("content", .str c)]
  | .developer c => .obj [("role", .str "developer"), ("content", .str c)]
  | .user c => .obj [("role", .str "user"), ("content", .str c)]
  | .assistant c [] => .obj (("role", .str "assistant") :: opt "content" .str c [])
  | .assistant c cs => .obj (("role", .str "assistant") :: ("content", orNullStr c) :: [("tool_calls", .arr (cs.map encodeToolCall))])
  | .tool i c => .obj [("role", .str "tool"), ("tool_call_id", .str i), ("content", .str c)]

def encodeTool (t : Tool) : Value :=
  .obj [("type", .str "function"), ("function", .obj (("name", .str t.name) :: opt "description" .str t.description (opt "parameters" .obj t.parameters (opt "strict" .bool t.strict []))))]

/-- The `reasoning` object: the effort, the only member modelled (OpenRouter and the compatible providers take `{"effort": <level>}`). -/
def encodeReasoning (effort : String) : Value :=
  .obj [("effort", .str effort)]

def encodeToolChoice : ToolChoice → Value
  | .never => .str "none"
  | .auto => .str "auto"
  | .required => .str "required"
  | .named n => .obj [("type", .str "function"), ("function", .obj [("name", .str n)])]

/-! ### The cache marker: the caller names the message that ends the cacheable prefix

Some providers cache a prompt prefix only when **one** content part of the request carries an explicit marker, `cache_control: {"type": "ephemeral"}`: the next call then reads the previous prefix back from the
cache instead of paying for it again. The marker is a **hint the caller asks for**, so it is an argument of the encoder (`Request.encodeWith`) and never a member of the typed request: a request is the same
request with or without it. With no marker the encoding is exactly `Request.encode`'s; an index whose message cannot carry one (an assistant message with no text) or that is past the end writes no marker
at all: a hint that cannot be honoured is dropped, never refused, and never a reason to guess where else to put it (`markable` and `lastMarkable` let the caller choose the index it can honour).

The marker word and the shape are the convention's, not ours: nothing here looks at a model or a provider name. -/

/-- The text a message carries; `none` for an assistant message whose turn is only tool calls (and so has no `content` to carry a marker). -/
def msgText : RequestMessage → Option String
  | .system c => some c
  | .developer c => some c
  | .user c => some c
  | .assistant c _ => c
  | .tool _ c => some c

/-- **Whether a message can carry the cache marker**: the marker sits on a content part, so only a message with text can carry one. A caller asks it of each message, or takes the index `lastMarkable` gives. -/
def markable (m : RequestMessage) : Bool := (msgText m).isSome

/-- **The index of the last message that can carry the cache marker**: `none` when no message can (the empty list, or one of assistant calls only). The message at that index is markable and no later one is. -/
def lastMarkable : List RequestMessage → Option Nat
  | [] => none
  | m :: ms =>
    (match lastMarkable ms with
     | some j => some (j + 1)
     | none => match markable m with
       | true => some 0
       | false => none)

/-- The marker itself: `{"type": "ephemeral"}`, the word and shape of the `cache-marker` clause the providers that need a marker accept (not a member of the pinned schema). -/
def cacheControl : Value := .obj [("type", .str "ephemeral")]

/-- A message's content as the one-part array that carries the marker: `[{"type": "text", "text": <t>, "cache_control": {"type": "ephemeral"}}]`, the text unchanged. -/
def markedContent (t : String) : Value :=
  .arr [.obj [("type", .str "text"), ("text", .str t), ("cache_control", cacheControl)]]

/-- The one-part marked array read back: the text of a content that is exactly one text part carrying `cache_control` `{"type": "ephemeral"}`. Anything else is `none`: a plain string, an array of other
parts, or a marker whose members are not exactly that (a marker member this library does not model is not read past, and the message's `content` is then refused by whoever asked, never coerced). -/
def markedText? : Value → Option String
  | .arr [part] =>
    (match get part "type", get part "text", get part "cache_control" with
     | .str "text", .str t, .obj [("type", .str "ephemeral")] => some t
     | _, _, _ => none)
  | _ => none

/-- An encoded message with its content as the one-part marked array (`markedContent <its text>`): every other member is the one `encodeMessage` writes. Only a message that can carry a marker is written
this way: `encodeMessageAt` writes a message with no text exactly as `encodeMessage` does, never through this function (the one difference for such a message is `"content": null`, which this shape replaces
with the marked array, and there is no text to carry). -/
def encodeMessageMarked : RequestMessage → Value
  | .system c => .obj [("role", .str "system"), ("content", markedContent c)]
  | .developer c => .obj [("role", .str "developer"), ("content", markedContent c)]
  | .user c => .obj [("role", .str "user"), ("content", markedContent c)]
  | .assistant c cs =>
    .obj (("role", .str "assistant") :: ("content", (match c with | none => .null | some t => markedContent t)) ::
      (match cs with | [] => [] | _ => [("tool_calls", .arr (cs.map encodeToolCall))]))
  | .tool i c => .obj [("role", .str "tool"), ("tool_call_id", .str i), ("content", markedContent c)]

/-- The message with the marker when it can carry one, and exactly `encodeMessage`'s encoding when it cannot. -/
def encodeMessageAt (m : RequestMessage) : Value :=
  if markable m then encodeMessageMarked m else encodeMessage m

/-- The messages of a request in order, each written as `encodeMessage`; `fuel` counts down to the message the caller marked, so at `some 0` the message at the front is written with the marker (when it
can carry one) and every other message of the list is written as usual. One pass: no message is encoded twice and no list of values is rebuilt. -/
def encodeMessagesFrom : Option Nat → List RequestMessage → List Value
  | _, [] => []
  | fuel, m :: ms =>
    (match fuel with | some 0 => encodeMessageAt m | _ => encodeMessage m) ::
      encodeMessagesFrom (match fuel with | some (k + 1) => some k | _ => none) ms

/-- **Encode a request with a cache marker request**: `cacheAt` is the index of the one message to mark, `none` for no marker (the encoding is then exactly `Request.encode`'s). -/
def Request.encodeWith (r : Request) (cacheAt : Option Nat) : Value :=
  .obj (("model", .str r.model) :: ("messages", .arr (encodeMessagesFrom cacheAt r.messages)) ::
    opt "tools" (fun ts => .arr (ts.map encodeTool)) (match r.tools with | [] => none | ts => some ts)
    (opt "tool_choice" encodeToolChoice r.toolChoice (opt "parallel_tool_calls" .bool r.parallelToolCalls (opt "stream" .bool r.stream
      (opt "stream_options" (fun b => .obj [("include_usage", .bool b)]) r.includeUsage (opt "max_completion_tokens" (fun n => .num (natNumber n)) r.maxCompletionTokens
        (opt "max_tokens" (fun n => .num (natNumber n)) r.maxTokens (opt "temperature" .num r.temperature (opt "top_p" .num r.topP
          (opt "reasoning" encodeReasoning r.reasoningEffort []))))))))))

/-- **The request with the marker as bytes, in one call**: the printed `encodeWith`, written straight into one buffer by `LeanJson.printBytes` (`encodeBytesWith_eq` says it is the bytes of the reference
printer, as `encodeBytes_eq` does for `encodeBytes`). -/
def Request.encodeBytesWith (r : Request) (cacheAt : Option Nat) : ByteArray := LeanJson.printBytes (r.encodeWith cacheAt)

/-- Whether an encoded message carries a cache marker in its `content` (an array with a part that has a `cache_control` member). -/
def carriesMarker (v : Value) : Bool :=
  match get v "content" with
  | .arr parts => parts.any (fun p => !(isNull (get p "cache_control")))
  | _ => false

/-- **Encode a request**: the members in a fixed order, absent ones left out. -/
def Request.encode (r : Request) : Value :=
  .obj (("model", .str r.model) :: ("messages", .arr (r.messages.map encodeMessage)) ::
    opt "tools" (fun ts => .arr (ts.map encodeTool)) (match r.tools with | [] => none | ts => some ts)
    (opt "tool_choice" encodeToolChoice r.toolChoice (opt "parallel_tool_calls" .bool r.parallelToolCalls (opt "stream" .bool r.stream
      (opt "stream_options" (fun b => .obj [("include_usage", .bool b)]) r.includeUsage (opt "max_completion_tokens" (fun n => .num (natNumber n)) r.maxCompletionTokens
        (opt "max_tokens" (fun n => .num (natNumber n)) r.maxTokens (opt "temperature" .num r.temperature (opt "top_p" .num r.topP
          (opt "reasoning" encodeReasoning r.reasoningEffort []))))))))))

/-- **The request as bytes, in one call**: the printed `encode`, written straight into one buffer by `LeanJson.printBytes` (no list of bytes: `encodeBytes_eq` says it is the bytes of the reference printer). -/
def Request.encodeBytes (r : Request) : ByteArray := LeanJson.printBytes r.encode

/-! ### Decoding: the same typed request, read back (fail closed)

Reading rules: `model` and `messages` (non-empty) are required; every other member is read when present and left `none` (or empty) when absent or `null`; a present member of the wrong type is refused, never
coerced; a `role` outside the five modelled, or a `content` that is not a string (an array of parts), is refused as not modelled, never dropped; members the type does not model are ignored. -/

def optBool (o : Value) (k : String) : Except Fault (Option Bool) :=
  match get o k with
  | .null => .ok none
  | .bool b => .ok (some b)
  | _ => .error { path := [.key k], kind := .wrongType .boolean }

def optNum (o : Value) (k : String) : Except Fault (Option Number) :=
  match get o k with
  | .null => .ok none
  | .num n => .ok (some n)
  | _ => .error { path := [.key k], kind := .wrongType .number }

def optMembers (o : Value) (k : String) : Except Fault (Option (List (String × Value))) :=
  match get o k with
  | .null => .ok none
  | .obj ms => .ok (some ms)
  | _ => .error { path := [.key k], kind := .wrongType .object }

/-- The members of an array, in order; a fault names the index. -/
def decodeEach {α : Type} (f : Value → Except Fault α) : List Value → Nat → Except Fault (List α)
  | [], _ => .ok []
  | v :: vs, i => do
    let a ← underStep (.idx i) (f v)
    let as ← decodeEach f vs (i + 1)
    pure (a :: as)

/-- A required `content`: a string, or the one-part marked text array (`markedText?`, the form the encoder writes when a caller marks the message). Any other array — two parts, an image part, a part with
no marker — is refused as not a string, never dropped, and a marked part whose text is not a string is refused too. -/
def decodeContentStr (o : Value) (k : String) : Except Fault String :=
  match get o k with
  | .null => .error { path := [.key k], kind := .missing }
  | .str s => .ok s
  | v =>
    match markedText? v with
    | some t => .ok t
    | none => .error { path := [.key k], kind := .wrongType .string }

/-- An optional `content` (an assistant message's): absent or `null` is no text, a string or the one-part marked text array is the text each carries, anything else is refused as not a string. -/
def optContentStr (o : Value) (k : String) : Except Fault (Option String) :=
  match get o k with
  | .null => .ok none
  | .str s => .ok (some s)
  | v =>
    match markedText? v with
    | some t => .ok (some t)
    | none => .error { path := [.key k], kind := .wrongType .string }

def decodeReqMessage (v : Value) : Except Fault RequestMessage :=
  match v with
  | .obj _ =>
    match reqStr v "role" with
    | .ok "system" => RequestMessage.system <$> decodeContentStr v "content"
    | .ok "developer" => RequestMessage.developer <$> decodeContentStr v "content"
    | .ok "user" => RequestMessage.user <$> decodeContentStr v "content"
    | .ok "assistant" => do
      let c ← optContentStr v "content"
      let cs ← decodeCalls v
      pure (.assistant c cs)
    | .ok "tool" => do
      let i ← reqStr v "tool_call_id"
      let c ← decodeContentStr v "content"
      pure (.tool i c)
    | .ok other => .error { path := [.key "role"], kind := .unsupported other }
    | .error e => .error e
  | _ => .error (Fault.here (.wrongType .object))

def decodeTool (v : Value) : Except Fault Tool :=
  match v with
  | .obj _ => do
    checkType v
    let fn ← reqObj v "function"
    let name ← underStep (.key "function") (reqStr fn "name")
    let description ← underStep (.key "function") (optStr fn "description")
    let parameters ← underStep (.key "function") (optMembers fn "parameters")
    let strict ← underStep (.key "function") (optBool fn "strict")
    pure { name, description, parameters, strict }
  | _ => .error (Fault.here (.wrongType .object))

/-- `tool_choice`: a word of the three, or a named function; any other word is refused as not modelled. -/
def decodeToolChoice (v : Value) : Except Fault (Option ToolChoice) :=
  match get v "tool_choice" with
  | .null => .ok none
  | .str "none" => .ok (some .never)
  | .str "auto" => .ok (some .auto)
  | .str "required" => .ok (some .required)
  | .str w => .error { path := [.key "tool_choice"], kind := .unsupported w }
  | .obj ms => underStep (.key "tool_choice") (do
      checkType (.obj ms)
      let fn ← reqObj (.obj ms) "function"
      let n ← underStep (.key "function") (reqStr fn "name")
      pure (some (.named n)))
  | _ => .error { path := [.key "tool_choice"], kind := .wrongType .object }

def decodeMessages (v : Value) : Except Fault (List RequestMessage) :=
  match get v "messages" with
  | .null => .error { path := [.key "messages"], kind := .missing }
  | .arr [] => .error { path := [.key "messages"], kind := .empty }
  | .arr xs => underStep (.key "messages") (decodeEach decodeReqMessage xs 0)
  | _ => .error { path := [.key "messages"], kind := .wrongType .array }

/-- The index of the first message whose content is the one-part marked array (`markedText?`): the marker request a request body carries, `none` when it carries none. The encoder writes at most one
(`encodeWith_at_most_one_marker`), so the first is the one a caller asked for; a body with the marker on two messages is reported at the first, and neither is dropped from the messages. -/
def firstMarkedFrom : Nat → List Value → Option Nat
  | _, [] => none
  | i, m :: ms =>
    (match markedText? (get m "content") with
     | some _ => some i
     | none => firstMarkedFrom (i + 1) ms)

/-- **The cache marker request a request body carries**: the index of the marked message, `none` when it carries none. Read from the body, beside `Request.decode`, which reads the messages. -/
def Request.markerAt (v : Value) : Option Nat :=
  match get v "messages" with
  | .arr xs => firstMarkedFrom 0 xs
  | _ => none

def decodeTools (v : Value) : Except Fault (List Tool) :=
  match get v "tools" with
  | .null => .ok []
  | .arr xs => underStep (.key "tools") (decodeEach decodeTool xs 0)
  | _ => .error { path := [.key "tools"], kind := .wrongType .array }

def decodeIncludeUsage (v : Value) : Except Fault (Option Bool) :=
  match get v "stream_options" with
  | .null => .ok none
  | .obj ms => underStep (.key "stream_options") (optBool (.obj ms) "include_usage")
  | _ => .error { path := [.key "stream_options"], kind := .wrongType .object }

/-- `reasoning`: absent or `null` is no setting; an object with a string `effort` is the level; anything else is refused (the effort is opaque: never coerced, never guessed). -/
def decodeReasoning (v : Value) : Except Fault (Option String) :=
  match get v "reasoning" with
  | .null => .ok none
  | .obj ms => underStep (.key "reasoning") (optStr (.obj ms) "effort")
  | _ => .error { path := [.key "reasoning"], kind := .wrongType .object }

def Request.decodeBody (v : Value) : Except Fault Request := do
  let model ← reqStr v "model"
  let messages ← decodeMessages v
  let tools ← decodeTools v
  let toolChoice ← decodeToolChoice v
  let parallelToolCalls ← optBool v "parallel_tool_calls"
  let stream ← optBool v "stream"
  let includeUsage ← decodeIncludeUsage v
  let maxCompletionTokens ← optNat v "max_completion_tokens"
  let maxTokens ← optNat v "max_tokens"
  let temperature ← optNum v "temperature"
  let topP ← optNum v "top_p"
  let reasoningEffort ← decodeReasoning v
  pure { model, messages, tools, toolChoice, parallelToolCalls, stream, includeUsage, maxCompletionTokens, maxTokens, temperature, topP, reasoningEffort }

/-- **Decode a request.** -/
def Request.decode (v : Value) : Except Fault Request :=
  match v with
  | .obj _ => Request.decodeBody v
  | _ => .error (Fault.here (.wrongType .object))

end VbmLlm.OpenAI
