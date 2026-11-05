import VbmLlm.OpenAI.Response
/-! # OpenAI chat-completions: the request of one call

The wire contract of `CreateChatCompletionRequest` (schema pinned in `docs/schemas/openai-chat.md`) as a **typed request** and its encoding to a `LeanJson.Value` (printing the value to bytes is
`LeanJson.print`, proved in `vbm-json` to parse back to it). The typed request carries what a tool-using agent sends: the model (an opaque string), the messages (system, developer, user and tool
messages as text, assistant messages as text and tool calls), the tool declarations, `tool_choice`, `parallel_tool_calls`, `stream`, `stream_options.include_usage`, the token limits and the two sampling
numbers. Everything else the schema lists is not modelled (`docs/clause-index.txt` says which).

Encoding rules (each a theorem in `VbmLlmProofs/OpenAI/Request.lean`): a member that is `none` (or an empty `tools` list, or an assistant message with no calls) is **left out**, never written as `null`;
a tool call's arguments are written verbatim; a count is written as a plain natural. No client behaviour: the model name is not looked at, nothing says which fields a provider honours. -/
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

def encodeMessage : RequestMessage → Value
  | .system c => .obj [("role", .str "system"), ("content", .str c)]
  | .developer c => .obj [("role", .str "developer"), ("content", .str c)]
  | .user c => .obj [("role", .str "user"), ("content", .str c)]
  | .assistant c [] => .obj (("role", .str "assistant") :: opt "content" .str c [])
  | .assistant c cs => .obj (("role", .str "assistant") :: opt "content" .str c [("tool_calls", .arr (cs.map encodeToolCall))])
  | .tool i c => .obj [("role", .str "tool"), ("tool_call_id", .str i), ("content", .str c)]

def encodeTool (t : Tool) : Value :=
  .obj [("type", .str "function"), ("function", .obj (("name", .str t.name) :: opt "description" .str t.description (opt "parameters" .obj t.parameters (opt "strict" .bool t.strict []))))]

def encodeToolChoice : ToolChoice → Value
  | .never => .str "none"
  | .auto => .str "auto"
  | .required => .str "required"
  | .named n => .obj [("type", .str "function"), ("function", .obj [("name", .str n)])]

/-- **Encode a request**: the members in a fixed order, absent ones left out. -/
def Request.encode (r : Request) : Value :=
  .obj (("model", .str r.model) :: ("messages", .arr (r.messages.map encodeMessage)) ::
    opt "tools" (fun ts => .arr (ts.map encodeTool)) (match r.tools with | [] => none | ts => some ts)
    (opt "tool_choice" encodeToolChoice r.toolChoice (opt "parallel_tool_calls" .bool r.parallelToolCalls (opt "stream" .bool r.stream
      (opt "stream_options" (fun b => .obj [("include_usage", .bool b)]) r.includeUsage (opt "max_completion_tokens" (fun n => .num (natNumber n)) r.maxCompletionTokens
        (opt "max_tokens" (fun n => .num (natNumber n)) r.maxTokens (opt "temperature" .num r.temperature (opt "top_p" .num r.topP [])))))))))

end VbmLlm.OpenAI
