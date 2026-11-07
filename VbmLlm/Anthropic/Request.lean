import LeanJson.PrintBytes
import VbmLlm.OpenAI.Request
/-! # Anthropic messages: the request of one call

The wire contract of `MessageCreateParams` (the same pinned type document as the reply: `docs/schemas/anthropic-messages.md`) as a **typed request** and its encoding to a `LeanJson.Value`
(printing is `Request.encodeBytes`, the bytes of `LeanJson.print`). What differs from the OpenAI request is the convention: `max_tokens` is **required**, the system prompt is a member of the request (not a message), a message
is a role (`user` or `assistant`) and an **array of typed blocks**, a tool call is a `tool_use` block of the assistant and its answer a `tool_result` block (the first blocks of the next user message),
a tool declares an `input_schema`. Content is modelled as text only (an image or a document block is not modelled yet); the model name is an opaque string.

Encoding rules (each a theorem in `VbmLlmProofs/Anthropic/Request.lean`): a member that is `none` (or an empty `tools` or `stop_sequences` list) is **left out**, never written as `null`;
a count is written as a plain natural; a tool call's `input` is written as the object it is. No client behaviour: nothing says which fields a provider honours. -/
namespace VbmLlm.Anthropic
open LeanJson VbmLlm.OpenAI

/-- A block of a message to send. `toolUse.input` is the members of the input object. -/
inductive ReqBlock where
  | text (text : String)
  | toolUse (id name : String) (input : List (String × Value))
  /-- the answer to the call `toolUseId`: its text, when there is one, and whether it is an error -/
  | toolResult (toolUseId : String) (content : Option String) (isError : Option Bool)
  | thinking (thinking signature : String)
  | redactedThinking (data : String)
  deriving Repr

inductive Role where
  | user | assistant
  deriving DecidableEq, Repr

structure Message where
  role : Role
  content : List ReqBlock
  deriving Repr

/-- A tool the model may call. `inputSchema` is the members of the JSON Schema object, as the caller wrote them. -/
structure Tool where
  name : String
  description : Option String := none
  inputSchema : List (String × Value)
  strict : Option Bool := none
  deriving Repr

inductive ToolChoice where
  | auto (disableParallel : Option Bool)
  | any (disableParallel : Option Bool)
  /-- no tool call -/
  | never
  | tool (name : String) (disableParallel : Option Bool)
  deriving DecidableEq, Repr

structure Request where
  /-- an opaque string -/
  model : String
  /-- required by the convention -/
  maxTokens : Nat
  messages : List Message
  system : Option String := none
  tools : List Tool := []
  toolChoice : Option ToolChoice := none
  stream : Option Bool := none
  temperature : Option Number := none
  topP : Option Number := none
  topK : Option Nat := none
  stopSequences : List String := []
  deriving Repr

/-! ### Encoding -/

def encodeBlock : ReqBlock → Value
  | .text t => .obj [("type", .str "text"), ("text", .str t)]
  | .toolUse i n inp => .obj [("type", .str "tool_use"), ("id", .str i), ("name", .str n), ("input", .obj inp)]
  | .toolResult i c e => .obj (("type", .str "tool_result") :: ("tool_use_id", .str i) :: opt "content" .str c (opt "is_error" .bool e []))
  | .thinking t s => .obj [("type", .str "thinking"), ("thinking", .str t), ("signature", .str s)]
  | .redactedThinking d => .obj [("type", .str "redacted_thinking"), ("data", .str d)]

def Role.word : Role → String
  | .user => "user"
  | .assistant => "assistant"

def encodeMessage (m : Message) : Value := .obj [("role", .str m.role.word), ("content", .arr (m.content.map encodeBlock))]

def encodeTool (t : Tool) : Value :=
  .obj (("name", .str t.name) :: ("input_schema", .obj t.inputSchema) :: opt "description" .str t.description (opt "strict" .bool t.strict []))

def encodeToolChoice : ToolChoice → Value
  | .auto d => .obj (("type", .str "auto") :: opt "disable_parallel_tool_use" .bool d [])
  | .any d => .obj (("type", .str "any") :: opt "disable_parallel_tool_use" .bool d [])
  | .never => .obj [("type", .str "none")]
  | .tool n d => .obj (("type", .str "tool") :: ("name", .str n) :: opt "disable_parallel_tool_use" .bool d [])

/-- **Encode a request**: the members in a fixed order, absent ones left out. -/
def Request.encode (r : Request) : Value :=
  .obj (("model", .str r.model) :: ("max_tokens", .num (natNumber r.maxTokens)) :: ("messages", .arr (r.messages.map encodeMessage)) ::
    opt "system" .str r.system (opt "tools" (fun ts => .arr (ts.map encodeTool)) (match r.tools with | [] => none | ts => some ts)
      (opt "tool_choice" encodeToolChoice r.toolChoice (opt "stream" .bool r.stream (opt "temperature" .num r.temperature (opt "top_p" .num r.topP
        (opt "top_k" (fun n => .num (natNumber n)) r.topK (opt "stop_sequences" (fun ss => .arr (ss.map .str)) (match r.stopSequences with | [] => none | ss => some ss) []))))))))

/-- **The request as bytes, in one call**: the printed `encode`, written straight into one buffer by `LeanJson.printBytes` (no list of bytes: `encodeBytes_eq` says it is the bytes of the reference printer). -/
def Request.encodeBytes (r : Request) : ByteArray := LeanJson.printBytes r.encode

end VbmLlm.Anthropic
