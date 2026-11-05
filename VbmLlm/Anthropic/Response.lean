import VbmLlm.OpenAI.Response
import VbmLlm.Usage
import VbmLlm.Finish
/-! # Anthropic messages: the response of one non-streaming call

The wire contract of `Message` (schema pinned in `docs/schemas/anthropic-messages.md`), read from a parsed `LeanJson.Value`, by the same rules as the OpenAI reply (`VbmLlm/OpenAI/Response.lean`): a field that is read and
present has its type or is refused; `null` and absent are the same; a count is a plain natural; unread members are ignored. What differs is the convention:

* `content` is an array of **typed blocks**; a tool call is a `tool_use` block whose `input` is a JSON **value** (not a string of JSON text: it is kept as the value), `id` and `name` required strings. A block whose `type`
  is not one this library models (a server tool block, say) is **kept raw** (`Block.other`), never dropped and never guessed at;
* `stop_reason` is kept as the provider's text (`FinishClass.ofAnthropic` classes it);
* `usage.input_tokens` **excludes** the cache: the cache reads and writes are separate counts (`Usage.tokens`: fresh = `input_tokens`, read and write as reported). OpenAI's prompt count includes the cache. -/
namespace VbmLlm.Anthropic
open LeanJson VbmLlm.OpenAI

inductive Block where
  | text (text : String)
  /-- a tool call: the provider's id, the tool's name and its input as the JSON value -/
  | toolUse (id name : String) (input : Value)
  | thinking (thinking signature : String)
  | redactedThinking (data : String)
  /-- a block of a type not modelled here, kept as it came -/
  | other (raw : Value)
  deriving Repr

structure Usage where
  inputTokens : Option Nat
  outputTokens : Option Nat
  cacheReadTokens : Option Nat
  cacheCreationTokens : Option Nat
  deriving DecidableEq, Repr

structure Response where
  id : Option String
  model : Option String
  content : List Block
  stopReason : Option String
  stopSequence : Option String
  usage : Option Usage
  deriving Repr

/-- The normalized counts: `input_tokens` is the fresh input (it excludes the cache), the cache reads and writes are their own counts, an unreported count is 0. -/
def Usage.tokens (u : Usage) : Tokens :=
  ⟨u.inputTokens.getD 0, u.cacheReadTokens.getD 0, u.cacheCreationTokens.getD 0, u.outputTokens.getD 0, 0⟩

/-- The block of the type `t`: the four modelled words are read, any other type is kept raw. -/
def decodeBlockOf (t : String) (v : Value) : Except Fault Block :=
  match t with
  | "text" => do pure (.text (← reqStr v "text"))
  | "tool_use" => do
    let id ← reqStr v "id"
    let name ← reqStr v "name"
    match get v "input" with
    | .null => .error { path := [.key "input"], kind := .missing }
    | input => pure (.toolUse id name input)
  | "thinking" => do pure (.thinking (← reqStr v "thinking") (← reqStr v "signature"))
  | "redacted_thinking" => do pure (.redactedThinking (← reqStr v "data"))
  | _ => .ok (.other v)

def decodeBlock (v : Value) : Except Fault Block :=
  match v with
  | .obj _ =>
    match reqStr v "type" with
    | .ok t => decodeBlockOf t v
    | .error e => .error e
  | _ => .error (Fault.here (.wrongType .object))

def decodeBlocks : List Value → Nat → Except Fault (List Block)
  | [], _ => .ok []
  | v :: vs, i => do
    let b ← underStep (.idx i) (decodeBlock v)
    let bs ← decodeBlocks vs (i + 1)
    pure (b :: bs)

def decodeUsage (u : Value) : Except Fault Usage := do
  let inputTokens ← optNat u "input_tokens"
  let outputTokens ← optNat u "output_tokens"
  let cacheReadTokens ← optNat u "cache_read_input_tokens"
  let cacheCreationTokens ← optNat u "cache_creation_input_tokens"
  pure { inputTokens, outputTokens, cacheReadTokens, cacheCreationTokens }

def decodeUsageOpt (v : Value) : Except Fault (Option Usage) :=
  match get v "usage" with
  | .null => .ok none
  | .obj ms => do pure (some (← underStep (.key "usage") (decodeUsage (.obj ms))))
  | _ => .error { path := [.key "usage"], kind := .wrongType .object }

/-- `content`: required array (it may be empty). -/
def decodeContent (v : Value) : Except Fault (List Block) :=
  match get v "content" with
  | .null => .error { path := [.key "content"], kind := .missing }
  | .arr xs => underStep (.key "content") (decodeBlocks xs 0)
  | _ => .error { path := [.key "content"], kind := .wrongType .array }

/-- **Decode one complete messages reply.** -/
def decode (v : Value) : Except Fault Response :=
  match v with
  | .obj _ => do
    let id ← optStr v "id"
    let model ← optStr v "model"
    let content ← decodeContent v
    let stopReason ← optStr v "stop_reason"
    let stopSequence ← optStr v "stop_sequence"
    let usage ← decodeUsageOpt v
    pure { id, model, content, stopReason, stopSequence, usage }
  | _ => .error (Fault.here (.wrongType .object))

end VbmLlm.Anthropic
