/-! # The finish reason: a closed set of classes

A convention names why a generation stopped with its own words. The consumer needs one decision, so the words map **totally** onto a closed set of classes. The words themselves stay
available (a choice keeps the provider's text); the class never replaces them. A word the convention does not list is `unknown`: preserved, never guessed at, never an error (a provider adds
words; a decoder that refused them would stop working the day one appears). -/
namespace VbmLlm

/-- Why a generation stopped, as a decision. -/
inductive FinishClass where
  /-- the model finished its turn -/
  | complete
  /-- cut off by a length limit: the content may end mid-sentence, a tool call's arguments mid-JSON -/
  | truncated
  /-- the model asks for tool calls to be answered before it continues -/
  | callsPending
  /-- stopped by the provider's content filter or a refusal -/
  | filtered
  /-- a word the convention does not list -/
  | unknown
  deriving DecidableEq, Repr

namespace FinishClass

def name : FinishClass → String
  | .complete => "complete"
  | .truncated => "truncated"
  | .callsPending => "callsPending"
  | .filtered => "filtered"
  | .unknown => "unknown"

/-- OpenAI chat-completions `finish_reason`: `stop`, `length`, `tool_calls`, `content_filter`, and the deprecated `function_call` (a call is pending, as with `tool_calls`). -/
def ofOpenAI : String → FinishClass
  | "stop" => .complete
  | "length" => .truncated
  | "tool_calls" => .callsPending
  | "function_call" => .callsPending
  | "content_filter" => .filtered
  | _ => .unknown

end FinishClass
end VbmLlm
