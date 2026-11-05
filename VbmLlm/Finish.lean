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
  /-- the provider ended the generation with an error (OpenRouter's `error`): what was received is partial -/
  | failed
  /-- the provider paused a long turn: it is sent back to continue -/
  | paused
  /-- a word the convention does not list -/
  | unknown
  deriving DecidableEq, Repr

namespace FinishClass

def name : FinishClass → String
  | .complete => "complete"
  | .truncated => "truncated"
  | .callsPending => "callsPending"
  | .filtered => "filtered"
  | .paused => "paused"
  | .failed => "failed"
  | .unknown => "unknown"

/-- OpenAI chat-completions `finish_reason`: `stop`, `length`, `tool_calls`, `content_filter`, and the deprecated `function_call` (a call is pending, as with `tool_calls`). -/
def ofOpenAI : String → FinishClass
  | "stop" => .complete
  | "length" => .truncated
  | "tool_calls" => .callsPending
  | "function_call" => .callsPending
  | "content_filter" => .filtered
  | _ => .unknown

/-- Anthropic messages `stop_reason`: `end_turn` and `stop_sequence` finish the turn, `max_tokens` and `model_context_window_exceeded` cut it off, `tool_use` asks for calls, `pause_turn` pauses a long turn, `refusal` is filtered. -/
def ofAnthropic : String → FinishClass
  | "end_turn" => .complete
  | "stop_sequence" => .complete
  | "max_tokens" => .truncated
  | "model_context_window_exceeded" => .truncated
  | "tool_use" => .callsPending
  | "pause_turn" => .paused
  | "refusal" => .filtered
  | _ => .unknown

/-- OpenRouter's chat-completions `finish_reason`: normalized to OpenAI's words plus `error` (a generation that failed after it had begun). -/
def ofOpenRouter : String → FinishClass
  | "error" => .failed
  | w => ofOpenAI w

end FinishClass
end VbmLlm
