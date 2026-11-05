import VbmLlm.Turn
import VbmLlm.OpenAI.Request
/-! # The turn machine in OpenAI's shape: one `tool` message per call

`render` shows the segments of `VbmLlm.pair` as the messages of the next request: a turn is the assistant message with its calls, then **one `tool` message per call, directly after it, in call order, carrying the
call's id**; an unanswered call is shown with the placeholder; an orphan result is plain text under the user role, never a `tool` message; text is text. The two texts are a policy of the consumer. -/
namespace VbmLlm.OpenAI

structure RenderPolicy where
  /-- what a call nobody answered is shown with -/
  placeholder : String := "[no result]"
  /-- how an orphan result is shown as user text -/
  orphan : String → String := fun c => "[tool result] " ++ c

def _root_.VbmLlm.Role.message : Role → String → RequestMessage
  | .system => .system
  | .developer => .developer
  | .user => .user
  | .assistant => fun c => .assistant (some c) []

def _root_.VbmLlm.Seg.render (p : RenderPolicy) : Seg → List RequestMessage
  | .text r c => [r.message c]
  | .orphan _ c => [.user (p.orphan c)]
  | .turn c answers => .assistant c (answers.map (·.1)) :: answers.map fun a => .tool a.1.id (a.2.getD p.placeholder)

/-- **The messages of the next request** for a recorded conversation. -/
def render (p : RenderPolicy) (items : List Entry) : List RequestMessage := (pair items).flatMap (Seg.render p)

end VbmLlm.OpenAI
