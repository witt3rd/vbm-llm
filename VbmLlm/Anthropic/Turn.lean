import LeanJson
import VbmLlm.Turn
import VbmLlm.Anthropic.RequestDecode
/-! # The turn machine in Anthropic's shape: one user message of results

`render` shows the segments of `VbmLlm.pair` as the messages of the next request: a turn is **one assistant message** (its text, then one `tool_use` block per call) and, when it made calls, **one user message
whose first blocks are the `tool_result`s of the turn's calls, in call order, each carrying its call's id**; the user text of the turn's window (text and orphan results, shown as text) follows the results **in
the same message** (a user message that follows a results message joins it: the results stay first). An unanswered call is shown with the placeholder; an orphan result is plain user text, never a `tool_result`. Assistant messages are never
joined (a consecutive pair is the provider's to combine), which keeps what was rendered as it was when the conversation grows by a reply. The recorded text of a call's arguments becomes the call's `input` object; a
text that is not a JSON object is shown as `badArguments` (a policy of the consumer: the provider refuses a non-object input). System and developer text is shown as user text: a consumer puts the system prompt in the
request's `system` member instead. The texts and the bad-arguments object are policy. -/
namespace VbmLlm.Anthropic
open LeanJson

structure RenderPolicy where
  /-- what a call nobody answered is shown with -/
  placeholder : String := "[no result]"
  /-- how an orphan result is shown as user text -/
  orphan : String → String := fun c => "[tool result] " ++ c
  /-- the input shown for a call whose recorded arguments are not a JSON object -/
  badArguments : List (String × Value) := []

/-- A call's recorded arguments text as the object the provider wants. -/
def inputOf (p : RenderPolicy) (args : String) : List (String × Value) :=
  match LeanJson.parseFast args.toUTF8 with
  | .ok (.obj ms) => ms
  | _ => p.badArguments

def userText (s : String) : Message := ⟨.user, [.text s]⟩

/-- The assistant message of a turn. -/
def asstOf (p : RenderPolicy) (c : Option String) (answers : List (VbmLlm.OpenAI.ToolCall × Option String)) : Message :=
  ⟨.assistant, (match c with | some t => [.text t] | none => []) ++ answers.map fun a => .toolUse a.1.id a.1.name (inputOf p a.1.arguments)⟩

/-- The results of a turn, in call order. -/
def resultsOf (p : RenderPolicy) (answers : List (VbmLlm.OpenAI.ToolCall × Option String)) : List ReqBlock :=
  answers.map fun a => .toolResult a.1.id (some (a.2.getD p.placeholder)) none

/-- A results message takes the user message that follows it. -/
def joinUser (rs : List ReqBlock) : List Message → List Message
  | n :: rest => if n.role = .user then ⟨.user, rs ++ n.content⟩ :: rest else ⟨.user, rs⟩ :: n :: rest
  | [] => [⟨.user, rs⟩]

/-- The messages of a list of segments. -/
def renderSegs (p : RenderPolicy) : List VbmLlm.Seg → List Message
  | [] => []
  | .text .assistant c :: rest => ⟨.assistant, [.text c]⟩ :: renderSegs p rest
  | .text _ c :: rest => userText c :: renderSegs p rest
  | .orphan _ c :: rest => userText (p.orphan c) :: renderSegs p rest
  | .turn c [] :: rest => asstOf p c [] :: renderSegs p rest
  | .turn c answers :: rest => asstOf p c answers :: joinUser (resultsOf p answers) (renderSegs p rest)

/-- **The messages of the next request** for a recorded conversation. -/
def render (p : RenderPolicy) (items : List VbmLlm.Entry) : List Message := renderSegs p (VbmLlm.pair items)

end VbmLlm.Anthropic
