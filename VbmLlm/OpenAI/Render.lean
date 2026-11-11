import VbmLlm.OpenAI.Response
import VbmLlm.Finish
import VbmLlm.Usage
import VbmLlm.OpenAI.Stream
/-! # A plain-text rendering of a decoded reply, and of a refusal

For the recorded conformance vectors (`vectors/`) and for diagnostics: one line per fact, strings quoted, nothing that depends on the machine. The rendering is **not** a wire format and
nothing parses it. -/
namespace VbmLlm.OpenAI

def optS (o : Option String) : String :=
  match o with
  | none => "none"
  | some s => s.quote

def optN (o : Option Nat) : String :=
  match o with
  | none => "none"
  | some n => toString n

/-- The digits of a lexeme's digit list, as written. -/
def digitsStr (ds : List LeanJson.Digit) : String := String.ofList (ds.map fun d => Char.ofNat (48 + d.val))

/-- The reported amount, printed as the provider wrote it: sign, integer part, fraction and exponent. -/
def optC (o : Option Amount) : String :=
  match o with
  | none => "none"
  | some n =>
    (if n.neg then "-" else "") ++ (match n.int with | .zero => "0" | .nz lead rest => digitsStr (lead.succ :: rest)) ++
      (match n.frac with | none => "" | some (a, bs) => "." ++ digitsStr (a :: bs)) ++
      (match n.exp with | none => "" | some (s, a, bs) => "e" ++ (if s then "-" else "") ++ digitsStr (a :: bs))

def ToolCall.render (c : ToolCall) : String := s!"  call id={c.id.quote} name={c.name.quote} arguments={c.arguments.quote}"

def Choice.render (c : Choice) : String :=
  let cls := match c.finishReason with
    | none => "none"
    | some w => (FinishClass.ofOpenAI w).name
  String.intercalate "\n" (
    [s!"choice index={optN c.index} finish={optS c.finishReason} class={cls}", s!"  content {optS c.message.content}", s!"  refusal {optS c.message.refusal}", s!"  reasoning {optS c.message.reasoning}"] ++
    c.message.toolCalls.map ToolCall.render)

def Usage.render (u : Usage) : String :=
  let t := match u.tokens with
    | .ok t => s!"tokens uncached={t.inputUncached} read={t.inputCacheRead} write={t.inputCacheWrite} output={t.output} reasoning={t.reasoning}"
    | .error (.cachedExceedsPrompt p c) => s!"tokens refused cachedExceedsPrompt prompt={p} cached={c}"
    | .error (.reasoningExceedsCompletion o r) => s!"tokens refused reasoningExceedsCompletion completion={o} reasoning={r}"
  s!"usage prompt={optN u.promptTokens} completion={optN u.completionTokens} total={optN u.totalTokens} cached={optN u.cachedTokens} reasoning={optN u.reasoningTokens} cost={optC u.cost}\n{t}"

def Response.render (r : Response) : String :=
  String.intercalate "\n" (
    [s!"response id={optS r.id} model={optS r.model} provider={optS r.provider}"] ++ r.choices.map Choice.render ++
    (match r.usage with | none => ["usage none"] | some u => [u.render]))

/-- `ok` and the rendering, or `error` and the refusal. -/
def renderResult : Except Fault Response → String
  | .ok r => "ok\n" ++ r.render ++ "\n"
  | .error f => "error\n" ++ f.render ++ "\n"

def StreamFault.render : StreamFault → String
  | .notJson i => s!"event {i} is neither the sentinel nor JSON"
  | .eventType i t => s!"event {i} has the type {t.quote}, which the convention does not use"
  | .chunk i f => s!"chunk {i}: {f.render}"
  | .missingIndex i => s!"chunk {i} has a choice or a tool-call fragment with no index"
  | .afterDone i => s!"event {i} follows the sentinel"
  | .callIdentity => "a completed tool call has no id or no name"
  | .noChoices => "the stream ended with the sentinel but carried no choice"

/-- The outcome of a fold: its kind, then the reply (partial for `truncated` and `error chunk`). -/
def renderOutcome : Except StreamFault Outcome → String
  | .ok (.complete r) => "complete\n" ++ r.render ++ "\n"
  | .ok (.truncated r) => "truncated\n" ++ r.render ++ "\n"
  | .ok (.errorChunk m r) => s!"error chunk message={optS m}\n" ++ r.render ++ "\n"
  | .error f => "fault\n" ++ f.render ++ "\n"

end VbmLlm.OpenAI
