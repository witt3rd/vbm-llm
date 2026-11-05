import VbmLlm.OpenAI.Response
/-! # The tool-call turn machine: pairing what the model asked with what came back

A conversation is recorded as `Entry`s, in order: text under a role, an assistant **turn** that made tool calls, and tool **results** (each names the call it answers). Whatever order the results were recorded in,
the next request must show every call of a turn answered **exactly once**, in call order. `pair` is the machine that decides it, once for every convention; the shape of the messages (one `tool` message per call,
or one user message of results) is the adapter's (`VbmLlm/OpenAI/Turn.lean`), over the `Seg`s this produces.

The rules (each a theorem in `VbmLlmProofs/Turn.lean`):
* the **window** of a turn is the items after it up to the next assistant item (a text or another turn); a result in the window whose id is one of the turn's calls answers that call; **the newest result recorded
  for an id wins**;
* a call with no result in its window is **unanswered**: it stays in the turn with no answer (the adapter shows a placeholder), so a request is always well formed;
* a result that answers no call of the turn it sits in (its call is gone, or from an earlier turn) is an **orphan**: it is never shown as an answer, it is kept in place as a segment of its own;
* every other item of the window is kept, in order, after the turn;
* a segment never depends on what comes after the next assistant item, so **extending the conversation by an assistant item leaves everything earlier as it was** (a prefix of the output stays a prefix: cache coherence).

Not here: what text an orphan or a placeholder is shown as (the adapter's policy parameter), and whether a provider accepts the sequence (the theorem is "the sequence satisfies the documented rule"). -/
namespace VbmLlm
open OpenAI

inductive Role where
  | system | developer | user | assistant
  deriving DecidableEq, Repr

/-- What a conversation records. -/
inductive Entry where
  | text (role : Role) (content : String)
  /-- an assistant turn that made calls (a turn with none is shown as it is) -/
  | turn (content : Option String) (calls : List ToolCall)
  /-- the result of the call `callId`, wherever it was recorded -/
  | result (callId content : String)
  deriving DecidableEq, Repr

/-- What the machine decides. A turn carries each of its calls, in order, with its answer (`none`: unanswered). -/
inductive Seg where
  | text (role : Role) (content : String)
  | orphan (callId content : String)
  | turn (content : Option String) (answers : List (ToolCall × Option String))
  deriving DecidableEq, Repr

/-- A turn whose window is still open: its results so far and the other items of the window, newest first. -/
structure Open where
  content : Option String
  calls : List ToolCall
  got : List (String × String)
  kept : List Seg

def Open.close (o : Open) : List Seg :=
  .turn o.content (o.calls.map fun c => (c, (o.got.find? (·.1 == c.id)).map (·.2))) :: o.kept.reverse

def closeOpt : Option Open → List Seg
  | none => []
  | some o => o.close

/-- One item: the segments it finishes and the window it leaves open. -/
def feed (s : Option Open) : Entry → List Seg × Option Open
  | .turn c cs => (closeOpt s, some ⟨c, cs, [], []⟩)
  | .text r c =>
    match s with
    | none => ([.text r c], none)
    | some o => if r = .assistant then (o.close ++ [.text r c], none) else ([], some { o with kept := .text r c :: o.kept })
  | .result i c =>
    match s with
    | none => ([.orphan i c], none)
    | some o => if o.calls.any (·.id == i) then ([], some { o with got := (i, c) :: o.got }) else ([], some { o with kept := .orphan i c :: o.kept })

def pairFrom : Option Open → List Entry → List Seg
  | s, [] => closeOpt s
  | s, it :: rest => (feed s it).1 ++ pairFrom (feed s it).2 rest

/-- **Pair the results with the calls** of a conversation. -/
def pair (items : List Entry) : List Seg := pairFrom none items

end VbmLlm
