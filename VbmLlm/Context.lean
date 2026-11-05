import VbmLlm.OpenAI.Turn
/-! # The one-action context: the prompt of each call is three parts and no transcript

A caller that keeps its working state outside the conversation sends, for every model call, only (a) a **stable system prefix** (the same bytes at every step, so a provider's prefix cache can hold it), (b) a **state
block**, an opaque string the caller rendered from its own state, and (c) the **last observation**, an opaque string, and optionally (d) an **ephemeral tail**, an opaque string the caller rendered for this call alone (notices, a budget line, the clock): it is the last message of
this request and of no other, and the caller's next call is built without it. There is no history: nothing the model said or saw earlier is in the prompt. Not here: what the
state means, how it is rendered or compacted (the caller's), prices (a parameter of whoever weighs the sizes). Theorems: `VbmLlmProofs/Context.lean`. -/
namespace VbmLlm
open OpenAI

structure OneAction where
  /-- the stable system prefix -/
  sys : String
  /-- the rendered state, opaque here -/
  state : String
  /-- the last observation, as text -/
  obs : String
  /-- the ephemeral tail, opaque here: shown in this request only, after the observation -/
  tail : Option String := none
  deriving DecidableEq, Repr

/-- The recorded conversation of one call: three items, and the tail as a fourth when there is one. -/
def OneAction.entries (c : OneAction) : List Entry := [.text .system c.sys, .text .user c.state, .text .user c.obs] ++ c.tail.toList.map (.text .user)

/-- **The messages of the call**, through the same turn machine as every other request. -/
def OneAction.messages (p : RenderPolicy) (c : OneAction) : List RequestMessage := render p c.entries

/-- The request of one call: the three parts under a model name (opaque), nothing else changed from the defaults. -/
def OneAction.request (p : RenderPolicy) (model : String) (c : OneAction) : Request := { model, messages := c.messages p }

/-- The bytes a message carries (text, tool call ids, names and arguments). -/
def RequestMessage.bytes : RequestMessage → Nat
  | .system c | .developer c | .user c => c.utf8ByteSize
  | .assistant c cs => (c.getD "").utf8ByteSize + (cs.map fun k => k.id.utf8ByteSize + k.name.utf8ByteSize + k.arguments.utf8ByteSize).sum
  | .tool i c => i.utf8ByteSize + c.utf8ByteSize

/-- The size of a prompt: the bytes of its messages. -/
def promptBytes (ms : List RequestMessage) : Nat := (ms.map RequestMessage.bytes).sum

/-- The size of the call as a function of the sizes of its three parts, and of its four with the tail. -/
def OneAction.cost (a b c : Nat) : Nat := a + b + c
def OneAction.cost4 (a b c t : Nat) : Nat := OneAction.cost a b c + t

/-- The bytes of the tail (none: no bytes). -/
def OneAction.tailBytes (c : OneAction) : Nat := (c.tail.getD "").utf8ByteSize

end VbmLlm
