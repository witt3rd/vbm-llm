import VbmLlm.OpenAI.Response
/-! # Usage arithmetic: one record, per-convention adapters

The conventions count input differently, which is where hand-written clients go wrong:
* **OpenAI chat-completions:** `prompt_tokens` **includes** the cached ones (`prompt_tokens_details.cached_tokens` is a part of it); `completion_tokens` includes the reasoning tokens.
* **Anthropic messages** (a later adapter): `input_tokens` **excludes** cache reads and writes, which are separate counts.

`Tokens` is the one normalized record: input split into fresh, read from the cache and written to the cache, then output (of which `reasoning` is a part). An adapter maps a convention's report onto it
and the arithmetic is proved (`VbmLlmProofs/Usage.lean`): the three input parts add up to the prompt the provider reported, and totals add over a turn and over a run. What is **not** here: what a token costs,
and how cached and fresh tokens are weighed (policy of the client). An unreported count is 0 in `Tokens` (a frame with no usage adds nothing); the raw report (`OpenAI.Usage`) keeps the difference. -/
namespace VbmLlm

structure Tokens where
  inputUncached : Nat
  inputCacheRead : Nat
  inputCacheWrite : Nat
  output : Nat
  /-- a part of `output` -/
  reasoning : Nat
  deriving DecidableEq, Repr

namespace Tokens

def zero : Tokens := ⟨0, 0, 0, 0, 0⟩

def add (a b : Tokens) : Tokens :=
  ⟨a.inputUncached + b.inputUncached, a.inputCacheRead + b.inputCacheRead, a.inputCacheWrite + b.inputCacheWrite, a.output + b.output, a.reasoning + b.reasoning⟩

/-- What the model was shown, whatever it cost: every input token. -/
def input (t : Tokens) : Nat := t.inputUncached + t.inputCacheRead + t.inputCacheWrite

/-- Input plus output. -/
def total (t : Tokens) : Nat := t.input + t.output

end Tokens

/-- Why a usage report cannot be normalized: it contradicts itself. -/
inductive UsageFault where
  /-- more cached tokens than prompt tokens -/
  | cachedExceedsPrompt (prompt cached : Nat)
  /-- more reasoning tokens than completion tokens -/
  | reasoningExceedsCompletion (completion reasoning : Nat)
  deriving DecidableEq, Repr

namespace OpenAI

/-- OpenAI's report as `Tokens`: fresh = prompt - cached (cached is a part of prompt), cache write 0 (the convention has no such count), output = completion. -/
def Usage.tokens (u : Usage) : Except UsageFault Tokens :=
  let p := u.promptTokens.getD 0
  let c := u.cachedTokens.getD 0
  let o := u.completionTokens.getD 0
  let r := u.reasoningTokens.getD 0
  if c ≤ p then
    if r ≤ o then .ok ⟨p - c, c, 0, o, r⟩ else .error (.reasoningExceedsCompletion o r)
  else .error (.cachedExceedsPrompt p c)

end OpenAI
end VbmLlm
