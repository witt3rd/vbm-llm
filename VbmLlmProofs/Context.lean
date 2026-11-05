import VbmLlmProofs.Turn
import VbmLlm.Context
/-! # Proofs about the one-action context (`VbmLlm/Context.lean`)

* **Built from the three parts, and only them** (`messages_eq`, `messages_inj`, `request_messages`): the prompt is exactly `[system, user, user]` of the parts, so equal parts give equal requests, different parts give
  different requests, and no history is in it (`messages_length`).
* **Well paired** (`messages_paired`): the turn machine's guarantee holds for it.
* **Stable prefix** (`prefix_stable`, `prefix_state_stable`): the system message is the first message whatever the state and the observation; two steps with the same prefix share it byte for byte.
* **Bounded size** (`bytes_eq`, `bytes_le`): the bytes of the prompt are the sum of the three parts' bytes, so a bound on each part bounds the call, and a per-step cost is a function of three sizes. -/
namespace VbmLlm
open OpenAI

theorem messages_eq (p : RenderPolicy) (c : OneAction) : c.messages p = [.system c.sys, .user c.state, .user c.obs] := rfl

theorem messages_length (p : RenderPolicy) (c : OneAction) : (c.messages p).length = 3 := rfl

theorem request_messages (p : RenderPolicy) (m : String) (c : OneAction) : (c.request p m).messages = [.system c.sys, .user c.state, .user c.obs] := rfl

/-- The request tells the three parts apart again: nothing of them is lost or mixed. -/
theorem messages_inj (p : RenderPolicy) (c d : OneAction) : c.messages p = d.messages p ↔ c = d := by
  cases c; cases d; simp [messages_eq]

theorem messages_paired (p : RenderPolicy) (c : OneAction) : Paired (c.messages p) := render_paired p c.entries

/-- **Stable prefix**: the first message is the system prefix, whatever the state and the observation are. -/
theorem prefix_stable (p : RenderPolicy) (c : OneAction) (s o : String) :
    [.system c.sys] <+: c.messages p ∧ [.system c.sys] <+: ({ c with state := s, obs := o } : OneAction).messages p :=
  ⟨⟨[.user c.state, .user c.obs], rfl⟩, ⟨[.user s, .user o], rfl⟩⟩

/-- Two steps with the same prefix and the same state share the first two messages byte for byte, whatever the observations. -/
theorem prefix_state_stable (p : RenderPolicy) (c d : OneAction) (hs : c.sys = d.sys) (ht : c.state = d.state) :
    (c.messages p).take 2 = (d.messages p).take 2 := by
  simp [messages_eq, hs, ht]

theorem bytes_eq (p : RenderPolicy) (c : OneAction) :
    promptBytes (c.messages p) = OneAction.cost c.sys.utf8ByteSize c.state.utf8ByteSize c.obs.utf8ByteSize := by
  simp [messages_eq, promptBytes, RequestMessage.bytes, OneAction.cost, Nat.add_assoc]

/-- **Bounded size**: parts within bounds give a prompt within the sum of the bounds. -/
theorem bytes_le (p : RenderPolicy) (c : OneAction) (a b o : Nat) (ha : c.sys.utf8ByteSize ≤ a) (hb : c.state.utf8ByteSize ≤ b) (ho : c.obs.utf8ByteSize ≤ o) :
    promptBytes (c.messages p) ≤ OneAction.cost a b o := by
  rw [bytes_eq]; unfold OneAction.cost; omega

end VbmLlm
