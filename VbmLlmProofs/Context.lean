import VbmLlmProofs.Turn
import VbmLlm.Context
/-! # Proofs about the one-action context (`VbmLlm/Context.lean`)

* **Built from the parts, and only them** (`messages_eq`, `messages_inj`, `request_messages`): the prompt is exactly `[system, user, user]` of the three parts, then the tail as one more `user` message when there is
  one, so equal parts give equal requests, different parts give different requests, and no history is in it (`messages_length`, `messages_length_le`).
* **The render equation** (`messages_tail`): the messages with a tail are the messages without it followed by the tail.
* **Well paired** (`messages_paired`): the turn machine's guarantee holds for it.
* **Stable prefix** (`prefix_stable`, `prefix_state_stable`, `history_stable`, `history_prefix`): the system message is the first message whatever the rest is; the first three messages are the same bytes whatever the tail, so
  a changed tail changes only the tail's own message (`tail_changes_only_tail`).
* **Bounded size** (`bytes_eq`, `bytes_le`): the bytes of the prompt are the sum of the four parts' bytes, so a bound on each part bounds the call, and a per-step cost is a function of four sizes. -/
namespace VbmLlm
open OpenAI

theorem messages_eq (p : RenderPolicy) (c : OneAction) :
    c.messages p = [.system c.sys, .user c.state, .user c.obs] ++ c.tail.toList.map RequestMessage.user := by
  obtain ⟨s, t, o, tl⟩ := c
  cases tl <;> rfl

theorem messages_length (p : RenderPolicy) (c : OneAction) : (c.messages p).length = 3 + c.tail.toList.length := by
  simp [messages_eq]; omega

theorem messages_length_le (p : RenderPolicy) (c : OneAction) : (c.messages p).length ≤ 4 := by
  rw [messages_length]; cases c.tail <;> simp

theorem request_messages (p : RenderPolicy) (m : String) (c : OneAction) :
    (c.request p m).messages = [.system c.sys, .user c.state, .user c.obs] ++ c.tail.toList.map RequestMessage.user := messages_eq p c

/-- **The render equation**: the request with a tail is the request without it, then the tail. -/
theorem messages_tail (p : RenderPolicy) (c : OneAction) :
    c.messages p = ({ c with tail := none } : OneAction).messages p ++ c.tail.toList.map RequestMessage.user := by
  rw [messages_eq, messages_eq]; simp

/-- The request tells the parts apart again: nothing of them is lost or mixed. -/
theorem messages_inj (p : RenderPolicy) (c d : OneAction) : c.messages p = d.messages p ↔ c = d := by
  obtain ⟨s, t, o, tl⟩ := c
  obtain ⟨s', t', o', tl'⟩ := d
  cases tl <;> cases tl' <;> simp [messages_eq]

theorem messages_paired (p : RenderPolicy) (c : OneAction) : Paired (c.messages p) := render_paired p c.entries

/-- **Stable prefix**: the first message is the system prefix, whatever the state, the observation and the tail are. -/
theorem prefix_stable (p : RenderPolicy) (c : OneAction) (s o : String) (tl : Option String) :
    [.system c.sys] <+: c.messages p ∧ [.system c.sys] <+: ({ c with state := s, obs := o, tail := tl } : OneAction).messages p := by
  constructor
  · exact ⟨[.user c.state, .user c.obs] ++ c.tail.toList.map RequestMessage.user, by simp [messages_eq]⟩
  · exact ⟨[.user s, .user o] ++ tl.toList.map RequestMessage.user, by simp [messages_eq]⟩

/-- Two steps with the same prefix and the same state share the first two messages byte for byte, whatever the observations and the tails. -/
theorem prefix_state_stable (p : RenderPolicy) (c d : OneAction) (hs : c.sys = d.sys) (ht : c.state = d.state) :
    (c.messages p).take 2 = (d.messages p).take 2 := by
  simp [messages_eq, hs, ht]

/-- The three messages of the history are the same bytes whatever the tail. -/
theorem history_stable (p : RenderPolicy) (c : OneAction) (tl : Option String) :
    (({ c with tail := tl } : OneAction).messages p).take 3 = (c.messages p).take 3 := by
  simp [messages_eq]

/-- The request without a tail is a prefix of the request with any tail. -/
theorem history_prefix (p : RenderPolicy) (c : OneAction) (tl : Option String) :
    ({ c with tail := none } : OneAction).messages p <+: ({ c with tail := tl } : OneAction).messages p :=
  ⟨tl.toList.map RequestMessage.user, (messages_tail p { c with tail := tl }).symm⟩

/-- **A changed tail changes only the tail**: two requests that differ only in the tail are one request without it, then each tail. -/
theorem tail_changes_only_tail (p : RenderPolicy) (c : OneAction) (t u : Option String) :
    ∃ base, ({ c with tail := t } : OneAction).messages p = base ++ t.toList.map RequestMessage.user ∧
      ({ c with tail := u } : OneAction).messages p = base ++ u.toList.map RequestMessage.user :=
  ⟨({ c with tail := none } : OneAction).messages p, messages_tail p { c with tail := t }, messages_tail p { c with tail := u }⟩

theorem bytes_eq (p : RenderPolicy) (c : OneAction) :
    promptBytes (c.messages p) = OneAction.cost4 c.sys.utf8ByteSize c.state.utf8ByteSize c.obs.utf8ByteSize c.tailBytes := by
  obtain ⟨s, t, o, tl⟩ := c
  cases tl <;> simp [messages_eq, promptBytes, RequestMessage.bytes, OneAction.cost4, OneAction.cost, OneAction.tailBytes, Nat.add_assoc]

/-- **Bounded size**: parts within bounds give a prompt within the sum of the bounds. -/
theorem bytes_le (p : RenderPolicy) (c : OneAction) (a b o t : Nat) (ha : c.sys.utf8ByteSize ≤ a) (hb : c.state.utf8ByteSize ≤ b) (ho : c.obs.utf8ByteSize ≤ o)
    (ht : c.tailBytes ≤ t) : promptBytes (c.messages p) ≤ OneAction.cost4 a b o t := by
  rw [bytes_eq]; unfold OneAction.cost4 OneAction.cost; omega

end VbmLlm
