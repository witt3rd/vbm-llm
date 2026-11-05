import VbmLlm.Anthropic.Event
import VbmLlmProofs.OpenAI.Response
/-! # Proofs about reading one Anthropic stream event (`VbmLlm/Anthropic/Event.lean`)

* **The event's type must agree** (`decodeEventData_type_mismatch`): an event whose stream-level type is named and differs from its data's `type` is refused; one that names the same type, or none, is read.
* **Only the convention's events are read** (`decodeItemOf_unsupported`): a data type outside the eight is refused, never guessed at; `ping` and `message_stop` are read as what they are.
* **A delta is read as it says** (`decodeDelta_text`, `decodeDelta_json`, `decodeDelta_other`): the pieces a fold concatenates are the strings the delta carries; a delta of a type not merged is `other`, never a text.
* **A block event needs its index** (`reqIndex_missing`) and an event is an object (`decodeEventData_not_object`). -/
namespace VbmLlm.Anthropic
open LeanJson
open VbmLlm.OpenAI (reqStr optNat)

/-- An event whose data is not an object is refused. -/
theorem decodeEventData_not_object (e : String) (v : Value) (h : ∀ ms, v ≠ .obj ms) (i : Item) : ∀ r, decodeEventData e v = r → r ≠ .ok i := by
  intro r hr; subst hr; cases v <;> simp [decodeEventData] <;> exact absurd rfl (h _)

/-- **The stream's event type and the data's type must agree.** -/
theorem decodeEventData_type_mismatch (ev t : String) (v : Value) (hv : ∃ ms, v = .obj ms) (ht : get v "type" = .str t) (h1 : ev ≠ "") (h2 : ev ≠ t) :
    decodeEventData ev v = .error { path := [.key "type"], kind := .unsupported ev } := by
  obtain ⟨ms, rfl⟩ := hv
  simp [decodeEventData, reqStr, ht, h1, h2]

/-- An event whose stream-level type is absent or equal to the data's is read by the data's type. -/
theorem decodeEventData_agrees (ev t : String) (v : Value) (hv : ∃ ms, v = .obj ms) (ht : get v "type" = .str t) (h : ev = "" ∨ ev = t) :
    decodeEventData ev v = decodeItemOf t v := by
  obtain ⟨ms, rfl⟩ := hv
  rcases h with rfl | rfl <;> simp [decodeEventData, reqStr, ht]

/-- A data type outside the convention's events is refused as not modelled. -/
theorem decodeItemOf_unsupported (t : String) (v : Value)
    (h : t ≠ "message_start" ∧ t ≠ "content_block_start" ∧ t ≠ "content_block_delta" ∧ t ≠ "content_block_stop" ∧ t ≠ "message_delta" ∧ t ≠ "message_stop" ∧ t ≠ "ping" ∧ t ≠ "error") :
    decodeItemOf t v = .error { path := [.key "type"], kind := .unsupported t } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  unfold decodeItemOf
  split
  all_goals first | (exfalso; simp_all; done) | rfl

theorem decodeItemOf_ping (v : Value) : ∃ r, decodeItemOf "ping" v = .ok r ∧ r = Item.ping := ⟨_, rfl, rfl⟩

theorem decodeItemOf_stop (v : Value) : ∃ r, decodeItemOf "message_stop" v = .ok r ∧ r = Item.stop := ⟨_, rfl, rfl⟩

/-- A text delta carries its text. -/
theorem decodeDelta_text (v : Value) (hv : ∃ ms, v = .obj ms) (ht : get v "type" = .str "text_delta") (s : String) (hs : get v "text" = .str s) : decodeDelta v = .ok (.text s) := by
  obtain ⟨ms, rfl⟩ := hv
  simp [decodeDelta, reqStr, ht, hs, bind, Except.bind, pure, Except.pure]

/-- A tool-input delta carries its piece of JSON text, verbatim. -/
theorem decodeDelta_json (v : Value) (hv : ∃ ms, v = .obj ms) (ht : get v "type" = .str "input_json_delta") (s : String) (hs : get v "partial_json" = .str s) : decodeDelta v = .ok (.json s) := by
  obtain ⟨ms, rfl⟩ := hv
  simp [decodeDelta, reqStr, ht, hs, bind, Except.bind, pure, Except.pure]

/-- A delta of a type that is not merged (a citations delta, say) is `other`: kept out of the reply, never read as text. -/
theorem decodeDelta_other (v : Value) (hv : ∃ ms, v = .obj ms) (t : String) (ht : get v "type" = .str t)
    (hw : t ≠ "text_delta" ∧ t ≠ "input_json_delta" ∧ t ≠ "thinking_delta" ∧ t ≠ "signature_delta") : decodeDelta v = .ok .other := by
  obtain ⟨ms, rfl⟩ := hv
  simp [decodeDelta, reqStr, ht, hw, bind, Except.bind, pure, Except.pure]

/-- A block event with no index is refused. -/
theorem reqIndex_missing (v : Value) (h : get v "index" = .null) (n : Nat) : reqIndex v ≠ .ok n := by
  simp [reqIndex, optNat, h]

end VbmLlm.Anthropic
