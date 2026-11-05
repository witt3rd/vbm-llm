import VbmLlm.Finish
/-! # Proofs about the finish-reason classes (`VbmLlm/Finish.lean`) -/
namespace VbmLlm.FinishClass

theorem ofOpenAI_stop : ofOpenAI "stop" = .complete := rfl
theorem ofOpenAI_length : ofOpenAI "length" = .truncated := rfl
theorem ofOpenAI_tool_calls : ofOpenAI "tool_calls" = .callsPending := rfl
theorem ofOpenAI_function_call : ofOpenAI "function_call" = .callsPending := rfl
theorem ofOpenAI_content_filter : ofOpenAI "content_filter" = .filtered := rfl

/-- A word the convention does not list is `unknown`: preserved as the provider's text by the choice, never refused, never read as another class. -/
theorem ofOpenAI_unknown (s : String) (h : s ≠ "stop" ∧ s ≠ "length" ∧ s ≠ "tool_calls" ∧ s ≠ "function_call" ∧ s ≠ "content_filter") : ofOpenAI s = .unknown := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  unfold ofOpenAI; split <;> simp_all

/-- Only a `length` stop is a truncation (so a decoder that sees `truncated` may say the content or the arguments can be cut off). -/
theorem ofOpenAI_truncated_iff (s : String) : ofOpenAI s = .truncated ↔ s = "length" := by
  constructor
  · intro h; unfold ofOpenAI at h; split at h <;> simp_all
  · rintro rfl; rfl

end VbmLlm.FinishClass
