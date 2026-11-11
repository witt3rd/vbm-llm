import VbmLlm.Usage
/-! # Proofs about the usage arithmetic (`VbmLlm/Usage.lean`)

* **OpenAI's prompt count includes the cache**: the three input parts of the normalized record add up to the reported `prompt_tokens` (`openai_input_eq_prompt`), the fresh part is `prompt - cached`
  (`openai_uncached`), and a report with more cached than prompt tokens is refused, not clamped (`openai_cached_exceeds_refused`).
* **Totals add**: over a turn and over a run (`add_comm`, `add_assoc`, `zero_add`, `input_add`, `total_add`): a frame that reports nothing adds 0. -/
namespace VbmLlm
namespace Tokens

theorem add_comm (a b : Tokens) : add a b = add b a := by simp [add, Nat.add_comm]
theorem add_assoc (a b c : Tokens) : add (add a b) c = add a (add b c) := by simp [add, Nat.add_assoc]
theorem zero_add (a : Tokens) : add zero a = a := by cases a; simp [add, zero]
theorem add_zero (a : Tokens) : add a zero = a := by cases a; simp [add, zero]
theorem input_add (a b : Tokens) : (add a b).input = a.input + b.input := by simp [add, input]; omega
theorem total_add (a b : Tokens) : (add a b).total = a.total + b.total := by
  simp only [total, input_add]; simp only [add]; omega
theorem input_zero : zero.input = 0 := rfl

end Tokens

namespace OpenAI

/-- What a normalization is, exactly: it succeeds when the cached count fits in the prompt and the reasoning count in the completion, and then gives these five numbers. -/
theorem tokens_ok_iff (u : Usage) (t : Tokens) :
    u.tokens = .ok t ↔ u.cachedTokens.getD 0 ≤ u.promptTokens.getD 0 ∧ u.reasoningTokens.getD 0 ≤ u.completionTokens.getD 0 ∧
      t = ⟨u.promptTokens.getD 0 - u.cachedTokens.getD 0, u.cachedTokens.getD 0, 0, u.completionTokens.getD 0, u.reasoningTokens.getD 0⟩ := by
  unfold Usage.tokens
  by_cases h1 : u.cachedTokens.getD 0 ≤ u.promptTokens.getD 0 <;> by_cases h2 : u.reasoningTokens.getD 0 ≤ u.completionTokens.getD 0 <;> simp [h1, h2, eq_comm]

theorem openai_uncached (u : Usage) (t : Tokens) (h : u.tokens = .ok t) : t.inputUncached = u.promptTokens.getD 0 - u.cachedTokens.getD 0 := by
  rw [tokens_ok_iff] at h; obtain ⟨_, _, rfl⟩ := h; rfl

theorem openai_read (u : Usage) (t : Tokens) (h : u.tokens = .ok t) : t.inputCacheRead = u.cachedTokens.getD 0 := by
  rw [tokens_ok_iff] at h; obtain ⟨_, _, rfl⟩ := h; rfl

/-- OpenAI's convention has no cache-write count. -/
theorem openai_no_write (u : Usage) (t : Tokens) (h : u.tokens = .ok t) : t.inputCacheWrite = 0 := by
  rw [tokens_ok_iff] at h; obtain ⟨_, _, rfl⟩ := h; rfl

theorem openai_output (u : Usage) (t : Tokens) (h : u.tokens = .ok t) : t.output = u.completionTokens.getD 0 := by
  rw [tokens_ok_iff] at h; obtain ⟨_, _, rfl⟩ := h; rfl

/-- The cache is a part of the prompt: fresh + cached = the prompt the provider reported. -/
theorem openai_input_eq_prompt (u : Usage) (t : Tokens) (h : u.tokens = .ok t) : t.input = u.promptTokens.getD 0 := by
  rw [tokens_ok_iff] at h; obtain ⟨h1, _, rfl⟩ := h; simp only [Tokens.input]; omega

/-- Input plus output of the record is the prompt plus the completion the provider reported. -/
theorem openai_total (u : Usage) (t : Tokens) (h : u.tokens = .ok t) : t.total = u.promptTokens.getD 0 + u.completionTokens.getD 0 := by
  have := openai_input_eq_prompt u t h; have := openai_output u t h; simp only [Tokens.total]; omega

/-- More cached tokens than prompt tokens contradicts the convention: refused, never clamped to something that adds up. -/
theorem openai_cached_exceeds_refused (u : Usage) (t : Tokens) (h : u.promptTokens.getD 0 < u.cachedTokens.getD 0) : u.tokens ≠ .ok t := by
  intro hc; rw [tokens_ok_iff] at hc; omega

/-- More reasoning tokens than completion tokens likewise. -/
theorem openai_reasoning_exceeds_refused (u : Usage) (t : Tokens) (h : u.completionTokens.getD 0 < u.reasoningTokens.getD 0) : u.tokens ≠ .ok t := by
  intro hc; rw [tokens_ok_iff] at hc; omega

/-- A report with nothing in it is the zero record (a frame with no usage adds nothing). -/
theorem openai_empty : Usage.tokens ⟨none, none, none, none, none, none⟩ = .ok Tokens.zero := rfl

end OpenAI
end VbmLlm
