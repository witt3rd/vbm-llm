import VbmLlm.Anthropic.Response
import VbmLlmProofs.OpenAI.Response
import VbmLlmProofs.Usage
import VbmLlmProofs.Finish
/-! # Proofs about the Anthropic messages reply decoder (`VbmLlm/Anthropic/Response.lean`)

* **The usage arithmetic** (`tokens_*`): `input_tokens` **excludes** the cache, so the input the model was shown is `input_tokens + cache reads + cache writes`; with OpenAI's convention (`OpenAI.openai_input_eq_prompt`) it is the prompt.
* **The stop reason** (`ofAnthropic_*`): a total map onto the closed classes; an unlisted word is `unknown`.
* **The blocks** (`decodeBlock_*`): text, tool use (the `input` kept as the value); a block of another type is kept raw, never dropped; a block with no type or a tool use with no input is refused.
* **The reply** (`decode_ok_iff`, the refusals). -/
namespace VbmLlm.Anthropic
open LeanJson VbmLlm.OpenAI VbmLlm

/-! ### Usage -/

theorem tokens_uncached (u : Usage) : u.tokens.inputUncached = u.inputTokens.getD 0 := rfl
theorem tokens_read (u : Usage) : u.tokens.inputCacheRead = u.cacheReadTokens.getD 0 := rfl
theorem tokens_write (u : Usage) : u.tokens.inputCacheWrite = u.cacheCreationTokens.getD 0 := rfl
theorem tokens_output (u : Usage) : u.tokens.output = u.outputTokens.getD 0 := rfl

/-- **`input_tokens` excludes the cache**: the input the model was shown is the three counts added. -/
theorem tokens_input (u : Usage) : u.tokens.input = u.inputTokens.getD 0 + u.cacheReadTokens.getD 0 + u.cacheCreationTokens.getD 0 := rfl

/-- A report with no counts adds nothing. -/
theorem tokens_empty : (Usage.tokens ⟨none, none, none, none⟩) = Tokens.zero := rfl

/-! ### The stop reason -/

theorem _root_.VbmLlm.FinishClass.ofAnthropic_end_turn : FinishClass.ofAnthropic "end_turn" = .complete := rfl
theorem _root_.VbmLlm.FinishClass.ofAnthropic_stop_sequence : FinishClass.ofAnthropic "stop_sequence" = .complete := rfl
theorem _root_.VbmLlm.FinishClass.ofAnthropic_tool_use : FinishClass.ofAnthropic "tool_use" = .callsPending := rfl
theorem _root_.VbmLlm.FinishClass.ofAnthropic_pause_turn : FinishClass.ofAnthropic "pause_turn" = .paused := rfl
theorem _root_.VbmLlm.FinishClass.ofAnthropic_refusal : FinishClass.ofAnthropic "refusal" = .filtered := rfl

/-- Truncation is a class of its own: output cut by `max_tokens` or by the context window. -/
theorem _root_.VbmLlm.FinishClass.ofAnthropic_truncated_iff (w : String) : FinishClass.ofAnthropic w = .truncated ↔ w = "max_tokens" ∨ w = "model_context_window_exceeded" := by
  unfold FinishClass.ofAnthropic; split <;> simp_all

/-- A word the convention does not list is kept and classed `unknown`, never guessed. -/
theorem _root_.VbmLlm.FinishClass.ofAnthropic_unknown (w : String) (h : ∀ k ∈ ["end_turn", "stop_sequence", "max_tokens", "model_context_window_exceeded", "tool_use", "pause_turn", "refusal"], w ≠ k) :
    FinishClass.ofAnthropic w = .unknown := by
  unfold FinishClass.ofAnthropic; split <;> simp_all

/-! ### Blocks -/

/-- A block is read by its `type` word. -/
theorem decodeBlock_of_type (ms : List (String × Value)) (t : String) (h : get (.obj ms) "type" = .str t) : decodeBlock (.obj ms) = decodeBlockOf t (.obj ms) := by
  simp [decodeBlock, reqStr, h]

/-- A block with no `type` (or a `type` that is not a string) is refused. -/
theorem decodeBlock_no_type (ms : List (String × Value)) (h : ∀ t, get (.obj ms) "type" ≠ .str t) (b : Block) : decodeBlock (.obj ms) ≠ .ok b := by
  unfold decodeBlock; cases hh : get (.obj ms) "type" <;> simp_all [reqStr]

/-- A text block reads as its text. -/
theorem decodeBlock_text (ms : List (String × Value)) (s : String) (ht : get (.obj ms) "type" = .str "text") (hs : get (.obj ms) "text" = .str s) :
    decodeBlock (.obj ms) = .ok (.text s) := by
  rw [decodeBlock_of_type ms _ ht]
  simp [decodeBlockOf, (reqStr_ok_iff _ _ _).2 hs, bind, Except.bind, pure, Except.pure]

/-- **A tool call keeps its input as the value**: id and name strings, the input required. -/
theorem decodeBlock_toolUse (ms : List (String × Value)) (i n : String) (inp : Value) (ht : get (.obj ms) "type" = .str "tool_use") (hi : get (.obj ms) "id" = .str i)
    (hn : get (.obj ms) "name" = .str n) (hp : get (.obj ms) "input" = inp) (hnn : inp ≠ .null) : decodeBlock (.obj ms) = .ok (.toolUse i n inp) := by
  rw [decodeBlock_of_type ms _ ht]
  cases inp <;> simp_all [decodeBlockOf, (reqStr_ok_iff _ _ _).2 hi, (reqStr_ok_iff _ _ _).2 hn, bind, Except.bind, pure, Except.pure]

/-- A tool call with no input is refused. -/
theorem decodeBlock_toolUse_no_input (ms : List (String × Value)) (ht : get (.obj ms) "type" = .str "tool_use") (hi : ∃ s, get (.obj ms) "id" = .str s) (hn : ∃ s, get (.obj ms) "name" = .str s)
    (h : get (.obj ms) "input" = .null) (b : Block) : decodeBlock (.obj ms) ≠ .ok b := by
  obtain ⟨i, hi⟩ := hi; obtain ⟨n, hn⟩ := hn
  rw [decodeBlock_of_type ms _ ht]
  simp [decodeBlockOf, (reqStr_ok_iff _ _ _).2 hi, (reqStr_ok_iff _ _ _).2 hn, h, bind, Except.bind]

/-- Thinking blocks are read as they are (they must be sent back unchanged with their tool calls). -/
theorem decodeBlock_thinking (ms : List (String × Value)) (t g : String) (ht : get (.obj ms) "type" = .str "thinking") (h1 : get (.obj ms) "thinking" = .str t)
    (h2 : get (.obj ms) "signature" = .str g) : decodeBlock (.obj ms) = .ok (.thinking t g) := by
  rw [decodeBlock_of_type ms _ ht]
  simp [decodeBlockOf, (reqStr_ok_iff _ _ _).2 h1, (reqStr_ok_iff _ _ _).2 h2, bind, Except.bind, pure, Except.pure]

theorem decodeBlock_redacted (ms : List (String × Value)) (d : String) (ht : get (.obj ms) "type" = .str "redacted_thinking") (h : get (.obj ms) "data" = .str d) :
    decodeBlock (.obj ms) = .ok (.redactedThinking d) := by
  rw [decodeBlock_of_type ms _ ht]
  simp [decodeBlockOf, (reqStr_ok_iff _ _ _).2 h, bind, Except.bind, pure, Except.pure]

/-- **A block of a type this library does not model is kept raw**, never dropped. -/
theorem decodeBlock_other (ms : List (String × Value)) (t : String) (ht : get (.obj ms) "type" = .str t)
    (h : t ≠ "text" ∧ t ≠ "tool_use" ∧ t ≠ "thinking" ∧ t ≠ "redacted_thinking") : decodeBlock (.obj ms) = .ok (.other (.obj ms)) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [decodeBlock_of_type ms _ ht]
  simp [decodeBlockOf]

/-! ### The reply -/

theorem decodeBlocks_ok_iff (xs : List Value) (i : Nat) (bs : List Block) :
    decodeBlocks xs i = .ok bs ↔ Each (fun v b => decodeBlock v = .ok b) xs bs := by
  induction xs generalizing i bs with
  | nil => simp [decodeBlocks, each_nil_iff, eq_comm]
  | cons v vs ih =>
    simp only [decodeBlocks, bind_ok_iff, pure_ok_iff, underStep_ok, ih, each_cons_iff]
    constructor
    · rintro ⟨c, hc, cs', hcs, rfl⟩; exact ⟨c, cs', rfl, hc, hcs⟩
    · rintro ⟨c, cs', rfl, hc, hcs⟩; exact ⟨c, hc, cs', hcs, rfl⟩

theorem decodeContent_ok_iff (v : Value) (bs : List Block) :
    decodeContent v = .ok bs ↔ ∃ xs, get v "content" = .arr xs ∧ Each (fun x b => decodeBlock x = .ok b) xs bs := by
  unfold decodeContent
  cases get v "content" with
  | arr xs => simp [underStep_ok, decodeBlocks_ok_iff]
  | _ => simp

theorem decodeUsage_ok_iff (u : Value) (r : Usage) :
    decodeUsage u = .ok r ↔ optNat u "input_tokens" = .ok r.inputTokens ∧ optNat u "output_tokens" = .ok r.outputTokens ∧
      optNat u "cache_read_input_tokens" = .ok r.cacheReadTokens ∧ optNat u "cache_creation_input_tokens" = .ok r.cacheCreationTokens := by
  cases r with
  | mk a b c d =>
    simp only [decodeUsage, bind_ok_iff, pure_ok_iff]
    constructor
    · rintro ⟨a', ha, b', hb, c', hc, d', hd, h⟩; cases h; exact ⟨ha, hb, hc, hd⟩
    · rintro ⟨ha, hb, hc, hd⟩; exact ⟨_, ha, _, hb, _, hc, _, hd, rfl⟩

/-- **The whole contract in one statement.** -/
theorem decode_ok_iff (v : Value) (r : Response) :
    decode v = .ok r ↔
      (∃ ms, v = .obj ms) ∧ optStr v "id" = .ok r.id ∧ optStr v "model" = .ok r.model ∧ decodeContent v = .ok r.content ∧
      optStr v "stop_reason" = .ok r.stopReason ∧ optStr v "stop_sequence" = .ok r.stopSequence ∧ decodeUsageOpt v = .ok r.usage := by
  cases v with
  | obj ms =>
    cases r with
    | mk id model content stopReason stopSequence usage =>
      simp only [decode, bind_ok_iff, pure_ok_iff]
      constructor
      · rintro ⟨a, ha, b, hb, c, hc, d, hd, e, he, f, hf, h⟩; cases h; exact ⟨⟨_, rfl⟩, ha, hb, hc, hd, he, hf⟩
      · rintro ⟨_, ha, hb, hc, hd, he, hf⟩; exact ⟨_, ha, _, hb, _, hc, _, hd, _, he, _, hf, rfl⟩
  | _ => simp [decode]

theorem decode_not_object (v : Value) (h : ∀ ms, v ≠ .obj ms) (r : Response) : decode v ≠ .ok r := by
  intro hc; rw [decode_ok_iff] at hc; obtain ⟨⟨ms, hms⟩, _⟩ := hc; exact h ms hms

/-- A reply with no `content` array is refused. -/
theorem decode_no_content (v : Value) (h : get v "content" = .null) (r : Response) : decode v ≠ .ok r := by
  intro hc; rw [decode_ok_iff] at hc; obtain ⟨_, _, _, hc, _⟩ := hc
  rw [decodeContent_ok_iff] at hc; obtain ⟨xs, hx, _⟩ := hc; rw [h] at hx; cases hx

theorem decode_content_not_array (v : Value) (h : ∀ xs, get v "content" ≠ .arr xs) (r : Response) : decode v ≠ .ok r := by
  intro hc; rw [decode_ok_iff] at hc; obtain ⟨_, _, _, hc, _⟩ := hc
  rw [decodeContent_ok_iff] at hc; obtain ⟨xs, hx, _⟩ := hc; exact h xs hx

end VbmLlm.Anthropic
