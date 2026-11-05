import VbmLlm.OpenAI.Response
import VbmLlmProofs.Wire
/-! # Proofs about the OpenAI chat-completions response decoder

Each theorem is a clause of the contract (`VbmLlm/OpenAI/Response.lean`, the header), stated of the decoder that runs. `*_ok_iff` says exactly what a value must be for a decode to succeed, and what it yields;
the refusals name the fault (path and kind). -/
namespace VbmLlm.OpenAI
open LeanJson

/-! ### Field readers -/

theorem optStr_ok_iff (o : Value) (k : String) (r : Option String) :
    optStr o k = .ok r ↔ (get o k = .null ∧ r = none) ∨ ∃ s, get o k = .str s ∧ r = some s := by
  unfold optStr; cases get o k <;> simp [eq_comm]

theorem optStr_wrong (o : Value) (k : String) (h : ∀ s, get o k ≠ .str s) (h' : get o k ≠ .null) :
    optStr o k = .error { path := [.key k], kind := .wrongType .string } := by
  unfold optStr; cases h2 : get o k <;> simp_all

theorem optNat_ok_iff (o : Value) (k : String) (r : Option Nat) :
    optNat o k = .ok r ↔ (get o k = .null ∧ r = none) ∨ ∃ n m, get o k = .num n ∧ natOf n = some m ∧ r = some m := by
  unfold optNat; cases get o k <;> simp [eq_comm]
  rename_i n; cases natOf n <;> simp [eq_comm]

theorem optNat_wrong (o : Value) (k : String) (h : ∀ n m, get o k = .num n → natOf n ≠ some m) (h' : get o k ≠ .null) :
    optNat o k = .error { path := [.key k], kind := .wrongType .natural } := by
  unfold optNat; cases h2 : get o k <;> simp_all
  rename_i n; cases h3 : natOf n <;> simp_all


theorem reqStr_ok_iff (o : Value) (k s : String) : reqStr o k = .ok s ↔ get o k = .str s := by
  unfold reqStr; cases get o k <;> simp [eq_comm]

theorem reqStr_missing (o : Value) (k : String) (h : get o k = .null) : reqStr o k = .error { path := [.key k], kind := .missing } := by
  simp [reqStr, h]

theorem reqStr_wrong (o : Value) (k : String) (h : ∀ s, get o k ≠ .str s) (h' : get o k ≠ .null) :
    reqStr o k = .error { path := [.key k], kind := .wrongType .string } := by
  unfold reqStr; cases h2 : get o k <;> simp_all

theorem reqObj_ok_iff (o : Value) (k : String) (w : Value) : reqObj o k = .ok w ↔ ∃ ms, get o k = .obj ms ∧ w = .obj ms := by
  unfold reqObj; cases get o k <;> simp [eq_comm]

theorem reqObj_missing (o : Value) (k : String) (h : get o k = .null) : reqObj o k = .error { path := [.key k], kind := .missing } := by
  simp [reqObj, h]

theorem reqObj_wrong (o : Value) (k : String) (h : ∀ ms, get o k ≠ .obj ms) (h' : get o k ≠ .null) :
    reqObj o k = .error { path := [.key k], kind := .wrongType .object } := by
  unfold reqObj; cases h2 : get o k <;> simp_all

theorem underStep_ok {α : Type} (s : Step) (e : Except Fault α) (a : α) : underStep s e = .ok a ↔ e = .ok a := by
  cases e <;> simp [underStep]

theorem underStep_error {α : Type} (s : Step) (e : Except Fault α) (f : Fault) : underStep s e = .error f ↔ ∃ g, e = .error g ∧ f = g.under s := by
  cases e <;> simp [underStep, eq_comm]

theorem optDetail_ok_iff (u : Value) (obj k : String) (r : Option Nat) :
    optDetail u obj k = .ok r ↔ (get u obj = .null ∧ r = none) ∨ ∃ ms, get u obj = .obj ms ∧ optNat (.obj ms) k = .ok r := by
  unfold optDetail; cases get u obj <;> simp [eq_comm]
  rename_i ms; rw [eq_comm, underStep_ok, eq_comm]


theorem bind_ok_iff {α β : Type} (x : Except Fault α) (f : α → Except Fault β) (b : β) :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [bind, Except.bind]

theorem pure_ok_iff {α : Type} (a b : α) : (pure a : Except Fault α) = .ok b ↔ a = b := by
  simp [pure, Except.pure]

/-! ### Tool calls (`ChatCompletionMessageToolCall`) -/

theorem checkType_ok_iff (v : Value) : checkType v = .ok () ↔ get v "type" = .null ∨ get v "type" = .str "function" := by
  unfold checkType; cases h : get v "type" <;> simp
  rename_i t; by_cases ht : t = "function" <;> simp [ht]

theorem checkType_ok_iff' (v : Value) (a : Unit) : checkType v = .ok a ↔ get v "type" = .null ∨ get v "type" = .str "function" := by
  cases a; exact checkType_ok_iff v

/-- A `type` that is a string other than `"function"` (a `custom` call, say) is refused as unsupported: it is not read as a function call. -/
theorem checkType_unsupported (v : Value) (t : String) (h : get v "type" = .str t) (ht : t ≠ "function") :
    checkType v = .error { path := [.key "type"], kind := .unsupported t } := by
  simp [checkType, h]

/-- **A tool call decodes exactly when** it is an object whose `type` is absent or `"function"`, with a string `id` and a `function` object holding string `name` and `arguments`;
it yields those strings, the arguments verbatim. -/
theorem decodeToolCall_ok_iff (v : Value) (c : ToolCall) :
    decodeToolCall v = .ok c ↔
      (∃ ms, v = .obj ms) ∧ (get v "type" = .null ∨ get v "type" = .str "function") ∧ get v "id" = .str c.id ∧
      ∃ fms, get v "function" = .obj fms ∧ get (.obj fms) "name" = .str c.name ∧ get (.obj fms) "arguments" = .str c.arguments := by
  cases v with
  | obj ms =>
    cases c with
    | mk id name arguments =>
      simp only [decodeToolCall, bind_ok_iff, pure_ok_iff, underStep_ok, checkType_ok_iff', reqStr_ok_iff, reqObj_ok_iff]
      simp
      intro _
      constructor
      · rintro ⟨a, ha, a1, ⟨ms1, h1, rfl⟩, a2, h2, a3, h3, rfl, rfl, rfl⟩
        exact ⟨ha, ms1, h1, h2, h3⟩
      · rintro ⟨ha, fms, h1, h2, h3⟩
        exact ⟨id, ha, .obj fms, ⟨fms, h1, rfl⟩, name, h2, arguments, h3, rfl, rfl, rfl⟩
  | _ => simp [decodeToolCall]

/-- A tool call of another kind (a `custom` call) is refused, never read as a function call. -/
theorem decodeToolCall_custom_refused (v : Value) (t : String) (h : get v "type" = .str t) (ht : t ≠ "function") (c : ToolCall) :
    decodeToolCall v ≠ .ok c := by
  intro hc; rw [decodeToolCall_ok_iff] at hc
  rcases hc with ⟨_, hty, _⟩; rcases hty with hty | hty <;> rw [h] at hty <;> simp at hty; exact ht hty

/-- A tool call with no `function` object is refused. -/
theorem decodeToolCall_no_function_refused (v : Value) (h : ∀ ms, get v "function" ≠ .obj ms) (c : ToolCall) : decodeToolCall v ≠ .ok c := by
  intro hc; rw [decodeToolCall_ok_iff] at hc
  rcases hc with ⟨_, _, _, fms, hf, _⟩; exact h fms hf

/-- The calls of an array decode exactly when every call does, member by member (the index only names a fault). -/
theorem decodeToolCalls_ok_iff (xs : List Value) (i : Nat) (cs : List ToolCall) :
    decodeToolCalls xs i = .ok cs ↔ Each (fun v c => decodeToolCall v = .ok c) xs cs := by
  induction xs generalizing i cs with
  | nil => simp [decodeToolCalls, each_nil_iff, eq_comm]
  | cons v vs ih =>
    simp only [decodeToolCalls, bind_ok_iff, pure_ok_iff, underStep_ok, ih, each_cons_iff]
    constructor
    · rintro ⟨c, hc, cs', hcs, rfl⟩; exact ⟨c, cs', rfl, hc, hcs⟩
    · rintro ⟨c, cs', rfl, hc, hcs⟩; exact ⟨c, hc, cs', hcs, rfl⟩

theorem decodeCalls_ok_iff (m : Value) (cs : List ToolCall) :
    decodeCalls m = .ok cs ↔ (get m "tool_calls" = .null ∧ cs = []) ∨ ∃ xs, get m "tool_calls" = .arr xs ∧ Each (fun v c => decodeToolCall v = .ok c) xs cs := by
  unfold decodeCalls
  cases get m "tool_calls" with
  | arr xs => simp [underStep_ok, decodeToolCalls_ok_iff]
  | _ => simp [eq_comm]

/-! ### Messages and choices -/

theorem decodeMessage_ok_iff (m : Value) (r : Message) :
    decodeMessage m = .ok r ↔ optStr m "content" = .ok r.content ∧ optStr m "refusal" = .ok r.refusal ∧ decodeCalls m = .ok r.toolCalls := by
  cases r with
  | mk content refusal toolCalls =>
    simp only [decodeMessage, bind_ok_iff, pure_ok_iff]
    constructor
    · rintro ⟨a, ha, b, hb, c, hc, h⟩; cases h; exact ⟨ha, hb, hc⟩
    · rintro ⟨ha, hb, hc⟩; exact ⟨_, ha, _, hb, _, hc, rfl⟩

theorem decodeChoice_ok_iff (c : Value) (r : Choice) :
    decodeChoice c = .ok r ↔ (∃ ms, c = .obj ms) ∧ optNat c "index" = .ok r.index ∧ optStr c "finish_reason" = .ok r.finishReason ∧
      ∃ ms, get c "message" = .obj ms ∧ decodeMessage (.obj ms) = .ok r.message := by
  cases c with
  | obj cms =>
    cases r with
    | mk index message finishReason =>
      simp only [decodeChoice, bind_ok_iff, pure_ok_iff, underStep_ok, reqObj_ok_iff]
      constructor
      · rintro ⟨a, ha, b, hb, m, ⟨ms, hm, rfl⟩, msg, hmsg, h⟩; cases h; exact ⟨⟨_, rfl⟩, ha, hb, ms, hm, hmsg⟩
      · rintro ⟨_, ha, hb, ms, hm, hmsg⟩; exact ⟨_, ha, _, hb, _, ⟨ms, hm, rfl⟩, _, hmsg, rfl⟩
  | _ => simp [decodeChoice]

/-- A choice with no `message` object is refused. -/
theorem decodeChoice_no_message_refused (c : Value) (h : ∀ ms, get c "message" ≠ .obj ms) (r : Choice) : decodeChoice c ≠ .ok r := by
  intro hc; rw [decodeChoice_ok_iff] at hc
  rcases hc with ⟨_, _, _, ms, hm, _⟩; exact h ms hm

theorem decodeChoices_ok_iff (xs : List Value) (i : Nat) (cs : List Choice) :
    decodeChoices xs i = .ok cs ↔ Each (fun v c => decodeChoice v = .ok c) xs cs := by
  induction xs generalizing i cs with
  | nil => simp [decodeChoices, each_nil_iff, eq_comm]
  | cons v vs ih =>
    simp only [decodeChoices, bind_ok_iff, pure_ok_iff, underStep_ok, ih, each_cons_iff]
    constructor
    · rintro ⟨c, hc, cs', hcs, rfl⟩; exact ⟨c, cs', rfl, hc, hcs⟩
    · rintro ⟨c, cs', rfl, hc, hcs⟩; exact ⟨c, hc, cs', hcs, rfl⟩

/-! ### Usage (`CompletionUsage`) -/

theorem decodeUsage_ok_iff (u : Value) (r : Usage) :
    decodeUsage u = .ok r ↔ optNat u "prompt_tokens" = .ok r.promptTokens ∧ optNat u "completion_tokens" = .ok r.completionTokens ∧ optNat u "total_tokens" = .ok r.totalTokens ∧
      optDetail u "prompt_tokens_details" "cached_tokens" = .ok r.cachedTokens ∧ optDetail u "completion_tokens_details" "reasoning_tokens" = .ok r.reasoningTokens := by
  cases r with
  | mk p c t ca re =>
    simp only [decodeUsage, bind_ok_iff, pure_ok_iff]
    constructor
    · rintro ⟨a, ha, b, hb, d, hd, e, he, f, hf, h⟩; cases h; exact ⟨ha, hb, hd, he, hf⟩
    · rintro ⟨ha, hb, hd, he, hf⟩; exact ⟨_, ha, _, hb, _, hd, _, he, _, hf, rfl⟩

theorem decodeUsageOpt_ok_iff (v : Value) (r : Option Usage) :
    decodeUsageOpt v = .ok r ↔ (get v "usage" = .null ∧ r = none) ∨ ∃ ms u, get v "usage" = .obj ms ∧ decodeUsage (.obj ms) = .ok u ∧ r = some u := by
  unfold decodeUsageOpt
  cases get v "usage" with
  | obj ms =>
    cases h : decodeUsage (.obj ms) <;> simp [underStep, h, Functor.map, Except.map]
    exact eq_comm
  | _ => simp [eq_comm]

/-! ### The reply -/

theorem decodeChoicesField_ok_iff (v : Value) (cs : List Choice) :
    decodeChoicesField v = .ok cs ↔ ∃ xs, get v "choices" = .arr xs ∧ xs ≠ [] ∧ Each (fun x c => decodeChoice x = .ok c) xs cs := by
  unfold decodeChoicesField
  cases get v "choices" with
  | arr xs => cases xs <;> simp [underStep_ok, decodeChoices_ok_iff]
  | _ => simp

/-- **The whole contract in one statement.** A value decodes to `r` exactly when it is an object, its optional `id` and `model` are strings or absent, its `choices` is a non-empty array every member of which
decodes (to `r.choices`, member by member), and its `usage` is absent or decodes (to `r.usage`). -/
theorem decode_ok_iff (v : Value) (r : Response) :
    decode v = .ok r ↔
      (∃ ms, v = .obj ms) ∧ optStr v "id" = .ok r.id ∧ optStr v "model" = .ok r.model ∧
      (∃ xs, get v "choices" = .arr xs ∧ xs ≠ [] ∧ Each (fun x c => decodeChoice x = .ok c) xs r.choices) ∧ decodeUsageOpt v = .ok r.usage := by
  cases v with
  | obj ms =>
    cases r with
    | mk id model choices usage =>
      simp only [decode, bind_ok_iff, pure_ok_iff, decodeChoicesField_ok_iff]
      constructor
      · rintro ⟨a, ha, b, hb, c, hc, d, hd, h⟩; cases h; exact ⟨⟨_, rfl⟩, ha, hb, hc, hd⟩
      · rintro ⟨_, ha, hb, hc, hd⟩; exact ⟨_, ha, _, hb, _, hc, _, hd, rfl⟩
  | _ => simp [decode]

/-- A reply that is not an object is refused. -/
theorem decode_not_object (v : Value) (h : ∀ ms, v ≠ .obj ms) (r : Response) : decode v ≠ .ok r := by
  intro hc; rw [decode_ok_iff] at hc; rcases hc with ⟨⟨ms, hms⟩, _⟩; exact h ms hms

/-- A reply with no `choices` is refused (nothing to read), and so is one whose `choices` is empty. -/
theorem decode_no_choices (v : Value) (h : get v "choices" = .null) (r : Response) : decode v ≠ .ok r := by
  intro hc; rw [decode_ok_iff] at hc; rcases hc with ⟨_, _, _, ⟨xs, hx, _⟩, _⟩; rw [h] at hx; cases hx

theorem decode_empty_choices (v : Value) (h : get v "choices" = .arr []) (r : Response) : decode v ≠ .ok r := by
  intro hc; rw [decode_ok_iff] at hc; rcases hc with ⟨_, _, _, ⟨xs, hx, hne, _⟩, _⟩; rw [h] at hx; cases hx; exact hne rfl

/-- A reply whose `choices` is not an array is refused. -/
theorem decode_choices_not_array (v : Value) (h : ∀ xs, get v "choices" ≠ .arr xs) (r : Response) : decode v ≠ .ok r := by
  intro hc; rw [decode_ok_iff] at hc; rcases hc with ⟨_, _, _, ⟨xs, hx, _⟩, _⟩; exact h xs hx

/-- A well-typed reply is **never coerced**: a present `id` that is not a string is refused. -/
theorem decode_id_wrong_type (v : Value) (h : ∀ s, get v "id" ≠ .str s) (h' : get v "id" ≠ .null) (r : Response) : decode v ≠ .ok r := by
  intro hc; rw [decode_ok_iff] at hc; rcases hc with ⟨_, hid, _⟩; rw [optStr_wrong v "id" h h'] at hid; cases hid

end VbmLlm.OpenAI
