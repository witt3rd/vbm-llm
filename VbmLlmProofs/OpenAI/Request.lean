import VbmLlm.OpenAI.Request
import VbmLlmProofs.OpenAI.Response
/-! # Proofs about the OpenAI chat-completions request encoder (`VbmLlm/OpenAI/Request.lean`)

* **A count is written as a plain natural** (`natOf_natNumber`): reading the lexeme back gives the count, for every natural.
* **What the encoding says, member by member** (`encode_get_*`): each member of the encoded request is the value of its field, and a member whose field is absent is absent (null); an encoded request
  is an object. No member is ever written as `null`.
* **A tool call is written the way the response decoder reads it** (`decodeToolCall_encodeToolCall`): the id, the name and the arguments verbatim. -/
namespace VbmLlm.OpenAI
open LeanJson

/-! ### A count as a lexeme -/

theorem digitsVal_append (a : List Digit) (d : Digit) (acc : Nat) :
    digitsVal (a ++ [d]) acc = digitsVal a acc * 10 + d.val := by
  simp [digitsVal, List.foldl_append]

theorem leadRest_val : ∀ n : Nat, 1 ≤ n → digitsVal (leadRest n).2 ((leadRest n).1.val + 1) = n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn
    rw [leadRest]
    by_cases h : n < 10
    · simp [h, digitsVal]; omega
    · have h2 := ih (n / 10) (by omega) (by omega)
      simp only [h, dite_false, digitsVal_append]
      rw [h2]; omega

/-- **A count is written as a plain natural**: the lexeme of `n` reads back as `n`, for every natural. -/
theorem natOf_natNumber (n : Nat) : natOf (natNumber n) = some n := by
  unfold natNumber
  by_cases h : n = 0
  · simp [h, natOf]
  · simp only [h, ite_false, natOf]
    simp
    exact leadRest_val n (by omega)

/-! ### The members of an encoded request -/

theorem go_mem : ∀ (ms : List (String × Value)) (k : String) (v : Value) (acc : Value), (k, v) ∈ ms → ∃ w, (k, w) ∈ ms ∧ go ms k acc = w
  | [], _, _, _, h => by simp at h
  | (k', v') :: rest, k, v, acc, h => by
    by_cases hk : k' = k
    · subst hk
      by_cases hr : ∃ w, (k', w) ∈ rest
      · obtain ⟨w, hw⟩ := hr
        obtain ⟨w2, h2, h3⟩ := go_mem rest k' w v' hw
        exact ⟨w2, List.mem_cons_of_mem _ h2, by simpa [go] using h3⟩
      · refine ⟨v', by simp, ?_⟩
        have : ∀ p ∈ rest, p.1 ≠ k' := fun p hp he => hr ⟨p.2, by rw [← he]; exact hp⟩
        simp [go, go_absent rest k' v' this]
    · have h' : (k, v) ∈ rest := by simpa [Ne.symm hk, Prod.ext_iff] using h
      obtain ⟨w, h2, h3⟩ := go_mem rest k v _ h'
      have : (k' == k) = false := by simpa using hk
      exact ⟨w, List.mem_cons_of_mem _ h2, by simpa [go, this] using h3⟩

/-- A key that has exactly one binding reads as it. -/
theorem lookup_unique (ms : List (String × Value)) (k : String) (v : Value) (hm : (k, v) ∈ ms) (hu : ∀ p ∈ ms, p.1 = k → p.2 = v) : lookup ms k = v := by
  obtain ⟨w, hw, h⟩ := go_mem ms k v .null hm
  rw [lookup, h]; exact hu _ hw rfl

theorem mem_opt {α : Type} (k : String) (f : α → Value) (o : Option α) (rest : List (String × Value)) (p : String × Value) :
    p ∈ opt k f o rest ↔ (∃ a, o = some a ∧ p = (k, f a)) ∨ p ∈ rest := by
  cases o <;> simp [opt]

/-- The value of an optional field as the member that reads it: `null` when the field is absent. -/
def orNull {α : Type} (f : α → Value) : Option α → Value
  | none => .null
  | some a => f a

/-- No member of `ms` has the key `k`. -/
def Fresh (k : String) (ms : List (String × Value)) : Prop := ∀ p ∈ ms, p.1 ≠ k

theorem fresh_nil (k : String) : Fresh k [] := by simp [Fresh]

theorem fresh_opt {α : Type} {k k' : String} (f : α → Value) (o : Option α) {rest : List (String × Value)} (h : k' ≠ k) (hr : Fresh k rest) : Fresh k (opt k' f o rest) := by
  intro p hp; rcases (mem_opt k' f o rest p).1 hp with ⟨a, _, rfl⟩ | h2
  · exact h
  · exact hr p h2

theorem lookup_opt_ne {α : Type} {k k' : String} (f : α → Value) (o : Option α) (rest : List (String × Value)) (h : k' ≠ k) : lookup (opt k' f o rest) k = lookup rest k := by
  cases o <;> simp [opt, lookup, go, h]

theorem lookup_cons_ne {k k' : String} (v : Value) (rest : List (String × Value)) (h : k' ≠ k) : lookup ((k', v) :: rest) k = lookup rest k := by
  simp [lookup, go, h]

theorem lookup_cons_self (k : String) (v : Value) (rest : List (String × Value)) (hk : Fresh k rest) : lookup ((k, v) :: rest) k = v := by
  simp [lookup, go, go_absent rest k v hk]

theorem fresh_cons {k k' : String} (v : Value) {rest : List (String × Value)} (h : k' ≠ k) (hr : Fresh k rest) : Fresh k ((k', v) :: rest) := by
  intro p hp; rcases List.mem_cons.1 hp with rfl | h2
  · exact h
  · exact hr p h2

theorem lookup_opt_self {α : Type} (k : String) (f : α → Value) (o : Option α) (rest : List (String × Value)) (hk : Fresh k rest) : lookup (opt k f o rest) k = orNull f o := by
  cases o with
  | none => simp [opt, orNull, lookup_absent hk]
  | some a => exact lookup_cons_self k (f a) rest hk

theorem encode_get_model (r : Request) : get r.encode "model" = .str r.model := by
  unfold Request.encode
  rw [get_obj]
  exact lookup_cons_self _ _ _ (by repeat (first | exact fresh_nil _ | apply fresh_opt _ _ (by decide) | apply fresh_cons _ (by decide)))

theorem encode_get_messages (r : Request) : get r.encode "messages" = .arr (r.messages.map encodeMessage) := by
  unfold Request.encode
  rw [get_obj]
  simp (disch := decide) only [lookup_cons_ne]
  exact lookup_cons_self _ _ _ (by repeat (first | exact fresh_nil _ | apply fresh_opt _ _ (by decide) | apply fresh_cons _ (by decide)))

theorem encode_get_top_p (r : Request) : get r.encode "top_p" = orNull .num r.topP := by
  unfold Request.encode
  rw [get_obj]
  simp (disch := decide) only [lookup_cons_ne, lookup_opt_ne]
  exact lookup_opt_self _ _ _ _ (by repeat (first | exact fresh_nil _ | apply fresh_opt _ _ (by decide) | apply fresh_cons _ (by decide)))

theorem encode_get_temperature (r : Request) : get r.encode "temperature" = orNull .num r.temperature := by
  unfold Request.encode
  rw [get_obj]
  simp (disch := decide) only [lookup_cons_ne, lookup_opt_ne]
  exact lookup_opt_self _ _ _ _ (by repeat (first | exact fresh_nil _ | apply fresh_opt _ _ (by decide) | apply fresh_cons _ (by decide)))

theorem encode_get_max_tokens (r : Request) : get r.encode "max_tokens" = orNull (fun n => .num (natNumber n)) r.maxTokens := by
  unfold Request.encode
  rw [get_obj]
  simp (disch := decide) only [lookup_cons_ne, lookup_opt_ne]
  exact lookup_opt_self _ _ _ _ (by repeat (first | exact fresh_nil _ | apply fresh_opt _ _ (by decide) | apply fresh_cons _ (by decide)))

theorem encode_get_max_completion_tokens (r : Request) : get r.encode "max_completion_tokens" = orNull (fun n => .num (natNumber n)) r.maxCompletionTokens := by
  unfold Request.encode
  rw [get_obj]
  simp (disch := decide) only [lookup_cons_ne, lookup_opt_ne]
  exact lookup_opt_self _ _ _ _ (by repeat (first | exact fresh_nil _ | apply fresh_opt _ _ (by decide) | apply fresh_cons _ (by decide)))

theorem encode_get_stream_options (r : Request) : get r.encode "stream_options" = orNull (fun b => .obj [("include_usage", .bool b)]) r.includeUsage := by
  unfold Request.encode
  rw [get_obj]
  simp (disch := decide) only [lookup_cons_ne, lookup_opt_ne]
  exact lookup_opt_self _ _ _ _ (by repeat (first | exact fresh_nil _ | apply fresh_opt _ _ (by decide) | apply fresh_cons _ (by decide)))

theorem encode_get_stream (r : Request) : get r.encode "stream" = orNull .bool r.stream := by
  unfold Request.encode
  rw [get_obj]
  simp (disch := decide) only [lookup_cons_ne, lookup_opt_ne]
  exact lookup_opt_self _ _ _ _ (by repeat (first | exact fresh_nil _ | apply fresh_opt _ _ (by decide) | apply fresh_cons _ (by decide)))

theorem encode_get_parallel_tool_calls (r : Request) : get r.encode "parallel_tool_calls" = orNull .bool r.parallelToolCalls := by
  unfold Request.encode
  rw [get_obj]
  simp (disch := decide) only [lookup_cons_ne, lookup_opt_ne]
  exact lookup_opt_self _ _ _ _ (by repeat (first | exact fresh_nil _ | apply fresh_opt _ _ (by decide) | apply fresh_cons _ (by decide)))

theorem encode_get_tool_choice (r : Request) : get r.encode "tool_choice" = orNull encodeToolChoice r.toolChoice := by
  unfold Request.encode
  rw [get_obj]
  simp (disch := decide) only [lookup_cons_ne, lookup_opt_ne]
  exact lookup_opt_self _ _ _ _ (by repeat (first | exact fresh_nil _ | apply fresh_opt _ _ (by decide) | apply fresh_cons _ (by decide)))

theorem encode_get_tools (r : Request) : get r.encode "tools" = orNull (fun ts => .arr (ts.map encodeTool)) (match r.tools with | [] => none | ts => some ts) := by
  unfold Request.encode
  rw [get_obj]
  simp (disch := decide) only [lookup_cons_ne]
  exact lookup_opt_self _ _ _ _ (by repeat (first | exact fresh_nil _ | apply fresh_opt _ _ (by decide) | apply fresh_cons _ (by decide)))

/-- An encoded request is an object. -/
theorem encode_object (r : Request) : ∃ ms, r.encode = .obj ms := ⟨_, rfl⟩

theorem opt_not_null {α : Type} {k : String} {f : α → Value} (o : Option α) {rest : List (String × Value)} (hf : ∀ a, f a ≠ .null) (hr : ∀ p ∈ rest, p.2 ≠ .null) :
    ∀ p ∈ opt k f o rest, p.2 ≠ .null := by
  intro p hp; rcases (mem_opt k f o rest p).1 hp with ⟨a, _, rfl⟩ | h2
  · exact hf a
  · exact hr p h2

theorem cons_not_null {k : String} {v : Value} {rest : List (String × Value)} (hv : v ≠ .null) (hr : ∀ p ∈ rest, p.2 ≠ .null) : ∀ p ∈ (k, v) :: rest, p.2 ≠ .null := by
  intro p hp; rcases List.mem_cons.1 hp with rfl | h2
  · exact hv
  · exact hr p h2

/-- **No member of an encoded request is `null`**: an absent field is left out, never written as `null`. -/
theorem encode_members_not_null (r : Request) (ms : List (String × Value)) (h : r.encode = .obj ms) : ∀ p ∈ ms, p.2 ≠ .null := by
  unfold Request.encode at h
  cases h
  refine cons_not_null (by simp) (cons_not_null (by simp) ?_)
  repeat (first | exact fun p hp => by simp at hp | refine opt_not_null _ (by intro a; cases a <;> simp [encodeToolChoice]) ?_)

/-! ### A tool call is written the way the response decoder reads it -/

theorem decodeToolCall_encodeToolCall (c : ToolCall) : decodeToolCall (encodeToolCall c) = .ok c := by
  rw [decodeToolCall_ok_iff]
  simp [encodeToolCall, get, lookup, go]

end VbmLlm.OpenAI
