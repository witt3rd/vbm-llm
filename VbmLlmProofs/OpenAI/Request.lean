import LeanJsonProofs.PrintBytes
import VbmLlm.OpenAI.Request
import VbmLlmProofs.OpenAI.Response
/-! # Proofs about the OpenAI chat-completions request encoder (`VbmLlm/OpenAI/Request.lean`)

* **A count is written as a plain natural** (`natOf_natNumber`): reading the lexeme back gives the count, for every natural.
* **What the encoding says, member by member** (`encode_get_*`): each member of the encoded request is the value of its field, and a member whose field is absent is absent (null); an encoded request
  is an object. The reasoning effort is written as the object `{"effort": <level>}` under `reasoning`, after `top_p`, and only when it is set (`encode_get_reasoning`, `encode_reasoning_absent`); the level is
  an opaque string, read back as itself (`decodeReasoning_encodeReasoning`). No member of the request object is ever written as `null` (inside a message, an assistant message with calls and no text is written with `"content": null`: `encodeMessage_assistant_calls_no_text`).
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

/-- **The reasoning effort is written as the object `{"effort": <level>}`**: absent when there is no setting, never `null`. -/
theorem encode_get_reasoning (r : Request) : get r.encode "reasoning" = orNull encodeReasoning r.reasoningEffort := by
  unfold Request.encode
  rw [get_obj]
  simp (disch := decide) only [lookup_cons_ne, lookup_opt_ne]
  exact lookup_opt_self _ _ _ _ (by repeat (first | exact fresh_nil _ | apply fresh_opt _ _ (by decide) | apply fresh_cons _ (by decide)))

/-- The `effort` of a written reasoning object is the level itself. -/
theorem encodeReasoning_get (s : String) : get (encodeReasoning s) "effort" = .str s := by
  simp [encodeReasoning, get, lookup, go]

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

/-- **No member of an encoded request object is `null`**: an absent field is left out, never written as `null` (the one `null` is inside a message: `encodeMessage_assistant_calls_no_text`). -/
theorem encode_members_not_null (r : Request) (ms : List (String × Value)) (h : r.encode = .obj ms) : ∀ p ∈ ms, p.2 ≠ .null := by
  unfold Request.encode at h
  cases h
  refine cons_not_null (by simp) (cons_not_null (by simp) ?_)
  repeat (first | exact fun p hp => by simp at hp | refine opt_not_null _ (by intro a; cases a <;> simp [encodeToolChoice, encodeReasoning]) ?_)

/-! ### A tool call is written the way the response decoder reads it -/

theorem decodeToolCall_encodeToolCall (c : ToolCall) : decodeToolCall (encodeToolCall c) = .ok c := by
  rw [decodeToolCall_ok_iff]
  simp [encodeToolCall, get, lookup, go]

/-! ### The round trip -/

theorem decodeToolCalls_encode : ∀ (cs : List ToolCall) (i : Nat), decodeToolCalls (cs.map encodeToolCall) i = .ok cs
  | [], _ => by simp [decodeToolCalls]
  | c :: cs, i => by
    simp [decodeToolCalls, underStep, decodeToolCall_encodeToolCall, decodeToolCalls_encode cs (i + 1), bind, Except.bind, pure, Except.pure]

theorem decodeToolCalls_encode_cons (x : ToolCall) (xs : List ToolCall) (i : Nat) :
    decodeToolCalls (encodeToolCall x :: xs.map encodeToolCall) i = .ok (x :: xs) := by
  simpa using decodeToolCalls_encode (x :: xs) i

theorem decodeEach_encode {α : Type} (f : Value → Except Fault α) (g : α → Value) (hg : ∀ a, f (g a) = .ok a) :
    ∀ (as : List α) (i : Nat), decodeEach f (as.map g) i = .ok as
  | [], _ => by simp [decodeEach]
  | a :: as, i => by
    simp [decodeEach, underStep, hg, bind, Except.bind, pure, Except.pure]
    rw [decodeEach_encode f g hg as (i + 1)]

theorem decodeReqMessage_encodeMessage (m : RequestMessage) : decodeReqMessage (encodeMessage m) = .ok m := by
  cases m with
  | system c => simp [encodeMessage, decodeReqMessage, decodeContentStr, reqStr, get, lookup, go, Functor.map, Except.map]
  | developer c => simp [encodeMessage, decodeReqMessage, decodeContentStr, reqStr, get, lookup, go, Functor.map, Except.map]
  | user c => simp [encodeMessage, decodeReqMessage, decodeContentStr, reqStr, get, lookup, go, Functor.map, Except.map]
  | tool i c => simp [encodeMessage, decodeReqMessage, decodeContentStr, reqStr, get, lookup, go, bind, Except.bind, pure, Except.pure]
  | assistant c cs =>
    cases cs with
    | nil => cases c <;> simp [encodeMessage, decodeReqMessage, optContentStr, reqStr, decodeCalls, opt, get, lookup, go, bind, Except.bind, pure, Except.pure]
    | cons x xs =>
      cases c <;> simp [encodeMessage, orNullStr, decodeReqMessage, optContentStr, reqStr, decodeCalls, get, lookup, go, underStep, decodeToolCalls_encode_cons, bind, Except.bind, pure, Except.pure]

/-- An assistant message with tool calls and no text is written with `"content": null` (the decoder reads it back as no text: `decodeReqMessage_encodeMessage`). -/
theorem encodeMessage_assistant_calls_no_text (x : ToolCall) (xs : List ToolCall) :
    get (encodeMessage (.assistant none (x :: xs))) "content" = .null := by
  simp [encodeMessage, orNullStr, get, lookup, go]

/-- The `function` object of an encoded tool, member by member. -/
theorem tool_fn_get (t : Tool) :
    get (.obj (("name", .str t.name) :: opt "description" .str t.description (opt "parameters" .obj t.parameters (opt "strict" .bool t.strict [])))) "name" = .str t.name ∧
    get (.obj (("name", .str t.name) :: opt "description" .str t.description (opt "parameters" .obj t.parameters (opt "strict" .bool t.strict [])))) "description" = orNull .str t.description ∧
    get (.obj (("name", .str t.name) :: opt "description" .str t.description (opt "parameters" .obj t.parameters (opt "strict" .bool t.strict [])))) "parameters" = orNull .obj t.parameters ∧
    get (.obj (("name", .str t.name) :: opt "description" .str t.description (opt "parameters" .obj t.parameters (opt "strict" .bool t.strict [])))) "strict" = orNull .bool t.strict := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [get_obj]
  · exact lookup_cons_self _ _ _ (by repeat (first | exact fresh_nil _ | apply fresh_opt _ _ (by decide) | apply fresh_cons _ (by decide)))
  · rw [lookup_cons_ne _ _ (by decide)]
    exact lookup_opt_self _ _ _ _ (by repeat (first | exact fresh_nil _ | apply fresh_opt _ _ (by decide) | apply fresh_cons _ (by decide)))
  · rw [lookup_cons_ne _ _ (by decide), lookup_opt_ne _ _ _ (by decide)]
    exact lookup_opt_self _ _ _ _ (by repeat (first | exact fresh_nil _ | apply fresh_opt _ _ (by decide) | apply fresh_cons _ (by decide)))
  · rw [lookup_cons_ne _ _ (by decide), lookup_opt_ne _ _ _ (by decide), lookup_opt_ne _ _ _ (by decide)]
    exact lookup_opt_self _ _ _ _ (by repeat (first | exact fresh_nil _ | apply fresh_opt _ _ (by decide) | apply fresh_cons _ (by decide)))

theorem decodeTool_encodeTool (t : Tool) : decodeTool (encodeTool t) = .ok t := by
  obtain ⟨h1, h2, h3, h4⟩ := tool_fn_get t
  obtain ⟨ms, hms⟩ : ∃ ms, encodeTool t = .obj ms := ⟨_, rfl⟩
  have hty : get (encodeTool t) "type" = .str "function" := by simp [encodeTool, get, lookup, go]
  have hfn : get (encodeTool t) "function" = .obj (("name", .str t.name) :: opt "description" .str t.description (opt "parameters" .obj t.parameters (opt "strict" .bool t.strict []))) := by
    simp [encodeTool, get, lookup, go]
  rw [hms] at hty hfn ⊢
  unfold decodeTool
  simp only [bind, Except.bind, checkType, hty, reqObj, hfn, underStep, reqStr, h1, optStr, optMembers, optBool]
  cases t with
  | mk name description parameters strict =>
    cases description <;> cases parameters <;> cases strict <;> simp_all [orNull, pure, Except.pure]

/-! ### Reading what was written: each reader, then the request -/

theorem optBool_orNull (v : Value) (k : String) (o : Option Bool) (h : get v k = orNull .bool o) : optBool v k = .ok o := by
  cases o <;> simp [optBool, h, orNull]

theorem optNum_orNull (v : Value) (k : String) (o : Option Number) (h : get v k = orNull .num o) : optNum v k = .ok o := by
  cases o <;> simp [optNum, h, orNull]

theorem optNat_orNull (v : Value) (k : String) (o : Option Nat) (h : get v k = orNull (fun n => .num (natNumber n)) o) : optNat v k = .ok o := by
  cases o <;> simp [optNat, h, orNull, natOf_natNumber]

theorem decodeMessages_encode (v : Value) (ms : List RequestMessage) (hne : ms ≠ []) (h : get v "messages" = .arr (ms.map encodeMessage)) : decodeMessages v = .ok ms := by
  cases ms with
  | nil => exact absurd rfl hne
  | cons m ms =>
    simp only [decodeMessages, List.map_cons, h]
    rw [← List.map_cons, underStep_ok, decodeEach_encode _ _ decodeReqMessage_encodeMessage]

theorem decodeTools_encode (v : Value) (ts : List Tool) (h : get v "tools" = orNull (fun ts => .arr (ts.map encodeTool)) (match ts with | [] => none | ts => some ts)) :
    decodeTools v = .ok ts := by
  cases ts with
  | nil => simp [decodeTools, h, orNull]
  | cons t ts =>
    simp only [orNull] at h
    simp only [decodeTools, h, List.map_cons]
    rw [← List.map_cons, underStep_ok, decodeEach_encode _ _ decodeTool_encodeTool]

theorem decodeToolChoice_encode (v : Value) (o : Option ToolChoice) (h : get v "tool_choice" = orNull encodeToolChoice o) : decodeToolChoice v = .ok o := by
  cases o with
  | none => simp [decodeToolChoice, h, orNull]
  | some c =>
    cases c <;> simp only [decodeToolChoice, h, orNull, encodeToolChoice]
    simp [checkType, reqObj, reqStr, get, lookup, go, underStep, bind, Except.bind, pure, Except.pure]

theorem decodeIncludeUsage_encode (v : Value) (o : Option Bool) (h : get v "stream_options" = orNull (fun b => .obj [("include_usage", .bool b)]) o) : decodeIncludeUsage v = .ok o := by
  cases o <;> simp only [decodeIncludeUsage, h, orNull]
  simp [optBool, get, lookup, go, underStep]

/-- The reasoning effort, read back from its own object: `{"effort": <level>}` is the level. -/
theorem optStr_encodeReasoning (s : String) : optStr (encodeReasoning s) "effort" = .ok (some s) := by
  simp [encodeReasoning, optStr, get, lookup, go]

theorem decodeReasoning_encode (v : Value) (o : Option String) (h : get v "reasoning" = orNull encodeReasoning o) : decodeReasoning v = .ok o := by
  cases o with
  | none => simp [decodeReasoning, h, orNull]
  | some s =>
    simp only [orNull] at h
    unfold decodeReasoning
    rw [h]
    simp [encodeReasoning, underStep, optStr, get, lookup, go]

/-- **The round trip.** Decoding an encoded request gives the request back, for every request that has a message (the schema requires one). -/
theorem decode_encode (r : Request) (h : r.messages ≠ []) : Request.decode r.encode = .ok r := by
  obtain ⟨ms, hms⟩ := encode_object r
  have g1 := encode_get_model r
  have g2 := encode_get_messages r
  have g3 := encode_get_tools r
  have g4 := encode_get_tool_choice r
  have g5 := encode_get_parallel_tool_calls r
  have g6 := encode_get_stream r
  have g7 := encode_get_stream_options r
  have g8 := encode_get_max_completion_tokens r
  have g9 := encode_get_max_tokens r
  have g10 := encode_get_temperature r
  have g11 := encode_get_top_p r
  have g12 := encode_get_reasoning r
  rw [hms] at g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 ⊢
  simp only [Request.decode, Request.decodeBody, bind, Except.bind, (reqStr_ok_iff _ _ _).2 g1, decodeMessages_encode _ _ h g2, decodeTools_encode _ _ g3, decodeToolChoice_encode _ _ g4,
    optBool_orNull _ _ _ g5, optBool_orNull _ _ _ g6, decodeIncludeUsage_encode _ _ g7, optNat_orNull _ _ _ g8, optNat_orNull _ _ _ g9, optNum_orNull _ _ _ g10, optNum_orNull _ _ _ g11,
    decodeReasoning_encode _ _ g12, pure, Except.pure]

/-! ### Refusals (fail closed) -/

/-- A request that is not an object is refused. -/
theorem Request.decode_not_object (v : Value) (h : ∀ ms, v ≠ .obj ms) (r : Request) : Request.decode v ≠ .ok r := by
  cases v <;> simp [Request.decode] <;> exact absurd rfl (h _)

/-- A request with no `messages` is refused, and so is one whose `messages` is empty or not an array. -/
theorem decodeMessages_none (v : Value) (h : get v "messages" = .null) (ms : List RequestMessage) : decodeMessages v ≠ .ok ms := by
  simp [decodeMessages, h]

theorem decodeMessages_empty (v : Value) (h : get v "messages" = .arr []) (ms : List RequestMessage) : decodeMessages v ≠ .ok ms := by
  simp [decodeMessages, h]

theorem decodeMessages_not_array (v : Value) (h : ∀ xs, get v "messages" ≠ .arr xs) (h' : get v "messages" ≠ .null) (ms : List RequestMessage) : decodeMessages v ≠ .ok ms := by
  unfold decodeMessages; cases h2 : get v "messages" <;> simp_all

/-- A role the library does not model (the deprecated `function` role, say) is refused, never read as another role. -/
theorem decodeReqMessage_unsupported_role (v : Value) (hv : ∃ ms, v = .obj ms) (w : String) (h : get v "role" = .str w)
    (hw : w ≠ "system" ∧ w ≠ "developer" ∧ w ≠ "user" ∧ w ≠ "assistant" ∧ w ≠ "tool") :
    decodeReqMessage v = .error { path := [.key "role"], kind := .unsupported w } := by
  obtain ⟨ms, rfl⟩ := hv
  obtain ⟨h1, h2, h3, h4, h5⟩ := hw
  simp only [decodeReqMessage, reqStr, h]

/-- `markedText?` on anything but an array of exactly one part is `none`, and on an array of two or more parts too: the marked form is exactly one part. -/
theorem markedText?_null : markedText? (.null) = none := rfl
theorem markedText?_str (s : String) : markedText? (.str s) = none := rfl
theorem markedText?_bool (b : Bool) : markedText? (.bool b) = none := rfl
theorem markedText?_num (n : Number) : markedText? (.num n) = none := rfl
theorem markedText?_arr_nil : markedText? (.arr ([] : List Value)) = none := rfl
theorem markedText?_arr_two (a b : Value) (rest : List Value) : markedText? (.arr (a :: b :: rest)) = none := rfl

/-- **What a required `content` reads as**: a string, or the one-part marked text array (and nothing else). -/
theorem decodeContentStr_ok_iff (o : Value) (k : String) (s : String) :
    decodeContentStr o k = .ok s ↔ (get o k = .str s ∨ markedText? (get o k) = some s) := by
  unfold decodeContentStr
  cases hg : get o k
  case str t => simp [markedText?_str]
  case null => simp [markedText?_null]
  case bool b => simp [markedText?_bool]
  case num n => simp [markedText?_num]
  case obj m => cases h2 : markedText? (Value.obj m) <;> simp [h2]
  case arr xs => cases h2 : markedText? (Value.arr xs) <;> simp [h2]

/-- A `content` that is neither a string nor the one-part marked text array is refused: it is never dropped, and never read as another form. -/
theorem decodeContentStr_not_str (o : Value) (k : String) (h : ∀ s, get o k ≠ .str s) (hm : ∀ t, markedText? (get o k) ≠ some t) (s : String) :
    decodeContentStr o k ≠ .ok s := by
  intro hc
  rcases (decodeContentStr_ok_iff o k s).1 hc with h1 | h2
  · exact h _ h1
  · exact hm _ h2

/-- A `content` that is neither a string nor the one-part marked text array (an array of two parts, an image part, a part with no marker: `markedText?` is `none`) is refused for a user message,
never dropped. -/
theorem decodeReqMessage_user_content (v : Value) (hv : ∃ ms, v = .obj ms) (h : get v "role" = .str "user") (hc : ∀ s, get v "content" ≠ .str s)
    (hm : ∀ t, markedText? (get v "content") ≠ some t) (m : RequestMessage) :
    decodeReqMessage v ≠ .ok m := by
  obtain ⟨ms, rfl⟩ := hv
  intro hcontra
  simp only [decodeReqMessage, reqStr, h, Functor.map, Except.map] at hcontra
  cases h5 : decodeContentStr (Value.obj ms) "content"
  case error e => simp [h5] at hcontra
  case ok a =>
    simp [h5] at hcontra
    exact decodeContentStr_not_str _ _ hc hm a h5

/-- A `tool_choice` word outside `none`, `auto`, `required` is refused. -/
theorem decodeToolChoice_unsupported (v : Value) (w : String) (h : get v "tool_choice" = .str w) (hw : w ≠ "none" ∧ w ≠ "auto" ∧ w ≠ "required") :
    decodeToolChoice v = .error { path := [.key "tool_choice"], kind := .unsupported w } := by
  obtain ⟨h1, h2, h3⟩ := hw
  simp only [decodeToolChoice, h]

/-- Nothing is coerced: a present `stream` that is not a boolean is refused. -/
theorem optBool_wrong (o : Value) (k : String) (h : ∀ b, get o k ≠ .bool b) (h' : get o k ≠ .null) :
    optBool o k = .error { path := [.key k], kind := .wrongType .boolean } := by
  unfold optBool; cases h2 : get o k <;> simp_all

/-! ### What was read is stable under writing -/

theorem decodeEach_cons_ne_nil {α : Type} (f : Value → Except Fault α) (v : Value) (vs : List Value) (i : Nat) (as : List α) (h : decodeEach f (v :: vs) i = .ok as) : as ≠ [] := by
  simp only [decodeEach, bind_ok_iff, pure_ok_iff] at h
  obtain ⟨_, _, _, _, rfl⟩ := h
  simp

theorem decodeMessages_ne_nil (v : Value) (ms : List RequestMessage) (h : decodeMessages v = .ok ms) : ms ≠ [] := by
  unfold decodeMessages at h
  cases hg : get v "messages" <;> simp only [hg] at h <;> try (cases h; done)
  rename_i xs
  cases xs with
  | nil => cases h
  | cons x xs => exact decodeEach_cons_ne_nil _ _ _ _ _ ((underStep_ok _ _ _).1 h)

/-- **A request that decodes is read back from its own encoding**: whatever a decode yields, `decode (encode r) = r` (a decoded request always has a message). -/
theorem decode_ok_stable (v : Value) (r : Request) (h : Request.decode v = .ok r) : Request.decode r.encode = .ok r := by
  apply decode_encode
  cases v <;> simp only [Request.decode] at h <;> try (cases h; done)
  simp only [Request.decodeBody, bind_ok_iff, pure_ok_iff] at h
  obtain ⟨_, _, ms, hms, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := h
  exact decodeMessages_ne_nil _ _ hms

/-- **The request as bytes is the reference printer's**: `encodeBytes r` is exactly the bytes of `print (encode r)` (from `printBytes_eq`), so everything proved of the printed request holds of these bytes. -/
theorem Request.encodeBytes_eq (r : Request) : r.encodeBytes = ⟨(LeanJson.print r.encode).toArray⟩ := LeanJson.printBytes_eq r.encode

/-- **The request with a marker request as bytes is the reference printer's**: `encodeBytesWith r cacheAt` is exactly the bytes of `print (encodeWith r cacheAt)` (from `printBytes_eq`), so everything proved of
the printed request holds of these bytes. -/
theorem Request.encodeBytesWith_eq (r : Request) (cacheAt : Option Nat) :
    r.encodeBytesWith cacheAt = ⟨(LeanJson.print (r.encodeWith cacheAt)).toArray⟩ := LeanJson.printBytes_eq (r.encodeWith cacheAt)

/-! ### The cache marker: what the encoder writes when a caller names the message

* **No marker request is today's encoding** (`encodeWith_none`): `encodeWith r none = r.encode`, for every request.
* **A markable message is marked and nothing else moves** (`encodeWith_some_markable`): the encoded messages are the plain ones with position `i` replaced by the marked message, whose `content` is the
  one-part array `markedContent t` carrying the **same text** the message carried (the plain message of that text writes it as the string `content`: `encodeMessage_content_text`), reading that content back
  gives that text (`markedText?_markedContent`), and the marker request read from that body is `some i` (`markerAt_encodeWith_some`).
* **An index that cannot be honoured writes no marker** (`encodeWith_some_unmarkable`): a message with no text cannot carry one, and an index past the end names no message, so the encoding is exactly
  `r.encode`.
* **`lastMarkable` is the index a caller wants** (`lastMarkable_spec`, with `lastMarkable_some_markable`, `lastMarkable_no_later` and `lastMarkable_none_iff`): the message at the index it gives can
  carry the marker, no later message can, and it is `none` exactly when no message can.
* **At most one message of an encoding carries a marker** (`encodeWith_at_most_one_marker`), for every request and every marker request.
* **What was written is read back** (`decodeReqMessage_encodeMessageMarked`, `markerAt_encodeWith_none`): the marked message decodes to the message it was written from, and a body with no marker reads
  back as a request with no marker request. The bytes of a marked request are the reference printer's (`Request.encodeBytesWith_eq`), as for a plain one.

A hint is never a refusal: the theorems say what the encoding is in each case, and no case is an error. -/

/-- The plain message of a message with text has that text as its `content` string. -/
theorem encodeMessage_content_text (m : RequestMessage) (t : String) (ht : msgText m = some t) :
    get (encodeMessage m) "content" = .str t := by
  cases m with
  | system c => simp [msgText] at ht; subst ht; simp [encodeMessage, get, lookup, go]
  | developer c => simp [msgText] at ht; subst ht; simp [encodeMessage, get, lookup, go]
  | user c => simp [msgText] at ht; subst ht; simp [encodeMessage, get, lookup, go]
  | assistant c cs =>
    simp only [msgText] at ht
    cases c with
    | none => simp at ht
    | some c =>
      simp only [Option.some.injEq] at ht
      subst ht
      cases cs with
      | nil => simp [encodeMessage, opt, get, lookup, go]
      | cons x xs => simp [encodeMessage, orNullStr, get, lookup, go]
  | tool i c => simp [msgText] at ht; subst ht; simp [encodeMessage, get, lookup, go]

/-- The `content` of a message written with the marker is the one-part marked array of its text. -/
theorem encodeMessageMarked_content (m : RequestMessage) (t : String) (ht : msgText m = some t) :
    get (encodeMessageMarked m) "content" = markedContent t := by
  cases m with
  | system c => simp [msgText] at ht; subst ht; simp [encodeMessageMarked, get, lookup, go]
  | developer c => simp [msgText] at ht; subst ht; simp [encodeMessageMarked, get, lookup, go]
  | user c => simp [msgText] at ht; subst ht; simp [encodeMessageMarked, get, lookup, go]
  | assistant c cs =>
    simp only [msgText] at ht
    cases c with
    | none => simp at ht
    | some c =>
      simp only [Option.some.injEq] at ht
      subst ht
      cases cs <;> simp [encodeMessageMarked, get, lookup, go]
  | tool i c => simp [msgText] at ht; subst ht; simp [encodeMessageMarked, get, lookup, go]

/-- The marked content of a text reads back as that text: the marker changes the shape of `content`, never the text it carries. -/
theorem markedText?_markedContent (t : String) : markedText? (markedContent t) = some t := by
  simp [markedContent, cacheControl, markedText?, get, lookup, go]

/-- The plain encoding of a message carries no marked content: a marker in a body was written by `encodeMessageMarked` (or by a provider, on the way in). -/
theorem markedText?_plain (m : RequestMessage) : markedText? (get (encodeMessage m) "content") = none := by
  cases m with
  | system c => simp [encodeMessage, get, lookup, go, markedText?_str]
  | developer c => simp [encodeMessage, get, lookup, go, markedText?_str]
  | user c => simp [encodeMessage, get, lookup, go, markedText?_str]
  | assistant c cs =>
    cases c with
    | none =>
      cases cs with
      | nil => simp [encodeMessage, opt, get, lookup, go, markedText?_null]
      | cons x xs => simp [encodeMessage, orNullStr, get, lookup, go, markedText?_null]
    | some c =>
      cases cs with
      | nil => simp [encodeMessage, opt, get, lookup, go, markedText?_str]
      | cons x xs => simp [encodeMessage, orNullStr, get, lookup, go, markedText?_str]
  | tool i c => simp [encodeMessage, get, lookup, go, markedText?_str]

/-- A message can carry a marker exactly when it carries a text. -/
theorem markable_iff (m : RequestMessage) : markable m = true ↔ ∃ t, msgText m = some t := by
  unfold markable
  cases msgText m with
  | none => simp
  | some t => exact ⟨fun _ => ⟨t, rfl⟩, fun _ => rfl⟩

/-! #### The encoding, message by message -/

/-- The messages written with no marker request are the plain ones, in order. -/
theorem encodeMessagesFrom_none : ∀ (ms : List RequestMessage), encodeMessagesFrom none ms = ms.map encodeMessage
  | [] => rfl
  | m :: ms => by
    show encodeMessage m :: encodeMessagesFrom none ms = encodeMessage m :: List.map encodeMessage ms
    rw [encodeMessagesFrom_none ms]

/-- **An encoding with no marker request is today's encoding**, for every request. -/
theorem encodeWith_none (r : Request) : r.encodeWith none = r.encode := by
  unfold Request.encodeWith Request.encode
  rw [encodeMessagesFrom_none]

/-- The `messages` member of an encoding with no marker request. -/
theorem Request.encodeWith_messages_none (r : Request) : get (r.encodeWith none) "messages" = .arr (r.messages.map encodeMessage) := by
  unfold Request.encodeWith
  rw [get_obj, lookup_cons_ne _ _ (by decide),
    lookup_cons_self _ _ _ (by repeat (first | exact fresh_nil _ | apply fresh_opt _ _ (by decide) | apply fresh_cons _ (by decide))),
    encodeMessagesFrom_none]

/-- The `messages` member of an encoding with a marker request at index `i`. -/
theorem Request.encodeWith_messages_some (r : Request) (i : Nat) : get (r.encodeWith (some i)) "messages" = .arr (encodeMessagesFrom (some i) r.messages) := by
  unfold Request.encodeWith
  rw [get_obj, lookup_cons_ne _ _ (by decide),
    lookup_cons_self _ _ _ (by repeat (first | exact fresh_nil _ | apply fresh_opt _ _ (by decide) | apply fresh_cons _ (by decide)))]

/-- A message that cannot carry a marker is written exactly as `encodeMessage` writes it. -/
theorem encodeMessageAt_eq (m : RequestMessage) (h : markable m = false) : encodeMessageAt m = encodeMessage m := by
  unfold encodeMessageAt
  rw [h]; rfl

/-- A message that can carry a marker is written with it. -/
theorem encodeMessageAt_marked (m : RequestMessage) (h : markable m = true) : encodeMessageAt m = encodeMessageMarked m := by
  unfold encodeMessageAt
  rw [h]; rfl

/-- **An index that names no message that can carry a marker writes no marker**: the messages are the plain ones, in order. -/
theorem encodeMessagesFrom_unmarkable : ∀ (i : Nat) (ms : List RequestMessage),
    (∀ m, ms[i]? = some m → markable m = false) → encodeMessagesFrom (some i) ms = ms.map encodeMessage
  | 0, [], _ => rfl
  | 0, m :: ms, h => by
    have hm : markable m = false := h m rfl
    simp only [encodeMessagesFrom, List.map_cons, encodeMessageAt_eq m hm, encodeMessagesFrom_none]
  | i + 1, [], _ => rfl
  | i + 1, m :: ms, h => by
    simp only [encodeMessagesFrom, List.map_cons]
    rw [encodeMessagesFrom_unmarkable i ms (fun m' hm' => h m' (by rw [List.getElem?_cons_succ]; exact hm'))]

/-- **With an index that names no markable message the whole encoding is exactly the plain one.** -/
theorem encodeWith_some_unmarkable (r : Request) (i : Nat) (h : ∀ m, r.messages[i]? = some m → markable m = false) :
    r.encodeWith (some i) = r.encode := by
  unfold Request.encodeWith Request.encode
  rw [encodeMessagesFrom_unmarkable i r.messages h]

/-- The message at the marked index is the one written with the marker (when it can carry one) and every other message is written exactly as usual. -/
theorem encodeMessagesFrom_lt : ∀ (i : Nat) (ms : List RequestMessage) (m : RequestMessage), ms[i]? = some m →
    encodeMessagesFrom (some i) ms = (ms.map encodeMessage).set i (encodeMessageAt m)
  | 0, [], m, h => by simp at h
  | 0, x :: xs, m, h => by
    rw [List.getElem?_cons_zero] at h
    cases h
    show encodeMessageAt x :: encodeMessagesFrom none xs = (encodeMessage x :: List.map encodeMessage xs).set 0 (encodeMessageAt x)
    rw [List.set_cons_zero, encodeMessagesFrom_none]
  | i + 1, [], m, h => by simp at h
  | i + 1, x :: xs, m, h => by
    rw [List.getElem?_cons_succ] at h
    simp only [encodeMessagesFrom, List.map_cons, List.set_cons_succ]
    rw [encodeMessagesFrom_lt i xs m h]

/-- The marked message carries the text of the message it was written from, as the one-part array. -/
theorem encodeMessageAt_content (m : RequestMessage) (t : String) (hm : markable m = true) (ht : msgText m = some t) :
    get (encodeMessageAt m) "content" = markedContent t := by
  rw [encodeMessageAt_marked m hm]
  exact encodeMessageMarked_content m t ht

/-- **With a markable index the messages are the plain ones with position `i` replaced by the marked message**, whose `content` is the one-part array carrying the same text (which the plain message wrote
as a string, and which reads back from the array unchanged). -/
theorem encodeWith_some_markable (r : Request) (i : Nat) (m : RequestMessage) (t : String)
    (h : r.messages[i]? = some m) (hm : markable m = true) (ht : msgText m = some t) :
    get (r.encodeWith (some i)) "messages" = .arr ((r.messages.map encodeMessage).set i (encodeMessageMarked m)) ∧
    encodeMessageAt m = encodeMessageMarked m ∧
    get (encodeMessageMarked m) "content" = markedContent t ∧
    markedText? (get (encodeMessageMarked m) "content") = some t ∧
    get (encodeMessage m) "content" = .str t := by
  refine ⟨?_, encodeMessageAt_marked m hm, encodeMessageMarked_content m t ht, ?_, encodeMessage_content_text m t ht⟩
  · rw [Request.encodeWith_messages_some, encodeMessagesFrom_lt i _ m h, encodeMessageAt_marked m hm]
  · rw [encodeMessageMarked_content m t ht, markedText?_markedContent]

/-! #### `lastMarkable` -/

/-- `lastMarkable` one step at a time: past the index of the tail when the tail has one, else the head when it can carry a marker. -/
theorem lastMarkable_cons (m : RequestMessage) (ms : List RequestMessage) :
    lastMarkable (m :: ms) = (match lastMarkable ms with | some j => some (j + 1) | none => match markable m with | true => some 0 | false => none) := rfl

/-- When `lastMarkable` is `none`, no message of the list can carry a marker. -/
theorem lastMarkable_none_spec : ∀ (ms : List RequestMessage), lastMarkable ms = none → ∀ m ∈ ms, markable m = false
  | [], _, m, hm => by simp at hm
  | m :: ms, h, m', hm' => by
    rw [lastMarkable_cons] at h
    cases hl : lastMarkable ms with
    | some i => rw [hl] at h; simp at h
    | none =>
      rw [hl] at h
      cases hm : markable m with
      | true => rw [hm] at h; simp at h
      | false =>
        rcases List.mem_cons.1 hm' with rfl | hmem
        · exact hm
        · exact lastMarkable_none_spec ms hl m' hmem

/-- When `lastMarkable` is `some j`, the message at `j` can carry a marker and no later one can. -/
theorem lastMarkable_some_spec : ∀ (ms : List RequestMessage) (j : Nat), lastMarkable ms = some j →
    ∃ m, ms[j]? = some m ∧ markable m = true ∧ ∀ k, j < k → ∀ m', ms[k]? = some m' → markable m' = false
  | [], j, h => by simp [lastMarkable] at h
  | m :: ms, j, h => by
    rw [lastMarkable_cons] at h
    cases hl : lastMarkable ms with
    | some i =>
      rw [hl] at h
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨m', hm', hmk, hlater⟩ := lastMarkable_some_spec ms i hl
      refine ⟨m', ?_, hmk, ?_⟩
      · rw [List.getElem?_cons_succ]; exact hm'
      · intro k hk m'' hm''
        cases k with
        | zero => omega
        | succ k' =>
          rw [List.getElem?_cons_succ] at hm''
          exact hlater k' (by omega) m'' hm''
    | none =>
      rw [hl] at h
      cases hm : markable m with
      | true =>
        simp only [hm] at h
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨m, ?_, hm, ?_⟩
        · rw [List.getElem?_cons_zero]
        · intro k hk m' hm'
          cases k with
          | zero => omega
          | succ k' =>
            rw [List.getElem?_cons_succ] at hm'
            exact lastMarkable_none_spec ms hl m' (List.mem_of_getElem? hm')
      | false => rw [hm] at h; simp at h

/-- **`lastMarkable` answers what a caller needs**: the message at the index it gives can carry a marker, no later message can, and it is `none` exactly when no message can. -/
theorem lastMarkable_spec (ms : List RequestMessage) :
    (match lastMarkable ms with
     | some j => ∃ m, ms[j]? = some m ∧ markable m = true ∧ ∀ k, j < k → ∀ m', ms[k]? = some m' → markable m' = false
     | none => ∀ m ∈ ms, markable m = false) := by
  cases hl : lastMarkable ms with
  | some j => exact lastMarkable_some_spec ms j hl
  | none => exact lastMarkable_none_spec ms hl

/-- The index `lastMarkable` gives names a message that can carry a marker. -/
theorem lastMarkable_some_markable (ms : List RequestMessage) (j : Nat) (h : lastMarkable ms = some j) :
    ∃ m, ms[j]? = some m ∧ markable m = true := by
  obtain ⟨m, hm, hmk, _⟩ := lastMarkable_some_spec ms j h
  exact ⟨m, hm, hmk⟩

/-- After the index `lastMarkable` gives, no message can carry a marker. -/
theorem lastMarkable_no_later (ms : List RequestMessage) (j k : Nat) (h : lastMarkable ms = some j) (hk : j < k) :
    ∀ m, ms[k]? = some m → markable m = false := by
  obtain ⟨_, _, _, hlater⟩ := lastMarkable_some_spec ms j h
  exact hlater k hk

/-- `lastMarkable` is `none` exactly when no message of the list can carry a marker (the empty list, or one of assistant calls only). -/
theorem lastMarkable_none_iff (ms : List RequestMessage) :
    lastMarkable ms = none ↔ ∀ m ∈ ms, markable m = false := by
  constructor
  · exact lastMarkable_none_spec ms
  · intro h
    cases hl : lastMarkable ms with
    | none => rfl
    | some j =>
      obtain ⟨m, hm, hmk⟩ := lastMarkable_some_markable ms j hl
      rw [h m (List.mem_of_getElem? hm)] at hmk
      exact absurd hmk (by simp)

/-- `lastMarkable` of the empty list is `none`. -/
theorem lastMarkable_nil : lastMarkable ([] : List RequestMessage) = none := rfl

/-! #### At most one message of an encoding carries a marker -/

/-- A message written without the marker carries none. -/
theorem carriesMarker_encodeMessage (m : RequestMessage) : carriesMarker (encodeMessage m) = false := by
  unfold carriesMarker
  cases m with
  | system c => simp [encodeMessage, get, lookup, go]
  | developer c => simp [encodeMessage, get, lookup, go]
  | user c => simp [encodeMessage, get, lookup, go]
  | assistant c cs =>
    cases c with
    | none =>
      cases cs with
      | nil => simp [encodeMessage, opt, get, lookup, go]
      | cons x xs => simp [encodeMessage, orNullStr, get, lookup, go]
    | some c =>
      cases cs with
      | nil => simp [encodeMessage, opt, get, lookup, go]
      | cons x xs => simp [encodeMessage, orNullStr, get, lookup, go]
  | tool i c => simp [encodeMessage, get, lookup, go]

/-- A message written with the marker carries one (its content is the one-part array, whose part has `cache_control`). -/
theorem carriesMarker_encodeMessageMarked (m : RequestMessage) (t : String) (ht : msgText m = some t) :
    carriesMarker (encodeMessageMarked m) = true := by
  unfold carriesMarker
  rw [encodeMessageMarked_content m t ht]
  simp [markedContent, cacheControl, get, lookup, go, isNull]

/-- **A message written by `encodeMessageAt` carries a marker exactly when its message can**: the marker goes where the message has text, and nowhere else. -/
theorem carriesMarker_encodeMessageAt (m : RequestMessage) : carriesMarker (encodeMessageAt m) = markable m := by
  cases hm : markable m with
  | false => rw [encodeMessageAt_eq m hm]; exact carriesMarker_encodeMessage m
  | true =>
    rw [encodeMessageAt_marked m hm]
    obtain ⟨t, ht⟩ := (markable_iff m).1 hm
    exact carriesMarker_encodeMessageMarked m t ht

/-- A list of plain encodings carries no marker, so the count of marked messages among them is zero. -/
theorem countP_encodeMessage_zero (ms : List RequestMessage) : (ms.map encodeMessage).countP carriesMarker = 0 := by
  induction ms with
  | nil => rfl
  | cons m ms ih => simp [carriesMarker_encodeMessage, ih]

/-- The messages written with no marker request carry no marker at all. -/
theorem encodeMessagesFrom_none_count (ms : List RequestMessage) : (encodeMessagesFrom none ms).countP carriesMarker = 0 := by
  rw [encodeMessagesFrom_none]; exact countP_encodeMessage_zero ms

/-- The messages written with a marker request at index `i` carry at most one marker. -/
theorem countP_some_le : ∀ (i : Nat) (ms : List RequestMessage), (encodeMessagesFrom (some i) ms).countP carriesMarker ≤ 1
  | 0, [] => by simp [encodeMessagesFrom]
  | 0, m :: ms => by
    show (encodeMessageAt m :: encodeMessagesFrom none ms).countP carriesMarker ≤ 1
    rw [List.countP_cons, carriesMarker_encodeMessageAt, encodeMessagesFrom_none_count]
    split <;> omega
  | i + 1, [] => by simp [encodeMessagesFrom]
  | i + 1, m :: ms => by
    show (encodeMessage m :: encodeMessagesFrom (some i) ms).countP carriesMarker ≤ 1
    rw [List.countP_cons, carriesMarker_encodeMessage]
    simp only [Bool.false_eq_true, ite_false]
    exact countP_some_le i ms

/-- **At most one message of an encoding carries a marker** — that is, at most one of its `content` members is an array with a part carrying a non-null `cache_control` (`carriesMarker`), which is the only
shape in which this library writes one — for every request and every marker request. -/
theorem encodeWith_at_most_one_marker (r : Request) (cacheAt : Option Nat) (vs : List Value)
    (hvs : get (r.encodeWith cacheAt) "messages" = .arr vs) : vs.countP carriesMarker ≤ 1 := by
  cases cacheAt with
  | none =>
    rw [Request.encodeWith_messages_none] at hvs
    injection hvs with harr
    rw [← harr, countP_encodeMessage_zero]
    omega
  | some i =>
    rw [Request.encodeWith_messages_some] at hvs
    injection hvs with harr
    rw [← harr]
    exact countP_some_le i r.messages

/-! #### Reading a marked body back -/

/-- The marked message decodes to the message it was written from, when that message can carry the marker. -/
theorem decodeReqMessage_encodeMessageMarked (m : RequestMessage) (hm : markable m = true) :
    decodeReqMessage (encodeMessageMarked m) = .ok m := by
  cases m with
  | system c =>
    simp [encodeMessageMarked, markedContent, cacheControl, markedText?, decodeReqMessage, decodeContentStr,
      reqStr, get, lookup, go, Functor.map, Except.map]
  | developer c =>
    simp [encodeMessageMarked, markedContent, cacheControl, markedText?, decodeReqMessage, decodeContentStr,
      reqStr, get, lookup, go, Functor.map, Except.map]
  | user c =>
    simp [encodeMessageMarked, markedContent, cacheControl, markedText?, decodeReqMessage, decodeContentStr,
      reqStr, get, lookup, go, Functor.map, Except.map]
  | tool i c =>
    simp [encodeMessageMarked, markedContent, cacheControl, markedText?, decodeReqMessage, decodeContentStr,
      reqStr, get, lookup, go, bind, Except.bind, pure, Except.pure]
  | assistant c cs =>
    rw [markable_iff] at hm
    obtain ⟨t, ht⟩ := hm
    simp only [msgText] at ht
    cases c with
    | none => simp at ht
    | some c =>
      simp only [Option.some.injEq] at ht
      subst ht
      cases cs with
      | nil =>
        simp [encodeMessageMarked, markedContent, cacheControl, markedText?, decodeReqMessage, optContentStr,
          reqStr, decodeCalls, get, lookup, go, bind, Except.bind, pure, Except.pure]
      | cons x xs =>
        simp [encodeMessageMarked, markedContent, cacheControl, markedText?, decodeReqMessage, optContentStr,
          reqStr, decodeCalls, get, lookup, go, underStep, decodeToolCalls_encode_cons, bind, Except.bind,
          pure, Except.pure]

/-- A list of plain encodings carries no marker, so the marker request read from it is none. -/
theorem firstMarkedFrom_plain : ∀ (k : Nat) (ms : List RequestMessage), firstMarkedFrom k (ms.map encodeMessage) = none
  | k, [] => rfl
  | k, m :: ms => by
    show (match markedText? (get (encodeMessage m) "content") with
      | some _ => some k
      | none => firstMarkedFrom (k + 1) (ms.map encodeMessage)) = none
    rw [markedText?_plain, firstMarkedFrom_plain (k + 1) ms]

/-- Reading a list from index `k`, the first marked message of a list that is plain everywhere except at position `i` is at `k + i`. -/
theorem firstMarkedFrom_set : ∀ (k : Nat) (ws : List Value) (w : Value) (i : Nat),
    (∀ v ∈ ws, markedText? (get v "content") = none) → markedText? (get w "content") ≠ none → i < ws.length →
    firstMarkedFrom k (ws.set i w) = some (k + i)
  | k, [], w, i, _, _, h => by simp at h
  | k, x :: xs, w, 0, hw, hw', _ => by
    simp only [List.set_cons_zero, firstMarkedFrom]
    cases hm : markedText? (get w "content") with
    | none => exact absurd hm hw'
    | some t => rfl
  | k, x :: xs, w, i + 1, hw, hw', h => by
    have hx : markedText? (get x "content") = none := hw x (by simp)
    have hxs : ∀ v ∈ xs, markedText? (get v "content") = none := fun v hv => hw v (by simp [hv])
    have hi : i < xs.length := by
      have := h
      simp only [List.length_cons] at this
      omega
    have ih : firstMarkedFrom (k+1) (xs.set i w) = some (k+1+i) := firstMarkedFrom_set (k+1) xs w i hxs hw' hi
    rw [show (x :: xs).set (i+1) w = x :: xs.set i w from rfl]
    simp only [firstMarkedFrom, hx, ih]
    rw [show k + 1 + i = k + (i + 1) from by omega]

/-- The marker request read from a body with no marker is none. -/
theorem markerAt_encodeWith_none (r : Request) : Request.markerAt (r.encodeWith none) = none := by
  unfold Request.markerAt
  rw [Request.encodeWith_messages_none]
  exact firstMarkedFrom_plain 0 r.messages

/-- **The marker request read from a marked body is the index the caller named**: `some i`. -/
theorem markerAt_encodeWith_some (r : Request) (i : Nat) (m : RequestMessage) (t : String)
    (h : r.messages[i]? = some m) (ht : msgText m = some t) : Request.markerAt (r.encodeWith (some i)) = some i := by
  have hlt : i < r.messages.length := (List.getElem?_eq_some_iff.1 h).1
  have hm : markable m = true := (markable_iff m).2 ⟨t, ht⟩
  have hcontent : get (encodeMessageAt m) "content" = markedContent t := encodeMessageAt_content m t hm ht
  have hmarked : markedText? (get (encodeMessageAt m) "content") ≠ none := by
    rw [hcontent, markedText?_markedContent]; simp
  have hlen : i < (r.messages.map encodeMessage).length := by
    rw [List.length_map]; exact hlt
  simp only [Request.markerAt, Request.encodeWith_messages_some, encodeMessagesFrom_lt i _ m h]
  rw [firstMarkedFrom_set 0 _ _ i (by
        intro v hv
        obtain ⟨m', -, rfl⟩ := List.mem_map.1 hv
        exact markedText?_plain m') hmarked hlen]
  simp

/-! #### Concrete cases: the shape on the wire, and the witnesses that the hypotheses can hold -/

/-- The marker's own value, by `rfl`: `{"type": "ephemeral"}`. -/
theorem cacheControl_eq : cacheControl = .obj [("type", .str "ephemeral")] := rfl

set_option maxRecDepth 4000 in
/-- The one-part marked array, printed: the text unchanged, the marker beside it. -/
theorem markedContent_print :
    String.fromUTF8! (ByteArray.mk (LeanJson.print (markedContent "hi")).toArray) =
      "[{\"type\":\"text\",\"text\":\"hi\",\"cache_control\":{\"type\":\"ephemeral\"}}]" := rfl

/-- A markable message, and what the marker turns it into: the same text, in the one-part array. -/
theorem marked_user_witness :
    markable (.user "hi") = true ∧ msgText (.user "hi") = some "hi" ∧
    encodeMessage (.user "hi") = .obj [("role", .str "user"), ("content", .str "hi")] ∧
    encodeMessageAt (.user "hi") = .obj [("role", .str "user"), ("content", markedContent "hi")] := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  exact encodeMessageAt_marked _ rfl

/-- A message that cannot carry a marker: an assistant turn of calls and no text has no content part to mark, and is written exactly as before. -/
theorem unmarkable_witness :
    markable (.assistant none [⟨"c1", "f", "{}"⟩]) = false ∧ msgText (.assistant none [⟨"c1", "f", "{}"⟩]) = none ∧
    encodeMessageAt (.assistant none [⟨"c1", "f", "{}"⟩]) = encodeMessage (.assistant none [⟨"c1", "f", "{}"⟩]) ∧
    carriesMarker (encodeMessageAt (.assistant none [⟨"c1", "f", "{}"⟩])) = false := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  rw [encodeMessageAt_eq _ rfl]
  exact carriesMarker_encodeMessage _

/-- The marked content is an array of one part, so it is not the plain string: that is why a marked body differs from the plain one. -/
theorem markedContent_ne_str (t : String) : markedContent t ≠ .str t := by
  simp [markedContent]

/-- A marked message and a plain one are different values, so the theorems that compare them are not vacuous: the marker request changes the body. -/
theorem marked_ne_plain : encodeMessageAt (.user "hi") ≠ encodeMessage (.user "hi") := by
  intro h
  have hc := congrArg (fun v => get v "content") h
  rw [encodeMessageAt_marked _ rfl, encodeMessageMarked_content _ _ rfl, encodeMessage_content_text _ _ rfl] at hc
  exact markedContent_ne_str "hi" hc

/-- `lastMarkable` on hand-built conversations: the last message that can carry a marker, past the assistant calls after it, and none when nothing can. -/
theorem lastMarkable_cases :
    lastMarkable [.system "s", .user "u"] = some 1 ∧
    lastMarkable [.user "u", .assistant none [⟨"c1", "f", "{}"⟩]] = some 0 ∧
    lastMarkable [.assistant none [⟨"c1", "f", "{}"⟩], .tool "c1" "3 C"] = some 1 ∧
    lastMarkable [.assistant none [⟨"c1", "f", "{}"⟩]] = none ∧
    lastMarkable ([] : List RequestMessage) = none := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rfl

/-- A request built by hand, for the concrete cases below. -/
def concreteRequest : Request := { model := "m", messages := [.user "hi", .tool "c1" "3 C"] }

set_option maxRecDepth 8000 in
/-- The whole encoding on a hand-built request: with no marker request it is today's bytes, and with the second message marked it is the same bytes with that one content arrayed. -/
theorem encodeWith_print_cases :
    concreteRequest.encodeWith none = concreteRequest.encode ∧
    String.fromUTF8! (ByteArray.mk (LeanJson.print (concreteRequest.encodeWith (some 1))).toArray) =
      "{\"model\":\"m\",\"messages\":[{\"role\":\"user\",\"content\":\"hi\"},{\"role\":\"tool\",\"tool_call_id\":\"c1\",\"content\":[{\"type\":\"text\",\"text\":\"3 C\",\"cache_control\":{\"type\":\"ephemeral\"}}]}]}" ∧
    concreteRequest.encodeWith (some 2) = concreteRequest.encode ∧
    Request.markerAt (concreteRequest.encodeWith (some 1)) = some 1 ∧
    Request.markerAt (concreteRequest.encodeWith none) = none := by
  refine ⟨encodeWith_none concreteRequest, rfl, encodeWith_some_unmarkable concreteRequest 2 (by decide), ?_,
    markerAt_encodeWith_none concreteRequest⟩
  exact markerAt_encodeWith_some concreteRequest 1 (.tool "c1" "3 C") "3 C" rfl rfl

/-- The count of marked messages, on hand-built values: one when the caller names a message that can carry a marker, one when it names the last message (the bound is attained, so `≤ 1` is not vacuous),
and none when the index is past the end or no marker is asked for. -/
theorem encodeWith_one_marker_witness :
    (encodeMessagesFrom (some 1) concreteRequest.messages).countP carriesMarker = 1 ∧
    (encodeMessagesFrom (some 5) concreteRequest.messages).countP carriesMarker = 0 ∧
    (encodeMessagesFrom none concreteRequest.messages).countP carriesMarker = 0 ∧
    carriesMarker (encodeMessageAt (.tool "c1" "3 C")) = true ∧
    carriesMarker (encodeMessage (.user "hi")) = false := by
  refine ⟨?_, ?_, encodeMessagesFrom_none_count _, ?_, carriesMarker_encodeMessage _⟩
  · decide
  · decide
  · decide

/-! #### The witnesses: each theorem with a hypothesis, applied to a hand-built value -/

/-- The encoding named in (b), applied: the marked index is the second message and the marked content is its text in the one-part array. -/
theorem encodeWith_some_markable_witness :
    get (concreteRequest.encodeWith (some 1)) "messages" =
      .arr ((concreteRequest.messages.map encodeMessage).set 1 (encodeMessageMarked (.tool "c1" "3 C"))) ∧
    get (encodeMessageMarked (.tool "c1" "3 C")) "content" = markedContent "3 C" ∧
    markedText? (get (encodeMessageMarked (.tool "c1" "3 C")) "content") = some "3 C" := by
  obtain ⟨h1, -, h3, h4, -⟩ :=
    encodeWith_some_markable concreteRequest 1 (.tool "c1" "3 C") "3 C" rfl rfl rfl
  exact ⟨h1, h3, h4⟩

/-- The position-by-position form of (b), applied: the encoded list is the plain one with the marked message set at the named index. -/
theorem encodeMessagesFrom_lt_witness :
    encodeMessagesFrom (some 1) concreteRequest.messages =
      (concreteRequest.messages.map encodeMessage).set 1 (encodeMessageAt (.tool "c1" "3 C")) :=
  encodeMessagesFrom_lt 1 concreteRequest.messages (.tool "c1" "3 C") rfl

/-- The refusal of an unmodelled content array, applied: `markedText?` is `none` for a two-part array, so `decodeContentStr` refuses it. -/
theorem decodeContentStr_two_parts_refused :
    decodeContentStr (.obj [("content", .arr [.obj [("type", .str "text"), ("text", .str "a"), ("cache_control", cacheControl)],
      .obj [("type", .str "text"), ("text", .str "b")]])]) "content" = .error { path := [.key "content"], kind := .wrongType .string } := by
  simp [decodeContentStr, markedText?, get, lookup, go]

/-- The codec of a marked message, applied: the marked message decodes to the message it was written from. -/
theorem decodeReqMessage_encodeMessageMarked_witness :
    decodeReqMessage (encodeMessageMarked (.user "hi")) = .ok (.user "hi") :=
  decodeReqMessage_encodeMessageMarked _ rfl

/-- `lastMarkable`'s corollaries, applied to a hand-built conversation `[user, tool, assistant-calls]`: the index is `1`, the message there can carry a marker, and the message at the **next** index — which
exists, an assistant turn of calls only — cannot; and a list of assistant calls only has `lastMarkable` `none`. -/
theorem lastMarkable_witness :
    lastMarkable ([.user "u", .tool "c1" "3 C", .assistant none [⟨"c1", "f", "{}"⟩]] : List RequestMessage) = some 1 ∧
    (∃ m, ([.user "u", .tool "c1" "3 C", .assistant none [⟨"c1", "f", "{}"⟩]] : List RequestMessage)[1]? = some m ∧ markable m = true) ∧
    (∀ m, ([.user "u", .tool "c1" "3 C", .assistant none [⟨"c1", "f", "{}"⟩]] : List RequestMessage)[2]? = some m → markable m = false) ∧
    lastMarkable ([.assistant none [⟨"c1", "f", "{}"⟩]] : List RequestMessage) = none := by
  refine ⟨rfl, lastMarkable_some_markable _ 1 rfl, lastMarkable_no_later _ 1 2 rfl (by omega), ?_⟩
  exact lastMarkable_none_iff _ |>.2 (fun m hm => by
    rcases List.mem_cons.1 hm with rfl | hmem
    · rfl
    · simp at hmem)

/-- The bound of (e), applied to a request and attained: the messages a marked request encodes carry at most one marker, and exactly one, so the bound is not vacuous. -/
theorem encodeWith_at_most_one_marker_witness :
    (encodeMessagesFrom (some 1) concreteRequest.messages).countP carriesMarker ≤ 1 ∧
    (encodeMessagesFrom (some 1) concreteRequest.messages).countP carriesMarker = 1 := by
  refine ⟨encodeWith_at_most_one_marker concreteRequest (some 1) _ (Request.encodeWith_messages_some _ _), ?_⟩
  decide

/-- A required content that is the one-part marked array is read as its text (the branch of `decodeContentStr_ok_iff` a caller marks a message for). -/
theorem decodeContentStr_marked_witness :
    decodeContentStr (.obj [("content", markedContent "hi")]) "content" = .ok "hi" := by
  simp [decodeContentStr, markedContent, cacheControl, markedText?, get, lookup, go]

end VbmLlm.OpenAI