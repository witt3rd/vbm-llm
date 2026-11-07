import VbmLlm.OpenAI.Request
import VbmLlmProofs.OpenAI.Response
/-! # Proofs about the OpenAI chat-completions request encoder (`VbmLlm/OpenAI/Request.lean`)

* **A count is written as a plain natural** (`natOf_natNumber`): reading the lexeme back gives the count, for every natural.
* **What the encoding says, member by member** (`encode_get_*`): each member of the encoded request is the value of its field, and a member whose field is absent is absent (null); an encoded request
  is an object. No member of the request object is ever written as `null` (inside a message, an assistant message with calls and no text is written with `"content": null`: `encodeMessage_assistant_calls_no_text`).
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

/-- **No member of an encoded request object is `null`**: an absent field is left out, never written as `null` (the one `null` is inside a message: `encodeMessage_assistant_calls_no_text`). -/
theorem encode_members_not_null (r : Request) (ms : List (String × Value)) (h : r.encode = .obj ms) : ∀ p ∈ ms, p.2 ≠ .null := by
  unfold Request.encode at h
  cases h
  refine cons_not_null (by simp) (cons_not_null (by simp) ?_)
  repeat (first | exact fun p hp => by simp at hp | refine opt_not_null _ (by intro a; cases a <;> simp [encodeToolChoice]) ?_)

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
  | system c => simp [encodeMessage, decodeReqMessage, reqStr, get, lookup, go, Functor.map, Except.map]
  | developer c => simp [encodeMessage, decodeReqMessage, reqStr, get, lookup, go, Functor.map, Except.map]
  | user c => simp [encodeMessage, decodeReqMessage, reqStr, get, lookup, go, Functor.map, Except.map]
  | tool i c => simp [encodeMessage, decodeReqMessage, reqStr, get, lookup, go, bind, Except.bind, pure, Except.pure]
  | assistant c cs =>
    cases cs with
    | nil => cases c <;> simp [encodeMessage, decodeReqMessage, reqStr, optStr, decodeCalls, opt, get, lookup, go, bind, Except.bind, pure, Except.pure]
    | cons x xs =>
      cases c <;> simp [encodeMessage, orNullStr, decodeReqMessage, reqStr, optStr, decodeCalls, get, lookup, go, underStep, decodeToolCalls_encode_cons, bind, Except.bind, pure, Except.pure]

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
  rw [hms] at g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 ⊢
  simp only [Request.decode, Request.decodeBody, bind, Except.bind, (reqStr_ok_iff _ _ _).2 g1, decodeMessages_encode _ _ h g2, decodeTools_encode _ _ g3, decodeToolChoice_encode _ _ g4,
    optBool_orNull _ _ _ g5, optBool_orNull _ _ _ g6, decodeIncludeUsage_encode _ _ g7, optNat_orNull _ _ _ g8, optNat_orNull _ _ _ g9, optNum_orNull _ _ _ g10, optNum_orNull _ _ _ g11, pure, Except.pure]

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

/-- A `content` that is not a string (an array of content parts) is refused for a user message, never dropped. -/
theorem decodeReqMessage_user_content (v : Value) (hv : ∃ ms, v = .obj ms) (h : get v "role" = .str "user") (hc : ∀ s, get v "content" ≠ .str s) (m : RequestMessage) :
    decodeReqMessage v ≠ .ok m := by
  obtain ⟨ms, rfl⟩ := hv
  simp only [decodeReqMessage, reqStr, h]
  cases h2 : get (.obj ms) "content" <;> simp_all [Functor.map, Except.map]

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
  obtain ⟨_, _, ms, hms, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := h
  exact decodeMessages_ne_nil _ _ hms

end VbmLlm.OpenAI
