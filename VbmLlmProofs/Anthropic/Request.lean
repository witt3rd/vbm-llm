import VbmLlm.Anthropic.Request
import VbmLlmProofs.OpenAI.Request
/-! # Proofs about the Anthropic messages request encoder (`VbmLlm/Anthropic/Request.lean`)

* **What the encoding says, member by member** (`encode_get_*`): each member of the encoded request is the value of its field, and a member whose field is absent is absent (null); an encoded request is an
  object. No member is ever written as `null`.
* **`max_tokens` is written as a plain natural** (`encode_max_tokens_natural`), required: it is always written.
* **A block is written as the schema says** (`encodeBlock_*`): a call's `input` is the object it is, a result's absent content is left out. -/
namespace VbmLlm.Anthropic
open LeanJson
open VbmLlm.OpenAI (opt orNull Fresh fresh_nil fresh_opt fresh_cons lookup_cons_ne lookup_cons_self lookup_opt_ne lookup_opt_self natNumber natOf_natNumber opt_not_null cons_not_null)

theorem encode_get_model (r : Request) : get r.encode "model" = .str r.model := by
  unfold Request.encode
  rw [get_obj]
  exact lookup_cons_self _ _ _ (by repeat (first | exact fresh_nil _ | apply fresh_opt _ _ (by decide) | apply fresh_cons _ (by decide)))

theorem encode_get_max_tokens (r : Request) : get r.encode "max_tokens" = .num (natNumber r.maxTokens) := by
  unfold Request.encode
  rw [get_obj]
  simp (disch := decide) only [lookup_cons_ne]
  exact lookup_cons_self _ _ _ (by repeat (first | exact fresh_nil _ | apply fresh_opt _ _ (by decide) | apply fresh_cons _ (by decide)))

theorem encode_get_messages (r : Request) : get r.encode "messages" = .arr (r.messages.map encodeMessage) := by
  unfold Request.encode
  rw [get_obj]
  simp (disch := decide) only [lookup_cons_ne]
  exact lookup_cons_self _ _ _ (by repeat (first | exact fresh_nil _ | apply fresh_opt _ _ (by decide) | apply fresh_cons _ (by decide)))

theorem encode_get_system (r : Request) : get r.encode "system" = orNull .str r.system := by
  unfold Request.encode
  rw [get_obj]
  simp (disch := decide) only [lookup_cons_ne]
  exact lookup_opt_self _ _ _ _ (by repeat (first | exact fresh_nil _ | apply fresh_opt _ _ (by decide) | apply fresh_cons _ (by decide)))

theorem encode_get_tools (r : Request) : get r.encode "tools" = orNull (fun ts => .arr (ts.map encodeTool)) (match r.tools with | [] => none | ts => some ts) := by
  unfold Request.encode
  rw [get_obj]
  simp (disch := decide) only [lookup_cons_ne, lookup_opt_ne]
  exact lookup_opt_self _ _ _ _ (by repeat (first | exact fresh_nil _ | apply fresh_opt _ _ (by decide) | apply fresh_cons _ (by decide)))

theorem encode_get_tool_choice (r : Request) : get r.encode "tool_choice" = orNull encodeToolChoice r.toolChoice := by
  unfold Request.encode
  rw [get_obj]
  simp (disch := decide) only [lookup_cons_ne, lookup_opt_ne]
  exact lookup_opt_self _ _ _ _ (by repeat (first | exact fresh_nil _ | apply fresh_opt _ _ (by decide) | apply fresh_cons _ (by decide)))

theorem encode_get_stream (r : Request) : get r.encode "stream" = orNull .bool r.stream := by
  unfold Request.encode
  rw [get_obj]
  simp (disch := decide) only [lookup_cons_ne, lookup_opt_ne]
  exact lookup_opt_self _ _ _ _ (by repeat (first | exact fresh_nil _ | apply fresh_opt _ _ (by decide) | apply fresh_cons _ (by decide)))

theorem encode_get_temperature (r : Request) : get r.encode "temperature" = orNull .num r.temperature := by
  unfold Request.encode
  rw [get_obj]
  simp (disch := decide) only [lookup_cons_ne, lookup_opt_ne]
  exact lookup_opt_self _ _ _ _ (by repeat (first | exact fresh_nil _ | apply fresh_opt _ _ (by decide) | apply fresh_cons _ (by decide)))

theorem encode_get_top_p (r : Request) : get r.encode "top_p" = orNull .num r.topP := by
  unfold Request.encode
  rw [get_obj]
  simp (disch := decide) only [lookup_cons_ne, lookup_opt_ne]
  exact lookup_opt_self _ _ _ _ (by repeat (first | exact fresh_nil _ | apply fresh_opt _ _ (by decide) | apply fresh_cons _ (by decide)))

theorem encode_get_top_k (r : Request) : get r.encode "top_k" = orNull (fun n => .num (natNumber n)) r.topK := by
  unfold Request.encode
  rw [get_obj]
  simp (disch := decide) only [lookup_cons_ne, lookup_opt_ne]
  exact lookup_opt_self _ _ _ _ (by repeat (first | exact fresh_nil _ | apply fresh_opt _ _ (by decide) | apply fresh_cons _ (by decide)))

theorem encode_get_stop_sequences (r : Request) : get r.encode "stop_sequences" = orNull (fun ss => .arr (ss.map .str)) (match r.stopSequences with | [] => none | ss => some ss) := by
  unfold Request.encode
  rw [get_obj]
  simp (disch := decide) only [lookup_cons_ne, lookup_opt_ne]
  exact lookup_opt_self _ _ _ _ (by repeat (first | exact fresh_nil _ | apply fresh_opt _ _ (by decide) | apply fresh_cons _ (by decide)))

/-- An encoded request is an object. -/
theorem encode_object (r : Request) : ∃ ms, r.encode = .obj ms := ⟨_, rfl⟩

/-- **`max_tokens` is a plain natural**: the member is the lexeme of the count, and reading it back gives the count, for every natural. -/
theorem encode_max_tokens_natural (r : Request) : ∃ n, get r.encode "max_tokens" = .num n ∧ natOf n = some r.maxTokens :=
  ⟨natNumber r.maxTokens, encode_get_max_tokens r, natOf_natNumber r.maxTokens⟩

/-- **No member of an encoded request is `null`**: an absent field is left out, never written as `null`. -/
theorem encode_members_not_null (r : Request) (ms : List (String × Value)) (h : r.encode = .obj ms) : ∀ p ∈ ms, p.2 ≠ .null := by
  unfold Request.encode at h
  cases h
  refine cons_not_null (by simp) (cons_not_null (by simp) (cons_not_null (by simp) ?_))
  repeat (first | exact fun p hp => by simp at hp | refine opt_not_null _ (by intro a; cases a <;> simp [encodeToolChoice]) ?_)

/-! ### Blocks -/

/-- A call is written with its input as the object it is, verbatim. -/
theorem encodeBlock_toolUse (i n : String) (inp : List (String × Value)) :
    get (encodeBlock (.toolUse i n inp)) "type" = .str "tool_use" ∧ get (encodeBlock (.toolUse i n inp)) "id" = .str i ∧
    get (encodeBlock (.toolUse i n inp)) "name" = .str n ∧ get (encodeBlock (.toolUse i n inp)) "input" = .obj inp := by
  simp [encodeBlock, get, lookup, go]

/-- A result names its call, and an absent content or error flag is left out. -/
theorem encodeBlock_toolResult (i : String) (c : Option String) (e : Option Bool) :
    get (encodeBlock (.toolResult i c e)) "tool_use_id" = .str i ∧ get (encodeBlock (.toolResult i c e)) "content" = orNull .str c ∧
    get (encodeBlock (.toolResult i c e)) "is_error" = orNull .bool e := by
  cases c <;> cases e <;> simp [encodeBlock, get, lookup, go, opt, orNull]

/-- **The request as bytes is the reference printer's**: `encodeBytes r` is exactly the bytes of `print (encode r)` (from `printBytes_eq`). -/
theorem Request.encodeBytes_eq (r : Request) : r.encodeBytes = ⟨(LeanJson.print r.encode).toArray⟩ := LeanJson.printBytes_eq r.encode

end VbmLlm.Anthropic
