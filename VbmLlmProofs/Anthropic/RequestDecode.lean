import VbmLlm.Anthropic.RequestDecode
import VbmLlmProofs.Anthropic.Request
/-! # Proofs about the Anthropic messages request decoder (`VbmLlm/Anthropic/RequestDecode.lean`)

* **The round trip** (`decode_encode`): decoding an encoded request gives the request back, for every request that has a message (the schema requires one), block by block, tool by tool, choice by choice.
* **What decodes is written back the same** (`decode_ok_stable`): `decode (encode r) = r` for whatever a decode yields.
* **Fail closed** (`Request.decode_not_object`, `decodeMsgs_*`, `decodeMsg_unsupported_role`, `decodeReqBlock_unsupported_type`, `decodeToolPick_unsupported`, `reqNat_missing`): a request that is not an object, a request with no `max_tokens`
  or no (or an empty, or a non-array) `messages`, a role, a block type or a `tool_choice` word that is not modelled is refused, never read as another. -/
namespace VbmLlm.Anthropic
open LeanJson
open VbmLlm.OpenAI (reqStr optStr optNat opt orNull decodeEach decodeEach_encode optBool optNum optBool_orNull optNum_orNull optNat_orNull natNumber natOf_natNumber optStr_ok_iff reqStr_ok_iff underStep_ok bind_ok_iff pure_ok_iff)

/-! ### Blocks, messages, tools -/

theorem decodeReqBlock_encodeBlock (b : ReqBlock) : decodeReqBlock (encodeBlock b) = .ok b := by
  cases b with
  | text t => simp [encodeBlock, decodeReqBlock, reqStr, get, lookup, go, Functor.map, Except.map]
  | toolUse i n inp => simp [encodeBlock, decodeReqBlock, reqStr, reqMembers, get, lookup, go, bind, Except.bind, pure, Except.pure]
  | thinking t s => simp [encodeBlock, decodeReqBlock, reqStr, get, lookup, go, bind, Except.bind, pure, Except.pure]
  | redactedThinking d => simp [encodeBlock, decodeReqBlock, reqStr, get, lookup, go, Functor.map, Except.map]
  | toolResult i c e =>
    cases c <;> cases e <;> simp [encodeBlock, decodeReqBlock, reqStr, optStr, optBool, opt, get, lookup, go, bind, Except.bind, pure, Except.pure]

theorem decodeMsg_encodeMessage (m : Message) : decodeMsg (encodeMessage m) = .ok m := by
  obtain ⟨role, content⟩ := m
  have hc : get (encodeMessage ⟨role, content⟩) "content" = .arr (content.map encodeBlock) := by simp [encodeMessage, get, lookup, go]
  cases role <;> simp only [decodeMsg, encodeMessage, Role.word, reqStr, get, lookup, go] <;> simp [decodeMsgContent, get, lookup, go, underStep, decodeEach_encode _ _ decodeReqBlock_encodeBlock, bind, Except.bind, pure, Except.pure]

theorem decodeToolDecl_encodeTool (t : Tool) : decodeToolDecl (encodeTool t) = .ok t := by
  obtain ⟨name, description, inputSchema, strict⟩ := t
  cases description <;> cases strict <;> simp [decodeToolDecl, encodeTool, reqStr, reqMembers, optStr, optBool, opt, get, lookup, go, bind, Except.bind, pure, Except.pure]

theorem decodeToolPick_encode (v : Value) (o : Option ToolChoice) (h : get v "tool_choice" = orNull encodeToolChoice o) : decodeToolPick v = .ok o := by
  cases o with
  | none => simp [decodeToolPick, h, orNull]
  | some c =>
    cases c with
    | auto d => cases d <;> (simp only [decodeToolPick, h, orNull, encodeToolChoice]; simp [reqStr, optBool, opt, get, lookup, go, underStep, bind, Except.bind, pure, Except.pure])
    | any d => cases d <;> (simp only [decodeToolPick, h, orNull, encodeToolChoice]; simp [reqStr, optBool, opt, get, lookup, go, underStep, bind, Except.bind, pure, Except.pure])
    | never => simp only [decodeToolPick, h, orNull, encodeToolChoice]; simp [reqStr, get, lookup, go, underStep]
    | tool n d => cases d <;> (simp only [decodeToolPick, h, orNull, encodeToolChoice]; simp [reqStr, optBool, opt, get, lookup, go, underStep, bind, Except.bind, pure, Except.pure])

/-! ### Reading what was written: each reader, then the request -/

theorem decodeMsgs_encode (v : Value) (ms : List Message) (hne : ms ≠ []) (h : get v "messages" = .arr (ms.map encodeMessage)) : decodeMsgs v = .ok ms := by
  cases ms with
  | nil => exact absurd rfl hne
  | cons m ms =>
    simp only [decodeMsgs, List.map_cons, h]
    rw [← List.map_cons, underStep_ok, decodeEach_encode _ _ decodeMsg_encodeMessage]

theorem decodeToolDecls_encode (v : Value) (ts : List Tool) (h : get v "tools" = orNull (fun ts => .arr (ts.map encodeTool)) (match ts with | [] => none | ts => some ts)) :
    decodeToolDecls v = .ok ts := by
  cases ts with
  | nil => simp [decodeToolDecls, h, orNull]
  | cons t ts =>
    simp only [orNull] at h
    simp only [decodeToolDecls, h, List.map_cons]
    rw [← List.map_cons, underStep_ok, decodeEach_encode _ _ decodeToolDecl_encodeTool]

theorem decodeStops_encode (v : Value) (ss : List String)
    (h : get v "stop_sequences" = orNull (fun ss => .arr (ss.map .str)) (match ss with | [] => none | ss => some ss)) : decodeStops v = .ok ss := by
  cases ss with
  | nil => simp [decodeStops, h, orNull]
  | cons s ss =>
    simp only [orNull] at h
    simp only [decodeStops, h, List.map_cons]
    rw [← List.map_cons, underStep_ok]
    exact decodeEach_encode _ .str (fun _ => rfl) (s :: ss) 0

theorem optStr_orNull (v : Value) (k : String) (o : Option String) (h : get v k = orNull .str o) : optStr v k = .ok o := by
  cases o <;> simp [optStr, h, orNull]

theorem reqNat_natNumber (v : Value) (k : String) (n : Nat) (h : get v k = .num (natNumber n)) : reqNat v k = .ok n := by
  simp [reqNat, optNat, h, natOf_natNumber]

/-- **The round trip.** Decoding an encoded request gives the request back, for every request that has a message (the schema requires one). -/
theorem decode_encode (r : Request) (h : r.messages ≠ []) : Request.decode r.encode = .ok r := by
  obtain ⟨ms, hms⟩ := encode_object r
  have g1 := encode_get_model r
  have g2 := encode_get_max_tokens r
  have g3 := encode_get_messages r
  have g4 := encode_get_system r
  have g5 := encode_get_tools r
  have g6 := encode_get_tool_choice r
  have g7 := encode_get_stream r
  have g8 := encode_get_temperature r
  have g9 := encode_get_top_p r
  have g10 := encode_get_top_k r
  have g11 := encode_get_stop_sequences r
  rw [hms] at g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 ⊢
  simp only [Request.decode, Request.decodeBody, bind, Except.bind, (reqStr_ok_iff _ _ _).2 g1, reqNat_natNumber _ _ _ g2, decodeMsgs_encode _ _ h g3, optStr_orNull _ _ _ g4,
    decodeToolDecls_encode _ _ g5, decodeToolPick_encode _ _ g6, optBool_orNull _ _ _ g7, optNum_orNull _ _ _ g8, optNum_orNull _ _ _ g9, optNat_orNull _ _ _ g10, decodeStops_encode _ _ g11, pure, Except.pure]

/-! ### Refusals (fail closed) -/

/-- A request that is not an object is refused. -/
theorem Request.decode_not_object (v : Value) (h : ∀ ms, v ≠ .obj ms) (r : Request) : Request.decode v ≠ .ok r := by
  cases v <;> simp [Request.decode] <;> exact absurd rfl (h _)

/-- `max_tokens` is required: a request without it is refused. -/
theorem reqNat_missing (v : Value) (h : get v "max_tokens" = .null) (n : Nat) : reqNat v "max_tokens" ≠ .ok n := by
  simp [reqNat, optNat, h]

theorem decodeMsgs_none (v : Value) (h : get v "messages" = .null) (ms : List Message) : decodeMsgs v ≠ .ok ms := by
  simp [decodeMsgs, h]

theorem decodeMsgs_empty (v : Value) (h : get v "messages" = .arr []) (ms : List Message) : decodeMsgs v ≠ .ok ms := by
  simp [decodeMsgs, h]

theorem decodeMsgs_not_array (v : Value) (h : ∀ xs, get v "messages" ≠ .arr xs) (h' : get v "messages" ≠ .null) (ms : List Message) : decodeMsgs v ≠ .ok ms := by
  unfold decodeMsgs; cases h2 : get v "messages" <;> simp_all

/-- A role the library does not model is refused, never read as another role. -/
theorem decodeMsg_unsupported_role (v : Value) (hv : ∃ ms, v = .obj ms) (w : String) (h : get v "role" = .str w) (hw : w ≠ "user" ∧ w ≠ "assistant") :
    decodeMsg v = .error { path := [.key "role"], kind := .unsupported w } := by
  obtain ⟨ms, rfl⟩ := hv
  obtain ⟨h1, h2⟩ := hw
  simp only [decodeMsg, reqStr, h]

/-- A block of a type the library does not model (an image, a document, a server-tool block) is refused, never dropped. -/
theorem decodeReqBlock_unsupported_type (v : Value) (hv : ∃ ms, v = .obj ms) (w : String) (h : get v "type" = .str w)
    (hw : w ≠ "text" ∧ w ≠ "tool_use" ∧ w ≠ "tool_result" ∧ w ≠ "thinking" ∧ w ≠ "redacted_thinking") :
    decodeReqBlock v = .error { path := [.key "type"], kind := .unsupported w } := by
  obtain ⟨ms, rfl⟩ := hv
  obtain ⟨h1, h2, h3, h4, h5⟩ := hw
  simp only [decodeReqBlock, reqStr, h]

/-- A `tool_choice` word outside `auto`, `any`, `none`, `tool` is refused as not modelled. -/
theorem decodeToolPick_unsupported (v : Value) (ms : List (String × Value)) (h : get v "tool_choice" = .obj ms) (w : String) (ht : get (.obj ms) "type" = .str w)
    (hw : w ≠ "auto" ∧ w ≠ "any" ∧ w ≠ "none" ∧ w ≠ "tool") :
    decodeToolPick v = .error { path := [.key "tool_choice", .key "type"], kind := .unsupported w } := by
  obtain ⟨h1, h2, h3, h4⟩ := hw
  simp only [decodeToolPick, h, reqStr, ht, underStep, Fault.under]

/-! ### What was read is stable under writing -/

theorem decodeMsgs_ne_nil (v : Value) (ms : List Message) (h : decodeMsgs v = .ok ms) : ms ≠ [] := by
  unfold decodeMsgs at h
  cases hg : get v "messages" <;> simp only [hg] at h <;> try (cases h; done)
  rename_i xs
  cases xs with
  | nil => cases h
  | cons x xs => exact VbmLlm.OpenAI.decodeEach_cons_ne_nil _ _ _ _ _ ((underStep_ok _ _ _).1 h)

/-- **A request that decodes is read back from its own encoding**: whatever a decode yields, `decode (encode r) = r` (a decoded request always has a message). -/
theorem decode_ok_stable (v : Value) (r : Request) (h : Request.decode v = .ok r) : Request.decode r.encode = .ok r := by
  apply decode_encode
  cases v <;> simp only [Request.decode] at h <;> try (cases h; done)
  simp only [Request.decodeBody, bind_ok_iff, pure_ok_iff] at h
  obtain ⟨_, _, _, _, ms, hms, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := h
  exact decodeMsgs_ne_nil _ _ hms

end VbmLlm.Anthropic
