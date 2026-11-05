import VbmLlm.Anthropic.Request
/-! # Anthropic messages: the request, read back (fail closed)

The same typed request as `Request.lean`, decoded from a parsed `LeanJson.Value` (for tests, replays and servers: a consumer that only sends never calls it). Reading rules: `model`, `max_tokens` and
`messages` (non-empty) are required; every other member is read when present and absent (or empty) when not there or `null`; a present member of the wrong type is refused, never coerced; a `role`
outside `user` and `assistant`, a block `type` outside the five modelled (an image, a document, a server-tool block) and a `content` that is not a string (the array of parts form of a result, the array form
of the system prompt) are refused as not modelled, never dropped; a message `content` that is a bare string is read as one text block; members the type does not model are ignored. -/
namespace VbmLlm.Anthropic
open LeanJson VbmLlm.OpenAI

/-- A required object member, as its members. -/
def reqMembers (o : Value) (k : String) : Except Fault (List (String × Value)) :=
  match get o k with
  | .null => .error { path := [.key k], kind := .missing }
  | .obj ms => .ok ms
  | _ => .error { path := [.key k], kind := .wrongType .object }

/-- A required natural member. -/
def reqNat (o : Value) (k : String) : Except Fault Nat :=
  match optNat o k with
  | .ok (some n) => .ok n
  | .ok none => .error { path := [.key k], kind := .missing }
  | .error e => .error e

def decodeReqBlock (v : Value) : Except Fault ReqBlock :=
  match v with
  | .obj _ =>
    match reqStr v "type" with
    | .ok "text" => ReqBlock.text <$> reqStr v "text"
    | .ok "tool_use" => do pure (.toolUse (← reqStr v "id") (← reqStr v "name") (← reqMembers v "input"))
    | .ok "tool_result" => do pure (.toolResult (← reqStr v "tool_use_id") (← optStr v "content") (← optBool v "is_error"))
    | .ok "thinking" => do pure (.thinking (← reqStr v "thinking") (← reqStr v "signature"))
    | .ok "redacted_thinking" => ReqBlock.redactedThinking <$> reqStr v "data"
    | .ok other => .error { path := [.key "type"], kind := .unsupported other }
    | .error e => .error e
  | _ => .error (Fault.here (.wrongType .object))

/-- `content`: an array of blocks, or a bare string read as one text block. -/
def decodeMsgContent (v : Value) : Except Fault (List ReqBlock) :=
  match get v "content" with
  | .null => .error { path := [.key "content"], kind := .missing }
  | .str s => .ok [.text s]
  | .arr xs => underStep (.key "content") (decodeEach decodeReqBlock xs 0)
  | _ => .error { path := [.key "content"], kind := .wrongType .array }

def decodeMsg (v : Value) : Except Fault Message :=
  match v with
  | .obj _ =>
    match reqStr v "role" with
    | .ok "user" => do pure ⟨.user, ← decodeMsgContent v⟩
    | .ok "assistant" => do pure ⟨.assistant, ← decodeMsgContent v⟩
    | .ok other => .error { path := [.key "role"], kind := .unsupported other }
    | .error e => .error e
  | _ => .error (Fault.here (.wrongType .object))

def decodeToolDecl (v : Value) : Except Fault Tool :=
  match v with
  | .obj _ => do pure { name := ← reqStr v "name", description := ← optStr v "description", inputSchema := ← reqMembers v "input_schema", strict := ← optBool v "strict" }
  | _ => .error (Fault.here (.wrongType .object))

/-- `tool_choice`: an object whose `type` is `auto`, `any`, `none` or `tool` (with its `name`); any other word is refused as not modelled. -/
def decodeToolPick (v : Value) : Except Fault (Option ToolChoice) :=
  match get v "tool_choice" with
  | .null => .ok none
  | .obj ms => underStep (.key "tool_choice") (
      match reqStr (.obj ms) "type" with
      | .ok "auto" => do pure (some (.auto (← optBool (.obj ms) "disable_parallel_tool_use")))
      | .ok "any" => do pure (some (.any (← optBool (.obj ms) "disable_parallel_tool_use")))
      | .ok "none" => .ok (some .never)
      | .ok "tool" => do pure (some (.tool (← reqStr (.obj ms) "name") (← optBool (.obj ms) "disable_parallel_tool_use")))
      | .ok other => .error { path := [.key "type"], kind := .unsupported other }
      | .error e => .error e)
  | _ => .error { path := [.key "tool_choice"], kind := .wrongType .object }

def decodeMsgs (v : Value) : Except Fault (List Message) :=
  match get v "messages" with
  | .null => .error { path := [.key "messages"], kind := .missing }
  | .arr [] => .error { path := [.key "messages"], kind := .empty }
  | .arr xs => underStep (.key "messages") (decodeEach decodeMsg xs 0)
  | _ => .error { path := [.key "messages"], kind := .wrongType .array }

def decodeToolDecls (v : Value) : Except Fault (List Tool) :=
  match get v "tools" with
  | .null => .ok []
  | .arr xs => underStep (.key "tools") (decodeEach decodeToolDecl xs 0)
  | _ => .error { path := [.key "tools"], kind := .wrongType .array }

def decodeStops (v : Value) : Except Fault (List String) :=
  match get v "stop_sequences" with
  | .null => .ok []
  | .arr xs => underStep (.key "stop_sequences") (decodeEach (fun x => match x with | .str s => .ok s | _ => .error (Fault.here (.wrongType .string))) xs 0)
  | _ => .error { path := [.key "stop_sequences"], kind := .wrongType .array }

def Request.decodeBody (v : Value) : Except Fault Request := do
  pure { model := ← reqStr v "model", maxTokens := ← reqNat v "max_tokens", messages := ← decodeMsgs v, system := ← optStr v "system", tools := ← decodeToolDecls v,
         toolChoice := ← decodeToolPick v, stream := ← optBool v "stream", temperature := ← optNum v "temperature", topP := ← optNum v "top_p", topK := ← optNat v "top_k",
         stopSequences := ← decodeStops v }

/-- **Decode a request.** -/
def Request.decode (v : Value) : Except Fault Request :=
  match v with
  | .obj _ => Request.decodeBody v
  | _ => .error (Fault.here (.wrongType .object))

end VbmLlm.Anthropic
