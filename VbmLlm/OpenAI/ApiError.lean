import VbmLlm.OpenAI.Response
/-! # OpenAI chat-completions: the body of a failed call

`ErrorResponse` (schema pinned in `docs/schemas/openai-chat.md`): `{"error": {"message", "type", "param", "code"}}`. Reading rules, as for the reply: `error` must be an object and `message` a string, both required;
`type`, `param` and `code` are strings or `null`, read when present, a present wrong type refused (the schema's numeric `code` of some compatible servers is **not** read as text: it is refused until an adapter says it may be a number).
The status of the call is not in the body: `VbmLlm.ErrorClass.ofStatus` classes it. -/
namespace VbmLlm.OpenAI
open LeanJson

structure ApiError where
  message : String
  type : Option String
  param : Option String
  code : Option String
  deriving DecidableEq, Repr

/-- **Decode the body of a failed call.** -/
def decodeApiError (v : Value) : Except Fault ApiError :=
  match v with
  | .obj _ => do
    let e ← reqObj v "error"
    underStep (.key "error") (do
      let message ← reqStr e "message"
      let type ← optStr e "type"
      let param ← optStr e "param"
      let code ← optStr e "code"
      pure { message, type, param, code })
  | _ => .error (Fault.here (.wrongType .object))

end VbmLlm.OpenAI
