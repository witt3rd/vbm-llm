import VbmLlm.OpenAI.Response
/-! # OpenRouter chat-completions: the body of a failed call

OpenRouter's chat profile is OpenAI's with four deviations (the pinned pages: `docs/schemas/openrouter-chat.md`): the final usage frame of a stream carries `choices`; each choice carries a `native_finish_reason`;
a failure after the stream began arrives as a chunk with a top-level `error` and `finish_reason` `"error"` (the fold of `VbmLlm/OpenAI/Stream.lean` already stops there); comment lines keep the connection alive.
Reading these needs no new decoder: unread members are ignored, a usage report is read from any frame, an `error` member makes a chunk an error chunk, comments are the event splitter's. What differs for a **failed call** is
the `code` of the error body: before the stream is committed it is a **number** (the HTTP status: `{"error": {"code": 400, "message": ...}}`), mid-stream a string. `decodeApiError` reads either, as itself, never one as the other. -/
namespace VbmLlm.OpenRouter
open LeanJson VbmLlm.OpenAI

/-- An error's `code`: a word, or a plain natural (the status). -/
inductive Code where
  | text (s : String)
  | num (n : Nat)
  deriving DecidableEq, Repr

structure ApiError where
  message : String
  code : Option Code
  deriving DecidableEq, Repr

def optCode (e : Value) : Except Fault (Option Code) :=
  match get e "code" with
  | .null => .ok none
  | .str s => .ok (some (.text s))
  | .num n =>
    match natOf n with
    | some m => .ok (some (.num m))
    | none => .error { path := [.key "code"], kind := .wrongType .natural }
  | _ => .error { path := [.key "code"], kind := .wrongType .string }

/-- **Decode the body of a failed call**: `error` an object, `message` a string, `code` a word or a natural. -/
def decodeApiError (v : Value) : Except Fault ApiError :=
  match v with
  | .obj _ => do
    let e ← reqObj v "error"
    underStep (.key "error") (do
      let message ← reqStr e "message"
      let code ← optCode e
      pure { message, code })
  | _ => .error (Fault.here (.wrongType .object))

end VbmLlm.OpenRouter
