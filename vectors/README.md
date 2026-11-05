# Conformance vectors

`openai-chat/NAME.json` is a reply as a server sends it (or a malformed one); `NAME.expect` is what the library makes of it: `ok` and the rendering of the decoded reply, or `error` and the refusal (its path and kind).
`lake exe vbm-llm-vectors --check` decodes every vector with the compiled library and compares; `--selftest` shows the check can fail (a tampered expectation, a missing vector); `--write` regenerates the expectations, to be **read and committed by a reviewer**.

* `001` to `004`: the response examples of `POST /chat/completions` in the pinned OpenAI document, unchanged (`docs/schemas/openai-chat.md`).
* `010` to `020`: built to exercise the policy (omitted fields, two choices, empty and truncated tool arguments, an unlisted finish reason, cached tokens, duplicate keys, a contradictory usage report).
* `100` to `120`: one refusal each (not an object, no `choices`, empty, wrong types, a custom tool call, an object where `arguments` must be a string, bad counts, a bad second element, not JSON).

These are conformance and regression evidence: the expectations are the library's own rendering, read by a reviewer. They prove nothing; the ledger's claims are the proofs.
