# The pinned schema: OpenAI chat-completions (response and request)

The convention is a published, versioned, machine-readable document; the library reads it, never the vendor's prose from memory.

| | |
|---|---|
| source | `https://raw.githubusercontent.com/openai/openai-openapi/manual_spec/openapi.yaml` (OpenAPI 3.0.0, `info.version` 2.3.0, the repository's `manual_spec` branch) |
| fetched | 2026-11-05, read only |
| sha256 of the document | `6a6c681b182002de4ad335fa80214158f2d8f383a418f865c87876c3ed67cad9` (1,376,003 bytes) |
| components read | `CreateChatCompletionResponse`, `ChatCompletionResponseMessage`, `ChatCompletionMessageToolCalls`, `ChatCompletionMessageToolCall`, `CompletionUsage`, `CreateChatCompletionStreamResponse`, `ChatCompletionStreamResponseDelta`, `ChatCompletionMessageToolCallChunk`; for the request: `CreateChatCompletionRequest`, `ChatCompletionRequestMessage` (the system, developer, user, assistant and tool messages), `ChatCompletionTool`, `FunctionObject`, `ChatCompletionToolChoiceOption`, `ChatCompletionNamedToolChoice`, `ChatCompletionStreamOptions`; for a failed call: `ErrorResponse`, `Error`; the response examples of `POST /chat/completions` |

The clause index (`clause-index.txt` in this directory's parent) lists every property of these components as read, policy or ignored. Fetching the document again and finding another hash is a **schema bump**: read the diff of the components above, update the index and the decoder, then change this table; nothing else may move the pin.

## What the document says that the decoder relies on

* `CreateChatCompletionResponse` requires `choices`, `created`, `id`, `model`, `object`. The decoder requires only `choices` (and that it is non-empty): compatible servers omit the others, and the decoder reads what a consumer acts on. `id` and `model` are read when present.
* A choice requires `finish_reason` (an enum of `stop`, `length`, `tool_calls`, `content_filter`, `function_call`), `index`, `message`, `logprobs`. The decoder requires `message`, keeps `finish_reason` as the provider's text when it is a string (a word outside the enum is kept and classed `unknown`), and reads `index` when present.
* `ChatCompletionResponseMessage` requires `role`, `content` (string or null), `refusal` (string or null). `tool_calls` is an array of `ChatCompletionMessageToolCall`.
* `ChatCompletionMessageToolCall` requires `id`, `type` (the enum `function` only, in this version), `function` with `name` and `arguments`, both strings: `arguments` is JSON **text** that the model may have got wrong, and is kept verbatim.
* `CompletionUsage` requires `prompt_tokens`, `completion_tokens`, `total_tokens` (integers); `prompt_tokens_details.cached_tokens` and `completion_tokens_details.reasoning_tokens` are optional detail counts. `prompt_tokens` includes the cached tokens, `completion_tokens` the reasoning tokens.

## What the document says that the request encoder relies on

* `CreateChatCompletionRequest` requires `model` and `messages` (at least one); `tools` (functions only), `tool_choice` (`none`, `auto`, `required` or a named function), `parallel_tool_calls`, `stream`, `stream_options.include_usage`, `max_completion_tokens`, `max_tokens` (deprecated, still the member compatible servers read), `temperature` and `top_p` are optional and nullable. The encoder writes an absent field **left out**, never as `null`.
* A message is one of `system`, `developer`, `user`, `assistant`, `tool` (the deprecated `function` role is not modelled). `content` is modelled as its string form, plus **one** array form: the one-part text array that carries the cache marker (`cache-marker` in the clause index). The schema also allows other arrays of content parts (images, audio, files for the user; two text parts), which are not modelled: the decoder refuses them rather than dropping a part. An assistant message requires `role` and carries `content` unless it has `tool_calls`; a tool message requires `role`, `content` and `tool_call_id`.
* **The cache marker is not in the pinned document.** Some providers cache a prompt prefix only when one content part carries `cache_control: {"type": "ephemeral"}`, and a request without it re-bills the whole prompt. `cache_control` is no member of any content part of the pinned schema, so the shape (`[{"type": "text", "text": ..., "cache_control": {"type": "ephemeral"}}]`) is a `policy` clause of this library, not a clause of the document: the encoder writes it only when a caller names one message (`Request.encodeWith`, with `markable` and `lastMarkable` to choose it), at most one message of a request carries it, a named message that cannot carry one (an assistant turn of calls only, which has no content part) or an index past the end writes no marker at all, and with no marker requested the encoding is exactly the encoding of the schema's own shape. Which providers honour the marker, and what they charge for it, is client behaviour and not claimed here.
* A tool is `{type: "function", function: {name, description?, parameters?, strict?}}`; `parameters` is a JSON Schema object the library does not look into.
* The numbers `temperature` and `top_p` are kept as number lexemes (the pinned `vbm-json` never reads a number as a float); the schema's ranges (0 to 2, 0 to 1) are the provider's to enforce.

## Provenance of the vectors

`vectors/openai-chat/001` to `004` are the response examples (Default, Image input, Functions, Logprobs) of `POST /chat/completions` in this document, the text is copied unchanged. `vectors/openai-chat-request/001` to `005` are the request examples (Default, Image input, Streaming, Functions, Logprobs) of the same operation, the JSON bodies copied unchanged out of the `curl` examples (re-indented). The rest are built here to exercise the policy (omitted fields, two choices, empty arguments, truncated arguments, unknown finish reasons, cached tokens, duplicate keys) and each refusal.

## The stream framing (`openai-chat-sse` in the clause index)

The OpenAPI document gives the shape of a chunk but not the framing. The framing the library relies on, from the vendor's streaming description and OpenRouter's documented examples (`https://openrouter.ai/docs/api-reference/streaming`, read 2026-11-05): events carry only `data` lines, no `event:` type; the stream ends with the sentinel `data: [DONE]`; the final usage frame (`stream_options.include_usage`) has an empty `choices`; a chunk may carry an `error` after content has been sent, with the HTTP status still 200. These are `policy` clauses, stated as policy because no machine-readable source pins them; they are checked by the recorded streams in `vectors/openai-chat-stream/`.

## The turn rule (`openai-chat-turn` in the clause index)

The schema gives the shape of an assistant message with `tool_calls` and of a `tool` message (`tool_call_id`, `content`) but not the sequence rule; the vendor's function-calling guide states in prose that every call must be answered by a `tool` message carrying its id, directly after the assistant message. The turn machine (`VbmLlm.pair`, `VbmLlm.OpenAI.render`) decides that sequence from a recorded conversation; every clause is `policy` and is checked by the recorded conversations in `vectors/openai-chat-turn/`, whose rendering is also checked by a second, independent implementation of the rule in the checker. That the provider **accepts** the sequence is not claimed.

## The error body and the status class (`openai-chat` `Error*`, `openai-chat-status`)

`ErrorResponse` is `{error: Error}` and `Error` requires `type`, `message`, `param` and `code` (`param` and `code` nullable strings). The decoder requires the `error` object and the string `message` and reads the other three when present (a compatible server that omits them is not refused). The status of a failed call is not in the body; its class (`VbmLlm.ErrorClass.ofStatus`) is the standard meaning of the status, stated as `policy` clauses because no machine-readable source pins it, and checked by the recorded failed calls in `vectors/openai-chat-error/` (built here: the bodies follow the schema's shape and the vendor's documented error pages). Whether the message says the context was too long is a heuristic and stays the consumer's: it is a parameter, never decided here.
