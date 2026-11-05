# The pinned schema: OpenAI chat-completions (response)

The convention is a published, versioned, machine-readable document; the library reads it, never the vendor's prose from memory.

| | |
|---|---|
| source | `https://raw.githubusercontent.com/openai/openai-openapi/manual_spec/openapi.yaml` (OpenAPI 3.0.0, `info.version` 2.3.0, the repository's `manual_spec` branch) |
| fetched | 2026-11-05, read only |
| sha256 of the document | `6a6c681b182002de4ad335fa80214158f2d8f383a418f865c87876c3ed67cad9` (1,376,003 bytes) |
| components read | `CreateChatCompletionResponse`, `ChatCompletionResponseMessage`, `ChatCompletionMessageToolCalls`, `ChatCompletionMessageToolCall`, `CompletionUsage`; the response examples of `POST /chat/completions` |

The clause index (`clause-index.txt` in this directory's parent) lists every property of these components as read, policy or ignored. Fetching the document again and finding another hash is a **schema bump**: read the diff of the components above, update the index and the decoder, then change this table; nothing else may move the pin.

## What the document says that the decoder relies on

* `CreateChatCompletionResponse` requires `choices`, `created`, `id`, `model`, `object`. The decoder requires only `choices` (and that it is non-empty): compatible servers omit the others, and the decoder reads what a consumer acts on. `id` and `model` are read when present.
* A choice requires `finish_reason` (an enum of `stop`, `length`, `tool_calls`, `content_filter`, `function_call`), `index`, `message`, `logprobs`. The decoder requires `message`, keeps `finish_reason` as the provider's text when it is a string (a word outside the enum is kept and classed `unknown`), and reads `index` when present.
* `ChatCompletionResponseMessage` requires `role`, `content` (string or null), `refusal` (string or null). `tool_calls` is an array of `ChatCompletionMessageToolCall`.
* `ChatCompletionMessageToolCall` requires `id`, `type` (the enum `function` only, in this version), `function` with `name` and `arguments`, both strings: `arguments` is JSON **text** that the model may have got wrong, and is kept verbatim.
* `CompletionUsage` requires `prompt_tokens`, `completion_tokens`, `total_tokens` (integers); `prompt_tokens_details.cached_tokens` and `completion_tokens_details.reasoning_tokens` are optional detail counts. `prompt_tokens` includes the cached tokens, `completion_tokens` the reasoning tokens.

## Provenance of the vectors

`vectors/openai-chat/001` to `004` are the response examples (Default, Image input, Functions, Logprobs) of `POST /chat/completions` in this document, the text is copied unchanged. The rest are built here to exercise the policy (omitted fields, two choices, empty arguments, truncated arguments, unknown finish reasons, cached tokens, duplicate keys) and each refusal.
