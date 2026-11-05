# The pinned schema: Anthropic messages (response)

The convention is published as TypeScript type definitions in the vendor's SDK; there is no first-party machine-readable OpenAPI file for it. The library reads the type definitions, never the vendor's prose from memory.

| | |
|---|---|
| source | `https://raw.githubusercontent.com/anthropics/anthropic-sdk-typescript/08e2e5ffa7566e893d5be64f0e74a6658f7ee422/src/resources/messages/messages.ts` (the file at that commit of the SDK repository, committed 2026-11-04) |
| fetched | 2026-11-05, read only |
| sha256 of the document | `6f9d6f3421bcddceb423a7990c3c18bd1bc2b9deb62590245f85539511e1b6a5` (251,058 bytes) |
| components read | `Message`, `ContentBlock` (`TextBlock`, `ThinkingBlock`, `RedactedThinkingBlock`, `ToolUseBlock`; the other members are kept raw), `StopReason`, `Usage`; for the request: `MessageCreateParamsBase`, `MessageParam`, `ContentBlockParam` (`TextBlockParam`, `ThinkingBlockParam`, `RedactedThinkingBlockParam`, `ToolUseBlockParam`, `ToolResultBlockParam`; the other members are refused), `Tool`, `ToolChoice` |

The clause index (`clause-index.txt`) lists the properties read, decided by policy or ignored, under the convention name `anthropic-messages`. Fetching the file at another commit and finding another hash is a **schema bump**: read the diff of the components above, update the index and the decoder, then change this table; nothing else may move the pin.

## What the document says that the decoder relies on

* `Message` has `id`, `type: 'message'`, `role: 'assistant'`, `model`, `content: Array<ContentBlock>`, `stop_reason: StopReason | null`, `stop_sequence: string | null`, `usage: Usage`. The decoder requires only `content` (an array, which may be empty) and reads `id`, `model`, `stop_reason`, `stop_sequence` and `usage` when present: compatible servers omit them and the decoder reads what a consumer acts on.
* A `ContentBlock` is a union discriminated by `type`: `text` (`text`), `thinking` (`thinking`, `signature`), `redacted_thinking` (`data`), `tool_use` (`id`, `name`, `input: unknown`) and server-tool and result blocks. A block whose `type` is not one of the four modelled is **kept raw**.
* `StopReason` is `end_turn`, `max_tokens`, `stop_sequence`, `tool_use`, `pause_turn`, `refusal`, `model_context_window_exceeded`; any other word is kept and classed unknown.
* `Usage` has `input_tokens`, `output_tokens`, `cache_creation_input_tokens`, `cache_read_input_tokens` (the last two nullable) and others not read. `input_tokens` **excludes** the cache reads and writes (OpenAI's `prompt_tokens` includes the cache).

## Provenance of the vectors

`vectors/anthropic-messages/001` to `014` and `100` to `120` are built here from the shape the type definitions give (the text example in the `Message.content` comment, `Hi, I'm Claude.`, is `001`); none is a recorded reply of the service.

## What the document says that the request codec relies on

* `MessageCreateParamsBase` requires `max_tokens`, `messages` and `model`; `system` (a string or an array of text blocks), `tools`, `tool_choice`, `stream`, `temperature`, `top_p`, `top_k` and `stop_sequences` are optional. The encoder writes an absent field **left out**, never as `null`; the system prompt is a member of the request, not a message.
* A `MessageParam` is a `role` (`user` or `assistant`) and a `content` that is a string or an array of blocks; the encoder always writes the array form, the decoder reads a bare string as one text block. A tool call is a `ToolUseBlockParam` (`id`, `name`, `input`: here an object) in an assistant message, its answer a `ToolResultBlockParam` (`tool_use_id`, `content`, `is_error`) in the next user message. Content is modelled as text only: an image, a document or a server-tool block, the array form of a result's `content` and the array form of `system` are refused, never dropped.
* A `Tool` is `{name, description?, input_schema, strict?}` (the schema's server-tool variants have no `input_schema` and are refused); a `ToolChoice` is `auto`, `any`, `none` or `tool` (with its `name`); all but `none` carry an optional `disable_parallel_tool_use`.
* The numbers `temperature` and `top_p` are kept as number lexemes; their ranges are the provider's to enforce.

`vectors/anthropic-messages-request/001` and `002` carry, as the value of `messages`, the documented examples of that field (`Hello, Claude`; the three conversational turns), `003` the documented block form; the rest are built here from the shapes (the field list above) and each refusal.

## The turn rule (`anthropic-messages-turn` in the clause index)

The type document gives the shape of a `tool_use` block and of a `tool_result` block (`tool_use_id`, `content`, `is_error`) but not the sequence rule; the vendor's tool-use guide states in prose that each `tool_use` block is answered by a `tool_result` block among the first blocks of the user message that directly follows, and that results precede any text in that message. The turn machine (`VbmLlm.pair`, `VbmLlm.Anthropic.render`) decides that sequence from a recorded conversation: one assistant message (its text, then a `tool_use` block per call) and one user message whose first blocks are the results in call order; the window's user text follows the results in the same message; an unanswered call is shown with the placeholder; an orphan result is user text. Every clause is `policy`, checked by `vectors/anthropic-messages-turn/` and by a second, independent implementation of the pairing rule in the checker. That the provider **accepts** the sequence is not claimed. `vectors/anthropic-messages-turn/001` to `012` are the OpenAI turn records over the same conversations (the entries do not depend on the provider); `020` to `023` are built for this shape.

## The stream (`anthropic-messages-stream` in the clause index)

The type document gives the eight events of `RawMessageStreamEvent` (`message_start`, `content_block_start`, `content_block_delta`, `content_block_stop`, `message_delta`, `message_stop`, plus `ping` and `error` of the stream) and their deltas (`text_delta`, `input_json_delta`, `thinking_delta`, `signature_delta`, `citations_delta`); the vendor's streaming guide gives the order (one `message_start`, then blocks, then one or more `message_delta`, then `message_stop`; `ping` anywhere; an `error` may arrive at any point with the HTTP status still 200). The fold's terminal and ordering rules are stated from those as policy and checked by `vectors/anthropic-messages-stream/`, whose `*.single.json` twins are the reply the stream must fold to. A call's `input` arrives as `partial_json` pieces whose concatenation is parsed when the message completes. The counts of a `message_delta` are cumulative. `a001` to `a021` are built here from the event shapes; none is a recorded stream of the service.

