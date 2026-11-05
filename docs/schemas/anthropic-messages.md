# The pinned schema: Anthropic messages (response)

The convention is published as TypeScript type definitions in the vendor's SDK; there is no first-party machine-readable OpenAPI file for it. The library reads the type definitions, never the vendor's prose from memory.

| | |
|---|---|
| source | `https://raw.githubusercontent.com/anthropics/anthropic-sdk-typescript/08e2e5ffa7566e893d5be64f0e74a6658f7ee422/src/resources/messages/messages.ts` (the file at that commit of the SDK repository, committed 2026-11-04) |
| fetched | 2026-11-05, read only |
| sha256 of the document | `6f9d6f3421bcddceb423a7990c3c18bd1bc2b9deb62590245f85539511e1b6a5` (251,058 bytes) |
| components read | `Message`, `ContentBlock` (`TextBlock`, `ThinkingBlock`, `RedactedThinkingBlock`, `ToolUseBlock`; the other members are kept raw), `StopReason`, `Usage` |

The clause index (`clause-index.txt`) lists the properties read, decided by policy or ignored, under the convention name `anthropic-messages`. Fetching the file at another commit and finding another hash is a **schema bump**: read the diff of the components above, update the index and the decoder, then change this table; nothing else may move the pin.

## What the document says that the decoder relies on

* `Message` has `id`, `type: 'message'`, `role: 'assistant'`, `model`, `content: Array<ContentBlock>`, `stop_reason: StopReason | null`, `stop_sequence: string | null`, `usage: Usage`. The decoder requires only `content` (an array, which may be empty) and reads `id`, `model`, `stop_reason`, `stop_sequence` and `usage` when present: compatible servers omit them and the decoder reads what a consumer acts on.
* A `ContentBlock` is a union discriminated by `type`: `text` (`text`), `thinking` (`thinking`, `signature`), `redacted_thinking` (`data`), `tool_use` (`id`, `name`, `input: unknown`) and server-tool and result blocks. A block whose `type` is not one of the four modelled is **kept raw**.
* `StopReason` is `end_turn`, `max_tokens`, `stop_sequence`, `tool_use`, `pause_turn`, `refusal`, `model_context_window_exceeded`; any other word is kept and classed unknown.
* `Usage` has `input_tokens`, `output_tokens`, `cache_creation_input_tokens`, `cache_read_input_tokens` (the last two nullable) and others not read. `input_tokens` **excludes** the cache reads and writes (OpenAI's `prompt_tokens` includes the cache).

## Provenance of the vectors

`vectors/anthropic-messages/001` to `014` and `100` to `120` are built here from the shape the type definitions give (the text example in the `Message.content` comment, `Hi, I'm Claude.`, is `001`); none is a recorded reply of the service.
