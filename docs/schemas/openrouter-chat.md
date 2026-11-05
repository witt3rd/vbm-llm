# The pinned documents: OpenRouter chat-completions (the deviations from OpenAI's)

OpenRouter publishes its chat profile as documentation pages (Markdown, the response schema as TypeScript) and states that it "normalizes the schema to comply with the OpenAI Chat API". The adapter is OpenAI's plus four deviations; the library reads the pages, never the vendor's prose from memory.

| page | source | fetched | sha256 |
|---|---|---|---|
| Streaming | `https://openrouter.ai/docs/api-reference/streaming.md` (10,074 bytes) | 2026-11-05, read only | `6d055bdcff265cadf9ff7a094772fcd145872a1d279994c689024ef46ee43fb5` |
| API overview | `https://openrouter.ai/docs/api-reference/overview.md` (18,737 bytes) | 2026-11-05, read only | `254df1df41593b7ac240dc80f4e32375424988fce02600ab060deb4dc06caff2` |

The pages are not versioned: fetching them again and finding another hash is a **schema bump**: read the diff, update the index (`openrouter-chat` in `clause-index.txt`) and the decoders, then change this table; nothing else may move the pin.

## The four deviations, and what the library does with each

1. **The final usage frame of a stream has `choices`** (OpenAI's has none): the frame repeats the last `finish_reason`. The fold reads a usage report from any frame, whatever its `choices` (a repeated finish reason leaves the reply as it was): checked on the recorded stream `o001` and its single-shot twin.
2. **`native_finish_reason`** (the provider's own word) beside `finish_reason`: not read (the normalized `finish_reason` is; an unread member is ignored); the normalized word `error` is its own finish class (`FinishClass.ofOpenRouter`).
3. **A failure after the stream began** arrives as a chunk with a top-level `error` and `finish_reason: "error"`, HTTP status still 200, possibly the first and only chunk: the fold stops there and returns the message and the partial reply (an `error chunk` outcome, never a complete reply: vectors `o002`, `o003`).
4. **Comment lines** (`: OPENROUTER PROCESSING`) keep the connection alive: the event splitter's (a comment is not an event).

Also, **the `code` of an error body is a number before the stream is committed** (`{"error": {"code": 400, "message": ...}}`, the HTTP status) and a word mid-stream: `OpenRouter.decodeApiError` reads either, as itself (a fraction or any other type is refused). A parameter the chosen model does not support is **ignored by the provider**: nothing the wire contract can say.

## Provenance of the vectors

`vectors/openai-chat-stream/o001` to `o003` and `vectors/openrouter-chat-error/` are built here from the shapes the two pages show (the abridged chunk examples of the Streaming page, the `{"error": {"code": 400, ...}}` example); none is a recorded reply of the service.
