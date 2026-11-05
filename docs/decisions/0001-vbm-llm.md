# 0001. vbm-llm: the wire contract, proved, and nothing else

Status: accepted for the scaffold and the first slice (the OpenAI chat-completions response decoder). The policies in section 4 are the working assumption; each is a claim in the ledger.

## 1. Decision

**A library of the wire contract of three published conventions** (OpenAI chat-completions, Anthropic messages, OpenRouter's variants), written once in Lean over the verified JSON value of `vbm-json`, as one adapter per convention over a neutral core:
request and response codecs, the streaming delta fold, the tool-call turn pairing state machine, usage-field arithmetic (`prompt_tokens` **includes** the cache, Anthropic's `input_tokens` **excludes** it) and the finish-reason and error taxonomy.

What is provable is the **wire contract**. What is not is **client behaviour**: that a provider honours a field, that tool arguments are valid JSON or fit their schema, retry, failover and authentication policy, prices, model names and capabilities, cancellation and billing. The library carries none of it:
no HTTP, no retries, no credentials, no prices, **no model names** (a model is an opaque string), no capability tables. A consumer decides what to do with a reply; the library says what the reply is.

## 2. Shape

* `VbmLlm/` (the spec and the code, one Lean core): imports `Init`, the pinned `LeanJson` and itself only (Tier 1 scans the imports). `VbmLlmProofs/`: may import `Std` and `Lean`, never linked, nothing in `VbmLlm` imports it.
* One module per convention under `VbmLlm/<Convention>/`; the neutral pieces (`Wire`, `Fault`, `Finish`, `Usage`) at the root.
* **Fail closed, with typed refusals.** A reply that does not fit is refused with a `Fault` (a path and a kind from a closed set), never guessed at. An unlisted *word* (a finish reason a provider adds) is kept and classed `unknown`, because refusing it would stop a consumer on the day a provider adds one.
* **One adapter per convention, each pinned to a schema hash** (`docs/schemas/`): the clause index (`docs/clause-index.txt`) is data read from the pinned document; ledger claims are tagged with the clauses they are about; the ledger gate fails on a tag that is not in the index and prints the coverage.

## 3. Dependencies

* `vbm-json`, a lake dependency pinned by revision (`lakefile.lean`) **and** by hash of its specification files (`scripts/pinned-libs.lock`, checked by `scripts/pinned-lib.py verify` in Tier 1: the manifest's revision, the checkout's HEAD and the hash of the library's spec files must all equal the lock; a stale revision, an edited file, a fork or an unlocked package fails). The revision is the one the first consumer pins: every library of the family pins `vbm-json` to the **same** revision (a diamond through a shared dependency needs one agreed revision).
* `vbm-sse` (server-sent events) when it exists: pinned the same way. Until then the stream fold is written against a stubbed event interface (`Event`: type, data, id), so the interface, not the implementation, is the contract.
* `vbm-land`, vendored and pinned (`scripts/land/PIN`), the landing tool.

## 4. The pinned policies of the reply decoders

1. `null` and an absent key are the same ("not there"); a key's **last** binding wins (the policy `vbm-json` states for duplicates).
2. A field that is read and **present** must have its type: a wrong type is refused, never coerced.
3. A count is a plain natural: a sign, a fraction, an exponent or a string is refused. An absent count stays absent in the raw report; the normalized record reads it as 0 (a frame with no report adds nothing).
4. Required: for a reply, a non-empty `choices` array; for a choice, a `message` object; for a tool call, `id`, `function.name` and `function.arguments` strings. Everything else is read when present and ignored when absent. A tool call whose `type` is present must be `function`.
5. Tool-call `arguments` are kept **verbatim**. Whether they are valid JSON is not a wire question.
6. A finish reason is kept as the provider's text and classed by a total map; truncation (`length`) is a class of its own because a truncated tool call's arguments end mid-JSON.
7. A contradictory usage report (more cached than prompt tokens) is refused when normalized, never clamped.
8. Unread fields are ignored and listed in the clause index as such.

## 5. The stream fold (policies)

A stream folds to exactly one **outcome**: `complete` (the sentinel was seen and nothing followed it), `truncated` (the events ended with no sentinel: the partial reply is typed as partial, never presented as complete), or `errorChunk` (a chunk carried an error: the fold stops there with the message and the partial reply; whether to discard what was received is the consumer's decision). Merge rules: the first `id`/`model`, the first tool-call `id`/`name` win; text, refusal and arguments concatenate in order; the last non-null `usage` and the last non-null `finish_reason` win; choices and tool calls are keyed by `index` in order of first appearance. A missing `index` is refused unless the policy reads it as 0 (the schema requires it); an event with a type the convention does not use is refused; an event with empty data is ignored; a `complete` reply has a choice and every call has an id and a name. The fold starts from **events** (`VbmLlm.Event`), the interface of `vbm-sse`: a conformance checker's splitter stands in until it is pinned.

## 6. What is not here yet

The request codec, the tool-call turn machine, the Anthropic adapter and OpenRouter's variants are open claims in the ledger, in that order. The closure gate (the specified share of the executed mass) of the project these gates were first built in is not ported: every claim here names theorems about the functions that are the library.
