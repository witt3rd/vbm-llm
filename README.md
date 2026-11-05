# vbm-llm

The **wire contract** of the LLM provider conventions, written once in Lean 4 and machine-checked: what a conforming reply is, how its usage numbers add up, why a generation stopped. One adapter per convention, over a neutral core. It is a codec library, not a client: no HTTP, no retries, no authentication, no prices and no model names (a model is an opaque string in a field).

> **Status: pre-release, private.** The first convention is in: **OpenAI chat-completions: the response of one non-streaming call, and the fold of a stream of events into one outcome**. Nothing is published to a package registry; build from source. The API may still change.

| convention | request | response | stream | tool-call turns | usage | finish reasons |
|---|---|---|---|---|---|---|
| OpenAI chat-completions | planned | **decoded and proved** | **folded, merge rules and terminal rule proved** | planned | **arithmetic proved** | **classed, total** |
| Anthropic messages | planned | planned | planned | planned | planned | planned |
| OpenRouter's variants | planned | planned | planned | planned | planned | planned |

## What is proved, and what is not

The specification is the code that runs: `VbmLlm/` imports only Lean's `Init` and the pinned [vbm-json](https://github.com/witt3rd/vbm-json) (so a reply is read from the same verified parse everywhere). The proofs are in `VbmLlmProofs/` and are never linked. The ledger (`docs/proof-ledger.md`, generated) says which claims are proved and which are open, and tags each claim with the clause of the published schema it is about (`docs/clause-index.txt`). Only a `proved` claim is called verified.

Proved today, of the response decoder (`VbmLlm/OpenAI/Response.lean`): it accepts exactly the replies that are objects with a non-empty `choices` array of choices with a `message` object, string-or-null text, tool calls of the shape `{id, function: {name, arguments}}` (the arguments kept verbatim: the model's text, never parsed), and plain-natural usage counts (`decode_ok_iff`); a present field of the wrong type is refused and never coerced; a tool call of another type is refused as unsupported; every refusal names its path and kind. Of the usage arithmetic (`VbmLlm/Usage.lean`): OpenAI's `prompt_tokens` includes the cached tokens, and the normalized record's input parts add up to it; a contradictory report is refused, never clamped; totals add over a turn and a run. Of the stream fold (`VbmLlm/OpenAI/Stream.lean`, over server-sent events: the interface is stubbed until `vbm-sse` is pinned): the first `id`/`model` and the first tool-call `id`/`name` win, text and arguments concatenate so that **chunk boundaries do not matter**, the last non-null `usage` wins; a stream with no sentinel is `truncated` and never `complete`, nothing may follow the sentinel, an error chunk stops the fold and hands over its message with the partial reply (the consumer decides whether to discard it), a fragment with no `index` is refused unless the policy reads it as 0. The whole equality *a stream folds to exactly the single-shot reply* is proved for text and arguments split anywhere and checked on recorded streams (`vectors/openai-chat-stream/*.single.json`); for every interleaving it is still open (the ledger says so). Of the finish reason: a total map from the provider's words onto a closed set of classes, with unknown words kept.

**Not proved** (the ledger's `limit` claims): that a server sends what its schema says; that tool arguments are valid JSON or fit the tool's parameters; that a clause of the schema is stated faithfully (checked by review); that the parse of the bytes is the RFC 8259 reference (that is vbm-json's claim, pinned here by revision and hash).

## Using it

```lean
import VbmLlm
open VbmLlm.OpenAI

-- `bytes : ByteArray` is the body of a reply
match LeanJson.parseFast bytes with
| .error _ => ...                      -- not JSON: the pinned parser refused it
| .ok v =>
  match decode v with
  | .error f => ... f.render ...       -- a typed refusal: a path and a kind
  | .ok reply => ... reply.choices ... -- the typed reply
```

`VbmLlm.OpenAI.Usage.tokens` turns the report into the normalized record (`inputUncached`, `inputCacheRead`, `inputCacheWrite`, `output`, `reasoning`); `VbmLlm.FinishClass.ofOpenAI` classes a finish reason. `docs/consumption.md` says what a verified agent harness can delete once it consumes each slice.

## Build and test

Everything runs as `mise exec -- ...` (Lean 4.35.0, pinned in `mise.toml`). `mise exec -- scripts/tier1.sh` is the gate before landing: forbidden constructs, import rule, zero-warning build, the axiom gate, the obligation ledger with its spec-clause tags, the trust ledger, the pinned-library check, the conformance vectors (`vectors/`: the published schema's own examples plus refusals), and the self-tests of the process scripts. Every gate has a negative self-test.

## How it is built

Agents write it, under mechanical gates instead of line-by-line review; the standard is VBM (verified bare metal), see [the VBM standard](https://github.com/witt3rd/vbm). Direction and the pinned policies: `docs/decisions/0001-vbm-llm.md`. Landing: `scripts/land-direct` (a pinned copy of [vbm-land](https://github.com/witt3rd/vbm-land)); the scorecard adapter is `scorecard.toml`.

## License

Apache-2.0. See [LICENSE](LICENSE) and [NOTICE](NOTICE).
