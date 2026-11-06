# vbm-llm

The **wire contract** of the LLM provider conventions, written once in Lean 4 and machine-checked: what a conforming reply is, how its usage numbers add up, why a generation stopped. One adapter per convention, over a neutral core. It is a codec library, not a client: no HTTP, no retries, no authentication, no prices and no model names (a model is an opaque string in a field).

> **Status: pre-release.** Nothing is published to a package registry; build from source. The API may still change. Today the library covers the **reply side of all three conventions**, the **request codec and the tool-call turn machine of OpenAI chat-completions and of Anthropic messages**, and the **stream fold of OpenAI and of Anthropic (named events)**. The Anthropic error body is the remaining open piece of that adapter (`docs/decisions/0001-vbm-llm.md`, section 6). The scorecard card is linked under [Score](#score).

| convention | request | response | stream | tool-call turns | usage | finish reasons | error |
|---|---|---|---|---|---|---|---|
| OpenAI chat-completions | **encoded, decoded, round trip proved** | **decoded and proved** | **folded, merge rules and terminal rule proved** | **pairing proved** | **arithmetic proved** | **classed, total** | **status class and body proved** |
| Anthropic messages | **encoded, decoded, round trip proved** | **decoded and proved** | **folded, merge rules and terminal rule proved** | **pairing proved** (one user message of results) | **arithmetic proved** (input excludes the cache) | **classed, total** | planned |
| OpenRouter's variants | the OpenAI one | the OpenAI one | the OpenAI fold (usage and error frames) | the OpenAI one | the OpenAI one | **one more class** | **number-or-word code proved** |

## What it proves, in plain words

The specification is the code that runs: `VbmLlm/` imports only Lean's `Init` and the pinned [vbm-json](https://github.com/witt3rd/vbm-json), so a reply is read from the same verified parse everywhere. The proofs live in `VbmLlmProofs/` and are never linked. The ledger (`docs/proof-ledger.md`, generated) says which claims are proved and which are open, and tags each claim with the clause of the published schema it is about (`docs/clause-index.txt`). Only a `proved` claim is called verified.

* **A reply decoder accepts exactly what the documented shape allows** (`decode_ok_iff`, one characterisation theorem per decoder): a present field of the wrong type is refused, never coerced; a count is a plain natural; a tool call's arguments are kept verbatim (the model's text, never parsed); every refusal names its path and kind.
* **Usage arithmetic.** OpenAI's `prompt_tokens` includes the cache, Anthropic's `input_tokens` excludes it: both map onto one record whose parts add up to the input the model was shown; a contradictory report is refused, never clamped; totals add over a turn and a run.
* **The stream fold.** Chunk boundaries do not matter; the first `id`/`name` win, text and arguments concatenate, the last usage wins; a stream with no sentinel is `truncated` and never `complete`, nothing may follow the sentinel, an error chunk stops the fold and hands over its message with the partial reply (the consumer decides whether to discard it).
* **The turn machine.** Every tool call is answered exactly once, in order; an orphan result is text; an unanswered call gets a placeholder; the newest result wins; extending a conversation leaves what was already rendered as it was.
* **The request codec.** Each field is written as its member, an absent field is left out (never `null`), and `decode (encode r) = r`.
* **Finish reasons and failed calls** map totally onto closed classes; an unlisted word is kept and classed unknown; the status of a failed call has a class.

**What is not proved** (the ledger's `limit` and `open` claims): that a server sends what its schema says; that tool arguments are valid JSON or fit the tool's parameters; that a clause of the schema is stated faithfully (checked by review); that the parse of the bytes is the RFC 8259 reference (vbm-json's claim, pinned here by revision and hash); that *a stream folds to exactly the single-shot reply* for every interleaving of calls (proved for text and arguments split anywhere, checked on recorded streams; the ledger says it is partial); the whole stream-equals-single-shot equality for every interleaving of Anthropic blocks (open). The library is a codec: no HTTP, retries, credentials, prices or model names. **The conformance vectors are regression evidence, not proof**: their inputs are the schemas' own examples or built here, none is a recorded reply of a service, and their expectations are the library's own rendering read by a reviewer.

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

`VbmLlm.OpenAI.Usage.tokens` (and `VbmLlm.Anthropic.Usage.tokens`) turn the report into the normalized record (`inputUncached`, `inputCacheRead`, `inputCacheWrite`, `output`, `reasoning`); `VbmLlm.FinishClass.ofOpenAI`, `ofAnthropic` and `ofOpenRouter` class a finish reason. `docs/consumption.md` says what a verified agent harness can delete once it consumes each slice.

## Score

The VBM scorecard reads this repository from `scorecard.toml` and prints one card; every number comes from a command, never from a document. The first card, and the registry entry (unscored until the card is current), are in [the VBM repository](https://github.com/witt3rd/vbm). Several measures are `not-measurable` today and the card says why (no freestanding export yet, no mutation or comparator run): a metric that cannot be measured counts as a fail, so the card does not pass, and this README does not claim it does.

## Build and test

Prerequisites: `git`, [mise](https://mise.jdx.dev), `python3`, `jq`, a C compiler (`cc`), `coredumpctl` (systemd-coredump: the crash-record gate refuses to skip) and network access for the first fetch (the pinned Lean toolchain and the pinned `vbm-json`); a clean `ubuntu:24.04` with those passes the gate with the network cut after the fetch. Everything runs as `mise exec -- ...` (Lean 4.35.0, pinned in `mise.toml`). `mise exec -- scripts/tier1.sh` is the gate before landing: forbidden constructs, import rule, zero-warning build, the axiom gate, the obligation ledger with its spec-clause tags, the pinned-library check, the conformance vectors (`vectors/`: the published schema's own examples plus refusals), and the self-tests of the process scripts. Every gate has a negative self-test.

## How it is built

Agents write it, under mechanical gates instead of line-by-line review; the standard is VBM (verified bare metal), see [the VBM standard](https://github.com/witt3rd/vbm). Direction and the pinned policies: `docs/decisions/0001-vbm-llm.md`. Landing: `scripts/land-direct` (a pinned copy of [vbm-land](https://github.com/witt3rd/vbm-land)); the scorecard adapter is `scorecard.toml`.

## License

Apache-2.0. See [LICENSE](LICENSE) and [NOTICE](NOTICE). Security reports: [SECURITY.md](SECURITY.md). Everything outside our control that the library depends on is listed in `docs/trust-ledger.md`.

## Continuous integration

`.github/workflows/ci.yml` runs Tier 1 on every push to `main` and Tier 2 (the independent proof checkers) on a schedule (and on a manual dispatch), on GitHub-hosted runners only. No workflow reads a secret. What was checked before the repository went public, and the settings applied, are in `docs/flip-record.md`.
