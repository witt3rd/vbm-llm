## Landing (direct to main, no PRs)
- Work in a worktree off a fresh origin/main. Diff ≤150 production lines, ≤45 min without a passing build; over either, stop and write a decomposition plan.
- Commit locally with Conventional Commits. Land only with `scripts/land-direct`; never push main yourself, never force-push it, never open a PR.
- New behaviour lands behind a flag that defaults OFF. Interface changes: add beside the old, migrate callers, delete at zero references.
- Main is RED when the Tier 1 job of its latest push failed. While red or frozen, only a fix or revert lands. Never hotfix on main: pull the revert, reproduce in a new worktree, resubmit.
- `scripts/land/` and `scripts/land-direct` are a pinned copy of vbm-land: never edit them (`scripts/land/bin/land-check` fails the gate). Change the tool upstream, then `scripts/land/bin/land-update <tag>`.
- Decide anything reversible and log it. Escalate only money, data loss, secrets, publishing, or harm to a third party; say so in one line and stop.

# AGENTS.md: vbm-llm

The wire contract of the LLM provider conventions (OpenAI chat-completions, Anthropic messages, OpenRouter's variants), **written once in Lean and machine-checked**: request and response codecs, the streaming delta fold, the tool-call turn pairing machine, usage arithmetic, the finish-reason and error taxonomy, as one adapter per convention over a neutral core. Agent-built, no human code review. Private until the owner publishes; built PUBLIC-READY (no private name, host or path anywhere: `scripts/lint-public` fails Tier 1). Design and the pinned policies: `docs/decisions/0001-vbm-llm.md` (read first). The standard is VBM (verified bare metal), the libraries are `vbm-<name>`. `README.md` is the public face (for humans, kept short); this file is the agent file.

**Scope.** Only the wire contract is provable. No client behaviour: no HTTP, no retries or failover, no authentication, no prices, **no model names** (a model is an opaque string), no capability tables, no policy about what to do with a reply. A decoder says what a reply *is*; the consumer decides. `docs/consumption.md` says which hand-written pieces of a consumer each slice replaces.

## Status
Slices (the order of work): scaffold, **OpenAI response decode** (with usage arithmetic and the finish classes), **the stream fold** (over `vbm-sse` events: pinned like `vbm-json` once it exists, a stubbed event interface until then; the conformance checker carries a stub splitter), the tool-call turn machine, the request codec, the Anthropic adapter, OpenRouter's variants. Which have landed: `git log`; what is proved: `docs/proof-ledger.md` (generated). Toolchain: Lean 4.35.0, pinned in `mise.toml` and `lean-toolchain` (no elan). Run everything as `mise exec -- ...`; the gate is `mise exec -- scripts/tier1.sh`.

## Hard rules
- **Forbidden anywhere in Lean:** `sorry`, `admit`, `axiom`, `unsafe`, `implemented_by`, `csimp` (Tier 1 scans for them; a comment may mention one only on a line marked `tier1-allow`). A proof is hard? Decompose it; never weaken the statement.
- **Spec first.** Behaviour lands as a specification and its proofs. The conformance vectors' inputs are the published schema's own examples and built refusals; their expectations are the library's rendering, read and committed by a reviewer: they are regression and conformance evidence, never proof.
- **No unproved claim called verified.** Only `proved` in the obligation ledger (`VbmLlmProofs/Ledger.lean`, rendered to `docs/proof-ledger.md`) may be called verified. A claim is tagged with the clauses of the pinned schema it is about (`docs/clause-index.txt`): a tag not in the index fails Tier 1.
- **Fail closed.** A reply that does not fit is refused with a typed `Fault`; a present field of the wrong type is never coerced; an unlisted word (a finish reason) is kept and classed unknown, never guessed.
- **One adapter per convention, each pinned to a schema hash** (`docs/schemas/`). Never branch on a model name. A schema bump is a deliberate change: read the diff, update the index and the decoder, then the table.
- **Pinned dependency.** `vbm-json` is pinned by revision (`lakefile.lean`) and by the hash of its spec files (`scripts/pinned-libs.lock`); `scripts/pinned-lib.py verify` is a Tier 1 step. Every library of the family pins `vbm-json` to the same revision. A bump is: pin from a real checkout (`scripts/pinned-lib.py hash`), then the lock and the dependency in one change.
- **Every gate has a negative self-test** (it must be shown able to fail, in the same run). A new gate without one does not land.
- **Land with `scripts/land-direct`, never open a PR** (`scripts/land/` is a pinned copy of vbm-land: never edit it; `scripts/land/bin/land-check` fails Tier 1 on a local edit). Never push to `main` yourself, never force-push it. A change to a gate-defining file (the protected set: `scripts/land.conf`, `scripts/land/`) is allowed but never counts as a fix for a red main.
- **TTL 45 minutes without a passing build:** abort and decompose. **Small diffs:** at most 150 production lines under `VbmLlm/` per landing (a `Diff-Budget:` trailer waives it with a decomposition note). Conventional Commits `type(scope): summary`.
- **No secrets in the repository.** No paid model calls and no network call from a test or a gate (the pin fetch reads one public repository).
- **Public-ready, always.** No private name, no path of ours, no number of ours anywhere (`scripts/lint-public`; names are kept as hashes). Write generic ("a verified agent harness", "the first consumer").

## Library rules
- **Module roots:** `VbmLlm` imports `Init`, `LeanJson` (the pin) and other `VbmLlm` modules only (Tier 1 scans the imports); `VbmLlmProofs` may import `Std` and `Lean` and is never linked, and nothing in `VbmLlm` may import it.
- **Reading a value** goes through `VbmLlm/Wire.lean` (last binding wins, null and absent are the same, a count is a plain natural); written as scans that carry their answer: a decoder allocates no more than the code it replaces.
- **Decoders** are written as chains of small total functions each with an `_ok_iff` theorem; faults build their path on the way out. A new decoder has its characterisation theorem, its refusal theorems, its vectors (a refusal each) and its clause tags before it lands.
- **The trust ledger** (`docs/trust-ledger.md`) lists everything outside our control; a new boundary (extern, C file, workflow, pinned library, tool) is listed there before it lands.

## Gates (Tier 1 before landing; Tier 2 after landing)
- **Tier 1** (`scripts/tier1.sh`): forbidden-constructs scan, import scan, pipefail lint, the vendored lander's drift check, the pinned-library check, zero-warning build, axiom gate (`scripts/AxiomGate.lean`), named-theorem ledger check with clause tags (`scripts/LedgerGate.lean`; the counts are reported, not gated), conformance vectors (`vectors/`), public-readiness lint, and the offline self-tests of the parallel runner and the crash-record check.
- **Tier 2** (`scripts/tier2.sh`, CI on a schedule, never a gate for a landing): Tier 1 again, `leanchecker --fresh`, nanoda over the exported proof. A failure on main means revert, then fix in a worktree.
- **Not ported yet** from the project these gates were first built in: the closure gate (the specified share of executed mass; every claim here names theorems about the functions that are the library, nothing else is executed), the delta test selection, the mutation and non-vacuity metrics, the watchdog.

## Layout
`VbmLlm/` spec and code (Init and the pin only) · `VbmLlmProofs/` proofs (never linked), `Ledger.lean` the claims · `vectors/` the conformance checker and the recorded replies · `docs/` decisions, schemas, clause index, trust ledger, proof ledger (generated), consumption note · `scripts/` gates, the lock, the process scripts and their self-tests, the pinned lander · `scorecard.toml` the adapter for the VBM scorecard.
