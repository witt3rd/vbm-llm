# Scorecard

Status: draft by a worker, 2026-11-18; goals and targets are the owner's to set.

Every value below was measured on 2026-11-18 on a copy of this tree (`cp -a` to a scratch directory, Lean 4.35.0, 4 cores, no network) unless it says `unmeasured`. Commands are run from the repository root; `mise exec --` is the repository's own prefix (`AGENTS.md:22`).

## Goals as the repository states them

1. **The wire contract of the provider conventions, written once in Lean and machine-checked** (request and response codecs, stream fold, tool-call turn machine, usage arithmetic, finish and error taxonomy). Source: `AGENTS.md:17`, `README.md:3`, `docs/decisions/0001-vbm-llm.md:7`.
2. **Only a claim marked `proved` in the obligation ledger may be called verified**; every claim is tagged with the clauses of the pinned schema it is about, and the ledger names what is open, partial or a limit. Source: `AGENTS.md:27`, `README.md:15`, `README.md:25`.
3. **Fail closed**: a reply that does not fit is refused with a typed `Fault`, a present field of the wrong type is never coerced. Source: `AGENTS.md:28`, `docs/decisions/0001-vbm-llm.md:20`.
4. **One adapter per convention, each pinned to a schema hash**; the Anthropic error body is the one piece of the three conventions still planned. Source: `AGENTS.md:29`, `README.md:5`, `README.md:10`, `docs/decisions/0001-vbm-llm.md:46`.
5. **Verified by construction is the first priority; the size of the unverified base is the most critical measure**: nothing outside our control is used without an entry in the trust ledger; the one dependency is pinned by tag, commit and tree hash. Source: `docs/trust-ledger.md:3`, `AGENTS.md:30`, `AGENTS.md:41`.
6. **No `sorry`, `admit`, `axiom`, `unsafe`, `implemented_by`, `csimp`; zero build warnings; the axiom gate is clean.** Source: `AGENTS.md:25`, `AGENTS.md:44`.
7. **Conformance vectors are the boundary evidence** (regression, never proof); the checker is shown able to fail. Source: `AGENTS.md:26`, `README.md:25`, `vectors/README.md:15`.
8. **Public-ready, always**: no private name, host, path or number of ours anywhere. Source: `AGENTS.md:35`, `AGENTS.md:44` (the lint is a Tier 1 gate).
9. **Every gate has a negative self-test; Tier 1 passes before every landing and a landing adds no failure.** Source: `AGENTS.md:31`, `AGENTS.md:5`, `AGENTS.md:44`.
10. **Gates not yet ported: the closure gate (specified share of executed mass), the delta test selection, the mutation and non-vacuity metrics**; the adapter declares a floor of 100 for the specified share. Source: `AGENTS.md:46`, `scorecard.toml:108`, `README.md:46`.
11. **Pre-release, published by the owner when ready; built public-ready.** No registry release exists. Source: `README.md:5`, `AGENTS.md:17`.

## Metrics

Units: `count` is a plain count; `-hundredths` is a share in hundredths of a percent (10000 = 100%); `-permille` a ratio in thousandths; `-seconds` a duration; `-lines` physical lines.

| metric | direction | goal it serves | how to measure (from the repository root) | now | floor (= now) | target |
|---|---|---|---|---|---|---|
| proof-ledger-proved-claims (count) | higher | 1, 2 | `grep -c '\| \*\*proved\*\* \|' docs/proof-ledger.md` | 82 (2026-11-18) | 82 | |
| proof-ledger-claims (count) | higher | 1, 2 | `grep -cE '^\| \`[a-z0-9-]+\` \|' docs/proof-ledger.md` | 90 (2026-11-18) | 90 | |
| proof-ledger-proved-share-hundredths | higher | 1, 2 | proved claims / all claims in `docs/proof-ledger.md` (line 5: "82 proved, 4 partial, 1 open, 3 limit, of 90"); `mise exec -- .land/tool/bin/land-lean ledger \| head -1` regenerates it | 9111 (82 of 90, 2026-11-18) | 9111 | |
| proof-ledger-gaps (count; partial + open claims) | lower | 2, 4 | `mise exec -- .land/tool/bin/land-lean ledger \| head -1` (partial + open) | 5 (4 partial, 1 open, 2026-11-18) | 5 | |
| proof-ledger-limit-claims (count; claims no machine decides) | lower | 2 | same command (`limit`) | 3 (2026-11-18) | 3 | |
| clause-coverage-gaps (count; clauses with no proved or partial claim) | lower | 2 | `mise exec -- .land/tool/bin/land-lean ledger \| grep 'clause coverage'` (157 minus the covered) | 1 (`openrouter-chat:comment-lines`, 2026-11-18) | 1 | |
| clause-coverage-share-hundredths | higher | 2, 4 | same command: 156 of 157 | 9936 (2026-11-18) | 9936 | |
| axiom-gate-offending (count) | lower | 6 | `mise exec -- .land/tool/bin/land-lean axiom` (after `mise exec -- lake build VbmLlm VbmLlmProofs`) | 0 (4108 constants checked, 2026-11-18) | 0 | |
| forbidden-construct-hits (count) | lower | 6 | `grep -rnE '\b(sorry\|admit\|axiom\|unsafe\|implemented_by\|csimp)\b' VbmLlm VbmLlmProofs vectors/Main.lean VbmLlm.lean VbmLlmProofs.lean \| grep -vc tier1-allow` | 0 (2026-11-18) | 0 | |
| warnings (count) | lower | 6 | `mise exec -- lake build VbmLlm VbmLlmProofs vbm-llm-vectors 2>&1 \| grep -ci warning` (cold; `warningAsError` is also set in `lakefile.lean`) | 0 (2026-11-18) | 0 | |
| vectors (count; expectation files under `vectors/`) | higher | 7, 3 | `ls vectors/*/*.expect \| wc -l` | 261 (2026-11-18) | 261 | |
| vectors-differ (count) | lower | 7 | `mise exec -- lake exe vbm-llm-vectors --check 2>&1 \| tail -1` (the "N differ" figure) | 0 (2026-11-18) | 0 | |
| trust-ledger-entries (count; boundaries outside our control) | lower | 5 | `mise exec -- .land/tool/bin/land-lean trust \| tail -1` ("9 entries") | 9 (2026-11-18) | 9 | |
| trust-ledger-gaps (count; entries with no written contract or no test) | lower | 5 | same command ("7 with no written contract or no test") | 7 (2026-11-18) | 7 | |
| pin-failures (count) | lower | 5 | `mise exec -- .land/tool/bin/land-pin verify; echo $?` (exit status) | 0 (2026-11-18) | 0 | |
| lander-drift (count; 1 = `land-check` fails) | lower | 5, 9 | `.land/tool/bin/land-check >/dev/null 2>&1; echo $?` (exit status) | 0 (2026-11-18) | 0 | |
| public-lint-violations (count) | lower | 8 | `scripts/lint-public 2>&1 \| grep -c .` (it prints a blank line when clean; exit status 0) | 0 (2026-11-18) | 0 | |
| planned-convention-cells (count; "planned" cells of the README table) | lower | 4 | `grep -o '\| planned \|' README.md \| wc -l` | 1 (Anthropic error body, 2026-11-18) | 1 | |
| core-lines (lines of spec and code, `VbmLlm/` + `VbmLlm.lean`) | lower | 5, 1 | `cat $(find VbmLlm -name '*.lean') VbmLlm.lean \| wc -l` | 2205 (2026-11-18) | 2205 | |
| proof-lines (lines under `VbmLlmProofs/`) | higher | 2 | `cat $(find VbmLlmProofs -name '*.lean') VbmLlmProofs.lean \| wc -l` | 3814 (2026-11-18) | 3814 | |
| proof-to-core-permille (proof lines per core line) | higher | 2 | proof-lines * 1000 / core-lines | 1729 (2026-11-18) | 1729 | |
| build-seconds (cold build of the library, proofs and checker, 4 cores) | lower | 9 | `time mise exec -- lake build VbmLlm VbmLlmProofs vbm-llm-vectors` on a fresh copy (no `.lake`) | 66 (2026-11-18) | 66 | |
| tier1-seconds (wall time of the whole gate) | lower | 9 | `time mise exec -- scripts/tier1.sh` (declared timeout 1800 s in `.land/land.conf`) | unmeasured: needs the network for `mise` to fetch the pinned toolchain on a clean box, `coredumpctl` and a full gate run (the harness runs it at landing; not run here) | | |
| tier1-gate-selftests-passing (count; of the 15 gates `scorecard.toml` names) | higher | 9 | read the selftest line of each gate named under `[tier1] gates` in `scorecard.toml` from a `scripts/tier1.sh` log | unmeasured: needs one full Tier 1 run | | |
| signed-release-tags (count) | higher | 11 | `git tag \| wc -l` (`VERSION` reads 0.1.0) | 0 (2026-11-18) | 0 | |
| closure-specified-share-hundredths | higher | 10, 1 | none: the closure gate is not ported (`scorecard.toml` `closure_cmd = ""`; floor 100 declared there) | unmeasured: needs the closure gate ported | | |
| spec-mutants-killed-permille | higher | 10, 2 | none: no mutant set declared (`scorecard.toml` `[nonvacuity]`, `[mutation]` empty) | unmeasured: needs the mutation and non-vacuity runner ported | | |
| decode-allocation-budget (count; open claim `decode-allocation-budget`) | lower | 1 | `grep -c '\| open \|' docs/proof-ledger.md` | 1 (2026-11-18) | 1 | |

Notes. The two gaps rows overlap the ledger share row on purpose: the share can rise while a partial claim stays partial. `warnings` was read from a cold build on a copy; the repository's `lake` tree was not built in place. The cold build (66 s) is a little over the one-minute "cheap" line; it was run once.

## Health today

* **Clean and at the floor of what the gates can see**: 0 axiom offenders, 0 forbidden constructs, 0 warnings, 0 vector differences over 261 vectors, 0 public-lint violations, the pin and the lander copy verify. Nothing is regressed; this is the first measurement, so no history exists to regress against.
* **Far from the goals' direction**: 5 ledger gaps (4 partial, 1 open) and 3 limit claims; 82 of 90 proved (9111 hundredths). The stream-equals-single-shot claims (OpenAI and Anthropic) and `anthropic-messages-adapter` are partial; the allocation budget is open.
* **Trust base**: 9 entries, 7 with no written contract or no test, against a goal that calls this the most critical measure.
* **Incomplete adapter**: 1 planned cell (the Anthropic error body); 1 clause uncovered (`openrouter-chat:comment-lines`).
* **Unmeasured**: tier1-seconds, the gates' self-test count, the closure-specified share and the spec-mutant kill rate. The last two are the standard's own "verified" measures and are not yet measurable here; the README says a metric that cannot be measured counts as a fail (`README.md:46`).
* **Not released**: 0 tags.

## What a steward would do first

1. Port or declare the closure gate, so `closure-specified-share-hundredths` stops being `unmeasured` (the most central unmeasured measure of the verified-by-construction goal; the adapter already sets its floor at 100).
2. Close the partial and open ledger claims (the two stream-equals-single-shot claims, `anthropic-messages-adapter`, the allocation budget), which moves `proof-ledger-gaps` down and `proof-ledger-proved-share-hundredths` up, together with the planned Anthropic error body (`planned-convention-cells`) and the one uncovered clause (`clause-coverage-gaps`).
3. Write contracts and tests for the seven trust-ledger entries that lack them, which moves `trust-ledger-gaps` down; and record `tier1-seconds` from a full gate run so the time of the gate has a first value.

## Questions for the owner

* What are the targets? None is stated in the repository, except the closure floor of 100 in `scorecard.toml`. Is the target for `proof-ledger-gaps` 0, and is a `limit` claim ever acceptable as a final state?
* Is a smaller `core-lines` a goal, or only a measure of the size of the verified core? The repository says the unverified base is what matters, not the core size; the direction given is a guess.
* Should `proof-to-core-permille` be a goal at all? It is a proxy the repository does not state.
* When is the first signed release and the publication wanted (`signed-release-tags`)? The repository says only "private until the owner publishes" and "pre-release".
* Is the mutation and non-vacuity runner expected to be ported here or only in the VBM scorecard, and is `build-seconds` a goal or only a signal? The 45-minute rule (`AGENTS.md:33`) is about a change, not the build.
* Is OpenRouter's `comment-lines` clause meant to stay uncovered, or is the claim to be added?
