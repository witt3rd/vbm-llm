# 0001. vbm-json: the Lean is the product

Status: accepted for the scaffold (PR 0); the pinned policies in section 5 are **PROPOSED**, pending the owner's ratification.
Inputs: the plan for a family of verified libraries split out of a larger Lean project (its policy list);
the direction that verified by construction is priority 1 and efficiency, the per-agent footprint, is priority 2; the gates of that larger project, which this repository copies.

## 1. Decision
**The important thing is the Lean.** From it we generate C, Rust, TypeScript, C# and whatever comes next. The repository holds one Lean core and everything else is derived from it or
checked against it.

1. **One Lean core.** The specification, the reference, the fast parser, the printer and the tape are in one module root, `LeanJson` (imports `Init` only). The proofs are in
   `LeanJsonProofs` (may import `Std` and `Lean`; **never linked**: any `Lean.*` import in the closure of an export forces the full runtime initialisation, which is the very cost
   vbm-json removes from its consumers). The family is `vbm-<name>`, the ABI prefix `vbm_json_`.
2. **Lean emits C with a stable, Lean-described ABI.** Lean's own C emitter is the one supported, widely exercised path (already used in production Lean projects). The ABI is described in Lean
   (`abi/Abi.lean` writes `abi.json`: exports, error enum, buffer protocol, tape layout, limits). Exports are bytes in, bytes out: `vbm_json_validate`, `_parse_tape`, `_print`,
   `_canonicalize`, over caller-owned buffers with a "needed size" return, no allocator across the ABI, and a flat u32 tape (kind, offset, len) the bindings read. Tape encode/decode is **proved in Lean**.
3. **WASM** is the same C compiled freestanding (no imports, linked without `--allow-undefined`) with a small allocator shim (`runtime/runtime.c`, about 200 lines: trusted, in the ledger).
4. **Bindings are thin and generated.** Rust, TypeScript, C# and Python get types and FFI declarations generated from `abi.json`, plus a hand loader of at most 100 lines each. All of it is
   **counted as boundary** (trust ledger), never as verified: a binding's tape reader is a second decoder, tested by vectors and mutants, not proved.
5. **Shared vectors close the loop.** Lean generates the vectors from the **reference** (never from the fast code); every binding runs all of them in CI. Format `vbm-json-vectors-1`
   (rows plus a hash in `manifest.json`). Sets: JSONTestSuite `y_`/`n_`/`i_` (vendored, MIT, with the reference's verdict checked at generation: a `y_` file the reference rejects fails
   generation), exhaustive enumeration of all byte strings up to length N over a 12-byte alphabet, number/escape/UTF-8-boundary/depth-limit sets, print and tape vectors.
6. **Spec-first, in two layers.** PR 1 (spec, no `sorry`): `Value`, the RFC 8259 grammar as a Lean relation, a slow reference recogniser derived straight from the ABNF, the policies, the
   vector generator. PR 2: the fast parser (explicit stack, no recursion, `ByteArray` in place) with a refinement proof to the reference.
7. **A Lean consumer uses the Lean directly**: a lake dependency pinned by rev plus a `vbm-json.lock` (the spec hash), compiled from Lean into the consumer; never a vendored C artifact, and never the bindings.
   Same Lean pin (4.35.0) in both repositories. The consumer's closure gate needs a fourth class, "pinned library", counted as specified only while rev and spec hash match the lock.

## 2. Verified by construction first, size second
The measure is the specified share of the executed mass of the exports (`scripts/ClosureGate.lean`, printed on every Tier 1 run, may only rise) and the size of the trust ledger
(`docs/trust-ledger.md`). The boundary never decides: C, loaders and bindings move bytes and read the tape; every decision (what is valid, what a value is) is made by the Lean.

## 3. What is in this repository now (PR 0)
Scaffolding only: the build targets (`LeanJson`, `LeanJsonProofs`), the gates with their negative self-tests, the process scripts, the trust ledger, the obligation ledger (all claims open) and
AGENTS.md. No library code (the spec layer follows in PR 1a-1c), and no CI workflow: `.github/workflows/core.yml` (Tier 1 then Tier 2, adapted from the CI of the originating project) is the owner's merge and
comes as PR 0b.

## 4. The extractor survey (honest result; checked 2026-11-04 via GitHub repository search and the 4.35.0 toolchain tree; descriptions and READMEs read, code not audited)
- Official Lean 4: the C emitter (`Lean/Compiler/LCNF/EmitC.lean`) and an LLVM emitter (`IR/EmitLLVM.lean`). No Rust, TypeScript/JavaScript or C# target.
- Community Lean to Rust: `auser/lean4-prod` (LCNF to Rust, created 2026-08-08, 3 stars, no licence), `O6lvl4/lean4-rust-backend` (0 stars, one day of commits, no licence). Lean to WASM:
  `dennj/solana-lean` (modified compiler, 4 stars). Older: `SchrodingerZhu/LeanGccBackend` (libgccjit, last push 2023-10). Nothing found for C# or TS/JS extraction (`lidangzzz/Lean4-ts`
  implements Lean, it does not extract). **No project proves its emitter preserves semantics.**
- Not extraction: Rust-calls-Lean FFI crates (`argumentcomputer/lean-ffi`, `digama0/lean-rs`, `jcreinhold/lean-rs`); Rust-to-Lean (Aeneas, Charon, hax: the reverse direction). The closest
  precedent for the fallback is AWS Cedar (`cedar-policy/cedar-spec`: a Lean model and a Rust implementation tied by differential testing).
- **Conclusion: no mature extractor exists.** The C ABI plus WASM is the route, because Lean's C emitter is the supported path, the same proved code ships to every language, and the shared
  vectors close the loop. Watch `lean4-prod` quarterly; if one matures, add it as a vector-checked extra binding, never as the trusted path.

## 5. The pinned JSON policies (PROPOSED: pending the owner's ratification)
Until ratified these are the working assumption of PR 1 and every one is a ledger claim (`LeanJsonProofs/Ledger.lean`, the `policy-*` slugs); each is listed in the vectors.
- **Strict text.** No lone-surrogate escapes and no invalid UTF-8 (RFC 8259 permits either; I-JSON forbids both).
- **Numbers are lexemes**, kept as sign, digits and exponent; no floats in the core.
- **Duplicate keys are kept**, in input order.
- **`maxDepth`** is named and reported as an error code (JSONTestSuite has 100000-deep arrays). Proposed default 512, printed like any other named limit.
- **Lean.Json compatibility.** `print` must reproduce `Lean.Json.compress` bytes (a consumer's journal hash chains cover bytes). A one-time differential run against `Lean.Json` on the corpus gates the
  migration, then it is deleted.

## 6. Open questions held for the owner (none blocks PR 0)
Names (crate `vbm-json`, npm `@witt3rd/vbm-json`, NuGet `Witt3rd.VbmJson`, PyPI `vbm-json`: check availability before the first publish); licence (Apache-2.0, `LICENSE`);
which bindings first (TypeScript and Rust); where CI runs (GitHub Actions: Linux on every PR, macOS and Windows for the native bindings on main, tags and nightly); the policies above; the "pinned library" class in a consumer's
closure gate; and the shared `lean-gates` (copy now, extract at the second library: section 8).

## 7. Consequences
- `LeanJson/` is the specification **and** the code. Changes to it land like any other change (the spec lock and the owner-approval wait were withdrawn 2026-11-06).
- Forbidden anywhere: `sorry`, `admit`, new axioms, `unsafe`, `[implemented_by]`, `[csimp]` (Tier 1 scan). A proof that is hard is decomposed, never weakened.
- The gates are copies of the originating project's, adapted: the handler class and handler-mass ratchet are not carried over (there are no handlers: the boundary never decides); the deciding-code detector and
  the hidden-code fix were not yet upstream when this was copied and are to be ported when they land.

## 8. What in the gates is repo-specific (the parameters a shared `lean-gates` would need)
The gates were copied from the originating project (copy now, extract at the second library). A shared `lean-gates` would need these made parameters (a `gates.toml` or equivalent):
- **Module roots and their meaning:** `LeanJson` = spec, `LeanJsonProofs` = proofs, `Init` = toolchain, `Std`/`Lean` = forbidden-in-closure are hard-coded in `ClosureGate.classifyModule`, `AxiomGate.ours`, `LedgerGate.isSpec` and the `import` lines of all three (the originating project has its own spec and main module names); the class set itself differs (it has refined, handler classes).
- **Entry points:** the originating project hard-codes its main module; here a file (`scripts/closure-entries.txt`), which is the form to keep.
- **Build target lists** in `tier1.sh`, `regen-baselines.sh`, `tier2.sh` (`lake build ...`, `leanchecker --fresh <roots>`, `leanexport <roots>`).
- **Source roots** scanned by the forbidden-constructs and import scans (`spec impl` there, `LeanJson LeanJsonProofs abi` here).
- **The ledger's home** (`LeanJsonProofs/Ledger.lean`, the `ledger : List Obligation` and `Status` types) and a caveat table inside `LedgerGate.lean`.
- **Names in messages and paths:** the project-specific names in messages, the lander's worktree directory, the hook's override variable, the C directory and the module names in the handler and refined class files.
- **The trust-ledger derivation** (`trust-ledger-check.sh`: which files, externs, tools and hosts are required keys) and the path pattern and extern prefix in `trust_ledger.py`.
- **The protected-set list** and the required-class list in `test_protected_set.sh` (the engine, `protected-set.sh`, is generic).
- **The summary line `land` quotes** (`closure gate: spec ...`, `trust ledger: N entries`): a printed-line contract between the gates and the lander.
- Already generic: `protected-set.sh`, `land` (apart from its directory name and the quoted lines), `run-tests-parallel.sh`, `lint-pipefail.sh` (its file list), the githook, `wt`, `trust_ledger.py` (apart from the pattern).
