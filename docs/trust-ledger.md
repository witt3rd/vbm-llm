# The trust ledger

One file listing **everything outside our direct control that vbm-llm executes or depends on**: code we did not prove, code we did not write, and facilities we assume. It exists because verified by construction is the first priority: the size of the unverified base is the most critical measure. A boundary with no entry here does not land (`scripts/trust-ledger-check.sh`, Tier 1). The pattern is borrowed from the project the gates were first built in; only the derivation of the required set differs.

**Test code that is trusted:** `vectors/Main.lean` carries a minimal server-sent-event splitter that stands in for the `vbm-sse` library until it is pinned (whole buffer, the WHATWG rules). It is not part of the library; a mistake in it can only make a recorded stream decode wrongly, which the recorded expectations (read by a reviewer) would show. It goes away when the splitter library is pinned.

**Snapshot at the first slice (unchanged by the stream fold):** the library has no C, no `extern`, no executable of its own except the vector checker (`vectors/Main.lean`, Lean, not part of any export). What the build depends on is below. The one outside library is `vbm-json` (T09), whose proofs are trusted by revision and hash, not re-proved here.

## How the gate keeps this file true

The set of things that must appear here is **derived from the tree, not from this file**: every `@[extern]` symbol in `VbmLlm/`, every C file, the build pins (`lean-toolchain`, `mise.toml`, `lakefile.lean`, `lake-manifest.json`), the pinned landing tool (`.land/PIN`), the Lean pin's compiler, runtime and bundled clang/ld.lld (the keys `lean-compiler`, `lean-runtime`, `clang-lld`), every pinned library (`pin:NAME`, one per line of `.land/pins.lock`), and a watch-list of tools the scripts run. Each is a key (`file:`, `extern:`, `pin:`, `tool:`, plus the three Lean keys) that an entry must name on its **Covers** line.
- A new boundary (extern, C file, workflow, pinned library, tool) with no entry **fails**.
- A `Covers` key that names nothing real fails (a stale or invented cover), and **removing any entry fails** (the gate does this to itself on every run, one entry at a time). Dangling file references fail. An entry needs all seven fields, a **Plan** from `verify | replace | sandbox | accept`, and `accept` needs `because ...`. **Assumes** must link a written contract or say `no written contract` (counted as a gap); **Test** must name a test that can fail or say `none` (counted as a gap).
- Not covered by the gate (said, not hidden): a tool called from a script that is not on the watch-list in `scripts/trust-ledger-check.sh`, and the *quality* of an entry's prose.

The count printed on every run: `trust ledger: N entries (... gaps)`.

Entry format: **What** it is; **Enters** where it enters; **Assumes** what we assume of it (the contract); **Test** the test that can fail; **Owner**; **Plan**.

## The Lean toolchain (pinned: 4.35.0)

### T01. The Lean compiler: frontend, kernel, C emitter
- **What:** the `lean` release pinned in `lean-toolchain` and `mise.toml`: the elaborator, the kernel that checks every proof, and `EmitC`, which would turn our definitions into C. A kernel soundness bug would void the proofs; an emitter bug would give the compiled code different semantics from the Lean definition.
- **Enters:** `lean-toolchain`, `mise.toml`; every `.lean` file.
- **Assumes:** the kernel is sound and the compiler is faithful: no written contract beyond Lean's own documentation. The conformance vectors (`vectors/`) run the compiled decoder and compare it with the recorded expectations; `leanchecker` and nanoda are the checks on the kernel (T02).
- **Test:** the compiled decoder is checked by the vectors in Tier 1 (`vectors/Main.lean`, with a negative self-test).
- **Owner:** upstream Lean (leanprover/lean4); the owner pins it (CODEOWNERS: `lean-toolchain`, `mise.toml`).
- **Plan:** accept, because there is no other mature route from Lean to running code and the kernel is small and independently re-checked; revisit when an extractor with a semantics-preservation proof exists.
- **Covers:** `lean-compiler` `file:lean-toolchain` `file:mise.toml`

### T03. The Lean runtime and its headers (lean.h, libleanrt)
- **What:** the C runtime every Lean-compiled program links: reference counting, allocation, arrays and strings, big numbers. It is the lowest layer under the compiled decoder and the vector checker. It is not checked by us.
- **Enters:** the Lean release pinned in `lean-toolchain`.
- **Assumes:** the runtime implements Lean's object model correctly; no written contract.
- **Test:** none of ours: it is exercised only through the vectors (`vectors/Main.lean`).
- **Owner:** upstream Lean; the owner pins the version.
- **Plan:** accept, because the runtime is part of the one Lean release we pin and no verified replacement exists; the library imports only `Init` and the pinned parser, so the part of it that runs is small.
- **Covers:** `lean-runtime`

### T04. clang and ld.lld (the compiler and linker the Lean release bundles)
- **What:** the C compiler and linker bundled in the Lean release, used by `lake` to compile Lean's emitted C into objects and the vector checker's executable. A miscompile here changes the program the proofs were about.
- **Enters:** `lean-toolchain` (the bundle comes with the pin); `lakefile.lean` (every `lean_lib` and `lean_exe` build).
- **Assumes:** the compiler preserves C semantics for the emitted code; no written contract.
- **Test:** the vectors run against the compiled checker, which is the real check (`vectors/Main.lean`); a reproducible-build check is not built yet.
- **Owner:** upstream LLVM via the Lean release; the owner pins it.
- **Plan:** sandbox. Check the compiled artifact against recorded expectations, never trust the compile; no replacement is planned.
- **Covers:** `clang-lld`

## The build and process tools

### T05. Lake and the build file
- **What:** `lake` (shipped in the Lean release) reads `lakefile.lean` and builds the libraries; the file sets `warningAsError` and `autoImplicit false`, declares the module roots (`VbmLlm`, the Init-and-LeanJson-only one; `VbmLlmProofs`, never linked) and requires `vbm-json` by path from its vendored copy (`vendor/vbm-json`, locked in `.land/pins.lock`; `lake-manifest.json` records the resolved packages).
- **Enters:** `lakefile.lean`, `lake-manifest.json`; every `lake build` and `lake env lean --run` in `scripts/`.
- **Assumes:** the build builds the files that are in the tree and nothing else; the root split and the import rule are enforced by Tier 1, not by Lake (scripts/tier1.sh: the import scan).
- **Test:** scripts/tier1.sh (zero-warning check with its negative case; the import scan with its negative cases) and `land-pin verify` (the vendored closure against the lock).
- **Owner:** the owner (CODEOWNERS: `lakefile.lean`, `lake-manifest.json`).
- **Plan:** accept, because Lake is the Lean toolchain's own build tool and a change to it is a toolchain change (T01).
- **Covers:** `file:lakefile.lean` `tool:lake`

### T06. mise: installs the pinned Lean release
- **What:** `mise` downloads and installs the Lean release tarball named in `mise.toml` from GitHub releases and puts it on `PATH` for `mise exec -- ...`.
- **Enters:** `mise.toml`; every script is run as `mise exec -- scripts/...`.
- **Assumes:** the tarball is the one released for that tag; no checksum is verified by us today (no written contract): this is a supply-chain gap.
- **Test:** none: nothing here can fail if the tarball were swapped (a gap, counted).
- **Owner:** the owner (`mise.toml` is in the protected set); mise is upstream.
- **Plan:** sandbox. Pin the release checksum in a mise lockfile; until then the tarball's integrity is GitHub's.
- **Covers:** `tool:mise`

### T07. git and python3: the process tooling
- **What:** `git` (rebase, push, the file lists the checks read) and `python3` (the trust-ledger checker of the landing tool and the public-readiness lint). They run on the developer's machine; none is part of any artifact.
- **Enters:** `.land/land-direct`, `.land/tool/`, the Tier 1 scripts (`scripts/tier1.sh`).
- **Assumes:** they do what their manuals say; the lint's own test (a scratch tree it must flag) is the check that our use of python3 is right; no written contract.
- **Test:** `scripts/test_lint_public.sh` (runs the real lint against scratch trees); the checker negative-tests itself on every run.
- **Owner:** upstream tools; the owner approves the scripts.
- **Plan:** accept because they touch the process and not the artifact: a compromised tool could land a bad change, which the gates are there to catch.
- **Covers:** `tool:git` `tool:python3`

## The pinned libraries

### T09. vbm-json: the verified JSON codec every reply is read through
- **What:** the library `vbm-json` (https://github.com/witt3rd/vbm-json), vendored at a signed release (`vendor/vbm-json/`, locked in `.land/pins.lock`). Its `LeanJson.parseFast` turns the bytes of a reply into a `LeanJson.Value`; its own proofs (the fast parser equals the RFC 8259 reference, the reference is sound and complete) are the basis of every claim here that starts from a parsed value. Its code runs in every decode, together with its trusted header `include/vbm_json.h` and the two externs `s1_ld64` and `s1_st64`.
- **Enters:** `lakefile.lean` (the `require ... from "vendor/vbm-json"`), `.land/pins.lock`, `vendor/vbm-json/`; `VbmLlm/Wire.lean` imports `LeanJson.Value`, the vector checker calls `LeanJson.parseFast`.
- **Assumes:** the library's own ledger and its own independent re-check (`leanchecker`, nanoda at the pinned release); this repository does **not** re-prove them: the gate checks that the bytes are the bytes of the signed release (`land-pin verify`: the tree hash), never that they were proved. See docs/decisions/0001-vbm-llm.md, section 3.
- **Test:** `scripts/tier1.sh` runs `land-pin verify` first (an edited, added or deleted file, an unlocked library or two different copies of one fail it); the standard's scorer re-checks the vendored copy against the signed release it names.
- **Owner:** the owner (the lock is `.land/pins.lock`); upstream vbm-json is the same owner's.
- **Plan:** verify. Re-check the library's proof modules in this repository so the recheck is ours rather than the library's; until then the pin is a trusted-by-hash claim and says so.
- **Covers:** `pin:vbm-json` `dep:vbm-json/include/vbm_json.h` `extern:s1_ld64` `extern:s1_st64`

### T10. vbm-land: the vendored landing tool
- **What:** a pinned, vendored copy of vbm-land (`.land/tool/`, the entry script `.land/land-direct`, the skills in `.agents/skills/`): the lander that rebases, runs Tier 1 on the exact combination and pushes a plain fast-forward to `main`. It runs with the credentials of whoever lands.
- **Enters:** `.land/PIN` (source, version, the commit, the manifest hash), `.land/land-direct`, `.land/land.conf`.
- **Assumes:** the release at the pinned commit is signed by the owner's key (`.land/land.signers`) and records the tree hash of what it ships; `.land/tool/bin/land-check` checks every vendored file against the manifest, offline, on every landing (with `--upstream` it also fetches the manifest at the pinned commit), so a forged pin and tree edited together fail it; no written contract beyond the lander's own documentation.
- **Test:** `.land/tool/bin/land-check` checks every vendored file against `.land/tool/MANIFEST.sha256` (an edited copy or a stray file is refused); the lander's own tests run in its repository.
- **Owner:** upstream vbm-land (same owner).
- **Plan:** accept because the release is signed by the owner's key and checked offline on every landing.
- **Covers:** `file:.land/PIN`

### T11. vbm-simd: the bit-parallel kernels `vbm-json` is built on
- **What:** the library `vbm-simd` (https://github.com/witt3rd/vbm-simd), vendored inside `vbm-json` (`vendor/vbm-json/vendor/vbm-simd/`); its compiled objects are archived with `vbm-json`'s and run inside every parse, and its trusted shim header `include/vbm_simd.h` and its eleven `vbm_simd_*` externs are trusted code. Nothing in `VbmLlm` imports it.
- **Enters:** `vendor/vbm-json/vendor/vbm-simd/` (inside the vendored vbm-json: the tree hash of the release of `vbm-json` covers it).
- **Assumes:** the same as T09: the gate checks that the bytes are the bytes of the signed release, never that they were proved; the library's own trust ledger carries its proofs and its trusted shim header; no written contract here beyond that ledger.
- **Test:** `scripts/tier1.sh` runs `land-pin verify` first (it also refuses two different copies of one library in the closure).
- **Owner:** the owner; upstream vbm-simd is the same owner's.
- **Plan:** verify. As T09.
- **Covers:** `dep:vbm-simd/include/vbm_simd.h` `extern:vbm_simd_append` `extern:vbm_simd_classify64` `extern:vbm_simd_ctz` `extern:vbm_simd_find_avx2` `extern:vbm_simd_find_neon` `extern:vbm_simd_has_avx2` `extern:vbm_simd_has_neon` `extern:vbm_simd_inset64` `extern:vbm_simd_ld64` `extern:vbm_simd_st32` `extern:vbm_simd_st64`

