# Contributing to vbm-json

Thanks for looking. Short version: **fork, branch, open a pull request.** A maintainer lands it; you do not need to run the landing tool yourself.

## Why the process looks unusual

The maintainers' own work (mostly done by AI agents in parallel worktrees) lands **directly on `main`, with no pull requests**, through one script that runs the full gate locally first. Outside contributions use ordinary pull requests, and a maintainer carries them through the same gate and lands them (rebasing onto `main`, so history stays linear). Your PR may therefore show up as landed under a different commit hash.

## Before you open a PR

1. Install what the README lists (`mise`, `python3` with PyYAML, `git`; `node` and `cargo` for the WASM and Rust tests).
2. Make your change on a branch of your fork.
3. Run the gate, **Tier 1**, and make sure it passes:

   ```sh
   mise install
   mise exec -- scripts/tier1.sh
   ```

   Tier 1 builds both Lean libraries with zero warnings, scans for forbidden constructs and imports, runs the axiom and trust-ledger checks, the shared vectors, and the ABI, WebAssembly, native and binding tests.
4. Use Conventional Commit subjects: `type(scope): summary` (`feat`, `fix`, `docs`, `test`, `perf`, `refactor`, `build`, `ci`, `chore`).
5. Keep the change small and focused; a larger change needs a short plan in the PR description.

## The rules that matter

- **No `sorry`, `admit`, `axiom`, `unsafe`, `implemented_by` or `csimp`** anywhere in the Lean. If a proof is hard, break it into lemmas; never weaken the statement.
- **Spec first.** A behaviour change is a change to the specification (`LeanJson/`, the grammar and policies) together with its proofs and vectors; optimised code exists only with a proof that it agrees with the reference. Vectors come from the reference, never from the fast code.
- **Only a `proved` claim in the ledger may be called verified.** Do not lower the proved count or the specified share; they only go up.
- **The boundary never decides.** C, loaders and bindings move bytes and read the tape; what is valid JSON is decided in Lean.
- **A new boundary** (an `extern`, a C file, a loader, a tool) needs an entry in `docs/trust-ledger.md`, or Tier 1 fails.
- **Checks and pins:** please do not edit a check to make something pass.
- No secrets in the repository.

## The maintainers' tools, in plain words

You do not need these to contribute; they are described so the repository makes sense.

- **`scripts/wt`**: makes a separate working copy (a git worktree, through the optional [Worktrunk](https://worktrunk.dev) tool) for each task, so parallel workers never share a checkout. The main clone stays on `main` and is never edited.
- **`.land/land-direct`**: lands the local commits of a worktree on `main`. Under one lock it checks that `main` is not red, rebases the commits onto `origin/main`, runs Tier 1 on exactly that result, and pushes as a plain fast-forward (never forced). It refuses commits with bad subjects or oversize diffs and reports whether protected files were touched. The lander itself is a pinned, vendored copy of vbm-land (`.land/tool/`, checked by `.land/tool/bin/land-check`: never edit it); this repository's own rules are `.land/land.conf` and `.land/land.d/`. Design: `docs/decisions/0002-land-direct.md`.
- **Tier 1**: the gate described above, run once, before the push, by `.land/land-direct` on exactly the commit it lands. Nothing runs after the push; if `main` is ever red, whoever sees it reverts the offending commit with `git revert` and the author fixes forward.

## Licence

By contributing you agree your contribution is licensed under Apache-2.0 (`LICENSE`).
