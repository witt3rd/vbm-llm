# Architecture (one page)

vbm-json is one Lean program with one proof, projected onto several languages. Nothing in this page is aspirational: each arrow exists in the tree.

```
 LeanJson/  (imports Init only)                 LeanJsonProofs/  (never linked)
 ├ Value, Grammar   the RFC 8259 grammar         ├ the reference parser is sound, complete, total
 │                  as a relation                ├ parseFast = parse   (parseFast_eq_parse)
 ├ Reference        slow parser, straight        ├ print / tape / policy theorems
 │                  from the grammar             └ Ledger.lean: every claim, proved or not
 ├ Parse            the fast parser (explicit        │
 │                  stack, in place)                 ▼
 ├ Print, Tape      printer; the flat tape      Lean kernel (the only checker)
 └ Policy, Vectors  limits; test vectors
        │  Lean's C emitter
        ▼
 generated C ──┬─► clang -ffreestanding ─► libvbm_json.a / .so   (no libc, no runtime imports)
 + abi/vbm_json.c (107 lines)  └─► clang --target=wasm32 ─► vbm.wasm   (no imports)
 + runtime/rt.c  (the shared freestanding runtime)
        │  abi/vbm_json.abi.json  (checked against include/vbm_json.h)
        ▼
 bindings/  generated tape readers for Python and Rust + a few hand-written lines of loader each
```

## The pieces

- **The specification is the code.** `LeanJson/` holds the grammar (as a relation), a slow reference parser derived from it, the fast parser, the printer and the tape layout. It imports `Init` only, so the closure of an export never reaches Lean's `Std` or `Lean` packages and never forces the full Lean runtime to start.
- **The proofs are separate and never linked.** `LeanJsonProofs/` may import `Std` and `Lean`; nothing in `LeanJson/` may import it. `LeanJsonProofs/Ledger.lean` lists every claim with the theorems that back it; `docs/proof-ledger.md` is rendered from it by a gate, and the proved count may only rise.
- **The fast parser is not trusted on its own.** It exists only with a refinement proof to the reference (`parseFast_eq_parse`). The test vectors are generated from the reference, never from the fast code, and checked against both.
- **The boundary never decides.** The C shim copies bytes in, calls the Lean export, checks the result header and hands back a flat tape. A language binding reads the tape. Which documents are valid, and what a value is, is decided in Lean only.
- **One runtime for every target.** `runtime/rt.c` replaces, for the objects the verified parser builds, the few Lean runtime functions the generated C calls, and the handful of libc functions it needs. It serves the native library and the WebAssembly module alike.
- **The ABI is small and stable.** `vbm_json_parse` and `vbm_json_free`, `vbm_json_print_tape` (a tape back to compact JSON bytes), `vbm_json_escape_string` (a string literal from UTF-8) and `vbm_json_bytes_free`, caller-owned memory or your own allocator, a flat tape of little-endian 64-bit words (kind and length, then offset or subtree size). The description `abi/vbm_json.abi.json` is checked against the header by Tier 1, and the bindings are generated from it.

## The gates that keep the picture true

| gate | what it enforces |
|---|---|
| forbidden-constructs scan, import scan | no `sorry`, `admit`, new axioms, `unsafe`, `implemented_by`, `csimp`; `LeanJson` imports `Init` only |
| axiom gate | the proofs depend only on the standard axioms |
| obligation ledger | a claim is `proved` only by naming checked theorems; proved may rise, never fall |
| closure gate | the share of executed code that is specified Lean may only rise; nothing from `Std`, `Lean` or the proofs is reachable from an export |
| trust ledger | every hand-written file, extern, loader and tool has an entry |
| vectors and differential tests | the fast parser, the native library, the WebAssembly module and every binding agree with the reference on every vector |

The mutation metric (`scripts/test_mutants.sh`, local, not run by Tier 1) shows the tests can fail. Decisions and their reasons: [`decisions/`](decisions/). What is trusted and why: [`TRUST.md`](TRUST.md).
