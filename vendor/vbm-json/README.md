# vbm-json

A JSON parser (RFC 8259) whose correctness is a machine-checked theorem, written once in Lean 4 and compiled to freestanding C and WebAssembly, with generated Python and Rust bindings. It has no runtime, no libc and no allocator surprises, and the hand-written code around the verified core is small enough to read and is listed line by line in a ledger.

> **Status: pre-release.** No packages are published to any registry (crates.io, npm, NuGet, PyPI); build from source. The API and the ABI may still change.

```
 Lean specification ──► Lean proofs ──► Lean-generated C ──► native library ──► C, Python, Rust
 (grammar, policies,    (checked by       (the same code,      WebAssembly module   (generated tape
  reference parser,      Lean's kernel     not a rewrite)      (no imports)         readers, no logic)
  fast parser)           (no re-checkers: nothing runs after the push)
```

## Why it exists

A JSON parser sits at the trust boundary of almost every system: it is the first code that touches bytes from outside. It is usually written in a memory-unsafe language or without a proof, and there is one hand-written parser per language, each with its own bugs and its own idea of what "valid" means. A bug there is a security bug.

vbm-json takes the other route. There is **one** parser, its correctness is a theorem that a proof checker verifies, and every language gets that same code, not a re-implementation. The proofs are about the code that runs, not about a model of it.

## The ethos: verified bare metal (VBM)

VBM is a standard for libraries that are small, proved, and run on nothing. See [the VBM standard](https://github.com/witt3rd/vbm). In this repository it means four things.

- **Verified: proofs, not tests.** The specification is the RFC 8259 grammar written as a Lean relation. Proved today (see the ledger for the exact theorems): a reference parser derived from that grammar is **sound and complete** (it accepts exactly the documents the grammar derives, with the value the grammar assigns) and **total**; and the parser the exports run **provably equals** the reference (`parseTapeSimd_eq`, proved through `parseFast_eq_parse`). Other claims are partly proved: that the grammar is unambiguous, that the printer round-trips and prints valid JSON, and that the tape encoding is faithful. The ledger says exactly which parts are proved and which are open, and only a `proved` claim is called verified anywhere in this repository.
- **Bare metal.** The verified core imports only Lean's `Init`; it is compiled to freestanding C and to a WebAssembly module that imports nothing. No libc, no WASI, no operating-system calls. Memory is a small runtime of our own (`runtime/rt.c`) or your allocator.
- **Correct by construction.** The Lean specification *is* the code that runs: C and WebAssembly are generated from it. The test vectors are generated from the specification's reference parser, never from the fast one, and every binding runs all of them (the vendored [JSONTestSuite](https://github.com/nst/JSONTestSuite) included). A trusted-base ledger names every hand-written piece and what is assumed of it.
- **Built agentically.** Coding agents wrote the specifications, the proofs and the generated code, under mechanical gates instead of line-by-line human review: forbidden constructs (`sorry`, `admit`, new axioms, `unsafe`, `implemented_by`, `csimp`) fail the build, and the proofs, the axiom check and the real tests decide what lands.

## Quickstart

Build first (see [Build and test](#build-and-test)): `scripts/build_native.sh OUT` writes `OUT/libvbm_json.a` and `.so`, `scripts/build_wasm.sh OUT.wasm` the module, `scripts/build_shared.sh OUT` the shared library for the bindings.

### C

`include/vbm_json.h`: bytes in, a flat **tape** out (two little-endian `u64` words per node: `kind | len << 8`, then an offset or a subtree size; see the header), caller-owned memory.

```c
#include <stdio.h>
#include <string.h>
#include "vbm_json.h"

int main(void) {
  const char *doc = "{\"name\":\"vbm\",\"tags\":[1,2,3]}";
  vbm_json_tape t;
  int rc = vbm_json_parse((const uint8_t *)doc, strlen(doc), NULL, &t);  /* NULL: default allocator */
  if (rc != VBM_JSON_OK) { fprintf(stderr, "parse failed: code %d\n", rc); return 1; }
  printf("root kind %llu, %llu members, %zu words, %zu text bytes\n",
         (unsigned long long)(t.words[0] & 0xff), (unsigned long long)(t.words[0] >> 8), t.nwords, t.ntext);
  vbm_json_free(&t);
  return 0;
}
```

```sh
cc -I include example.c OUT/libvbm_json.a -o example
```

To write JSON, `vbm_json_print_tape(&t, NULL, &out)` prints a parsed tape back as compact bytes (`out.data`, `out.len`; release with `vbm_json_bytes_free(&out)`), and `vbm_json_escape_string(utf8, len, NULL, &out)` gives the quoted, escaped string literal of UTF-8 text you already hold; both are the verified printer's bytes.

Error codes: `VBM_JSON_SYNTAX` (not valid), `VBM_JSON_DEPTH` (nested deeper than 512), `VBM_JSON_NOMEM`, `VBM_JSON_ARG`, `VBM_JSON_INTERNAL`. On any error nothing is allocated and nothing needs freeing.

### WebAssembly

`tests/wasm/vbm_json.mjs` is a 68-line loader with no dependencies (Node or a browser); the module takes an empty import object.

```js
import { readFileSync } from "node:fs";
import { load, OK } from "./tests/wasm/vbm_json.mjs";

const { parse } = await load(readFileSync("vbm.wasm"));
const r = parse(new TextEncoder().encode('{"a":[1,2]}'));
if (r.code === OK) console.log(r.words.length, new TextDecoder().decode(r.text));  // 10 "a12"
```

### Python and Rust (generated)

Both are generated from the ABI description `abi/vbm_json.abi.json`; the committed copies are checked against a fresh generation on every Tier 1 run. They move bytes and read the tape; what is valid is decided in Lean.

```python
# VBM_JSON_LIB=OUT/libvbm_json.so  PYTHONPATH=bindings/python
import vbm_json
vbm_json.parse(b'{"a":[1,2.5,"x"],"a":null}')
# [('a', [Number('1'), Number('2.5'), 'x']), ('a', None)]    numbers keep their lexeme, duplicate keys stay in order
# vbm_json.parse(b"[1,]") raises vbm_json.JSONSyntaxError
```

```rust
// bindings/rust (VBM_JSON_LIB_DIR=OUT tells the build script where libvbm_json is)
let v = vbm_json::parse(br#"{"a":[1,2]}"#)?;   // Value::Object(vec![("a".into(), Value::Array(..))]); Err(Error::Syntax) on bad input
```

### Lean

A Lean project can use the specification and code directly, with no C in between: depend on this repository by a pinned revision in your `lakefile.lean` (`require «vbm-json» from git "<repository url>" @ "<commit>"`) and use the same Lean release as this repository (`lean-toolchain`, 4.35.0). Pin the revision, never a branch: the pin is what ties your proofs and your build to exactly the specification you reviewed. A lock file that records the specification's hash, so that a changed specification is detected rather than trusted, is planned (decision 0001, point 7) and does not exist yet.

## Build and test

You need [`mise`](https://mise.jdx.dev), `git` and `python3`. `mise install` fetches the pinned Lean release (with the clang and lld it bundles); there is no `elan`. The WebAssembly and binding tests also need `node`, `cargo` and the C library headers (`libc6-dev` on Debian and Ubuntu); where a tool is absent, that test reports it as skipped, not passed.

```sh
mise install
mise exec -- lake build            # the library and its proofs
mise exec -- scripts/tier1.sh      # the gate: zero-warning build, all proof gates, vectors, ABI, WebAssembly, bindings
```

## What you can trust, and what you must

| piece | status | what stands behind it |
|---|---|---|
| The parser, the grammar, the policies, the fast-equals-reference theorem | **proved** (where the [ledger](docs/proof-ledger.md) says `proved`) | Lean's kernel |
| The printer, the tape encoding, some policy claims | **partly proved**; the open parts are listed | same, plus the shared vectors |
| The C and WebAssembly code | **generated** from the Lean | Lean's C emitter (trusted, [T01](docs/trust-ledger.md)); a differential test of the native and WebAssembly builds against the reference |
| The C shim (`abi/vbm_json.c`) and the freestanding runtime (`runtime/rt.c`) | **hand-written, trusted**, about 450 lines in all | the vectors, a mutation test of the shim, a leak and a failing-allocator test |
| Bindings: tape readers (generated), loaders (hand-written) | trusted, tested | every binding runs all the vectors; each is a second decoder, counted as boundary |
| The Lean compiler and kernel, the C compiler and linker, the Lean runtime headers | **trusted, not ours** | accepted, with the reasons, in the ledger |

The full list, with what is assumed of each piece, where it enters and how it is tested, is the [trust ledger](docs/trust-ledger.md), explained in [`docs/TRUST.md`](docs/TRUST.md). A hand-written file, an `extern`, a loader or a tool with no ledger entry fails the build.

## The honest numbers

Numbers rot when they are copied into prose, so none are kept here. **See the card:** [the scorecard card of this repository](https://github.com/witt3rd/vbm/blob/main/registry/scores/witt3rd__vbm-json.md) lists every metric on one page, measured by the [vbm](https://github.com/witt3rd/vbm) scorecard runner on a pinned commit (throughput against Python's `json`, serde_json and simdjson on six corpora, the verified share of the code, the trusted C, test and mutation evidence, the time of the landing check), with the raw JSON linked from it. The method behind the performance numbers, and the profile of where the time goes, are in [`docs/perf/`](docs/perf/) (`docs/perf/results.md` has the per-corpus tables of each change, each marked with the host and its load). What is proved, partial, open or a stated limit is in [`docs/proof-ledger.md`](docs/proof-ledger.md) (generated); mutation survivors are in [`docs/mutants.md`](docs/mutants.md). Concurrent calls are not yet tested or promised; TypeScript and C# bindings are planned and not in the tree.
## How it is developed

The repository is agent-built and lands **directly on `main`**, one commit at a time, through a script that rebases, runs the whole of Tier 1 locally on exactly the result, and pushes a plain fast-forward. Nothing runs after the push; if `main` is ever red, whoever sees it reverts the offending commit with `git revert` and the author fixes forward. There is no human line-by-line review: the checks are the review. Outside contributions are welcome as pull requests; a maintainer lands them through the same gate. See [`CONTRIBUTING.md`](CONTRIBUTING.md), [`docs/decisions/0002-land-direct.md`](docs/decisions/0002-land-direct.md), [`AGENTS.md`](AGENTS.md), and the standard it is measured against ([`vbm`](https://github.com/witt3rd/vbm)).

More: [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) (one page), [`docs/TRUST.md`](docs/TRUST.md), the design record [`docs/decisions/0001-vbm-json.md`](docs/decisions/0001-vbm-json.md).

## Licence

Apache-2.0: [`LICENSE`](LICENSE), [`NOTICE`](NOTICE) (the vendored JSONTestSuite is MIT). Security reports: [`SECURITY.md`](SECURITY.md).
