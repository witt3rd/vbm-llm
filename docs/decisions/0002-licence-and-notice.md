# 0002. Licence and notice

Status: accepted (the repository is built public-ready; the owner publishes).

## Decision

* **Code, proofs, vectors and documents of this repository: Apache-2.0** (`LICENSE`), the default of the VBM family; copyright "the vbm-llm authors" (`NOTICE`).
* **Nothing third-party is copied except two kinds of example**, both named in `NOTICE`: the four response examples and the five request examples of the OpenAI OpenAPI description (MIT), unchanged, as vectors `openai-chat/001` to `004` and `openai-chat-request/001` to `005`; and the vendored `vbm-land` lander (Apache-2.0, `scripts/land/`, unchanged and checked by `scripts/land/bin/land-check`).
* **Read, not copied:** the Anthropic SDK type definitions (MIT) and the OpenRouter documentation pages are the pinned sources of two adapters (`docs/schemas/`: URL, date and hash). The clause index lists the property names and policies read from them; the vectors of those adapters are built here from the shapes, none is a recorded reply of a service and none copies a documentation page.
* **Pinned dependency, not vendored:** `vbm-json` (Apache-2.0), fetched by lake at the revision in `lakefile.lean` and `scripts/pinned-libs.lock`.
* The Lean toolchain (Apache-2.0) is downloaded at build time and is not part of the repository.

## Why

A library meant to be pinned by other projects must say, in one file, what it contains and under what terms; the examples are the only third-party text in the tree, so the notice names them, and the sources that are only read are named in `docs/schemas/` where their hash is. A change that copies a new third-party text lands with its `NOTICE` line in the same commit.
