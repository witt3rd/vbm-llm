# Security policy

vbm-json is a **pre-release** parser. Nothing is published to a package registry and there are no supported versions yet; report problems against the latest `main`.

## What to report

- A document the parser accepts that RFC 8259 or the documented policy (`docs/decisions/0001-vbm-json.md`, section 5) says it must reject, or the reverse.
- A crash, hang, out-of-bounds access, leak or unbounded memory use on any input, in the C shim (`abi/`), the runtime (`runtime/`), the WASM module or a binding.
- A disagreement between a binding and the Lean reference.
- A hole in the proofs: a way to make the ledger (`docs/proof-ledger.md`) claim more than is proved (a forbidden construct that evades the gates, an axiom, a theorem about code the exports do not run).

The unverified parts, and what is assumed of them, are listed in `docs/trust-ledger.md`: findings there are expected and welcome.

## How to report

Use GitHub's private vulnerability reporting for this repository (Security tab, "Report a vulnerability"). If that is not available, open an issue that says only that you have a security report and ask for a private channel; do not put exploit details in a public issue.

Please include the input (or a minimal one), the build you used (commit hash, target: C, WASM, Python or Rust) and what you expected.

## What to expect

This is maintained on a best-effort basis. Expect an acknowledgement within about a week and a fix or a written assessment as soon as practical. A confirmed bug is fixed on `main` with a regression vector in the shared vector set.
