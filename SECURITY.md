# Security policy

vbm-llm is a **pre-release** library. Nothing is published to a package registry and there are no supported versions yet; report problems against the latest `main`.

## What to report

- A reply that the decoder accepts that the pinned convention (`docs/schemas/`) or the documented policy (`docs/decisions/0001-vbm-llm.md`) says it must refuse, or the reverse.
- A crash, hang or unbounded memory use on any input.
- A hole in the proofs: a way to make the ledger (`docs/proof-ledger.md`) claim more than is proved (a forbidden construct that evades the gates, an axiom, a theorem about code that does not run).
- Anything in the tooling this repository runs (`scripts/`, the vendored lander) that would expose a secret or run untrusted code with privileges.

The unverified parts, and what is assumed of them, are listed in `docs/trust-ledger.md`: findings there are expected and welcome. This library is a **wire contract**: it does not talk to a network,
hold a credential, or decide what to do with a reply, so no key or token belongs in this repository, its tests or its logs.

## How to report

Use GitHub's private vulnerability reporting for this repository (Security tab, "Report a vulnerability"). If that is not available, open an issue that says only that you have a security report and ask for a private channel; do not put exploit details in a public issue.

Please include the input (or a minimal one), the commit and what you expected.

## What to expect

This is maintained on a best-effort basis. Expect an acknowledgement within about a week and a fix or a written assessment as soon as practical. A confirmed bug is fixed on `main` with a regression vector.
