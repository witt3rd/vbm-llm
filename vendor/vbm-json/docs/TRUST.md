# What is trusted, and how to read the ledger

A proof says: *if* these assumptions hold, *then* the parser accepts exactly RFC 8259 JSON. This page says where the assumptions are. The full list is [`trust-ledger.md`](trust-ledger.md); this page explains how to read it.

## Three kinds of thing in the tree

1. **Proved.** Lean specifications and theorems. Lean's kernel checks them; nothing re-checks them after the push. [`proof-ledger.md`](proof-ledger.md) is the list of claims and their status: `proved` (theorems about the code the exports run), `partial` (some part proved, the rest named as open), `open`, and `limit` (a claim no machine decides, for example that the grammar was transcribed from the RFC correctly: that is checked by reading).
2. **Generated.** The C and WebAssembly come from the Lean by Lean's own C emitter; the Python and Rust tape readers come from the ABI description. Nobody edits them, and Tier 1 fails if a committed copy differs from a fresh generation. They are *not* proved: they are as trustworthy as the generator, which is why each generated reader is tested against every vector.
3. **Hand-written and trusted.** About 450 lines of C (`abi/vbm_json.c`, `abi/lean_mini.h`, `runtime/rt.c`), a few lines of loader per binding, the build scripts. These are the places a bug can hide from the proofs, so each has an entry saying what it is, what is assumed of it, and the test that would fail if the assumption broke.

## What stays outside our control

The Lean compiler, kernel and C emitter; the Lean runtime headers; the clang and lld that the Lean release bundles; Node and Rust as test toolchains. They are listed with a **Plan** for each: `verify`, `replace`, `sandbox` or `accept` (and `accept` must say *because*). Today the kernel and emitter are accepted, because there is no other mature route from Lean to C and WebAssembly, and the independent checker narrows the kernel risk.

## How an entry reads

Each entry has seven fields: **What** it is; **Where** it enters; **What is assumed** and the contract; the **Test** that can fail (or `none`, counted as a gap); the **Owner**; the **Plan**; and the keys it **Covers**. The count printed on every Tier 1 run (`trust ledger: N entries (... gaps)`) includes the number of entries with no written contract or no test: that is the list of work still to do, shown rather than hidden.

## Why the ledger cannot drift

The set of things that must be listed is derived from the tree, not from the ledger: every `extern`, every C file, every hand-written loader, every pin, every bundled compiler piece and every tool the scripts run. A new one with no entry fails the build; an entry that covers nothing real fails; and the gate deletes each entry in turn on every run to show that removing one is noticed. What the gate cannot judge is the quality of the prose, and a tool that is not on its watch-list: the ledger says so in its own text.

## What this does not claim

Verified here means a theorem about the Lean code, within the ledger's boundary. It does not mean the C compiler is correct, that Lean's emitter preserves semantics (no project proves that for any language), or that the policy choices are the ones you want: strictness about text, numbers kept as lexemes, duplicate keys kept in input order and a nesting limit of 512 are stated in [`decisions/0001-vbm-json.md`](decisions/0001-vbm-json.md), section 5. A policy change is a specification change.
