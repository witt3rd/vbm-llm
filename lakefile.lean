import Lake
open System Lake DSL

package «vbm-llm» where
  leanOptions := #[⟨`warningAsError, true⟩, ⟨`autoImplicit, false⟩]

/-- The one dependency: the verified JSON codec, vendored at vendor/vbm-json (its own dependency vbm-simd is inside it) and locked in .land/pins.lock; `land-pin verify` is the gate. -/
require «vbm-json» from "vendor/vbm-json"

/-- The library: specification and code, one Lean core. Imports `Init`, `LeanJson` (the pin) and itself only (checked by Tier 1). -/
@[default_target]
lean_lib VbmLlm where
  globs := #[.andSubmodules `VbmLlm]

/-- The proofs: may import `Std` and `Lean`; NEVER linked (nothing in `VbmLlm` may import it). -/
require «land-ledger» from ".land/tool/lean"   -- the landing tool's Lean modules (the ledger vocabulary and the reach walk), a package it ships: required, never declared, so a repository that vendors this one shares a single copy

lean_lib VbmLlmProofs where
  globs := #[.andSubmodules `VbmLlmProofs]

/-- The vector checker: decodes every recorded reply of `vectors/` with the library and compares it with the expected rendering. Not part of any export. -/
lean_exe «vbm-llm-vectors» where
  srcDir := "vectors"
  root := `Main
