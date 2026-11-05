import Lake
open System Lake DSL

package «vbm-llm» where
  leanOptions := #[⟨`warningAsError, true⟩, ⟨`autoImplicit, false⟩]

/-- The one dependency: the verified JSON codec, pinned to the revision the first consumer pins (every library of the family pins `vbm-json` to the same revision:
`scripts/pinned-libs.lock` holds its hash, `scripts/pinned-lib.py verify` is the gate). -/
require «vbm-json» from git "https://github.com/witt3rd/vbm-json.git" @ "320e4f8fd16330e97282baa75efea256547c357d"

/-- The library: specification and code, one Lean core. Imports `Init`, `LeanJson` (the pin) and itself only (checked by Tier 1). -/
@[default_target]
lean_lib VbmLlm where
  globs := #[.andSubmodules `VbmLlm]

/-- The proofs: may import `Std` and `Lean`; NEVER linked (nothing in `VbmLlm` may import it). -/
lean_lib VbmLlmProofs where
  globs := #[.andSubmodules `VbmLlmProofs]

/-- The vector checker: decodes every recorded reply of `vectors/` with the library and compares it with the expected rendering. Not part of any export. -/
lean_exe «vbm-llm-vectors» where
  srcDir := "vectors"
  root := `Main
