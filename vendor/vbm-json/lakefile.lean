import Lake
open System Lake DSL

package «vbm-json» where
  leanOptions := #[⟨`warningAsError, true⟩, ⟨`autoImplicit, false⟩]

/-- The reusable verified bit-parallel kernels (the model of the vector operations, the proved kernels, the trusted shim header): a pinned, vendored dependency (vendor/vbm-simd, locked in .land/pins.lock: `land-pin`). -/
require «vbm-simd» from "vendor/vbm-simd"

/-- The library: specification and code, one Lean core. Imports `Init` only (checked by Tier 1): this is what is compiled to C, to WASM and into
every consumer, so nothing from `Std` or `Lean` may be in its closure (a `Lean.*` import forces full runtime initialisation). The export `vbm_json_parse_tape` is the bit-parallel parser of `LeanJsonSimd`, so the objects of that
library and of the pinned `VbmSimd` modules it uses are archived with this library (`moreLinkObjs`): `libvbm_x2djson_LeanJson.a` is all a C consumer links, as before. -/
@[default_target]
lean_lib LeanJson where
  -- every module under LeanJson/ is built, imported by the umbrella or not: a module cannot hide from the build
  globs := #[.andSubmodules `LeanJson]
  moreLinkObjs := #[`+LeanJsonSimd.Stage1:o, `+LeanJsonSimd.ParseSimd:o, `+LeanJsonSimd.PrintSimd:o, `@«vbm-simd»/+VbmSimd.Spec:o, `@«vbm-simd»/+VbmSimd.Lanes:o, `@«vbm-simd»/+VbmSimd.Escape:o, `@«vbm-simd»/+VbmSimd.PrefixXor:o,
    `@«vbm-simd»/+VbmSimd.Shims:o, `@«vbm-simd»/+VbmSimd.Bytes:o, `@«vbm-simd»/+VbmSimd.Cursor:o, `@«vbm-simd»/+VbmSimd.Find:o, `@«vbm-simd»/+VbmSimd.Inset:o, `@«vbm-simd»/+VbmSimd.Append:o, `@«vbm-simd»/+VbmSimd.Classify:o]

/-- The bit-parallel structural stage and the index-driven parser (docs/perf/simd-plan.md): `LeanJson` plus the pinned dependency `VbmSimd` (checked by scripts/test_simd_imports.sh). Compiled with the dependency's trusted shim
header (static inline loads, stores and ctz) first in every generated C file. It holds the export `vbm_json_parse_tape` (`parseTapeSimd`). -/
lean_lib LeanJsonSimd where
  globs := #[.andSubmodules `LeanJsonSimd]
  moreLeancArgs := #["-fno-builtin-memset", "-fno-builtin-memcpy", "-fno-builtin-memmove", "-include", (__dir__ / "vendor" / "vbm-simd" / "include" / "vbm_simd.h").toString]

/-- The proofs: may import `Std` and `Lean`; NEVER linked (nothing in `LeanJson` may import it, and no executable or export depends on it). -/
lean_lib LeanJsonProofs where
  globs := #[.andSubmodules `LeanJsonProofs]

/-- The vector generator (`vbm-json-vectors-1`): rows come from the Lean REFERENCE and printer only (`LeanJson.Vectors`); this executable only writes them. Not part of any export. -/
lean_exe «vbm-json-vectors» where
  srcDir := "vectors"
  root := `Main
