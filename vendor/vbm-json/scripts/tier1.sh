#!/usr/bin/env bash
# Tier 1 (the landing check): build, the guards that ARE the verified product, and the real tests. Nothing else refuses a landing.
#   guards: no sorry/axiom/unsafe in Lean sources; Init-only imports; a warning-free build; only the standard axioms; a new trusted boundary has a trust-ledger entry; the shared vectors agree with the reference.
#   reported, never gated: the specified share and the closure/ledger counts.
# Run from the repo root: mise exec -- scripts/tier1.sh.
set -euo pipefail
cd "$(dirname "$0")/.."
# 0. The vendored libraries are exactly their pins (docs/pin.md of vbm-land): the same first step in every repository.
.land/tool/bin/land-pin verify

lean_sources() { find LeanJson LeanJsonProofs abi -name '*.lean' 2>/dev/null; ls LeanJson.lean LeanJsonProofs.lean 2>/dev/null; }
# 1. Forbidden constructs in Lean sources; a comment may mention one only on a line marked `-- tier1-allow`.
bad=$(grep -HnE '\b(sorry|admit|axiom|unsafe|implemented_by|csimp)\b' $(lean_sources) | grep -v 'tier1-allow' || true)
if [ -n "$bad" ]; then echo "tier1: forbidden construct(s):" >&2; echo "$bad" >&2; exit 1; fi
# 1a. LeanJson imports Init (implicit) and its own modules only.
bad=$(grep -HnE '^[[:space:]]*((public|meta|private)[[:space:]]+)*(import|prelude)\b' $(find LeanJson -name '*.lean') LeanJson.lean | grep -vE ':[0-9]+:import LeanJson(\.[A-Za-z0-9_]+)*[[:space:]]*$' || true)
if [ -n "$bad" ]; then echo "tier1: LeanJson may import only LeanJson modules:" >&2; echo "$bad" >&2; exit 1; fi
# 2. Build (warningAsError is set in lakefile.lean), once, for the guards and every test.
lake build LeanJson LeanJsonProofs vbm-json-vectors LeanJson:static LeanJsonSimd VbmSimd VbmSimdProofs
# 2a. Only the standard axioms. 2d. A new trusted boundary has a trust-ledger entry. 2e. The shared vectors agree with the Lean reference.
lake env lean --run scripts/AxiomGate.lean
scripts/trust-ledger-check.sh
vdir=$(mktemp -d); trap 'rm -rf "$vdir"' EXIT   # generating runs every check of --check (reference consistency, fast parser, fused tape parser, JSONTestSuite) and writes the rows the tests below share
lake exe vbm-json-vectors --n 4 --out "$vdir"
export VBM_JSON_VECTORS="$vdir/vectors.jsonl" VBM_OBJ_CACHE="$vdir/obj"
# Reported, not gated: the specified share and the closure counts.
lake env lean --run scripts/ClosureGate.lean || true
# 4. The real tests, in parallel.
.land/tool/bin/run-tests-parallel scripts/test_abi.sh scripts/test_wasm.sh scripts/test_native.sh scripts/test_bindings.sh scripts/test_build_cache.sh
echo "tier1: ok"
