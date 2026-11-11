#!/usr/bin/env bash
# Generate the language bindings (bindings/python/vbm_json/{__init__,_generated}.py, bindings/rust/src/{lib,sys}.rs) from abi/vbm_json.abi.json (scripts/gen_bindings.py).
#   scripts/gen-bindings.sh            regenerate in place
#   scripts/gen-bindings.sh --check [ROOT]   the drift check (Tier 1): the files committed under ROOT (default: the repo) must equal the regenerated ones; exit 1 and name them otherwise
# Run: mise exec -- scripts/gen-bindings.sh
set -euo pipefail
cd "$(dirname "$0")/.."
if [ "${1:-}" = --check ]; then
  root=${2:-.}; tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
  python3 scripts/gen_bindings.py "$tmp" >/dev/null
  bad=0
  while IFS= read -r f; do
    cmp -s "$tmp/$f" "$root/$f" || { echo "gen-bindings: $f is not what the ABI description generates (run scripts/gen-bindings.sh)" >&2; bad=1; }
  done < <(cd "$tmp" && find bindings -type f | sort)
  exit $bad
fi
python3 scripts/gen_bindings.py .
