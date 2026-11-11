# Sourced library: `cc ARGS...` is `clang ARGS...`, and when VBM_OBJ_CACHE names a directory (tier1 sets one for the length of a run) an object already compiled with the same arguments and the same source
# (and -include header) is copied instead of compiled again: the freestanding native build runs three times and the wasm build once over the same generated C. Writes are atomic (a concurrent compile of the same object is harmless).
cc() {
  [ -n "${VBM_OBJ_CACHE:-}" ] || { clang "$@"; return; }
  local a out="" src="" hdr="" prev="" key; local -a rest=()
  for a in "$@"; do
    case $prev in -o) out=$a; prev=""; continue;; -c) src=$a;; -include) hdr=$a;; esac
    [ "$a" = -o ] || rest+=("$a"); prev=$a
  done
  [ -n "$out" ] && [ -f "$src" ] || { clang "$@"; return; }
  key=$( { printf '%s\0' "${rest[@]}"; cat "$src" ${hdr:+"$hdr"}; } | sha256sum | cut -c1-40 )
  mkdir -p "$VBM_OBJ_CACHE"
  if [ -f "$VBM_OBJ_CACHE/$key.o" ]; then cp "$VBM_OBJ_CACHE/$key.o" "$out"; return; fi
  clang "$@" && cp "$out" "$VBM_OBJ_CACHE/$key.$$.tmp" && mv "$VBM_OBJ_CACHE/$key.$$.tmp" "$VBM_OBJ_CACHE/$key.o"
}
