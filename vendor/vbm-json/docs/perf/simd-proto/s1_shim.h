/* docs/perf/simd-proto/s1_shim.h: the two memory primitives of the stage-1 prototype as they would be in the trusted shim (models: `ld64`, `st64` in Stage1.lean). Included into the generated C with
 * `-include`, as `static inline`, so the compiler can see through them. */
#include <lean/lean.h>
#include <string.h>
static inline uint64_t s1_ld64(b_lean_obj_arg a, size_t i) { uint64_t w; memcpy(&w, lean_sarray_cptr(a) + i, 8); return w; }
static inline lean_obj_res s1_st64(lean_obj_arg out, size_t k, uint64_t w) { lean_object *r = lean_sarray_ensure_exclusive(out); memcpy(lean_sarray_cptr(r) + 8 * k, &w, 8); return r; }
