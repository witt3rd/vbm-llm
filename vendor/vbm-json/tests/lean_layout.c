/* tests/lean_layout.c: abi/lean_mini.h (the freestanding stand-in for the parts of lean.h the shim uses) against lean.h itself. Hosted test code, not shipped.
 * lean_mini.h is compiled here under other names (a prefix on every Lean name); each is checked against the real one: the struct layout, the tag, the limit, and, run, the header and size
 * that mini_alloc_sarray leaves against lean_alloc_sarray's (m_cs_sz excepted: lean.h sets it only without mimalloc and nothing reads it there). Exit 0 = identical. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <lean/lean.h>
static const size_t real_tag = LeanScalarArray, real_max = LEAN_MAX_SMALL_NAT;
#undef LeanScalarArray
#undef LEAN_MAX_SMALL_NAT
#define lean_object mini_object
#define lean_sarray_object mini_sarray_object
#define lean_alloc_object mini_alloc_object_extern
#define lean_dec_ref_cold mini_dec_ref_cold_extern
#define lean_internal_panic mini_panic_extern
#define lean_io_mark_end_initialization mini_mark_extern
#define lean_alloc_sarray mini_alloc_sarray
#define lean_sarray_cptr mini_sarray_cptr
#define lean_sarray_size mini_sarray_size
#define lean_dec_ref mini_dec_ref
#define lean_io_result_is_ok mini_io_result_is_ok
#define lean_is_exclusive mini_is_exclusive
#include "../abi/lean_mini.h"
static const size_t mini_tag = LeanScalarArray, mini_max = LEAN_MAX_SMALL_NAT;
#undef lean_object
#undef lean_sarray_object
#undef LeanScalarArray
#undef LEAN_MAX_SMALL_NAT
#undef lean_alloc_object
#undef lean_dec_ref_cold
#undef lean_internal_panic
#undef lean_io_mark_end_initialization
#undef lean_alloc_sarray
#undef lean_sarray_cptr
#undef lean_sarray_size
#undef lean_dec_ref
#undef lean_io_result_is_ok
#undef lean_is_exclusive

/* the mini header calls these (renamed) externs: route them to the real runtime */
mini_object *mini_alloc_object_extern(size_t sz) { return (mini_object *)lean_alloc_object(sz); }
void mini_dec_ref_cold_extern(mini_object *o) { lean_dec_ref_cold((lean_object *)o); }
void mini_panic_extern(const char *m) { lean_internal_panic(m); }
void mini_mark_extern(void) {}

static int bad;
#define CHECK(c, what) do { if (!(c)) { fprintf(stderr, "lean_layout: MISMATCH: %s\n", what); bad = 1; } } while (0)
int main(void) {
  CHECK(sizeof(mini_object) == sizeof(lean_object), "sizeof(lean_object)");
  CHECK(sizeof(mini_sarray_object) == sizeof(lean_sarray_object), "sizeof(lean_sarray_object)");
  CHECK(__builtin_offsetof(mini_object, m_rc) == __builtin_offsetof(lean_object, m_rc), "m_rc offset");
  { lean_object a; mini_object b; memset(&a, 0, sizeof a); memset(&b, 0, sizeof b);   /* the bit-fields: same bytes for the same values */
    a.m_rc = b.m_rc = 0x01020304; a.m_cs_sz = b.m_cs_sz = 0x1234; a.m_other = b.m_other = 0x56; a.m_tag = b.m_tag = 0x78;
    CHECK(memcmp(&a, &b, sizeof a) == 0, "bit-field layout of the header"); }
  CHECK(__builtin_offsetof(mini_sarray_object, m_size) == __builtin_offsetof(lean_sarray_object, m_size), "m_size offset");
  CHECK(__builtin_offsetof(mini_sarray_object, m_capacity) == __builtin_offsetof(lean_sarray_object, m_capacity), "m_capacity offset");
  CHECK(__builtin_offsetof(mini_sarray_object, m_data) == __builtin_offsetof(lean_sarray_object, m_data), "m_data offset");
  CHECK(mini_tag == real_tag, "LeanScalarArray");
  CHECK(mini_max == real_max, "LEAN_MAX_SMALL_NAT");
  for (size_t n = 0; n < 70; n += 7) {
    lean_object *a = lean_alloc_sarray(1, n, n + 3); mini_object *b = mini_alloc_sarray(1, n, n + 3);
    CHECK(a->m_rc == b->m_rc && a->m_tag == b->m_tag && a->m_other == b->m_other, "sarray header");
    CHECK(lean_sarray_size(a) == mini_sarray_size(b) && lean_to_sarray(a)->m_capacity == ((mini_sarray_object *)b)->m_capacity, "sarray size and capacity");
    CHECK((unsigned char *)mini_sarray_cptr(b) - (unsigned char *)b == (unsigned char *)lean_sarray_cptr(a) - (unsigned char *)a, "sarray data offset");
    CHECK(lean_io_result_is_ok(a) == mini_io_result_is_ok(b), "io_result_is_ok on a non-ctor header");
    lean_object *ok = lean_io_result_mk_ok(lean_box(0)), *er = lean_io_result_mk_error(lean_box(0));
    CHECK(mini_io_result_is_ok((mini_object *)ok) == 1 && mini_io_result_is_ok((mini_object *)er) == 0, "io_result_is_ok");
    lean_dec_ref(ok); lean_dec_ref(er);
    for (int rc = -2; rc <= 3; rc++) { a->m_rc = b->m_rc = rc; CHECK(lean_is_exclusive(a) == mini_is_exclusive(b), "is_exclusive (counts -2 to 3: single-threaded, unshared, shared, persistent, multi-threaded)"); }
    a->m_rc = b->m_rc = 1;
    mini_dec_ref(b); lean_dec_ref(a);   /* the count logic: a count of 1 is released through the cold path of the real runtime */
  }
  if (bad) return 1;
  printf("lean_layout: lean_mini.h agrees with lean.h (layout, tag, limit, sarray header and size, io-result test, exclusiveness, release)\n");
  return 0;
}
