/* abi/lean_mini.h: the few names of lean.h that abi/vbm_json.c uses, for the FREESTANDING compile of the shim (-ffreestanding -nostdinc: the Lean runtime header needs libc headers, which are not
 * reachable). TRUSTED, unverified (docs/trust-ledger.md, T09). Included only when __STDC_HOSTED__ is 0; a hosted build uses lean.h itself. tests/lean_layout.c compiles this file next to lean.h and checks
 * every name below against lean.h's: the layout, the tags, the size arithmetic and the header initialisation. m_cs_sz is NOT set here: lean.h sets it only without mimalloc, and nothing reads it there. */
#ifndef VBM_LEAN_MINI_H
#define VBM_LEAN_MINI_H
typedef struct { int m_rc; unsigned m_cs_sz:16; unsigned m_other:8; unsigned m_tag:8; } lean_object;
typedef struct { lean_object m_header; size_t m_size; size_t m_capacity; uint8_t m_data[]; } lean_sarray_object;
#define LeanScalarArray 248
#define LEAN_MAX_SMALL_NAT (__SIZE_MAX__ >> 1)
lean_object *lean_alloc_object(size_t sz);
void lean_dec_ref_cold(lean_object *o);
void lean_internal_panic(const char *msg) __attribute__((noreturn));
void lean_io_mark_end_initialization(void);
static inline lean_object *lean_alloc_sarray(unsigned elem_size, size_t size, size_t capacity) {
  if (elem_size >= 128) lean_internal_panic("scalar array element size is larger than 2^7");
  size_t bytes;
  if (__builtin_mul_overflow((size_t)elem_size, capacity, &bytes) || __builtin_add_overflow(bytes, sizeof(lean_sarray_object), &bytes)) lean_internal_panic("Nat.add overflow");
  lean_sarray_object *o = (lean_sarray_object *)lean_alloc_object(bytes);
  o->m_header.m_rc = 1; o->m_header.m_tag = LeanScalarArray; o->m_header.m_other = elem_size;
  o->m_size = size; o->m_capacity = capacity;
  return (lean_object *)o;
}
static inline uint8_t *lean_sarray_cptr(lean_object *o) { return ((lean_sarray_object *)o)->m_data; }
static inline size_t lean_sarray_size(lean_object *o) { return ((lean_sarray_object *)o)->m_size; }
static inline void lean_dec_ref(lean_object *o) { if (o->m_rc > 1) o->m_rc--; else if (o->m_rc != 0) lean_dec_ref_cold(o); }
static inline int lean_is_exclusive(lean_object *o) { return o->m_rc == 1; }
static inline int lean_io_result_is_ok(lean_object *r) { return r->m_tag == 0; }
#endif
