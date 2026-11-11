/* runtime/rt.c: the ONE freestanding runtime of vbm-json, for the wasm32 module and the native library alike. TRUSTED, unverified (docs/trust-ledger.md, entry T10). No libc, no WASI, no imports.
 * Two platform parts only: (1) memory: wasm32 uses memory.copy/fill and grows linear memory from __heap_base; the native build (any 64-bit host) uses plain loops and one static arena of
 * VBM_RT_ARENA_BYTES (default 256 MiB, zero-initialised, so the OS commits pages only as they are touched); (2) the host exports of the wasm module. Everything else is shared.
 * It replaces, for exactly the objects the verified parser builds, the pieces of libleanrt the generated C calls, and the handful of libc functions lean.h and the shim use:
 *   the allocator (malloc/free/free_sized: size-class free lists over a bump region of linear memory, memory.grow on demand), mem* and strlen,
 *   lean_alloc_object, lean_free_object, lean_dec_ref_cold (the object deleter: ctor, array, scalar array, string, closure; any other kind traps),
 *   lean_mark_persistent, lean_inc_heartbeat, initialize_Init and lean_initialize_runtime_module (stubs: the closure of the exports uses no Init constant, so there is nothing to
 *   initialise; the linker proves it: a reference to one would be an undefined symbol), lean_io_mark_end_initialization, the panics (trap).
 * Single-threaded: lean.h is built without LEAN_MIMALLOC (runtime/include/lean/config.h), so objects carry their size in the word before them (lean_alloc_small_object). */
#include <lean/lean.h>
#include <stdlib.h>
#include <string.h>

#define TRAP() __builtin_trap()
static size_t live_;   /* bytes currently allocated (payloads), exported for the leak test */

/* ---- memory ---- */
#ifdef __wasm__
void *memcpy(void *d, const void *s, size_t n) { return __builtin_memcpy(d, s, n); }   /* memory.copy (bulk-memory) */
void *memmove(void *d, const void *s, size_t n) { return __builtin_memmove(d, s, n); }
void *memset(void *d, int c, size_t n) { return __builtin_memset(d, c, n); }
#else
/* The compiler may emit calls to these even from freestanding code (struct copies, zeroing): they must exist, and must not be turned back into calls to themselves (no_builtin). */
__attribute__((no_builtin("memcpy"))) void *memcpy(void *d, const void *s, size_t n) {
  unsigned char *dp = d; const unsigned char *sp = s;
  while (n > 7) { uint64_t w; __builtin_memcpy_inline(&w, sp, 8); __builtin_memcpy_inline(dp, &w, 8); dp += 8; sp += 8; n -= 8; }
  while (n--) *dp++ = *sp++;
  return d;
}
__attribute__((no_builtin("memmove"))) void *memmove(void *d, const void *s, size_t n) {
  unsigned char *dp = d; const unsigned char *sp = s;
  if (dp <= sp || dp >= sp + n) { while (n--) *dp++ = *sp++; }
  else { dp += n; sp += n; while (n--) *--dp = *--sp; }
  return d;
}
__attribute__((no_builtin("memset"))) void *memset(void *d, int c, size_t n) {
  unsigned char *dp = d;
  while (n--) *dp++ = (unsigned char)c;
  return d;
}
#endif
int memcmp(const void *a, const void *b, size_t n) {
  const unsigned char *x = a, *y = b;
  for (size_t i = 0; i < n; i++) if (x[i] != y[i]) return x[i] < y[i] ? -1 : 1;
  return 0;
}
size_t strlen(const char *s) { size_t n = 0; while (s[n]) n++; return n; }
void abort(void) { TRAP(); }

/* The allocator. Block = 8-byte header (the usable size) + payload, payload 8-aligned. Sizes up to 1024 get an exact 8-byte class; larger ones round up to a power of two.
 * Freed blocks go to their class's list and are reused; the heap only grows (a parse leaves the Lean heap empty, so the arena stops growing at its high-water mark). */
#ifdef __wasm__
extern unsigned char __heap_base;
#else
#ifndef VBM_RT_ARENA_BYTES
#define VBM_RT_ARENA_BYTES (256UL << 20)
#endif
_Static_assert(VBM_RT_ARENA_BYTES < (1UL << 32) - 4096, "object links are 32-bit offsets into the arena");
static unsigned char arena_[VBM_RT_ARENA_BYTES] __attribute__((aligned(16)));
#endif
#define SMALL_MAX 1024
#define NSMALL (SMALL_MAX / 8 + 1)
#define NBIG 24   /* 2^11 .. 2^34 */
static void *small_[NSMALL], *big_[NBIG];
static unsigned char *brk_, *end_;

static size_t class_size(size_t n, void ***list) {
  if (n <= SMALL_MAX) { n = (n + 7) & ~(size_t)7; if (!n) n = 8; *list = &small_[n / 8]; return n; }
  size_t c = 2048; int k = 0;
  while (c < n) { c <<= 1; k++; if (k >= NBIG) return 0; }
  *list = &big_[k]; return c;
}

void *malloc(size_t n) {
  void **list; size_t c = class_size(n, &list);
  if (!c) return 0;
  if (*list) { void *p = *list; *list = *(void **)p; live_ += c; return p; }
#ifdef __wasm__
  if (!brk_) { brk_ = (unsigned char *)(((uintptr_t)&__heap_base + 7) & ~(uintptr_t)7); end_ = (unsigned char *)(__builtin_wasm_memory_size(0) * 65536UL); }
  size_t need = c + 8;
  if (need < c || (size_t)(end_ - brk_) < need) {
    size_t short_ = need - (size_t)(end_ - brk_), pages = (short_ + 65535) / 65536;
    if (pages > 65536 || __builtin_wasm_memory_grow(0, pages) == (size_t)-1) return 0;
    end_ += pages * 65536;
  }
#else
  if (!brk_) { brk_ = arena_; end_ = arena_ + sizeof arena_; }
  size_t need = c + 8;
  if (need < c || (size_t)(end_ - brk_) < need) return 0;   /* arena exhausted: the caller (lean_alloc_small_object) panics, i.e. traps */
#endif
  unsigned char *p = brk_ + 8;
  *(size_t *)(brk_) = c;
  brk_ += need; live_ += c;
  return p;
}
void free(void *p) {
  if (!p) return;
  size_t c = *(size_t *)((unsigned char *)p - 8); void **list; (void)class_size(c, &list);
  live_ -= c; *(void **)p = *list; *list = p;
}
void free_sized(void *p, size_t n) { (void)n; free(p); }

/* ---- the Lean objects ---- */
void lean_inc_heartbeat(void) {}
void lean_notify_assert(const char *f, int l, const char *c) { (void)f; (void)l; (void)c; TRAP(); }
void lean_internal_panic(const char *m) { (void)m; TRAP(); }
void lean_internal_panic_out_of_memory(void) { TRAP(); }
void lean_internal_panic_unreachable(void) { TRAP(); }
void lean_internal_panic_rc_overflow(void) { TRAP(); }
void lean_internal_panic_overflow(void) { TRAP(); }

lean_object *lean_alloc_object(size_t sz) { if (sz > 0xfffffff0u) lean_internal_panic_out_of_memory(); return lean_alloc_small_object((unsigned)((sz + 7) & ~(size_t)7)); }
void lean_free_object(lean_object *o) { lean_free_small_object(o); }

/* Delete o (its count reached zero) and, iteratively, every child whose count then reaches zero: the pending list is threaded through the dead objects' own m_rc word
 * (32 bits: a pointer on wasm32, an offset into the arena natively), so a long list is freed without recursion. */
#ifdef __wasm__
#define LINK_ENC(o) ((uint32_t)(uintptr_t)(o))
#define LINK_DEC(w) ((lean_object *)(uintptr_t)(w))
#else
#define LINK_ENC(o) ((o) ? (uint32_t)((unsigned char *)(o) - arena_) : 0u)   /* every object lives in arena_, past its first 16 bytes: never offset 0 */
#define LINK_DEC(w) ((w) ? (lean_object *)(arena_ + (w)) : (lean_object *)0)
#endif
static lean_object *link_get(lean_object *o) { return LINK_DEC(*(uint32_t *)&o->m_rc); }
static void link_set(lean_object *o, lean_object *n) { *(uint32_t *)&o->m_rc = LINK_ENC(n); }
static void push_dec(lean_object **todo, lean_object *c) {
  if (lean_is_scalar(c)) return;
  int rc = lean_internal_get_rc(c);
  if (rc > 1) lean_internal_sub_rc(c, 1);
  else if (rc == 1) { link_set(c, *todo); *todo = c; }
  /* rc == 0: persistent, never freed; rc < 0: multi-threaded, not produced here */
}
void lean_dec_ref_cold(lean_object *o) {
  if (lean_internal_get_rc(o) != 1) TRAP();
  lean_object *todo = o; link_set(o, 0);
  while (todo) {
    lean_object *x = todo; todo = link_get(x);
    unsigned tag = x->m_tag;
    if (tag <= LeanMaxCtorTag) { unsigned n = x->m_other; for (unsigned i = 0; i < n; i++) push_dec(&todo, lean_ctor_get(x, i)); }
    else if (tag == LeanArray) { lean_array_object *a = (lean_array_object *)x; for (size_t i = 0; i < a->m_size; i++) push_dec(&todo, a->m_data[i]); }
    else if (tag == LeanClosure) { lean_closure_object *c = (lean_closure_object *)x; for (unsigned i = 0; i < c->m_num_fixed; i++) push_dec(&todo, c->m_objs[i]); }
    else if (tag == LeanScalarArray || tag == LeanString) { /* no children */ }
    else TRAP();
    lean_free_small_object(x);
  }
}

/* Mark o and everything it reaches persistent (count 0): used on the closed constants after module initialisation (small, shallow terms: plain recursion). */
void lean_mark_persistent(lean_object *o) {
  if (lean_is_scalar(o) || lean_internal_get_rc(o) == 0) return;
  lean_internal_set_rc(o, 0);
  unsigned tag = o->m_tag;
  if (tag <= LeanMaxCtorTag) { for (unsigned i = 0; i < o->m_other; i++) lean_mark_persistent(lean_ctor_get(o, i)); }
  else if (tag == LeanArray) { lean_array_object *a = (lean_array_object *)o; for (size_t i = 0; i < a->m_size; i++) lean_mark_persistent(a->m_data[i]); }
  else if (tag == LeanClosure) { lean_closure_object *c = (lean_closure_object *)o; for (unsigned i = 0; i < c->m_num_fixed; i++) lean_mark_persistent(c->m_objs[i]); }
  else if (tag == LeanScalarArray || tag == LeanString) { }
  else TRAP();
}

/* Bignums are not linked: a Nat above LEAN_MAX_SMALL_NAT (2^31-1 on wasm32, 2^63-1 natively) would need them. The parser's Nats are input offsets (the shim refuses len > LEAN_MAX_SMALL_NAT, the loader
 * refuses more than 2^30 bytes), so this is unreachable; if it ever were reached it traps rather than answer. */
lean_object *lean_nat_big_add(lean_object *a, lean_object *b) { (void)a; (void)b; TRAP(); }
bool lean_nat_big_lt(lean_object *a, lean_object *b) { (void)a; (void)b; TRAP(); }
lean_object *lean_big_usize_to_nat(size_t n) { (void)n; TRAP(); }
lean_object *lean_big_uint64_to_nat(uint64_t n) { (void)n; TRAP(); }   /* the printer's tape words: every word read as a Nat is first bounded (a length is below 2^56, an offset below 2^62: LeanJson/PrintTape.lean) */
lean_object *lean_nat_big_sub(lean_object *a, lean_object *b) { (void)a; (void)b; TRAP(); }
lean_object *lean_nat_big_mul(lean_object *a, lean_object *b) { (void)a; (void)b; TRAP(); }
lean_object *lean_nat_overflow_mul(size_t a, size_t b) { (void)a; (void)b; TRAP(); }
bool lean_nat_big_eq(lean_object *a, lean_object *b) { (void)a; (void)b; TRAP(); }
bool lean_nat_big_le(lean_object *a, lean_object *b) { (void)a; (void)b; TRAP(); }
uint8_t lean_uint8_of_big_nat(lean_object *a) { (void)a; TRAP(); }
uint64_t lean_uint64_of_big_nat(lean_object *a) { (void)a; TRAP(); }
size_t lean_usize_of_big_nat(lean_object *a) { (void)a; TRAP(); }
lean_object *lean_nat_big_land(lean_object *a, lean_object *b) { (void)a; (void)b; TRAP(); }
lean_object *lean_nat_big_mod(lean_object *a, lean_object *b) { (void)a; (void)b; TRAP(); }
lean_object *lean_nat_big_shiftr(lean_object *a, lean_object *b) { (void)a; (void)b; TRAP(); }

/* ---- the rest of libleanrt and Init that the closure reaches (found by linking: every one is an undefined symbol until written) ---- */
lean_object *lean_obj_once_cold(lean_object **loc, lean_once_cell_t *tok, lean_object *(*init)(void)) {
  if (tok->state == 0) { lean_object *v = init(); lean_mark_persistent(v); *loc = v; tok->state = 1; }
  return *loc;
}

/* The same for a closed term of type UInt64 (the constants of the bit-parallel kernels). Single-threaded, like the rest of the freestanding heap. */
uint64_t lean_uint64_once_cold(uint64_t *loc, lean_once_cell_t *tok, uint64_t (*init)(void)) {
  if (tok->state == 0) { *loc = init(); tok->state = 1; }
  return *loc;
}

/* `Char.ofNat n` (Init; n borrowed): n itself when it is a Unicode scalar value, else 0. */
uint32_t l_Char_ofNat(lean_object *n) {
  if (!lean_is_scalar(n)) return 0;
  size_t v = lean_unbox(n);
  return (v < 0xd800 || (v > 0xdfff && v < 0x110000)) ? (uint32_t)v : 0;
}

/* `List.lengthTR` (Init; borrowed). */
lean_object *l_List_lengthTR___redArg(lean_object *l) {
  size_t n = 0;
  while (!lean_is_scalar(l)) { n++; l = lean_ctor_get(l, 1); }
  return lean_box(n);
}

lean_object *l_List_reverse___redArg(lean_object *l);
/* `List.appendTR as bs` (Init; both owned): as.reverse onto bs, cell by cell. */
lean_object *l_List_appendTR___redArg(lean_object *as, lean_object *bs) {
  lean_object *r = l_List_reverse___redArg(as);
  while (!lean_is_scalar(r)) {
    lean_object *hd = lean_ctor_get(r, 0), *tl = lean_ctor_get(r, 1), *cell;
    if (lean_is_exclusive(r)) cell = r;
    else { lean_inc(hd); lean_inc(tl); lean_dec_ref(r); cell = lean_alloc_ctor(1, 2, 0); lean_ctor_set(cell, 0, hd); }
    lean_ctor_set(cell, 1, bs);
    bs = cell; r = tl;
  }
  return bs;
}

/* Scalar arrays (ByteArray): copy with capacity cap (>= size), consuming a. */
lean_obj_res lean_copy_sarray(lean_obj_arg a, size_t cap) {
  size_t sz = lean_sarray_size(a), es = lean_sarray_elem_size(a);
  lean_object *r = lean_alloc_sarray(es, sz, cap);
  memcpy(lean_sarray_cptr(r), lean_sarray_cptr(a), sz * es);
  lean_dec(a);
  return r;
}
lean_obj_res lean_copy_sarray_nonlinear(lean_obj_arg a, size_t cap) { return lean_copy_sarray(a, cap); }

lean_obj_res lean_byte_array_push(lean_obj_arg a, uint8_t b) {
  size_t sz = lean_sarray_size(a);
  lean_object *r = (lean_is_exclusive(a) && sz < lean_sarray_capacity(a)) ? a : lean_copy_sarray(a, sz < 8 ? 16 : 2 * sz);
  lean_sarray_cptr(r)[sz] = b;
  lean_to_sarray(r)->m_size = sz + 1;
  return r;
}

static size_t nat_or_max(lean_object *n) { return lean_is_scalar(n) ? lean_unbox(n) : (size_t)-1; }
/* `ByteArray.copySlice src srcOff dest destOff len exact`: src borrowed, dest owned (the Nats are scalars or clamp). */
lean_obj_res lean_byte_array_copy_slice(lean_obj_arg src, lean_obj_arg so, lean_obj_arg dest, lean_obj_arg dof, lean_obj_arg ln, uint8_t exact) {
  size_t ssz = lean_sarray_size(src), dsz = lean_sarray_size(dest), src_off = nat_or_max(so);
  if (src_off > ssz) return dest;
  size_t len = nat_or_max(ln); if (len > ssz - src_off) len = ssz - src_off;
  size_t dest_off = nat_or_max(dof); if (dest_off > dsz) dest_off = dsz;
  size_t new_size = dest_off + len; if (new_size < dsz) new_size = dsz;
  lean_object *r = dest;
  if (!(lean_is_exclusive(dest) && lean_sarray_capacity(dest) >= new_size)) {
    size_t cap = exact ? new_size : (2 * new_size > new_size ? 2 * new_size : new_size);
    if (src == dest) { r = lean_copy_sarray(dest, cap); src = r; }   /* src aliases dest: it is borrowed, so keep it alive through the copy */
    else r = lean_copy_sarray(dest, cap);
  }
  lean_to_sarray(r)->m_size = new_size;
  memmove(lean_sarray_cptr(r) + dest_off, lean_sarray_cptr(src) + src_off, len);
  return r;
}

/* `String.toUTF8` (s borrowed): the bytes without the terminating NUL. */
lean_obj_res lean_string_to_utf8(lean_object *s) {
  size_t n = lean_string_size(s) - 1;
  lean_object *r = lean_alloc_sarray(1, n, n);
  memcpy(lean_sarray_cptr(r), lean_string_cstr(s), n);
  return r;
}

/* `List.toArray` (Array.mk; the list is owned: each head is retained, then the list released). */
lean_object *lean_array_mk(lean_obj_arg l) {
  size_t n = 0;
  for (lean_object *p = l; !lean_is_scalar(p); p = lean_ctor_get(p, 1)) n++;
  lean_object *a = lean_alloc_array(n, n), *p = l; size_t i = 0;
  for (; !lean_is_scalar(p); p = lean_ctor_get(p, 1)) { lean_object *h = lean_ctor_get(p, 0); lean_inc(h); lean_array_cptr(a)[i++] = h; }
  lean_dec(l);
  return a;
}
/* `ByteArray.mk` (the Array UInt8 is owned; its elements are boxed scalars). */
lean_obj_res lean_byte_array_mk(lean_obj_arg a) {
  size_t n = lean_array_size(a);
  lean_object *r = lean_alloc_sarray(1, n, n);
  for (size_t i = 0; i < n; i++) lean_sarray_cptr(r)[i] = (uint8_t)lean_unbox(lean_array_cptr(a)[i]);
  lean_dec(a);
  return r;
}

/* `String.push s c` (s owned; c a Unicode scalar value): in place when s is unshared and has room. */
lean_obj_res lean_string_push(lean_obj_arg s, uint32_t c) {
  unsigned char b[4]; size_t k;
  if (c < 0x80) { b[0] = (unsigned char)c; k = 1; }
  else if (c < 0x800) { b[0] = 0xc0 | (c >> 6); b[1] = 0x80 | (c & 0x3f); k = 2; }
  else if (c < 0x10000) { b[0] = 0xe0 | (c >> 12); b[1] = 0x80 | ((c >> 6) & 0x3f); b[2] = 0x80 | (c & 0x3f); k = 3; }
  else { b[0] = 0xf0 | (c >> 18); b[1] = 0x80 | ((c >> 12) & 0x3f); b[2] = 0x80 | ((c >> 6) & 0x3f); b[3] = 0x80 | (c & 0x3f); k = 4; }
  size_t sz = lean_string_size(s), len = lean_string_len(s), nsz = sz + k;   /* sz counts the NUL */
  lean_object *r = s;
  if (!(lean_is_exclusive(s) && lean_string_capacity(s) >= nsz)) {
    size_t cap = 2 * nsz < 16 ? 16 : 2 * nsz;
    r = lean_alloc_string(sz, cap, len);
    memcpy((char *)lean_string_cstr(r), lean_string_cstr(s), sz);
    lean_dec(s);
  }
  lean_string_object *o = lean_to_string(r);
  memcpy(o->m_data + sz - 1, b, k); o->m_data[nsz - 1] = 0;
  o->m_size = nsz; o->m_length = len + 1;
  return r;
}

/* `List.reverse` (Init, l_List_reverse___redArg: the only Init function the closure of the exports calls): the list is consumed (owned); a cons cell nobody else holds is reused. */
lean_object *l_List_reverse___redArg(lean_object *l) {
  lean_object *acc = lean_box(0);
  while (!lean_is_scalar(l)) {
    lean_object *hd = lean_ctor_get(l, 0), *tl = lean_ctor_get(l, 1), *cell;
    if (lean_is_exclusive(l)) cell = l;
    else { lean_inc(hd); lean_inc(tl); lean_dec_ref(l); cell = lean_alloc_ctor(1, 2, 0); lean_ctor_set(cell, 0, hd); }
    lean_ctor_set(cell, 1, acc);
    acc = cell; l = tl;
  }
  return acc;
}

void lean_initialize_runtime_module(void) {}
/* `ByteArray.empty` (an Init constant: the only one the closure reads), initialised by initialize_Init as the real one is. An unresolved data symbol would silently read address 0, so
 * scripts/build_wasm.sh links WITHOUT --allow-undefined: any other Init constant the closure grows to need is a link error, not garbage. */
lean_object *l_ByteArray_empty;
lean_object *initialize_Init(uint8_t builtin) {
  (void)builtin;
  l_ByteArray_empty = lean_alloc_sarray(1, 0, 0);
  lean_mark_persistent(l_ByteArray_empty);
  return lean_io_result_mk_ok(lean_box(0));
}
void lean_io_mark_end_initialization(void) {}

/* ---- the host's view ---- */
#ifdef __wasm__
__attribute__((export_name("vbm_json_wasm_alloc"))) void *vbm_json_wasm_alloc(size_t n) { return malloc(n); }
__attribute__((export_name("vbm_json_wasm_dealloc"))) void vbm_json_wasm_dealloc(void *p) { free(p); }
__attribute__((export_name("vbm_json_wasm_live"))) size_t vbm_json_wasm_live(void) { return live_; }   /* test hook: bytes allocated and not yet freed */
#else
size_t vbm_json_rt_live(void) { return live_; }   /* test hook: bytes allocated and not yet freed (the leak test of scripts/test_native.sh) */
#endif
