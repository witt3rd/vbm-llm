/* abi/vbm_json.c: the C edge of vbm-json (slice 1). TRUSTED, unverified (docs/trust-ledger.md, entry T09). It moves bytes: copies the input into a Lean ByteArray, calls the
 * Lean export vbm_json_parse_tape (LeanJson/Tape.lean: the parse, the policies and the tape layout are decided there), and copies the result into memory from the embedder's allocator (or, with the default allocator, hands the result out in place).
 * Contract: include/vbm_json.h. It decides nothing about JSON. */
#include "../include/vbm_json.h"
#if __STDC_HOSTED__
#include <lean/lean.h>
#else
#include "lean_mini.h"   /* freestanding: no libc header is reachable (-ffreestanding -nostdinc); the few lean.h names this file uses, as lean.h defines them (tests/lean_layout.c checks that) */
#endif
/* No libc symbol is referenced from this file: no malloc/free (the default allocator is a Lean ByteArray), no memcpy/memset (the loops below, which the compiler may not turn back into calls), no pthread_once. */
#ifndef memcpy   /* tests/abi_test.c substitutes its own */
__attribute__((no_builtin("memcpy"))) static void *vbm_copy_(void *d, const void *s, size_t n) {
  unsigned char *dp = d; const unsigned char *sp = s;
  while (n > 7) { uint64_t w; __builtin_memcpy_inline(&w, sp, 8); __builtin_memcpy_inline(dp, &w, 8); dp += 8; sp += 8; n -= 8; }
  while (n--) *dp++ = *sp++;
  return d;
}
#define memcpy vbm_copy_
#endif
__attribute__((no_builtin("memset"))) static void vbm_zero_(void *d, size_t n) { unsigned char *dp = d; while (n--) *dp++ = 0; }

_Static_assert(__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__, "the tape is little-endian u64 words: a little-endian host is required");

lean_object *vbm_json_parse_tape(lean_object *input);     /* the Lean export (LeanJsonSimd/ParseSimd.lean: parseTapeSimd) */
lean_object *initialize_vbm_x2djson_LeanJsonSimd_ParseSimd(uint8_t builtin);   /* Lean 4.35 names it package_Module; it also initialises the runtime and Init */
lean_object *vbm_json_lean_print_tape(lean_object *words, lean_object *text);   /* the Lean exports of LeanJsonSimd/PrintSimd.lean (print and escape): the JSON bytes, or no bytes for a refused tape */
lean_object *vbm_json_lean_escape_string(lean_object *text);                    /* the string literal, or no bytes for text that is not valid UTF-8 */
lean_object *initialize_vbm_x2djson_LeanJsonSimd_PrintSimd(uint8_t builtin);

/* Once-only initialisation: 0 = not started, 1 = running, 2 = done. A concurrent first caller waits for the first to finish. */
static int once_state_;
static int init_ok_;

static void init_once_(void) {
  int expect = 0;
  if (__atomic_compare_exchange_n(&once_state_, &expect, 1, 0, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE)) {
    lean_object *r = initialize_vbm_x2djson_LeanJsonSimd_ParseSimd(1);
    init_ok_ = lean_io_result_is_ok(r);
    lean_dec_ref(r);
    if (init_ok_) { r = initialize_vbm_x2djson_LeanJsonSimd_PrintSimd(1); init_ok_ = lean_io_result_is_ok(r); lean_dec_ref(r); }
    lean_io_mark_end_initialization();
    __atomic_store_n(&once_state_, 2, __ATOMIC_RELEASE);
  } else {
    while (__atomic_load_n(&once_state_, __ATOMIC_ACQUIRE) != 2) { }
  }
}

/* The default allocator: a block is inside the payload of a Lean ByteArray, released with lean_dec_ref. The ByteArray payload is only 4-aligned on wasm32 (the runtime's header word is 4 bytes), so the block is
 * the first 8-aligned address past the payload's first byte and the byte before it records the distance back (1..8). The Lean heap is the only heap the library has. */
static void *dflt_alloc_(void *ctx, size_t n) {
  (void)ctx;
  unsigned char *d = lean_sarray_cptr(lean_alloc_sarray(1, n + 8, n + 8));
  unsigned char *b = (unsigned char *)(((uintptr_t)d + 8) & ~(uintptr_t)7);
  b[-1] = (unsigned char)(b - d);
  return b;
}
static void dflt_free_(void *ctx, void *p, size_t n) {
  (void)ctx; (void)n;
  unsigned char *d = (unsigned char *)p - ((unsigned char *)p)[-1];
  lean_dec_ref((lean_object *)(d - __builtin_offsetof(lean_sarray_object, m_data)));
}
static const vbm_json_allocator dflt_ = { 0, dflt_alloc_, dflt_free_ };
/* The default allocator, in place: the export's result (24 header bytes, the words, the text) is a Lean ByteArray already, so with the default allocator, a result nobody else holds and the words 8-aligned in its payload
 * nothing is allocated or copied: the block IS the ByteArray (block_ is the object, not a payload address) and the tape points into it; vbm_json_free releases it with lean_dec_ref. Otherwise (a custom allocator, or a payload
 * that is only 4-aligned, as on wasm32) the tape is copied into a block as before. */
static void dflt_free_inplace_(void *ctx, void *p, size_t n) { (void)ctx; (void)n; lean_dec_ref((lean_object *)p); }
static const vbm_json_allocator dflt_inplace_ = { 0, dflt_alloc_, dflt_free_inplace_ };

static uint64_t word_(const uint8_t *p) { uint64_t w; memcpy(&w, p, 8); return w; }   /* little-endian host */

int vbm_json_parse(const uint8_t *buf, size_t len, const vbm_json_opts *opts, vbm_json_tape *tape) {
  if (!tape) return VBM_JSON_ARG;
  vbm_zero_(tape, sizeof *tape);
  if ((!buf && len) || len > (size_t)LEAN_MAX_SMALL_NAT) return VBM_JSON_ARG;
  const vbm_json_allocator *al = &dflt_;
  if (opts) {
    if (opts->size < sizeof(size_t) + sizeof(void *)) return VBM_JSON_ARG;   /* too old to carry an allocator field */
    if (opts->allocator) al = opts->allocator;
  }
  if (!al->alloc || !al->free) return VBM_JSON_ARG;
  init_once_();
  if (!init_ok_) return VBM_JSON_INTERNAL;

  lean_object *in = lean_alloc_sarray(1, len, len);
  if (len) memcpy(lean_sarray_cptr(in), buf, len);
  lean_object *out = vbm_json_parse_tape(in);                 /* consumes `in` */
  const uint8_t *p = lean_sarray_cptr(out);
  size_t n = lean_sarray_size(out);
  int rc = VBM_JSON_INTERNAL;
  if (n >= 24) {
    uint64_t status = word_(p), nw = word_(p + 8), nt = word_(p + 16);
    if (status == VBM_JSON_SYNTAX || status == VBM_JSON_DEPTH) {
      if (n == 24 && nw == 0 && nt == 0) rc = (int)status;
    } else if (status == 0 && nw <= (n - 24) / 8 && nt <= n && 24 + 8 * nw + nt == n) {
      size_t total = n - 24;                                   /* words, then text: one block */
      const uint8_t *wp = p + 24;                              /* the words, in the result's payload */
      if (al == &dflt_ && ((uintptr_t)wp & 7) == 0 && lean_is_exclusive(out)) {   /* in place: ownership of `out` passes to the tape */
        tape->words = (const uint64_t *)wp; tape->nwords = (size_t)nw;
        tape->text = wp + 8 * nw; tape->ntext = (size_t)nt;
        tape->block_ = out; tape->block_size_ = total ? total : 8; tape->allocator_ = dflt_inplace_;
        return VBM_JSON_OK;
      }
      void *blk = al->alloc(al->ctx, total ? total : 8);
      if (!blk) rc = VBM_JSON_NOMEM;
      else if ((uintptr_t)blk % 8) { al->free(al->ctx, blk, total ? total : 8); rc = VBM_JSON_ARG; }
      else {
        memcpy(blk, p + 24, total);
        tape->words = blk; tape->nwords = (size_t)nw;
        tape->text = (const uint8_t *)blk + 8 * nw; tape->ntext = (size_t)nt;
        tape->block_ = blk; tape->block_size_ = total ? total : 8; tape->allocator_ = *al;
        rc = VBM_JSON_OK;
      }
    }
  }
  lean_dec_ref(out);
  return rc;
}

void vbm_json_free(vbm_json_tape *tape) {
  if (!tape) return;
  if (tape->block_) tape->allocator_.free(tape->allocator_.ctx, tape->block_, tape->block_size_);
  vbm_zero_(tape, sizeof *tape);
}

/* PRINTING (the same rules as the parse: the allocator in opts, the default one handing the Lean result out in place). The Lean functions decide everything (what a tape prints to, what is valid UTF-8); this moves bytes. */
static int pick_alloc_(const vbm_json_opts *opts, const vbm_json_allocator **al) {
  *al = &dflt_;
  if (opts) {
    if (opts->size < sizeof(size_t) + sizeof(void *)) return VBM_JSON_ARG;
    if (opts->allocator) *al = opts->allocator;
  }
  return (*al)->alloc && (*al)->free ? VBM_JSON_OK : VBM_JSON_ARG;
}

/* Hand out the Lean result `r` (consumed): no bytes = `refused`; with the default allocator and a result nobody else holds, the ByteArray itself; otherwise a copy in one block from the embedder's allocator. */
static int deliver_(lean_object *r, const vbm_json_allocator *al, vbm_json_bytes *out, int refused) {
  size_t n = lean_sarray_size(r);
  int rc = refused;
  if (n == 0) { }
  else if (al == &dflt_ && lean_is_exclusive(r)) {
    out->data = lean_sarray_cptr(r); out->len = n;
    out->block_ = r; out->block_size_ = n; out->allocator_ = dflt_inplace_;
    return VBM_JSON_OK;
  } else {
    void *blk = al->alloc(al->ctx, n);
    if (!blk) rc = VBM_JSON_NOMEM;
    else if ((uintptr_t)blk % 8) { al->free(al->ctx, blk, n); rc = VBM_JSON_ARG; }
    else {
      memcpy(blk, lean_sarray_cptr(r), n);
      out->data = blk; out->len = n; out->block_ = blk; out->block_size_ = n; out->allocator_ = *al;
      rc = VBM_JSON_OK;
    }
  }
  lean_dec_ref(r);
  return rc;
}

int vbm_json_print_tape(const vbm_json_tape *tape, const vbm_json_opts *opts, vbm_json_bytes *out) {
  if (!out) return VBM_JSON_ARG;
  vbm_zero_(out, sizeof *out);
  if (!tape || (!tape->words && tape->nwords) || (!tape->text && tape->ntext)) return VBM_JSON_ARG;
  if (tape->nwords > (size_t)LEAN_MAX_SMALL_NAT / 8 || tape->ntext > (size_t)LEAN_MAX_SMALL_NAT) return VBM_JSON_ARG;
  const vbm_json_allocator *al;
  int rc = pick_alloc_(opts, &al);
  if (rc) return rc;
  init_once_();
  if (!init_ok_) return VBM_JSON_INTERNAL;
  size_t wb = tape->nwords * 8;
  lean_object *w = lean_alloc_sarray(1, wb, wb), *x = lean_alloc_sarray(1, tape->ntext, tape->ntext);
  if (wb) memcpy(lean_sarray_cptr(w), tape->words, wb);
  if (tape->ntext) memcpy(lean_sarray_cptr(x), tape->text, tape->ntext);
  return deliver_(vbm_json_lean_print_tape(w, x), al, out, VBM_JSON_ARG);   /* consumes w and x */
}

int vbm_json_escape_string(const uint8_t *buf, size_t len, const vbm_json_opts *opts, vbm_json_bytes *out) {
  if (!out) return VBM_JSON_ARG;
  vbm_zero_(out, sizeof *out);
  if ((!buf && len) || len > (size_t)LEAN_MAX_SMALL_NAT) return VBM_JSON_ARG;
  const vbm_json_allocator *al;
  int rc = pick_alloc_(opts, &al);
  if (rc) return rc;
  init_once_();
  if (!init_ok_) return VBM_JSON_INTERNAL;
  lean_object *in = lean_alloc_sarray(1, len, len);
  if (len) memcpy(lean_sarray_cptr(in), buf, len);
  return deliver_(vbm_json_lean_escape_string(in), al, out, VBM_JSON_SYNTAX);   /* consumes in */
}

void vbm_json_bytes_free(vbm_json_bytes *out) {
  if (!out) return;
  if (out->block_) out->allocator_.free(out->allocator_.ctx, out->block_, out->block_size_);
  vbm_zero_(out, sizeof *out);
}
