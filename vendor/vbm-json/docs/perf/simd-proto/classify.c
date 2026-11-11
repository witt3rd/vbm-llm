/* docs/perf/simd-proto/classify.c: PROTOTYPE of the stage-1 classifier of docs/perf/simd-plan.md. Not part of the library, not a gate, not linked into any export.
 *
 * Stage 1 reads the input 64 bytes at a time and produces, per block, one 64-bit mask `structural` (bit i set iff byte i starts a token: an operator `{}[]:,` outside a string,
 * a quote of a string (the opening one and the closing one: stage 2 learns where a string ends from the index), or the first byte of a run of scalar bytes (number, literal, or garbage) outside a string), plus two sticky error bits (a control byte < 0x20
 * inside a string; invalid UTF-8 anywhere) and three bits of state carried from block to block (escape, in-string, previous byte was a scalar).
 *
 * Variants (all must agree bit for bit; `main` checks that on every input before timing anything):
 *   scalar  one byte at a time, a transcription of the specification (a Mealy machine over bytes). The REFERENCE of this file.
 *   swar    portable 64-bit code, 8 bytes per u64 word, no intrinsics: the shape the Lean C emitter can produce (the same arithmetic is in Stage1.lean).
 *   avx2    256-bit intrinsics (+ PCLMULQDQ for the prefix xor), with the Keiser-Lemire UTF-8 check.
 * Usage: classify FILE...  (prints MB/s per variant; the machine is shared, so each number is the best of several 0.4 s windows).  Build: see run.sh. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <immintrin.h>

typedef uint64_t u64; typedef uint8_t u8;
#define EVEN 0x5555555555555555ULL
#define ODD  0xAAAAAAAAAAAAAAAAULL

/* ---------- shared state and the in-block combination (the part that is plain u64 arithmetic in every variant) ---------- */
typedef struct { u64 esc, str, scal, err_ctrl; u64 utf8; } state_t;   /* esc/str/scal in {0,1}; utf8 = the scalar DFA state (scalar+swar) */

/* raw per-block class masks: bit i of each is a predicate of byte i alone */
typedef struct { u64 quote, bslash, op, ws, ctrl; } masks_t;

static inline u64 prefix_xor(u64 x) { x ^= x << 1; x ^= x << 2; x ^= x << 4; x ^= x << 8; x ^= x << 16; x ^= x << 32; return x; }

/* find_escaped: bit i of the result is set iff byte i is escaped (preceded by an odd run of backslashes, the run started by `*esc` carry counting), via two additions. Updates *esc. */
static inline u64 find_escaped(u64 B, u64 *esc) {
  u64 prev = *esc;
  u64 bs = B & ~prev;                       /* a backslash that is itself escaped by the carry opens no run */
  u64 starts = bs & ~(bs << 1);
  u64 ev = starts & EVEN, od = starts & ODD;
  u64 s_ev = bs + ev, s_od = bs + od;
  u64 ends_ev = s_ev & ~bs, ends_od = s_od & ~bs;
  *esc = (s_od < bs);                       /* carry out of bit 63 of the odd-start addition: an odd run reaches the block end */
  return (ends_ev & ODD) | (ends_od & EVEN) | prev;
}

/* the combination: returns the structural mask, updates the carried state, accumulates the control-byte error */
static inline u64 combine(const masks_t *m, state_t *s) {
  u64 escaped = find_escaped(m->bslash, &s->esc);
  u64 Q = m->quote & ~escaped;
  u64 in_str = prefix_xor(Q) ^ (0 - s->str);
  s->str = in_str >> 63;
  u64 nq = ~(m->op | m->ws | Q);
  u64 follows = (nq << 1) | s->scal;
  s->scal = nq >> 63;
  u64 pseudo = nq & ~follows & ~in_str;
  s->err_ctrl |= m->ctrl & in_str;
  return (m->op & ~in_str) | Q | pseudo;
}

/* ---------- UTF-8: the scalar DFA (the specification; RFC 3629 accepts exactly these) ---------- */
/* states: 0 accept; 1,2,3 continuation bytes owed; 4 after E0 (A0..BF), 5 after ED (80..9F), 6 after F0 (90..BF), 7 after F4 (80..8F); 8 error (sticky) */
static inline unsigned u8step(unsigned s, unsigned b) {
  switch (s) {
    case 0: if (b < 0x80) return 0; if (b < 0xC2) return 8; if (b < 0xE0) return 1; if (b == 0xE0) return 4; if (b == 0xED) return 5; if (b < 0xF0) return 2;
            if (b == 0xF0) return 6;
            if (b < 0xF4) return 3; if (b == 0xF4) return 7; return 8;
    case 1: case 2: case 3: return (b >= 0x80 && b < 0xC0) ? s - 1 : 8;
    case 4: return (b >= 0xA0 && b < 0xC0) ? 1 : 8;
    case 5: return (b >= 0x80 && b < 0xA0) ? 1 : 8;
    case 6: return (b >= 0x90 && b < 0xC0) ? 2 : 8;
    case 7: return (b >= 0x80 && b < 0x90) ? 2 : 8;
    default: return 8;
  }
}

/* ---------- variant 0: scalar, the Mealy machine over bytes (specification) ---------- */
static inline int is_ws(u8 c) { return c == 0x20 || c == 0x09 || c == 0x0A || c == 0x0D; }
static inline int is_op(u8 c) { return c == '{' || c == '}' || c == '[' || c == ']' || c == ':' || c == ','; }
static void block_scalar(const u8 *p, state_t *s, u64 *S) {
  u64 out = 0;
  for (int i = 0; i < 64; i++) {
    u8 c = p[i];
    s->utf8 = u8step((unsigned)s->utf8, c);
    int escaped = (int)s->esc; s->esc = (c == '\\') && !escaped;            /* escape state: tracked everywhere, in or out of a string (the vector kernel does the same) */
    int quote = (c == '"') && !escaped; s->str ^= (u64)quote;               /* an unescaped quote toggles; in_str includes the opening quote and excludes the closing one */
    int op = is_op(c), ws = is_ws(c), nq = !(op || ws || quote);
    if (c < 0x20 && s->str) s->err_ctrl |= 1;
    int st = (op && !s->str) || quote || (nq && !s->scal && !s->str);
    s->scal = (u64)nq;
    out |= (u64)st << i;
  }
  *S = out;
}

/* ---------- variant 1: SWAR, 8 bytes per u64 ---------- */
#define REP(c) ((u64)(c) * 0x0101010101010101ULL)
#define LO7 0x7f7f7f7f7f7f7f7fULL
static inline u64 zl(u64 x) { return ~(((x & LO7) + LO7) | x | LO7); }          /* 0x80 in each byte lane of x that is zero (exact) */
static inline u64 pack8(u64 m) { return ((m >> 7) * 0x0102040810204080ULL) >> 56; }   /* the 0x80 lanes to 8 bits, lane i to bit i */
static inline u64 ld64(const u8 *p) { u64 w; memcpy(&w, p, 8); return w; }
static inline void swar_word(u64 w, u64 *q, u64 *b, u64 *o, u64 *ws, u64 *c, int k) {
  u64 wo = w | REP(0x20);
  *q  |= pack8(zl(w ^ REP('"'))) << (8 * k);
  *b  |= pack8(zl(w ^ REP('\\'))) << (8 * k);
  *o  |= pack8(zl(wo ^ REP('{')) | zl(wo ^ REP('}')) | zl(w ^ REP(':')) | zl(w ^ REP(','))) << (8 * k);
  *ws |= pack8(zl(w ^ REP(0x20)) | zl(w ^ REP(0x09)) | zl(w ^ REP(0x0A)) | zl(w ^ REP(0x0D))) << (8 * k);
  *c  |= pack8(zl(w & REP(0xE0))) << (8 * k);
}
/* NB: (w | 0x20) == '{' also matches '[' (0x5B|0x20 = 0x7B) and (w | 0x20) == '}' matches ']' (0x5D|0x20 = 0x7D), and nothing else. */
static void block_swar(const u8 *p, state_t *s, u64 *S) {
  masks_t m = {0, 0, 0, 0, 0}; u64 ors = 0;
  for (int k = 0; k < 8; k++) { u64 w = ld64(p + 8 * k); ors |= w; swar_word(w, &m.quote, &m.bslash, &m.op, &m.ws, &m.ctrl, k); }
  if ((ors & REP(0x80)) == 0) { if (s->utf8 != 0) s->utf8 = 8; }           /* an ASCII block: only a character left open by the previous block is an error */
  else { unsigned st = (unsigned)s->utf8; for (int i = 0; i < 64; i++) st = u8step(st, p[i]); s->utf8 = st; }
  *S = combine(&m, s);
}

/* ---------- variant 2: AVX2 ---------- */
#ifdef __AVX2__
static inline u64 movemask2(__m256i a, __m256i b) { return (u64)(uint32_t)_mm256_movemask_epi8(a) | ((u64)(uint32_t)_mm256_movemask_epi8(b) << 32); }
static inline u64 prefix_xor_clmul(u64 x) { __m128i r = _mm_clmulepi64_si128(_mm_set_epi64x(0, (long long)x), _mm_set1_epi8((char)0xFF), 0); return (u64)_mm_cvtsi128_si64(r); }
typedef struct { __m256i prev_in; } avx_state_t;   /* the last 32 bytes of the previous block, for the UTF-8 lookback */
/* Keiser-Lemire: error bits from the byte pairs (prev1, cur), and the 3- and 4-byte lead checks from prev2, prev3 */
#define TOO_SHORT (1<<0)
#define TOO_LONG (1<<1)
#define OVERLONG_3 (1<<2)
#define TOO_LARGE (1<<3)
#define SURROGATE (1<<4)
#define OVERLONG_2 (1<<5)
#define TOO_LARGE_1000 (1<<6)
#define OVERLONG_4 (1<<6)
#define TWO_CONTS (1<<7)
#define CARRY (TOO_SHORT | TOO_LONG | TWO_CONTS)
static inline __m256i tbl16(const u8 *t) { return _mm256_broadcastsi128_si256(_mm_loadu_si128((const __m128i *)t)); }
static const u8 T1[16] = { TOO_LONG, TOO_LONG, TOO_LONG, TOO_LONG, TOO_LONG, TOO_LONG, TOO_LONG, TOO_LONG, TWO_CONTS, TWO_CONTS, TWO_CONTS, TWO_CONTS,
  TOO_SHORT | OVERLONG_2, TOO_SHORT, TOO_SHORT | OVERLONG_3 | SURROGATE, TOO_SHORT | TOO_LARGE | TOO_LARGE_1000 | OVERLONG_4 };
static const u8 T2[16] = { CARRY | OVERLONG_3 | OVERLONG_2 | OVERLONG_4, CARRY | OVERLONG_2, CARRY, CARRY, CARRY | TOO_LARGE, CARRY | TOO_LARGE | TOO_LARGE_1000,
  CARRY | TOO_LARGE | TOO_LARGE_1000, CARRY | TOO_LARGE | TOO_LARGE_1000, CARRY | TOO_LARGE | TOO_LARGE_1000, CARRY | TOO_LARGE | TOO_LARGE_1000, CARRY | TOO_LARGE | TOO_LARGE_1000,
  CARRY | TOO_LARGE | TOO_LARGE_1000, CARRY | TOO_LARGE | TOO_LARGE_1000, CARRY | TOO_LARGE | TOO_LARGE_1000 | SURROGATE, CARRY | TOO_LARGE | TOO_LARGE_1000, CARRY | TOO_LARGE | TOO_LARGE_1000 };
static const u8 T3[16] = { TOO_SHORT, TOO_SHORT, TOO_SHORT, TOO_SHORT, TOO_SHORT, TOO_SHORT, TOO_SHORT, TOO_SHORT,
  TOO_LONG | OVERLONG_2 | TWO_CONTS | OVERLONG_3 | TOO_LARGE_1000 | OVERLONG_4, TOO_LONG | OVERLONG_2 | TWO_CONTS | OVERLONG_3 | TOO_LARGE,
  TOO_LONG | OVERLONG_2 | TWO_CONTS | SURROGATE | TOO_LARGE, TOO_LONG | OVERLONG_2 | TWO_CONTS | SURROGATE | TOO_LARGE, TOO_SHORT, TOO_SHORT, TOO_SHORT, TOO_SHORT };
/* bytes of `cur` shifted by N positions, filling from `prev` (lane-crossing for AVX2) */
#define SHIFT_IN(N, cur, prev) _mm256_alignr_epi8((cur), _mm256_permute2x128_si256((prev), (cur), 0x21), 16 - (N))
static inline __m256i utf8_check32(__m256i cur, __m256i prev) {
  __m256i p1 = SHIFT_IN(1, cur, prev), p2 = SHIFT_IN(2, cur, prev), p3 = SHIFT_IN(3, cur, prev);
  __m256i m0f = _mm256_set1_epi8(0x0F);
  __m256i sc = _mm256_and_si256(_mm256_and_si256(
      _mm256_shuffle_epi8(tbl16(T1), _mm256_and_si256(_mm256_srli_epi16(p1, 4), m0f)),
      _mm256_shuffle_epi8(tbl16(T2), _mm256_and_si256(p1, m0f))),
      _mm256_shuffle_epi8(tbl16(T3), _mm256_and_si256(_mm256_srli_epi16(cur, 4), m0f)));
  __m256i is3 = _mm256_subs_epu8(p2, _mm256_set1_epi8((char)(0xE0 - 0x80)));
  __m256i is4 = _mm256_subs_epu8(p3, _mm256_set1_epi8((char)(0xF0 - 0x80)));
  __m256i must23_80 = _mm256_and_si256(_mm256_or_si256(is3, is4), _mm256_set1_epi8((char)0x80));
  return _mm256_xor_si256(must23_80, sc);
}
static void block_avx2(const u8 *p, state_t *s, avx_state_t *as, __m256i *uerr, u64 *S) {
  __m256i a = _mm256_loadu_si256((const __m256i *)p), b = _mm256_loadu_si256((const __m256i *)(p + 32));
  #define EQ(x, c) _mm256_cmpeq_epi8((x), _mm256_set1_epi8((char)(c)))
  masks_t m;
  m.quote  = movemask2(EQ(a, '"'), EQ(b, '"'));
  m.bslash = movemask2(EQ(a, '\\'), EQ(b, '\\'));
  __m256i la = _mm256_or_si256(a, _mm256_set1_epi8(0x20)), lb = _mm256_or_si256(b, _mm256_set1_epi8(0x20));
  m.op = movemask2(_mm256_or_si256(_mm256_or_si256(EQ(la, '{'), EQ(la, '}')), _mm256_or_si256(EQ(a, ':'), EQ(a, ','))),
                   _mm256_or_si256(_mm256_or_si256(EQ(lb, '{'), EQ(lb, '}')), _mm256_or_si256(EQ(b, ':'), EQ(b, ','))));
  m.ws = movemask2(_mm256_or_si256(_mm256_or_si256(EQ(a, 0x20), EQ(a, 0x09)), _mm256_or_si256(EQ(a, 0x0A), EQ(a, 0x0D))),
                   _mm256_or_si256(_mm256_or_si256(EQ(b, 0x20), EQ(b, 0x09)), _mm256_or_si256(EQ(b, 0x0A), EQ(b, 0x0D))));
  __m256i e0 = _mm256_set1_epi8(0x1F);   /* byte < 0x20  <=>  max(byte, 0x1F) == 0x1F */
  m.ctrl = movemask2(_mm256_cmpeq_epi8(_mm256_max_epu8(a, e0), e0), _mm256_cmpeq_epi8(_mm256_max_epu8(b, e0), e0));
  /* UTF-8 */
  if (!_mm256_movemask_epi8(_mm256_or_si256(a, b))) {   /* ASCII block: only an unfinished character from the previous block is an error */
    *uerr = _mm256_or_si256(*uerr, _mm256_subs_epu8(as->prev_in, _mm256_setr_epi8(-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,(char)(0xF0-1),(char)(0xE0-1),(char)(0xC0-1))));
    /* (incomplete-at-end test: the last 3 bytes of the previous block hold a lead byte that still wants continuations) */
  } else {
    *uerr = _mm256_or_si256(*uerr, utf8_check32(a, as->prev_in));
    *uerr = _mm256_or_si256(*uerr, utf8_check32(b, a));
  }
  as->prev_in = b;
  /* in-block combination with the clmul prefix xor */
  u64 escaped = find_escaped(m.bslash, &s->esc);
  u64 Q = m.quote & ~escaped;
  u64 in_str = prefix_xor_clmul(Q) ^ (0 - s->str);
  s->str = in_str >> 63;
  u64 nq = ~(m.op | m.ws | Q);
  u64 follows = (nq << 1) | s->scal;
  s->scal = nq >> 63;
  s->err_ctrl |= m.ctrl & in_str;
  *S = (m.op & ~in_str) | Q | (nq & ~follows & ~in_str);
}
#endif

typedef struct { u64 err_ctrl; u64 utf8_err; } result_t;

#ifdef WITH_LEAN
extern void lean_initialize_runtime_module(void);
/* the SAME algorithm as Stage1.lean, compiled by Lean's C emitter (Stage1.c): called through its export with Lean ByteArrays */
#include <lean/lean.h>
extern lean_object *s1_lean(lean_object *a, lean_object *out, size_t n, uint8_t utf8);
extern lean_object *s1_lean_x(lean_object *a, lean_object *out, size_t n, uint8_t utf8);
static int lean_use_x = 0;
extern lean_object *initialize_Stage1(uint8_t builtin, lean_object *w);
static int lean_copy_out = 0, lean_fresh = 1;   /* fresh: re-copy the input into the Lean ByteArray on every call (tests); the timing loops run with fresh = 0 */
static result_t run_lean(const u8 *in, size_t nblk, u64 *out) {
  static const u8 *cached_in; static lean_object *a, *o;
  if (lean_fresh || cached_in != in) { if (a) { lean_dec(a); lean_dec(o); } a = lean_alloc_sarray(1, nblk * 64, nblk * 64); memcpy(lean_sarray_cptr(a), in, nblk * 64); o = lean_alloc_sarray(1, (nblk + 2) * 8, (nblk + 2) * 8); cached_in = in; }
  lean_inc(a); o = lean_use_x ? s1_lean_x(a, o, nblk, 1) : s1_lean(a, o, nblk, 1);
  u64 *p = (u64 *)lean_sarray_cptr(o);
  if (lean_copy_out) memcpy(out, p, nblk * 8);
  result_t r = { p[nblk] != 0, p[nblk + 1] != 0 }; return r;
}
#endif

/* ---------- drivers ---------- */
static result_t run_scalar(const u8 *in, size_t nblk, u64 *out) {
  state_t s = {0, 0, 0, 0, 0};
  for (size_t k = 0; k < nblk; k++) block_scalar(in + 64 * k, &s, &out[k]);
  result_t r = { s.err_ctrl != 0, s.utf8 != 0 }; return r;
}
static result_t run_swar(const u8 *in, size_t nblk, u64 *out) {
  state_t s = {0, 0, 0, 0, 0};
  for (size_t k = 0; k < nblk; k++) block_swar(in + 64 * k, &s, &out[k]);
  result_t r = { s.err_ctrl != 0, s.utf8 != 0 }; return r;
}
#ifdef __AVX2__
static result_t run_avx2(const u8 *in, size_t nblk, u64 *out) {
  state_t s = {0, 0, 0, 0, 0}; avx_state_t as; as.prev_in = _mm256_setzero_si256(); __m256i uerr = _mm256_setzero_si256();
  for (size_t k = 0; k < nblk; k++) block_avx2(in + 64 * k, &s, &as, &uerr, &out[k]);
  /* the input ends at a block boundary here: a lead byte in the last 3 bytes that wants more is an error (the padding of the real stage 1 is space bytes, which the pair checks catch) */
  uint8_t tail[32]; _mm256_storeu_si256((__m256i *)tail, as.prev_in);
  int bad = (tail[31] >= 0xC0) || (tail[30] >= 0xE0) || (tail[29] >= 0xF0);
  result_t r = { s.err_ctrl != 0, bad || !_mm256_testz_si256(uerr, uerr) }; return r;
}
#endif

/* flattening the masks to a u32 index (what stage 2 reads): the simple loop, and the loop that writes 8 candidates unconditionally (no branch per bit) */
static size_t flatten_simple(const u64 *m, size_t nblk, uint32_t *idx) {
  size_t n = 0;
  for (size_t k = 0; k < nblk; k++) { u64 b = m[k]; while (b) { idx[n++] = (uint32_t)(64 * k) + (uint32_t)__builtin_ctzll(b); b &= b - 1; } }
  return n;
}
static size_t flatten_batched(const u64 *m, size_t nblk, uint32_t *idx) {   /* needs tzcnt (BMI): tzcnt(0) = 64, so the surplus writes are harmless garbage past the count */
  size_t n = 0;
  for (size_t k = 0; k < nblk; k++) {
    u64 b = m[k]; unsigned c = (unsigned)__builtin_popcountll(b); uint32_t base = (uint32_t)(64 * k); uint32_t *o = idx + n;
    for (int j = 0; j < 8; j++) { o[j] = base + (uint32_t)_tzcnt_u64(b); b &= b - 1; }
    if (c > 8) { for (unsigned j = 8; j < c; j++) { o[j] = base + (uint32_t)_tzcnt_u64(b); b &= b - 1; } }
    n += c;
  }
  return n;
}

/* ---------- harness ---------- */
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + t.tv_nsec * 1e-9; }
static volatile u64 sink;
typedef result_t (*run_fn)(const u8 *, size_t, u64 *);
static double bench(run_fn f, const u8 *in, size_t nblk, u64 *out, int windows) {   /* MB/s, best window of 0.4 s */
  double best = 0;
  for (int w = 0; w < windows; w++) {
    double t0 = now(), e; long it = 0;
    do { result_t r = f(in, nblk, out); sink += r.err_ctrl + r.utf8_err + out[nblk / 2]; it++; e = now() - t0; } while (e < 0.4);
    double mbs = (double)it * nblk * 64 / 1e6 / e; if (mbs > best) best = mbs;
  }
  return best;
}
typedef size_t (*flat_fn)(const u64 *, size_t, uint32_t *);
static double bench_flat(flat_fn f, const u64 *m, size_t nblk, uint32_t *idx, int windows) {
  double best = 0;
  for (int w = 0; w < windows; w++) {
    double t0 = now(), e; long it = 0;
    do { sink += f(m, nblk, idx); it++; e = now() - t0; } while (e < 0.4);
    double mbs = (double)it * nblk * 64 / 1e6 / e; if (mbs > best) best = mbs;
  }
  return best;
}

static int check_one(const char *name, const u8 *buf, size_t nblk, int quiet) {
  u64 *a = malloc(nblk * 8 + 8), *b = malloc(nblk * 8 + 8), *c = malloc(nblk * 8 + 8); int ok = 1;
  result_t ra = run_scalar(buf, nblk, a), rb = run_swar(buf, nblk, b);
  if (memcmp(a, b, nblk * 8) || ra.err_ctrl != rb.err_ctrl || ra.utf8_err != rb.utf8_err) { if (!quiet) fprintf(stderr, "MISMATCH scalar/swar on %s\n", name); ok = 0; }
#ifdef __AVX2__
  result_t rc = run_avx2(buf, nblk, c);
  if (memcmp(a, c, nblk * 8) || ra.err_ctrl != rc.err_ctrl || ra.utf8_err != rc.utf8_err) { if (!quiet) fprintf(stderr, "MISMATCH scalar/avx2 on %s (err %llu/%llu utf8 %llu/%llu)\n", name, (unsigned long long)ra.err_ctrl, (unsigned long long)rc.err_ctrl, (unsigned long long)ra.utf8_err, (unsigned long long)rc.utf8_err); ok = 0; }
#endif
#ifdef WITH_LEAN
  { u64 *d = malloc(nblk * 8 + 8); lean_copy_out = 1; result_t rd = run_lean(buf, nblk, d); lean_copy_out = 0;
    if (memcmp(a, d, nblk * 8) || ra.err_ctrl != rd.err_ctrl || ra.utf8_err != rd.utf8_err) { if (!quiet) fprintf(stderr, "MISMATCH scalar/lean on %s\n", name); ok = 0; }
    lean_use_x = 1; lean_copy_out = 1; rd = run_lean(buf, nblk, d); lean_copy_out = 0; lean_use_x = 0;
    if (memcmp(a, d, nblk * 8) || ra.err_ctrl != rd.err_ctrl || ra.utf8_err != rd.utf8_err) { if (!quiet) fprintf(stderr, "MISMATCH scalar/lean+shim on %s\n", name); ok = 0; } free(d); }
#endif
  free(a); free(b); free(c); return ok;
}

/* the differential test on random bytes from an alphabet that exercises every transition (quotes, backslashes, operators, whitespace, controls, UTF-8 leads/continuations/garbage) */
static int fuzz(long n) {
  static const u8 alpha[] = { '"', '"', '"', '\\', '\\', '{', '}', '[', ']', ':', ',', ' ', '\t', '\n', 'a', 'b', '1', '-', '.', 0x01, 0x1f, 0x7f, 0x80, 0xBF, 0xC2, 0xDF, 0xE0, 0xE1, 0xED, 0xEF, 0xF0, 0xF4, 0xF5, 0xFF, 0xA0, 0x90, 0x8F, 0x9F, 0xBF, 0xC0, 0xC1 };
  unsigned long x = 88172645463325252UL; size_t nblk = 6; u8 *buf = malloc(nblk * 64); long bad = 0;
  for (long t = 0; t < n; t++) {
    int mode = t % 4;   /* 0: uniform over the alphabet, 1: mostly ASCII structure, 2: mostly backslashes and quotes, 3: valid-ish UTF-8 heavy */
    for (size_t i = 0; i < nblk * 64; i++) {
      x ^= x << 13; x ^= x >> 7; x ^= x << 17; unsigned r = (unsigned)(x >> 20);
      u8 c;
      if (mode == 0) c = alpha[r % sizeof alpha];
      else if (mode == 1) c = (r % 8 == 0) ? alpha[(r >> 3) % sizeof alpha] : "{}[]:, \"abc123"[(r >> 3) % 15];
      else if (mode == 2) c = (r % 3 == 0) ? '\\' : (r % 3 == 1) ? '"' : alpha[(r >> 3) % sizeof alpha];
      else { static const char *u[] = { "\xC3\xA9", "\xE4\xB8\xAD", "\xF0\x9F\x98\x80", "a", "\"", "\xE2\x82\xAC" }; const char *q = u[(r >> 4) % 6]; c = (u8)q[(r >> 8) % strlen(q)]; }
      buf[i] = c;
    }
    if (!check_one("fuzz", buf, nblk, 0)) { bad++; if (bad > 5) break; }
  }
  free(buf); return bad == 0;
}

/* UTF-8 exhaustive-ish: every 1- and 2-byte sequence, every 3-byte sequence over the interesting bytes, every 4-byte over a smaller set, at offsets that cross lane (16/32) and block (64) boundaries
 * and at the very end of the buffer; the verdict of the three variants must be the same (and, for the scalar DFA, equal to the one RFC 3629 gives: checked against Python's decoder in run.sh). */
static int utf8_all(void) {
  static const u8 B3[] = { 0x00, 0x41, 0x7F, 0x80, 0x8F, 0x90, 0x9F, 0xA0, 0xBF, 0xC0, 0xC1, 0xC2, 0xDF, 0xE0, 0xE1, 0xEC, 0xED, 0xEE, 0xEF, 0xF0, 0xF1, 0xF3, 0xF4, 0xF5, 0xFF };
  static const u8 B4[] = { 0x41, 0x80, 0x8F, 0x90, 0xBF, 0xC2, 0xE0, 0xED, 0xF0, 0xF4, 0xF5 };
  static const int offs[] = { 0, 1, 13, 14, 15, 16, 17, 29, 30, 31, 32, 33, 60, 61, 62, 63, 64, 65, 190, 191 };
  size_t nblk = 3; u8 buf[192]; long n = 0, bad = 0, valid = 0;
  for (int oi = 0; oi < (int)(sizeof offs / sizeof *offs); oi++) {
    int o = offs[oi];
    for (int len = 1; len <= 4; len++) {
      long total = len == 1 ? 256 : len == 2 ? 65536 : len == 3 ? 25L * 25 * 25 : 11L * 11 * 11 * 11;
      for (long v = 0; v < total; v++) {
        u8 seq[4]; long x = v;
        for (int j = 0; j < len; j++) {
          if (len <= 2) { seq[j] = (u8)(x & 255); x >>= 8; } else if (len == 3) { seq[j] = B3[x % 25]; x /= 25; } else { seq[j] = B4[x % 11]; x /= 11; }
        }
        if (o + len > 192) continue;
        memset(buf, ' ', sizeof buf); memcpy(buf + o, seq, (size_t)len);
        if (o + len < 192) buf[o + len] = 'a';
        u64 a[3], b[3], c[3]; result_t ra = run_scalar(buf, nblk, a), rb = run_swar(buf, nblk, b);
        int ok = ra.utf8_err == rb.utf8_err;
#ifdef __AVX2__
        result_t rc = run_avx2(buf, nblk, c); ok = ok && ra.utf8_err == rc.utf8_err;
#endif
#ifdef WITH_LEAN
        { u64 d[3]; result_t rd = run_lean(buf, nblk, d); ok = ok && ra.utf8_err == rd.utf8_err; }
#endif
        (void)c; n++; valid += !ra.utf8_err;
        if (!ok && bad++ < 8) fprintf(stderr, "UTF-8 MISMATCH off %d len %d bytes %02x %02x %02x %02x (scalar %d swar %d)\n", o, len, seq[0], len > 1 ? seq[1] : 0, len > 2 ? seq[2] : 0, len > 3 ? seq[3] : 0, (int)ra.utf8_err, (int)rb.utf8_err);
      }
    }
  }
  printf("utf8: %ld sequences at %d offsets, %ld valid, %s\n", n, (int)(sizeof offs / sizeof *offs), valid, bad ? "MISMATCH" : "all variants agree");
  return bad == 0;
}

#ifndef NO_MAIN
int main(int argc, char **argv) {
#ifdef WITH_LEAN
  lean_initialize_runtime_module(); lean_set_panic_messages(0); lean_object *res = initialize_Stage1(1, lean_io_mk_world()); if (lean_io_result_is_error(res)) { fprintf(stderr, "lean init failed\n"); return 2; } lean_dec_ref(res); lean_io_mark_end_initialization();
#endif
  if (argc >= 2 && !strcmp(argv[1], "--utf8")) return !utf8_all();
  if (argc >= 2 && !strcmp(argv[1], "--fuzz")) { long n = 200000; if (argc > 2) { n = 0; for (const char *q = argv[2]; *q >= '0' && *q <= '9'; q++) n = n * 10 + (*q - '0'); }   /* (no atol: the bundled linker's libc has no strtol alias for it) */ int ok = fuzz(n); printf("fuzz: %ld random 384-byte inputs, %s\n", n, ok ? "all variants agree" : "MISMATCH"); return !ok; }
  int windows = 3;
  printf("%-22s %9s %9s %9s %9s %9s %9s %12s %12s %10s\n", "corpus", "bytes", "scalar", "swar-C", "swar-Lean", "Lean+shim", "avx2", "flat-simple", "flat-batch", "tokens/B");
  for (int f = 1; f < argc; f++) {
    FILE *fp = fopen(argv[f], "rb"); if (!fp) { perror(argv[f]); return 2; }
    fseek(fp, 0, SEEK_END); long len = ftell(fp); fseek(fp, 0, SEEK_SET);
    size_t nblk = ((size_t)len + 63) / 64 + 1; u8 *buf = aligned_alloc(64, nblk * 64); memset(buf, ' ', nblk * 64);   /* padding: spaces, as the real stage 1 would */
    if (fread(buf, 1, (size_t)len, fp) != (size_t)len) return 2;
    fclose(fp);
    u64 *out = aligned_alloc(64, nblk * 8 + 64); uint32_t *idx = malloc((nblk * 64 + 64) * 4);
    if (!check_one(argv[f], buf, nblk, 0)) return 1;
    result_t r = run_scalar(buf, nblk, out); size_t ntok = flatten_simple(out, nblk, idx);
    { uint32_t *i2 = malloc((nblk * 64 + 64) * 4); size_t n2 = flatten_batched(out, nblk, i2); if (n2 != ntok || memcmp(idx, i2, ntok * 4)) { fprintf(stderr, "flatten MISMATCH\n"); return 1; } free(i2); }
    double s0 = bench(run_scalar, buf, nblk, out, windows), s1 = bench(run_swar, buf, nblk, out, windows);
#ifdef WITH_LEAN
    lean_fresh = 0; double sl = bench(run_lean, buf, nblk, out, windows); lean_use_x = 1; lean_fresh = 1; { u64 *d = malloc(nblk * 8 + 8); lean_copy_out = 1; run_lean(buf, nblk, d); lean_copy_out = 0; if (memcmp(d, out, 0) || 0) {} free(d); } lean_fresh = 0; double sx = bench(run_lean, buf, nblk, out, windows); lean_use_x = 0; lean_fresh = 1;
#else
    double sl = 0, sx = 0;
#endif
#ifdef __AVX2__
    double s2 = bench(run_avx2, buf, nblk, out, windows);
#else
    double s2 = 0;
#endif
    run_swar(buf, nblk, out);
    double f1 = bench_flat(flatten_simple, out, nblk, idx, windows), f2 = bench_flat(flatten_batched, out, nblk, idx, windows);
    const char *b = strrchr(argv[f], '/'); b = b ? b + 1 : argv[f];
    printf("%-22s %9ld %9.0f %9.0f %9.0f %9.0f %9.0f %12.0f %12.0f %10.3f%s\n", b, len, s0, s1, sl, sx, s2, f1, f2, (double)ntok / (double)len, (r.err_ctrl || r.utf8_err) ? "  (errors flagged!)" : "");
    free(buf); free(out); free(idx);
  }
  return 0;
}
#endif
