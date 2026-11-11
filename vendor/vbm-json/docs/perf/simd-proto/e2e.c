/* docs/perf/simd-proto/e2e.c: PROTOTYPE of the whole two-stage pipeline of docs/perf/simd-plan.md, in C, to bound what the verified version can reach. NOT part of the library, not a gate.
 *   stage 1  classify.c's AVX2 kernel: input -> per-block structural masks (+ the two sticky errors),
 *   flatten  masks -> u32 index of token starts,
 *   stage 2  walks the index and writes the SAME tape the library's `vbm_json_parse` returns (docs/perf/simd-plan.md section 6): a grammar-checking state machine over the tokens, strings copied
 *            from the input (escapes decoded), numbers scanned and copied in canonical form. Any irregularity (a stage-1 error flag, a grammar error, anything) returns "fall back": the real design
 *            then runs the scalar parser, which produces the exact error word; here the harness only counts that it did not happen on the six corpora.
 * The output is checked word for word against the library's tape on every corpus before anything is timed. Build and run: run_e2e.sh. */
#define NO_MAIN
#include "classify.c"
#include <stdint.h>
#include "vbm_json.h"

typedef struct { uint32_t at, count; uint8_t kind; } frame_t;
#define MAXDEPTH 512

static inline int is_delim(u8 c) { return c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == ',' || c == ']' || c == '}' || c == ':' || c == '"' || c == '{' || c == '['; }
static inline int is_digit(u8 c) { return (unsigned)(c - '0') < 10; }

/* the end of the number at p (the grammar of LeanJson.scanNum), or 0 */
static inline size_t scan_num(const u8 *b, size_t p) {
  size_t i = p; if (b[i] == '-') i++;
  if (b[i] == '0') i++; else if ((unsigned)(b[i] - '1') < 9) { i++; while (is_digit(b[i])) i++; } else return 0;
  if (b[i] == '.') { i++; if (!is_digit(b[i])) return 0; while (is_digit(b[i])) i++; }
  if (b[i] == 'e' || b[i] == 'E') { i++; if (b[i] == '+' || b[i] == '-') i++; if (!is_digit(b[i])) return 0; while (is_digit(b[i])) i++; }
  return i;
}
static inline int hexv(u8 c) { if (is_digit(c)) return c - '0'; c |= 0x20; return (c >= 'a' && c <= 'f') ? c - 'a' + 10 : -1; }
static inline int hex4(const u8 *p) { int a = hexv(p[0]), b = hexv(p[1]), c = hexv(p[2]), d = hexv(p[3]); return (a | b | c | d) < 0 ? -1 : (a << 12 | b << 8 | c << 4 | d); }
/* the string between the quotes at q0 and q1 (exclusive), unescaped, appended at `out`; returns the new end, or NULL */
static inline u8 *copy_string(const u8 *b, size_t q0, size_t q1, u8 *out) {
  const u8 *s = b + q0 + 1, *e = b + q1;
  const u8 *bs = s; while (bs + 8 <= e) { u64 w = ld64(bs); if (zl(w ^ REP('\\'))) break; memcpy(out + (bs - s), bs, 8); bs += 8; }
  while (bs < e && *bs != '\\') { out[bs - s] = *bs; bs++; }
  out += bs - s; s = bs;
  if (s == e) return out;
  while (s < e) {   /* slow path: this string has an escape */
    if (*s != '\\') { *out++ = *s++; continue; }
    u8 c = s[1]; s += 2;
    switch (c) {
      case '"': *out++ = '"'; break; case '\\': *out++ = '\\'; break; case '/': *out++ = '/'; break; case 'b': *out++ = 8; break; case 'f': *out++ = 12; break;
      case 'n': *out++ = 10; break; case 'r': *out++ = 13; break; case 't': *out++ = 9; break;
      case 'u': {
        int n = hex4(s); if (n < 0) return NULL; s += 4;
        if (n >= 0xD800 && n < 0xE000) {
          if (n >= 0xDC00 || s[0] != '\\' || s[1] != 'u') return NULL;
          int lo = hex4(s + 2); if (lo < 0xDC00 || lo >= 0xE000) return NULL; s += 6;
          n = 0x10000 + ((n - 0xD800) << 10) + (lo - 0xDC00);
        }
        if (n < 0x80) *out++ = (u8)n;
        else if (n < 0x800) { *out++ = (u8)(0xC0 | n >> 6); *out++ = (u8)(0x80 | (n & 0x3F)); }
        else if (n < 0x10000) { *out++ = (u8)(0xE0 | n >> 12); *out++ = (u8)(0x80 | ((n >> 6) & 0x3F)); *out++ = (u8)(0x80 | (n & 0x3F)); }
        else { *out++ = (u8)(0xF0 | n >> 18); *out++ = (u8)(0x80 | ((n >> 12) & 0x3F)); *out++ = (u8)(0x80 | ((n >> 6) & 0x3F)); *out++ = (u8)(0x80 | (n & 0x3F)); }
        break; }
      default: return NULL;
    }
  }
  return out;
}

typedef struct { u64 *tape; u8 *text; size_t nw, nt; } tape_t;
#define NODE(k, len, aux) do { tp[0] = (u64)(k) | (u64)(len) << 8; tp[1] = (aux); tp += 2; } while (0)

/* returns 1 and fills `out` (tape/text buffers are the caller's, big enough), or 0: fall back */
static int fail_line; static int fail(int l) { fail_line = l; return 0; }
static int stage2(const u8 *b, const uint32_t *idx, size_t ntok, tape_t *out) {
  u64 *tp = out->tape; u8 *xp = out->text, *x0 = xp; frame_t st[MAXDEPTH + 1]; int sp = 0; size_t t = 0;
  enum { VALUE, AFTER, KEY } state = VALUE;
  for (;;) {
    if (t >= ntok) { if (state == AFTER && sp == 0) break; return fail(__LINE__); }
    u8 c = b[idx[t]];
    if (state == KEY) {   /* a member's key and its colon */
      if (c != '"' || t + 1 >= ntok) return fail(__LINE__);
      size_t q0 = idx[t], q1 = idx[t + 1]; if (b[q1] != '"' || t + 2 >= ntok || b[idx[t + 2]] != ':') return fail(__LINE__);
      u8 *e = copy_string(b, q0, q1, xp); if (!e) return fail(__LINE__);
      NODE(4, e - xp, xp - x0); xp = e; t += 3; state = VALUE; continue;
    }
    if (state == VALUE) {
      switch (c) {
        case '{': case '[': {
          if (sp >= MAXDEPTH) return fail(__LINE__);
          u8 close = c == '{' ? '}' : ']'; t++;
          if (t < ntok && b[idx[t]] == close) { NODE(c == '{' ? 6 : 5, 0, 2); t++; state = AFTER; break; }
          st[sp].at = (uint32_t)(tp - out->tape); st[sp].count = 0; st[sp].kind = c == '{' ? 6 : 5; sp++;
          NODE(c == '{' ? 6 : 5, 0, 0); state = c == '{' ? KEY : VALUE; break; }
        case '"': {
          if (t + 1 >= ntok) return fail(__LINE__); size_t q0 = idx[t], q1 = idx[t + 1]; if (b[q1] != '"') return fail(__LINE__);
          u8 *e = copy_string(b, q0, q1, xp); if (!e) return fail(__LINE__);
          NODE(4, e - xp, xp - x0); xp = e; t += 2; state = AFTER; break; }
        case 't': { size_t p = idx[t]; if (memcmp(b + p, "true", 4) || !is_delim(b[p + 4])) return fail(__LINE__); NODE(2, 0, 0); t++; state = AFTER; break; }
        case 'f': { size_t p = idx[t]; if (memcmp(b + p, "false", 5) || !is_delim(b[p + 5])) return fail(__LINE__); NODE(1, 0, 0); t++; state = AFTER; break; }
        case 'n': { size_t p = idx[t]; if (memcmp(b + p, "null", 4) || !is_delim(b[p + 4])) return fail(__LINE__); NODE(0, 0, 0); t++; state = AFTER; break; }
        default: {
          size_t p = idx[t], j = scan_num(b, p); if (!j || !is_delim(b[j])) return fail(__LINE__);
          u8 *o = xp;
          for (size_t i = p; i < j; i++) { u8 d = b[i]; if (d == '+') continue; *o++ = d == 'E' ? 'e' : d; }
          NODE(3, o - xp, xp - x0); xp = o; t++; state = AFTER; break; }
      }
      continue;
    }
    /* AFTER: a value was completed */
    if (sp == 0) { if (t != ntok) return fail(__LINE__); break; }
    frame_t *f = &st[sp - 1];
    f->count++;
    if (c == ',') { t++; state = f->kind == 6 ? KEY : VALUE; continue; }
    if (c == (f->kind == 6 ? '}' : ']')) {
      u64 *h = out->tape + f->at; h[0] = (u64)f->kind | (u64)f->count << 8; h[1] = (u64)(tp - h); sp--; t++; continue;
    }
    return fail(__LINE__);
  }
  out->nw = (size_t)(tp - out->tape); out->nt = (size_t)(xp - x0); return 1;
}

/* the full pipeline over a padded buffer: returns the tape (in `out`), 0 = fall back. `s1` is the stage-1 variant (AVX2 intrinsics, or portable SWAR). */
static int pipeline(run_fn s1, const u8 *buf, size_t nblk, u64 *masks, uint32_t *idx, tape_t *out) {
  result_t r = s1(buf, nblk, masks);
  if (r.err_ctrl || r.utf8_err) return 0;
  size_t ntok = flatten_batched(masks, nblk, idx);
  return stage2(buf, idx, ntok, out);
}

static double window(int (*fn)(void *), void *arg, size_t len) {   /* best of 3 windows of 0.4 s, MB/s */
  double best = 0;
  for (int w = 0; w < 3; w++) { double t0 = now(), e; long it = 0; do { sink += fn(arg); it++; e = now() - t0; } while (e < 0.4); double m = (double)it * len / 1e6 / e; if (m > best) best = m; }
  return best;
}
typedef struct { const u8 *buf; size_t nblk, len; u64 *masks; uint32_t *idx; tape_t *out; size_t ntok; run_fn s1; u8 *res; } ctx_t;
static int f_stage1(void *a) { ctx_t *c = a; result_t r = c->s1(c->buf, c->nblk, c->masks); return (int)(r.err_ctrl + r.utf8_err); }
static int f_flatten(void *a) { ctx_t *c = a; return (int)flatten_batched(c->masks, c->nblk, c->idx); }
static int f_stage2(void *a) { ctx_t *c = a; return stage2(c->buf, c->idx, c->ntok, c->out); }
static int f_pipe(void *a) {   /* the pipeline and the final copy into one result block, as the library returns it */
  ctx_t *c = a; int ok = pipeline(c->s1, c->buf, c->nblk, c->masks, c->idx, c->out); u64 *hd = (u64 *)c->res; hd[0] = 0; hd[1] = c->out->nw; hd[2] = c->out->nt;
  memcpy(c->res + 24, c->out->tape, c->out->nw * 8); memcpy(c->res + 24 + c->out->nw * 8, c->out->text, c->out->nt); return ok;
}

int main(int argc, char **argv) {
  printf("%-22s %9s %9s %9s %9s %9s %10s %10s  %s\n", "corpus", "bytes", "s1-avx2", "s1-swar", "flatten", "stage2", "pipe-avx2", "pipe-swar", "tape == library tape");
  for (int f = 1; f < argc; f++) {
    FILE *fp = fopen(argv[f], "rb"); if (!fp) return 2; fseek(fp, 0, SEEK_END); long len = ftell(fp); fseek(fp, 0, SEEK_SET);
    size_t nblk = ((size_t)len + 63) / 64 + 1; u8 *buf = aligned_alloc(64, nblk * 64 + 64); memset(buf, ' ', nblk * 64 + 64);
    if (fread(buf, 1, (size_t)len, fp) != (size_t)len) return 2;
    fclose(fp);
    u64 *masks = aligned_alloc(64, nblk * 8 + 64); uint32_t *idx = malloc((nblk * 64 + 64) * 4);
    tape_t out; out.tape = malloc((size_t)(len + 64) * 8 * 2); out.text = malloc((size_t)len + 64);
    ctx_t c = { buf, nblk, (size_t)len, masks, idx, &out, 0, run_avx2, NULL };
    vbm_json_tape lt; int rc = vbm_json_parse(buf, (size_t)len, NULL, &lt);
    const char *verdict = "identical";
    for (int v = 0; v < 2; v++) {   /* both stage-1 variants must produce the library's tape */
      c.s1 = v ? run_swar : run_avx2;
      int ok = pipeline(c.s1, buf, nblk, masks, idx, &out);
      if (!ok) verdict = "STAGE 2 FELL BACK (not expected on a valid corpus)";
      else if (rc != VBM_JSON_OK) verdict = "library failed?";
      else if (lt.nwords != out.nw || lt.ntext != out.nt || memcmp(lt.words, out.tape, out.nw * 8) || memcmp(lt.text, out.text, out.nt)) verdict = "MISMATCH";
    }
    if (strcmp(verdict, "identical")) { fprintf(stderr, "%s: %s (stage 2 failed at e2e.c line %d)\n", argv[f], verdict, fail_line); return 1; }
    c.res = malloc(24 + out.nw * 8 + out.nt + 64);
    c.s1 = run_avx2; double a1 = window(f_stage1, &c, (size_t)len); c.s1 = run_swar; double a2 = window(f_stage1, &c, (size_t)len);
    c.s1 = run_avx2; f_stage1(&c); c.ntok = flatten_batched(masks, nblk, idx);
    double fl = window(f_flatten, &c, (size_t)len), s2 = window(f_stage2, &c, (size_t)len);
    c.s1 = run_avx2; double pa = window(f_pipe, &c, (size_t)len); c.s1 = run_swar; double ps = window(f_pipe, &c, (size_t)len);
    const char *bn = strrchr(argv[f], '/'); bn = bn ? bn + 1 : argv[f];
    printf("%-22s %9ld %9.0f %9.0f %9.0f %9.0f %10.0f %10.0f  %s\n", bn, len, a1, a2, fl, s2, pa, ps, verdict);
    vbm_json_free(&lt); free(buf); free(masks); free(idx); free(out.tape); free(out.text); free(c.res);
  }
  return 0;
}
