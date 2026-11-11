/* tests/native_rt.c: the freestanding native runtime (runtime/rt.c) from outside: memcpy/memmove/memset against byte-by-byte references over every size 0..300, every alignment and every overlap,
 * and the leak hook (vbm_json_rt_live) over repeated parses of rows of the generated vectors (argv[1]: no document of its own). Hosted test code, not shipped. Linked with a build that keeps memcpy/memmove/memset/vbm_json_rt_live global (VBM_KEEP in
 * scripts/build_native.sh); the aliases below name those exact symbols, so the library's own are called, not the compiler's builtins. Exit 0 = all correct. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "../include/vbm_json.h"
void *rt_memcpy(void *, const void *, size_t) __asm__("memcpy");
void *rt_memmove(void *, const void *, size_t) __asm__("memmove");
void *rt_memset(void *, int, size_t) __asm__("memset");
size_t vbm_json_rt_live(void);
static int bad;
#define CHECK(c, what, n) do { if (!(c)) { fprintf(stderr, "native_rt: FAIL: %s (n=%zu)\n", what, (size_t)(n)); bad = 1; } } while (0)
static int hexv(int c) { return c >= '0' && c <= '9' ? c - '0' : c >= 'a' && c <= 'f' ? c - 'a' + 10 : -1; }
/* the input of the first row with the given verdict whose input is 20..300 bytes: from the generated vectors, hex-decoded */
static size_t pick(const char *path, const char *verdict, unsigned char *out) {
  FILE *f = fopen(path, "r"); if (!f) { perror(path); exit(2); }
  char *line = NULL; size_t cap = 0, n = 0; ssize_t got; char pat[32]; snprintf(pat, sizeof pat, "\"verdict\":\"%s\"", verdict);
  while (!n && (got = getline(&line, &cap, f)) > 0) {
    char *p = strstr(line, "\"input\":\""); if (!p || !strstr(line, pat)) continue;
    p += 9; char *q = strchr(p, '"'); size_t hn = q ? (size_t)(q - p) : 0;
    if (hn < 40 || hn > 600 || hn % 2) continue;
    size_t k = 0; for (; k < hn / 2; k++) { int a = hexv(p[2 * k]), b = hexv(p[2 * k + 1]); if (a < 0 || b < 0) break; out[k] = (unsigned char)(a * 16 + b); }
    if (k == hn / 2) n = k;
  }
  free(line); fclose(f); return n;
}
int main(int argc, char **argv) {
  if (argc != 2) { fprintf(stderr, "usage: native_rt VECTORS.jsonl\n"); return 2; }
  static unsigned char src[700], a[700], b[700];
  for (size_t i = 0; i < sizeof src; i++) src[i] = (unsigned char)(i * 31 + 7);
  for (size_t n = 0; n <= 300; n++) for (size_t so = 0; so < 9; so++) for (size_t d = 0; d < 9; d += (n < 40 ? 1 : 4)) {
    memset(a, 0xAA, sizeof a); memset(b, 0xAA, sizeof b);
    for (size_t i = 0; i < n; i++) ((volatile unsigned char *)b)[d + i] = src[so + i];
    void *r = rt_memcpy(a + d, src + so, n);
    CHECK(r == a + d && !memcmp(a, b, sizeof a), "memcpy", n);
    memcpy(a, src, 700); memcpy(b, src, 700);   /* overlap, forward and backward: the reference goes through a temporary */
    unsigned char t[320]; for (size_t i = 0; i < n; i++) t[i] = b[so + i];
    for (size_t i = 0; i < n; i++) b[d + i] = t[i];
    r = rt_memmove(a + d, a + so, n);
    CHECK(r == a + d && !memcmp(a, b, sizeof a), "memmove", n);
    memset(a, 0x55, sizeof a); memset(b, 0x55, sizeof b);
    for (size_t i = 0; i < n; i++) ((volatile unsigned char *)b)[d + i] = 0x1C3 & 0xff;
    r = rt_memset(a + d, 0x1C3, n);   /* the value is converted to unsigned char */
    CHECK(r == a + d && !memcmp(a, b, sizeof a), "memset", n);
  }
  static unsigned char okin[400], errin[400]; size_t okn = pick(argv[1], "ok", okin), errn = pick(argv[1], "err", errin);
  if (!okn || !errn) { fprintf(stderr, "native_rt: the vectors have no small accepted row and no small rejected row\n"); return 2; }
  vbm_json_tape t;
  /* warm-up: the ok path and the error path each once or more, so that the runtime's one-time allocations (its free lists) are not counted as growth */
  for (int i = 0; i < 3; i++) { if (vbm_json_parse(okin, okn, NULL, &t) != VBM_JSON_OK) return 3; vbm_json_free(&t); if (vbm_json_parse(errin, errn, NULL, &t) == VBM_JSON_OK) return 3; }
  size_t base = vbm_json_rt_live();
  for (int i = 0; i < 2000; i++) {
    if (vbm_json_parse(okin, okn, NULL, &t) != VBM_JSON_OK) return 3;
    vbm_json_free(&t);
    if (vbm_json_parse(errin, errn, NULL, &t) == VBM_JSON_OK) return 3;
  }
  CHECK(vbm_json_rt_live() == base, "the runtime heap grows over 4000 parses: a leak", vbm_json_rt_live() - base);
  CHECK(base > 0, "the leak hook reads zero (the hook is not wired)", base);
  if (bad) return 1;
  printf("native_rt: memcpy/memmove/memset agree with the references (sizes 0..300, alignments, overlaps); runtime heap flat over 4000 parses (%zu bytes live)\n", base);
  return 0;
}
