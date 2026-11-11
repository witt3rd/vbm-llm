/* docs/perf/prof.c: the profiling harness of docs/perf/profile.md. NOT part of the library, not built by any gate. Calls vbm_json_parse through the C ABI on a file.
 *   prof FILE bench SECONDS         -> prints "MB/s" (median of 5 timed windows)
 *   prof FILE sample SECONDS OUT    -> SIGPROF sampler (ITIMER_PROF, 1 kHz): writes one instruction pointer per line (hex) to OUT; resolve with nm -n (docs/perf/resolve.py)
 *   prof FILE parseonly SECONDS    -> MB/s of parseFast alone (Value built and freed; no tape)  [scratch build only]
 *   prof FILE shim SECONDS         -> MB/s of the shim's own byte movement (copy in, copy out, free), no parsing
 *   prof FILE count                 -> allocation counts for ONE parse (needs the link flags of docs/perf/run.sh: --wrap on the allocator entry points)
 * Build and run: docs/perf/run.sh. */
#define _GNU_SOURCE
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/time.h>
#include <time.h>
#include <ucontext.h>
#include <stdint.h>
#include <lean/lean.h>
#include "vbm_json.h"

/* only in the scratch build of docs/perf/run.sh, which appends the export prof_parse_only (parseFast and nothing else) to a COPY of LeanJson/Tape.lean; the repository has no such symbol */
extern uint64_t prof_parse_only(lean_object *) __attribute__((weak));

/* allocation counters, fed by the linker's --wrap of the entry points */
unsigned long cnt_obj, cnt_obj_bytes, cnt_small, cnt_small_bytes, cnt_cold, cnt_mi, cnt_mi_bytes, cnt_free;
#ifdef COUNT_WRAP
extern void *__real_lean_alloc_object(size_t);
extern void *__real_lean_alloc_small_object_core(unsigned);
extern void __real_lean_dec_ref_cold(void *);
void *__wrap_lean_alloc_object(size_t n) { cnt_obj++; cnt_obj_bytes += n; return __real_lean_alloc_object(n); }
void *__wrap_lean_alloc_small_object_core(unsigned n) { cnt_small++; cnt_small_bytes += n; return __real_lean_alloc_small_object_core(n); }
void __wrap_lean_dec_ref_cold(void *o) { cnt_cold++; __real_lean_dec_ref_cold(o); }
#endif

static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + t.tv_nsec / 1e9; }
static uintptr_t *samples; static size_t nsamp, capsamp;
static void on_prof(int sig, siginfo_t *si, void *uc) { (void)sig; (void)si; if (nsamp < capsamp) samples[nsamp++] = ((ucontext_t *)uc)->uc_mcontext.gregs[REG_RIP]; }
static int cmp(const void *a, const void *b) { double x = *(const double *)a, y = *(const double *)b; return (x > y) - (x < y); }

int main(int argc, char **argv) {
  if (argc < 3) return 2;
  FILE *f = fopen(argv[1], "rb"); if (!f) return 2; fseek(f, 0, SEEK_END); long n = ftell(f); rewind(f);
  uint8_t *b = malloc(n); if (fread(b, 1, n, f) != (size_t)n) return 2; fclose(f);
  vbm_json_tape t; if (vbm_json_parse(b, n, NULL, &t) != VBM_JSON_OK) { fprintf(stderr, "parse failed\n"); return 3; }   /* warm-up + runtime init */
  size_t nw = t.nwords, nt = t.ntext; vbm_json_free(&t);
  if (!strcmp(argv[2], "count")) {
    cnt_obj = cnt_obj_bytes = cnt_small = cnt_small_bytes = cnt_cold = 0;
    vbm_json_parse(b, n, NULL, &t); vbm_json_free(&t);
    printf("bytes %ld tape_words %zu text_bytes %zu | lean_alloc_object %lu (%lu B) | lean_alloc_small_object_core %lu (%lu B) | lean_dec_ref_cold %lu\n", n, nw, nt, cnt_obj, cnt_obj_bytes, cnt_small, cnt_small_bytes, cnt_cold);
    return 0;
  }
  double secs = argc > 3 ? atof(argv[3]) : 3;
  if (!strcmp(argv[2], "bench")) {
    double r[5];
    for (int w = 0; w < 5; w++) { long it = 0; double a = now(), e; do { vbm_json_parse(b, n, NULL, &t); vbm_json_free(&t); it++; e = now() - a; } while (e < secs / 5); r[w] = it * (double)n / 1e6 / e; }
    qsort(r, 5, sizeof *r, cmp); printf("%.1f\n", r[2]); return 0;
  }
  if (!strcmp(argv[2], "parseonly")) {
    if (!prof_parse_only) { fprintf(stderr, "no prof_parse_only in this build\n"); return 2; }
    double r[5];
    for (int w = 0; w < 5; w++) { long it = 0; double a = now(), e; do { lean_object *in = lean_alloc_sarray(1, n, n); memcpy(lean_sarray_cptr(in), b, n); prof_parse_only(in); it++; e = now() - a; } while (e < secs / 5); r[w] = it * (double)n / 1e6 / e; }
    qsort(r, 5, sizeof *r, cmp); printf("%.1f\n", r[2]); return 0;
  }
  if (!strcmp(argv[2], "shim")) {
    size_t tn = 24 + 8 * nw + nt; uint8_t *src = calloc(1, tn); double r[5];
    for (int w = 0; w < 5; w++) { long it = 0; double a = now(), e; do { lean_object *in = lean_alloc_sarray(1, n, n); memcpy(lean_sarray_cptr(in), b, n); lean_object *o = lean_alloc_sarray(1, tn, tn); memcpy(lean_sarray_cptr(o), src, tn); void *blk = malloc(tn); memcpy(blk, lean_sarray_cptr(o), tn); ((volatile char *)blk)[0] = 1; free(blk); lean_dec_ref(o); lean_dec_ref(in); it++; e = now() - a; } while (e < secs / 5); r[w] = it * (double)n / 1e6 / e; }
    qsort(r, 5, sizeof *r, cmp); printf("%.1f\n", r[2]); return 0;
  }
  if (!strcmp(argv[2], "sample")) {
    capsamp = 1u << 22; samples = malloc(capsamp * sizeof *samples);
    struct sigaction sa; memset(&sa, 0, sizeof sa); sa.sa_sigaction = on_prof; sa.sa_flags = SA_SIGINFO | SA_RESTART; sigaction(SIGPROF, &sa, NULL);
    struct itimerval tv = { {0, 1000}, {0, 1000} }; setitimer(ITIMER_PROF, &tv, NULL);
    double a = now(); while (now() - a < secs) { vbm_json_parse(b, n, NULL, &t); vbm_json_free(&t); }
    memset(&tv, 0, sizeof tv); setitimer(ITIMER_PROF, &tv, NULL);
    FILE *o = fopen(argv[4], "w"); fprintf(o, "%lx\n", (unsigned long)(uintptr_t)&main);   /* first line: where main is, so a PIE can be resolved */
    for (size_t i = 0; i < nsamp; i++) fprintf(o, "%lx\n", (unsigned long)samples[i]); fclose(o); return 0;
  }
  return 2;
}
