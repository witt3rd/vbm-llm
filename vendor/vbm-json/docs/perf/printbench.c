/* docs/perf/printbench.c: the measurement of the printer through the C ABI. NOT part of the library, not built by any gate (the harness of docs/perf/prof.c for printing). The document is parsed once; what is timed is
 * vbm_json_print_tape of that tape (the whole call: the copy of the tape into the runtime, the print, the hand-out, the free).
 *   printbench FILE bench SECONDS      -> output MB/s (median of 5 windows) and the same in MB/s of the INPUT document's size
 *   printbench FILE pc ITERS           -> "instructions-per-output-byte cycles-per-output-byte" (user, P core; the minimum of ITERS calls)
 *   printbench FILE escape SECONDS     -> MB/s of vbm_json_escape_string over the document's own bytes as text (valid UTF-8 only; else it reports the refusal)
 *   printbench FILE sample SECONDS OUT -> SIGPROF sampler as prof.c (resolve with docs/perf/resolve.py)
 * Build: leanc -O2 -isystem /usr/include -I include -o printbench docs/perf/printbench.c abi/vbm_json.c .lake/build/lib/libvbm_x2djson_LeanJson.a */
#define _GNU_SOURCE
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <unistd.h>
#include <time.h>
#include <sys/time.h>
#include <sys/syscall.h>
#include <sys/ioctl.h>
#include <ucontext.h>
#include <linux/perf_event.h>
#include "vbm_json.h"
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + t.tv_nsec / 1e9; }
static int cmp(const void *a, const void *b) { double x = *(const double *)a, y = *(const double *)b; return (x > y) - (x < y); }
static int pe(unsigned type, uint64_t cfg) {
  struct perf_event_attr a; memset(&a, 0, sizeof a); a.size = sizeof a; a.type = PERF_TYPE_HARDWARE; a.config = ((uint64_t)type << 32) | cfg;
  a.exclude_kernel = 1; a.exclude_hv = 1; a.disabled = 1;
  return syscall(SYS_perf_event_open, &a, 0, -1, -1, 0);
}
static uintptr_t *samples; static size_t nsamp, capsamp;
static void on_prof(int sig, siginfo_t *si, void *uc) { (void)sig; (void)si; if (nsamp < capsamp) samples[nsamp++] = ((ucontext_t *)uc)->uc_mcontext.gregs[REG_RIP]; }
int main(int argc, char **argv) {
  if (argc < 3) return 2;
  FILE *f = fopen(argv[1], "rb"); if (!f) return 2; fseek(f, 0, SEEK_END); long n = ftell(f); rewind(f);
  uint8_t *b = malloc(n); if (fread(b, 1, n, f) != (size_t)n) return 2; fclose(f);
  vbm_json_tape t; if (vbm_json_parse(b, n, NULL, &t) != VBM_JSON_OK) { fprintf(stderr, "parse failed\n"); return 3; }
  vbm_json_bytes o; if (vbm_json_print_tape(&t, NULL, &o) != VBM_JSON_OK) { fprintf(stderr, "print failed\n"); return 3; }
  size_t on = o.len; vbm_json_bytes_free(&o);
  double secs = argc > 3 ? atof(argv[3]) : 3;
  if (!strcmp(argv[2], "bench")) {
    double r[5];
    for (int w = 0; w < 5; w++) { long it = 0; double a = now(), e; do { vbm_json_print_tape(&t, NULL, &o); vbm_json_bytes_free(&o); it++; e = now() - a; } while (e < secs / 5); r[w] = it * (double)on / 1e6 / e; }
    qsort(r, 5, sizeof *r, cmp); printf("%.1f %.1f %zu\n", r[2], r[4], on); return 0;   /* median and best window, MB/s of output; the output size */
  }
  if (!strcmp(argv[2], "escape")) {
    double r[5]; vbm_json_bytes e0;
    if (vbm_json_escape_string(b, n, NULL, &e0) != VBM_JSON_OK) { printf("refused (not valid UTF-8)\n"); return 0; }
    vbm_json_bytes_free(&e0);
    for (int w = 0; w < 5; w++) { long it = 0; double a = now(), e; do { vbm_json_escape_string(b, n, NULL, &o); vbm_json_bytes_free(&o); it++; e = now() - a; } while (e < secs / 5); r[w] = it * (double)n / 1e6 / e; }
    qsort(r, 5, sizeof *r, cmp); printf("%.1f %.1f\n", r[2], r[4]); return 0;
  }
  if (!strcmp(argv[2], "pc")) {
    unsigned type = 4; { FILE *tf = fopen("/sys/bus/event_source/devices/cpu_core/type", "r"); if (tf) { char buf[16] = {0}; if (fgets(buf, sizeof buf, tf)) { type = 0; for (char *q = buf; *q >= 48 && *q <= 57; q++) type = type * 10 + (*q - 48); } fclose(tf); } }
    int fi = pe(type, PERF_COUNT_HW_INSTRUCTIONS), fc = pe(type, PERF_COUNT_HW_CPU_CYCLES);
    if (fi < 0 || fc < 0) { perror("perf_event_open"); return 3; }
    int iters = 0; for (const char *q = argc > 3 ? argv[3] : "15"; *q; q++) iters = iters * 10 + (*q - 48); uint64_t bi = ~0ull, bc = ~0ull;
    for (int w = 0; w < 3; w++) { vbm_json_print_tape(&t, NULL, &o); vbm_json_bytes_free(&o); }
    for (int r = 0; r < iters; r++) {
      ioctl(fi, PERF_EVENT_IOC_RESET, 0); ioctl(fc, PERF_EVENT_IOC_RESET, 0); ioctl(fi, PERF_EVENT_IOC_ENABLE, 0); ioctl(fc, PERF_EVENT_IOC_ENABLE, 0);
      vbm_json_print_tape(&t, NULL, &o); vbm_json_bytes_free(&o);
      ioctl(fi, PERF_EVENT_IOC_DISABLE, 0); ioctl(fc, PERF_EVENT_IOC_DISABLE, 0);
      uint64_t i = 0, c = 0; if (read(fi, &i, 8) != 8 || read(fc, &c, 8) != 8) return 4;
      if (i < bi) bi = i; if (c < bc) bc = c;
    }
    printf("%.3f %.3f\n", (double)bi / on, (double)bc / on); return 0;
  }
  if (!strcmp(argv[2], "sample")) {
    capsamp = 1u << 22; samples = malloc(capsamp * sizeof *samples);
    struct sigaction sa; memset(&sa, 0, sizeof sa); sa.sa_sigaction = on_prof; sa.sa_flags = SA_SIGINFO | SA_RESTART; sigaction(SIGPROF, &sa, NULL);
    struct itimerval tv = { {0, 1000}, {0, 1000} }; setitimer(ITIMER_PROF, &tv, NULL);
    double a = now(); while (now() - a < secs) { vbm_json_print_tape(&t, NULL, &o); vbm_json_bytes_free(&o); }
    memset(&tv, 0, sizeof tv); setitimer(ITIMER_PROF, &tv, NULL);
    FILE *of = fopen(argv[4], "w"); fprintf(of, "%lx\n", (unsigned long)(uintptr_t)&main);
    for (size_t i = 0; i < nsamp; i++) fprintf(of, "%lx\n", (unsigned long)samples[i]); fclose(of); return 0;
  }
  return 2;
}
