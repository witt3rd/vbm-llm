/* docs/perf/pc.c: instructions retired and user cycles per input byte of one parse through the C ABI (perf_event_open, user mode; the minimum over ITERS parses after 3 warm-ups). NOT part of the library, not built by any gate.
 *   pc FILE [ITERS]  -> prints "instr/byte cycles/byte". Build as docs/perf/prof.c is built (docs/perf/run.sh); pin to one core with taskset. */
#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <unistd.h>
#include <sys/syscall.h>
#include <sys/ioctl.h>
#include <linux/perf_event.h>
#include <lean/lean.h>
#include "vbm_json.h"
static int pe(unsigned type, uint64_t cfg) {
  struct perf_event_attr a; memset(&a, 0, sizeof a); a.size = sizeof a; a.type = PERF_TYPE_HARDWARE; a.config = ((uint64_t)type << 32) | cfg;
  a.exclude_kernel = 1; a.exclude_hv = 1; a.disabled = 1;
  return syscall(SYS_perf_event_open, &a, 0, -1, -1, 0);
}
int main(int argc, char **argv) {
  FILE *f = fopen(argv[1], "rb"); fseek(f, 0, SEEK_END); long n = ftell(f); rewind(f);
  uint8_t *b = malloc(n); if (fread(b, 1, n, f) != (size_t)n) return 2; fclose(f);
  int iters = 20; if (argc > 2) { iters = 0; for (const char *q = argv[2]; *q; q++) iters = iters * 10 + (*q - 48); }
  unsigned type = 4; { FILE *t = fopen("/sys/bus/event_source/devices/cpu_core/type", "r"); if (t) { char buf[16] = {0}; if (fgets(buf, sizeof buf, t)) { type = 0; for (char *q = buf; *q >= 48 && *q <= 57; q++) type = type * 10 + (*q - 48); } fclose(t); } }
  int fi = pe(type, PERF_COUNT_HW_INSTRUCTIONS), fc = pe(type, PERF_COUNT_HW_CPU_CYCLES);
  if (fi < 0 || fc < 0) { perror("perf_event_open"); return 3; }
  vbm_json_tape t; for (int w = 0; w < 3; w++) { vbm_json_parse(b, n, NULL, &t); vbm_json_free(&t); }
  uint64_t bi = ~0ull, bc = ~0ull;
  for (int r = 0; r < iters; r++) {
    ioctl(fi, PERF_EVENT_IOC_RESET, 0); ioctl(fc, PERF_EVENT_IOC_RESET, 0); ioctl(fi, PERF_EVENT_IOC_ENABLE, 0); ioctl(fc, PERF_EVENT_IOC_ENABLE, 0);
    vbm_json_parse(b, n, NULL, &t); vbm_json_free(&t);
    ioctl(fi, PERF_EVENT_IOC_DISABLE, 0); ioctl(fc, PERF_EVENT_IOC_DISABLE, 0);
    uint64_t i = 0, c = 0; if (read(fi, &i, 8) != 8 || read(fc, &c, 8) != 8) return 4;
    if (i < bi) bi = i; if (c < bc) bc = c;
  }
  printf("%.3f %.3f\n", (double)bi / n, (double)bc / n);
  return 0;
}
