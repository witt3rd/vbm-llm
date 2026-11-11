#define _GNU_SOURCE
/* docs/perf/iprof.c (NOT part of the library, not built by any gate): iprof FILE OUT [PERIOD] [ITERS]: samples the instruction pointer every PERIOD retired user instructions (perf_event_open, overflow signal) over many parses; writes the format of prof.c sample. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <unistd.h>
#include <fcntl.h>
#include <signal.h>
#include <ucontext.h>
#include <sys/syscall.h>
#include <sys/ioctl.h>
#include <linux/perf_event.h>
#include <lean/lean.h>
static long num(const char *q) { long r = 0; for (; *q >= 48 && *q <= 57; q++) r = r * 10 + (*q - 48); return r; }
#include "vbm_json.h"
static uintptr_t *samples; static size_t nsamp, cap = 4000000;
static int fd;
static void on_sig(int sig, siginfo_t *si, void *uc) { (void)sig; (void)si; if (nsamp < cap) samples[nsamp++] = ((ucontext_t *)uc)->uc_mcontext.gregs[REG_RIP]; ioctl(fd, PERF_EVENT_IOC_REFRESH, 1); }
int main(int argc, char **argv) {
  FILE *f = fopen(argv[1], "rb"); fseek(f, 0, SEEK_END); long n = ftell(f); rewind(f);
  uint8_t *b = malloc(n); if (fread(b, 1, n, f) != (size_t)n) return 2; fclose(f);
  long period = argc > 3 ? num(argv[3]) : 1000;
  int iters = argc > 4 ? (int)num(argv[4]) : 50;
  samples = malloc(cap * sizeof *samples);
  vbm_json_tape t; for (int w = 0; w < 3; w++) { vbm_json_parse(b, n, NULL, &t); vbm_json_free(&t); }
  unsigned type = 4; { FILE *tf = fopen("/sys/bus/event_source/devices/cpu_core/type", "r"); if (tf) { char buf[16] = {0}; if (fgets(buf, sizeof buf, tf)) type = (unsigned)num(buf); fclose(tf); } }
  struct perf_event_attr a; memset(&a, 0, sizeof a); a.size = sizeof a; a.type = PERF_TYPE_HARDWARE; a.config = ((uint64_t)type << 32) | PERF_COUNT_HW_INSTRUCTIONS;
  a.exclude_kernel = 1; a.exclude_hv = 1; a.sample_period = period; a.disabled = 1; a.precise_ip = 0;
  fd = syscall(SYS_perf_event_open, &a, 0, -1, -1, 0); if (fd < 0) { perror("perf_event_open"); return 3; }
  struct sigaction sa; memset(&sa, 0, sizeof sa); sa.sa_sigaction = on_sig; sa.sa_flags = SA_SIGINFO; sigaction(SIGIO, &sa, NULL);
  fcntl(fd, F_SETFL, O_ASYNC); fcntl(fd, F_SETSIG, SIGIO); fcntl(fd, F_SETOWN, getpid());
  ioctl(fd, PERF_EVENT_IOC_RESET, 0); ioctl(fd, PERF_EVENT_IOC_REFRESH, 1);
  for (int r = 0; r < iters; r++) { vbm_json_parse(b, n, NULL, &t); vbm_json_free(&t); }
  ioctl(fd, PERF_EVENT_IOC_DISABLE, 0);
  FILE *o = fopen(argv[2], "w"); fprintf(o, "%lx\n", (unsigned long)(uintptr_t)&main);
  for (size_t i = 0; i < nsamp; i++) fprintf(o, "%lx\n", (unsigned long)samples[i]); fclose(o);
  fprintf(stderr, "%zu samples over %d parses = %.1f instr/B\n", nsamp, iters, (double)nsamp * period / iters / n);
  return 0;
}
