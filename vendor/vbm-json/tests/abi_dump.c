/* tests/abi_dump.c: the NATIVE ABI's verdicts, for scripts/test_wasm.sh to diff against the WASM build's. Usage: abi_dump VECTORS.jsonl
 * One line per row: "<id> <rc> <fnv1a64 of the tape bytes: the words, then the text>" (the hash is 0 for a non-OK result). Test code, not shipped. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "../include/vbm_json.h"

static int hexval(int c) { return c >= '0' && c <= '9' ? c - '0' : c >= 'a' && c <= 'f' ? c - 'a' + 10 : -1; }
static uint64_t fnv(uint64_t h, const uint8_t *p, size_t n) { for (size_t i = 0; i < n; i++) { h ^= p[i]; h *= 1099511628211ULL; } return h; }

int main(int argc, char **argv) {
  if (argc != 2) { fprintf(stderr, "usage: abi_dump VECTORS.jsonl\n"); return 2; }
  FILE *f = fopen(argv[1], "r"); if (!f) { perror(argv[1]); return 1; }
  char *line = NULL; size_t cap = 0; ssize_t got; size_t id = 0;
  while ((got = getline(&line, &cap, f)) > 0) {
    const char *p = strstr(line, "\"input\":\""); if (!p) { fprintf(stderr, "malformed row %zu\n", id); return 1; }
    p += 9; const char *q = strchr(p, '"'); size_t n = (size_t)(q - p) / 2;
    uint8_t *in = malloc(n + 1); if (!in) abort();
    for (size_t k = 0; k < n; k++) in[k] = (uint8_t)(hexval(p[2 * k]) * 16 + hexval(p[2 * k + 1]));
    vbm_json_tape t; int rc = vbm_json_parse(in, n, NULL, &t);
    uint64_t h = 0;
    if (rc == VBM_JSON_OK) { h = 14695981039346656037ULL; h = fnv(h, (const uint8_t *)t.words, 8 * t.nwords); h = fnv(h, t.text, t.ntext); }
    printf("%zu %d %016llx\n", id++, rc, (unsigned long long)h);
    vbm_json_free(&t); free(in);
  }
  free(line); fclose(f); return 0;
}
