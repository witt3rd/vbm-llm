#ifndef VBM_STDLIB_H
#define VBM_STDLIB_H
#include <stddef.h>
void *malloc(size_t);
void free(void *);
void free_sized(void *, size_t);
void abort(void) __attribute__((noreturn));
#endif
