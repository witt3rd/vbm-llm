/* Freestanding stddef.h for the wasm32 build (the bundled clang ships no resource headers). */
#ifndef VBM_STDDEF_H
#define VBM_STDDEF_H
typedef __SIZE_TYPE__ size_t;
typedef __PTRDIFF_TYPE__ ptrdiff_t;
typedef __WCHAR_TYPE__ wchar_t;
#define NULL ((void *)0)
#define offsetof(t, m) __builtin_offsetof(t, m)
#endif
