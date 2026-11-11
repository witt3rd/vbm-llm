/* lean/config.h for the freestanding builds (wasm32 and native): the toolchain's, WITHOUT LEAN_MIMALLOC (no mimalloc in a freestanding build: lean.h then allocates with malloc/free_sized, runtime/rt.c). */
#pragma once
#include <lean/version.h>
#define LEAN_IS_STAGE0 0
