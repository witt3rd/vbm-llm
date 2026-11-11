/* vbm_json.h: the C ABI of vbm-json (slice 1). Parses RFC 8259 JSON with the verified parser and returns a flat TAPE.
 * What is valid, and what a value is, is decided in Lean only; this header and abi/vbm_json.c move bytes. Tape layout: LeanJson/Tape.lean (the same text is below).
 * Prefix vbm_json_ (functions, types) and VBM_JSON_ (constants). Stable within ABI version VBM_JSON_ABI_VERSION; an ABI change is expand-and-contract.
 *
 * THE TAPE: little-endian u64 words (a little-endian host is required: the build refuses others). A node is two words: head = kind | len << 8, then aux.
 *   VBM_JSON_NULL, VBM_JSON_FALSE, VBM_JSON_TRUE: len = 0, aux = 0.
 *   VBM_JSON_NUMBER, VBM_JSON_STRING: len bytes of `text` starting at aux. A number's text is its lexeme (-, digits, .digits, e[-]digits); a string's text is its UTF-8, unescaped.
 *   VBM_JSON_ARRAY: len elements follow, each a node. VBM_JSON_OBJECT: len members follow, each a VBM_JSON_STRING node (the key) then a node (the value). Duplicate keys are kept in input order.
 *     aux = the number of words of the whole subtree, this node's two words included (skip a subtree: i += aux).
 *   The tape is the root node and everything inside it (words[0..nwords)). `text` is the concatenation of all texts in document order.
 * MEMORY: the tape and the text are one block obtained from the allocator in vbm_json_opts (default: the library's own heap: the result's own Lean ByteArray, handed out in place when its words are 8-aligned, else a copy of it: no libc) and released by vbm_json_free. The Lean runtime inside the library
 *   has its own heap for the parse; it is empty again when vbm_json_parse returns. Only the result memory comes from your allocator. A NULL from it is VBM_JSON_NOMEM.
 * THREADS: the first call initialises the Lean runtime (once; an atomic flag, a concurrent first caller waits). Concurrent calls are not yet tested or promised. */
#ifndef VBM_JSON_H
#define VBM_JSON_H
#if __STDC_HOSTED__
#include <stddef.h>
#include <stdint.h>
#else   /* freestanding (-ffreestanding -nostdinc): the types from the compiler's own macros, no header */
typedef __SIZE_TYPE__ size_t; typedef __UINTPTR_TYPE__ uintptr_t; typedef __UINT8_TYPE__ uint8_t; typedef __UINT64_TYPE__ uint64_t;
#endif
#ifdef __cplusplus
extern "C" {
#endif

#define VBM_JSON_ABI_VERSION 1u

enum { VBM_JSON_NULL = 0, VBM_JSON_FALSE = 1, VBM_JSON_TRUE = 2, VBM_JSON_NUMBER = 3, VBM_JSON_STRING = 4, VBM_JSON_ARRAY = 5, VBM_JSON_OBJECT = 6 };

/* Result codes of vbm_json_parse. 1 and 2 are the Lean `Error.code`s (LeanJson/Policy.lean). */
enum { VBM_JSON_OK = 0, VBM_JSON_SYNTAX = 1, VBM_JSON_DEPTH = 2, VBM_JSON_NOMEM = 3, VBM_JSON_ARG = 4, VBM_JSON_INTERNAL = 5 };

/* The embedder's memory. alloc returns a block of `size` bytes aligned to 8, or NULL; free receives the pointer, the same size, and ctx. */
typedef struct vbm_json_allocator {
  void *ctx;
  void *(*alloc)(void *ctx, size_t size);
  void (*free)(void *ctx, void *ptr, size_t size);
} vbm_json_allocator;

/* size = sizeof(vbm_json_opts) as the caller compiled it (room to grow). allocator NULL = the built-in default. opts may be NULL = defaults. */
typedef struct vbm_json_opts {
  size_t size;
  const vbm_json_allocator *allocator;
} vbm_json_opts;

typedef struct vbm_json_tape {
  const uint64_t *words; size_t nwords;
  const uint8_t *text;   size_t ntext;
  void *block_; size_t block_size_; vbm_json_allocator allocator_;   /* private: for vbm_json_free */
} vbm_json_tape;

/* Parse buf[0..len). VBM_JSON_OK: *tape is filled and must be released with vbm_json_free. Any other code: *tape is zeroed and there is nothing to free.
 * VBM_JSON_SYNTAX: not valid JSON (strict: no lone surrogates, no invalid UTF-8, no trailing bytes). VBM_JSON_DEPTH: nested deeper than the named limit (512). */
int vbm_json_parse(const uint8_t *buf, size_t len, const vbm_json_opts *opts, vbm_json_tape *tape);

/* Release a tape (with the allocator it came from). Safe on a zeroed tape and called twice. */
void vbm_json_free(vbm_json_tape *tape);

/* PRINTING. Bytes the library wrote: `data[0..len)`, from the same allocator rules as the tape (default: the library's own heap, handed out in place; opts->allocator: one block of exactly `len` bytes from yours). Release with vbm_json_bytes_free. */
typedef struct vbm_json_bytes {
  const uint8_t *data; size_t len;
  void *block_; size_t block_size_; vbm_json_allocator allocator_;   /* private: for vbm_json_bytes_free */
} vbm_json_bytes;

/* The compact JSON of a tape (no whitespace; numbers as the tape's lexeme; strings escaped minimally: `"` `\` and the controls below 0x20, everything else as UTF-8). The tape is read, not changed: pass the tape vbm_json_parse gave you (or one
 * with that layout). VBM_JSON_OK: *out is filled (never empty) and must be released with vbm_json_bytes_free; parsing the bytes again gives the same tape. VBM_JSON_ARG: the tape is refused (bad pointers, or its structure, a string's UTF-8 or a number's
 * characters, its nesting past 512, or its sizes do not hold together); a tape from vbm_json_parse is never refused. Any other code: *out is zeroed and there is nothing to free. */
int vbm_json_print_tape(const vbm_json_tape *tape, const vbm_json_opts *opts, vbm_json_bytes *out);

/* The JSON string literal of the UTF-8 text buf[0..len): a quote, the text escaped as above, a quote (never empty). An encoder that holds a string builds objects around this. VBM_JSON_SYNTAX: the text is not valid UTF-8 (strict, as for parsing). */
int vbm_json_escape_string(const uint8_t *buf, size_t len, const vbm_json_opts *opts, vbm_json_bytes *out);

/* Release bytes (with the allocator they came from). Safe on a zeroed value and called twice. */
void vbm_json_bytes_free(vbm_json_bytes *out);

#ifdef __cplusplus
}
#endif
#endif
