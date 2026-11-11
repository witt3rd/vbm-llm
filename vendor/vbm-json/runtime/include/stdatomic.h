/* Freestanding stdatomic.h over clang's __c11_atomic builtins. The wasm32 module is single-threaded: these lower to plain loads and stores. */
#ifndef VBM_STDATOMIC_H
#define VBM_STDATOMIC_H
typedef enum { memory_order_relaxed = __ATOMIC_RELAXED, memory_order_acquire = __ATOMIC_ACQUIRE, memory_order_release = __ATOMIC_RELEASE,
               memory_order_acq_rel = __ATOMIC_ACQ_REL, memory_order_seq_cst = __ATOMIC_SEQ_CST } memory_order;
#define atomic_load_explicit(p, o) __c11_atomic_load(p, o)
#define atomic_store_explicit(p, v, o) __c11_atomic_store(p, v, o)
#define atomic_fetch_add_explicit(p, v, o) __c11_atomic_fetch_add(p, v, o)
#define atomic_fetch_sub_explicit(p, v, o) __c11_atomic_fetch_sub(p, v, o)
#define atomic_exchange_explicit(p, v, o) __c11_atomic_exchange(p, v, o)
#define atomic_compare_exchange_strong_explicit(p, e, d, s, f) __c11_atomic_compare_exchange_strong(p, e, d, s, f)
#define atomic_compare_exchange_weak_explicit(p, e, d, s, f) __c11_atomic_compare_exchange_weak(p, e, d, s, f)
#endif
