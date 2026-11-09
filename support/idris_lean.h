/* Runtime support for the Idris2 -> C backend built on Lean 4's runtime (lean.h).
 *
 * Value representation:
 *   - every boxed value is a lean_object*
 *   - nullary constructors / erased values are lean_box(tag) (no allocation, no RC)
 *   - data constructors are Lean ctor objects (lean_alloc_ctor)
 *   - closures are Lean closures (lean_alloc_closure / lean_apply_*)
 *   - Integer is Lean's Int (small ints are scalars, large ones GMP objects)
 *   - String is Lean's String (UTF-8, cached char length)
 *   - Int/IntN/BitsN/Char are unboxed C scalars when the type is known; when they
 *     need to be boxed (polymorphic positions) they use idr_box_int: a tagged
 *     scalar if the value fits in 62 bits, otherwise a ctor carrying 8 bytes.
 *   - Double is unboxed `double`, boxed with lean_box_float.
 */
#pragma once
#define LEAN_USE_GMP
#include <gmp.h>
#include <lean/lean.h>
#include <lean/lean_gmp.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

#define IDR_INLINE static inline __attribute__((always_inline))
#define IDR_LIKELY(x) __builtin_expect(!!(x), 1)
#define IDR_UNLIKELY(x) __builtin_expect(!!(x), 0)

/* ------------------------------------------------------------------ */
/* errors                                                              */

LEAN_EXPORT void lean_internal_set_thread_stack_size(size_t);
__attribute__((noreturn, cold)) void idr_crash(b_lean_obj_arg msg);
__attribute__((noreturn, cold)) void idr_crash_cstr(const char *msg);
__attribute__((noreturn, cold)) lean_object *idr_crash_v(b_lean_obj_arg msg);

/* ------------------------------------------------------------------ */
/* boxing of scalars                                                   */

IDR_INLINE lean_object *idr_box_int(int64_t v) {
    if (IDR_LIKELY(v >= -(INT64_C(1) << 61) && v < (INT64_C(1) << 61)))
        return (lean_object *)(((size_t)v << 1) | 1);
    return lean_box_uint64((uint64_t)v);
}
IDR_INLINE int64_t idr_unbox_int(b_lean_obj_arg o) {
    if (IDR_LIKELY(lean_is_scalar(o))) return ((int64_t)(size_t)o) >> 1;
    return (int64_t)lean_unbox_uint64(o);
}
#define idr_box_i8(v) idr_box_int((int64_t)(int8_t)(v))
#define idr_box_i16(v) idr_box_int((int64_t)(int16_t)(v))
#define idr_box_i32(v) idr_box_int((int64_t)(int32_t)(v))
#define idr_box_i64(v) idr_box_int((int64_t)(v))
#define idr_box_u8(v) idr_box_int((int64_t)(uint8_t)(v))
#define idr_box_u16(v) idr_box_int((int64_t)(uint16_t)(v))
#define idr_box_u32(v) idr_box_int((int64_t)(uint32_t)(v))
#define idr_box_u64(v) idr_box_int((int64_t)(uint64_t)(v))
#define idr_box_f64(v) lean_box_float(v)
#define idr_unbox_i8(o) ((int8_t)idr_unbox_int(o))
#define idr_unbox_i16(o) ((int16_t)idr_unbox_int(o))
#define idr_unbox_i32(o) ((int32_t)idr_unbox_int(o))
#define idr_unbox_i64(o) ((int64_t)idr_unbox_int(o))
#define idr_unbox_u8(o) ((uint8_t)idr_unbox_int(o))
#define idr_unbox_u16(o) ((uint16_t)idr_unbox_int(o))
#define idr_unbox_u32(o) ((uint32_t)idr_unbox_int(o))
#define idr_unbox_u64(o) ((uint64_t)idr_unbox_int(o))
IDR_INLINE double idr_unbox_f64(b_lean_obj_arg o) {
    /* an erased/garbage value may reach here through believe_me; be defensive */
    if (lean_is_scalar(o)) return (double)idr_unbox_int(o);
    return lean_unbox_float(o);
}

/* ------------------------------------------------------------------ */
/* fixed width arithmetic (Idris semantics: wrap around)               */

#define IDR_WRAP_OPS(T, S)                                                         \
    IDR_INLINE T idr_add_##S(T a, T b) { return (T)((uint64_t)a + (uint64_t)b); }   \
    IDR_INLINE T idr_sub_##S(T a, T b) { return (T)((uint64_t)a - (uint64_t)b); }   \
    IDR_INLINE T idr_mul_##S(T a, T b) { return (T)((uint64_t)a * (uint64_t)b); }   \
    IDR_INLINE T idr_neg_##S(T a) { return (T)(0 - (uint64_t)a); }                  \
    IDR_INLINE T idr_and_##S(T a, T b) { return (T)(a & b); }                       \
    IDR_INLINE T idr_or_##S(T a, T b) { return (T)(a | b); }                        \
    IDR_INLINE T idr_xor_##S(T a, T b) { return (T)(a ^ b); }                       \
    IDR_INLINE T idr_shl_##S(T a, T b) {                                            \
        return (T)((uint64_t)a << ((uint64_t)b & (sizeof(T) * 8 - 1)));             \
    }

IDR_WRAP_OPS(int8_t, i8)
IDR_WRAP_OPS(int16_t, i16)
IDR_WRAP_OPS(int32_t, i32)
IDR_WRAP_OPS(int64_t, i64)
IDR_WRAP_OPS(uint8_t, u8)
IDR_WRAP_OPS(uint16_t, u16)
IDR_WRAP_OPS(uint32_t, u32)
IDR_WRAP_OPS(uint64_t, u64)

/* signed: arithmetic shift; unsigned: logical */
#define IDR_SHR(T, S) \
    IDR_INLINE T idr_shr_##S(T a, T b) { return (T)(a >> ((uint64_t)b & (sizeof(T) * 8 - 1))); }
IDR_SHR(int8_t, i8)
IDR_SHR(int16_t, i16)
IDR_SHR(int32_t, i32)
IDR_SHR(int64_t, i64)
IDR_SHR(uint8_t, u8)
IDR_SHR(uint16_t, u16)
IDR_SHR(uint32_t, u32)
IDR_SHR(uint64_t, u64)

/* comparisons (Idris booleans are Int 0/1) */
#define IDR_CMP(T, S)                                                   \
    IDR_INLINE int64_t idr_lt_##S(T a, T b) { return a < b; }            \
    IDR_INLINE int64_t idr_le_##S(T a, T b) { return a <= b; }           \
    IDR_INLINE int64_t idr_eq_##S(T a, T b) { return a == b; }           \
    IDR_INLINE int64_t idr_ge_##S(T a, T b) { return a >= b; }           \
    IDR_INLINE int64_t idr_gt_##S(T a, T b) { return a > b; }
IDR_CMP(int8_t, i8)
IDR_CMP(int16_t, i16)
IDR_CMP(int32_t, i32)
IDR_CMP(int64_t, i64)
IDR_CMP(uint8_t, u8)
IDR_CMP(uint16_t, u16)
IDR_CMP(uint32_t, u32)
IDR_CMP(uint64_t, u64)
IDR_CMP(double, f64)

IDR_INLINE double idr_add_f64(double a, double b) { return a + b; }
IDR_INLINE double idr_sub_f64(double a, double b) { return a - b; }
IDR_INLINE double idr_mul_f64(double a, double b) { return a * b; }
IDR_INLINE double idr_div_f64(double a, double b) { return a / b; }
IDR_INLINE double idr_mod_f64(double a, double b) { return fmod(a, b); }
IDR_INLINE double idr_neg_f64(double a) { return -a; }

/* Euclidean division/modulus for signed types (matches the Chez/RefC backends) */
#define IDR_SDIV(T, S)                                                             \
    IDR_INLINE T idr_div_##S(T n, T d) {                                            \
        if (IDR_UNLIKELY(d == 0)) idr_crash_cstr("Division by zero");               \
        if (IDR_UNLIKELY(d == -1)) return idr_neg_##S(n);                           \
        T r = n % d;                                                                \
        return (T)(n / d + ((r < 0) ? ((d < 0) ? 1 : -1) : 0));                     \
    }                                                                               \
    IDR_INLINE T idr_mod_##S(T n, T d) {                                            \
        if (IDR_UNLIKELY(d == 0)) idr_crash_cstr("Division by zero");               \
        if (IDR_UNLIKELY(d == -1)) return 0;                                        \
        T ad = d < 0 ? (T)-d : d;                                                   \
        T r = n % ad;                                                               \
        return (T)(r < 0 ? r + ad : r);                                             \
    }
IDR_SDIV(int8_t, i8)
IDR_SDIV(int16_t, i16)
IDR_SDIV(int32_t, i32)
IDR_SDIV(int64_t, i64)
#define IDR_UDIV(T, S)                                                             \
    IDR_INLINE T idr_div_##S(T n, T d) {                                            \
        if (IDR_UNLIKELY(d == 0)) idr_crash_cstr("Division by zero");               \
        return n / d;                                                               \
    }                                                                               \
    IDR_INLINE T idr_mod_##S(T n, T d) {                                            \
        if (IDR_UNLIKELY(d == 0)) idr_crash_cstr("Division by zero");               \
        return n % d;                                                               \
    }
IDR_UDIV(uint8_t, u8)
IDR_UDIV(uint16_t, u16)
IDR_UDIV(uint32_t, u32)
IDR_UDIV(uint64_t, u64)

/* ------------------------------------------------------------------ */
/* Integer (Lean Int)                                                  */

lean_obj_res idr_integer_of_mpz(mpz_t m); /* clears m */
lean_obj_res idr_integer_of_u64(uint64_t v);
lean_obj_res idr_integer_of_str(const char *s); /* parses decimal, invalid => 0 */
lean_obj_res idr_integer_of_double(double d);
double idr_integer_to_double(b_lean_obj_arg a);
lean_obj_res idr_integer_to_string(b_lean_obj_arg a);
lean_obj_res idr_integer_and(b_lean_obj_arg a, b_lean_obj_arg b);
lean_obj_res idr_integer_or(b_lean_obj_arg a, b_lean_obj_arg b);
lean_obj_res idr_integer_xor(b_lean_obj_arg a, b_lean_obj_arg b);
lean_obj_res idr_integer_shl(b_lean_obj_arg a, b_lean_obj_arg b);
lean_obj_res idr_integer_shr(b_lean_obj_arg a, b_lean_obj_arg b);
lean_obj_res idr_integer_lit(const char *s, lean_object **cache);

IDR_INLINE lean_obj_res idr_integer_of_i64(int64_t v) { return lean_int64_to_int(v); }
IDR_INLINE int64_t idr_integer_to_i64(b_lean_obj_arg a) { return (int64_t)lean_int64_of_int(a); }
IDR_INLINE lean_obj_res idr_integer_div(b_lean_obj_arg a, b_lean_obj_arg b) {
    if (IDR_UNLIKELY(lean_is_scalar(b) && lean_scalar_to_int64(b) == 0)) idr_crash_cstr("Division by zero");
    return lean_int_ediv(a, b);
}
IDR_INLINE lean_obj_res idr_integer_mod(b_lean_obj_arg a, b_lean_obj_arg b) {
    if (IDR_UNLIKELY(lean_is_scalar(b) && lean_scalar_to_int64(b) == 0)) idr_crash_cstr("Division by zero");
    return lean_int_emod(a, b);
}
IDR_INLINE int64_t idr_integer_lt(b_lean_obj_arg a, b_lean_obj_arg b) { return lean_int_dec_lt(a, b); }
IDR_INLINE int64_t idr_integer_le(b_lean_obj_arg a, b_lean_obj_arg b) { return lean_int_dec_le(a, b); }
IDR_INLINE int64_t idr_integer_eq(b_lean_obj_arg a, b_lean_obj_arg b) { return lean_int_dec_eq(a, b); }
IDR_INLINE int64_t idr_integer_gt(b_lean_obj_arg a, b_lean_obj_arg b) { return lean_int_dec_lt(b, a); }
IDR_INLINE int64_t idr_integer_ge(b_lean_obj_arg a, b_lean_obj_arg b) { return lean_int_dec_le(b, a); }

/* ------------------------------------------------------------------ */
/* Strings                                                             */

IDR_INLINE int64_t idr_str_length(b_lean_obj_arg s) { return (int64_t)lean_string_len(s); }
IDR_INLINE int idr_str_is_ascii(b_lean_obj_arg s) {
    return lean_string_size(s) - 1 == lean_string_len(s);
}
uint32_t idr_str_index_slow(b_lean_obj_arg s, int64_t i);
IDR_INLINE uint32_t idr_str_index(b_lean_obj_arg s, int64_t i) {
    if (IDR_LIKELY(idr_str_is_ascii(s))) {
        if (IDR_UNLIKELY(i < 0 || (size_t)i >= lean_string_len(s))) return 0;
        return (uint8_t)lean_string_cstr(s)[i];
    }
    return idr_str_index_slow(s, i);
}
IDR_INLINE uint32_t idr_str_head(b_lean_obj_arg s) { return idr_str_index(s, 0); }
lean_obj_res idr_str_tail(b_lean_obj_arg s);
lean_obj_res idr_str_cons(uint32_t c, b_lean_obj_arg s);
IDR_INLINE lean_obj_res idr_str_append(lean_obj_arg a, b_lean_obj_arg b) { return lean_string_append(a, b); }
lean_obj_res idr_str_reverse(b_lean_obj_arg s);
lean_obj_res idr_str_substr(int64_t start, int64_t len, b_lean_obj_arg s);
IDR_INLINE int64_t idr_str_eq(b_lean_obj_arg a, b_lean_obj_arg b) { return lean_string_dec_eq(a, b); }
IDR_INLINE int64_t idr_str_lt(b_lean_obj_arg a, b_lean_obj_arg b) { return lean_string_dec_lt(a, b); }
IDR_INLINE int64_t idr_str_le(b_lean_obj_arg a, b_lean_obj_arg b) { return !lean_string_dec_lt(b, a); }
IDR_INLINE int64_t idr_str_gt(b_lean_obj_arg a, b_lean_obj_arg b) { return lean_string_dec_lt(b, a); }
IDR_INLINE int64_t idr_str_ge(b_lean_obj_arg a, b_lean_obj_arg b) { return !lean_string_dec_lt(a, b); }

lean_obj_res idr_str_of_cstr(const char *s);
lean_obj_res idr_str_of_i64(int64_t v);
lean_obj_res idr_str_of_u64(uint64_t v);
lean_obj_res idr_str_of_double(double d);
lean_obj_res idr_str_of_char(uint32_t c);
int64_t idr_str_to_i64(b_lean_obj_arg s);
double idr_str_to_double(b_lean_obj_arg s);
IDR_INLINE lean_obj_res idr_str_to_integer(b_lean_obj_arg s) { return idr_integer_of_str(lean_string_cstr(s)); }
IDR_INLINE uint32_t idr_str_to_char(b_lean_obj_arg s) { return idr_str_index(s, 0); }

/* ------------------------------------------------------------------ */
/* Mutable references and arrays                                       */

IDR_INLINE lean_obj_res idr_ioref_new(lean_obj_arg v) {
    lean_object *r = lean_alloc_ctor(0, 1, 0);
    lean_ctor_set(r, 0, v);
    return r;
}
IDR_INLINE lean_obj_res idr_ioref_read(b_lean_obj_arg r) {
    lean_object *v = lean_ctor_get(r, 0);
    lean_inc(v);
    return v;
}
IDR_INLINE lean_obj_res idr_ioref_write(b_lean_obj_arg r, lean_obj_arg v) {
    /* values stored into a reference shared between threads become shared */
    if (IDR_UNLIKELY(lean_is_mt(r)) && !lean_is_scalar(v)) lean_mark_mt(v);
    lean_object *old = lean_ctor_get(r, 0);
    lean_ctor_set(r, 0, v);
    lean_dec(old);
    return lean_box(0);
}
lean_obj_res idr_array_new(int64_t n, lean_obj_arg v);
IDR_INLINE lean_obj_res idr_array_get(b_lean_obj_arg a, int64_t i) {
    lean_object *v = lean_array_get_core(a, (size_t)i);
    lean_inc(v);
    return v;
}
IDR_INLINE lean_obj_res idr_array_set(b_lean_obj_arg a, int64_t i, lean_obj_arg v) {
    if (IDR_UNLIKELY(lean_is_mt(a)) && !lean_is_scalar(v)) lean_mark_mt(v);
    lean_object **p = lean_array_cptr(a) + i;
    lean_object *old = *p;
    *p = v;
    lean_dec(old);
    return lean_box(0);
}

/* pointers (AnyPtr / Ptr t / Buffer ...) */
IDR_INLINE lean_obj_res idr_box_ptr(void *p) { return lean_box_usize((size_t)p); }
typedef struct { void *ptr; lean_object *finalizer; } idr_gcptr;
IDR_INLINE void *idr_unbox_ptr(b_lean_obj_arg o) {
    if (lean_is_scalar(o)) return NULL;
    /* GCPtr / GCAnyPtr: external object carrying the pointer and its finalizer */
    if (IDR_UNLIKELY(lean_is_external(o))) return ((idr_gcptr *)lean_get_external_data(o))->ptr;
    return (void *)lean_unbox_usize(o);
}
lean_obj_res idr_on_collect(lean_obj_arg ptr, lean_obj_arg finalizer);

/* natively implemented foreign functions of the prelude */
lean_obj_res idr_fast_pack(b_lean_obj_arg chars);
lean_obj_res idr_fast_unpack(b_lean_obj_arg s);
lean_obj_res idr_fast_concat(b_lean_obj_arg strs);

/* closures with more than LEAN_CLOSURE_MAX_ARGS arguments */
IDR_INLINE lean_obj_res idr_apply(lean_obj_arg f, lean_obj_arg a) { return lean_apply_1(f, a); }

/* ------------------------------------------------------------------ */
/* entry point helpers                                                 */

int idr_run_main(int argc, char **argv, lean_object *(*main_fn)(void));

/* ------------------------------------------------------------------ */
/* Natively implemented RefC-only foreign functions of base/contrib    */

/* Buffer = Lean scalar array of bytes (mutable in place) */
lean_obj_res idr_buf_new(int64_t size);
int64_t idr_buf_size(b_lean_obj_arg b);
#define IDR_BUF(b) ((uint8_t *)lean_sarray_cptr(b))
#define IDR_BUF_GETSET(NAME, T)                                                              \
    static inline lean_obj_res idr_buf_set_##NAME(b_lean_obj_arg b, int64_t off, T v) {     \
        memcpy(IDR_BUF(b) + off, &v, sizeof(T)); return lean_box(0); }                     \
    static inline T idr_buf_get_##NAME(b_lean_obj_arg b, int64_t off) {                      \
        T v; memcpy(&v, IDR_BUF(b) + off, sizeof(T)); return v; }
IDR_BUF_GETSET(u8, uint8_t)
IDR_BUF_GETSET(u16, uint16_t)
IDR_BUF_GETSET(u32, uint32_t)
IDR_BUF_GETSET(u64, uint64_t)
IDR_BUF_GETSET(i8, int8_t)
IDR_BUF_GETSET(i16, int16_t)
IDR_BUF_GETSET(i32, int32_t)
IDR_BUF_GETSET(i64, int64_t)
IDR_BUF_GETSET(f64, double)
static inline lean_obj_res idr_buf_set_byte(b_lean_obj_arg b, int64_t off, int64_t v) {
    IDR_BUF(b)[off] = (uint8_t)v; return lean_box(0); }
static inline int64_t idr_buf_get_byte(b_lean_obj_arg b, int64_t off) { return IDR_BUF(b)[off]; }
lean_obj_res idr_buf_set_string(b_lean_obj_arg b, int64_t off, b_lean_obj_arg s);
lean_obj_res idr_buf_get_string(b_lean_obj_arg b, int64_t off, int64_t len);
lean_obj_res idr_buf_copy(b_lean_obj_arg src, int64_t soff, int64_t len, b_lean_obj_arg dst, int64_t doff);

/* OSClock = ctor with scalars {sec:u64, nsec:u64, valid:u8} */
lean_obj_res idr_clock_utc(void);
lean_obj_res idr_clock_process(void);
lean_obj_res idr_clock_thread(void);
lean_obj_res idr_clock_invalid(void);
lean_obj_res idr_clock_monotonic(void);
int64_t idr_clock_valid(b_lean_obj_arg c);
uint64_t idr_clock_second(b_lean_obj_arg c);
uint64_t idr_clock_nanosecond(b_lean_obj_arg c);

/* StringIterator = boxed byte offset */
static inline int64_t idr_str_bytelen(b_lean_obj_arg s) { return (int64_t)(lean_string_size(s) - 1); }
static inline lean_obj_res idr_strit_new(b_lean_obj_arg s) { (void)s; return lean_box(0); }
lean_obj_res idr_strit_to_string(b_lean_obj_arg ty, b_lean_obj_arg s, b_lean_obj_arg it, b_lean_obj_arg f);
lean_obj_res idr_strit_next(b_lean_obj_arg s, b_lean_obj_arg it);

/* threads: Idris fork = Lean task on a dedicated thread (the closure is
   applied to the unit value, which doubles as the world token) */
#define IDR_DEDICATED_PRIO 9
lean_obj_res idr_fork(b_lean_obj_arg prog);
static inline lean_obj_res idr_thread_wait(b_lean_obj_arg t) {
    (void)lean_task_get(t);
    return lean_box(0);
}

/* System.Concurrency / System.Future (Scheme-only primitives in base) */
lean_obj_res idr_set_thread_data(b_lean_obj_arg v);
lean_obj_res idr_get_thread_data(void);
int64_t idr_get_thread_id(void);
lean_obj_res idr_mutex_new(void);
lean_obj_res idr_mutex_acquire(b_lean_obj_arg m);
lean_obj_res idr_mutex_release(b_lean_obj_arg m);
lean_obj_res idr_cond_new(void);
lean_obj_res idr_cond_wait(b_lean_obj_arg c, b_lean_obj_arg m);
lean_obj_res idr_cond_wait_timeout(b_lean_obj_arg c, b_lean_obj_arg m, int64_t usec);
lean_obj_res idr_cond_signal(b_lean_obj_arg c);
lean_obj_res idr_cond_broadcast(b_lean_obj_arg c);
lean_obj_res idr_sem_new(int64_t n);
lean_obj_res idr_sem_post(b_lean_obj_arg s);
lean_obj_res idr_sem_wait(b_lean_obj_arg s);
lean_obj_res idr_barrier_new(int64_t n);
lean_obj_res idr_barrier_wait(b_lean_obj_arg b);
lean_obj_res idr_chan_new(void);
lean_obj_res idr_chan_get(b_lean_obj_arg c);
lean_obj_res idr_chan_get_nb(b_lean_obj_arg c);
lean_obj_res idr_chan_get_timeout(b_lean_obj_arg c, int64_t msec);
lean_obj_res idr_chan_put(b_lean_obj_arg c, b_lean_obj_arg v);
lean_obj_res idr_future_new(b_lean_obj_arg f);
lean_obj_res idr_future_await(b_lean_obj_arg t);
