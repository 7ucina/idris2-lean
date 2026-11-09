#include "idris_lean.h"
#include <errno.h>

void idris2_setArgs(int argc, char *argv[]);

/* like the Chez backend: message on stdout, exit code 1 */
void idr_crash(b_lean_obj_arg msg) {
    printf("%s\n", lean_string_cstr(msg));
    fflush(stdout);
    exit(1);
}
void idr_crash_cstr(const char *msg) {
    printf("%s\n", msg);
    fflush(stdout);
    exit(1);
}

lean_object *idr_crash_v(b_lean_obj_arg msg) { idr_crash(msg); }

/* ------------------------------------------------------------------ */
/* Integer                                                             */

lean_obj_res idr_integer_of_mpz(mpz_t m) {
    lean_object *r;
    if (mpz_fits_slong_p(m)) r = lean_int64_to_int(mpz_get_si(m));
    else r = lean_alloc_mpz(m);
    mpz_clear(m);
    return r;
}

static void idr_to_mpz(b_lean_obj_arg a, mpz_t m) {
    mpz_init(m);
    if (lean_is_scalar(a)) mpz_set_si(m, lean_scalar_to_int64(a));
    else lean_extract_mpz_value(a, m);
}

lean_obj_res idr_integer_of_u64(uint64_t v) {
    if (v <= (uint64_t)INT64_MAX) return lean_int64_to_int((int64_t)v);
    mpz_t m;
    mpz_init(m);
    mpz_set_ui(m, v);
    return idr_integer_of_mpz(m);
}

lean_obj_res idr_integer_of_str(const char *s) {
    const char *p = s;
    if (*p == '-' || *p == '+') p++;
    if (!*p) return lean_box(0);
    for (const char *q = p; *q; q++)
        if (*q < '0' || *q > '9') return lean_box(0);
    mpz_t m;
    mpz_init(m);
    if (mpz_set_str(m, *s == '+' ? s + 1 : s, 10) != 0) {
        mpz_clear(m);
        return lean_box(0);
    }
    return idr_integer_of_mpz(m);
}

lean_obj_res idr_integer_lit(const char *s, lean_object **cache) {
    if (*cache) return *cache;
    lean_object *v = idr_integer_of_str(s);
    lean_mark_persistent(v);
    *cache = v;
    return v;
}

lean_obj_res idr_integer_of_double(double d) {
    if (d >= -9.2e18 && d <= 9.2e18) return lean_int64_to_int((int64_t)d);
    if (isnan(d) || isinf(d)) return lean_box(0);
    mpz_t m;
    mpz_init(m);
    mpz_set_d(m, d);
    return idr_integer_of_mpz(m);
}

double idr_integer_to_double(b_lean_obj_arg a) {
    if (lean_is_scalar(a)) return (double)lean_scalar_to_int64(a);
    mpz_t m;
    idr_to_mpz(a, m);
    double d = mpz_get_d(m);
    mpz_clear(m);
    return d;
}

lean_obj_res idr_integer_to_string(b_lean_obj_arg a) {
    if (lean_is_scalar(a)) return idr_str_of_i64(lean_scalar_to_int64(a));
    mpz_t m;
    idr_to_mpz(a, m);
    char *buf = mpz_get_str(NULL, 10, m);
    lean_object *r = lean_mk_string(buf);
    void (*freefunc)(void *, size_t);
    mp_get_memory_functions(NULL, NULL, &freefunc);
    freefunc(buf, strlen(buf) + 1);
    mpz_clear(m);
    return r;
}

#define IDR_INTEGER_BITOP(NAME, OP, MPZOP)                                  \
    lean_obj_res idr_integer_##NAME(b_lean_obj_arg a, b_lean_obj_arg b) {   \
        if (lean_is_scalar(a) && lean_is_scalar(b))                         \
            return lean_int64_to_int(lean_scalar_to_int64(a) OP lean_scalar_to_int64(b)); \
        mpz_t x, y, r;                                                      \
        idr_to_mpz(a, x);                                                   \
        idr_to_mpz(b, y);                                                   \
        mpz_init(r);                                                        \
        MPZOP(r, x, y);                                                     \
        mpz_clear(x);                                                       \
        mpz_clear(y);                                                       \
        return idr_integer_of_mpz(r);                                       \
    }
IDR_INTEGER_BITOP(and, &, mpz_and)
IDR_INTEGER_BITOP(or, |, mpz_ior)
IDR_INTEGER_BITOP(xor, ^, mpz_xor)

lean_obj_res idr_integer_shl(b_lean_obj_arg a, b_lean_obj_arg b) {
    int64_t n = lean_is_scalar(b) ? lean_scalar_to_int64(b) : 0;
    if (n < 0) n = 0;
    mpz_t x;
    idr_to_mpz(a, x);
    mpz_mul_2exp(x, x, (mp_bitcnt_t)n);
    return idr_integer_of_mpz(x);
}
lean_obj_res idr_integer_shr(b_lean_obj_arg a, b_lean_obj_arg b) {
    int64_t n = lean_is_scalar(b) ? lean_scalar_to_int64(b) : 0;
    if (n < 0) n = 0;
    if (lean_is_scalar(a)) {
        int64_t v = lean_scalar_to_int64(a);
        return lean_int64_to_int(n >= 63 ? (v < 0 ? -1 : 0) : (v >> n));
    }
    mpz_t x;
    idr_to_mpz(a, x);
    mpz_fdiv_q_2exp(x, x, (mp_bitcnt_t)n);
    return idr_integer_of_mpz(x);
}

/* ------------------------------------------------------------------ */
/* Strings (UTF-8; character indexed like the Chez backend)            */

static size_t utf8_encode(uint32_t c, char *out) {
    if (c < 0x80) { out[0] = (char)c; return 1; }
    if (c < 0x800) { out[0] = (char)(0xC0 | (c >> 6)); out[1] = (char)(0x80 | (c & 0x3F)); return 2; }
    if (c < 0x10000) {
        out[0] = (char)(0xE0 | (c >> 12)); out[1] = (char)(0x80 | ((c >> 6) & 0x3F));
        out[2] = (char)(0x80 | (c & 0x3F)); return 3;
    }
    out[0] = (char)(0xF0 | (c >> 18)); out[1] = (char)(0x80 | ((c >> 12) & 0x3F));
    out[2] = (char)(0x80 | ((c >> 6) & 0x3F)); out[3] = (char)(0x80 | (c & 0x3F)); return 4;
}

static size_t utf8_len_at(const unsigned char *p) {
    unsigned char c = *p;
    if (c < 0x80) return 1;
    if ((c & 0xE0) == 0xC0) return 2;
    if ((c & 0xF0) == 0xE0) return 3;
    return 4;
}

static uint32_t utf8_decode(const unsigned char *p) {
    unsigned char c = *p;
    if (c < 0x80) return c;
    if ((c & 0xE0) == 0xC0) return ((uint32_t)(c & 0x1F) << 6) | (p[1] & 0x3F);
    if ((c & 0xF0) == 0xE0) return ((uint32_t)(c & 0x0F) << 12) | ((uint32_t)(p[1] & 0x3F) << 6) | (p[2] & 0x3F);
    return ((uint32_t)(c & 0x07) << 18) | ((uint32_t)(p[1] & 0x3F) << 12) | ((uint32_t)(p[2] & 0x3F) << 6) | (p[3] & 0x3F);
}

/* byte offset of character i (i <= length) */
static size_t utf8_offset(b_lean_obj_arg s, size_t i) {
    if (idr_str_is_ascii(s)) return i;
    const unsigned char *p = (const unsigned char *)lean_string_cstr(s);
    size_t off = 0;
    while (i > 0) { off += utf8_len_at(p + off); i--; }
    return off;
}

uint32_t idr_str_index_slow(b_lean_obj_arg s, int64_t i) {
    if (i < 0 || (size_t)i >= lean_string_len(s)) return 0;
    const unsigned char *p = (const unsigned char *)lean_string_cstr(s);
    return utf8_decode(p + utf8_offset(s, (size_t)i));
}

lean_obj_res idr_str_tail(b_lean_obj_arg s) {
    size_t len = lean_string_len(s);
    if (len == 0) return lean_mk_string_unchecked("", 0, 0);
    const char *p = lean_string_cstr(s);
    size_t first = utf8_len_at((const unsigned char *)p);
    size_t sz = lean_string_size(s) - 1;
    return lean_mk_string_unchecked(p + first, sz - first, len - 1);
}

lean_obj_res idr_str_cons(uint32_t c, b_lean_obj_arg s) {
    char buf[4];
    size_t n = utf8_encode(c, buf);
    size_t sz = lean_string_size(s) - 1;
    size_t len = lean_string_len(s);
    lean_object *r = lean_alloc_object(sizeof(lean_string_object) + sz + n + 1);
    lean_string_object *o = (lean_string_object *)r;
    lean_set_st_header(r, LeanString, 0);
    o->m_size = sz + n + 1;
    o->m_capacity = sz + n + 1;
    o->m_length = len + 1;
    memcpy(o->m_data, buf, n);
    memcpy(o->m_data + n, lean_string_cstr(s), sz + 1);
    return r;
}

lean_obj_res idr_str_reverse(b_lean_obj_arg s) {
    size_t sz = lean_string_size(s) - 1;
    size_t len = lean_string_len(s);
    const unsigned char *p = (const unsigned char *)lean_string_cstr(s);
    char *buf = (char *)malloc(sz + 1);
    size_t off = 0;
    while (off < sz) {
        size_t n = utf8_len_at(p + off);
        memcpy(buf + sz - off - n, p + off, n);
        off += n;
    }
    lean_object *r = lean_mk_string_unchecked(buf, sz, len);
    free(buf);
    return r;
}

lean_obj_res idr_str_substr(int64_t start, int64_t len, b_lean_obj_arg s) {
    int64_t slen = (int64_t)lean_string_len(s);
    if (start < 0) start = 0;
    if (start > slen) start = slen;
    if (len < 0) len = 0;
    if (len > slen - start) len = slen - start;
    size_t b = utf8_offset(s, (size_t)start);
    size_t e;
    if (idr_str_is_ascii(s)) e = b + (size_t)len;
    else {
        const unsigned char *p = (const unsigned char *)lean_string_cstr(s);
        e = b;
        for (int64_t i = 0; i < len; i++) e += utf8_len_at(p + e);
    }
    return lean_mk_string_unchecked(lean_string_cstr(s) + b, e - b, (size_t)len);
}

lean_obj_res idr_str_of_cstr(const char *s) { return lean_mk_string(s ? s : ""); }

lean_obj_res idr_str_of_i64(int64_t v) {
    char buf[32];
    int n = snprintf(buf, sizeof buf, "%lld", (long long)v);
    return lean_mk_string_unchecked(buf, (size_t)n, (size_t)n);
}
lean_obj_res idr_str_of_u64(uint64_t v) {
    char buf[32];
    int n = snprintf(buf, sizeof buf, "%llu", (unsigned long long)v);
    return lean_mk_string_unchecked(buf, (size_t)n, (size_t)n);
}
lean_obj_res idr_str_of_char(uint32_t c) {
    char buf[4];
    size_t n = utf8_encode(c, buf);
    return lean_mk_string_unchecked(buf, n, 1);
}

/* Shortest round-tripping representation, formatted like Chez Scheme */
lean_obj_res idr_str_of_double(double d) {
    char buf[64];
    if (isnan(d)) return lean_mk_string("+nan.0");
    if (isinf(d)) return lean_mk_string(d > 0 ? "+inf.0" : "-inf.0");
    for (int prec = 1; prec <= 17; prec++) {
        snprintf(buf, sizeof buf, "%.*g", prec, d);
        if (strtod(buf, NULL) == d) break;
    }
    /* Chez prints integral doubles as "3.0" and uses "e" exponents */
    char *e = strchr(buf, 'e');
    if (e) {
        /* mantissa needs no ".0"; normalise exponent: 1e+21 -> 1e21, 1e-07 -> 1e-7 */
        char mant[64], out[80];
        size_t ml = (size_t)(e - buf);
        memcpy(mant, buf, ml);
        mant[ml] = 0;
        int ex = atoi(e + 1);
        snprintf(out, sizeof out, "%se%d", mant, ex);
        return lean_mk_string(out);
    }
    if (!strchr(buf, '.')) strcat(buf, ".0");
    return lean_mk_string(buf);
}

int64_t idr_str_to_i64(b_lean_obj_arg s) {
    const char *p = lean_string_cstr(s);
    while (*p == ' ' || *p == '\t' || *p == '\n') p++;
    errno = 0;
    char *end;
    long long v = strtoll(p, &end, 10);
    if (end == p) return 0;
    while (*end == ' ' || *end == '\t' || *end == '\n') end++;
    if (*end) {
        /* like Chez: a decimal number is truncated towards zero */
        double d = strtod(p, &end);
        while (*end == ' ' || *end == '\t' || *end == '\n') end++;
        if (*end || isnan(d)) return 0;
        return (int64_t)d;
    }
    return (int64_t)v;
}

double idr_str_to_double(b_lean_obj_arg s) {
    const char *p = lean_string_cstr(s);
    char *end;
    double d = strtod(p, &end);
    if (end == p) return 0.0;
    while (*end == ' ' || *end == '\t' || *end == '\n') end++;
    if (*end) return 0.0;
    if (d == 0.0 && !strpbrk(p, ".eE")) return 0.0; /* exact zero, e.g. "-0" */
    return d;
}

/* Lists: Nil = lean_box(0), (::) = ctor tag 1 with 2 fields */
lean_obj_res idr_fast_pack(b_lean_obj_arg chars) {
    size_t sz = 0, len = 0;
    char buf[4];
    for (lean_object *p = chars; !lean_is_scalar(p); p = lean_ctor_get(p, 1)) {
        sz += utf8_encode(idr_unbox_u32(lean_ctor_get(p, 0)), buf);
        len++;
    }
    char *data = (char *)malloc(sz + 1);
    size_t off = 0;
    for (lean_object *p = chars; !lean_is_scalar(p); p = lean_ctor_get(p, 1))
        off += utf8_encode(idr_unbox_u32(lean_ctor_get(p, 0)), data + off);
    lean_object *r = lean_mk_string_unchecked(data, sz, len);
    free(data);
    return r;
}

lean_obj_res idr_fast_unpack(b_lean_obj_arg s) {
    const unsigned char *p = (const unsigned char *)lean_string_cstr(s);
    size_t sz = lean_string_size(s) - 1;
    lean_object *head = lean_box(0);
    lean_object **tail = &head;
    size_t off = 0;
    while (off < sz) {
        lean_object *c = lean_alloc_ctor(1, 2, 0);
        lean_ctor_set(c, 0, idr_box_u32(utf8_decode(p + off)));
        *tail = c;
        tail = &lean_ctor_obj_cptr(c)[1];
        off += utf8_len_at(p + off);
    }
    *tail = lean_box(0);
    return head;
}

lean_obj_res idr_fast_concat(b_lean_obj_arg strs) {
    size_t sz = 0, len = 0;
    for (lean_object *p = strs; !lean_is_scalar(p); p = lean_ctor_get(p, 1)) {
        sz += lean_string_size(lean_ctor_get(p, 0)) - 1;
        len += lean_string_len(lean_ctor_get(p, 0));
    }
    char *data = (char *)malloc(sz + 1);
    size_t off = 0;
    for (lean_object *p = strs; !lean_is_scalar(p); p = lean_ctor_get(p, 1)) {
        lean_object *str = lean_ctor_get(p, 0);
        size_t n = lean_string_size(str) - 1;
        memcpy(data + off, lean_string_cstr(str), n);
        off += n;
    }
    lean_object *r = lean_mk_string_unchecked(data, sz, len);
    free(data);
    return r;
}

/* ------------------------------------------------------------------ */
/* arrays                                                              */

lean_obj_res idr_array_new(int64_t n, lean_obj_arg v) {
    if (n < 0) n = 0;
    lean_object *a = lean_alloc_array((size_t)n, (size_t)n);
    lean_object **p = lean_array_cptr(a);
    if (n == 0) { lean_dec(v); return a; }
    if (n > 1) lean_inc_n(v, (size_t)(n - 1));
    for (int64_t i = 0; i < n; i++) p[i] = v;
    return a;
}

/* GC'd pointers (onCollect): a Lean external object holding the raw pointer
   and the Idris finalizer.  With reference counting the finalizer runs
   deterministically, as soon as the last reference to the GCPtr is dropped. */
static void idr_gcptr_finalize(void *data) {
    idr_gcptr *g = (idr_gcptr *)data;
    /* finalizer : Ptr t -> PrimIO (); apply to the pointer and the world token */
    lean_object *r = lean_apply_2(g->finalizer, idr_box_ptr(g->ptr), lean_box(0));
    lean_dec(r);
    free(g);
}
static void idr_gcptr_foreach(void *data, b_lean_obj_arg f) {
    idr_gcptr *g = (idr_gcptr *)data;
    lean_inc(f);
    lean_inc(g->finalizer);
    lean_dec(lean_apply_1(f, g->finalizer));
}
static lean_external_class *g_gcptr_class = NULL;
void idr_init_gcptr(void) { g_gcptr_class = lean_register_external_class(idr_gcptr_finalize, idr_gcptr_foreach); }

lean_obj_res idr_on_collect(lean_obj_arg ptr, lean_obj_arg finalizer) {
    idr_gcptr *g = (idr_gcptr *)malloc(sizeof *g);
    g->ptr = idr_unbox_ptr(ptr);
    g->finalizer = finalizer;   /* ownership transferred */
    lean_dec(ptr);
    return lean_alloc_external(g_gcptr_class, g);
}

/* ------------------------------------------------------------------ */
/* main                                                                */

static lean_object *(*g_main_fn)(void);
void idr_set_main_thread(void);
static lean_object *idr_run_main_thunk(int argc, char **argv) {
    (void)argc; (void)argv;
    idr_set_main_thread();
    lean_object *r = g_main_fn();
    lean_dec(r);
    return lean_io_result_mk_ok(lean_box(0));
}

void lean_initialize_runtime_module(void);

int idr_run_main(int argc, char **argv, lean_object *(*main_fn)(void)) {
    lean_initialize_runtime_module();
    lean_io_mark_end_initialization();
    lean_init_task_manager();
    { void idr_init_gcptr(void); idr_init_gcptr(); }
    idris2_setArgs(argc, argv);
    g_main_fn = main_fn;
    /* Idris code is often deeply (non-tail) recursive; run on a big stack */
    lean_internal_set_thread_stack_size((size_t)1 << 33);
    lean_object *res = lean_run_main(idr_run_main_thunk, argc, argv);
    fflush(stdout);
    /* like Chez: the program ends when main returns, even if other threads
       are still running (so we don't finalize/wait for the task manager) */
    if (lean_io_result_is_ok(res)) exit(0);
    lean_io_result_show_error(res);
    exit(1);
}

/* ------------------------------------------------------------------ */
/* Buffers                                                             */

lean_obj_res idr_buf_new(int64_t size) {
    if (size < 0) size = 0;
    lean_object *b = lean_alloc_sarray(1, (size_t)size, (size_t)size);
    memset(lean_sarray_cptr(b), 0, (size_t)size);
    return b;
}
int64_t idr_buf_size(b_lean_obj_arg b) { return (int64_t)lean_sarray_size(b); }
lean_obj_res idr_buf_set_string(b_lean_obj_arg b, int64_t off, b_lean_obj_arg s) {
    memcpy(IDR_BUF(b) + off, lean_string_cstr(s), lean_string_size(s) - 1);
    return lean_box(0);
}
lean_obj_res idr_buf_get_string(b_lean_obj_arg b, int64_t off, int64_t len) {
    return lean_mk_string_from_bytes((const char *)IDR_BUF(b) + off, (size_t)len);
}
lean_obj_res idr_buf_copy(b_lean_obj_arg src, int64_t soff, int64_t len, b_lean_obj_arg dst, int64_t doff) {
    memmove(IDR_BUF(dst) + doff, IDR_BUF(src) + soff, (size_t)len);
    return lean_box(0);
}

/* ------------------------------------------------------------------ */
/* Clocks                                                              */
#include <time.h>
static lean_obj_res mk_clock(uint64_t s, uint64_t ns, uint8_t valid) {
    lean_object *c = lean_alloc_ctor(0, 0, 17);
    uint8_t *p = (uint8_t *)lean_ctor_obj_cptr(c);
    memcpy(p, &s, 8); memcpy(p + 8, &ns, 8); p[16] = valid;
    return c;
}
static lean_obj_res clock_of(clockid_t id) {
    struct timespec ts;
    if (clock_gettime(id, &ts) != 0) return mk_clock(0, 0, 0);
    return mk_clock((uint64_t)ts.tv_sec, (uint64_t)ts.tv_nsec, 1);
}
lean_obj_res idr_clock_utc(void) { return clock_of(CLOCK_REALTIME); }
lean_obj_res idr_clock_process(void) { return clock_of(CLOCK_PROCESS_CPUTIME_ID); }
lean_obj_res idr_clock_thread(void) { return clock_of(CLOCK_THREAD_CPUTIME_ID); }
lean_obj_res idr_clock_monotonic(void) { return clock_of(CLOCK_MONOTONIC); }
lean_obj_res idr_clock_invalid(void) { return mk_clock(0, 0, 0); }
int64_t idr_clock_valid(b_lean_obj_arg c) { return ((uint8_t *)lean_ctor_obj_cptr(c))[16]; }
uint64_t idr_clock_second(b_lean_obj_arg c) { uint64_t v; memcpy(&v, lean_ctor_obj_cptr(c), 8); return v; }
uint64_t idr_clock_nanosecond(b_lean_obj_arg c) { uint64_t v; memcpy(&v, (uint8_t *)lean_ctor_obj_cptr(c) + 8, 8); return v; }

/* ------------------------------------------------------------------ */
/* String iterators                                                    */

lean_obj_res idr_strit_to_string(b_lean_obj_arg ty, b_lean_obj_arg s, b_lean_obj_arg it, b_lean_obj_arg f) {
    (void)ty;
    size_t off = lean_unbox(it);
    size_t sz = lean_string_size(s) - 1;
    lean_object *rest = lean_mk_string_from_bytes(lean_string_cstr(s) + off, sz - off);
    lean_inc(f);
    return lean_apply_1(f, rest);
}

/* UnconsResult is list-shaped, so Idris compiles it as _builtin.NIL/CONS:
   EOF = box(0); Character c it = ctor 1 with two boxed fields (c, it) */
lean_obj_res idr_strit_next(b_lean_obj_arg s, b_lean_obj_arg it) {
    size_t off = lean_unbox(it);
    size_t sz = lean_string_size(s) - 1;
    if (off >= sz) return lean_box(0);
    const unsigned char *p = (const unsigned char *)lean_string_cstr(s) + off;
    uint32_t c = utf8_decode(p);
    lean_object *r = lean_alloc_ctor(1, 2, 0);
    lean_ctor_set(r, 0, idr_box_u32(c));
    lean_ctor_set(r, 1, lean_box(off + utf8_len_at(p)));
    return r;
}

/* ------------------------------------------------------------------ */
/* Concurrency                                                         */
#include <pthread.h>
#include <semaphore.h>
#include <errno.h>
#include <sys/time.h>

static _Thread_local lean_object *g_thread_data = NULL;
static _Thread_local int64_t g_thread_id = -1;
static int64_t g_next_thread_id = 1;

/* entry of a forked thread: install the inherited thread data, run prog */
static lean_object *idr_fork_entry(lean_object *env, lean_object *unit) {
    lean_object *prog = lean_ctor_get(env, 0);
    lean_object *data = lean_ctor_get(env, 1);
    lean_inc(prog);
    if (!lean_is_scalar(data)) { lean_inc(data); g_thread_data = data; }
    lean_dec(env);
    return lean_apply_1(prog, unit);
}

lean_obj_res idr_fork(b_lean_obj_arg prog) {
    lean_object *env = lean_alloc_ctor(0, 2, 0);
    lean_inc(prog);
    lean_ctor_set(env, 0, prog);
    lean_object *data = g_thread_data ? g_thread_data : lean_box(0);
    lean_inc(data);
    lean_ctor_set(env, 1, data);
    lean_object *c = lean_alloc_closure((void *)idr_fork_entry, 2, 1);
    lean_closure_set(c, 0, env);
    /* keep_alive: Idris threads run even if their id is dropped */
    return lean_task_spawn_core(c, IDR_DEDICATED_PRIO, true);
}

lean_obj_res idr_set_thread_data(b_lean_obj_arg v) {
    lean_inc(v);
    if (g_thread_data) lean_dec(g_thread_data);
    g_thread_data = v;
    return lean_box(0);
}
lean_obj_res idr_get_thread_data(void) {
    if (!g_thread_data) return lean_box(0);
    lean_inc(g_thread_data);
    return g_thread_data;
}
int64_t idr_get_thread_id(void) {
    if (g_thread_id < 0) g_thread_id = __atomic_fetch_add(&g_next_thread_id, 1, __ATOMIC_SEQ_CST);
    return g_thread_id;
}
void idr_set_main_thread(void) { g_thread_id = 0; }

#define BOXP(p) idr_box_ptr(p)
#define UNBOXP(T, o) ((T *)idr_unbox_ptr(o))

lean_obj_res idr_mutex_new(void) {
    pthread_mutex_t *m = malloc(sizeof *m);
    pthread_mutexattr_t a;
    pthread_mutexattr_init(&a);
    pthread_mutexattr_settype(&a, PTHREAD_MUTEX_RECURSIVE);
    pthread_mutex_init(m, &a);
    return BOXP(m);
}
lean_obj_res idr_mutex_acquire(b_lean_obj_arg m) { pthread_mutex_lock(UNBOXP(pthread_mutex_t, m)); return lean_box(0); }
lean_obj_res idr_mutex_release(b_lean_obj_arg m) { pthread_mutex_unlock(UNBOXP(pthread_mutex_t, m)); return lean_box(0); }

lean_obj_res idr_cond_new(void) {
    pthread_cond_t *c = malloc(sizeof *c);
    pthread_cond_init(c, NULL);
    return BOXP(c);
}
lean_obj_res idr_cond_wait(b_lean_obj_arg c, b_lean_obj_arg m) {
    pthread_cond_wait(UNBOXP(pthread_cond_t, c), UNBOXP(pthread_mutex_t, m));
    return lean_box(0);
}
static void deadline(struct timespec *ts, int64_t usec) {
    clock_gettime(CLOCK_REALTIME, ts);
    ts->tv_sec += usec / 1000000;
    ts->tv_nsec += (usec % 1000000) * 1000;
    if (ts->tv_nsec >= 1000000000) { ts->tv_sec++; ts->tv_nsec -= 1000000000; }
}
lean_obj_res idr_cond_wait_timeout(b_lean_obj_arg c, b_lean_obj_arg m, int64_t usec) {
    struct timespec ts;
    deadline(&ts, usec);
    pthread_cond_timedwait(UNBOXP(pthread_cond_t, c), UNBOXP(pthread_mutex_t, m), &ts);
    return lean_box(0);
}
lean_obj_res idr_cond_signal(b_lean_obj_arg c) { pthread_cond_signal(UNBOXP(pthread_cond_t, c)); return lean_box(0); }
lean_obj_res idr_cond_broadcast(b_lean_obj_arg c) { pthread_cond_broadcast(UNBOXP(pthread_cond_t, c)); return lean_box(0); }

lean_obj_res idr_sem_new(int64_t n) {
    sem_t *s = malloc(sizeof *s);
    sem_init(s, 0, (unsigned)n);
    return BOXP(s);
}
lean_obj_res idr_sem_post(b_lean_obj_arg s) { sem_post(UNBOXP(sem_t, s)); return lean_box(0); }
lean_obj_res idr_sem_wait(b_lean_obj_arg s) {
    while (sem_wait(UNBOXP(sem_t, s)) != 0 && errno == EINTR) {}
    return lean_box(0);
}

lean_obj_res idr_barrier_new(int64_t n) {
    pthread_barrier_t *b = malloc(sizeof *b);
    pthread_barrier_init(b, NULL, (unsigned)n);
    return BOXP(b);
}
lean_obj_res idr_barrier_wait(b_lean_obj_arg b) { pthread_barrier_wait(UNBOXP(pthread_barrier_t, b)); return lean_box(0); }

typedef struct chan_node { lean_object *v; struct chan_node *next; } chan_node;
typedef struct { pthread_mutex_t m; pthread_cond_t c; chan_node *head, *tail; } chan;

lean_obj_res idr_chan_new(void) {
    chan *c = calloc(1, sizeof *c);
    pthread_mutex_init(&c->m, NULL);
    pthread_cond_init(&c->c, NULL);
    return BOXP(c);
}
lean_obj_res idr_chan_put(b_lean_obj_arg co, b_lean_obj_arg v) {
    chan *c = UNBOXP(chan, co);
    lean_inc(v);
    if (!lean_is_scalar(v)) lean_mark_mt(v);   /* crosses threads */
    chan_node *n = malloc(sizeof *n);
    n->v = v; n->next = NULL;
    pthread_mutex_lock(&c->m);
    if (c->tail) c->tail->next = n; else c->head = n;
    c->tail = n;
    pthread_cond_signal(&c->c);
    pthread_mutex_unlock(&c->m);
    return lean_box(0);
}
static lean_object *chan_pop(chan *c) {
    chan_node *n = c->head;
    c->head = n->next;
    if (!c->head) c->tail = NULL;
    lean_object *v = n->v;
    free(n);
    return v;
}
lean_obj_res idr_chan_get(b_lean_obj_arg co) {
    chan *c = UNBOXP(chan, co);
    pthread_mutex_lock(&c->m);
    while (!c->head) pthread_cond_wait(&c->c, &c->m);
    lean_object *v = chan_pop(c);
    pthread_mutex_unlock(&c->m);
    return v;
}
static lean_obj_res mk_just(lean_object *v) {
    lean_object *j = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(j, 0, v);
    return j;
}
lean_obj_res idr_chan_get_nb(b_lean_obj_arg co) {
    chan *c = UNBOXP(chan, co);
    pthread_mutex_lock(&c->m);
    lean_object *r = c->head ? mk_just(chan_pop(c)) : lean_box(0);
    pthread_mutex_unlock(&c->m);
    return r;
}
lean_obj_res idr_chan_get_timeout(b_lean_obj_arg co, int64_t msec) {
    chan *c = UNBOXP(chan, co);
    struct timespec ts;
    deadline(&ts, msec * 1000);
    pthread_mutex_lock(&c->m);
    int rc = 0;
    while (!c->head && rc != ETIMEDOUT) rc = pthread_cond_timedwait(&c->c, &c->m, &ts);
    lean_object *r = c->head ? mk_just(chan_pop(c)) : lean_box(0);
    pthread_mutex_unlock(&c->m);
    return r;
}

lean_obj_res idr_future_new(b_lean_obj_arg f) {
    lean_inc(f);
    return lean_task_spawn_core(f, IDR_DEDICATED_PRIO, true);
}
lean_obj_res idr_future_await(b_lean_obj_arg t) {
    lean_object *v = lean_task_get(t);
    lean_inc(v);
    return v;
}
