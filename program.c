#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef int64_t ptr_t;

typedef enum tag_t {
    T_NUM = 0,
    T_CHAR,
    T_SYM,
    T_SPECIAL,
    T_HEAP,
} tag_t;

tag_t ptr_tag(ptr_t p) { return p & 7; }
ptr_t *ptr_ptr(ptr_t p) { return (ptr_t *)(p & (~7ll)); }
int64_t ptr_int(ptr_t p) {
    int64_t sign = p >> 63;
    sign |= (sign << 1) | (sign << 2);
    return (p >> 3) | (sign << 61);
}
ptr_t make_ptr_int(long x, tag_t tag) { return x << 3 | tag; }
ptr_t make_ptr_ptr(ptr_t *x, tag_t tag) { return ((intptr_t)x) | tag; }

#define LOAD(p, offset) (*(ptr_ptr(p) + offset))
#define STORE(p, offset, value) (*(ptr_ptr(p) + offset) = value)

ptr_t *base, *fromspace, *alloc, *tospace;
ptr_t obarray;

const long heap_size = 1ll << 20;
const int always_gc = 1;

int runcnt = 0;

#define FAIL(...)                     \
    do {                              \
        fprintf(stderr, __VA_ARGS__); \
        fprintf(stderr, "\n");        \
        abort();                      \
    } while (0)

const int p0size[] = {3, 3, 2, 2};

size_t max_size_t(size_t a, size_t b) { return a < b ? b : a; }

size_t obj_size(ptr_t p) {
    // fprintf(stderr, "%llx %llx %llx\n", p, LOAD(p, 0), alloc);
    switch (ptr_tag(LOAD(p, 0))) {
        case 0:
            if (ptr_int(LOAD(p, 0)) >= 4) FAIL("unknown tag 0 object");
            return p0size[ptr_int(LOAD(p, 0))];
        case 1:
            return 1;
        case 2:
        case 3:
            return max_size_t(ptr_int(LOAD(p, 0)) + 1, 2);
        default:
            FAIL("unknown heap object");
    }
}

ptr_t copy(ptr_t p) {
    if (ptr_tag(p) != T_HEAP) return p;
    ptrdiff_t offset = ptr_ptr(p) - fromspace;
    if (offset < 0 || offset >= heap_size) return p;
    if (LOAD(p, 0) == make_ptr_int(4, 0)) return LOAD(p, 1);
    // fprintf(stderr, "copy %llx\n", p);
    size_t size = obj_size(p);
    memcpy(alloc, ptr_ptr(p), sizeof(ptr_t) * size);
    STORE(p, 0, make_ptr_int(4, 0));
    STORE(p, 1, make_ptr_ptr(alloc, T_HEAP));
    ptr_t *dst = alloc;
    alloc += size;
    return make_ptr_ptr(dst, T_HEAP);
}

void start_gc() { alloc = tospace; }

void dump_memory() {
    fprintf(stderr, "from: %llx\n", fromspace);
    for (ptr_t *p = base; p < base + heap_size; p++)
        fprintf(stderr, "%llx: %llx\n", p, *p);
    fprintf(stderr, "---\n");
    for (ptr_t *p = base + heap_size; p < base + 2 * heap_size; p++)
        fprintf(stderr, "%llx: %llx\n", p, *p);
}

void finish_gc() {
    ptr_t *scan = tospace;
    // dump_memory();

    size_t len;
    while (scan < alloc) {
        size_t size = obj_size(make_ptr_ptr(scan, T_HEAP));
        ptr_t tag = ptr_tag(*scan), ct = ptr_int(*scan);
        // fprintf(stderr, "scan: %llx, %llx, %llx, %lld\n", scan, alloc, *scan,
        //         size);
        switch (tag) {
            case 0:
                if (ct == 0) {
                    // pair
                    scan[1] = copy(scan[1]);
                    scan[2] = copy(scan[2]);
                } else if (ct == 1) {
                    // proc
                    scan[2] = copy(scan[2]);
                } else if (ct == 2) {
                    // flonum
                } else if (ct == 3) {
                    // box
                    scan[1] = copy(scan[1]);
                } else {
                    FAIL("tombstone in tospace during copy");
                }
                break;
            case 1:
                break;
            case 2:
                break;
            case 3:
                len = ptr_int(scan[0]);
                for (size_t i = 0; i < len; i++)
                    scan[i + 1] = copy(scan[i + 1]);
                break;
            default:
                FAIL("unknown heap object during scan");
        }
        scan += size;
    }
    // fprintf(stderr, "%llx=%llx\n", scan, alloc);

    ptr_t *tmp = fromspace;
    fromspace = tospace;
    tospace = tmp;

    // fprintf(stderr, "live memory: %lld words\n", alloc - fromspace);
}

ptr_t allocate(size_t size) {
    size = max_size_t(size, 2);
    ptr_t dst = make_ptr_ptr(alloc, T_HEAP);
    alloc += size;
    if (alloc >= fromspace + heap_size) FAIL("memory exhaustion");
    return dst;
}

ptr_t s_make_closure(void *code, ptr_t closure) {
    ptr_t ret = allocate(3);
    STORE(ret, 0, make_ptr_int(1, 0));
    STORE(ret, 1, (ptr_t)code);
    STORE(ret, 2, closure);
    return ret;
}

ptr_t s_make_ref(ptr_t val) {
    ptr_t ret = allocate(2);
    STORE(ret, 0, make_ptr_int(3, 0));
    STORE(ret, 1, val);
    return ret;
}

ptr_t make_ref() {
    ptr_t ret = allocate(2);
    STORE(ret, 0, make_ptr_int(3, 0));
    STORE(ret, 1, make_ptr_int(2, T_SPECIAL));
    return ret;
}

ptr_t s_ref_set_bang_(ptr_t ref, ptr_t val) {
    STORE(ref, 1, val);
    return make_ptr_int(0, T_SPECIAL);
}

ptr_t s_ref(ptr_t ref) { return LOAD(ref, 1); }

ptr_t cons(ptr_t car, ptr_t cdr) {
    ptr_t ret = allocate(3);
    STORE(ret, 0, make_ptr_int(0, 0));
    STORE(ret, 1, car);
    STORE(ret, 2, cdr);
    return ret;
}

#define STRHASH_P 10007
#define STRHASH_E 257

ptr_t obarray, obarray_t[STRHASH_P + 1];
long sym_cnt;

void init_obarray() {
    obarray = make_ptr_ptr(obarray_t, T_HEAP);
    STORE(obarray, 0, make_ptr_int(STRHASH_P, 3));
    for (int i = 0; i < STRHASH_P; i++)
        STORE(obarray, i + 1, make_ptr_int(2, T_SPECIAL));
    sym_cnt = 0;
}

ptr_t car(ptr_t x) { return LOAD(x, 1); }
ptr_t cdr(ptr_t x) { return LOAD(x, 2); }

ptr_t intern(ptr_t str) {
    int h = 0;
    for (int i = 0; i < ptr_int(LOAD(str, 0)); i++) {
        long ch = ptr_int(LOAD(str, i + 1));
        for (int j = 0; j < 8; j++) {
            int byte = ch >> (j * 8) & 255;
            h = (h * STRHASH_E % STRHASH_P + byte + 1) % STRHASH_P;
        }
    }
    ptr_t p = LOAD(obarray, h + 1);
    while (p != make_ptr_int(2, T_SPECIAL)) {
        if (LOAD(car(car(p)), 0) == LOAD(str, 0) &&
            memcmp(ptr_ptr(car(car(p))) + 1, ptr_ptr(str) + 1,
                   ptr_int(LOAD(str, 0)) * sizeof(ptr_t)) == 0) {
            return cdr(car(p));
        }
        p = cdr(p);
    }
    ptr_t ret = make_ptr_int(sym_cnt++, T_SYM);
    STORE(obarray, h + 1, cons(cons(str, ret), LOAD(obarray, h + 1)));
    return ret;
}

ptr_t bitrep(double x) {
    ptr_t y;
    memcpy(&y, &x, sizeof(double));
    return y;
}

ptr_t make_flonum(double x) {
    ptr_t ret = allocate(2);
    STORE(ret, 0, make_ptr_int(2, 0));
    STORE(ret, 1, bitrep(x));
    return ret;
}

ptr_t s_os_exit(ptr_t x) {
    // dump_memory();
    exit(ptr_int(x));
}

ptr_t s_closure_ref(ptr_t c, ptr_t i) {
    ptr_t v = LOAD(c, 2);
    return LOAD(v, ptr_int(i) + 1);
}

ptr_t s_builtin_car(ptr_t k, ptr_t x) {
    return ((ptr_t(*)(ptr_t, ptr_t))LOAD(k, 1))(k, car(x));
}

ptr_t s_builtin_cdr(ptr_t k, ptr_t x) {
    return ((ptr_t(*)(ptr_t, ptr_t))LOAD(k, 1))(k, cdr(x));
}

ptr_t s_builtin_cons(ptr_t k, ptr_t car, ptr_t cdr) {
    return ((ptr_t(*)(ptr_t, ptr_t))LOAD(k, 1))(k, cons(car, cdr));
}

ptr_t s_builtin_null_p_(ptr_t k, ptr_t x) {
    return ((ptr_t(*)(ptr_t, ptr_t))LOAD(k, 1))(
        k, make_ptr_int(x == make_ptr_int(2, T_SPECIAL) ? 1 : 0, T_SPECIAL));
}

ptr_t s_error(ptr_t err) {
    int len = ptr_int(LOAD(err, 0));
    for (int i = 1; i <= len; i++) fputc(LOAD(err, i), stderr);
    fprintf(stderr, "\n");
    exit(1);
}

ptr_t s_putchar(ptr_t c) {
    printf("%c", ptr_int(c));
    return make_ptr_int(1, T_SPECIAL);
}

// DECLS //
int main() {
    base = fromspace = malloc(2 * heap_size * sizeof(ptr_t));
    tospace = fromspace + heap_size;
    alloc = fromspace;

    init_obarray();

    // prepare constants
    // BODY //
}
