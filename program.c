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
    int sign = p >> 63;
    sign |= (sign << 1) | (sign << 2);
    return (p >> 3) | (sign << 61);
}
ptr_t make_ptr_int(long x, tag_t tag) { return x << 3 | tag; }
ptr_t make_ptr_ptr(ptr_t *x, tag_t tag) { return ((intptr_t)x) | tag; }

#define LOAD(p, offset) (*(ptr_ptr(p) + offset))
#define STORE(p, offset, value) (*(ptr_ptr(p) + offset) = value)

ptr_t *fromspace, *alloc, *tospace;
ptr_t obarray;

const long heap_size = 4ll << 20;

#define FAIL(...)                     \
    do {                              \
        fprintf(stderr, __VA_ARGS__); \
        fprintf(stderr, "\n");        \
        exit(1);                      \
    } while (0)

size_t obj_size(ptr_t p) {
    size_t len;
    switch (ptr_tag(LOAD(p, 0))) {
        case 0:
            switch (ptr_int(LOAD(p, 0))) {
                case 0:
                    // pair
                    return 3;
                case 1:
                    // proc
                    return 3;
                case 2:
                    // flonum
                    return 2;
                case 3:
                    // box
                    return 2;
                default:
                    FAIL("tombstone in tospace");
            }
            break;
        case 1:
            return 1;
        case 2:
            len = ptr_int(LOAD(p, 0));
            return len + 1;
        case 3:
            len = ptr_int(LOAD(p, 0));
            return len + 1;
        default:
            FAIL("unknown heap object");
    }
}

ptr_t copy(ptr_t p) {
    if (ptr_tag(p) != T_HEAP) return p;
    ptrdiff_t offset = ptr_ptr(p) - fromspace;
    if (offset < 0 || offset >= heap_size) return p;
    if (LOAD(p, 0) == make_ptr_int(4, 0)) return LOAD(p, 1);
    size_t size = obj_size(p);
    memcpy(alloc, ptr_ptr(p), sizeof(ptr_t) * size);
    STORE(p, 0, make_ptr_int(4, 0));
    STORE(p, 1, make_ptr_ptr(alloc, 0));
    ptr_t *dst = alloc;
    alloc += size;
    return make_ptr_ptr(dst, T_HEAP);
}

void start_gc() { alloc = tospace; }

void finish_gc() {
    ptr_t *scan = tospace;

    size_t len;
    while (scan < alloc) {
        size_t size = obj_size(make_ptr_ptr(scan, T_HEAP));
        switch (ptr_tag(*scan)) {
            case 0:
                switch (ptr_int(*scan)) {
                    case 0:
                        // pair
                        scan[1] = copy(scan[1]);
                        scan[2] = copy(scan[2]);
                        break;
                    case 1:
                        // proc
                        scan[2] = copy(scan[2]);
                    case 2:
                        // flonum
                        break;
                    case 3:
                        // box
                        scan[1] = copy(scan[1]);
                        break;
                    default:
                        FAIL("tombstone in tospace");
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
                FAIL("unknown heap object");
        }
        scan += size;
    }

    ptr_t *tmp = fromspace;
    fromspace = tospace;
    tospace = tmp;
}

ptr_t allocate(size_t size) {
    ptr_t dst = make_ptr_ptr(alloc, T_HEAP);
    alloc += size;
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

ptr_t obarray;
long sym_cnt;

void init_obarray() {
    obarray = allocate(STRHASH_P + 1);
    STORE(obarray, 0, make_ptr_int(STRHASH_P, 4));
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
            h = (h * STRHASH_E % STRHASH_P + byte) % STRHASH_P;
        }
    }
    ptr_t p = LOAD(obarray, h + 1);
    while (p != make_ptr_int(2, T_SPECIAL)) {
        if (LOAD(car(car(p)), 0) == LOAD(str, 0) &&
            memcmp(ptr_ptr(car(car(p))) + 1, ptr_ptr(str) + 1,
                   ptr_int(LOAD(str, 0))) == 0) {
            return cdr(car(p));
        }
        p = cdr(p);
    }
    ptr_t ret = make_ptr_int(sym_cnt, T_SYM);
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

ptr_t s_os_exit(ptr_t x) { exit(ptr_int(x)); }

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
        k, make_ptr_int(x == make_ptr_int(2, T_SPECIAL), T_SPECIAL));
}

ptr_t s_error(ptr_t err) {
    int len = ptr_int(LOAD(err, 0));
    for (int i = 1; i <= len; i++) fputc(LOAD(err, i), stderr);
    fprintf(stderr, "\n");
    exit(1);
}

// DECLS //

int main() {
    fromspace = malloc(heap_size * sizeof(ptr_t));
    tospace = malloc(heap_size * sizeof(ptr_t));
    alloc = fromspace;

    init_obarray();

    // prepare constants

    // BODY //
}
