/* rhshim.so -- LD_PRELOAD helper for running Lean on machines with a low vm.max_map_count.
 *
 * Problem.  Lean mmaps every imported .olean (plus .olean.server/.olean.private/.ir/.ir.sig for
 * module-system libraries such as Mathlib) as its own mapping.  `import Mathlib` alone costs ~52,000
 * mappings; Linux's default limit is 65,530 per process and cannot be raised without root (LUMI).
 * When mmap fails Lean already falls back to malloc()+read()+relocation (src/library/module.cpp), but
 * at the limit malloc cannot obtain memory either (it needs a new mapping), so the import fails with
 * "failed to read file".
 *
 * What this does.  It does not change what Lean loads, only where the bytes live:
 *   1. reserves one large anonymous region at startup (a single mapping, untouched pages cost nothing);
 *   2. refuses file mappings smaller than RH_MIN_MAP bytes (default 65536) and any file mapping once
 *      RH_MAP_LIMIT (default 58000) of them exist, so that Lean takes its own read fallback for those.
 *      Most of Mathlib's ~52,000 files are tiny (42,000 are under 4 KB, 16 MB in total), so reading the
 *      small ones costs a few hundred MB per process and frees most of the mapping budget;
 *   3. serves malloc/calloc/realloc/memalign and anonymous mmap requests from the reserved region
 *      when (and only when) the normal allocator fails.
 * build:  gcc -O2 -fPIC -shared -o rhshim.so rhshim.c
 */
#define _GNU_SOURCE
#include <errno.h>
#include <malloc.h>
#include <stdarg.h>
#include <stdatomic.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/syscall.h>
#include <unistd.h>

extern void *__libc_malloc(size_t);
extern void __libc_free(void *);
extern void *__libc_realloc(void *, size_t);
extern void *__libc_calloc(size_t, size_t);
extern void *__libc_memalign(size_t, size_t);

#define HDR 32
#define PG 4096UL
static char *arena;
static size_t arena_sz;
static _Atomic size_t arena_off;
static _Atomic long file_maps;
static long map_limit = 58000;
static size_t min_map = 65536;

static void *sys_mmap(void *a, size_t l, int p, int f, int fd, off_t o) {
    return (void *)syscall(SYS_mmap, a, l, p, f, fd, o);
}

__attribute__((constructor(101))) static void rh_init(void) {
    const char *s = getenv("RH_MAP_LIMIT");
    if (s && *s) map_limit = atol(s);
    s = getenv("RH_MIN_MAP");
    if (s && *s) min_map = (size_t)atol(s);
    size_t gib = 1024;
    s = getenv("RH_ARENA_GIB");
    if (s && *s) gib = (size_t)atol(s);
    size_t sz = gib << 30;
    void *p = sys_mmap(NULL, sz, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
    if (p != MAP_FAILED) { arena = p; arena_sz = sz; }
}

static int in_arena(const void *p) {
    return arena && (const char *)p >= arena && (const char *)p < arena + arena_sz;
}

static void *arena_take(size_t n, size_t align) {
    if (!arena) return NULL;
    size_t cur = atomic_load(&arena_off), start, end;
    do {
        start = (cur + align - 1) & ~(align - 1);
        end = start + n;
        if (end < start || end > arena_sz) return NULL;
    } while (!atomic_compare_exchange_weak(&arena_off, &cur, end));
    return arena + start;
}

static void arena_release(void *p, size_t n) {          /* give pages back, keep the single mapping */
    uintptr_t a = ((uintptr_t)p + PG - 1) & ~(PG - 1), b = ((uintptr_t)p + n) & ~(PG - 1);
    if (b > a) syscall(SYS_madvise, (void *)a, b - a, MADV_DONTNEED);
}

static void *arena_malloc(size_t n, size_t align) {     /* align: power of two >= 16 */
    char *q = arena_take(n + HDR + align, 16);
    if (!q) { errno = ENOMEM; return NULL; }
    char *u = (char *)(((uintptr_t)q + HDR + align - 1) & ~(uintptr_t)(align - 1));
    ((size_t *)u)[-1] = n;
    return u;
}

/* ---- malloc family: normal allocator first, reserved region only on failure ---- */
void *malloc(size_t n) {
    void *p = __libc_malloc(n);
    return (p || !n) ? p : arena_malloc(n, 16);
}
void free(void *p) {
    if (!p) return;
    if (in_arena(p)) { arena_release((char *)p - HDR, ((size_t *)p)[-1] + HDR); return; }
    __libc_free(p);
}
void *calloc(size_t a, size_t b) {
    void *p = __libc_calloc(a, b);
    if (p || !a || !b) return p;
    if (b && a > SIZE_MAX / b) { errno = ENOMEM; return NULL; }
    p = arena_malloc(a * b, 16);                        /* fresh or MADV_DONTNEED'ed pages read as zero... */
    if (p) memset(p, 0, a * b);                         /* ...but a reused partial page may not: clear */
    return p;
}
void *realloc(void *p, size_t n) {
    if (!p) return malloc(n);
    if (in_arena(p)) {
        size_t old = ((size_t *)p)[-1];
        if (n <= old) return p;
        void *q = malloc(n);
        if (!q) return NULL;
        memcpy(q, p, old);
        free(p);
        return q;
    }
    void *r = __libc_realloc(p, n);
    if (r || !n) return r;
    size_t old = malloc_usable_size(p);
    void *q = arena_malloc(n, 16);
    if (!q) return NULL;
    memcpy(q, p, old < n ? old : n);
    __libc_free(p);
    return q;
}
void *memalign(size_t al, size_t n) {
    void *p = __libc_memalign(al, n);
    return (p || !n) ? p : arena_malloc(n, al < 16 ? 16 : al);
}
void *aligned_alloc(size_t al, size_t n) { return memalign(al, n); }
int posix_memalign(void **out, size_t al, size_t n) {
    void *p = memalign(al, n);
    if (!p && n) return ENOMEM;
    *out = p;
    return 0;
}
size_t malloc_usable_size(void *p) {
    extern size_t __malloc_usable_size(void *) __attribute__((weak));
    if (!p) return 0;
    if (in_arena(p)) return ((size_t *)p)[-1];
    /* call glibc's implementation without recursing into this wrapper */
    static size_t (*real)(void *);
    if (!real) {
        extern void *dlsym(void *, const char *);
        real = (size_t (*)(void *))dlsym((void *)-1L /* RTLD_NEXT */, "malloc_usable_size");
    }
    return real ? real(p) : 0;
}

/* ---- mmap family ---- */
void *mmap(void *addr, size_t len, int prot, int flags, int fd, off_t off) {
    int file = !(flags & MAP_ANONYMOUS) && fd >= 0;
    /* only Lean's import mappings use MAP_FIXED_NOREPLACE; shared libraries etc. are left alone */
    if (file && (flags & MAP_FIXED_NOREPLACE) && (len < min_map || atomic_load(&file_maps) >= map_limit)) {
        errno = ENOMEM;
        return MAP_FAILED;
    }
    void *p = sys_mmap(addr, len, prot, flags, fd, off);
    if (p != MAP_FAILED) {
        if (file) atomic_fetch_add(&file_maps, 1);
        return p;
    }
    if (errno == ENOMEM && (flags & MAP_ANONYMOUS) && !(flags & (MAP_FIXED | MAP_FIXED_NOREPLACE))) {
        void *q = arena_take((len + PG - 1) & ~(PG - 1), PG);
        if (q) return q;
        errno = ENOMEM;
    }
    return MAP_FAILED;
}
void *mmap64(void *addr, size_t len, int prot, int flags, int fd, off_t off) {
    return mmap(addr, len, prot, flags, fd, off);
}
int munmap(void *addr, size_t len) {
    if (in_arena(addr)) { arena_release(addr, len); return 0; }
    return (int)syscall(SYS_munmap, addr, len);
}
int mprotect(void *addr, size_t len, int prot) {
    if (in_arena(addr)) {                               /* never split the reserved mapping */
        if (prot == PROT_NONE) arena_release(addr, len);
        return 0;
    }
    return (int)syscall(SYS_mprotect, addr, len, prot);
}
void *mremap(void *old, size_t olds, size_t news, int flags, ...) {
    if (in_arena(old)) { errno = ENOMEM; return MAP_FAILED; }
    void *na = NULL;
    if (flags & MREMAP_FIXED) { va_list ap; va_start(ap, flags); na = va_arg(ap, void *); va_end(ap); }
    return (void *)syscall(SYS_mremap, old, olds, news, flags, na);
}
