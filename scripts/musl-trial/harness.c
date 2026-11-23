/* Sanity harness for the musl trial (not a proof): links the objects assembled from
 * the files in examples/musl/ and checks each function against a plain reference loop on a few inputs,
 * including unaligned pointers and lengths around the word-size thresholds.
 * Freestanding: own _start, exit and write via ecall (the environment's syscalls 64 and 93). */
typedef unsigned long size_t; typedef long ssize_t;
#define NULL ((void *)0)
long labs(long); int memcmp(const void *, const void *, size_t); int bcmp(const void *, const void *, size_t);
void *memrchr(const void *, int, size_t); void *memchr(const void *, int, size_t);
size_t strnlen(const char *, size_t); int strncmp(const char *, const char *, size_t);
void swab(const void *, void *, ssize_t); void bzero(void *, size_t); void *memset(void *, int, size_t);
void *memcpy(void *, const void *, size_t); void *memccpy(void *, const void *, int, size_t);
void *memmove(void *, const void *, size_t); size_t strlen(const char *);
typedef struct FILE FILE; size_t fwrite(const void *, size_t, size_t, FILE *);

static long sys3(long n, long a, long b, long c) {
  register long a0 asm("a0") = a, a1 asm("a1") = b, a2 asm("a2") = c, a7 asm("a7") = n;
  asm volatile("ecall" : "+r"(a0) : "r"(a1), "r"(a2), "r"(a7) : "memory"); return a0;
}
static size_t slen(const char *s) { size_t n = 0; while (s[n]) n++; return n; }
static void put(const char *s) { sys3(64, 1, (long)s, (long)slen(s)); }
static int fails;
static void check(int ok, const char *what) { if (!ok) { put("FAIL "); put(what); put("\n"); fails++; } }

static unsigned char A[200], B[200], C[200];
static unsigned rnd = 12345;
static unsigned char r8(void) { rnd = rnd * 1103515245 + 12345; return rnd >> 16; }
static void fill(unsigned char *p, size_t n) { for (size_t i = 0; i < n; i++) p[i] = r8() % 4; }

static int ref_cmp(const unsigned char *l, const unsigned char *r, size_t n) {
  for (size_t i = 0; i < n; i++) if (l[i] != r[i]) return l[i] - r[i]; return 0; }
static int sgn(int x) { return (x > 0) - (x < 0); }

/* Stubs for fwrite's callees (unsafe contracts in the trial). FILE layout: lock at +140. */
struct FILE { char pad[140]; int lock; };
static size_t stub_ret;
size_t __fwritex(const unsigned char *s, size_t l, FILE *f) { (void)s; (void)f; return stub_ret < l ? stub_ret : l; }
int __lockfile(FILE *f) { (void)f; return 1; }
void __unlockfile(FILE *f) { (void)f; }

static const size_t lens[] = {0, 1, 2, 3, 5, 7, 8, 9, 15, 16, 17, 23, 24, 25, 31, 32, 33, 40, 63, 64, 65, 100};
#define NL (sizeof lens / sizeof lens[0])

void _start_c(void) {
  check(labs(-5) == 5 && labs(7) == 7 && labs(0) == 0, "labs");
  for (int t = 0; t < 400; t++) {
    size_t n = lens[t % NL], oa = r8() % 9, ob = r8() % 9;
    fill(A, sizeof A); fill(B, sizeof B);
    if (t & 1) for (size_t i = 0; i < n; i++) B[ob + i] = A[oa + i];   /* equal prefix often */
    if (t & 2 && n) B[ob + r8() % n] ^= 1;
    check(sgn(memcmp(A + oa, B + ob, n)) == sgn(ref_cmp(A + oa, B + ob, n)), "memcmp");
    check((bcmp(A + oa, B + ob, n) == 0) == (ref_cmp(A + oa, B + ob, n) == 0), "bcmp");
    int c = r8() % 4;
    unsigned char *e = NULL; for (size_t i = 0; i < n; i++) if (A[oa + i] == c) { e = A + oa + i; break; }
    check(memchr(A + oa, c + 256, n) == e, "memchr");
    unsigned char *er = NULL; for (size_t i = n; i-- > 0;) if (A[oa + i] == c) { er = A + oa + i; break; }
    check(memrchr(A + oa, c, n) == er, "memrchr");
    size_t z = n; for (size_t i = 0; i < n; i++) if (!A[oa + i]) { z = i; break; }
    check(strnlen((char *)A + oa, n) == z, "strnlen");
    int rs = 0; for (size_t i = 0; i < n; i++) { rs = A[oa+i] - B[ob+i]; if (rs || !A[oa+i]) break; }
    check(sgn(strncmp((char *)A + oa, (char *)B + ob, n)) == sgn(rs), "strncmp");
    /* writes: compare the whole buffer so out-of-range writes show up */
    fill(C, sizeof C); for (size_t i = 0; i < sizeof C; i++) B[i] = C[i];
    for (size_t i = 0; i < n; i++) B[ob + i] = (unsigned char)(c + 7);
    check(memset(C + ob, c + 7 + 256, n) == C + ob && !ref_cmp(B, C, sizeof C), "memset");
    for (size_t i = 0; i < n; i++) B[ob + i] = 0; bzero(C + ob, n);
    check(!ref_cmp(B, C, sizeof C), "bzero");
    for (size_t i = 0; i < n; i++) B[ob + i] = A[oa + i];
    check(memcpy(C + ob, A + oa, n) == C + ob && !ref_cmp(B, C, sizeof C), "memcpy");
    fill(C, sizeof C); for (size_t i = 0; i < sizeof C; i++) B[i] = C[i];
    unsigned char *pe = NULL; for (size_t i = 0; i < n; i++) { B[ob+i] = A[oa+i]; if (A[oa+i] == c) { pe = C + ob + i + 1; break; } }
    check(memccpy(C + ob, A + oa, c, n) == pe && !ref_cmp(B, C, sizeof C), "memccpy");
    fill(C, sizeof C); for (size_t i = 0; i < sizeof C; i++) B[i] = C[i];
    for (size_t i = 0; i + 1 < n; i += 2) { B[ob+i] = A[oa+i+1]; B[ob+i+1] = A[oa+i]; }
    swab(A + oa, C + ob, (ssize_t)n); check(!ref_cmp(B, C, sizeof C), "swab");
    /* memmove within one buffer, both directions */
    size_t d = 16 + r8() % 20, s = 16 + r8() % 20;
    fill(C, sizeof C); for (size_t i = 0; i < sizeof C; i++) B[i] = C[i];
    for (size_t i = 0; i < n; i++) A[i] = C[s + i];
    for (size_t i = 0; i < n; i++) B[d + i] = A[i];
    check(memmove(C + d, C + s, n) == C + d && !ref_cmp(B, C, sizeof C), "memmove");
    for (size_t i = 0; i < n; i++) A[oa + i] = 1 + r8() % 200; A[oa + n] = 0;
    check(strlen((char *)A + oa) == n, "strlen");
  }
  FILE f = {0}; f.lock = -1; stub_ret = 1000;
  check(fwrite(A, 4, 10, &f) == 10, "fwrite full");
  stub_ret = 13; check(fwrite(A, 4, 10, &f) == 3, "fwrite partial");
  f.lock = 0; check(fwrite(A, 4, 0, &f) == 0 && fwrite(A, 0, 9, &f) == 0, "fwrite zero");
  put(fails ? "harness: FAILED\n" : "harness: all checks passed\n");
  sys3(93, fails != 0, 0, 0);
}
asm(".globl _start\n_start:\n la sp, stack_top\n call _start_c\n"
    ".bss\n.balign 16\n.space 65536\nstack_top:\n.text\n");
