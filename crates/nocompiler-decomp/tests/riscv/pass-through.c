/* The shape of musl's strtol (decompile test fixture, crates/nocompiler-decomp/tests/riscv.rs):
   f returns g's result unchanged, and one branch computes an address in a1 to store
   through. Build: see the comment in riscv.rs (fixture_pass_through). */
__attribute__((noinline)) long g(long *p) { return p[0] * 3 + 1; }

__attribute__((noinline)) long f(long *p, long *q) {
    long r = g(p);
    if (q)
        *q = p[1] + p[2];
    return r;
}

/* Tail calls to a function that returns nothing: neither caller returns anything. */
__attribute__((noinline)) void nothing(long *p) { if (p) *p = 0; }
__attribute__((noinline)) void tail_void(long *p) { nothing(p); }
__attribute__((noinline)) void maybe(long *p) { if (p) nothing(p); }

long data[4] = {1, 2, 3, 4};

/* musl's mal0_clear (src/malloc/mallocng, MIT): an inner loop whose two
   exits each set the cursor and go back to the outer loop's head. The loop
   continues there; neither exit needs a goto. */
__attribute__((noinline)) char *zero(char *p, unsigned long n) {
    for (unsigned long k = 0; k < n; k++) {
        ((volatile char *)p)[k] = 0;
    }
    return p;
}
typedef unsigned long __attribute__((__may_alias__)) T;
__attribute__((noinline)) unsigned long mal0_clear(char *p, unsigned long n) {
    const unsigned long pagesz = 4096;
    if (n < pagesz) {
        return n;
    }
    char *pp = p + n;
    unsigned long i = (unsigned long)pp & (pagesz - 1);
    for (;;) {
        pp = zero(pp - i, i);
        if ((unsigned long)(pp - p) < pagesz) {
            return pp - p;
        }
        for (i = pagesz; i; i -= 2 * sizeof(T), pp -= 2 * sizeof(T)) {
            if (((T *)pp)[-1] | ((T *)pp)[-2]) {
                break;
            }
        }
    }
}

/* mbedtls_mpi_lsb's shape: an inner loop with two exits, one a return and
   one back to the outer loop. The return is written in the inner loop and
   the way back is its end; neither needs a goto. */
__attribute__((noinline)) long first_bit(const unsigned *w, long n) {
    long count = 0;
    for (long i = 0; i < n; i++) {
        for (long j = 0; j < 32; j++, count++) {
            if ((w[i] >> j) & 1) {
                return count;
            }
        }
    }
    return 0;
}

/* A call result tested and then returned, with a call that does not return
   on the other path (micropython's mp_obj_len): the return gives the first
   call's result, not the second's. */
__attribute__((noinline)) long maybe_len(long *p) { return p ? p[1] : 0; }
__attribute__((noinline, noreturn)) void fail(long x) {
    for (;;) {
        data[0] = x;
    }
}
/* x509_crt_check_cn's shape: a test, then a call and a test of its result,
   both going to the same block (`if (a[0] != n || maybe_len(a) != 0)`).
   Assembly, so the blocks are these. */
long or_call(long *a, long n);
__asm__(".globl or_call\n"
        "or_call:\n"
        "  addi sp, sp, -16\n"
        "  sd ra, 8(sp)\n"
        "  sd s0, 0(sp)\n"
        "  mv s0, a0\n"
        "  ld t0, 0(a0)\n"
        "  bne t0, a1, 1f\n"
        "  call maybe_len\n"
        "  bnez a0, 1f\n"
        "  li a0, 0\n"
        "  j 2f\n"
        "1:\n"
        "  ld a0, 8(s0)\n"
        "2:\n"
        "  ld ra, 8(sp)\n"
        "  ld s0, 0(sp)\n"
        "  addi sp, sp, 16\n"
        "  ret\n");

/* mp_obj_gen_resume's shape: the first test's way to the shared block runs a
   block of its own first (`if (a[0]) { a[1] = x; goto L; } if (y == x) { L:
   ... }`), one condition `(a[0] != 0) ? (a[1] = x, 1) : (y == x)`. */
long pass_or(long *a, long x, long y);
__asm__(".globl pass_or\n"
        "pass_or:\n"
        "  ld t0, 0(a0)\n"
        "  beqz t0, 1f\n"
        "  sd a1, 8(a0)\n"
        "  j 2f\n"
        "1:\n"
        "  bne a2, a1, 3f\n"
        "2:\n"
        "  ld a0, 16(a0)\n"
        "  ret\n"
        "3:\n"
        "  li a0, 0\n"
        "  ret\n");

/* exit (93) does not come back: quit's walk stops at its ecall and does not
   run on into after_quit, which the assembler places right behind it. */
void quit(long status);
long after_quit(long x);
__asm__(".globl quit\n"
        "quit:\n"
        "  li a7, 93\n"
        "  ecall\n"
        ".globl after_quit\n"
        "after_quit:\n"
        "  addi a0, a0, 7\n"
        "  ret\n");

/* via_constant jumps to a constant address (lla: auipc, addi), maybe_len's:
   that is maybe_len's call. A jump through a pointer loaded from memory
   leaves the function: a tail
   call through a function pointer (micropython's fun_builtin_0_call). A jump
   through a 32-bit offset added to a base is a switch's table (here with no
   bound, so not read) and stays unresolved. */
long via_pointer(long *obj, long x);
long via_table(long i, long *table);
long via_arg(long a, long b, long (*f)(long, long));
long via_result(long *p);
long via_checked(long *obj);
long via_constant(long *p);
__asm__(".globl via_pointer\n"
        "via_pointer:\n"
        "  ld t1, 8(a0)\n"
        "  mv a0, a1\n"
        "  jr t1\n"
        ".globl via_arg\n"
        "via_arg:\n"
        "  jr a2\n"
        ".globl via_result\n"
        "via_result:\n"
        "  addi sp, sp, -16\n"
        "  sd ra, 8(sp)\n"
        "  call maybe_len\n"
        "  mv t1, a0\n"
        "  ld ra, 8(sp)\n"
        "  addi sp, sp, 16\n"
        "  jr t1\n"
        ".globl via_checked\n"
        "via_checked:\n"
        "  ld t1, 8(a0)\n"
        "  bnez t1, 1f\n"
        "  li a0, 0\n"
        "  ret\n"
        "1:\n"
        "  jr t1\n"
        ".globl via_constant\n"
        "via_constant:\n"
        "  lla t1, maybe_len\n"
        "  jr t1\n"
        ".globl via_table\n"
        "via_table:\n"
        "  sh2add a5, a0, a1\n"
        "  lw a5, 0(a5)\n"
        "  add a5, a5, a1\n"
        "  jr a5\n");

/* scope_check_to_close_over's shape: an inner search whose "found" exit runs
   a loop of its own and returns, and whose other exit goes on to the outer
   loop. The found region is written inside the inner loop; no goto. */
__attribute__((noinline)) long find_in_lists(long **lists, long key) {
    for (long **l = lists; *l; l++) {
        long *p = *l;
        for (long n = p[0]; n; n--, p += 2) {
            if (p[1] == key) {
                long r = p[2];
                while (r > 100) {
                    r = maybe_len(&r) + r / 2;
                }
                return r;
            }
        }
    }
    return 0;
}

__attribute__((noinline)) long len_or_fail(long *p) {
    long n = maybe_len(p);
    if (n == 0) {
        fail((long)p);
    }
    return n;
}
long out;

void _start(void) {
    tail_void(&out);
    maybe(&out);
    out = len_or_fail(data);
    out += first_bit((const unsigned *)data, 2);
    out += mal0_clear((char *)data, sizeof data);
    out += or_call(data, 3);
    out += pass_or(data, 1, 2);
    out += after_quit(out);
    out += via_pointer(data, 1) + via_table(0, data);
    out += via_arg(1, 2, 0) + via_result(data) + via_checked(data);
    out += via_constant(data);
    out += find_in_lists((long **)data, 3);
    register long a0 __asm__("a0") = f(data, &out);
    register long a7 __asm__("a7") = 93;
    __asm__ volatile("ecall" : : "r"(a0), "r"(a7));
    for (;;) {}
}
