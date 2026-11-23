/* Float results come back in fa0 and float arguments go out in fa0 (lp64d).
   Built with -march=rv64imfd_zba_zbb -mabi=lp64d; see riscv.rs. */
__attribute__((noinline)) double half(double x) { return x * 0.5; }

/* Calls half after another call, so fa0 has to be the call's result and the
   argument has to be read from fa0, not a0. */
__attribute__((noinline)) long tick(long n) { return n + 1; }

__attribute__((noinline)) double square_half(double x, long n) {
    long t = tick(n);
    double y = half(x);
    return y * y + (double)t;
}

/* fa1 as scratch on one path only, so a phi of the entry fa1 and a loaded
   value reaches the return (as musl's log1p does with its constants): fa1 is
   not a second argument. Written in assembly so the registers are these. */
double scratch_fa1(double x, long n, const double *c);
__asm__(".globl scratch_fa1\n"
        "scratch_fa1:\n"
        "  beqz a0, 1f\n"
        "  fld fa1, 0(a1)\n"
        "  fadd.d fa0, fa0, fa1\n"
        "1:\n"
        "  ret\n");

static const double one[1] = {1.0};

/* Not floats: a system call after a call, setting three of openat's four
   arguments, so a3 is what tick left there and is not passed. */
__attribute__((noinline)) long open_after(const char *p) {
    long t = tick(1);
    register long a7 __asm__("a7") = 56;
    register long a0 __asm__("a0") = -100;
    register long a1 __asm__("a1") = (long)p;
    register long a2 __asm__("a2") = t;
    __asm__ volatile("ecall" : "+r"(a0) : "r"(a7), "r"(a1), "r"(a2) : "memory");
    return a0;
}

/* futex(p, FUTEX_WAKE_PRIVATE, 1), as musl's __wake: futex takes up to six,
   and a3..a5 here are only what wake was entered with, not its arguments. */
__attribute__((noinline)) long wake(int *p) {
    register long a7 __asm__("a7") = 98;
    register long a0 __asm__("a0") = (long)p;
    register long a1 __asm__("a1") = 129;
    register long a2 __asm__("a2") = 1;
    __asm__ volatile("ecall" : "+r"(a0) : "r"(a7), "r"(a1), "r"(a2) : "memory");
    return a0;
}

static int word;

/* A call through a pointer to a function returning a double: the result is
   in fa0, which is what the caller passes on (micropython's math_generic_1). */
__attribute__((noinline)) double apply(double (*fp)(double), double x) {
    return half(fp(x)) + 1.0;
}

/* a1 set on one path only and a0 the result (as musl's __unlock): a1 at the
   return is not a second argument. */
long a1_scratch(int *p);
__asm__(".globl a1_scratch\n"
        "a1_scratch:\n"
        "  lw a0, 0(a0)\n"
        "  bgez a0, 1f\n"
        "  addi a1, zero, 129\n"
        "  add a0, a0, a1\n"
        "1:\n"
        "  ret\n");

void _start(void) {
    volatile double r = square_half(3.0, 2);
    r = scratch_fa1(r, 1, one);
    r = (double)open_after("x");
    r = (double)wake(&word);
    r = (double)a1_scratch(&word);
    r = apply(half, r);
    (void)r;
    for (;;) {
    }
}
