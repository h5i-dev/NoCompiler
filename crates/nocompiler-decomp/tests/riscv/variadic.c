/* A variadic function and a caller (decompile test fixture,
   crates/nocompiler-decomp/tests/riscv.rs a_variadic_callee_gets_what_the_caller_set).
   sum_n spills a1-a7 for va_start; show passes two fixed arguments and one more. */
typedef __builtin_va_list va_list;

__attribute__((noinline)) long sum_n(long n, ...) {
    va_list ap;
    __builtin_va_start(ap, n);
    long s = 0;
    for (long i = 0; i < n; i++)
        s += __builtin_va_arg(ap, long);
    __builtin_va_end(ap);
    return s;
}

__attribute__((noinline)) long show(long x) { return sum_n(2, x, 7); }

void _start(void) {
    register long a0 __asm__("a0") = show(5);
    register long a7 __asm__("a7") = 93;
    __asm__ volatile("ecall" : : "r"(a0), "r"(a7));
    for (;;) {}
}
