# musl 1.2.5 src/string/bcmp.c (MIT, see examples/musl/COPYRIGHT), compiled by scripts/musl-trial/build.sh.
# Instructions as compiled, unchanged (scripts/musl-trial/verify.sh checks the bytes).
# Annotations are the lines that start with hash-colon (provisional syntax of docs/Tab 1.md; see docs/typed/musl-trial.md).
# Predicted (fixed before compiling): accept
# Expected now (after reading the compiled code): accept iff the call+return rule takes the auipc/jalr tail-call pair (R_RISCV_CALL); the note's rule is written for jal.
#! expect bcmp: accept
#: fn memcmp [l, r, n]
#:   in     a0: int(l), a1: int(r), a2: int(n)
#:   borrow l |-> bytes[n] ro
#:   borrow r |-> bytes[n] ro
#:   out    a0: int
#:   stack  0
#: fn bcmp [l, r, n]
#:   in     a0: int(l), a1: int(r), a2: int(n)
#:   borrow l |-> bytes[n] ro
#:   borrow r |-> bytes[n] ro
#:   out    a0: int
#:   stack  0
	.section .text.bcmp,"ax",@progbits
	.globl bcmp
	.p2align 2
	.type bcmp,@function
bcmp:
	tail	memcmp                  # 0: 00000317 00030067
	.size bcmp, .-bcmp
