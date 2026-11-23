# musl 1.2.5 src/string/bzero.c (MIT, see examples/musl/COPYRIGHT), compiled by scripts/musl-trial/build.sh.
# Instructions as compiled, unchanged (scripts/musl-trial/verify.sh checks the bytes).
# Annotations are the lines that start with hash-colon (provisional syntax of docs/Tab 1.md; see docs/typed/musl-trial.md).
# Predicted (fixed before compiling): accept
# Expected now (after reading the compiled code): accept iff the tail-call pair is taken as a call (see bcmp); uses memset's signature (memset itself is expected to be rejected).
#! expect bzero: accept
#: fn memset [s, n]
#:   in     a0: int(s), a2: int(n)
#:   borrow s |-> bytes[n] rw
#:   out    a0: int(s)
#:   stack  0
#: fn bzero [s, n]
#:   in     a0: int(s), a1: int(n)
#:   borrow s |-> bytes[n] rw
#:   stack  0
	.section .text.bzero,"ax",@progbits
	.globl bzero
	.p2align 2
	.type bzero,@function
bzero:
	addi	a2, a1, 0               # 0: 00058613
	addi	a1, zero, 0             # 4: 00000593
	tail	memset                  # 8: 00000317 00030067
	.size bzero, .-bzero
