# musl 1.2.5 src/string/strncpy.c (MIT, see examples/musl/COPYRIGHT), compiled by scripts/musl-trial/build.sh.
# Instructions as compiled, unchanged (scripts/musl-trial/verify.sh checks the bytes).
# Annotations are the lines that start with hash-colon (provisional syntax of docs/Tab 1.md; see docs/typed/musl-trial.md).
# Predicted (batch 2, fixed before compiling): accept (signature stronger than C)
# Expected now (after reading the compiled code): accept, if call pairs are typed as calls (I21); uses __stpncpy's signature (which itself is expected to be rejected).
#! expect strncpy: accept
#: fn __stpncpy [d, s, n]
#:   in     a0: int(d), a1: int(s), a2: int(n)
#:   borrow d |-> bytes[n] rw
#:   borrow s |-> bytes[n] ro
#:   out    a0: int
#:   stack  16
#: fn strncpy [d, s, n]
#:   in     a0: int(d), a1: int(s), a2: int(n)
#:   borrow d |-> bytes[n] rw
#:   borrow s |-> bytes[n] ro
#:   out    a0: int(d)
#:   stack  32
#:   frame  16 slots 0, 8
	.section .text.strncpy,"ax",@progbits
	.globl strncpy
	.p2align 2
	.type strncpy,@function
strncpy:
	addi	sp, sp, -16             # 0: ff010113
	sd	ra, 8(sp)               # 4: 00113423
	sd	s0, 0(sp)               # 8: 00813023
	addi	s0, a0, 0               # c: 00050413
	call	__stpncpy               # 10: 00000097 000080e7
	addi	a0, s0, 0               # 18: 00040513
	ld	ra, 8(sp)               # 1c: 00813083
	ld	s0, 0(sp)               # 20: 00013403
	addi	sp, sp, 16              # 24: 01010113
	jalr	zero, 0(ra)             # 28: 00008067
	.size strncpy, .-strncpy
