# musl 1.2.5 src/string/memrchr.c (MIT, see examples/musl/COPYRIGHT), compiled by scripts/musl-trial/build.sh.
# Instructions as compiled, unchanged (scripts/musl-trial/verify.sh checks the bytes).
# Annotations are the lines that start with hash-colon (provisional syntax of docs/Tab 1.md; see docs/typed/musl-trial.md).
# Predicted (fixed before compiling): accept
# Expected now (after reading the compiled code): accept.
#! expect __memrchr: accept
#: fn __memrchr [s, n]
#:   in     a0: int(s), a2: int(n)
#:   borrow s |-> bytes[n] ro
#:   out    a0: int
#:   stack  0
	.text
	.globl __memrchr
	.p2align 2
	.type __memrchr,@function
__memrchr:
	andi	a1, a1, 255             # 0: 0ff5f593
.L__memrchr_4:
	#: inv [m] a2: int(m) where 0 <= m <= n decreases m
	beq	a2, zero, .L__memrchr_24# 4: 02060063
	add	a3, a0, a2              # 8: 00c506b3
	lbu	a4, -1(a3)              # c: fff6c703
	addi	a3, a2, -1              # 10: fff60693
	addi	a2, a3, 0               # 14: 00068613
	bne	a4, a1, .L__memrchr_4   # 18: feb716e3
	add	a0, a0, a3              # 1c: 00d50533
	jalr	zero, 0(ra)             # 20: 00008067
.L__memrchr_24:
	addi	a0, zero, 0             # 24: 00000513
	jalr	zero, 0(ra)             # 28: 00008067
	.size __memrchr, .-__memrchr
