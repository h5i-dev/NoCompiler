# musl 1.2.5 src/string/wmemcpy.c (MIT, see examples/musl/COPYRIGHT), compiled by scripts/musl-trial/build.sh.
# Instructions as compiled, unchanged (scripts/musl-trial/verify.sh checks the bytes).
# Annotations are the lines that start with hash-colon (provisional syntax of docs/Tab 1.md; see docs/typed/musl-trial.md).
# Predicted (batch 2, fixed before compiling): accept
# Expected now (after reading the compiled code): accept.
#! expect wmemcpy: accept
#: fn wmemcpy [d, s, n]
#:   in     a0: int(d), a1: int(s), a2: int(n)
#:   borrow d |-> bytes[4n] rw
#:   borrow s |-> bytes[4n] ro
#:   where  4 | d, 4 | s
#:   out    a0: int(d)
#:   stack  0
	.section .text.wmemcpy,"ax",@progbits
	.globl wmemcpy
	.p2align 2
	.type wmemcpy,@function
wmemcpy:
	beq	a2, zero, .Lwmemcpy_24  # 0: 02060263
	addi	a3, a0, 0               # 4: 00050693
.Lwmemcpy_8:
	#: inv [m] a1: int(s + 4n - 4m), a3: int(d + 4n - 4m), a2: int(m) where 1 <= m <= n decreases m
	lw	a4, 0(a1)               # 8: 0005a703
	addi	a2, a2, -1              # c: fff60613
	addi	a1, a1, 4               # 10: 00458593
	addi	a5, a3, 4               # 14: 00468793
	sw	a4, 0(a3)               # 18: 00e6a023
	addi	a3, a5, 0               # 1c: 00078693
	bne	a2, zero, .Lwmemcpy_8   # 20: fe0614e3
.Lwmemcpy_24:
	jalr	zero, 0(ra)             # 24: 00008067
	.size wmemcpy, .-wmemcpy
