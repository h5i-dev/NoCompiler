# musl 1.2.5 src/string/wmemset.c (MIT, see examples/musl/COPYRIGHT), compiled by scripts/musl-trial/build.sh.
# Instructions as compiled, unchanged (scripts/musl-trial/verify.sh checks the bytes).
# Annotations are the lines that start with hash-colon (provisional syntax of docs/Tab 1.md; see docs/typed/musl-trial.md).
# Predicted (batch 2, fixed before compiling): accept
# Expected now (after reading the compiled code): accept.
#! expect wmemset: accept
#: fn wmemset [d, n]
#:   in     a0: int(d), a2: int(n)
#:   borrow d |-> bytes[4n] rw
#:   where  4 | d
#:   out    a0: int(d)
#:   stack  0
	.section .text.wmemset,"ax",@progbits
	.globl wmemset
	.p2align 2
	.type wmemset,@function
wmemset:
	beq	a2, zero, .Lwmemset_1c  # 0: 00060e63
	addi	a3, a0, 0               # 4: 00050693
.Lwmemset_8:
	#: inv [m] a3: int(d + 4n - 4m), a2: int(m) where 1 <= m <= n decreases m
	addi	a2, a2, -1              # 8: fff60613
	addi	a4, a3, 4               # c: 00468713
	sw	a1, 0(a3)               # 10: 00b6a023
	addi	a3, a4, 0               # 14: 00070693
	bne	a2, zero, .Lwmemset_8   # 18: fe0618e3
.Lwmemset_1c:
	jalr	zero, 0(ra)             # 1c: 00008067
	.size wmemset, .-wmemset
