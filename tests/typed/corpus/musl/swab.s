# musl 1.2.5 src/string/swab.c (MIT, see examples/musl/COPYRIGHT), compiled by scripts/musl-trial/build.sh.
# Instructions as compiled, unchanged (scripts/musl-trial/verify.sh checks the bytes).
# Annotations are the lines that start with hash-colon (provisional syntax of docs/Tab 1.md; see docs/typed/musl-trial.md).
# Predicted (fixed before compiling): accept
# Expected now (after reading the compiled code): accept. Signature narrower than C: 0 <= n (C allows n < 0, then nothing is touched; a capability of length max(n,0) is not a v0 index expression).
#! expect swab: accept
#: fn swab [s, d, n]
#:   in     a0: int(s), a1: int(d), a2: int(n)
#:   borrow s |-> bytes[n] ro
#:   borrow d |-> bytes[n] rw
#:   where  0 <= n < 2^63
#:   stack  0
	.section .text.swab,"ax",@progbits
	.globl swab
	.p2align 2
	.type swab,@function
swab:
	addi	a3, zero, 2             # 0: 00200693
	blt	a2, a3, .Lswab_34       # 4: 02d64863
	addi	a0, a0, 1               # 8: 00150513
	addi	a2, a2, 2               # c: 00260613
	addi	a3, zero, 3             # 10: 00300693
.Lswab_14:
	#: inv [k] a0: int(s + n + 3 - k), a1: int(d + n + 2 - k), a2: int(k) where 4 <= k <= n + 2 decreases k
	lb	a4, 0(a0)               # 14: 00050703
	lb	a5, -1(a0)              # 18: fff50783
	sb	a4, 0(a1)               # 1c: 00e58023
	sb	a5, 1(a1)               # 20: 00f580a3
	addi	a1, a1, 2               # 24: 00258593
	addi	a2, a2, -2              # 28: ffe60613
	addi	a0, a0, 2               # 2c: 00250513
	bltu	a3, a2, .Lswab_14       # 30: fec6e2e3
.Lswab_34:
	jalr	zero, 0(ra)             # 34: 00008067
	.size swab, .-swab
