	.text
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
