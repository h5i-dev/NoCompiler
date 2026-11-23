	.text
	.globl memcmp
	.p2align 2
	.type memcmp,@function
memcmp:
	beq	a2, zero, .Lmemcmp_20   # 0: 02060063
.Lmemcmp_4:
	#: inv [m] a0: int(l + n - m), a1: int(r + n - m), a2: int(m) where 1 <= m <= n decreases m
	lbu	a3, 0(a0)               # 4: 00054683
	lbu	a4, 0(a1)               # 8: 0005c703
	bne	a3, a4, .Lmemcmp_28     # c: 00e69e63
	addi	a2, a2, -1              # 10: fff60613
	addi	a0, a0, 1               # 14: 00150513
	addi	a1, a1, 1               # 18: 00158593
	bne	a2, zero, .Lmemcmp_4    # 1c: fe0614e3
.Lmemcmp_20:
	addi	a0, zero, 0             # 20: 00000513
	jalr	zero, 0(ra)             # 24: 00008067
.Lmemcmp_28:
	sub	a0, a3, a4              # 28: 40e68533
	jalr	zero, 0(ra)             # 2c: 00008067
	.size memcmp, .-memcmp
