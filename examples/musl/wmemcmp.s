	.text
	.globl wmemcmp
	.p2align 2
	.type wmemcmp,@function
wmemcmp:
	beq	a2, zero, .Lwmemcmp_20  # 0: 02060063
.Lwmemcmp_4:
	#: inv [m] a0: int(l + 4n - 4m), a1: int(r + 4n - 4m), a2: int(m) where 1 <= m <= n decreases m
	lw	a3, 0(a0)               # 4: 00052683
	lw	a4, 0(a1)               # 8: 0005a703
	bne	a3, a4, .Lwmemcmp_28    # c: 00e69e63
	addi	a2, a2, -1              # 10: fff60613
	addi	a0, a0, 4               # 14: 00450513
	addi	a1, a1, 4               # 18: 00458593
	bne	a2, zero, .Lwmemcmp_4   # 1c: fe0614e3
.Lwmemcmp_20:
	addi	a0, zero, 0             # 20: 00000513
	jalr	zero, 0(ra)             # 24: 00008067
.Lwmemcmp_28:
	addi	a0, zero, -1            # 28: fff00513
	blt	a3, a4, .Lwmemcmp_34    # 2c: 00e6c463
	slt	a0, a4, a3              # 30: 00d72533
.Lwmemcmp_34:
	jalr	zero, 0(ra)             # 34: 00008067
	.size wmemcmp, .-wmemcmp
