	.text
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
