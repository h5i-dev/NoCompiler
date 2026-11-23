	.text
	.globl strncmp
	.p2align 2
	.type strncmp,@function
strncmp:
	beq	a2, zero, .Lstrncmp_4c  # 0: 04060663
	lbu	a3, 0(a0)               # 4: 00054683
	beq	a3, zero, .Lstrncmp_3c  # 8: 02068a63
	addi	a2, a2, -1              # c: fff60613
	addi	a0, a0, 1               # 10: 00150513
.Lstrncmp_14:
	#: inv [m] a0: int(l + n - m), a1: int(r + n - m - 1), a2: int(m) where 0 <= m <= n - 1 decreases m
	lbu	a4, 0(a1)               # 14: 0005c703
	beq	a4, zero, .Lstrncmp_3c  # 18: 02070263
	beq	a2, zero, .Lstrncmp_3c  # 1c: 02060063
	andi	a5, a3, 255             # 20: 0ff6f793
	bne	a5, a4, .Lstrncmp_3c    # 24: 00e79c63
	lbu	a3, 0(a0)               # 28: 00054683
	addi	a1, a1, 1               # 2c: 00158593
	addi	a2, a2, -1              # 30: fff60613
	addi	a0, a0, 1               # 34: 00150513
	bne	a3, zero, .Lstrncmp_14  # 38: fc069ee3
.Lstrncmp_3c:
	#: join [q] a1: int(q) where r <= q <= r + n - 1
	lbu	a0, 0(a1)               # 3c: 0005c503
	andi	a1, a3, 255             # 40: 0ff6f593
	sub	a0, a1, a0              # 44: 40a58533
	jalr	zero, 0(ra)             # 48: 00008067
.Lstrncmp_4c:
	addi	a0, zero, 0             # 4c: 00000513
	jalr	zero, 0(ra)             # 50: 00008067
	.size strncmp, .-strncmp
