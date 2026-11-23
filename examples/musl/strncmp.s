	.text
	.globl strncmp
	.p2align 2
	.type strncmp,@function
strncmp:
	beq	a2, zero, .Lstrncmp_5c  # 0: 04060e63
	lbu	a3, 0(a0)               # 4: 00054683
	beq	a3, zero, .Lstrncmp_4c  # 8: 04068263
	addi	a2, a2, -1              # c: fff60613
	addi	a0, a0, 1               # 10: 00150513
.Lstrncmp_14:
	#: inv [m] a0: int(l + n - m), a1: int(r + n - m - 1), a2: int(m) where 0 <= m <= n - 1 decreases m
	lbu	a4, 0(a1)               # 14: 0005c703
	sltu	a5, zero, a4            # 18: 00e037b3
	sltu	a6, zero, a2            # 1c: 00c03833
	and	a5, a5, a6              # 20: 0107f7b3
	andi	a6, a3, 255             # 24: 0ff6f813
	xor	a4, a6, a4              # 28: 00e84733
	sltiu	a4, a4, 1               # 2c: 00173713
	and	a4, a5, a4              # 30: 00e7f733
	beq	a4, zero, .Lstrncmp_4c  # 34: 00070c63
	lbu	a3, 0(a0)               # 38: 00054683
	addi	a1, a1, 1               # 3c: 00158593
	addi	a2, a2, -1              # 40: fff60613
	addi	a0, a0, 1               # 44: 00150513
	bne	a3, zero, .Lstrncmp_14  # 48: fc0696e3
.Lstrncmp_4c:
	#: join [q] a1: int(q) where r <= q <= r + n - 1
	lbu	a0, 0(a1)               # 4c: 0005c503
	andi	a1, a3, 255             # 50: 0ff6f593
	sub	a0, a1, a0              # 54: 40a58533
	jalr	zero, 0(ra)             # 58: 00008067
.Lstrncmp_5c:
	addi	a0, zero, 0             # 5c: 00000513
	jalr	zero, 0(ra)             # 60: 00008067
	.size strncmp, .-strncmp
