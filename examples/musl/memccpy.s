	.text
	.globl memccpy
	.p2align 2
	.type memccpy,@function
memccpy:
	xor	a4, a1, a0              # 0: 00a5c733
	andi	a4, a4, 7               # 4: 00777713
	andi	a2, a2, 255             # 8: 0ff67613
	beq	a4, zero, .Lmemccpy_3c  # c: 02070863
.Lmemccpy_10:
	#: inv [m] a0: int(d + n - m), a1: int(s + n - m), a3: int(m) where 0 <= m <= n
	#: # 0x10, 0x14, 0x34, 0x9c are targets of backward edges only because of block layout; they are
	#: # not loops, so no decreases clause is given.
	beq	a3, zero, .Lmemccpy_34  # 10: 02068263
.Lmemccpy_14:
	#: inv [m] a0: int(d + n - m), a1: int(s + n - m), a3: int(m) where 1 <= m <= n
	addi	a0, a0, 1               # 14: 00150513
.Lmemccpy_18:
	#: inv [m] a0: int(d + n - m + 1), a1: int(s + n - m), a3: int(m) where 1 <= m <= n decreases m
	lbu	a4, 0(a1)               # 18: 0005c703
	sb	a4, -1(a0)              # 1c: fee50fa3
	beq	a4, a2, .Lmemccpy_110   # 20: 0ec70863
	addi	a3, a3, -1              # 24: fff68693
	addi	a1, a1, 1               # 28: 00158593
	addi	a0, a0, 1               # 2c: 00150513
	bne	a3, zero, .Lmemccpy_18  # 30: fe0694e3
.Lmemccpy_34:
	#: inv a0: int
	addi	a0, zero, 0             # 34: 00000513
	jalr	zero, 0(ra)             # 38: 00008067
.Lmemccpy_3c:
	andi	a4, a1, 7               # 3c: 0075f713
	sltiu	a5, a4, 1               # 40: 00173793
	sltiu	a6, a3, 1               # 44: 0016b813
	or	a5, a5, a6              # 48: 0107e7b3
	bne	a5, zero, .Lmemccpy_100 # 4c: 0a079a63
	addi	a6, a1, 1               # 50: 00158813
	addi	a7, a3, -1              # 54: fff68893
.Lmemccpy_58:
	#: inv [i] a5: int(i), a6: int(s + 1), a7: int(n - 1) where 0 <= i <= n - 1 decreases n - i
	add	a4, a1, a5              # 58: 00f58733
	lbu	t0, 0(a4)               # 5c: 00074283
	add	a4, a0, a5              # 60: 00f50733
	sb	t0, 0(a4)               # 64: 00570023
	beq	t0, a2, .Lmemccpy_114   # 68: 0ac28663
	addw	a4, a6, a5              # 6c: 00f8073b
	andi	a4, a4, 7               # 70: 00777713
	sltu	a4, zero, a4            # 74: 00e03733
	xor	t0, a7, a5              # 78: 00f8c2b3
	sltu	t0, zero, t0            # 7c: 005032b3
	and	t0, a4, t0              # 80: 005772b3
	addi	a5, a5, 1               # 84: 00178793
	bne	t0, zero, .Lmemccpy_58  # 88: fc0298e3
	add	a1, a1, a5              # 8c: 00f585b3
	add	a0, a0, a5              # 90: 00f50533
	sub	a3, a3, a5              # 94: 40f686b3
	bne	a4, zero, .Lmemccpy_108 # 98: 06071863
.Lmemccpy_9c:
	#: inv [m] a0: int(d + n - m), a1: int(s + n - m), a3: int(m) where 0 <= m <= n, 8 | s + n - m, 8 | d + n - m
	addi	a4, zero, 8             # 9c: 00800713
	bltu	a3, a4, .Lmemccpy_10    # a0: f6e6e8e3
.Lpcrel_a4:
	auipc	a4, %pcrel_hi(.LCPI0_0) # a4: 00000717
	addi	a4, a4, %pcrel_lo(.Lpcrel_a4)# a8: 00070713
	ld	a6, 0(a4)               # ac: 00073803
.Lpcrel_b0:
	auipc	a4, %pcrel_hi(.LCPI0_1) # b0: 00000717
	addi	a4, a4, %pcrel_lo(.Lpcrel_b0)# b4: 00070713
	ld	a4, 0(a4)               # b8: 00073703
.Lpcrel_bc:
	auipc	a5, %pcrel_hi(.LCPI0_2) # bc: 00000797
	addi	a5, a5, %pcrel_lo(.Lpcrel_bc)# c0: 00078793
	ld	a5, 0(a5)               # c4: 0007b783
	mul	a6, a2, a6              # c8: 03060833
	addi	a7, zero, 7             # cc: 00700893
.Lmemccpy_d0:
	#: inv [m] a0: int(d + n - m), a1: int(s + n - m), a3: int(m) where 8 <= m <= n, 8 | s + n - m, 8 | d + n - m decreases m
	ld	t0, 0(a1)               # d0: 0005b283
	xor	t1, t0, a6              # d4: 0102c333
	add	t2, t1, a5              # d8: 00f303b3
	andn	t1, a4, t1              # dc: 40677333
	and	t1, t1, t2              # e0: 00737333
	bne	t1, zero, .Lmemccpy_14  # e4: f20318e3
	sd	t0, 0(a0)               # e8: 00553023
	addi	a3, a3, -8              # ec: ff868693
	addi	a1, a1, 8               # f0: 00858593
	addi	a0, a0, 8               # f4: 00850513
	bltu	a7, a3, .Lmemccpy_d0    # f8: fcd8ece3
	jal	zero, .Lmemccpy_10      # fc: f15ff06f
.Lmemccpy_100:
	sltu	a4, zero, a4            # 100: 00e03733
	beq	a4, zero, .Lmemccpy_9c  # 104: f8070ce3
.Lmemccpy_108:
	beq	a3, zero, .Lmemccpy_34  # 108: f20686e3
	addi	a0, a0, 1               # 10c: 00150513
.Lmemccpy_110:
	jalr	zero, 0(ra)             # 110: 00008067
.Lmemccpy_114:
	addi	a0, a4, 1               # 114: 00170513
	jalr	zero, 0(ra)             # 118: 00008067
	.size memccpy, .-memccpy

	.section .rodata.cst8,"aM",@progbits,8
	.p2align 3
.LCPI0_0:
	.quad	0x0101010101010101
.LCPI0_1:
	.quad	0x8080808080808080
.LCPI0_2:
	.quad	0xfefefefefefefeff
