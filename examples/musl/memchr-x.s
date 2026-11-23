	.text
	.globl memchr
	.p2align 2
	.type memchr,@function
memchr:
	andi	a3, a1, 255             # 0: 0ff5f693
	andi	a1, a0, 7               # 4: 00757593
	sltu	a5, zero, a2            # 8: 00c037b3
	beq	a1, zero, .Lmemchr_44   # c: 02058c63
	beq	a2, zero, .Lmemchr_44   # 10: 02060a63
	addi	a1, a0, 1               # 14: 00150593
	addi	a6, zero, 1             # 18: 00100813
.Lmemchr_1c:
	#: inv [p, m] a0: int(p), a1: int(p + 1), a2: int(m) where s <= p, p + m = s + n, 1 <= m decreases m
	lbu	a5, 0(a0)               # 1c: 00054783
	addi	a4, a2, 0               # 20: 00060713
	beq	a5, a3, .Lmemchr_50     # 24: 02d78663
	addi	a0, a0, 1               # 28: 00150513
	addi	a2, a4, -1              # 2c: fff70613
	andi	a7, a1, 7               # 30: 0075f893
	sltu	a5, zero, a2            # 34: 00c037b3
	beq	a7, zero, .Lmemchr_44   # 38: 00088663
	addi	a1, a1, 1               # 3c: 00158593
	bne	a4, a6, .Lmemchr_1c     # 40: fd071ee3
.Lmemchr_44:
	#: join [p, m] a0: int(p), a2: int(m) where s <= p, p + m = s + n, 0 <= m, (8 | p || m = 0)
	addi	a1, zero, 0             # 44: 00000593
	addi	a4, a2, 0               # 48: 00060713
	beq	a5, zero, .Lmemchr_f8   # 4c: 0a078663
.Lmemchr_50:
	#: join [p, m] a0: int(p), a4: int(m) where s <= p, p + m = s + n, 1 <= m
	lbu	a1, 0(a0)               # 50: 00054583
	beq	a1, a3, .Lmemchr_d8     # 54: 08d58263
	addi	a1, zero, 8             # 58: 00800593
	bltu	a4, a1, .Lmemchr_d8     # 5c: 06b76e63
	lui	a1, 4112                # 60: 010105b7
	addiw	a1, a1, 257             # 64: 1015859b
	slli	a1, a1, 16              # 68: 01059593
	addi	a1, a1, 257             # 6c: 10158593
	slli	a1, a1, 16              # 70: 01059593
	addi	a1, a1, 257             # 74: 10158593
	mul	a1, a3, a1              # 78: 02b685b3
	lui	a2, 983297              # 7c: f0101637
	slli	a2, a2, 4               # 80: 00461613
	addi	a2, a2, 257             # 84: 10160613
	slli	a2, a2, 16              # 88: 01061613
	addi	a2, a2, 257             # 8c: 10160613
	slli	a2, a2, 15              # 90: 00f61613
	addi	a2, a2, 128             # 94: 08060613
	lui	a5, 1044464             # 98: feff07b7
	addiw	a5, a5, -257            # 9c: eff7879b
	slli	a5, a5, 16              # a0: 01079793
	addi	a5, a5, -257            # a4: eff78793
	slli	a5, a5, 16              # a8: 01079793
	addi	a5, a5, -257            # ac: eff78793
	addi	a6, zero, 7             # b0: 00700813
.Lmemchr_b4:
	#: inv [p, m] a0: int(p), a4: int(m) where s <= p, p + m = s + n, 8 <= m, 8 | p decreases m
	ld	a7, 0(a0)               # b4: 00053883
	xor	a7, a7, a1              # b8: 00b8c8b3
	add	t0, a7, a5              # bc: 00f882b3
	andn	a7, a2, a7              # c0: 411678b3
	and	a7, a7, t0              # c4: 0058f8b3
	bne	a7, zero, .Lmemchr_dc   # c8: 00089a63
	addi	a4, a4, -8              # cc: ff870713
	addi	a0, a0, 8               # d0: 00850513
	bltu	a6, a4, .Lmemchr_b4     # d4: fee860e3
.Lmemchr_d8:
	#: join [p, m] a0: int(p), a4: int(m) where s <= p, p + m = s + n, 0 <= m
	beq	a4, zero, .Lmemchr_f4   # d8: 00070e63
.Lmemchr_dc:
	#: join [p, m] a0: int(p), a4: int(m) where s <= p, p + m = s + n, 1 <= m
	addi	a1, a0, 0               # dc: 00050593
.Lmemchr_e0:
	#: inv [q, m] a1: int(q), a4: int(m) where s <= q, q + m = s + n, 1 <= m decreases m
	lbu	a0, 0(a1)               # e0: 0005c503
	beq	a0, a3, .Lmemchr_f8     # e4: 00d50a63
	addi	a4, a4, -1              # e8: fff70713
	addi	a1, a1, 1               # ec: 00158593
	bne	a4, zero, .Lmemchr_e0   # f0: fe0718e3
.Lmemchr_f4:
	addi	a1, zero, 0             # f4: 00000593
.Lmemchr_f8:
	addi	a0, a1, 0               # f8: 00058513
	jalr	zero, 0(ra)             # fc: 00008067
	.size memchr, .-memchr
