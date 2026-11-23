	.text
	.globl wmemchr
	.p2align 2
	.type wmemchr,@function
wmemchr:
	beq	a2, zero, .Lwmemchr_18  # 0: 00060c63
.Lwmemchr_4:
	#: inv [m] a0: int(s + 4n - 4m), a2: int(m) where 1 <= m <= n decreases m
	lw	a3, 0(a0)               # 4: 00052683
	beq	a3, a1, .Lwmemchr_1c    # 8: 00b68a63
	addi	a2, a2, -1              # c: fff60613
	addi	a0, a0, 4               # 10: 00450513
	bne	a2, zero, .Lwmemchr_4   # 14: fe0618e3
.Lwmemchr_18:
	addi	a0, zero, 0             # 18: 00000513
.Lwmemchr_1c:
	jalr	zero, 0(ra)             # 1c: 00008067
	.size wmemchr, .-wmemchr
