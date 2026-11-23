# musl 1.2.5 src/string/memccpy.c (MIT, see examples/musl/COPYRIGHT), compiled by scripts/musl-trial/build.sh
# with -mllvm -riscv-disable-using-constant-pool-for-large-ints -mllvm -jump-is-expensive=false
# (constants inline; && kept as branches). Instructions as compiled, unchanged (verify.sh).
# Annotations are the lines that start with hash-colon (docs/typed/syntax.md).
# Predicted (fixed before building this variant): reject
# Expected now (after reading the compiled code): reject: S2 6 violations (4 non-loop backward edges); xor alignment test, so the sd at 0x118 fails 8 | a. Annotated: signature and the three natural loops 0x18, 0x58, 0x100. Not annotated: the non-loop backward targets (joins under the natural-loop reading).
#! expect memccpy: reject cfg
#: fn memccpy [d, s, n]
#:   in     a0: int(d), a1: int(s), a3: int(n)
#:   borrow d |-> bytes[n] rw
#:   borrow s |-> bytes[n] ro
#:   out    a0: int
#:   stack  0
	.section .text.memccpy,"ax",@progbits
	.globl memccpy
	.p2align 2
	.type memccpy,@function
memccpy:
	xor	a4, a1, a0              # 0: 00a5c733
	andi	a4, a4, 7               # 4: 00777713
	andi	a2, a2, 255             # 8: 0ff67613
	beq	a4, zero, .Lmemccpy_3c  # c: 02070863
.Lmemccpy_10:
	#: join [m] a0: int(d + n - m), a1: int(s + n - m), a3: int(m) where 0 <= m <= n
	beq	a3, zero, .Lmemccpy_34  # 10: 02068263
.Lmemccpy_14:
	#: join [m] a0: int(d + n - m), a1: int(s + n - m), a3: int(m) where 1 <= m <= n
	addi	a0, a0, 1               # 14: 00150513
.Lmemccpy_18:
	#: inv [m] a0: int(d + n - m + 1), a1: int(s + n - m), a3: int(m) where 1 <= m <= n decreases m
	lbu	a4, 0(a1)               # 18: 0005c703
	sb	a4, -1(a0)              # 1c: fee50fa3
	beq	a4, a2, .Lmemccpy_a0    # 20: 08c70063
	addi	a3, a3, -1              # 24: fff68693
	addi	a1, a1, 1               # 28: 00158593
	addi	a0, a0, 1               # 2c: 00150513
	bne	a3, zero, .Lmemccpy_18  # 30: fe0694e3
.Lmemccpy_34:
	addi	a0, zero, 0             # 34: 00000513
	jalr	zero, 0(ra)             # 38: 00008067
.Lmemccpy_3c:
	andi	a5, a1, 7               # 3c: 0075f793
	sltu	a4, zero, a5            # 40: 00f03733
	beq	a5, zero, .Lmemccpy_94  # 44: 04078863
	beq	a3, zero, .Lmemccpy_94  # 48: 04068663
	addi	a7, zero, 0             # 4c: 00000893
	addi	a4, a1, 1               # 50: 00158713
	addi	a5, a3, -1              # 54: fff68793
.Lmemccpy_58:
	#: inv [i] a7: int(i) where 0 <= i <= n - 1 decreases n - i
	addi	a6, a7, 0               # 58: 00088813
	add	a7, a1, a7              # 5c: 011588b3
	lbu	t0, 0(a7)               # 60: 0008c283
	add	a7, a0, a6              # 64: 010508b3
	sb	t0, 0(a7)               # 68: 00588023
	beq	t0, a2, .Lmemccpy_130   # 6c: 0cc28263
	addw	a7, a4, a6              # 70: 010708bb
	andi	t0, a7, 7               # 74: 0078f293
	addi	a7, a6, 1               # 78: 00180893
	beq	t0, zero, .Lmemccpy_84  # 7c: 00028463
	bne	a5, a6, .Lmemccpy_58    # 80: fd079ce3
.Lmemccpy_84:
	#: join [i, r] a6: int(i), a7: int(i + 1), t0: int(r) where 0 <= i <= n - 1, 0 <= r <= 7, ((r = 0 && 8 | s + i + 1 && 8 | d + i + 1) || (r != 0 && i = n - 1))
	sltu	a4, zero, t0            # 84: 00503733
	add	a1, a1, a7              # 88: 011585b3
	add	a0, a0, a7              # 8c: 01150533
	sub	a3, a3, a7              # 90: 411686b3
.Lmemccpy_94:
	#: join [m, b] a0: int(d + n - m), a1: int(s + n - m), a3: int(m), a4: int(b) where 0 <= m <= n, ((b = 0 && 8 | s + n - m && 8 | d + n - m) || (b = 1 && m = 0))
	beq	a4, zero, .Lmemccpy_a4  # 94: 00070863
	beq	a3, zero, .Lmemccpy_34  # 98: f8068ee3
	addi	a0, a0, 1               # 9c: 00150513
.Lmemccpy_a0:
	jalr	zero, 0(ra)             # a0: 00008067
.Lmemccpy_a4:
	addi	a4, zero, 8             # a4: 00800713
	bltu	a3, a4, .Lmemccpy_10    # a8: f6e6e4e3
	lui	a4, 4112                # ac: 01010737
	addiw	a4, a4, 257             # b0: 1017071b
	slli	a4, a4, 16              # b4: 01071713
	addi	a4, a4, 257             # b8: 10170713
	slli	a4, a4, 16              # bc: 01071713
	addi	a4, a4, 257             # c0: 10170713
	mul	a4, a2, a4              # c4: 02e60733
	lui	a5, 983297              # c8: f01017b7
	slli	a5, a5, 4               # cc: 00479793
	addi	a5, a5, 257             # d0: 10178793
	slli	a5, a5, 16              # d4: 01079793
	addi	a5, a5, 257             # d8: 10178793
	slli	a5, a5, 15              # dc: 00f79793
	addi	a5, a5, 128             # e0: 08078793
	lui	a6, 1044464             # e4: feff0837
	addiw	a6, a6, -257            # e8: eff8081b
	slli	a6, a6, 16              # ec: 01081813
	addi	a6, a6, -257            # f0: eff80813
	slli	a6, a6, 16              # f4: 01081813
	addi	a6, a6, -257            # f8: eff80813
	addi	a7, zero, 7             # fc: 00700893
.Lmemccpy_100:
	#: inv [m] a0: int(d + n - m), a1: int(s + n - m), a3: int(m) where 8 <= m <= n, 8 | s + n - m, 8 | d + n - m decreases m
	ld	t0, 0(a1)               # 100: 0005b283
	xor	t1, t0, a4              # 104: 00e2c333
	add	t2, t1, a6              # 108: 010303b3
	andn	t1, a5, t1              # 10c: 4067f333
	and	t1, t1, t2              # 110: 00737333
	bne	t1, zero, .Lmemccpy_14  # 114: f00310e3
	sd	t0, 0(a0)               # 118: 00553023
	addi	a3, a3, -8              # 11c: ff868693
	addi	a1, a1, 8               # 120: 00858593
	addi	a0, a0, 8               # 124: 00850513
	bltu	a7, a3, .Lmemccpy_100   # 128: fcd8ece3
	jal	zero, .Lmemccpy_10      # 12c: ee5ff06f
.Lmemccpy_130:
	addi	a0, a7, 1               # 130: 00188513
	jalr	zero, 0(ra)             # 134: 00008067
	.size memccpy, .-memccpy
