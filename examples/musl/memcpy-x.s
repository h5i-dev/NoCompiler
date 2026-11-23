# musl 1.2.5 src/string/memcpy.c (MIT, see examples/musl/COPYRIGHT), compiled by scripts/musl-trial/build.sh
# with -mllvm -riscv-disable-using-constant-pool-for-large-ints -mllvm -jump-is-expensive=false
# (constants inline; && kept as branches). Instructions as compiled, unchanged (verify.sh).
# Annotations are the lines that start with hash-colon (docs/typed/syntax.md).
# Predicted (fixed before building this variant): reject
# Expected now (after reading the compiled code): reject: S2 33 violations (6 non-loop backward edges); andi n,2^k tails. Annotated in full (added when the checker got --loops natural): head loop, the aligned loop, the three misaligned loops (d = 1, 2, 3 mod 4: source pointer kept 13/14/15 bytes ahead of the byte position), and a join at every tail block (the tails test bits 16, 8, 4, 2, 1 of a2 without changing it: r is what remains to copy, 2^k | j - r).
#! expect memcpy: reject cfg
#: fn memcpy [d, s, n]
#:   in     a0: int(d), a1: int(s), a2: u64(n)
#:   borrow d |-> bytes[n] rw
#:   borrow s |-> bytes[n] ro
#:   out    a0: int(d)
#:   stack  0
	.section .text.memcpy,"ax",@progbits
	.globl memcpy
	.p2align 2
	.type memcpy,@function
memcpy:
	andi	a3, a1, 3               # 0: 0035f693
	beq	a3, zero, .Lmemcpy_44   # 4: 04068063
	beq	a2, zero, .Lmemcpy_108  # 8: 10060063
	addi	a4, a1, 1               # c: 00158713
	addi	a5, zero, 1             # 10: 00100793
	addi	a3, a0, 0               # 14: 00050693
.Lmemcpy_18:
	#: inv [m] a1: int(s + n - m), a3: int(d + n - m), a4: int(s + n - m + 1), a2: int(m) where 1 <= m <= n decreases m
	lb	a7, 0(a1)               # 18: 00058883
	addi	a6, a2, 0               # 1c: 00060813
	addi	a1, a1, 1               # 20: 00158593
	sb	a7, 0(a3)               # 24: 01168023
	addi	a3, a3, 1               # 28: 00168693
	andi	a7, a4, 3               # 2c: 00377893
	addi	a2, a2, -1              # 30: fff60613
	beq	a7, zero, .Lmemcpy_48   # 34: 00088a63
	addi	a4, a4, 1               # 38: 00170713
	bne	a6, a5, .Lmemcpy_18     # 3c: fcf81ee3
	jal	zero, .Lmemcpy_48       # 40: 0080006f
.Lmemcpy_44:
	addi	a3, a0, 0               # 44: 00050693
.Lmemcpy_48:
	#: join [m] a1: int(s + n - m), a3: int(d + n - m), a2: int(m) where 0 <= m <= n, (m = 0 || 4 | s + n - m)
	andi	a4, a3, 3               # 48: 0036f713
	beq	a4, zero, .Lmemcpy_114  # 4c: 0c070463
.Lmemcpy_50:
	#: join [m, x] a1: int(s + n - m), a3: int(d + n - m), a2: int(m), a4: int(x) where 0 <= m <= n, 1 <= x <= 3, 4 | d + n - m - x, (m = 0 || 4 | s + n - m)
	addi	a5, zero, 32            # 50: 02000793
	bltu	a2, a5, .Lmemcpy_208    # 54: 1af66a63
	addi	a5, zero, 3             # 58: 00300793
	beq	a4, a5, .Lmemcpy_18c    # 5c: 12f70863
	addi	a5, zero, 2             # 60: 00200793
	beq	a4, a5, .Lmemcpy_290    # 64: 22f70663
	addi	a5, zero, 1             # 68: 00100793
	bne	a4, a5, .Lmemcpy_208    # 6c: 18f71e63
	lw	a5, 0(a1)               # 70: 0005a783
	sb	a5, 0(a3)               # 74: 00f68023
	srli	a4, a5, 8               # 78: 0087d713
	sb	a4, 1(a3)               # 7c: 00e680a3
	srli	a4, a5, 16              # 80: 0107d713
	sb	a4, 2(a3)               # 84: 00e68123
	addi	a3, a3, 3               # 88: 00368693
	addi	a2, a2, -3              # 8c: ffd60613
	addi	a1, a1, 16              # 90: 01058593
	addi	a4, zero, 16            # 94: 01000713
.Lmemcpy_98:
	#: inv [j] a1: int(s + n - j + 13), a3: int(d + n - j), a2: int(j) where 17 <= j <= n, 4 | s + n - j + 1, 4 | d + n - j decreases j
	lw	a6, -12(a1)             # 98: ff45a803
	srliw	a5, a5, 24              # 9c: 0187d79b
	slli	a7, a6, 8               # a0: 00881893
	lw	t0, -8(a1)              # a4: ff85a283
	or	a5, a7, a5              # a8: 00f8e7b3
	sw	a5, 0(a3)               # ac: 00f6a023
	srliw	a5, a6, 24              # b0: 0188579b
	slli	a6, t0, 8               # b4: 00829813
	lw	a7, -4(a1)              # b8: ffc5a883
	or	a5, a6, a5              # bc: 00f867b3
	sw	a5, 4(a3)               # c0: 00f6a223
	srliw	a6, t0, 24              # c4: 0182d81b
	slli	t0, a7, 8               # c8: 00889293
	lw	a5, 0(a1)               # cc: 0005a783
	or	a6, t0, a6              # d0: 0102e833
	sw	a6, 8(a3)               # d4: 0106a423
	srliw	a6, a7, 24              # d8: 0188d81b
	slli	a7, a5, 8               # dc: 00879893
	or	a6, a7, a6              # e0: 0108e833
	sw	a6, 12(a3)              # e4: 0106a623
	addi	a3, a3, 16              # e8: 01068693
	addi	a2, a2, -16             # ec: ff060613
	addi	a1, a1, 16              # f0: 01058593
	bltu	a4, a2, .Lmemcpy_98     # f4: fac762e3
	addi	a1, a1, -13             # f8: ff358593
	andi	a4, a2, 16              # fc: 01067713
	beq	a4, zero, .Lmemcpy_210  # 100: 10070863
	jal	zero, .Lmemcpy_31c      # 104: 2180006f
.Lmemcpy_108:
	addi	a3, a0, 0               # 108: 00050693
	andi	a4, a3, 3               # 10c: 0036f713
	bne	a4, zero, .Lmemcpy_50   # 110: f40710e3
.Lmemcpy_114:
	#: join [k] a1: int(s + n - k), a3: int(d + n - k), a2: int(k) where 0 <= k <= n, 4 | d + n - k, (k = 0 || 4 | s + n - k)
	addi	a4, zero, 16            # 114: 01000713
	bltu	a2, a4, .Lmemcpy_150    # 118: 02e66c63
	addi	a4, zero, 15            # 11c: 00f00713
.Lmemcpy_120:
	#: inv [k] a1: int(s + n - k), a3: int(d + n - k), a2: int(k) where 16 <= k <= n, 4 | s + n - k, 4 | d + n - k decreases k
	lw	a5, 0(a1)               # 120: 0005a783
	lw	a6, 4(a1)               # 124: 0045a803
	lw	a7, 8(a1)               # 128: 0085a883
	lw	t0, 12(a1)              # 12c: 00c5a283
	sw	a5, 0(a3)               # 130: 00f6a023
	sw	a6, 4(a3)               # 134: 0106a223
	sw	a7, 8(a3)               # 138: 0116a423
	sw	t0, 12(a3)              # 13c: 0056a623
	addi	a1, a1, 16              # 140: 01058593
	addi	a2, a2, -16             # 144: ff060613
	addi	a3, a3, 16              # 148: 01068693
	bltu	a4, a2, .Lmemcpy_120    # 14c: fcc76ae3
.Lmemcpy_150:
	#: join [k] a1: int(s + n - k), a3: int(d + n - k), a2: int(k) where 0 <= k <= 15, k <= n, 4 | d + n - k, (k = 0 || 4 | s + n - k)
	andi	a4, a2, 8               # 150: 00867713
	beq	a4, zero, .Lmemcpy_170  # 154: 00070e63
	lw	a4, 0(a1)               # 158: 0005a703
	lw	a5, 4(a1)               # 15c: 0045a783
	sw	a4, 0(a3)               # 160: 00e6a023
	sw	a5, 4(a3)               # 164: 00f6a223
	addi	a3, a3, 8               # 168: 00868693
	addi	a1, a1, 8               # 16c: 00858593
.Lmemcpy_170:
	#: join [j, r] a2: int(j), a1: int(s + n - r), a3: int(d + n - r) where 0 <= r <= 7, 8 | j - r, 0 <= j <= 15, j <= n, 4 | d + n - r, (j = 0 || 4 | s + n - r)
	andi	a4, a2, 4               # 170: 00467713
	beq	a4, zero, .Lmemcpy_24c  # 174: 0c070c63
	lw	a4, 0(a1)               # 178: 0005a703
	sw	a4, 0(a3)               # 17c: 00e6a023
	addi	a3, a3, 4               # 180: 00468693
	addi	a1, a1, 4               # 184: 00458593
	jal	zero, .Lmemcpy_24c      # 188: 0c40006f
.Lmemcpy_18c:
	lw	a5, 0(a1)               # 18c: 0005a783
	sb	a5, 0(a3)               # 190: 00f68023
	addi	a3, a3, 1               # 194: 00168693
	addi	a2, a2, -1              # 198: fff60613
	addi	a1, a1, 16              # 19c: 01058593
	addi	a4, zero, 18            # 1a0: 01200713
.Lmemcpy_1a4:
	#: inv [j] a1: int(s + n - j + 15), a3: int(d + n - j), a2: int(j) where 19 <= j <= n, 4 | s + n - j + 3, 4 | d + n - j decreases j
	lw	a6, -12(a1)             # 1a4: ff45a803
	srliw	a5, a5, 8               # 1a8: 0087d79b
	slli	a7, a6, 24              # 1ac: 01881893
	lw	t0, -8(a1)              # 1b0: ff85a283
	or	a5, a7, a5              # 1b4: 00f8e7b3
	sw	a5, 0(a3)               # 1b8: 00f6a023
	srliw	a5, a6, 8               # 1bc: 0088579b
	slli	a6, t0, 24              # 1c0: 01829813
	lw	a7, -4(a1)              # 1c4: ffc5a883
	or	a5, a6, a5              # 1c8: 00f867b3
	sw	a5, 4(a3)               # 1cc: 00f6a223
	srliw	a6, t0, 8               # 1d0: 0082d81b
	slli	t0, a7, 24              # 1d4: 01889293
	lw	a5, 0(a1)               # 1d8: 0005a783
	or	a6, t0, a6              # 1dc: 0102e833
	sw	a6, 8(a3)               # 1e0: 0106a423
	srliw	a6, a7, 8               # 1e4: 0088d81b
	slli	a7, a5, 24              # 1e8: 01879893
	or	a6, a7, a6              # 1ec: 0108e833
	sw	a6, 12(a3)              # 1f0: 0106a623
	addi	a3, a3, 16              # 1f4: 01068693
	addi	a2, a2, -16             # 1f8: ff060613
	addi	a1, a1, 16              # 1fc: 01058593
	bltu	a4, a2, .Lmemcpy_1a4    # 200: fac762e3
	addi	a1, a1, -15             # 204: ff158593
.Lmemcpy_208:
	#: join [j] a2: int(j), a1: int(s + n - j), a3: int(d + n - j) where 0 <= j <= 31, j <= n
	andi	a4, a2, 16              # 208: 01067713
	bne	a4, zero, .Lmemcpy_31c  # 20c: 10071863
.Lmemcpy_210:
	#: join [j, r] a2: int(j), a1: int(s + n - r), a3: int(d + n - r) where 0 <= r <= 15, 16 | j - r, 0 <= j <= 31, j <= n
	andi	a4, a2, 8               # 210: 00867713
	bne	a4, zero, .Lmemcpy_3b0  # 214: 18071e63
.Lmemcpy_218:
	#: join [j, r] a2: int(j), a1: int(s + n - r), a3: int(d + n - r) where 0 <= r <= 7, 8 | j - r, 0 <= j <= 31, j <= n
	andi	a4, a2, 4               # 218: 00467713
	beq	a4, zero, .Lmemcpy_24c  # 21c: 02070863
.Lmemcpy_220:
	#: join [j, r] a2: int(j), a1: int(s + n - r), a3: int(d + n - r) where 4 <= r <= 7, 8 | j - r, 0 <= j <= 31, j <= n
	lb	a4, 0(a1)               # 220: 00058703
	lb	a5, 1(a1)               # 224: 00158783
	lb	a6, 2(a1)               # 228: 00258803
	sb	a4, 0(a3)               # 22c: 00e68023
	sb	a5, 1(a3)               # 230: 00f680a3
	lb	a4, 3(a1)               # 234: 00358703
	sb	a6, 2(a3)               # 238: 01068123
	addi	a1, a1, 4               # 23c: 00458593
	addi	a5, a3, 4               # 240: 00468793
	sb	a4, 3(a3)               # 244: 00e681a3
	addi	a3, a5, 0               # 248: 00078693
.Lmemcpy_24c:
	#: join [j, r] a2: int(j), a1: int(s + n - r), a3: int(d + n - r) where 0 <= r <= 3, 4 | j - r, 0 <= j <= 31, j <= n
	andi	a4, a2, 2               # 24c: 00267713
	bne	a4, zero, .Lmemcpy_260  # 250: 00071863
	andi	a2, a2, 1               # 254: 00167613
	bne	a2, zero, .Lmemcpy_284  # 258: 02061663
.Lmemcpy_25c:
	jalr	zero, 0(ra)             # 25c: 00008067
.Lmemcpy_260:
	#: join [j, r] a2: int(j), a1: int(s + n - r), a3: int(d + n - r) where 2 <= r <= 3, 4 | j - r, 0 <= j <= 31, j <= n
	lb	a4, 0(a1)               # 260: 00058703
	lb	a5, 1(a1)               # 264: 00158783
	sb	a4, 0(a3)               # 268: 00e68023
	addi	a1, a1, 2               # 26c: 00258593
	addi	a4, a3, 2               # 270: 00268713
	sb	a5, 1(a3)               # 274: 00f680a3
	addi	a3, a4, 0               # 278: 00070693
	andi	a2, a2, 1               # 27c: 00167613
	beq	a2, zero, .Lmemcpy_25c  # 280: fc060ee3
.Lmemcpy_284:
	#: join a1: int(s + n - 1), a3: int(d + n - 1) where 1 <= n
	lb	a1, 0(a1)               # 284: 00058583
	sb	a1, 0(a3)               # 288: 00b68023
	jalr	zero, 0(ra)             # 28c: 00008067
.Lmemcpy_290:
	lw	a5, 0(a1)               # 290: 0005a783
	sb	a5, 0(a3)               # 294: 00f68023
	srli	a4, a5, 8               # 298: 0087d713
	sb	a4, 1(a3)               # 29c: 00e680a3
	addi	a3, a3, 2               # 2a0: 00268693
	addi	a2, a2, -2              # 2a4: ffe60613
	addi	a1, a1, 16              # 2a8: 01058593
	addi	a4, zero, 17            # 2ac: 01100713
.Lmemcpy_2b0:
	#: inv [j] a1: int(s + n - j + 14), a3: int(d + n - j), a2: int(j) where 18 <= j <= n, 4 | s + n - j + 2, 4 | d + n - j decreases j
	lw	a6, -12(a1)             # 2b0: ff45a803
	srliw	a5, a5, 16              # 2b4: 0107d79b
	slli	a7, a6, 16              # 2b8: 01081893
	lw	t0, -8(a1)              # 2bc: ff85a283
	or	a5, a7, a5              # 2c0: 00f8e7b3
	sw	a5, 0(a3)               # 2c4: 00f6a023
	srliw	a5, a6, 16              # 2c8: 0108579b
	slli	a6, t0, 16              # 2cc: 01029813
	lw	a7, -4(a1)              # 2d0: ffc5a883
	or	a5, a6, a5              # 2d4: 00f867b3
	sw	a5, 4(a3)               # 2d8: 00f6a223
	srliw	a6, t0, 16              # 2dc: 0102d81b
	slli	t0, a7, 16              # 2e0: 01089293
	lw	a5, 0(a1)               # 2e4: 0005a783
	or	a6, t0, a6              # 2e8: 0102e833
	sw	a6, 8(a3)               # 2ec: 0106a423
	srliw	a6, a7, 16              # 2f0: 0108d81b
	slli	a7, a5, 16              # 2f4: 01079893
	or	a6, a7, a6              # 2f8: 0108e833
	sw	a6, 12(a3)              # 2fc: 0106a623
	addi	a3, a3, 16              # 300: 01068693
	addi	a2, a2, -16             # 304: ff060613
	addi	a1, a1, 16              # 308: 01058593
	bltu	a4, a2, .Lmemcpy_2b0    # 30c: fac762e3
	addi	a1, a1, -14             # 310: ff258593
	andi	a4, a2, 16              # 314: 01067713
	beq	a4, zero, .Lmemcpy_210  # 318: ee070ce3
.Lmemcpy_31c:
	#: join [j] a2: int(j), a1: int(s + n - j), a3: int(d + n - j) where 16 <= j <= 31, j <= n
	lb	a4, 0(a1)               # 31c: 00058703
	lb	a5, 1(a1)               # 320: 00158783
	lb	a6, 2(a1)               # 324: 00258803
	sb	a4, 0(a3)               # 328: 00e68023
	sb	a5, 1(a3)               # 32c: 00f680a3
	lb	a4, 3(a1)               # 330: 00358703
	sb	a6, 2(a3)               # 334: 01068123
	lb	a5, 4(a1)               # 338: 00458783
	lb	a6, 5(a1)               # 33c: 00558803
	sb	a4, 3(a3)               # 340: 00e681a3
	lb	a4, 6(a1)               # 344: 00658703
	sb	a5, 4(a3)               # 348: 00f68223
	sb	a6, 5(a3)               # 34c: 010682a3
	lb	a5, 7(a1)               # 350: 00758783
	sb	a4, 6(a3)               # 354: 00e68323
	lb	a4, 8(a1)               # 358: 00858703
	lb	a6, 9(a1)               # 35c: 00958803
	sb	a5, 7(a3)               # 360: 00f683a3
	lb	a5, 10(a1)              # 364: 00a58783
	sb	a4, 8(a3)               # 368: 00e68423
	sb	a6, 9(a3)               # 36c: 010684a3
	lb	a4, 11(a1)              # 370: 00b58703
	sb	a5, 10(a3)              # 374: 00f68523
	lb	a5, 12(a1)              # 378: 00c58783
	lb	a6, 13(a1)              # 37c: 00d58803
	sb	a4, 11(a3)              # 380: 00e685a3
	lb	a4, 14(a1)              # 384: 00e58703
	sb	a5, 12(a3)              # 388: 00f68623
	sb	a6, 13(a3)              # 38c: 010686a3
	lb	a5, 15(a1)              # 390: 00f58783
	sb	a4, 14(a3)              # 394: 00e68723
	addi	a1, a1, 16              # 398: 01058593
	addi	a4, a3, 16              # 39c: 01068713
	sb	a5, 15(a3)              # 3a0: 00f687a3
	addi	a3, a4, 0               # 3a4: 00070693
	andi	a4, a2, 8               # 3a8: 00867713
	beq	a4, zero, .Lmemcpy_218  # 3ac: e60706e3
.Lmemcpy_3b0:
	#: join [j, r] a2: int(j), a1: int(s + n - r), a3: int(d + n - r) where 8 <= r <= 15, 16 | j - r, 0 <= j <= 31, j <= n
	lb	a4, 0(a1)               # 3b0: 00058703
	lb	a5, 1(a1)               # 3b4: 00158783
	lb	a6, 2(a1)               # 3b8: 00258803
	sb	a4, 0(a3)               # 3bc: 00e68023
	sb	a5, 1(a3)               # 3c0: 00f680a3
	lb	a4, 3(a1)               # 3c4: 00358703
	sb	a6, 2(a3)               # 3c8: 01068123
	lb	a5, 4(a1)               # 3cc: 00458783
	lb	a6, 5(a1)               # 3d0: 00558803
	sb	a4, 3(a3)               # 3d4: 00e681a3
	lb	a4, 6(a1)               # 3d8: 00658703
	sb	a5, 4(a3)               # 3dc: 00f68223
	sb	a6, 5(a3)               # 3e0: 010682a3
	lb	a5, 7(a1)               # 3e4: 00758783
	sb	a4, 6(a3)               # 3e8: 00e68323
	addi	a1, a1, 8               # 3ec: 00858593
	addi	a4, a3, 8               # 3f0: 00868713
	sb	a5, 7(a3)               # 3f4: 00f683a3
	addi	a3, a4, 0               # 3f8: 00070693
	andi	a4, a2, 4               # 3fc: 00467713
	bne	a4, zero, .Lmemcpy_220  # 400: e20710e3
	jal	zero, .Lmemcpy_24c      # 404: e49ff06f
	.size memcpy, .-memcpy
