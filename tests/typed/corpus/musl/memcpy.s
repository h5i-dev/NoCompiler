# musl 1.2.5 src/string/memcpy.c (MIT, see examples/musl/COPYRIGHT), compiled by scripts/musl-trial/build.sh.
# Instructions as compiled, unchanged (scripts/musl-trial/verify.sh checks the bytes).
# Annotations are the lines that start with hash-colon (provisional syntax of docs/Tab 1.md; see docs/typed/musl-trial.md).
# Predicted (fixed before compiling): reject (v0 rules: andi n, 2^k tails)
# Expected now (after reading the compiled code): reject. (1) As predicted, the tails 'if (n&8)', 'if (n&4)', ... are andi a1, a2, 8 + beq (0x15c, 0x17c, ...): x != 0 does not give k >= 8, so lw 4(a4) at 0x168 fails. (2) S2: 33 violations (11 backward-edge targets; the misaligned cases share tail blocks reached backwards). (3) The head loop test '(uintptr_t)s % 4 && n' is branch-free (0x0-0x10, 0x30-0x4c). Annotated in full (added when the checker got --loops natural; same scheme as memcpy-x.ann): head loop, aligned loop, the three misaligned loops, and a join at every tail block.
#! expect memcpy: accept
#! expect-interval memcpy: reject cfg
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
	sltiu	a3, a3, 1               # 4: 0016b693
	sltiu	a4, a2, 1               # 8: 00163713
	or	a3, a3, a4              # c: 00e6e6b3
	bne	a3, zero, .Lmemcpy_110  # 10: 10069063
	addi	a5, a1, 1               # 14: 00158793
	addi	a6, a0, 0               # 18: 00050813
.Lmemcpy_1c:
	#: inv [m] a1: int(s + n - m), a5: int(s + n - m + 1), a6: int(d + n - m), a2: int(m) where 1 <= m <= n decreases m
	lb	a7, 0(a1)               # 1c: 00058883
	addi	a4, a1, 1               # 20: 00158713
	addi	a3, a6, 1               # 24: 00180693
	sb	a7, 0(a6)               # 28: 01180023
	addi	a2, a2, -1              # 2c: fff60613
	andi	a1, a5, 3               # 30: 0037f593
	sltu	a1, zero, a1            # 34: 00b035b3
	sltu	a6, zero, a2            # 38: 00c03833
	and	a7, a1, a6              # 3c: 0105f8b3
	addi	a5, a5, 1               # 40: 00178793
	addi	a1, a4, 0               # 44: 00070593
	addi	a6, a3, 0               # 48: 00068813
	bne	a7, zero, .Lmemcpy_1c   # 4c: fc0898e3
	andi	a1, a3, 3               # 50: 0036f593
	beq	a1, zero, .Lmemcpy_120  # 54: 0c058663
.Lmemcpy_58:
	#: join [m, x] a4: int(s + n - m), a3: int(d + n - m), a2: int(m), a1: int(x) where 0 <= m <= n, 1 <= x <= 3, 4 | d + n - m - x, (m = 0 || 4 | s + n - m)
	addi	a5, zero, 32            # 58: 02000793
	bltu	a2, a5, .Lmemcpy_214    # 5c: 1af66c63
	addi	a5, zero, 3             # 60: 00300793
	beq	a1, a5, .Lmemcpy_198    # 64: 12f58a63
	addi	a5, zero, 2             # 68: 00200793
	beq	a1, a5, .Lmemcpy_29c    # 6c: 22f58863
	addi	a5, zero, 1             # 70: 00100793
	bne	a1, a5, .Lmemcpy_214    # 74: 1af59063
	lw	a5, 0(a4)               # 78: 00072783
	sb	a5, 0(a3)               # 7c: 00f68023
	srli	a1, a5, 8               # 80: 0087d593
	sb	a1, 1(a3)               # 84: 00b680a3
	srli	a1, a5, 16              # 88: 0107d593
	sb	a1, 2(a3)               # 8c: 00b68123
	addi	a3, a3, 3               # 90: 00368693
	addi	a2, a2, -3              # 94: ffd60613
	addi	a1, a4, 16              # 98: 01070593
	addi	a4, zero, 16            # 9c: 01000713
.Lmemcpy_a0:
	#: inv [j] a1: int(s + n - j + 13), a3: int(d + n - j), a2: int(j) where 17 <= j <= n, 4 | s + n - j + 1, 4 | d + n - j decreases j
	lw	a6, -12(a1)             # a0: ff45a803
	srliw	a5, a5, 24              # a4: 0187d79b
	slli	a7, a6, 8               # a8: 00881893
	lw	t0, -8(a1)              # ac: ff85a283
	or	a5, a7, a5              # b0: 00f8e7b3
	sw	a5, 0(a3)               # b4: 00f6a023
	srliw	a5, a6, 24              # b8: 0188579b
	slli	a6, t0, 8               # bc: 00829813
	lw	a7, -4(a1)              # c0: ffc5a883
	or	a5, a6, a5              # c4: 00f867b3
	sw	a5, 4(a3)               # c8: 00f6a223
	srliw	a6, t0, 24              # cc: 0182d81b
	slli	t0, a7, 8               # d0: 00889293
	lw	a5, 0(a1)               # d4: 0005a783
	or	a6, t0, a6              # d8: 0102e833
	sw	a6, 8(a3)               # dc: 0106a423
	srliw	a6, a7, 24              # e0: 0188d81b
	slli	a7, a5, 8               # e4: 00879893
	or	a6, a7, a6              # e8: 0108e833
	sw	a6, 12(a3)              # ec: 0106a623
	addi	a3, a3, 16              # f0: 01068693
	addi	a2, a2, -16             # f4: ff060613
	addi	a1, a1, 16              # f8: 01058593
	bltu	a4, a2, .Lmemcpy_a0     # fc: fac762e3
	addi	a4, a1, -13             # 100: ff358713
	andi	a1, a2, 16              # 104: 01067593
	beq	a1, zero, .Lmemcpy_21c  # 108: 10058a63
	jal	zero, .Lmemcpy_328      # 10c: 21c0006f
.Lmemcpy_110:
	addi	a3, a0, 0               # 110: 00050693
	addi	a4, a1, 0               # 114: 00058713
	andi	a1, a3, 3               # 118: 0036f593
	bne	a1, zero, .Lmemcpy_58   # 11c: f2059ee3
.Lmemcpy_120:
	#: join [k] a4: int(s + n - k), a3: int(d + n - k), a2: int(k) where 0 <= k <= n, 4 | d + n - k, (k = 0 || 4 | s + n - k)
	addi	a1, zero, 16            # 120: 01000593
	bltu	a2, a1, .Lmemcpy_15c    # 124: 02b66c63
	addi	a1, zero, 15            # 128: 00f00593
.Lmemcpy_12c:
	#: inv [k] a4: int(s + n - k), a3: int(d + n - k), a2: int(k) where 16 <= k <= n, 4 | s + n - k, 4 | d + n - k decreases k
	lw	a5, 0(a4)               # 12c: 00072783
	lw	a6, 4(a4)               # 130: 00472803
	lw	a7, 8(a4)               # 134: 00872883
	lw	t0, 12(a4)              # 138: 00c72283
	sw	a5, 0(a3)               # 13c: 00f6a023
	sw	a6, 4(a3)               # 140: 0106a223
	sw	a7, 8(a3)               # 144: 0116a423
	sw	t0, 12(a3)              # 148: 0056a623
	addi	a4, a4, 16              # 14c: 01070713
	addi	a2, a2, -16             # 150: ff060613
	addi	a3, a3, 16              # 154: 01068693
	bltu	a1, a2, .Lmemcpy_12c    # 158: fcc5eae3
.Lmemcpy_15c:
	#: join [k] a4: int(s + n - k), a3: int(d + n - k), a2: int(k) where 0 <= k <= 15, k <= n, 4 | d + n - k, (k = 0 || 4 | s + n - k)
	andi	a1, a2, 8               # 15c: 00867593
	beq	a1, zero, .Lmemcpy_17c  # 160: 00058e63
	lw	a1, 0(a4)               # 164: 00072583
	lw	a5, 4(a4)               # 168: 00472783
	sw	a1, 0(a3)               # 16c: 00b6a023
	sw	a5, 4(a3)               # 170: 00f6a223
	addi	a3, a3, 8               # 174: 00868693
	addi	a4, a4, 8               # 178: 00870713
.Lmemcpy_17c:
	#: join [j, r] a2: int(j), a4: int(s + n - r), a3: int(d + n - r) where 0 <= r <= 7, 8 | j - r, 0 <= j <= 15, j <= n, 4 | d + n - r, (j = 0 || 4 | s + n - r)
	andi	a1, a2, 4               # 17c: 00467593
	beq	a1, zero, .Lmemcpy_258  # 180: 0c058c63
	lw	a1, 0(a4)               # 184: 00072583
	sw	a1, 0(a3)               # 188: 00b6a023
	addi	a3, a3, 4               # 18c: 00468693
	addi	a4, a4, 4               # 190: 00470713
	jal	zero, .Lmemcpy_258      # 194: 0c40006f
.Lmemcpy_198:
	lw	a5, 0(a4)               # 198: 00072783
	sb	a5, 0(a3)               # 19c: 00f68023
	addi	a3, a3, 1               # 1a0: 00168693
	addi	a2, a2, -1              # 1a4: fff60613
	addi	a1, a4, 16              # 1a8: 01070593
	addi	a4, zero, 18            # 1ac: 01200713
.Lmemcpy_1b0:
	#: inv [j] a1: int(s + n - j + 15), a3: int(d + n - j), a2: int(j) where 19 <= j <= n, 4 | s + n - j + 3, 4 | d + n - j decreases j
	lw	a6, -12(a1)             # 1b0: ff45a803
	srliw	a5, a5, 8               # 1b4: 0087d79b
	slli	a7, a6, 24              # 1b8: 01881893
	lw	t0, -8(a1)              # 1bc: ff85a283
	or	a5, a7, a5              # 1c0: 00f8e7b3
	sw	a5, 0(a3)               # 1c4: 00f6a023
	srliw	a5, a6, 8               # 1c8: 0088579b
	slli	a6, t0, 24              # 1cc: 01829813
	lw	a7, -4(a1)              # 1d0: ffc5a883
	or	a5, a6, a5              # 1d4: 00f867b3
	sw	a5, 4(a3)               # 1d8: 00f6a223
	srliw	a6, t0, 8               # 1dc: 0082d81b
	slli	t0, a7, 24              # 1e0: 01889293
	lw	a5, 0(a1)               # 1e4: 0005a783
	or	a6, t0, a6              # 1e8: 0102e833
	sw	a6, 8(a3)               # 1ec: 0106a423
	srliw	a6, a7, 8               # 1f0: 0088d81b
	slli	a7, a5, 24              # 1f4: 01879893
	or	a6, a7, a6              # 1f8: 0108e833
	sw	a6, 12(a3)              # 1fc: 0106a623
	addi	a3, a3, 16              # 200: 01068693
	addi	a2, a2, -16             # 204: ff060613
	addi	a1, a1, 16              # 208: 01058593
	bltu	a4, a2, .Lmemcpy_1b0    # 20c: fac762e3
	addi	a4, a1, -15             # 210: ff158713
.Lmemcpy_214:
	#: join [j] a2: int(j), a4: int(s + n - j), a3: int(d + n - j) where 0 <= j <= 31, j <= n
	andi	a1, a2, 16              # 214: 01067593
	bne	a1, zero, .Lmemcpy_328  # 218: 10059863
.Lmemcpy_21c:
	#: join [j, r] a2: int(j), a4: int(s + n - r), a3: int(d + n - r) where 0 <= r <= 15, 16 | j - r, 0 <= j <= 31, j <= n
	andi	a1, a2, 8               # 21c: 00867593
	bne	a1, zero, .Lmemcpy_3bc  # 220: 18059e63
.Lmemcpy_224:
	#: join [j, r] a2: int(j), a4: int(s + n - r), a3: int(d + n - r) where 0 <= r <= 7, 8 | j - r, 0 <= j <= 31, j <= n
	andi	a1, a2, 4               # 224: 00467593
	beq	a1, zero, .Lmemcpy_258  # 228: 02058863
.Lmemcpy_22c:
	#: join [j, r] a2: int(j), a4: int(s + n - r), a3: int(d + n - r) where 4 <= r <= 7, 8 | j - r, 0 <= j <= 31, j <= n
	lb	a1, 0(a4)               # 22c: 00070583
	lb	a5, 1(a4)               # 230: 00170783
	lb	a6, 2(a4)               # 234: 00270803
	sb	a1, 0(a3)               # 238: 00b68023
	sb	a5, 1(a3)               # 23c: 00f680a3
	lb	a1, 3(a4)               # 240: 00370583
	sb	a6, 2(a3)               # 244: 01068123
	addi	a4, a4, 4               # 248: 00470713
	addi	a5, a3, 4               # 24c: 00468793
	sb	a1, 3(a3)               # 250: 00b681a3
	addi	a3, a5, 0               # 254: 00078693
.Lmemcpy_258:
	#: join [j, r] a2: int(j), a4: int(s + n - r), a3: int(d + n - r) where 0 <= r <= 3, 4 | j - r, 0 <= j <= 31, j <= n
	andi	a1, a2, 2               # 258: 00267593
	bne	a1, zero, .Lmemcpy_26c  # 25c: 00059863
	andi	a1, a2, 1               # 260: 00167593
	bne	a1, zero, .Lmemcpy_290  # 264: 02059663
.Lmemcpy_268:
	jalr	zero, 0(ra)             # 268: 00008067
.Lmemcpy_26c:
	#: join [j, r] a2: int(j), a4: int(s + n - r), a3: int(d + n - r) where 2 <= r <= 3, 4 | j - r, 0 <= j <= 31, j <= n
	lb	a1, 0(a4)               # 26c: 00070583
	lb	a5, 1(a4)               # 270: 00170783
	sb	a1, 0(a3)               # 274: 00b68023
	addi	a4, a4, 2               # 278: 00270713
	addi	a1, a3, 2               # 27c: 00268593
	sb	a5, 1(a3)               # 280: 00f680a3
	addi	a3, a1, 0               # 284: 00058693
	andi	a1, a2, 1               # 288: 00167593
	beq	a1, zero, .Lmemcpy_268  # 28c: fc058ee3
.Lmemcpy_290:
	#: join a4: int(s + n - 1), a3: int(d + n - 1) where 1 <= n
	lb	a1, 0(a4)               # 290: 00070583
	sb	a1, 0(a3)               # 294: 00b68023
	jalr	zero, 0(ra)             # 298: 00008067
.Lmemcpy_29c:
	lw	a5, 0(a4)               # 29c: 00072783
	sb	a5, 0(a3)               # 2a0: 00f68023
	srli	a1, a5, 8               # 2a4: 0087d593
	sb	a1, 1(a3)               # 2a8: 00b680a3
	addi	a3, a3, 2               # 2ac: 00268693
	addi	a2, a2, -2              # 2b0: ffe60613
	addi	a1, a4, 16              # 2b4: 01070593
	addi	a4, zero, 17            # 2b8: 01100713
.Lmemcpy_2bc:
	#: inv [j] a1: int(s + n - j + 14), a3: int(d + n - j), a2: int(j) where 18 <= j <= n, 4 | s + n - j + 2, 4 | d + n - j decreases j
	lw	a6, -12(a1)             # 2bc: ff45a803
	srliw	a5, a5, 16              # 2c0: 0107d79b
	slli	a7, a6, 16              # 2c4: 01081893
	lw	t0, -8(a1)              # 2c8: ff85a283
	or	a5, a7, a5              # 2cc: 00f8e7b3
	sw	a5, 0(a3)               # 2d0: 00f6a023
	srliw	a5, a6, 16              # 2d4: 0108579b
	slli	a6, t0, 16              # 2d8: 01029813
	lw	a7, -4(a1)              # 2dc: ffc5a883
	or	a5, a6, a5              # 2e0: 00f867b3
	sw	a5, 4(a3)               # 2e4: 00f6a223
	srliw	a6, t0, 16              # 2e8: 0102d81b
	slli	t0, a7, 16              # 2ec: 01089293
	lw	a5, 0(a1)               # 2f0: 0005a783
	or	a6, t0, a6              # 2f4: 0102e833
	sw	a6, 8(a3)               # 2f8: 0106a423
	srliw	a6, a7, 16              # 2fc: 0108d81b
	slli	a7, a5, 16              # 300: 01079893
	or	a6, a7, a6              # 304: 0108e833
	sw	a6, 12(a3)              # 308: 0106a623
	addi	a3, a3, 16              # 30c: 01068693
	addi	a2, a2, -16             # 310: ff060613
	addi	a1, a1, 16              # 314: 01058593
	bltu	a4, a2, .Lmemcpy_2bc    # 318: fac762e3
	addi	a4, a1, -14             # 31c: ff258713
	andi	a1, a2, 16              # 320: 01067593
	beq	a1, zero, .Lmemcpy_21c  # 324: ee058ce3
.Lmemcpy_328:
	#: join [j] a2: int(j), a4: int(s + n - j), a3: int(d + n - j) where 16 <= j <= 31, j <= n
	lb	a1, 0(a4)               # 328: 00070583
	lb	a5, 1(a4)               # 32c: 00170783
	lb	a6, 2(a4)               # 330: 00270803
	sb	a1, 0(a3)               # 334: 00b68023
	sb	a5, 1(a3)               # 338: 00f680a3
	lb	a1, 3(a4)               # 33c: 00370583
	sb	a6, 2(a3)               # 340: 01068123
	lb	a5, 4(a4)               # 344: 00470783
	lb	a6, 5(a4)               # 348: 00570803
	sb	a1, 3(a3)               # 34c: 00b681a3
	lb	a1, 6(a4)               # 350: 00670583
	sb	a5, 4(a3)               # 354: 00f68223
	sb	a6, 5(a3)               # 358: 010682a3
	lb	a5, 7(a4)               # 35c: 00770783
	sb	a1, 6(a3)               # 360: 00b68323
	lb	a1, 8(a4)               # 364: 00870583
	lb	a6, 9(a4)               # 368: 00970803
	sb	a5, 7(a3)               # 36c: 00f683a3
	lb	a5, 10(a4)              # 370: 00a70783
	sb	a1, 8(a3)               # 374: 00b68423
	sb	a6, 9(a3)               # 378: 010684a3
	lb	a1, 11(a4)              # 37c: 00b70583
	sb	a5, 10(a3)              # 380: 00f68523
	lb	a5, 12(a4)              # 384: 00c70783
	lb	a6, 13(a4)              # 388: 00d70803
	sb	a1, 11(a3)              # 38c: 00b685a3
	lb	a1, 14(a4)              # 390: 00e70583
	sb	a5, 12(a3)              # 394: 00f68623
	sb	a6, 13(a3)              # 398: 010686a3
	lb	a5, 15(a4)              # 39c: 00f70783
	sb	a1, 14(a3)              # 3a0: 00b68723
	addi	a4, a4, 16              # 3a4: 01070713
	addi	a1, a3, 16              # 3a8: 01068593
	sb	a5, 15(a3)              # 3ac: 00f687a3
	addi	a3, a1, 0               # 3b0: 00058693
	andi	a1, a2, 8               # 3b4: 00867593
	beq	a1, zero, .Lmemcpy_224  # 3b8: e60586e3
.Lmemcpy_3bc:
	#: join [j, r] a2: int(j), a4: int(s + n - r), a3: int(d + n - r) where 8 <= r <= 15, 16 | j - r, 0 <= j <= 31, j <= n
	lb	a1, 0(a4)               # 3bc: 00070583
	lb	a5, 1(a4)               # 3c0: 00170783
	lb	a6, 2(a4)               # 3c4: 00270803
	sb	a1, 0(a3)               # 3c8: 00b68023
	sb	a5, 1(a3)               # 3cc: 00f680a3
	lb	a1, 3(a4)               # 3d0: 00370583
	sb	a6, 2(a3)               # 3d4: 01068123
	lb	a5, 4(a4)               # 3d8: 00470783
	lb	a6, 5(a4)               # 3dc: 00570803
	sb	a1, 3(a3)               # 3e0: 00b681a3
	lb	a1, 6(a4)               # 3e4: 00670583
	sb	a5, 4(a3)               # 3e8: 00f68223
	sb	a6, 5(a3)               # 3ec: 010682a3
	lb	a5, 7(a4)               # 3f0: 00770783
	sb	a1, 6(a3)               # 3f4: 00b68323
	addi	a4, a4, 8               # 3f8: 00870713
	addi	a1, a3, 8               # 3fc: 00868593
	sb	a5, 7(a3)               # 400: 00f683a3
	addi	a3, a1, 0               # 404: 00058693
	andi	a1, a2, 4               # 408: 00467593
	bne	a1, zero, .Lmemcpy_22c  # 40c: e20590e3
	jal	zero, .Lmemcpy_258      # 410: e49ff06f
	.size memcpy, .-memcpy
