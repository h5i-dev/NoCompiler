# musl 1.2.5 src/string/memchr.c (MIT, see examples/musl/COPYRIGHT), compiled by scripts/musl-trial/build.sh.
# Instructions as compiled, unchanged (scripts/musl-trial/verify.sh checks the bytes).
# Annotations are the lines that start with hash-colon (provisional syntax of docs/Tab 1.md; see docs/typed/musl-trial.md).
# Predicted (fixed before compiling): accept
# Expected now (after reading the compiled code): reject. (1) S2: clang places the return block 0x4c after the head loop and reaches it by backward branches (0x5c, 0xcc), giving loop intervals [0x4c,0xcc] and [0xc8,0xd8] that are not nested, and edges entering [0x4c,0xcc] in the middle. (2) Even with S2 fixed: the head-loop conditions '(s&7) && n' are branch-free sltiu/or/sltu/and (0x0-0x14, 0x2c-0x40), so 1 <= m at the head loop is not derivable. (3) The word loop 0x9c is reached through the join 0x60, also from the 'found' path 0x20 where s is not aligned; that path never reaches the word loop only because it re-reads the same byte (memory contents, not in v0 types), so 8 | p at 0x9c is not derivable under the coarse join (decision 2). Static data (constant pool via auipc+addi+ld) needs the note's static-data rule (implementation decision I14 postpones it).
#! expect memchr: reject static-data
#: fn memchr [s, n]
#:   in     a0: int(s), a2: int(n)
#:   borrow s |-> bytes[n] ro
#:   out    a0: int
#:   stack  0
	.text
	.globl memchr
	.p2align 2
	.type memchr,@function
memchr:
	andi	a3, a0, 7               # 0: 00757693
	sltiu	a3, a3, 1               # 4: 0016b693
	sltiu	a4, a2, 1               # 8: 00163713
	or	a4, a3, a4              # c: 00e6e733
	andi	a3, a1, 255             # 10: 0ff5f693
	bne	a4, zero, .Lmemchr_54   # 14: 04071063
	addi	a1, a0, 1               # 18: 00150593
.Lmemchr_1c:
	#: inv [p, m] a0: int(p), a1: int(p + 1), a2: int(m) where s <= p, p + m = s + n, 1 <= m decreases m
	lbu	a4, 0(a0)               # 1c: 00054703
	beq	a4, a3, .Lmemchr_60     # 20: 04d70063
	addi	a0, a0, 1               # 24: 00150513
	addi	a2, a2, -1              # 28: fff60613
	andi	a4, a1, 7               # 2c: 0075f713
	sltu	a5, zero, a4            # 30: 00e037b3
	sltu	a4, zero, a2            # 34: 00c03733
	and	a5, a5, a4              # 38: 00e7f7b3
	addi	a1, a1, 1               # 3c: 00158593
	bne	a5, zero, .Lmemchr_1c   # 40: fc079ee3
	addi	a1, zero, 0             # 44: 00000593
	bne	a4, zero, .Lmemchr_60   # 48: 00071c63
.Lmemchr_4c:
	#: inv a1: int
	# 0x4c is a return block, not a loop: no measure exists, so there is no decreases clause.
	addi	a0, a1, 0               # 4c: 00058513
	jalr	zero, 0(ra)             # 50: 00008067
.Lmemchr_54:
	sltu	a4, zero, a2            # 54: 00c03733
	addi	a1, zero, 0             # 58: 00000593
	beq	a4, zero, .Lmemchr_4c   # 5c: fe0708e3
.Lmemchr_60:
	#: join [p, m] a0: int(p), a2: int(m) where s <= p, p + m = s + n, 1 <= m
	lbu	a1, 0(a0)               # 60: 00054583
	beq	a1, a3, .Lmemchr_c0     # 64: 04d58e63
	addi	a1, zero, 8             # 68: 00800593
	bltu	a2, a1, .Lmemchr_c0     # 6c: 04b66a63
.Lpcrel_70:
	auipc	a1, %pcrel_hi(.LCPI0_0) # 70: 00000597
	addi	a1, a1, %pcrel_lo(.Lpcrel_70)# 74: 00058593
	ld	a5, 0(a1)               # 78: 0005b783
.Lpcrel_7c:
	auipc	a1, %pcrel_hi(.LCPI0_1) # 7c: 00000597
	addi	a1, a1, %pcrel_lo(.Lpcrel_7c)# 80: 00058593
	ld	a1, 0(a1)               # 84: 0005b583
.Lpcrel_88:
	auipc	a4, %pcrel_hi(.LCPI0_2) # 88: 00000717
	addi	a4, a4, %pcrel_lo(.Lpcrel_88)# 8c: 00070713
	ld	a4, 0(a4)               # 90: 00073703
	mul	a5, a3, a5              # 94: 02f687b3
	addi	a6, zero, 7             # 98: 00700813
.Lmemchr_9c:
	#: inv [p, m] a0: int(p), a2: int(m) where s <= p, p + m = s + n, 8 <= m, 8 | p decreases m
	ld	a7, 0(a0)               # 9c: 00053883
	xor	a7, a7, a5              # a0: 00f8c8b3
	add	t0, a7, a4              # a4: 00e882b3
	andn	a7, a1, a7              # a8: 4115f8b3
	and	a7, a7, t0              # ac: 0058f8b3
	bne	a7, zero, .Lmemchr_c4   # b0: 00089a63
	addi	a2, a2, -8              # b4: ff860613
	addi	a0, a0, 8               # b8: 00850513
	bltu	a6, a2, .Lmemchr_9c     # bc: fec860e3
.Lmemchr_c0:
	#: join [p, m] a0: int(p), a2: int(m) where s <= p, p + m = s + n, 0 <= m
	beq	a2, zero, .Lmemchr_dc   # c0: 00060e63
.Lmemchr_c4:
	#: join [p, m] a0: int(p), a2: int(m) where s <= p, p + m = s + n, 1 <= m
	addi	a1, a0, 0               # c4: 00050593
.Lmemchr_c8:
	#: inv [q, m] a1: int(q), a2: int(m) where s <= q, q + m = s + n, 1 <= m decreases m
	lbu	a0, 0(a1)               # c8: 0005c503
	beq	a0, a3, .Lmemchr_4c     # cc: f8d500e3
	addi	a2, a2, -1              # d0: fff60613
	addi	a1, a1, 1               # d4: 00158593
	bne	a2, zero, .Lmemchr_c8   # d8: fe0618e3
.Lmemchr_dc:
	addi	a1, zero, 0             # dc: 00000593
	addi	a0, a1, 0               # e0: 00058513
	jalr	zero, 0(ra)             # e4: 00008067
	.size memchr, .-memchr

	.section .rodata.cst8,"aM",@progbits,8
	.p2align 3
.LCPI0_0:
	.quad	0x0101010101010101
.LCPI0_1:
	.quad	0x8080808080808080
.LCPI0_2:
	.quad	0xfefefefefefefeff
