# musl 1.2.5 src/string/memchr.c (MIT, see examples/musl/COPYRIGHT), compiled by scripts/musl-trial/build.sh
# with -mllvm -riscv-disable-using-constant-pool-for-large-ints (constants inline, no static data).
# Instructions as compiled, unchanged (scripts/musl-trial/verify.sh checks the bytes).
# Annotations are the lines that start with hash-colon (provisional syntax of docs/Tab 1.md; see docs/typed/musl-trial.md).
# Predicted (fixed before compiling this variant): reject (as memchr without static data)
# Expected now (after reading the compiled code): reject. (1) S2: clang places the return block 0x4c after the head loop and reaches it by backward branches (0x5c, 0xf4), giving loop intervals [0x4c,0xf4] and [0xf0,0x100] that are not nested, and edges entering [0x4c,0xf4] in the middle. (2) Even with S2 fixed: the head-loop conditions '(s&7) && n' are branch-free sltiu/or/sltu/and (0x0-0x14, 0x2c-0x40), so 1 <= m at the head loop is not derivable. (3) The word loop 0xc4 is reached through the join 0x60, also from the 'found' path 0x20 where s is not aligned; that path never reaches the word loop only because it re-reads the same byte (memory contents, not in v0 types), so 8 | p at 0xc4 is not derivable under the coarse join (decision 2).
#! expect memchr: reject cfg
#: fn memchr [s, n]
#:   in     a0: int(s), a2: int(n)
#:   borrow s |-> bytes[n] ro
#:   out    a0: int
#:   stack  0
	.section .text.memchr,"ax",@progbits
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
	#: join a1: int
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
	beq	a1, a3, .Lmemchr_e8     # 64: 08d58263
	addi	a1, zero, 8             # 68: 00800593
	bltu	a2, a1, .Lmemchr_e8     # 6c: 06b66e63
	lui	a1, 4112                # 70: 010105b7
	addiw	a1, a1, 257             # 74: 1015859b
	slli	a1, a1, 16              # 78: 01059593
	addi	a1, a1, 257             # 7c: 10158593
	slli	a1, a1, 16              # 80: 01059593
	addi	a1, a1, 257             # 84: 10158593
	mul	a1, a3, a1              # 88: 02b685b3
	lui	a4, 983297              # 8c: f0101737
	slli	a4, a4, 4               # 90: 00471713
	addi	a4, a4, 257             # 94: 10170713
	slli	a4, a4, 16              # 98: 01071713
	addi	a4, a4, 257             # 9c: 10170713
	slli	a4, a4, 15              # a0: 00f71713
	addi	a4, a4, 128             # a4: 08070713
	lui	a5, 1044464             # a8: feff07b7
	addiw	a5, a5, -257            # ac: eff7879b
	slli	a5, a5, 16              # b0: 01079793
	addi	a5, a5, -257            # b4: eff78793
	slli	a5, a5, 16              # b8: 01079793
	addi	a5, a5, -257            # bc: eff78793
	addi	a6, zero, 7             # c0: 00700813
.Lmemchr_c4:
	#: inv [p, m] a0: int(p), a2: int(m) where s <= p, p + m = s + n, 8 <= m, 8 | p decreases m
	ld	a7, 0(a0)               # c4: 00053883
	xor	a7, a7, a1              # c8: 00b8c8b3
	add	t0, a7, a5              # cc: 00f882b3
	andn	a7, a4, a7              # d0: 411778b3
	and	a7, a7, t0              # d4: 0058f8b3
	bne	a7, zero, .Lmemchr_ec   # d8: 00089a63
	addi	a2, a2, -8              # dc: ff860613
	addi	a0, a0, 8               # e0: 00850513
	bltu	a6, a2, .Lmemchr_c4     # e4: fec860e3
.Lmemchr_e8:
	#: join [p, m] a0: int(p), a2: int(m) where s <= p, p + m = s + n, 0 <= m
	beq	a2, zero, .Lmemchr_104  # e8: 00060e63
.Lmemchr_ec:
	#: join [p, m] a0: int(p), a2: int(m) where s <= p, p + m = s + n, 1 <= m
	addi	a1, a0, 0               # ec: 00050593
.Lmemchr_f0:
	#: inv [q, m] a1: int(q), a2: int(m) where s <= q, q + m = s + n, 1 <= m decreases m
	lbu	a0, 0(a1)               # f0: 0005c503
	beq	a0, a3, .Lmemchr_4c     # f4: f4d50ce3
	addi	a2, a2, -1              # f8: fff60613
	addi	a1, a1, 1               # fc: 00158593
	bne	a2, zero, .Lmemchr_f0   # 100: fe0618e3
.Lmemchr_104:
	addi	a1, zero, 0             # 104: 00000593
	addi	a0, a1, 0               # 108: 00058513
	jalr	zero, 0(ra)             # 10c: 00008067
	.size memchr, .-memchr
