# musl 1.2.5 src/string/memmove.c (MIT, see examples/musl/COPYRIGHT), compiled by scripts/musl-trial/build.sh.
# Instructions as compiled, unchanged (scripts/musl-trial/verify.sh checks the bytes).
# Annotations are the lines that start with hash-colon (provisional syntax of docs/Tab 1.md; see docs/typed/musl-trial.md).
# Predicted (fixed before compiling): reject (v0 rules: xor alignment test)
# Expected now (after reading the compiled code): reject. (1) S2: the two copy directions share entry blocks 0x2c and 0x5c that are reached backwards from the word loops (0x110, 0x130, 0x168, 0x170) and the return 0x80 is reached backwards from 0xdc: intervals [0x2c,0x130]/[0x5c,0x170] and [0x80,0xdc]/[0xdc,0x100] are not nested. (2) As predicted, 's % 8 == d % 8' is xor + andi 7 (0x18-0x1c): the fact is lost and the sd at 0x11c / 0x15c fails 8 | a. The signature (one region, two offsets) and the tail call to memcpy with two disjoint sub-borrows are expressible; disjointness follows from the bgeu at 0x14 (u(-2n) >= u(s - d - n)) and d != s.
#! expect memmove: reject cfg
#: fn memcpy [d, s, n]
#:   in     a0: int(d), a1: int(s), a2: int(n)
#:   borrow d |-> bytes[n] rw
#:   borrow s |-> bytes[n] ro
#:   out    a0: int(d)
#:   stack  0
#: fn memmove [d, s, n, b, len]
#:   in     a0: int(d), a1: int(s), a2: int(n)
#:   borrow b |-> bytes[len] rw
#:   where  b <= d, d + n <= b + len, b <= s, s + n <= b + len
#:   out    a0: int(d)
#:   stack  0
	.text
	.globl memmove
	.p2align 2
	.type memmove,@function
memmove:
	beq	a0, a1, .Lmemmove_80    # 0: 08b50063
	add	a3, a0, a2              # 4: 00c506b3
	sub	a3, a1, a3              # 8: 40d586b3
	slli	a4, a2, 1               # c: 00161713
	sub	a4, zero, a4            # 10: 40e00733
	bgeu	a4, a3, .Lmemmove_50    # 14: 02d77e63
	xor	a3, a1, a0              # 18: 00a5c6b3
	andi	a3, a3, 7               # 1c: 0076f693
	bgeu	a0, a1, .Lmemmove_58    # 20: 02b57c63
	beq	a3, zero, .Lmemmove_84  # 24: 06068063
	addi	a3, a0, 0               # 28: 00050693
.Lmemmove_2c:
	#: inv [m] a1: int(s + n - m), a3: int(d + n - m), a2: int(m) where 0 <= m <= n
	# 0x2c, 0x5c, 0x80 are backward-edge targets only because of block layout (no decreases).
	beq	a2, zero, .Lmemmove_80  # 2c: 04060a63
.Lmemmove_30:
	#: inv [m] a1: int(s + n - m), a3: int(d + n - m), a2: int(m) where 1 <= m <= n decreases m
	lb	a4, 0(a1)               # 30: 00058703
	addi	a1, a1, 1               # 34: 00158593
	addi	a5, a3, 1               # 38: 00168793
	addi	a2, a2, -1              # 3c: fff60613
	sb	a4, 0(a3)               # 40: 00e68023
	addi	a3, a5, 0               # 44: 00078693
	bne	a2, zero, .Lmemmove_30  # 48: fe0614e3
	jal	zero, .Lmemmove_80      # 4c: 0340006f
.Lmemmove_50:
	tail	memcpy                  # 50: 00000317 00030067
.Lmemmove_58:
	beq	a3, zero, .Lmemmove_c8  # 58: 06068863
.Lmemmove_5c:
	#: inv [m] a1: int(s), a2: int(m) where 0 <= m <= n
	beq	a2, zero, .Lmemmove_80  # 5c: 02060263
	addi	a1, a1, -1              # 60: fff58593
.Lmemmove_64:
	#: inv [m] a1: int(s - 1), a2: int(m) where 1 <= m <= n decreases m
	add	a3, a1, a2              # 64: 00c586b3
	lb	a3, 0(a3)               # 68: 00068683
	addi	a4, a2, -1              # 6c: fff60713
	add	a2, a0, a2              # 70: 00c50633
	sb	a3, -1(a2)              # 74: fed60fa3
	addi	a2, a4, 0               # 78: 00070613
	bne	a4, zero, .Lmemmove_64  # 7c: fe0714e3
.Lmemmove_80:
	#: inv a0: int(d)
	jalr	zero, 0(ra)             # 80: 00008067
.Lmemmove_84:
	andi	a3, a0, 7               # 84: 00757693
	beq	a3, zero, .Lmemmove_108 # 88: 08068063
	addi	a4, zero, 0             # 8c: 00000713
	addi	a3, a0, 1               # 90: 00150693
.Lmemmove_94:
	#: inv [i] a4: int(i), a3: int(d + 1) where 0 <= i <= n decreases n - i
	beq	a2, a4, .Lmemmove_80    # 94: fee606e3
	add	a5, a1, a4              # 98: 00e587b3
	lb	a5, 0(a5)               # 9c: 00078783
	add	a6, a0, a4              # a0: 00e50833
	sb	a5, 0(a6)               # a4: 00f80023
	addw	a5, a3, a4              # a8: 00e687bb
	andi	a5, a5, 7               # ac: 0077f793
	addi	a4, a4, 1               # b0: 00170713
	bne	a5, zero, .Lmemmove_94  # b4: fe0790e3
	add	a1, a1, a4              # b8: 00e585b3
	add	a3, a0, a4              # bc: 00e506b3
	sub	a2, a2, a4              # c0: 40e60633
	jal	zero, .Lmemmove_10c     # c4: 0480006f
.Lmemmove_c8:
	addw	a3, a0, a2              # c8: 00c506bb
	andi	a3, a3, 7               # cc: 0076f693
	beq	a3, zero, .Lmemmove_134 # d0: 06068263
	addi	a4, a0, -1              # d4: fff50713
	addi	a5, a1, -1              # d8: fff58793
.Lmemmove_dc:
	#: inv [m] a2: int(m), a4: int(d - 1), a5: int(s - 1) where 0 <= m <= n decreases m
	beq	a2, zero, .Lmemmove_80  # dc: fa0602e3
	addi	a3, a2, -1              # e0: fff60693
	add	a6, a5, a2              # e4: 00c78833
	lb	a6, 0(a6)               # e8: 00080803
	add	a7, a4, a2              # ec: 00c708b3
	addw	a2, a4, a2              # f0: 00c7063b
	andi	t0, a2, 7               # f4: 00767293
	sb	a6, 0(a7)               # f8: 01088023
	addi	a2, a3, 0               # fc: 00068613
	bne	t0, zero, .Lmemmove_dc  # 100: fc029ee3
	jal	zero, .Lmemmove_138     # 104: 0340006f
.Lmemmove_108:
	addi	a3, a0, 0               # 108: 00050693
.Lmemmove_10c:
	addi	a4, zero, 8             # 10c: 00800713
	bltu	a2, a4, .Lmemmove_2c    # 110: f0e66ee3
	addi	a4, zero, 7             # 114: 00700713
.Lmemmove_118:
	#: inv [m] a1: int(s + n - m), a3: int(d + n - m), a2: int(m) where 8 <= m <= n, 8 | s + n - m, 8 | d + n - m decreases m
	ld	a5, 0(a1)               # 118: 0005b783
	sd	a5, 0(a3)               # 11c: 00f6b023
	addi	a2, a2, -8              # 120: ff860613
	addi	a3, a3, 8               # 124: 00868693
	addi	a1, a1, 8               # 128: 00858593
	bltu	a4, a2, .Lmemmove_118   # 12c: fec766e3
	jal	zero, .Lmemmove_2c      # 130: efdff06f
.Lmemmove_134:
	addi	a3, a2, 0               # 134: 00060693
.Lmemmove_138:
	addi	a2, zero, 8             # 138: 00800613
	bltu	a3, a2, .Lmemmove_16c   # 13c: 02c6e863
	addi	a4, a1, -8              # 140: ff858713
	addi	a5, a0, -8              # 144: ff850793
	addi	a6, zero, 7             # 148: 00700813
.Lmemmove_14c:
	#: inv [m] a3: int(m), a4: int(s - 8), a5: int(d - 8) where 8 <= m <= n, 8 | s + m, 8 | d + m decreases m
	add	a2, a4, a3              # 14c: 00d70633
	ld	a7, 0(a2)               # 150: 00063883
	addi	a2, a3, -8              # 154: ff868613
	add	a3, a5, a3              # 158: 00d786b3
	sd	a7, 0(a3)               # 15c: 0116b023
	addi	a3, a2, 0               # 160: 00060693
	bltu	a6, a2, .Lmemmove_14c   # 164: fec864e3
	jal	zero, .Lmemmove_5c      # 168: ef5ff06f
.Lmemmove_16c:
	addi	a2, a3, 0               # 16c: 00068613
	jal	zero, .Lmemmove_5c      # 170: eedff06f
	.size memmove, .-memmove
