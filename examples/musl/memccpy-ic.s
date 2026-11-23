# musl 1.2.5 src/string/memccpy.c (MIT, see examples/musl/COPYRIGHT), compiled by scripts/musl-trial/build.sh
# with -mllvm -riscv-disable-using-constant-pool-for-large-ints (constants inline, no static data).
# Instructions as compiled, unchanged (scripts/musl-trial/verify.sh checks the bytes).
# Annotations are the lines that start with hash-colon (provisional syntax of docs/Tab 1.md; see docs/typed/musl-trial.md).
# Predicted (fixed before compiling this variant): reject (as memccpy without static data)
# Expected now (after reading the compiled code): reject. (1) S2: 7 backward-edge targets (0x10, 0x14, 0x18, 0x34, 0x58, 0x9c, 0xf8); only 0x18, 0x58, 0xf8 are loops; the word loop exits back into the byte loop (0x10c -> 0x14) and return blocks are reached backwards, giving 5 non-nested pairs. (2) As predicted: '(s & 7) == (d & 7)' became xor a4, a1, a0; andi a4, a4, 7 (0x0-0x4); xor is not in the table, so s = d (mod 8) is lost and the aligned sd at 0x110 fails 8 | a. (3) The alignment-loop test is branch-free (sltu/xor/and, 0x6c-0x80).
#! expect memccpy: reject cfg
#: fn memccpy [d, s, n]
#:   in     a0: int(d), a1: int(s), a3: int(n)
#:   borrow d |-> bytes[n] rw
#:   borrow s |-> bytes[n] ro
#:   out    a0: int
#:   stack  0
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
	# 0x10, 0x14, 0x34, 0x9c are targets of backward edges only because of block layout; they are
	# not loops, so no decreases clause is given.
	beq	a3, zero, .Lmemccpy_34  # 10: 02068263
.Lmemccpy_14:
	#: inv [m] a0: int(d + n - m), a1: int(s + n - m), a3: int(m) where 1 <= m <= n
	addi	a0, a0, 1               # 14: 00150513
.Lmemccpy_18:
	#: inv [m] a0: int(d + n - m + 1), a1: int(s + n - m), a3: int(m) where 1 <= m <= n decreases m
	lbu	a4, 0(a1)               # 18: 0005c703
	sb	a4, -1(a0)              # 1c: fee50fa3
	beq	a4, a2, .Lmemccpy_138   # 20: 10c70c63
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
	bne	a5, zero, .Lmemccpy_128 # 4c: 0c079e63
	addi	a6, a1, 1               # 50: 00158813
	addi	a7, a3, -1              # 54: fff68893
.Lmemccpy_58:
	#: inv [i] a5: int(i), a6: int(s + 1), a7: int(n - 1) where 0 <= i <= n - 1 decreases n - i
	add	a4, a1, a5              # 58: 00f58733
	lbu	t0, 0(a4)               # 5c: 00074283
	add	a4, a0, a5              # 60: 00f50733
	sb	t0, 0(a4)               # 64: 00570023
	beq	t0, a2, .Lmemccpy_13c   # 68: 0cc28a63
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
	bne	a4, zero, .Lmemccpy_130 # 98: 08071c63
.Lmemccpy_9c:
	#: inv [m] a0: int(d + n - m), a1: int(s + n - m), a3: int(m) where 0 <= m <= n, 8 | s + n - m, 8 | d + n - m
	addi	a4, zero, 8             # 9c: 00800713
	bltu	a3, a4, .Lmemccpy_10    # a0: f6e6e8e3
	lui	a4, 4112                # a4: 01010737
	addiw	a4, a4, 257             # a8: 1017071b
	slli	a4, a4, 16              # ac: 01071713
	addi	a4, a4, 257             # b0: 10170713
	slli	a4, a4, 16              # b4: 01071713
	addi	a4, a4, 257             # b8: 10170713
	mul	a4, a2, a4              # bc: 02e60733
	lui	a5, 983297              # c0: f01017b7
	slli	a5, a5, 4               # c4: 00479793
	addi	a5, a5, 257             # c8: 10178793
	slli	a5, a5, 16              # cc: 01079793
	addi	a5, a5, 257             # d0: 10178793
	slli	a5, a5, 15              # d4: 00f79793
	addi	a5, a5, 128             # d8: 08078793
	lui	a6, 1044464             # dc: feff0837
	addiw	a6, a6, -257            # e0: eff8081b
	slli	a6, a6, 16              # e4: 01081813
	addi	a6, a6, -257            # e8: eff80813
	slli	a6, a6, 16              # ec: 01081813
	addi	a6, a6, -257            # f0: eff80813
	addi	a7, zero, 7             # f4: 00700893
.Lmemccpy_f8:
	#: inv [m] a0: int(d + n - m), a1: int(s + n - m), a3: int(m) where 8 <= m <= n, 8 | s + n - m, 8 | d + n - m decreases m
	ld	t0, 0(a1)               # f8: 0005b283
	xor	t1, t0, a4              # fc: 00e2c333
	add	t2, t1, a6              # 100: 010303b3
	andn	t1, a5, t1              # 104: 4067f333
	and	t1, t1, t2              # 108: 00737333
	bne	t1, zero, .Lmemccpy_14  # 10c: f00314e3
	sd	t0, 0(a0)               # 110: 00553023
	addi	a3, a3, -8              # 114: ff868693
	addi	a1, a1, 8               # 118: 00858593
	addi	a0, a0, 8               # 11c: 00850513
	bltu	a7, a3, .Lmemccpy_f8    # 120: fcd8ece3
	jal	zero, .Lmemccpy_10      # 124: eedff06f
.Lmemccpy_128:
	sltu	a4, zero, a4            # 128: 00e03733
	beq	a4, zero, .Lmemccpy_9c  # 12c: f60708e3
.Lmemccpy_130:
	beq	a3, zero, .Lmemccpy_34  # 130: f00682e3
	addi	a0, a0, 1               # 134: 00150513
.Lmemccpy_138:
	jalr	zero, 0(ra)             # 138: 00008067
.Lmemccpy_13c:
	addi	a0, a4, 1               # 13c: 00170513
	jalr	zero, 0(ra)             # 140: 00008067
	.size memccpy, .-memccpy
