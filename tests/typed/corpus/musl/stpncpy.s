# musl 1.2.5 src/string/stpncpy.c (MIT, see examples/musl/COPYRIGHT), compiled by scripts/musl-trial/build.sh.
# Instructions as compiled, unchanged (scripts/musl-trial/verify.sh checks the bytes).
# Annotations are the lines that start with hash-colon (provisional syntax of docs/Tab 1.md; see docs/typed/musl-trial.md).
# Predicted (batch 2, fixed before compiling): reject
# Expected now (after reading the compiled code): reject, as predicted, plus one unpredicted reason: it also uses a constant pool (static data, I14: parse error at 0x9c). Then (1) S2: 9 violations ([0x1c,0xe0]/[0x8c,0xe8], [0x20,0xc8]/[0xb8,0xdc]; the word loop exits into the byte loop 0xc8 -> 0x20); (2) xor alignment test (0x10-0x14), so the sd at 0xcc fails 8 | a; (3) branch-free && in the head loop (0x44-0x4c, 0x70-0x84). The tail call memset(d', 0, m) at 0xf8 itself is fine: d' = d + n - m.
#! expect __stpncpy: accept
#! expect-interval __stpncpy: reject cfg
#: fn memset [s, n]
#:   in     a0: int(s), a2: int(n)
#:   borrow s |-> bytes[n] rw
#:   out    a0: int(s)
#:   stack  0
#: fn __stpncpy [d, s, n]
#:   in     a0: int(d), a1: int(s), a2: int(n)
#:   borrow d |-> bytes[n] rw
#:   borrow s |-> bytes[n] ro
#:   out    a0: int
#:   stack  16
#:   frame  16 slots 0, 8
	.section .text.__stpncpy,"ax",@progbits
	.globl __stpncpy
	.p2align 2
	.type __stpncpy,@function
__stpncpy:
	addi	sp, sp, -16             # 0: ff010113
	sd	ra, 8(sp)               # 4: 00113423
	sd	s0, 0(sp)               # 8: 00813023
	addi	s0, a0, 0               # c: 00050413
	xor	a0, a1, a0              # 10: 00a5c533
	andi	a0, a0, 7               # 14: 00757513
	beq	a0, zero, .L__stpncpy_40# 18: 02050463
.L__stpncpy_1c:
	#: join [m] s0: int(d + n - m), a1: int(s + n - m), a2: int(m) where 0 <= m <= n
	# 0x1c and 0x8c are backward-edge targets only because of block layout: joins, not loops.
	beq	a2, zero, .L__stpncpy_f0# 1c: 0c060a63
.L__stpncpy_20:
	#: inv [m] s0: int(d + n - m), a1: int(s + n - m), a2: int(m) where 1 <= m <= n decreases m
	lbu	a0, 0(a1)               # 20: 0005c503
	sb	a0, 0(s0)               # 24: 00a40023
	beq	a0, zero, .L__stpncpy_f0# 28: 0c050463
	addi	a2, a2, -1              # 2c: fff60613
	addi	a1, a1, 1               # 30: 00158593
	addi	s0, s0, 1               # 34: 00140413
	bne	a2, zero, .L__stpncpy_20# 38: fe0614e3
	jal	zero, .L__stpncpy_f0    # 3c: 0b40006f
.L__stpncpy_40:
	andi	a0, a1, 7               # 40: 0075f513
	sltiu	a0, a0, 1               # 44: 00153513
	sltiu	a3, a2, 1               # 48: 00163693
	or	a0, a0, a3              # 4c: 00d56533
	bne	a0, zero, .L__stpncpy_e4# 50: 08051a63
	addi	a0, a1, 1               # 54: 00158513
.L__stpncpy_58:
	#: inv [m] s0: int(d + n - m), a1: int(s + n - m), a0: int(s + n - m + 1), a2: int(m) where 1 <= m <= n decreases m
	lbu	a3, 0(a1)               # 58: 0005c683
	sb	a3, 0(s0)               # 5c: 00d40023
	beq	a3, zero, .L__stpncpy_f0# 60: 08068863
	addi	a2, a2, -1              # 64: fff60613
	addi	a1, a1, 1               # 68: 00158593
	addi	s0, s0, 1               # 6c: 00140413
	andi	a3, a0, 7               # 70: 00757693
	sltu	a4, zero, a3            # 74: 00d03733
	sltu	a3, zero, a2            # 78: 00c036b3
	and	a4, a4, a3              # 7c: 00d77733
	addi	a0, a0, 1               # 80: 00150513
	bne	a4, zero, .L__stpncpy_58# 84: fc071ae3
	beq	a3, zero, .L__stpncpy_ec# 88: 06068263
.L__stpncpy_8c:
	#: join [m] s0: int(d + n - m), a1: int(s + n - m), a2: int(m) where 1 <= m <= n, 8 | s + n - m, 8 | d + n - m
	lbu	a0, 0(a1)               # 8c: 0005c503
	beq	a0, zero, .L__stpncpy_f0# 90: 06050063
	addi	a0, zero, 8             # 94: 00800513
	bltu	a2, a0, .L__stpncpy_1c  # 98: f8a662e3
.Lpcrel_9c:
	auipc	a0, %pcrel_hi(.LCPI0_0) # 9c: 00000517
	addi	a0, a0, %pcrel_lo(.Lpcrel_9c)# a0: 00050513
	ld	a0, 0(a0)               # a4: 00053503
.Lpcrel_a8:
	auipc	a3, %pcrel_hi(.LCPI0_1) # a8: 00000697
	addi	a3, a3, %pcrel_lo(.Lpcrel_a8)# ac: 00068693
	ld	a3, 0(a3)               # b0: 0006b683
	addi	a4, zero, 7             # b4: 00700713
.L__stpncpy_b8:
	#: inv [m] s0: int(d + n - m), a1: int(s + n - m), a2: int(m) where 8 <= m <= n, 8 | s + n - m, 8 | d + n - m decreases m
	ld	a5, 0(a1)               # b8: 0005b783
	add	a6, a5, a3              # bc: 00d78833
	andn	a7, a0, a5              # c0: 40f578b3
	and	a6, a7, a6              # c4: 0108f833
	bne	a6, zero, .L__stpncpy_20# c8: f4081ce3
	sd	a5, 0(s0)               # cc: 00f43023
	addi	a2, a2, -8              # d0: ff860613
	addi	a1, a1, 8               # d4: 00858593
	addi	s0, s0, 8               # d8: 00840413
	bltu	a4, a2, .L__stpncpy_b8  # dc: fcc76ee3
	jal	zero, .L__stpncpy_1c    # e0: f3dff06f
.L__stpncpy_e4:
	sltu	a3, zero, a2            # e4: 00c036b3
	bne	a3, zero, .L__stpncpy_8c# e8: fa0692e3
.L__stpncpy_ec:
	#: join [p] s0: int(p) where d <= p <= d + n
	addi	a2, zero, 0             # ec: 00000613
.L__stpncpy_f0:
	#: join [p, m] s0: int(p), a2: int(m) where d <= p, 0 <= m, p + m <= d + n
	addi	a0, s0, 0               # f0: 00040513
	addi	a1, zero, 0             # f4: 00000593
	call	memset                  # f8: 00000097 000080e7
	addi	a0, s0, 0               # 100: 00040513
	ld	ra, 8(sp)               # 104: 00813083
	ld	s0, 0(sp)               # 108: 00013403
	addi	sp, sp, 16              # 10c: 01010113
	jalr	zero, 0(ra)             # 110: 00008067
	.size __stpncpy, .-__stpncpy

	.section .rodata.cst8,"aM",@progbits,8
	.p2align 3
.LCPI0_0:
	.quad	0x8080808080808080
.LCPI0_1:
	.quad	0xfefefefefefefeff
