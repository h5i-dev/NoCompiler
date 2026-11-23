# musl 1.2.5 src/string/stpncpy.c (MIT, see examples/musl/COPYRIGHT), compiled by scripts/musl-trial/build.sh
# with -mllvm -riscv-disable-using-constant-pool-for-large-ints -mllvm -jump-is-expensive=false
# (constants inline; && kept as branches). Instructions as compiled, unchanged (verify.sh).
# Annotations are the lines that start with hash-colon (docs/typed/syntax.md).
# Predicted (fixed before building this variant): reject
# Expected now (after reading the compiled code): reject: S2 5 violations (4 non-loop backward edges); xor alignment test, so the sd at 0xec fails 8 | a. Annotated: signature and the three natural loops 0x24, 0x5c, 0xd8. Not annotated: the non-loop backward targets and joins.
#! expect __stpncpy: reject cfg
#: fn memset [s, n]
#:   in     a0: int(s), a2: int(n)
#:   borrow s |-> bytes[n] rw
#:   out    a0: int(s)
#:   stack  0
#: fn __stpncpy [d, s, n]
#:   in     a0: int(d), a1: int(s), a2: u64(n)
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
	beq	a0, zero, .L__stpncpy_44# 18: 02050663
.L__stpncpy_1c:
	#: join [m] s0: int(d + n - m), a1: int(s + n - m), a2: int(m) where 0 <= m <= n
	beq	a2, zero, .L__stpncpy_104# 1c: 0e060463
.L__stpncpy_20:
	#: join [m] s0: int(d + n - m), a1: int(s + n - m), a2: int(m) where 1 <= m <= n
	addi	a3, a2, 0               # 20: 00060693
.L__stpncpy_24:
	#: inv [m] s0: int(d + n - m), a1: int(s + n - m), a3: int(m) where 1 <= m <= n decreases m
	lbu	a0, 0(a1)               # 24: 0005c503
	sb	a0, 0(s0)               # 28: 00a40023
	beq	a0, zero, .L__stpncpy_108# 2c: 0c050e63
	addi	a3, a3, -1              # 30: fff68693
	addi	a1, a1, 1               # 34: 00158593
	addi	s0, s0, 1               # 38: 00140413
	bne	a3, zero, .L__stpncpy_24# 3c: fe0694e3
	jal	zero, .L__stpncpy_108   # 40: 0c80006f
.L__stpncpy_44:
	andi	a3, a1, 7               # 44: 0075f693
	sltu	a0, zero, a2            # 48: 00c03533
	beq	a3, zero, .L__stpncpy_8c# 4c: 04068063
	beq	a2, zero, .L__stpncpy_8c# 50: 02060e63
	addi	a4, a1, 1               # 54: 00158713
	addi	a5, zero, 1             # 58: 00100793
.L__stpncpy_5c:
	#: inv [m] s0: int(d + n - m), a1: int(s + n - m), a2: int(m), a4: int(s + n - m + 1) where 1 <= m <= n decreases m
	lbu	a0, 0(a1)               # 5c: 0005c503
	addi	a3, a2, 0               # 60: 00060693
	sb	a0, 0(s0)               # 64: 00a40023
	beq	a0, zero, .L__stpncpy_108# 68: 0a050063
	addi	a2, a3, -1              # 6c: fff68613
	addi	a1, a1, 1               # 70: 00158593
	addi	s0, s0, 1               # 74: 00140413
	andi	a6, a4, 7               # 78: 00777813
	sltu	a0, zero, a2            # 7c: 00c03533
	beq	a6, zero, .L__stpncpy_8c# 80: 00080663
	addi	a4, a4, 1               # 84: 00170713
	bne	a3, a5, .L__stpncpy_5c  # 88: fcf69ae3
.L__stpncpy_8c:
	#: join [m, b] s0: int(d + n - m), a1: int(s + n - m), a2: int(m), a0: int(b) where 0 <= m <= n, ((b = 0 && m = 0) || (b = 1 && 1 <= m && 8 | s + n - m && 8 | d + n - m))
	beq	a0, zero, .L__stpncpy_104# 8c: 06050c63
	lbu	a0, 0(a1)               # 90: 0005c503
	beq	a0, zero, .L__stpncpy_130# 94: 08050e63
	addi	a0, zero, 8             # 98: 00800513
	bltu	a2, a0, .L__stpncpy_1c  # 9c: f8a660e3
	lui	a0, 983297              # a0: f0101537
	slli	a0, a0, 4               # a4: 00451513
	addi	a0, a0, 257             # a8: 10150513
	slli	a0, a0, 16              # ac: 01051513
	addi	a0, a0, 257             # b0: 10150513
	slli	a0, a0, 15              # b4: 00f51513
	addi	a0, a0, 128             # b8: 08050513
	lui	a3, 1044464             # bc: feff06b7
	addiw	a3, a3, -257            # c0: eff6869b
	slli	a3, a3, 16              # c4: 01069693
	addi	a3, a3, -257            # c8: eff68693
	slli	a3, a3, 16              # cc: 01069693
	addi	a3, a3, -257            # d0: eff68693
	addi	a4, zero, 7             # d4: 00700713
.L__stpncpy_d8:
	#: inv [m] s0: int(d + n - m), a1: int(s + n - m), a2: int(m) where 8 <= m <= n, 8 | s + n - m, 8 | d + n - m decreases m
	ld	a5, 0(a1)               # d8: 0005b783
	add	a6, a5, a3              # dc: 00d78833
	andn	a7, a0, a5              # e0: 40f578b3
	and	a6, a7, a6              # e4: 0108f833
	bne	a6, zero, .L__stpncpy_20# e8: f2081ce3
	sd	a5, 0(s0)               # ec: 00f43023
	addi	a2, a2, -8              # f0: ff860613
	addi	a1, a1, 8               # f4: 00858593
	addi	s0, s0, 8               # f8: 00840413
	bltu	a4, a2, .L__stpncpy_d8  # fc: fcc76ee3
	jal	zero, .L__stpncpy_1c    # 100: f1dff06f
.L__stpncpy_104:
	#: join [p] s0: int(p) where d <= p <= d + n
	addi	a3, zero, 0             # 104: 00000693
.L__stpncpy_108:
	#: join [p, m] s0: int(p), a3: int(m) where d <= p, 0 <= m, p + m <= d + n
	addi	a0, s0, 0               # 108: 00040513
	addi	a1, zero, 0             # 10c: 00000593
	addi	a2, a3, 0               # 110: 00068613
	call	memset                  # 114: 00000097 000080e7
	addi	a0, s0, 0               # 11c: 00040513
	ld	ra, 8(sp)               # 120: 00813083
	ld	s0, 0(sp)               # 124: 00013403
	addi	sp, sp, 16              # 128: 01010113
	jalr	zero, 0(ra)             # 12c: 00008067
.L__stpncpy_130:
	addi	a3, a2, 0               # 130: 00060693
	jal	zero, .L__stpncpy_108   # 134: fd5ff06f
	.size __stpncpy, .-__stpncpy
