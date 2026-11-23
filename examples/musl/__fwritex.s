# musl 1.2.5 src/stdio/fwrite.c (MIT, see examples/musl/COPYRIGHT), compiled by scripts/musl-trial/build.sh.
# Instructions as compiled, unchanged (scripts/musl-trial/verify.sh checks the bytes).
# Annotations are the lines that start with hash-colon (docs/typed/syntax.md).
# Predicted (batch 3, fixed before compiling): reject profile
# Expected now (after reading the compiled code): reject: f->write is called through a register twice (tail call jalr zero, 0(t1) at 0x70; jalr ra, 0(a3) at 0xb8), outside S1. The memcpy into f->wpos would also fail: that buffer's pointer is read from memory and no capability for it is held.
#! expect __fwritex: reject profile
#: fn __towrite [f]
#:   in     a0: int(f)
#:   borrow f |-> bytes[232] rw
#:   where  8 | f
#:   out    a0: int
#:   stack  0
#: fn __fwritex [b, l, f]
#:   in     a0: int(b), a1: int(l), a2: int(f)
#:   borrow b |-> bytes[l] ro
#:   borrow f |-> bytes[232] rw
#:   borrow Stdio
#:   where  8 | f
#:   out    a0: int(r)
#:   where  0 <= r <= l
#:   stack  64
#:   frame  64 slots 8, 16, 24, 32, 40, 48, 56
	.section .text.__fwritex,"ax",@progbits
	.globl __fwritex
	.p2align 2
	.type __fwritex,@function
__fwritex:
	addi	sp, sp, -64             # 0: fc010113
	sd	ra, 56(sp)              # 4: 02113c23
	sd	s0, 48(sp)              # 8: 02813823
	sd	s1, 40(sp)              # c: 02913423
	sd	s2, 32(sp)              # 10: 03213023
	sd	s3, 24(sp)              # 14: 01313c23
	sd	s4, 16(sp)              # 18: 01413823
	sd	s5, 8(sp)               # 1c: 01513423
	addi	s0, a2, 0               # 20: 00060413
	ld	a2, 32(a2)              # 24: 02063603
	addi	s1, a1, 0               # 28: 00058493
	addi	s2, a0, 0               # 2c: 00050913
	beq	a2, zero, .L__fwritex_d4# 30: 0a060263
.L__fwritex_34:
	ld	a0, 40(s0)              # 34: 02843503
	sub	a1, a2, a0              # 38: 40a605b3
	bgeu	a1, s1, .L__fwritex_74  # 3c: 0295fc63
	ld	t1, 72(s0)              # 40: 04843303
	addi	a0, s0, 0               # 44: 00040513
	addi	a1, s2, 0               # 48: 00090593
	addi	a2, s1, 0               # 4c: 00048613
	ld	ra, 56(sp)              # 50: 03813083
	ld	s0, 48(sp)              # 54: 03013403
	ld	s1, 40(sp)              # 58: 02813483
	ld	s2, 32(sp)              # 5c: 02013903
	ld	s3, 24(sp)              # 60: 01813983
	ld	s4, 16(sp)              # 64: 01013a03
	ld	s5, 8(sp)               # 68: 00813a83
	addi	sp, sp, 64              # 6c: 04010113
	jalr	zero, 0(t1)             # 70: 00030067
.L__fwritex_74:
	lw	a1, 144(s0)             # 74: 09042583
	blt	a1, zero, .L__fwritex_f4# 78: 0605ce63
	addi	s4, zero, 0             # 7c: 00000a13
	addi	a1, zero, 10            # 80: 00a00593
	addi	s5, s2, 0               # 84: 00090a93
.L__fwritex_88:
	beq	s1, s4, .L__fwritex_f4  # 88: 07448663
	add	a2, s5, s1              # 8c: 009a8633
	lbu	a2, -1(a2)              # 90: fff64603
	addi	s4, s4, 1               # 94: 001a0a13
	addi	s5, s5, -1              # 98: fffa8a93
	bne	a2, a1, .L__fwritex_88  # 9c: feb616e3
	ld	a3, 72(s0)              # a0: 04843683
	sub	a0, s1, s4              # a4: 41448533
	addi	s3, a0, 1               # a8: 00150993
	addi	a0, s0, 0               # ac: 00040513
	addi	a1, s2, 0               # b0: 00090593
	addi	a2, s3, 0               # b4: 00098613
	jalr	ra, 0(a3)               # b8: 000680e7
	bltu	a0, s3, .L__fwritex_118 # bc: 05356e63
	ld	a0, 40(s0)              # c0: 02843503
	add	a1, s5, s1              # c4: 009a85b3
	addi	s1, s4, -1              # c8: fffa0493
	addi	s2, a1, 1               # cc: 00158913
	jal	zero, .L__fwritex_f8    # d0: 0280006f
.L__fwritex_d4:
	addi	a0, s0, 0               # d4: 00040513
	call	__towrite               # d8: 00000097 000080e7
	addi	a1, a0, 0               # e0: 00050593
	addi	a0, zero, 0             # e4: 00000513
	bne	a1, zero, .L__fwritex_118# e8: 02059863
	ld	a2, 32(s0)              # ec: 02043603
	jal	zero, .L__fwritex_34    # f0: f45ff06f
.L__fwritex_f4:
	addi	s3, zero, 0             # f4: 00000993
.L__fwritex_f8:
	addi	a1, s2, 0               # f8: 00090593
	addi	a2, s1, 0               # fc: 00048613
	call	memcpy                  # 100: 00000097 000080e7
	ld	a0, 40(s0)              # 108: 02843503
	add	a0, a0, s1              # 10c: 00950533
	sd	a0, 40(s0)              # 110: 02a43423
	add	a0, s3, s1              # 114: 00998533
.L__fwritex_118:
	ld	ra, 56(sp)              # 118: 03813083
	ld	s0, 48(sp)              # 11c: 03013403
	ld	s1, 40(sp)              # 120: 02813483
	ld	s2, 32(sp)              # 124: 02013903
	ld	s3, 24(sp)              # 128: 01813983
	ld	s4, 16(sp)              # 12c: 01013a03
	ld	s5, 8(sp)               # 130: 00813a83
	addi	sp, sp, 64              # 134: 04010113
	jalr	zero, 0(ra)             # 138: 00008067
	.size __fwritex, .-__fwritex
