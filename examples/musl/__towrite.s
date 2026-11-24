# musl 1.2.5 src/stdio/__towrite.c (MIT, see examples/musl/COPYRIGHT), compiled by scripts/musl-trial/build.sh.
# Instructions as compiled, unchanged (scripts/musl-trial/verify.sh checks the bytes).
# Annotations are the lines that start with hash-colon (docs/typed/syntax.md).
# Predicted (batch 3, fixed before compiling): accept
# Expected now (after reading the compiled code): accept: fixed-offset 4- and 8-byte accesses inside the FILE capability (offsets 0, 8, 16, 32, 40, 56, 88, 96, 136).
#! expect __towrite: accept
#: fn __towrite [f]
#:   in     a0: int(f)
#:   borrow f |-> bytes[232] rw
#:   where  8 | f
#:   out    a0: int
#:   stack  0
	.section .text.__towrite,"ax",@progbits
	.globl __towrite
	.p2align 2
	.type __towrite,@function
__towrite:
	lw	a2, 136(a0)             # 0: 08852603
	lwu	a1, 0(a0)               # 4: 00056583
	addi	a3, a2, -1              # 8: fff60693
	or	a2, a3, a2              # c: 00c6e633
	andi	a3, a1, 8               # 10: 0085f693
	sw	a2, 136(a0)             # 14: 08c52423
	bne	a3, zero, .L__towrite_44# 18: 02069663
	ld	a2, 88(a0)              # 1c: 05853603
	ld	a3, 96(a0)              # 20: 06053683
	sd	a2, 56(a0)              # 24: 02c53c23
	sd	a2, 40(a0)              # 28: 02c53423
	add	a2, a2, a3              # 2c: 00d60633
	sd	zero, 16(a0)            # 30: 00053823
	sd	zero, 8(a0)             # 34: 00053423
	sd	a2, 32(a0)              # 38: 02c53023
	addi	a0, zero, 0             # 3c: 00000513
	jalr	zero, 0(ra)             # 40: 00008067
.L__towrite_44:
	ori	a1, a1, 32              # 44: 0205e593
	sw	a1, 0(a0)               # 48: 00b52023
	addi	a0, zero, -1            # 4c: fff00513
	jalr	zero, 0(ra)             # 50: 00008067
	.size __towrite, .-__towrite
