# musl 1.2.5 src/stdlib/bsearch.c (MIT, see examples/musl/COPYRIGHT), compiled by scripts/musl-trial/build.sh.
# Instructions as compiled, unchanged (scripts/musl-trial/verify.sh checks the bytes).
# Annotations are the lines that start with hash-colon (docs/typed/syntax.md).
# Predicted (batch 3, fixed before compiling): reject profile
# Expected now (after reading the compiled code): reject: cmp is called through a register (jalr ra, 0(s0) at 0x68), outside S1. The signature is also only approximate: the array is nel*width bytes, not a linear length.
#! expect bsearch: reject profile
#: fn bsearch [k, b, n, w, len]
#:   in     a0: int(k), a1: int(b), a2: int(n), a3: int(w)
#:   borrow b |-> bytes[len] ro
#:   out    a0: int
#:   stack  64
#:   frame  64 slots 0, 8, 16, 24, 32, 40, 48, 56
	.section .text.bsearch,"ax",@progbits
	.globl bsearch
	.p2align 2
	.type bsearch,@function
bsearch:
	addi	sp, sp, -64             # 0: fc010113
	sd	ra, 56(sp)              # 4: 02113c23
	sd	s0, 48(sp)              # 8: 02813823
	sd	s1, 40(sp)              # c: 02913423
	sd	s2, 32(sp)              # 10: 03213023
	sd	s3, 24(sp)              # 14: 01313c23
	sd	s4, 16(sp)              # 18: 01413823
	sd	s5, 8(sp)               # 1c: 01513423
	sd	s6, 0(sp)               # 20: 01613023
	beq	a2, zero, .Lbsearch_78  # 24: 04060a63
	addi	s0, a4, 0               # 28: 00070413
	addi	s1, a3, 0               # 2c: 00068493
	addi	s4, a2, 0               # 30: 00060a13
	addi	s3, a1, 0               # 34: 00058993
	addi	s2, a0, 0               # 38: 00050913
	jal	zero, .Lbsearch_54      # 3c: 0180006f
.Lbsearch_40:
	add	s3, s5, s1              # 40: 009a89b3
	xori	a0, s6, -1              # 44: fffb4513
	add	s6, s4, a0              # 48: 00aa0b33
.Lbsearch_4c:
	addi	s4, s6, 0               # 4c: 000b0a13
	beq	s6, zero, .Lbsearch_78  # 50: 020b0463
.Lbsearch_54:
	srli	s6, s4, 1               # 54: 001a5b13
	mul	a0, s6, s1              # 58: 029b0533
	add	s5, s3, a0              # 5c: 00a98ab3
	addi	a0, s2, 0               # 60: 00090513
	addi	a1, s5, 0               # 64: 000a8593
	jalr	ra, 0(s0)               # 68: 000400e7
	blt	a0, zero, .Lbsearch_4c  # 6c: fe0540e3
	bne	a0, zero, .Lbsearch_40  # 70: fc0518e3
	jal	zero, .Lbsearch_7c      # 74: 0080006f
.Lbsearch_78:
	addi	s5, zero, 0             # 78: 00000a93
.Lbsearch_7c:
	addi	a0, s5, 0               # 7c: 000a8513
	ld	ra, 56(sp)              # 80: 03813083
	ld	s0, 48(sp)              # 84: 03013403
	ld	s1, 40(sp)              # 88: 02813483
	ld	s2, 32(sp)              # 8c: 02013903
	ld	s3, 24(sp)              # 90: 01813983
	ld	s4, 16(sp)              # 94: 01013a03
	ld	s5, 8(sp)               # 98: 00813a83
	ld	s6, 0(sp)               # 9c: 00013b03
	addi	sp, sp, 64              # a0: 04010113
	jalr	zero, 0(ra)             # a4: 00008067
	.size bsearch, .-bsearch
