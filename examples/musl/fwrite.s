# musl 1.2.5 src/stdio/fwrite.c (MIT, see examples/musl/COPYRIGHT), compiled by scripts/musl-trial/build.sh.
# Instructions as compiled, unchanged (scripts/musl-trial/verify.sh checks the bytes).
# Annotations are the lines that start with hash-colon (provisional syntax of docs/Tab 1.md; see docs/typed/musl-trial.md).
# Predicted (fixed before compiling): unsafe contract (function pointer)
# Expected now (after reading the compiled code): reject. Prediction was wrong about the reason: in this build fwrite is only a wrapper (the f->write call is in __fwritex, a separate unsafe contract), but (1) the buffer length is size*nmemb, not a linear index expression, so the signature cannot say how much of b is borrowed, and the call to __fwritex at 0x60/0xb8 cannot match borrow b |-> bytes[l] with l = a1 = mul s2 (a product of two variables: int); (2) S2: the return block 0x84 and the divu block 0x80 are placed before the second __fwritex call and reached by backward branches (0xc4, 0xc8): non-nested intervals, no real loop. divu is not in the table (int) - harmless.
#! expect fwrite: reject call-cap
#! expect-interval fwrite: reject cfg
#: unsafe fn __lockfile [f]
#:   in     a0: int(f)
#:   borrow f |-> bytes[232] rw
#:   borrow Stdio
#:   where  8 | f
#:   out    a0: int
#: unsafe fn __unlockfile [f]
#:   in     a0: int(f)
#:   borrow f |-> bytes[232] rw
#:   borrow Stdio
#:   where  8 | f
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
#: fn fwrite [b, size, nmemb, f, len]
#:   in     a0: int(b), a1: int(size), a2: int(nmemb), a3: int(f)
#:   borrow b |-> bytes[len] ro
#:   borrow f |-> bytes[232] rw
#:   borrow Stdio
#:   where  8 | f
#:   out    a0: int
#:   stack  128
#:   frame  64 slots 8, 16, 24, 32, 40, 48, 56
# len should be size*nmemb; v0 index expressions are linear, so len is left unrelated.
	.section .text.fwrite,"ax",@progbits
	.globl fwrite
	.p2align 2
	.type fwrite,@function
fwrite:
	addi	sp, sp, -64             # 0: fc010113
	sd	ra, 56(sp)              # 4: 02113c23
	sd	s0, 48(sp)              # 8: 02813823
	sd	s1, 40(sp)              # c: 02913423
	sd	s2, 32(sp)              # 10: 03213023
	sd	s3, 24(sp)              # 14: 01313c23
	sd	s4, 16(sp)              # 18: 01413823
	sd	s5, 8(sp)               # 1c: 01513423
	addi	s3, a3, 0               # 20: 00068993
	addi	s0, a1, 0               # 24: 00058413
	addi	s4, a0, 0               # 28: 00050a13
	addi	s1, zero, 0             # 2c: 00000493
	beq	a1, zero, .Lfwrite_38   # 30: 00058463
	addi	s1, a2, 0               # 34: 00060493
.Lfwrite_38:
	lw	a0, 140(s3)             # 38: 08c9a503
	mul	s2, a2, s0              # 3c: 02860933
	blt	a0, zero, .Lfwrite_ac   # 40: 06054663
	addi	a0, s3, 0               # 44: 00098513
	call	__lockfile              # 48: 00000097 000080e7
	addi	s5, a0, 0               # 50: 00050a93
	addi	a0, s4, 0               # 54: 000a0513
	addi	a1, s2, 0               # 58: 00090593
	addi	a2, s3, 0               # 5c: 00098613
	call	__fwritex               # 60: 00000097 000080e7
	addi	s4, a0, 0               # 68: 00050a13
	beq	s5, zero, .Lfwrite_7c   # 6c: 000a8863
	addi	a0, s3, 0               # 70: 00098513
	call	__unlockfile            # 74: 00000097 000080e7
.Lfwrite_7c:
	beq	s4, s2, .Lfwrite_84     # 7c: 012a0463
.Lfwrite_80:
	divu	s1, s4, s0              # 80: 028a54b3
.Lfwrite_84:
	addi	a0, s1, 0               # 84: 00048513
	ld	ra, 56(sp)              # 88: 03813083
	ld	s0, 48(sp)              # 8c: 03013403
	ld	s1, 40(sp)              # 90: 02813483
	ld	s2, 32(sp)              # 94: 02013903
	ld	s3, 24(sp)              # 98: 01813983
	ld	s4, 16(sp)              # 9c: 01013a03
	ld	s5, 8(sp)               # a0: 00813a83
	addi	sp, sp, 64              # a4: 04010113
	jalr	zero, 0(ra)             # a8: 00008067
.Lfwrite_ac:
	addi	a0, s4, 0               # ac: 000a0513
	addi	a1, s2, 0               # b0: 00090593
	addi	a2, s3, 0               # b4: 00098613
	call	__fwritex               # b8: 00000097 000080e7
	addi	s4, a0, 0               # c0: 00050a13
	bne	s4, s2, .Lfwrite_80     # c4: fb2a1ee3
	jal	zero, .Lfwrite_84       # c8: fbdff06f
	.size fwrite, .-fwrite
