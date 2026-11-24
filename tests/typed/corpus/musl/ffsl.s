# musl 1.2.5 src/misc/ffsl.c (MIT, see examples/musl/COPYRIGHT), compiled by scripts/musl-trial/build.sh.
# Instructions as compiled, unchanged (scripts/musl-trial/verify.sh checks the bytes).
# Annotations are the lines that start with hash-colon (docs/typed/syntax.md).
# Predicted (batch 3, fixed before compiling): accept
# Expected now (after reading the compiled code): accept, with a twist: musl's a_ctz_64 is a De Bruijn multiply and a lookup in a 64-byte read-only table (I30), not Zbb ctz. The index comes from srli 58, so it is in [0, 64) without a comparison: the note's 'no extra check' case.
#! expect ffsl: accept
#: fn ffsl [x]
#:   in     a0: int(x)
#:   out    a0: int
#:   stack  0
	.section .text.ffsl,"ax",@progbits
	.globl ffsl
	.p2align 2
	.type ffsl,@function
ffsl:
	beq	a0, zero, .Lffsl_34     # 0: 02050a63
.Lpcrel_4:
	auipc	a1, %pcrel_hi(.LCPI0_0) # 4: 00000597
	addi	a1, a1, %pcrel_lo(.Lpcrel_4)# 8: 00058593
	ld	a1, 0(a1)               # c: 0005b583
	sub	a2, zero, a0            # 10: 40a00633
	and	a0, a2, a0              # 14: 00a67533
	mul	a0, a0, a1              # 18: 02b50533
	srli	a0, a0, 58              # 1c: 03a55513
.Lpcrel_20:
	auipc	a1, %pcrel_hi(a_ctz_64.debruijn64)# 20: 00000597
	addi	a1, a1, %pcrel_lo(.Lpcrel_20)# 24: 00058593
	add	a0, a1, a0              # 28: 00a58533
	lbu	a0, 0(a0)               # 2c: 00054503
	addi	a0, a0, 1               # 30: 00150513
.Lffsl_34:
	jalr	zero, 0(ra)             # 34: 00008067
	.size ffsl, .-ffsl

	.section .rodata.cst8,"aM",@progbits,8
	.p2align 3
.LCPI0_0:
	.quad	0x022fdd63cc95386d

	.section .rodata.a_ctz_64.debruijn64,"a",@progbits
	.p2align 3
a_ctz_64.debruijn64:
	.quad	0x1b36070335020100
	.quad	0x1c30372208292604
	.quad	0x09162a2c2e27053e
	.quad	0x0b1d1231383b2318
	.quad	0x2f2128251a06343f
	.quad	0x0a113a17152b2d3d
	.quad	0x1039143c20241933
	.quad	0x0c0d0e1e0f131f32
