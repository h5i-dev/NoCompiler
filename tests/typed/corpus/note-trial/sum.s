# examples/typed/src/sum.c (bcb19fed), compiled by scripts/typed-trial/build.sh, unchanged;
# annotations are the '#:' lines (docs/typed/note-trial.md).
#! expect sum: accept
#! expect sum2: accept
#! expect _start: accept
#: fn sum [ρ, n]
#:   in     a0: int(ρ), a1: int(n)
#:   borrow ρ ↦ bytes[8n] ro
#:   where  8 ∣ ρ
#:   out    a0: int
#:   stack  0
#: fn sum2 [a, n, b, m]
#:   in     a0: int(a), a1: int(n), a2: int(b), a3: int(m)
#:   borrow a ↦ bytes[8n] ro, b ↦ bytes[8m] ro
#:   where  8 ∣ a, 8 ∣ b
#:   out    a0: int
#:   frame  32 slots 0, 8, 16, 24
#:   stack  32
#: fn _start [] borrow @data ↦ bytes[40] rw frame 32 slots 8, 16, 24 stack 32
	.text
	.attribute	4, 16
	.attribute	5, "rv64i2p0_m2p0_zba1p0_zbb1p0"
	.file	"sum.c"
	.section	.text.sum,"ax",@progbits
	.globl	sum                             # -- Begin function sum
	.p2align	2
	.type	sum,@function
sum:
# %bb.0:
	li	a2, 0
	beqz	a1, .LBB0_2
.LBB0_1:
	#: inv [k] a0: int(ρ + 8n − 8k), a1: int(k), a2: int where 1 ≤ k ≤ n decreases k
	ld	a3, 0(a0)
	add	a2, a3, a2
	addi	a1, a1, -1
	addi	a0, a0, 8
	bnez	a1, .LBB0_1
.LBB0_2:
	mv	a0, a2
	ret
.Lfunc_end0:
	.size	sum, .Lfunc_end0-sum
                                        # -- End function
	.section	.text.sum2,"ax",@progbits
	.globl	sum2                            # -- Begin function sum2
	.p2align	2
	.type	sum2,@function
sum2:
# %bb.0:
	addi	sp, sp, -32
	sd	ra, 24(sp)                      # 8-byte Folded Spill
	sd	s0, 16(sp)                      # 8-byte Folded Spill
	sd	s1, 8(sp)                       # 8-byte Folded Spill
	sd	s2, 0(sp)                       # 8-byte Folded Spill
	mv	s0, a3
	mv	s1, a2
	call	sum
	mv	s2, a0
	mv	a0, s1
	mv	a1, s0
	call	sum
	add	a0, a0, s2
	ld	ra, 24(sp)                      # 8-byte Folded Reload
	ld	s0, 16(sp)                      # 8-byte Folded Reload
	ld	s1, 8(sp)                       # 8-byte Folded Reload
	ld	s2, 0(sp)                       # 8-byte Folded Reload
	addi	sp, sp, 32
	ret
.Lfunc_end1:
	.size	sum2, .Lfunc_end1-sum2
                                        # -- End function
	.section	.text._start,"ax",@progbits
	.globl	_start                          # -- Begin function _start
	.p2align	2
	.type	_start,@function
_start:
# %bb.0:
	addi	sp, sp, -32
	sd	ra, 24(sp)                      # 8-byte Folded Spill
	sd	s0, 16(sp)                      # 8-byte Folded Spill
	sd	s1, 8(sp)                       # 8-byte Folded Spill
.LBB2_1:
	auipc	s0, %pcrel_hi(data)
	addi	s0, s0, %pcrel_lo(.LBB2_1)
	li	a1, 5
	mv	a0, s0
	call	sum
	mv	s1, a0
	addi	a0, s0, 8
	li	a1, 3
	call	sum
	add	a0, a0, s1
	li	a7, 93
	#APP
	ecall	
	#NO_APP
	ld	ra, 24(sp)                      # 8-byte Folded Reload
	ld	s0, 16(sp)                      # 8-byte Folded Reload
	ld	s1, 8(sp)                       # 8-byte Folded Reload
	addi	sp, sp, 32
	ret
.Lfunc_end2:
	.size	_start, .Lfunc_end2-_start
                                        # -- End function
	.type	data,@object                    # @data
	.section	.data.data,"aw",@progbits
	.globl	data
	.p2align	3
data:
	.quad	1                               # 0x1
	.quad	2                               # 0x2
	.quad	3                               # 0x3
	.quad	4                               # 0x4
	.quad	5                               # 0x5
	.size	data, 40

	.ident	"clang version 15.0.7 (AWS 15.0.7-3.amzn2023.0.4)"
	.section	".note.GNU-stack","",@progbits
	.addrsig
	.addrsig_sym data
