# examples/typed/src/cobs.c (bcb19fed), compiled by scripts/typed-trial/build.sh, unchanged;
# annotations are the '#:' lines (docs/typed/note-trial.md). The outer loop is entered at
# .LBB0_8, in the middle of the address interval that starts at .LBB0_7: S2 rejects it.
# The annotations are for the natural loops (proposal P1, --loops natural).
#! expect cobs_decode: accept
#! expect-interval cobs_decode: reject cfg
#: fn cobs_decode [r, b, len]
#:   in     a0: int(r), a1: int(b), a2: int(len)
#:   borrow r ↦ bytes[24] rw
#:   borrow b ↦ bytes[len] rw
#:   where  8 ∣ r
#:   stack  0
	.text
	.attribute	4, 16
	.file	"cobs.c"
	.section	.text.cobs_decode,"ax",@progbits
	.globl	cobs_decode                     # -- Begin function cobs_decode
	.p2align	2
	.type	cobs_decode,@function
cobs_decode:
# %bb.0:
	beqz	a2, .LBB0_16
# %bb.1:
	li	a3, 0
.LBB0_2:
	#: inv [i] a3: int(i) where 0 ≤ i < len decreases len − i
	add	a4, a1, a3
	lbu	a4, 0(a4)
	beqz	a4, .LBB0_5
# %bb.3:                                #   in Loop: Header=BB0_2 Depth=1
	addi	a3, a3, 1
	bne	a2, a3, .LBB0_2
# %bb.4:
	mv	a3, a2
.LBB0_5:
	#: join [n] a3: int(n) where 0 ≤ n ≤ len
	beqz	a3, .LBB0_17
# %bb.6:
	li	a5, 0
	li	a2, 0
	addi	a4, a1, 1
	j	.LBB0_8
.LBB0_7:
	#: join [s2, d2] a5: int(s2), a2: int(d2) where s + 1 ≤ s2 ≤ n, 0 ≤ d2 ≤ s2
	bgeu	a5, a3, .LBB0_18
.LBB0_8:
	#: inv [s, d, n] a5: int(s), a2: int(d), a3: int(n) where 0 ≤ d ≤ s < n ≤ len decreases n − s
                                        #     Child Loop BB0_11 Depth 2
	add	a6, a1, a5
	lbu	a6, 0(a6)
	add	a7, a5, a6
	bltu	a3, a7, .LBB0_19
# %bb.9:                                #   in Loop: Header=BB0_8 Depth=1
	addi	t0, a5, 1
	bgeu	t0, a7, .LBB0_13
# %bb.10:                               #   in Loop: Header=BB0_8 Depth=1
	addi	t0, a6, -1
	add	a5, a4, a5
.LBB0_11:
	#: inv [k, c] a6: int(c), a7: int(s + c), t0: int(k), a5: int(b + s + c − k),
	#:     a2: int(d + c − 1 − k) where 1 ≤ k ≤ c − 1, s + c ≤ n decreases k
                                        # =>  This Inner Loop Header: Depth=2
	lb	t1, 0(a5)
	add	t2, a1, a2
	addi	a2, a2, 1
	sb	t1, 0(t2)
	addi	t0, t0, -1
	addi	a5, a5, 1
	bnez	t0, .LBB0_11
# %bb.12:                               #   in Loop: Header=BB0_8 Depth=1
	mv	a5, a7
	j	.LBB0_14
.LBB0_13:
	mv	a5, t0
.LBB0_14:
	#: join [s1, d1] a5: int(s1), a2: int(d1) where s + 1 ≤ s1 ≤ n, 0 ≤ d1, d1 + 1 ≤ s1
	addi	a6, a6, -255
	snez	a6, a6
	sltu	a7, a5, a3
	and	a6, a6, a7
	beqz	a6, .LBB0_7
# %bb.15:                               #   in Loop: Header=BB0_8 Depth=1
	add	a6, a1, a2
	addi	a2, a2, 1
	sb	zero, 0(a6)
	j	.LBB0_7
.LBB0_16:
	li	a1, 1
	sd	a1, 0(a0)
	sd	zero, 8(a0)
	ret
.LBB0_17:
	li	a2, 0
	li	a5, 0
.LBB0_18:
	sd	zero, 0(a0)
	sd	a5, 8(a0)
	sd	a2, 16(a0)
	ret
.LBB0_19:
	li	a1, 1
	sd	a1, 0(a0)
	sd	a1, 8(a0)
	sd	a2, 16(a0)
	ret
.Lfunc_end0:
	.size	cobs_decode, .Lfunc_end0-cobs_decode
                                        # -- End function
	.ident	"clang version 15.0.7 (AWS 15.0.7-3.amzn2023.0.4)"
	.section	".note.GNU-stack","",@progbits
	.addrsig
