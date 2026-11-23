# examples/typed/src/hello.c (bcb19fed), compiled by scripts/typed-trial/build.sh, unchanged;
# annotations are the '#:' lines (docs/typed/note-trial.md).
#! expect write_all: accept
#! expect hello: accept
#: fn write_all [fd, b, n]
#:   in     a0: int(fd), a1: int(b), a2: int(n)
#:   borrow b ↦ bytes[n] ro
#:   where  0 ≤ n < 2^64
#:   out    a0: int
#:   stack  0
#: fn hello []
#:   frame  16 slots 8
#:   stack  16
	.text
	.attribute	4, 16
	.attribute	5, "rv64i2p0_m2p0_zba1p0_zbb1p0"
	.file	"hello.c"
	.section	.text.write_all,"ax",@progbits
	.globl	write_all                       # -- Begin function write_all
	.p2align	2
	.type	write_all,@function
write_all:
# %bb.0:
	mv	a3, a0
	li	a7, 64
.LBB0_1:
	#: inv [m] a1: int(b + n − m), a2: int(m) where 0 ≤ m ≤ n decreases m
	beqz	a2, .LBB0_4
# %bb.2:                                #   in Loop: Header=BB0_1 Depth=1
	mv	a0, a3
	#APP
	ecall	
	#NO_APP
	add	a1, a1, a0
	sub	a2, a2, a0
	bgez	a0, .LBB0_1
# %bb.3:
	ret
.LBB0_4:
	li	a0, 0
	ret
.Lfunc_end0:
	.size	write_all, .Lfunc_end0-write_all
                                        # -- End function
	.section	.text.hello,"ax",@progbits
	.globl	hello                           # -- Begin function hello
	.p2align	2
	.type	hello,@function
hello:
# %bb.0:
	addi	sp, sp, -16
	sd	ra, 8(sp)                       # 8-byte Folded Spill
.LBB1_1:
	auipc	a1, %pcrel_hi(msg)
	addi	a1, a1, %pcrel_lo(.LBB1_1)
	li	a0, 1
	li	a2, 11
	call	write_all
	srli	a0, a0, 63
	li	a7, 93
	li	a1, 0
	li	a2, 0
	#APP
	ecall	
	#NO_APP
	ld	ra, 8(sp)                       # 8-byte Folded Reload
	addi	sp, sp, 16
	ret
.Lfunc_end1:
	.size	hello, .Lfunc_end1-hello
                                        # -- End function
	.section	.text._start,"ax",@progbits
	.globl	_start                          # -- Begin function _start
	.p2align	2
	.type	_start,@function
_start:
# %bb.0:
	tail	hello
.Lfunc_end2:
	.size	_start, .Lfunc_end2-_start
                                        # -- End function
	.type	msg,@object                     # @msg
	.section	.rodata.msg,"a",@progbits
msg:
	.asciz	"nocompiler\n"
	.size	msg, 12

	.ident	"clang version 15.0.7 (AWS 15.0.7-3.amzn2023.0.4)"
	.section	".note.GNU-stack","",@progbits
	.addrsig
	.addrsig_sym msg
