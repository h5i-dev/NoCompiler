# musl 1.2.5 src/stdlib/div.c (MIT, see examples/musl/COPYRIGHT), compiled by scripts/musl-trial/build.sh.
# Instructions as compiled, unchanged (scripts/musl-trial/verify.sh checks the bytes).
# Annotations are the lines that start with hash-colon (docs/typed/syntax.md).
# Predicted (batch 3, fixed before compiling): accept
# Expected now (after reading the compiled code): accept: divw/mulw/subw/add.uw/or give int; div_t comes back packed in a0.
#! expect div: accept
#: fn div [a, b]
#:   in     a0: int(a), a1: int(b)
#:   out    a0: int
#:   stack  0
	.section .text.div,"ax",@progbits
	.globl div
	.p2align 2
	.type div,@function
div:
	divw	a2, a0, a1              # 0: 02b5463b
	mulw	a1, a2, a1              # 4: 02b605bb
	subw	a0, a0, a1              # 8: 40b5053b
	slli	a0, a0, 32              # c: 02051513
	add.uw	a1, a2, zero            # 10: 080605bb
	or	a0, a0, a1              # 14: 00b56533
	jalr	zero, 0(ra)             # 18: 00008067
	.size div, .-div
