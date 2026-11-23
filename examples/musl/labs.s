# musl 1.2.5 src/stdlib/labs.c (MIT, see examples/musl/COPYRIGHT), compiled by scripts/musl-trial/build.sh.
# Instructions as compiled, unchanged (scripts/musl-trial/verify.sh checks the bytes).
# Annotations are the lines that start with hash-colon (provisional syntax of docs/Tab 1.md; see docs/typed/musl-trial.md).
# Predicted (fixed before compiling): accept
# Expected now (after reading the compiled code): accept. max (Zbb) is not in the table, so a0 is just int.
#! expect labs: accept
#: fn labs [x]
#:   in     a0: int(x)
#:   out    a0: int
#:   stack  0
	.section .text.labs,"ax",@progbits
	.globl labs
	.p2align 2
	.type labs,@function
labs:
	sub	a1, zero, a0            # 0: 40a005b3
	max	a0, a0, a1              # 4: 0ab56533
	jalr	zero, 0(ra)             # 8: 00008067
	.size labs, .-labs
