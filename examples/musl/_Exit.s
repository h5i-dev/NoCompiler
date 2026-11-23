# musl 1.2.5 src/exit/_Exit.c (MIT, see examples/musl/COPYRIGHT), compiled by scripts/musl-trial/build.sh.
# Instructions as compiled, unchanged (scripts/musl-trial/verify.sh checks the bytes).
# Annotations are the lines that start with hash-colon (docs/typed/syntax.md).
# Predicted (batch 3, fixed before compiling): accept
# Expected now (after reading the compiled code): accept: ecall 94 has no successor (I17); the exit loop after it is unreachable, so its head is annotated 'where false' (true of an unreachable point).
#! expect _Exit: accept
#: fn _Exit [c]
#:   in     a0: int(c)
#:   stack  0
	.section .text._Exit,"ax",@progbits
	.globl _Exit
	.p2align 2
	.type _Exit,@function
_Exit:
	addi	a1, a0, 0               # 0: 00050593
	addi	a7, zero, 94            # 4: 05e00893
	ecall	                        # 8: 00000073
	addi	a7, zero, 93            # c: 05d00893
.L_Exit_10:
	#: inv where false decreases 0
	addi	a0, a1, 0               # 10: 00058513
	ecall	                        # 14: 00000073
	jal	zero, .L_Exit_10        # 18: ff9ff06f
	.size _Exit, .-_Exit
