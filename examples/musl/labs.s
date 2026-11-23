	.text
	.globl labs
	.p2align 2
	.type labs,@function
labs:
	sub	a1, zero, a0            # 0: 40a005b3
	max	a0, a0, a1              # 4: 0ab56533
	jalr	zero, 0(ra)             # 8: 00008067
	.size labs, .-labs
