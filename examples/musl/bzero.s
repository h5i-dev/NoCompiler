	.text
	.globl bzero
	.p2align 2
	.type bzero,@function
bzero:
	addi	a2, a1, 0               # 0: 00058613
	addi	a1, zero, 0             # 4: 00000593
	tail	memset                  # 8: 00000317 00030067
	.size bzero, .-bzero
