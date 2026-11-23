	.text
	.globl strncpy
	.p2align 2
	.type strncpy,@function
strncpy:
	addi	sp, sp, -16             # 0: ff010113
	sd	ra, 8(sp)               # 4: 00113423
	sd	s0, 0(sp)               # 8: 00813023
	addi	s0, a0, 0               # c: 00050413
	call	__stpncpy               # 10: 00000097 000080e7
	addi	a0, s0, 0               # 18: 00040513
	ld	ra, 8(sp)               # 1c: 00813083
	ld	s0, 0(sp)               # 20: 00013403
	addi	sp, sp, 16              # 24: 01010113
	jalr	zero, 0(ra)             # 28: 00008067
	.size strncpy, .-strncpy
