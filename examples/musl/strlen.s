	.text
	.globl strlen
	.p2align 2
	.type strlen,@function
strlen:
	andi	a2, a0, 7               # 0: 00757613
	addi	a1, a0, 0               # 4: 00050593
	beq	a2, zero, .Lstrlen_2c   # 8: 02060263
	addi	a2, a0, 1               # c: 00150613
	addi	a1, a0, 0               # 10: 00050593
.Lstrlen_14:
	#: inv [p] a1: int(p), a2: int(p + 1) where s <= p < s + n decreases s + n - p
	lbu	a3, 0(a1)               # 14: 0005c683
	beq	a3, zero, .Lstrlen_70   # 18: 04068c63
	addi	a1, a1, 1               # 1c: 00158593
	andi	a3, a2, 7               # 20: 00767693
	addi	a2, a2, 1               # 24: 00160613
	bne	a3, zero, .Lstrlen_14   # 28: fe0696e3
.Lstrlen_2c:
.Lpcrel_2c:
	auipc	a2, %pcrel_hi(.LCPI0_0) # 2c: 00000617
	addi	a2, a2, %pcrel_lo(.Lpcrel_2c)# 30: 00060613
	ld	a3, 0(a2)               # 34: 00063683
.Lpcrel_38:
	auipc	a2, %pcrel_hi(.LCPI0_1) # 38: 00000617
	addi	a2, a2, %pcrel_lo(.Lpcrel_38)# 3c: 00060613
	ld	a4, 0(a2)               # 40: 00063703
	addi	a2, a1, -9              # 44: ff758613
.Lstrlen_48:
	#: inv [p] a2: int(p - 9) where s <= p, p + 8 <= s + n, 8 | p decreases s + n - p
	ld	a1, 9(a2)               # 48: 00963583
	add	a5, a1, a4              # 4c: 00e587b3
	andn	a1, a3, a1              # 50: 40b6f5b3
	and	a1, a1, a5              # 54: 00f5f5b3
	addi	a2, a2, 8               # 58: 00860613
	beq	a1, zero, .Lstrlen_48   # 5c: fe0586e3
.Lstrlen_60:
	#: inv [p] a2: int(p - 1) where s <= p < s + n decreases s + n - p
	lbu	a3, 1(a2)               # 60: 00164683
	addi	a1, a2, 1               # 64: 00160593
	addi	a2, a1, 0               # 68: 00058613
	bne	a3, zero, .Lstrlen_60   # 6c: fe069ae3
.Lstrlen_70:
	sub	a0, a1, a0              # 70: 40a58533
	jalr	zero, 0(ra)             # 74: 00008067
	.size strlen, .-strlen

	.section .rodata.cst8,"aM",@progbits,8
	.p2align 3
.LCPI0_0:
	.quad	0x8080808080808080
.LCPI0_1:
	.quad	0xfefefefefefefeff
