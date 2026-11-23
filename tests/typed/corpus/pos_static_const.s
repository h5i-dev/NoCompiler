# A constant loaded from read-only data (I30): the field gives the exact value.
#! expect mask: accept
	.text
#: fn mask [x] in a0: int(x) out a0: int(x + 0x0101010101010101) stack 0
	.globl mask
mask:
.Lpcrel_0:
	auipc	a1, %pcrel_hi(.LCPI0_0)
	ld	a1, %pcrel_lo(.Lpcrel_0)(a1)
	add	a0, a0, a1
	ret
	.section .rodata.cst8,"aM",@progbits,8
	.p2align 3
.LCPI0_0:
	.quad	0x0101010101010101
