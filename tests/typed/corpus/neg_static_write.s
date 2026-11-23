#! expect poke: reject mem-write
	.text
#: fn poke [] stack 0
poke:
.Lpcrel_2:
	auipc	a1, %pcrel_hi(.LC0)
	sd	zero, %pcrel_lo(.Lpcrel_2)(a1)
	ret
	.section .rodata.cst8,"aM",@progbits,8
	.p2align 3
.LC0:
	.quad	7
