# Index checked against 17 for a 16-byte table.
#! expect lookup: reject mem-bounds
	.text
#: fn lookup [i] in a0: int(i) out a0: int stack 0
lookup:
	li	a1, 17
	bgeu	a0, a1, .Lbad
.Lpcrel_1:
	auipc	a1, %pcrel_hi(hexdigits)
	addi	a1, a1, %pcrel_lo(.Lpcrel_1)
	add	a0, a1, a0
	lbu	a0, 0(a0)
	ret
.Lbad:
	li	a0, 0
	ret
	.section .rodata,"a",@progbits
hexdigits:
	.ascii	"0123456789abcdef"
