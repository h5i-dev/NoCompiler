# Writable static data lent by the signature (I32): `@counter` is the symbol's address.
#! expect bump: accept
	.text
#: fn bump [] borrow @counter ↦ bytes[8] rw out a0: int stack 0
bump:
.Lpcrel_3:
	auipc	a1, %pcrel_hi(counter)
	ld	a0, %pcrel_lo(.Lpcrel_3)(a1)
	addi	a0, a0, 1
	sd	a0, %pcrel_lo(.Lpcrel_3)(a1)
	ret
	.data
	.p2align 3
counter:
	.quad	0
