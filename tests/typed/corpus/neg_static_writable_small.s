# The signature lends 4 bytes of the 8-byte symbol; the 8-byte load does not fit.
#! expect bump: reject mem-bounds
	.text
#: fn bump [] borrow @counter ↦ bytes[4] rw out a0: int stack 0
bump:
.Lpcrel_3:
	auipc	a1, %pcrel_hi(counter)
	ld	a0, %pcrel_lo(.Lpcrel_3)(a1)
	ret
	.data
	.p2align 3
counter:
	.quad	0
