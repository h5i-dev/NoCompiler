# Writable static data has no implicit capability (I32): reading it needs a signature that
# lends it.
#! expect bump: reject mem-bounds
	.text
#: fn bump [] stack 0
bump:
.Lpcrel_3:
	auipc	a1, %pcrel_hi(counter)
	ld	a2, %pcrel_lo(.Lpcrel_3)(a1)
	ret
	.data
	.p2align 3
counter:
	.quad	0
