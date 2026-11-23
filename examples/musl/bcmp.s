	.text
	.globl bcmp
	.p2align 2
	.type bcmp,@function
bcmp:
	tail	memcmp                  # 0: 00000317 00030067
	.size bcmp, .-bcmp
