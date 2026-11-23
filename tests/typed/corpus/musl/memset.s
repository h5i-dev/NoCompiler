# musl 1.2.5 src/string/memset.c (MIT, see examples/musl/COPYRIGHT), compiled by scripts/musl-trial/build.sh.
# Instructions as compiled, unchanged (scripts/musl-trial/verify.sh checks the bytes).
# Annotations are the lines that start with hash-colon (provisional syntax of docs/Tab 1.md; see docs/typed/musl-trial.md).
# Predicted (fixed before compiling): reject (v0 rules: andi -4, andi 4)
# Expected now (after reading the compiled code): reject (v0 rules), as predicted. 0x50 andi a2, a2, -4 (negative constant: not in the table, a2 becomes an unrelated int), so the store sw a5, -4(a1) at 0x70 (a1 = a3 + a2) is not provably inside s..s+n. Later 0xb0/0xb4 andi 4 + ori 24 lose the offset again.
#! expect memset: reject loop-inv
#: fn memset [s, n]
#:   in     a0: int(s), a2: int(n)
#:   borrow s |-> bytes[n] rw
#:   out    a0: int(s)
#:   stack  0
	.section .text.memset,"ax",@progbits
	.globl memset
	.p2align 2
	.type memset,@function
memset:
	beq	a2, zero, .Lmemset_f8   # 0: 0e060c63
	sb	a1, 0(a0)               # 4: 00b50023
	add	a3, a2, a0              # 8: 00a606b3
	addi	a4, zero, 3             # c: 00300713
	sb	a1, -1(a3)              # 10: feb68fa3
	bltu	a2, a4, .Lmemset_f8     # 14: 0ee66263
	sb	a1, 1(a0)               # 18: 00b500a3
	sb	a1, 2(a0)               # 1c: 00b50123
	sb	a1, -2(a3)              # 20: feb68f23
	addi	a4, zero, 7             # 24: 00700713
	sb	a1, -3(a3)              # 28: feb68ea3
	bltu	a2, a4, .Lmemset_f8     # 2c: 0ce66663
	sb	a1, 3(a0)               # 30: 00b501a3
	addi	a4, zero, 9             # 34: 00900713
	sb	a1, -4(a3)              # 38: feb68e23
	bltu	a2, a4, .Lmemset_f8     # 3c: 0ae66e63
	subw	a3, zero, a0            # 40: 40a006bb
	andi	a5, a3, 3               # 44: 0036f793
	add	a3, a0, a5              # 48: 00f506b3
	sub	a2, a2, a5              # 4c: 40f60633
	andi	a2, a2, -4              # 50: ffc67613
	slli	a1, a1, 56              # 54: 03859593
	lui	a5, 65793               # 58: 101017b7
	slli	a5, a5, 4               # 5c: 00479793
	addi	a5, a5, 256             # 60: 10078793
	mulhu	a5, a1, a5              # 64: 02f5b7b3
	sw	a5, 0(a3)               # 68: 00f6a023
	add	a1, a3, a2              # 6c: 00c685b3
	sw	a5, -4(a1)              # 70: fef5ae23
	bltu	a2, a4, .Lmemset_f8     # 74: 08e66263
	addiw	a4, a5, 0               # 78: 0007871b
	sw	a4, 4(a3)               # 7c: 00e6a223
	sw	a4, 8(a3)               # 80: 00e6a423
	sw	a4, -12(a1)             # 84: fee5aa23
	addi	a5, zero, 25            # 88: 01900793
	sw	a4, -8(a1)              # 8c: fee5ac23
	bltu	a2, a5, .Lmemset_f8     # 90: 06f66463
	sw	a4, 12(a3)              # 94: 00e6a623
	sw	a4, 16(a3)              # 98: 00e6a823
	sw	a4, 20(a3)              # 9c: 00e6aa23
	sw	a4, 24(a3)              # a0: 00e6ac23
	sw	a4, -28(a1)             # a4: fee5a223
	sw	a4, -24(a1)             # a8: fee5a423
	sw	a4, -20(a1)             # ac: fee5a623
	andi	a5, a3, 4               # b0: 0046f793
	ori	a5, a5, 24              # b4: 0187e793
	sub	a2, a2, a5              # b8: 40f60633
	addi	a6, zero, 32            # bc: 02000813
	sw	a4, -16(a1)             # c0: fee5a823
	bltu	a2, a6, .Lmemset_f8     # c4: 03066a63
	add.uw	a1, a4, zero            # c8: 080705bb
	slli	a4, a4, 32              # cc: 02071713
	or	a1, a4, a1              # d0: 00b765b3
	add	a3, a3, a5              # d4: 00f686b3
	addi	a4, zero, 31            # d8: 01f00713
.Lmemset_dc:
	#: inv [p, m] a3: int(p), a2: int(m) where s <= p, p + m <= s + n, 32 <= m, 8 | p decreases m
	sd	a1, 0(a3)               # dc: 00b6b023
	sd	a1, 8(a3)               # e0: 00b6b423
	sd	a1, 16(a3)              # e4: 00b6b823
	sd	a1, 24(a3)              # e8: 00b6bc23
	addi	a2, a2, -32             # ec: fe060613
	addi	a3, a3, 32              # f0: 02068693
	bltu	a4, a2, .Lmemset_dc     # f4: fec764e3
.Lmemset_f8:
	jalr	zero, 0(ra)             # f8: 00008067
	.size memset, .-memset
