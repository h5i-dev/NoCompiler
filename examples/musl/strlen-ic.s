# musl 1.2.5 src/string/strlen.c (MIT, see examples/musl/COPYRIGHT), compiled by scripts/musl-trial/build.sh
# with -mllvm -riscv-disable-using-constant-pool-for-large-ints (constants inline, no static data).
# Instructions as compiled, unchanged (scripts/musl-trial/verify.sh checks the bytes).
# Annotations are the lines that start with hash-colon (provisional syntax of docs/Tab 1.md; see docs/typed/musl-trial.md).
# Predicted (fixed before compiling this variant): not expressible
# Expected now (after reading the compiled code): not expressible, as predicted. The closest signature borrows s |-> bytes[n] ro, but nothing ties n to where the NUL is: the byte loop 0x14 and the word loop 0x64 stop on memory contents, so no invariant bounds the address and no decreases clause is provable. The word loop also reads whole aligned words past the NUL.
#! expect strlen: reject loop-inv
#: fn strlen [s, n]
#:   in     a0: int(s)
#:   borrow s |-> bytes[n] ro
#:   out    a0: int
#:   stack  0
# Not the C contract: C needs "a NUL at some s+k with s..s+k readable", not a v0 signature.
	.section .text.strlen,"ax",@progbits
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
	beq	a3, zero, .Lstrlen_8c   # 18: 06068a63
	addi	a1, a1, 1               # 1c: 00158593
	andi	a3, a2, 7               # 20: 00767693
	addi	a2, a2, 1               # 24: 00160613
	bne	a3, zero, .Lstrlen_14   # 28: fe0696e3
.Lstrlen_2c:
	lui	a2, 983297              # 2c: f0101637
	slli	a2, a2, 4               # 30: 00461613
	addi	a2, a2, 257             # 34: 10160613
	slli	a2, a2, 16              # 38: 01061613
	addi	a2, a2, 257             # 3c: 10160613
	slli	a2, a2, 15              # 40: 00f61613
	addi	a3, a2, 128             # 44: 08060693
	addi	a2, a1, -9              # 48: ff758613
	lui	a1, 1044464             # 4c: feff05b7
	addiw	a1, a1, -257            # 50: eff5859b
	slli	a1, a1, 16              # 54: 01059593
	addi	a1, a1, -257            # 58: eff58593
	slli	a1, a1, 16              # 5c: 01059593
	addi	a1, a1, -257            # 60: eff58593
.Lstrlen_64:
	#: inv [p] a2: int(p - 9) where s <= p, p + 8 <= s + n, 8 | p decreases s + n - p
	ld	a4, 9(a2)               # 64: 00963703
	add	a5, a4, a1              # 68: 00b707b3
	andn	a4, a3, a4              # 6c: 40e6f733
	and	a4, a4, a5              # 70: 00f77733
	addi	a2, a2, 8               # 74: 00860613
	beq	a4, zero, .Lstrlen_64   # 78: fe0706e3
.Lstrlen_7c:
	#: inv [p] a2: int(p - 1) where s <= p < s + n decreases s + n - p
	lbu	a3, 1(a2)               # 7c: 00164683
	addi	a1, a2, 1               # 80: 00160593
	addi	a2, a1, 0               # 84: 00058613
	bne	a3, zero, .Lstrlen_7c   # 88: fe069ae3
.Lstrlen_8c:
	sub	a0, a1, a0              # 8c: 40a58533
	jalr	zero, 0(ra)             # 90: 00008067
	.size strlen, .-strlen
