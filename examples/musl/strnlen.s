# musl 1.2.5 src/string/strnlen.c (MIT, see examples/musl/COPYRIGHT), compiled by scripts/musl-trial/build.sh.
# Instructions as compiled, unchanged (scripts/musl-trial/verify.sh checks the bytes).
# Annotations are the lines that start with hash-colon (provisional syntax of docs/Tab 1.md; see docs/typed/musl-trial.md).
# Predicted (fixed before compiling): accept (signature stronger than C: n bytes readable)
# Expected now (after reading the compiled code): accept iff auipc/jalr (R_RISCV_CALL) is taken as a call; uses memchr's signature (memchr itself is expected to be rejected).
#! expect strnlen: accept
#: fn memchr [s, n]
#:   in     a0: int(s), a2: int(n)
#:   borrow s |-> bytes[n] ro
#:   out    a0: int
#:   stack  0
#: fn strnlen [s, n]
#:   in     a0: int(s), a1: int(n)
#:   borrow s |-> bytes[n] ro
#:   out    a0: int
#:   stack  32
#:   frame  32 slots 8, 16, 24
	.text
	.globl strnlen
	.p2align 2
	.type strnlen,@function
strnlen:
	addi	sp, sp, -32             # 0: fe010113
	sd	ra, 24(sp)              # 4: 00113c23
	sd	s0, 16(sp)              # 8: 00813823
	sd	s1, 8(sp)               # c: 00913423
	addi	s0, a1, 0               # 10: 00058413
	addi	s1, a0, 0               # 14: 00050493
	addi	a1, zero, 0             # 18: 00000593
	addi	a2, s0, 0               # 1c: 00040613
	call	memchr                  # 20: 00000097 000080e7
	beq	a0, zero, .Lstrnlen_30  # 28: 00050463
	sub	s0, a0, s1              # 2c: 40950433
.Lstrnlen_30:
	addi	a0, s0, 0               # 30: 00040513
	ld	ra, 24(sp)              # 34: 01813083
	ld	s0, 16(sp)              # 38: 01013403
	ld	s1, 8(sp)               # 3c: 00813483
	addi	sp, sp, 32              # 40: 02010113
	jalr	zero, 0(ra)             # 44: 00008067
	.size strnlen, .-strnlen
