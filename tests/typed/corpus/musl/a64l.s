# musl 1.2.5 src/misc/a64l.c (MIT, see examples/musl/COPYRIGHT), compiled by scripts/musl-trial/build.sh.
# Instructions as compiled, unchanged (scripts/musl-trial/verify.sh checks the bytes).
# Annotations are the lines that start with hash-colon (docs/typed/syntax.md).
# Predicted (batch 3, fixed before compiling): not expressible
# Expected now (after reading the compiled code): not expressible, as predicted, but the reason narrowed: clang unrolled the loop completely (at most 6 characters, each read guarded by the previous one being non-zero), so a64l itself is fine with 'borrow s |-> bytes[6] ro' (narrower than C, where the string may be shorter). What is missing is strchr's contract: 'reads d up to its NUL' is not a v0 signature, so no contract is given and the call is rejected.
#! expect a64l: reject call-sig
#: fn a64l [s]
#:   in     a0: int(s)
#:   borrow s |-> bytes[6] ro
#:   out    a0: int
#:   stack  32
#:   frame  32 slots 0, 8, 16, 24
	.section .text.a64l,"ax",@progbits
	.globl a64l
	.p2align 2
	.type a64l,@function
a64l:
	addi	sp, sp, -32             # 0: fe010113
	sd	ra, 24(sp)              # 4: 00113c23
	sd	s0, 16(sp)              # 8: 00813823
	sd	s1, 8(sp)               # c: 00913423
	sd	s2, 0(sp)               # 10: 01213023
	lbu	a1, 0(a0)               # 14: 00054583
	beq	a1, zero, .La64l_11c    # 18: 10058263
	addi	s1, a0, 0               # 1c: 00050493
.Lpcrel_20:
	auipc	s0, %pcrel_hi(digits)   # 20: 00000417
	addi	s0, s0, %pcrel_lo(.Lpcrel_20)# 24: 00040413
	addi	a0, s0, 0               # 28: 00040513
	call	strchr                  # 2c: 00000097 000080e7
	beq	a0, zero, .La64l_11c    # 34: 0e050463
	lbu	a1, 1(s1)               # 38: 0014c583
	subw	s0, a0, s0              # 3c: 4085043b
	beq	a1, zero, .La64l_120    # 40: 0e058063
.Lpcrel_44:
	auipc	s2, %pcrel_hi(digits)   # 44: 00000917
	addi	s2, s2, %pcrel_lo(.Lpcrel_44)# 48: 00090913
	addi	a0, s2, 0               # 4c: 00090513
	call	strchr                  # 50: 00000097 000080e7
	beq	a0, zero, .La64l_120    # 58: 0c050463
	lbu	a1, 2(s1)               # 5c: 0024c583
	subw	a0, a0, s2              # 60: 4125053b
	slliw	a0, a0, 6               # 64: 0065151b
	or	s0, a0, s0              # 68: 00856433
	beq	a1, zero, .La64l_120    # 6c: 0a058a63
.Lpcrel_70:
	auipc	s2, %pcrel_hi(digits)   # 70: 00000917
	addi	s2, s2, %pcrel_lo(.Lpcrel_70)# 74: 00090913
	addi	a0, s2, 0               # 78: 00090513
	call	strchr                  # 7c: 00000097 000080e7
	beq	a0, zero, .La64l_120    # 84: 08050e63
	lbu	a1, 3(s1)               # 88: 0034c583
	subw	a0, a0, s2              # 8c: 4125053b
	slliw	a0, a0, 12              # 90: 00c5151b
	or	s0, a0, s0              # 94: 00856433
	beq	a1, zero, .La64l_120    # 98: 08058463
.Lpcrel_9c:
	auipc	s2, %pcrel_hi(digits)   # 9c: 00000917
	addi	s2, s2, %pcrel_lo(.Lpcrel_9c)# a0: 00090913
	addi	a0, s2, 0               # a4: 00090513
	call	strchr                  # a8: 00000097 000080e7
	beq	a0, zero, .La64l_120    # b0: 06050863
	lbu	a1, 4(s1)               # b4: 0044c583
	subw	a0, a0, s2              # b8: 4125053b
	slliw	a0, a0, 18              # bc: 0125151b
	or	s0, a0, s0              # c0: 00856433
	beq	a1, zero, .La64l_120    # c4: 04058e63
.Lpcrel_c8:
	auipc	s2, %pcrel_hi(digits)   # c8: 00000917
	addi	s2, s2, %pcrel_lo(.Lpcrel_c8)# cc: 00090913
	addi	a0, s2, 0               # d0: 00090513
	call	strchr                  # d4: 00000097 000080e7
	beq	a0, zero, .La64l_120    # dc: 04050263
	lbu	a1, 5(s1)               # e0: 0054c583
	subw	a0, a0, s2              # e4: 4125053b
	slliw	a0, a0, 24              # e8: 0185151b
	or	s0, a0, s0              # ec: 00856433
	beq	a1, zero, .La64l_120    # f0: 02058863
.Lpcrel_f4:
	auipc	s1, %pcrel_hi(digits)   # f4: 00000497
	addi	s1, s1, %pcrel_lo(.Lpcrel_f4)# f8: 00048493
	addi	a0, s1, 0               # fc: 00048513
	call	strchr                  # 100: 00000097 000080e7
	beq	a0, zero, .La64l_120    # 108: 00050c63
	subw	a0, a0, s1              # 10c: 4095053b
	slliw	a0, a0, 30              # 110: 01e5151b
	or	s0, a0, s0              # 114: 00856433
	jal	zero, .La64l_120        # 118: 0080006f
.La64l_11c:
	addi	s0, zero, 0             # 11c: 00000413
.La64l_120:
	addi	a0, s0, 0               # 120: 00040513
	ld	ra, 24(sp)              # 124: 01813083
	ld	s0, 16(sp)              # 128: 01013403
	ld	s1, 8(sp)               # 12c: 00813483
	ld	s2, 0(sp)               # 130: 00013903
	addi	sp, sp, 32              # 134: 02010113
	jalr	zero, 0(ra)             # 138: 00008067
	.size a64l, .-a64l

	.section .rodata.digits,"a",@progbits

digits:
	.byte	0x2e
	.byte	0x2f
	.byte	0x30
	.byte	0x31
	.byte	0x32
	.byte	0x33
	.byte	0x34
	.byte	0x35
	.byte	0x36
	.byte	0x37
	.byte	0x38
	.byte	0x39
	.byte	0x41
	.byte	0x42
	.byte	0x43
	.byte	0x44
	.byte	0x45
	.byte	0x46
	.byte	0x47
	.byte	0x48
	.byte	0x49
	.byte	0x4a
	.byte	0x4b
	.byte	0x4c
	.byte	0x4d
	.byte	0x4e
	.byte	0x4f
	.byte	0x50
	.byte	0x51
	.byte	0x52
	.byte	0x53
	.byte	0x54
	.byte	0x55
	.byte	0x56
	.byte	0x57
	.byte	0x58
	.byte	0x59
	.byte	0x5a
	.byte	0x61
	.byte	0x62
	.byte	0x63
	.byte	0x64
	.byte	0x65
	.byte	0x66
	.byte	0x67
	.byte	0x68
	.byte	0x69
	.byte	0x6a
	.byte	0x6b
	.byte	0x6c
	.byte	0x6d
	.byte	0x6e
	.byte	0x6f
	.byte	0x70
	.byte	0x71
	.byte	0x72
	.byte	0x73
	.byte	0x74
	.byte	0x75
	.byte	0x76
	.byte	0x77
	.byte	0x78
	.byte	0x79
	.byte	0x7a
	.byte	0x00
