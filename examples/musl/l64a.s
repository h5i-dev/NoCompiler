# musl 1.2.5 src/misc/a64l.c (MIT, see examples/musl/COPYRIGHT), compiled by scripts/musl-trial/build.sh.
# Instructions as compiled, unchanged (scripts/musl-trial/verify.sh checks the bytes).
# Annotations are the lines that start with hash-colon (docs/typed/syntax.md).
# Predicted (batch 3, fixed before compiling): reject static-data
# Expected now (after reading the compiled code): reject static-data: auipc to l64a.s in .bss (writable) at 0x8; I30 supports read-only data only. The read of digits[x & 63] would be fine (I30).
#! expect l64a: reject static-data
#: fn l64a [x]
#:   in     a0: int(x)
#:   out    a0: int
#:   stack  0
	.section .text.l64a,"ax",@progbits
	.globl l64a
	.p2align 2
	.type l64a,@function
l64a:
	addiw	a1, a0, 0               # 0: 0005059b
	beq	a1, zero, .Ll64a_40     # 4: 02058e63
.Lpcrel_8:
	auipc	a1, %pcrel_hi(l64a.s)   # 8: 00000597
	addi	a1, a1, %pcrel_lo(.Lpcrel_8)# c: 00058593
.Lpcrel_10:
	auipc	a2, %pcrel_hi(digits)   # 10: 00000617
	addi	a2, a2, %pcrel_lo(.Lpcrel_10)# 14: 00060613
	addi	a3, zero, 63            # 18: 03f00693
.Ll64a_1c:
	andi	a4, a0, 63              # 1c: 03f57713
	add	a4, a2, a4              # 20: 00e60733
	lb	a4, 0(a4)               # 24: 00070703
	addiw	a5, a0, 0               # 28: 0005079b
	sb	a4, 0(a1)               # 2c: 00e58023
	addi	a1, a1, 1               # 30: 00158593
	srliw	a0, a0, 6               # 34: 0065551b
	bltu	a3, a5, .Ll64a_1c       # 38: fef6e2e3
	jal	zero, .Ll64a_48         # 3c: 00c0006f
.Ll64a_40:
.Lpcrel_40:
	auipc	a1, %pcrel_hi(l64a.s)   # 40: 00000597
	addi	a1, a1, %pcrel_lo(.Lpcrel_40)# 44: 00058593
.Ll64a_48:
.Lpcrel_48:
	auipc	a0, %pcrel_hi(l64a.s)   # 48: 00000517
	addi	a0, a0, %pcrel_lo(.Lpcrel_48)# 4c: 00050513
	sb	zero, 0(a1)             # 50: 00058023
	jalr	zero, 0(ra)             # 54: 00008067
	.size l64a, .-l64a

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

	.section .bss.l64a.s,"aw",@nobits
l64a.s:
	.zero	1
	.zero	1
	.zero	1
	.zero	1
	.zero	1
	.zero	1
	.zero	1
