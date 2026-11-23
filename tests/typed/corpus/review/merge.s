# From the independent soundness review (2026-11-23); accepted before I33.
#! expect f: reject static-data
#: fn f
#:   out a0: int(2)
#:   stack 0
    .text
    .globl f
f:
.Lp:
    auipc a0, %pcrel_hi(tbl)
    ld a0, %pcrel_lo(.Lp)(a0)       # placeholder to use tbl
.Lq:
    auipc a0, %pcrel_hi(tbl)
    addi a0, a0, %pcrel_lo(.Lq)
    ld a0, 8(a0)                    # checker: field 8 of tbl = 2
    ret

    .section .rodata.cst8,"aM",@progbits,8
    .p2align 3
a:
    .quad 2
tbl:
    .quad 1
    .quad 2       # an 8-byte merge piece identical to a's: the linker may fold it away
