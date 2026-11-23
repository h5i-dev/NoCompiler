# From the independent soundness review (2026-11-23); accepted before I33.
#! expect f: reject ret-out
#: fn f
#:   out a0: int(1)
#:   stack 0
    .text
    .globl f
f:
.Lp:
    auipc a0, %pcrel_hi(tbl)
    ld a0, %pcrel_lo(.Lp)(a0)
    ret

    .section .rodata
    .p2align 3
tbl:
    .byte 1
    .p2align 3, 0xff
