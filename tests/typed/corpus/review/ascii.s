# From the independent soundness review (2026-11-23); accepted before I33.
#! expect f: reject mem-bounds
#: fn f
#:   out a0: int(5)
#:   stack 0
    .text
    .globl f
f:
.Lp:
    auipc a0, %pcrel_hi(tbl)
    addi a0, a0, %pcrel_lo(.Lp)
    ld a0, 8(a0)          # checker: tbl+8 holds 5; actually bytes 8..15 run past tbl (12 bytes)
    ret

    .section .rodata
    .p2align 3
tbl:
    .ascii "ab", "cd"
    .quad 5
