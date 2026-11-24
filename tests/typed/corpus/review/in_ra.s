# From the independent soundness review (2026-11-23); accepted before I33.
#! expect g: reject sig
#! expect f: reject call-sig
# g's contract only covers entries with ra = 0 (and a0 = anything);
# f's call is checked against ra *before* the jal writes ra = pc + 4.
#: extern fn g
#:   in ra: int(0)
#:   stack 0

#: fn f
#:   stack 16
#:   frame 16 slots 0
    .text
f:
    addi sp, sp, -16
    sd ra, 0(sp)
    li ra, 0
    call g
    ld ra, 0(sp)
    addi sp, sp, 16
    ret
