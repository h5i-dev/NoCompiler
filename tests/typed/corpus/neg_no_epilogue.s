#! expect f: reject stack-shape
#: fn f [] frame 16 slots 8 stack 16
f:
    addi sp, sp, -16
    sd   ra, 8(sp)
    ld   ra, 8(sp)
    ret
