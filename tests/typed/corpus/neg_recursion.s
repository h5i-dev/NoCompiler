#! expect f: reject recursion
#: fn f [] frame 16 slots 8 stack 1024
f:
    addi sp, sp, -16
    sd   ra, 8(sp)
    jal  ra, f
    ld   ra, 8(sp)
    addi sp, sp, 16
    ret
