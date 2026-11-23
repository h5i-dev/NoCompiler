#! expect g: assumed
#! expect f: reject call-partial
#: unsafe partial fn g [] stack 0
#: fn f [] frame 16 slots 8 stack 16
f:
    addi sp, sp, -16
    sd   ra, 8(sp)
    jal  ra, g
    ld   ra, 8(sp)
    addi sp, sp, 16
    ret
