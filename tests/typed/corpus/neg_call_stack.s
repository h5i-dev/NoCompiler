#! expect g: assumed
#! expect f: reject call-stack
#: unsafe fn g [] stack 64
#: fn f [] frame 16 slots 8 stack 32
f:
    addi sp, sp, -16
    sd   ra, 8(sp)
    jal  ra, g
    ld   ra, 8(sp)
    addi sp, sp, 16
    ret
