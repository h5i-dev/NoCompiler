# reads 65 bytes into a 64-byte frame buffer
#! expect f: reject call-cap
#: fn f [] frame 80 slots 72 addr [0, 64) out a0: int stack 80
f:
    addi sp, sp, -80
    sd   ra, 72(sp)
    mv   a1, sp
    li   a0, 0
    li   a2, 65
    li   a7, 63
    ecall
    ld   ra, 72(sp)
    addi sp, sp, 80
    ret
