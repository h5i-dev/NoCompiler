# hands an address-taken frame range to a function that keeps it
#! expect keep: assumed
#! expect f: reject frame
#: unsafe fn keep [b] in a0: int(b) take b ↦ bytes[16] rw stack 0
#: fn f [] frame 32 slots 24 addr [0, 16) stack 32
f:
    addi sp, sp, -32
    sd   ra, 24(sp)
    mv   a0, sp
    jal  ra, keep
    ld   ra, 24(sp)
    addi sp, sp, 32
    ret
