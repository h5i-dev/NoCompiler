# frees a block it only borrowed
#! expect free: assumed
#! expect f: reject ret-borrow
#: unsafe fn free [p, n] in a0: int(p) take p ↦ bytes[n] rw heap borrow Heap stack 0
#: fn f [p, n] in a0: int(p) borrow p ↦ bytes[n] rw heap, Heap frame 16 slots 8 stack 16
f:
    addi sp, sp, -16
    sd   ra, 8(sp)
    jal  ra, free
    ld   ra, 8(sp)
    addi sp, sp, 16
    ret
