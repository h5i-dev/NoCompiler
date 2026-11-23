#! expect copy: assumed
#! expect f: accept
#: unsafe fn copy [d, s, n] in a0: int(d), a1: int(s), a2: int(n) borrow d ↦ bytes[n] rw, s ↦ bytes[n] ro stack 0
#: fn f [ρ] in a0: int(ρ) borrow ρ ↦ bytes[64] rw frame 16 slots 8 stack 16
f:
    addi sp, sp, -16
    sd   ra, 8(sp)
    addi a1, a0, 32
    li   a2, 32
    jal  ra, copy
    ld   ra, 8(sp)
    addi sp, sp, 16
    ret
