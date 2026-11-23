# lends a part of a range (the last 8 words of 64 bytes)
#! expect sum: assumed
#! expect f: accept
#: unsafe fn sum [ρ, n] in a0: int(ρ), a1: int(n) borrow ρ ↦ bytes[8n] ro where 8 ∣ ρ out a0: int stack 0
#: fn f [ρ] in a0: int(ρ) borrow ρ ↦ bytes[64] ro where 8 ∣ ρ frame 16 slots 8 stack 16
f:
    addi sp, sp, -16
    sd   ra, 8(sp)
    addi a0, a0, 32
    li   a1, 4
    jal  ra, sum
    ld   ra, 8(sp)
    addi sp, sp, 16
    ret
