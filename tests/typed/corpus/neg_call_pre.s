#! expect sum: assumed
#! expect f: reject call-pre
#: unsafe fn sum [ρ, n] in a0: int(ρ), a1: int(n) borrow ρ ↦ bytes[8n] ro where 8 ∣ ρ out a0: int stack 0
#: fn f [ρ] in a0: int(ρ) borrow ρ ↦ bytes[64] ro where 4 ∣ ρ frame 16 slots 8 stack 16
f:
    addi sp, sp, -16
    sd   ra, 8(sp)
    li   a1, 8
    jal  ra, sum
    ld   ra, 8(sp)
    addi sp, sp, 16
    ret
