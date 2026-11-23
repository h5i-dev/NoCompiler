# no alignment fact for ρ: the 8-byte load is not provably aligned
#! expect sum: reject mem-bounds
#: fn sum [ρ, n] in a0: int(ρ), a1: int(n) borrow ρ ↦ bytes[8n] ro out a0: int stack 0
sum:
    li   a2, 0
    beqz a1, done
loop: #: inv [m] a0: int(ρ + 8n − 8m), a1: int(m), a2: int where 1 ≤ m ≤ n decreases m
    ld   a3, 0(a0)
    add  a2, a3, a2
    addi a1, a1, -1
    addi a0, a0, 8
    bnez a1, loop
done:
    mv   a0, a2
    ret
