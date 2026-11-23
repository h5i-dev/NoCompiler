# The note's `sum` (docs/Tab 1.md, 例 / sum).
#! expect sum: accept
    .text
#: fn sum [ρ, n]
#:   in     a0: int(ρ), a1: int(n)
#:   borrow ρ ↦ bytes[8n] ro
#:   where  8 ∣ ρ
#:   out    a0: int
#:   stack  0
    .globl sum
    .type sum,@function
sum:
    addi a2, zero, 0
    beq  a1, zero, done
loop:                    #: inv [m] a0: int(ρ + 8n − 8m), a1: int(m), a2: int
                         #:     where 1 ≤ m ≤ n   decreases m
    ld   a3, 0(a0)
    add  a2, a3, a2
    addi a1, a1, -1
    addi a0, a0, 8
    bne  a1, zero, loop
done:
    addi a0, a2, 0
    jalr zero, 0(ra)
