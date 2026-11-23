# a signed check lets a negative index through: s[i] is not provably in range
#! expect get: reject mem-bounds
#: fn get [ρ, n, i] in a0: int(ρ), a1: int(n), a2: int(i) borrow ρ ↦ bytes[n] ro out a0: int stack 0
get:
    bge  a2, a1, oob
    add  a0, a0, a2
    lbu  a0, 0(a0)
    ret
oob:
    li   a0, -1
    ret
