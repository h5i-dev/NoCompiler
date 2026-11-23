# The note's `parse` signature (fields): a struct {ptr, len} and its buffer.
#! expect first_byte: accept
#: fn first_byte [ρ, β, n]
#:   in     a0: int(ρ)
#:   borrow ρ ↦ bytes[16] ro {0: int(β), 8: int(n)}
#:   borrow β ↦ bytes[n] ro
#:   where  8 ∣ ρ
#:   out    a0: int
#:   stack  0
first_byte:
    ld   a1, 0(a0)
    ld   a2, 8(a0)
    beqz a2, empty
    lbu  a0, 0(a1)
    ret
empty:
    li   a0, -1
    ret
