# From the independent soundness review (2026-11-23); accepted before I33.
#! expect g: accept
#! expect f: reject call-cap
# g believes n >= 8 because the clause has a field at 0 (cap facts: 0 + 8 <= n).
#: fn g [q, n, x]
#:   in a0: int(q), a1: int(n)
#:   borrow q ↦ bytes[n] rw {0: int(x)} -> {}
#:   where 8 ∣ n
#:   stack 0
    .text
g:
    add a2, a0, a1
    sd zero, -8(a2)        # address q + n - 8
    ret

# f lends p ↦ bytes[0] (n = 0) with the field of its own capability at p:
# g writes p - 8, outside every capability f holds.
#: fn f [p]
#:   in a0: int(p)
#:   borrow p ↦ bytes[8] rw
#:   where 8 ∣ p
#:   stack 16
#:   frame 16 slots 0
f:
    addi sp, sp, -16
    sd ra, 0(sp)
    sd zero, 0(a0)
    li a1, 0
    call g
    ld ra, 0(sp)
    addi sp, sp, 16
    ret
