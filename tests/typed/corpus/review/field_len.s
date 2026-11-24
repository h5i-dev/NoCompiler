# From the independent soundness review (2026-11-23); accepted before I33.
#! expect g: accept
#! expect f: reject call-cap
#: fn g [q, n, x]
#:   in a0: int(q), a1: int(n)
#:   borrow q ↦ bytes[n] rw {0: int(x)} -> {}
#:   stack 0
    .text
g:
    sd zero, 0(a0)
    ret

#: fn f [p]
#:   in a0: int(p)
#:   borrow p ↦ bytes[8] rw
#:   where  8 ∣ p
#:   out a0: int(5)
#:   stack 16
#:   frame 16 slots 0, 8
f:
    addi sp, sp, -16
    sd ra, 0(sp)
    sd a0, 8(sp)
    li a1, 5
    sd a1, 0(a0)
    li a1, 0
    call g
    ld a0, 8(sp)
    ld a0, 0(a0)
    ld ra, 0(sp)
    addi sp, sp, 16
    ret
