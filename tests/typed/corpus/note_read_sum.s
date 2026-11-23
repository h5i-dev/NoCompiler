# The note's stack buffer + call example (docs/Tab 1.md, スタック上のバッファと呼出し).
# The note's prose declares slot 72 = ra and [0, 64) address-taken; here that is the
# signature's `frame` clause (I8).
#! expect sum_bytes: assumed
#! expect read_sum: reject cfg
# As written in the note, `fail` jumps back to `out`: a backward edge to a label that is
# not a loop head, which S2 forbids (the proof's S2 too). See note_read_sum_fwd.s.
    .text
#: unsafe fn sum_bytes [ρ, n]
#:   in a0: int(ρ), a1: int(n)   borrow ρ ↦ bytes[n] ro   out a0: int   stack 0

#: fn read_sum []
#:   frame 80 slots 72 addr [0, 64)
#:   out a0: int   stack 80
    .globl read_sum
read_sum:
    addi sp, sp, -80
    sd   ra, 72(sp)
    addi a1, sp, 0
    addi a0, zero, 0
    addi a2, zero, 64
    addi a7, zero, 63
    ecall
    blt  a0, zero, fail
    addi a1, a0, 0
    addi a0, sp, 0
    jal  ra, sum_bytes
out:
    ld   ra, 72(sp)
    addi sp, sp, 80
    jalr zero, 0(ra)
fail:
    addi a0, zero, 0
    jal  zero, out
