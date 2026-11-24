# Use after free: the note's example, last line. s1 still holds p, but no capability.
#! expect use_after_free: reject mem-bounds
    .text
#: unsafe fn malloc [n] in a0: int(n) borrow Heap where 0 ≤ n < 2^64 out a0: int(p) give p ≠ 0 ⇒ p ↦ bytes[n] rw heap where 0 ≤ p < 2^64, 16 ∣ p stack 64
#: unsafe fn free [p, n] in a0: int(p) take p ↦ bytes[n] rw heap borrow Heap stack 64
#: fn use_after_free [] borrow Heap frame 16 slots 0, 8 out a0: int stack 80
use_after_free:
    addi sp, sp, -16
    sd   ra, 8(sp)
    sd   s1, 0(sp)
    addi a0, zero, 32
    jal  ra, malloc
    beq  a0, zero, oom
    addi s1, a0, 0
    sd   zero, 0(s1)
    addi a0, s1, 0
    jal  ra, free
    ld   a1, 0(s1)
oom:
    ld   s1, 0(sp)
    ld   ra, 8(sp)
    addi sp, sp, 16
    jalr zero, 0(ra)
