# The note's malloc/free contracts (docs/Tab 1.md, malloc と free の契約) and a safe
# caller that allocates, writes, frees.
#! expect malloc: assumed
#! expect free: assumed
#! expect use_heap: accept
    .text
#: unsafe fn malloc [n]
#:   in     a0: int(n)
#:   borrow Heap
#:   where  0 ≤ n < 2^64
#:   out    a0: int(p)
#:   give   p ≠ 0 ⇒ p ↦ bytes[n] rw heap
#:   where  0 ≤ p < 2^64, 16 ∣ p
#:   stack  64

#: unsafe fn free [p, n]
#:   in     a0: int(p)
#:   take   p ↦ bytes[n] rw heap
#:   borrow Heap
#:   stack  64

#: fn use_heap []
#:   borrow Heap
#:   frame 16 slots 0, 8
#:   out a0: int
#:   stack 80
use_heap:
    addi sp, sp, -16
    sd   ra, 8(sp)
    sd   s1, 0(sp)
    addi a0, zero, 32
    jal  ra, malloc
    beq  a0, zero, oom
    addi s1, a0, 0
    sd   zero, 0(s1)
    sd   zero, 24(s1)
    addi a0, s1, 0
    jal  ra, free
    addi a0, zero, 0
    jal  zero, out
oom:
    addi a0, zero, -1
out:
    ld   s1, 0(sp)
    ld   ra, 8(sp)
    addi sp, sp, 16
    jalr zero, 0(ra)
