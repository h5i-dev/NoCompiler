# Writing through malloc's result without the null check: the capability is conditional.
#! expect no_null_check: reject mem-bounds
    .text
#: unsafe fn malloc [n] in a0: int(n) borrow Heap where 0 ≤ n < 2^64 out a0: int(p) give p ≠ 0 ⇒ p ↦ bytes[n] rw heap where 0 ≤ p < 2^64, 16 ∣ p stack 64
#: fn no_null_check [] borrow Heap frame 16 slots 8 out a0: int stack 80
no_null_check:
    addi sp, sp, -16
    sd   ra, 8(sp)
    addi a0, zero, 32
    jal  ra, malloc
    sd   zero, 0(a0)
    ld   ra, 8(sp)
    addi sp, sp, 16
    jalr zero, 0(ra)
