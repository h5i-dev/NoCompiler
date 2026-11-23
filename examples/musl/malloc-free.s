# musl 1.2.5 mallocng malloc/free: contracts only.
# The bodies do not compile with the trial flags (-march=rv64im_zba_zbb): arch/riscv64/atomic_arch.h
# uses lr.w/sc.w/lr.d/sc.d inline asm, which needs the A extension, outside the machine model.
# They also use brk/mmap/munmap/madvise syscalls, outside the environment's four (63, 64, 93, 94).
# So in the ledger they can only be "external" (note, "機械モデルの外にあるコード"): the contract
# is part of the environment model, not something to prove. The contracts are the note's.
#! expect malloc: external
#! expect free: external
#: extern fn malloc [n]
#:   in     a0: int(n)
#:   borrow Heap
#:   where  0 <= n < 2^64
#:   out    a0: int(p)
#:   give   p != 0 => p |-> bytes[n] rw heap
#:   where  0 <= p < 2^64, 16 | p
#: extern fn free [p, n]
#:   in     a0: int(p)
#:   take   p |-> bytes[n] rw heap
#:   borrow Heap
# Not expressible in v0 with these contracts: free(NULL) (allowed in C) needs a take that is
# conditional on p != 0; v0 has conditional give only.
