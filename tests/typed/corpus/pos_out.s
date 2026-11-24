#! expect inc: accept
#: fn inc [n] in a0: int(n) out a0: int(n + 1) stack 0
inc:
    addi a0, a0, 1
    ret
