#! expect count: accept
#: fn count [n] in a0: int(n) where 1 ≤ n < 2^63 stack 0
count:
loop: #: inv [m] a0: int(m) where 1 ≤ m ≤ n decreases m
    addi a0, a0, -1
    bnez a0, loop
    ret
