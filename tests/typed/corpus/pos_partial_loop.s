# a partial function may loop without a measure
#! expect count: accept
#: partial fn count [n] in a0: int(n) stack 0
count:
loop: #: inv a0: int
    addi a0, a0, -1
    bnez a0, loop
    ret
