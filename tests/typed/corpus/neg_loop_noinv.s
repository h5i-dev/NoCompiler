#! expect spin: reject cfg
#: fn spin [n] in a0: int(n) stack 0
spin:
    addi a0, a0, -1
    bnez a0, spin
    ret
