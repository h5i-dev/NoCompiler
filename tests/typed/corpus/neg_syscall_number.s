#! expect f: reject syscall
#: fn f [] stack 0
f:
    li   a7, 57
    ecall
    ret
