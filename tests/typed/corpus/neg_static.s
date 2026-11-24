#! expect f: reject static-data
#: fn f [] stack 0
f:
    auipc a0, 0
    ret
