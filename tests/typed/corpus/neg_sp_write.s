#! expect f: reject stack-shape
#: fn f [] stack 0
f:
    mv   sp, a0
    ret
