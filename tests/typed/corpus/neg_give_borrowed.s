# gives away a block it only borrowed
#! expect f: reject ret-give
#: fn f [p, n] in a0: int(p) borrow p ↦ bytes[n] rw out a0: int(p) give p ↦ bytes[n] rw stack 0
f:
    ret
