#! expect g: assumed
#! expect f: reject ret-preserved
#: unsafe fn g [] stack 0
#: fn f [] stack 0
f:
    jal  ra, g
    ret
