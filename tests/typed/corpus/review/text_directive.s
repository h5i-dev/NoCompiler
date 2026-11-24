# From the independent soundness review (2026-11-23); accepted before I33.
#! expect f: reject syntax
#: fn f
#:   out a0: int(5)
#:   stack 0
    .text
    .globl f
f:
    li a0, 5
    .uleb128 0x13     # one byte the checker does not see...
    ret
