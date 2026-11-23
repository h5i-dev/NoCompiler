# From the independent soundness review (2026-11-23); accepted before I33.
#! expect f: reject syntax
#: fn f
#:   out a0: int(7)
#:   stack 0
    .text
    .globl f
f:
    li a0, 5
    .pushsection .text.junk,"ax",@progbits
    li a0, 7
    .popsection
    ret
