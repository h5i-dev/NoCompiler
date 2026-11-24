# The head claims m ≤ 10 but the loop runs while m < 20: the back edge breaks the
# invariant. (Regression test: the checker once skipped the head's own constraint on back
# edges because the edge state inherits it by identity.)
#! expect f: reject loop-inv
#: fn f [] out a0: int stack 0
f:
    li   a0, 0
loop: #: inv [m] a0: int(m) where 0 ≤ m ≤ 10 decreases 20 − m
    addi a0, a0, 1
    li   t0, 20
    bltu a0, t0, loop
    ret
