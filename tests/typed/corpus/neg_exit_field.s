# The exit field promises the word is 1, the function writes 2.
#! expect set_one: reject ret-borrow
#: fn set_one [p] in a0: int(p) borrow p ↦ bytes[8] rw -> {0: int(1)} where 8 ∣ p stack 0
set_one:
    li   a1, 2
    sd   a1, 0(a0)
    ret
