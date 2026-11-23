#! expect zero_first: reject mem-write
#: fn zero_first [ρ] in a0: int(ρ) borrow ρ ↦ bytes[8] ro where 8 ∣ ρ stack 0
zero_first:
    sd   zero, 0(a0)
    ret
