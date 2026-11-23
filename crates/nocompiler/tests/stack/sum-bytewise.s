; rustc's bcmp (examples/refine/targets, compiler-builtins), as `sum`: A for tests/treediff.rs

func sum
  block $b0
    block $b1
      beq a2, zero, $b1
      loop $l2
        lbu a3, 0(a0)
        lbu a4, 0(a1)
        bne a3, a4, $b0
        addi a2, a2, -1
        addi a1, a1, 1
        addi a0, a0, 1
        bne a2, zero, $l2
      end
    end
    addi a0, zero, 0
    ret
  end
  sub a0, a3, a4
  ret
