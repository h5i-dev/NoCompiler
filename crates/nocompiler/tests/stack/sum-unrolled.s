; sum-bytewise.s unrolled by two (one exit per compared byte): B for tests/treediff.rs
func sum
  addi a5, zero, 1
  block $b0
    block $b1
      block $b3
        loop $l2
          bgeu a5, a2, $b3
          lbu a3, 0(a0)
          lbu a4, 0(a1)
          bne a3, a4, $b0
          lbu a3, 1(a0)
          lbu a4, 1(a1)
          bne a3, a4, $b0
          addi a2, a2, -2
          addi a1, a1, 2
          addi a0, a0, 2
          j $l2
        end
      end
      beq a2, zero, $b1
      lbu a3, 0(a0)
      lbu a4, 0(a1)
      bne a3, a4, $b0
    end
    addi a0, zero, 0
    ret
  end
  sub a0, a3, a4
  ret
