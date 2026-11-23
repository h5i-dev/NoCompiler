import LPS.Bridge.SimReg

/-!
# Bridge, step 3 (continued): R-type instructions, and `sim_reg`

`sim_rop`, `sim_rwop`: the RV64IM register-register instructions; `sim_reg`: every NoCompiler
instruction other than a load, a store or ECALL that has an LPS counterpart is simulated by one LPS
`exec`.
-/

namespace LPS.Bridge
open NoCompiler

theorem mul_div_mul {n : Nat} (a b : bv n) : mul_div .M_MUL a b = a * b := rfl

/-- add sub sll slt sltu xor srl sra or and, mul mulh mulhsu mulhu div divu rem remu (the Zba/Zbb
    ones: `toLPS` is `none`). -/
theorem sim_rop {s s' : State} {c : core} {j : LPS.instr} (h : RelC s c) (op : ROp) (rd rs1 rs2 : Reg)
    (hj : toLPS (.rop op rd rs1 rs2) = some j)
    (hs : NoCompiler.exec (Instr.rop op rd rs1 rs2) s = some s') :
    ∃ c', LPS.exec 4 j c = .EDone c' ∧ RelC s' c' := by
  simp only [NoCompiler.exec, Option.some.injEq] at hs
  subst hs
  cases op <;> simp only [toLPS, Option.some.injEq, reduceCtorEq] at hj <;> subst hj <;>
    refine ⟨_, rfl, ?_⟩ <;>
    simp only [evalR, alu64, alu, bv_shiftl_eq, bv_shiftr_eq, bv_ashiftr_eq, bv_and_eq, bv_or_eq, bv_xor_eq,
      mask63', bv_lts_eq, bv_ltu_eq, bool64, Z_to_bv64_one, Z_to_bv64_zero, mul_div_mul, mul_div_mulh,
      mul_div_mulhsu, mul_div_mulhu, mul_div_div, mul_div_divu, mul_div_rem, mul_div_remu, h.1 rs1,
      h.1 rs2] <;>
    exact h.next rd _

/-- addw subw sllw srlw sraw, mulw divw divuw remw remuw (the Zba/Zbb ones: `toLPS` is `none`). -/
theorem sim_rwop {s s' : State} {c : core} {j : LPS.instr} (h : RelC s c) (op : RWOp) (rd rs1 rs2 : Reg)
    (hj : toLPS (.rwop op rd rs1 rs2) = some j)
    (hs : NoCompiler.exec (Instr.rwop op rd rs1 rs2) s = some s') :
    ∃ c', LPS.exec 4 j c = .EDone c' ∧ RelC s' c' := by
  simp only [NoCompiler.exec, Option.some.injEq] at hs
  subst hs
  cases op <;> simp only [toLPS, Option.some.injEq, reduceCtorEq] at hj <;> subst hj <;>
    refine ⟨_, rfl, ?_⟩ <;>
    simp only [evalRW, w32, sext_eq, low32_eq, alu32, alu, bv_shiftl_eq, bv_shiftr_eq, bv_ashiftr_eq,
      bv_and_eq, mask31', mul_div_mul, mul_div_div, mul_div_divu, mul_div_rem, mul_div_remu, h.1 rs1,
      h.1 rs2] <;>
    exact h.next rd _

/-- The instructions that neither touch memory nor trap to the environment. -/
def Instr.regOnly : Instr → Bool
  | .load .. | .store .. | .ecall => false
  | _ => true

theorem sim_reg {s s' : State} {c : core} {i : Instr} {j : LPS.instr} (h : RelC s c)
    (hm : Instr.regOnly i = true) (hj : toLPS i = some j) (hs : NoCompiler.exec i s = some s') :
    ∃ c', LPS.exec 4 j c = .EDone c' ∧ RelC s' c' := by
  cases i with
  | lui rd imm => simp only [toLPS, Option.some.injEq] at hj; subst hj; exact sim_lui h rd imm hs
  | auipc rd imm => simp only [toLPS, Option.some.injEq] at hj; subst hj; exact sim_auipc h rd imm hs
  | jal rd off => simp only [toLPS, Option.some.injEq] at hj; subst hj; exact sim_jal h rd off hs
  | jalr rd rs1 off =>
    simp only [toLPS, Option.some.injEq] at hj; subst hj; exact sim_jalr h rd rs1 off hs
  | branch op rs1 rs2 off =>
    simp only [toLPS, Option.some.injEq] at hj; subst hj; exact sim_branch h op rs1 rs2 off hs
  | load => simp [Instr.regOnly] at hm
  | store => simp [Instr.regOnly] at hm
  | iop op rd rs1 imm =>
    simp only [toLPS, Option.some.injEq] at hj; subst hj; exact sim_iop h op rd rs1 imm hs
  | addiw rd rs1 imm =>
    simp only [toLPS, Option.some.injEq] at hj; subst hj; exact sim_addiw h rd rs1 imm hs
  | shift op rd rs1 sh => exact sim_shift h op rd rs1 sh hj hs
  | shiftw op rd rs1 sh => exact sim_shiftw h op rd rs1 sh hj hs
  | rop op rd rs1 rs2 => exact sim_rop h op rd rs1 rs2 hj hs
  | rwop op rd rs1 rs2 => exact sim_rwop h op rd rs1 rs2 hj hs
  | uop => simp [toLPS] at hj
  | ecall => simp [Instr.regOnly] at hm
  | unimp => simp [NoCompiler.exec] at hs

end LPS.Bridge
