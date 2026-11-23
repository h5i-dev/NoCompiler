import LPS.Common.PropExec3

/-!
# LPS `theories/Common/PropExec.v` (f1006fe8), part 4: generic and per-instruction ALU step lemmas

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Common/PropExec.v` at f1006fe8, lines 1031-1612: the generic step lemmas (`step_opimm_gen`
.. `step_branch_ft_gen`) and the per-instruction lemmas for the integer, RV64 word and M instructions.
Conventions as in `PropExec1.lean`. The Rocq section `WithFP2` (`Context {fx : FPState}`) and the
leading `forall segs regs pc mem rom w` of every lemma are the `variable`s below, in that order.
The Ltac `step_pipeline` (PropExec.v:1033) is not ported: its role is played by the local `step_simp`
macro (a `simp only` over the same definitions) in the proofs of the generic lemmas.
Added: `rget_getr` (the core's `rget` on the state's register file is `getr`).
-/

namespace LPS
open RiscvSemantics instr aluop mulop branch_cond msize core

theorem rget_getr (regs fregs : bvmap 5 word) (pc : word) (fcsr : bv 32) (resv : Option word) (r : reg) :
    rget (Core regs fregs pc fcsr resv) r = getr regs r := by
  unfold rget getr; rw [bv_eqb0_is_x0]; rfl

/-- The pipeline: unfold `step` down to the effect tree's interpretation, at a fetched, decoded word. -/
local macro "step_simp" : tactic => `(tactic| simp only [RiscvSemantics.step, step_accesses, ms_pc, mkst,
  decode_exec_accesses, exec, interp_eff_accesses, drop_access_report, rget_getr, with_pc, b_npc4,
  load_val, width_bytes, ov_rdn, b_addsext, Bool.false_eq_true, ↓reduceIte, *])

/-- Close `rset rd v c` against `if bv_eqb rd 0 then regs else regupd regs rd v`. -/
local macro "rd_close" rd:term : tactic =>
  `(tactic| (unfold rset regupd; rw [bv_eqb0_is_x0]; cases is_x0 $rd <;> rfl))

variable [FPState] (segs : List Segment) (regs : bvmap 5 word) (pc : word) (mem rom : word → Option byte)
  (w : bv 32)

/-! ## Generic step lemmas (PropExec.v:1053-1220) -/

theorem step_opimm_gen (op : aluop) (rd rs : reg) (imm : bv 12)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (OpImm op rd rs imm, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (alu64 op (getr regs rs) (sext 64 imm)))
      (v_addi pc 4) mem rom) := by
  step_simp; rd_close rd

theorem step_shiftimm_gen (op : aluop) (rd rs : reg) (sh : bv 6)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (ShiftImm op rd rs sh, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (alu64 op (getr regs rs) (zext 64 sh)))
      (v_addi pc 4) mem rom) := by
  step_simp; rd_close rd

theorem step_op_gen (op : aluop) (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (Op op rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (alu64 op (getr regs rs1) (getr regs rs2)))
      (v_addi pc 4) mem rom) := by
  step_simp; rd_close rd

theorem step_opimm32_gen (rd rs : reg) (imm : bv 12)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (OpImm32 rd rs imm, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (sext 64 (alu32 ALU_ADD (low32 (getr regs rs)) (sext 32 imm))))
      (v_addi pc 4) mem rom) := by
  step_simp; rd_close rd

theorem step_shiftimm32_gen (op : aluop) (rd rs : reg) (sh : bv 5)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (ShiftImm32 op rd rs sh, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (sext 64 (alu32 op (low32 (getr regs rs)) (zext 32 sh))))
      (v_addi pc 4) mem rom) := by
  step_simp; rd_close rd

theorem step_op32_gen (op : aluop) (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (Op32 op rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (sext 64 (alu32 op (low32 (getr regs rs1)) (low32 (getr regs rs2)))))
      (v_addi pc 4) mem rom) := by
  step_simp; rd_close rd

theorem step_mul_gen (op : mulop) (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (instr.Mul op rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (mul_div op (getr regs rs1) (getr regs rs2)))
      (v_addi pc 4) mem rom) := by
  step_simp; rd_close rd

theorem step_mul32_gen (op : mulop) (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (Mul32 op rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (sext 64 (mul_div op (low32 (getr regs rs1)) (low32 (getr regs rs2)))))
      (v_addi pc 4) mem rom) := by
  step_simp; rd_close rd

/-- Generic branch step lemmas: taken and fall-through. -/
theorem step_branch_tk_gen (c : branch_cond) (rs1 rs2 : reg) (imm : bv 13)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (Branch c rs1 rs2 imm, 4))
    (Hc : branch_taken c (getr regs rs1) (getr regs rs2) = true) :
    RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst regs (btgt pc (bv_signed imm)) mem rom) := by
  step_simp; rfl

theorem step_branch_ft_gen (c : branch_cond) (rs1 rs2 : reg) (imm : bv 13)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (Branch c rs1 rs2 imm, 4))
    (Hc : branch_taken c (getr regs rs1) (getr regs rs2) = false) :
    RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst regs (v_addi pc 4) mem rom) := by
  step_simp

/-! ## Per-instruction step lemmas (PropExec.v:1220-1612) -/

theorem step_addi (rd rs : reg) (imm : bv 12)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (OpImm ALU_ADD rd rs imm, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_addi (getr regs rs) (bv_signed imm))) (v_addi pc 4) mem rom) := by
  rw [step_opimm_gen segs regs pc mem rom w _ rd rs imm Hfetch Hecall Hdecode, alu_addi]

theorem step_andi (rd rs : reg) (imm : bv 12)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (OpImm ALU_AND rd rs imm, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_andi (getr regs rs) (bv_signed imm))) (v_addi pc 4) mem rom) := by
  rw [step_opimm_gen segs regs pc mem rom w _ rd rs imm Hfetch Hecall Hdecode, alu_andi]

theorem step_ori (rd rs : reg) (imm : bv 12)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (OpImm ALU_OR rd rs imm, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_ori (getr regs rs) (bv_signed imm))) (v_addi pc 4) mem rom) := by
  rw [step_opimm_gen segs regs pc mem rom w _ rd rs imm Hfetch Hecall Hdecode, alu_ori]

theorem step_xori (rd rs : reg) (imm : bv 12)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (OpImm ALU_XOR rd rs imm, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_xori (getr regs rs) (bv_signed imm))) (v_addi pc 4) mem rom) := by
  rw [step_opimm_gen segs regs pc mem rom w _ rd rs imm Hfetch Hecall Hdecode, alu_xori]

theorem step_sltiu (rd rs : reg) (imm : bv 12)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (OpImm ALU_SLTU rd rs imm, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_sltiu (getr regs rs) (bv_signed imm))) (v_addi pc 4) mem rom) := by
  rw [step_opimm_gen segs regs pc mem rom w _ rd rs imm Hfetch Hecall Hdecode, alu_sltiu]

theorem step_slti (rd rs : reg) (imm : bv 12)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (OpImm ALU_SLT rd rs imm, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_slti (getr regs rs) (bv_signed imm))) (v_addi pc 4) mem rom) := by
  rw [step_opimm_gen segs regs pc mem rom w _ rd rs imm Hfetch Hecall Hdecode, alu_slti]

theorem step_slli (rd rs : reg) (sh : bv 6)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (ShiftImm ALU_SLL rd rs sh, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_slli (getr regs rs) (bv_unsigned sh))) (v_addi pc 4) mem rom) := by
  rw [step_shiftimm_gen segs regs pc mem rom w _ rd rs sh Hfetch Hecall Hdecode, alu_slli]

theorem step_srli (rd rs : reg) (sh : bv 6)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (ShiftImm ALU_SRL rd rs sh, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_srli (getr regs rs) (bv_unsigned sh))) (v_addi pc 4) mem rom) := by
  rw [step_shiftimm_gen segs regs pc mem rom w _ rd rs sh Hfetch Hecall Hdecode, alu_srli]

theorem step_srai (rd rs : reg) (sh : bv 6)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (ShiftImm ALU_SRA rd rs sh, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_srai (getr regs rs) (bv_unsigned sh))) (v_addi pc 4) mem rom) := by
  rw [step_shiftimm_gen segs regs pc mem rom w _ rd rs sh Hfetch Hecall Hdecode, alu_srai]

theorem step_add (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (Op ALU_ADD rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_add (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom) := by
  rw [step_op_gen segs regs pc mem rom w _ rd rs1 rs2 Hfetch Hecall Hdecode, alu_add]

theorem step_sub (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (Op ALU_SUB rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_sub (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom) := by
  rw [step_op_gen segs regs pc mem rom w _ rd rs1 rs2 Hfetch Hecall Hdecode, alu_sub]

theorem step_slt (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (Op ALU_SLT rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_slt (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom) := by
  rw [step_op_gen segs regs pc mem rom w _ rd rs1 rs2 Hfetch Hecall Hdecode, alu_slt]

theorem step_sltu (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (Op ALU_SLTU rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_sltu (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom) := by
  rw [step_op_gen segs regs pc mem rom w _ rd rs1 rs2 Hfetch Hecall Hdecode, alu_sltu]

theorem step_and (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (Op ALU_AND rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_and (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom) := by
  rw [step_op_gen segs regs pc mem rom w _ rd rs1 rs2 Hfetch Hecall Hdecode, alu_and]

theorem step_or (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (Op ALU_OR rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_or (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom) := by
  rw [step_op_gen segs regs pc mem rom w _ rd rs1 rs2 Hfetch Hecall Hdecode, alu_or]

theorem step_xor (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (Op ALU_XOR rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_xor (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom) := by
  rw [step_op_gen segs regs pc mem rom w _ rd rs1 rs2 Hfetch Hecall Hdecode, alu_xor]

theorem step_sll (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (Op ALU_SLL rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_sll (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom) := by
  rw [step_op_gen segs regs pc mem rom w _ rd rs1 rs2 Hfetch Hecall Hdecode, alu_sll]

theorem step_srl (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (Op ALU_SRL rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_srl (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom) := by
  rw [step_op_gen segs regs pc mem rom w _ rd rs1 rs2 Hfetch Hecall Hdecode, alu_srl]

theorem step_sra (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (Op ALU_SRA rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_sra (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom) := by
  rw [step_op_gen segs regs pc mem rom w _ rd rs1 rs2 Hfetch Hecall Hdecode, alu_sra]

theorem step_addiw (rd rs : reg) (imm : bv 12)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (OpImm32 rd rs imm, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_addiw (getr regs rs) (bv_signed imm))) (v_addi pc 4) mem rom) := by
  rw [step_opimm32_gen segs regs pc mem rom w rd rs imm Hfetch Hecall Hdecode, w_addiw]

theorem step_slliw (rd rs : reg) (sh : bv 5)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (ShiftImm32 ALU_SLL rd rs sh, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_slliw (getr regs rs) (bv_unsigned sh))) (v_addi pc 4) mem rom) := by
  rw [step_shiftimm32_gen segs regs pc mem rom w _ rd rs sh Hfetch Hecall Hdecode, w_slliw]

theorem step_srliw (rd rs : reg) (sh : bv 5)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (ShiftImm32 ALU_SRL rd rs sh, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_srliw (getr regs rs) (bv_unsigned sh))) (v_addi pc 4) mem rom) := by
  rw [step_shiftimm32_gen segs regs pc mem rom w _ rd rs sh Hfetch Hecall Hdecode, w_srliw]

theorem step_sraiw (rd rs : reg) (sh : bv 5)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (ShiftImm32 ALU_SRA rd rs sh, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_sraiw (getr regs rs) (bv_unsigned sh))) (v_addi pc 4) mem rom) := by
  rw [step_shiftimm32_gen segs regs pc mem rom w _ rd rs sh Hfetch Hecall Hdecode, w_sraiw]

theorem step_addw (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (Op32 ALU_ADD rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_addw (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom) := by
  rw [step_op32_gen segs regs pc mem rom w _ rd rs1 rs2 Hfetch Hecall Hdecode, w_addw]

theorem step_subw (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (Op32 ALU_SUB rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_subw (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom) := by
  rw [step_op32_gen segs regs pc mem rom w _ rd rs1 rs2 Hfetch Hecall Hdecode, w_subw]

theorem step_sllw (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (Op32 ALU_SLL rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_sllw (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom) := by
  rw [step_op32_gen segs regs pc mem rom w _ rd rs1 rs2 Hfetch Hecall Hdecode, w_sllw]

theorem step_srlw (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (Op32 ALU_SRL rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_srlw (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom) := by
  rw [step_op32_gen segs regs pc mem rom w _ rd rs1 rs2 Hfetch Hecall Hdecode, w_srlw]

theorem step_sraw (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (Op32 ALU_SRA rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_sraw (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom) := by
  rw [step_op32_gen segs regs pc mem rom w _ rd rs1 rs2 Hfetch Hecall Hdecode, w_sraw]

theorem step_mul (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (instr.Mul M_MUL rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_mul (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom) := by
  rw [step_mul_gen segs regs pc mem rom w _ rd rs1 rs2 Hfetch Hecall Hdecode, m_mul]

theorem step_mulh (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (instr.Mul M_MULH rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_mulh (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom) := by
  rw [step_mul_gen segs regs pc mem rom w _ rd rs1 rs2 Hfetch Hecall Hdecode, m_mulh]

theorem step_mulhsu (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (instr.Mul M_MULHSU rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_mulhsu (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom) := by
  rw [step_mul_gen segs regs pc mem rom w _ rd rs1 rs2 Hfetch Hecall Hdecode, m_mulhsu]

theorem step_mulhu (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (instr.Mul M_MULHU rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_mulhu (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom) := by
  rw [step_mul_gen segs regs pc mem rom w _ rd rs1 rs2 Hfetch Hecall Hdecode, m_mulhu]

theorem step_div (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (instr.Mul M_DIV rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_div (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom) := by
  rw [step_mul_gen segs regs pc mem rom w _ rd rs1 rs2 Hfetch Hecall Hdecode, m_div]

theorem step_rem (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (instr.Mul M_REM rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_rem (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom) := by
  rw [step_mul_gen segs regs pc mem rom w _ rd rs1 rs2 Hfetch Hecall Hdecode, m_rem]

theorem step_mulw (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (Mul32 M_MUL rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_mulw (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom) := by
  rw [step_mul32_gen segs regs pc mem rom w _ rd rs1 rs2 Hfetch Hecall Hdecode, w_mulw]

theorem step_divw (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (Mul32 M_DIV rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_divw (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom) := by
  rw [step_mul32_gen segs regs pc mem rom w _ rd rs1 rs2 Hfetch Hecall Hdecode, w_divw]

theorem step_divuw (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (Mul32 M_DIVU rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_divuw (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom) := by
  rw [step_mul32_gen segs regs pc mem rom w _ rd rs1 rs2 Hfetch Hecall Hdecode, w_divuw]

theorem step_remw (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (Mul32 M_REM rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_remw (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom) := by
  rw [step_mul32_gen segs regs pc mem rom w _ rd rs1 rs2 Hfetch Hecall Hdecode, w_remw]

theorem step_remuw (rd rs1 rs2 : reg)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (Mul32 M_REMU rd rs1 rs2, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_remuw (getr regs rs1) (getr regs rs2))) (v_addi pc 4) mem rom) := by
  rw [step_mul32_gen segs regs pc mem rom w _ rd rs1 rs2 Hfetch Hecall Hdecode, w_remuw]

end LPS
