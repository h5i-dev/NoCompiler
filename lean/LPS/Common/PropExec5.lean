import LPS.Common.PropExec4

/-!
# LPS `theories/Common/PropExec.v` (f1006fe8), part 5: branch, jump, ecall and load step lemmas

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Common/PropExec.v` at f1006fe8, lines 1612-2002: the branch lemmas (no alignment side
conditions: the ISA model has no check), `lui`/`auipc`/`jal x0`/`jalr`/`ecall`, and the loads.
Conventions as in `PropExec4.lean` (same `variable`s; the local `step_simp`/`rd_close` macros are
repeated, being file-local).
-/

namespace LPS
open RiscvSemantics instr aluop mulop branch_cond msize core

local macro "step_simp" : tactic => `(tactic| simp only [RiscvSemantics.step, step_accesses, ms_pc, mkst,
  decode_exec_accesses, exec, interp_eff_accesses, drop_access_report, rget_getr, with_pc, b_npc4,
  load_val, width_bytes, ov_rdn, b_addsext, Bool.false_eq_true, ↓reduceIte, *])

local macro "rd_close" rd:term : tactic =>
  `(tactic| (unfold rset regupd; rw [bv_eqb0_is_x0]; cases is_x0 $rd <;> rfl))

variable [FPState] (segs : List Segment) (regs : bvmap 5 word) (pc : word) (mem rom : word → Option byte)
  (w : bv 32)

/-! ## Branches (PropExec.v:1612-1765) -/

theorem step_beq_tk (rs1 rs2 : reg) (imm : bv 13)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (Branch BC_EQ rs1 rs2 imm, 4))
    (Hc : c_eq (getr regs rs1) (getr regs rs2) = true) :
    RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst regs (btgt pc (bv_signed imm)) mem rom) := by
  apply step_branch_tk_gen segs regs pc mem rom w BC_EQ rs1 rs2 imm Hfetch Hecall Hdecode
  simp only [c_eq] at Hc; simp [branch_taken, Hc]

theorem step_beq_ft (rs1 rs2 : reg) (imm : bv 13)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (Branch BC_EQ rs1 rs2 imm, 4))
    (Hc : c_eq (getr regs rs1) (getr regs rs2) = false) :
    RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst regs (v_addi pc 4) mem rom) := by
  apply step_branch_ft_gen segs regs pc mem rom w BC_EQ rs1 rs2 imm Hfetch Hecall Hdecode
  simp only [c_eq] at Hc; simp [branch_taken, Hc]

theorem step_bne_tk (rs1 rs2 : reg) (imm : bv 13)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (Branch BC_NE rs1 rs2 imm, 4))
    (Hc : c_eq (getr regs rs1) (getr regs rs2) = false) :
    RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst regs (btgt pc (bv_signed imm)) mem rom) := by
  apply step_branch_tk_gen segs regs pc mem rom w BC_NE rs1 rs2 imm Hfetch Hecall Hdecode
  simp only [c_eq] at Hc; simp [branch_taken, Hc]

theorem step_bne_ft (rs1 rs2 : reg) (imm : bv 13)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (Branch BC_NE rs1 rs2 imm, 4))
    (Hc : c_eq (getr regs rs1) (getr regs rs2) = true) :
    RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst regs (v_addi pc 4) mem rom) := by
  apply step_branch_ft_gen segs regs pc mem rom w BC_NE rs1 rs2 imm Hfetch Hecall Hdecode
  simp only [c_eq] at Hc; simp [branch_taken, Hc]

theorem step_blt_tk (rs1 rs2 : reg) (imm : bv 13)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (Branch BC_LT rs1 rs2 imm, 4))
    (Hc : c_lts (getr regs rs1) (getr regs rs2) = true) :
    RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst regs (btgt pc (bv_signed imm)) mem rom) := by
  apply step_branch_tk_gen segs regs pc mem rom w BC_LT rs1 rs2 imm Hfetch Hecall Hdecode
  simp only [c_lts] at Hc; simp [branch_taken, Hc]

theorem step_blt_ft (rs1 rs2 : reg) (imm : bv 13)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (Branch BC_LT rs1 rs2 imm, 4))
    (Hc : c_lts (getr regs rs1) (getr regs rs2) = false) :
    RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst regs (v_addi pc 4) mem rom) := by
  apply step_branch_ft_gen segs regs pc mem rom w BC_LT rs1 rs2 imm Hfetch Hecall Hdecode
  simp only [c_lts] at Hc; simp [branch_taken, Hc]

theorem step_bge_tk (rs1 rs2 : reg) (imm : bv 13)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (Branch BC_GE rs1 rs2 imm, 4))
    (Hc : c_lts (getr regs rs1) (getr regs rs2) = false) :
    RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst regs (btgt pc (bv_signed imm)) mem rom) := by
  apply step_branch_tk_gen segs regs pc mem rom w BC_GE rs1 rs2 imm Hfetch Hecall Hdecode
  simp only [c_lts] at Hc; simp [branch_taken, Hc]

theorem step_bge_ft (rs1 rs2 : reg) (imm : bv 13)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (Branch BC_GE rs1 rs2 imm, 4))
    (Hc : c_lts (getr regs rs1) (getr regs rs2) = true) :
    RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst regs (v_addi pc 4) mem rom) := by
  apply step_branch_ft_gen segs regs pc mem rom w BC_GE rs1 rs2 imm Hfetch Hecall Hdecode
  simp only [c_lts] at Hc; simp [branch_taken, Hc]

theorem step_bltu_tk (rs1 rs2 : reg) (imm : bv 13)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (Branch BC_LTU rs1 rs2 imm, 4))
    (Hc : c_ltu (getr regs rs1) (getr regs rs2) = true) :
    RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst regs (btgt pc (bv_signed imm)) mem rom) := by
  apply step_branch_tk_gen segs regs pc mem rom w BC_LTU rs1 rs2 imm Hfetch Hecall Hdecode
  simp only [c_ltu] at Hc; simp [branch_taken, Hc]

theorem step_bltu_ft (rs1 rs2 : reg) (imm : bv 13)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (Branch BC_LTU rs1 rs2 imm, 4))
    (Hc : c_ltu (getr regs rs1) (getr regs rs2) = false) :
    RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst regs (v_addi pc 4) mem rom) := by
  apply step_branch_ft_gen segs regs pc mem rom w BC_LTU rs1 rs2 imm Hfetch Hecall Hdecode
  simp only [c_ltu] at Hc; simp [branch_taken, Hc]

theorem step_bgeu_tk (rs1 rs2 : reg) (imm : bv 13)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (Branch BC_GEU rs1 rs2 imm, 4))
    (Hc : c_ltu (getr regs rs1) (getr regs rs2) = false) :
    RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst regs (btgt pc (bv_signed imm)) mem rom) := by
  apply step_branch_tk_gen segs regs pc mem rom w BC_GEU rs1 rs2 imm Hfetch Hecall Hdecode
  simp only [c_ltu] at Hc; simp [branch_taken, Hc]

theorem step_bgeu_ft (rs1 rs2 : reg) (imm : bv 13)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (Branch BC_GEU rs1 rs2 imm, 4))
    (Hc : c_ltu (getr regs rs1) (getr regs rs2) = true) :
    RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst regs (v_addi pc 4) mem rom) := by
  apply step_branch_ft_gen segs regs pc mem rom w BC_GEU rs1 rs2 imm Hfetch Hecall Hdecode
  simp only [c_ltu] at Hc; simp [branch_taken, Hc]

/-! ## Upper immediates, jumps, ecall (PropExec.v:1766-1838) -/

/-- `imm` is the raw 20-bit U-immediate; the value shape takes the shifted signed immediate. -/
theorem step_lui (rd : reg) (imm : bv 20)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (Lui rd imm, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_lui (Z.shiftl (bv_signed imm) 12)))
      (v_addi pc 4) mem rom) := by
  step_simp; rw [b_lui]; rd_close rd

theorem step_auipc (rd : reg) (imm : bv 20)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (Auipc rd imm, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_auipc pc (Z.shiftl (bv_signed imm) 12)))
      (v_addi pc 4) mem rom) := by
  step_simp; rw [← b_addsext, b_auipc]; rd_close rd

theorem step_jal_x0 (imm : bv 21)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (Jal 0 imm, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst regs (btgt pc (bv_signed imm)) mem rom) := by
  step_simp; simp only [rset, is_x0_0, ↓reduceIte]; rfl

/-- General Jalr: rd := pc + 4 (unless rd = x0), jump to the masked target. -/
theorem step_jalr_gen (rd rs1 : reg) (imm : bv 12)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (Jalr rd rs1 imm, 4)) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_addi pc 4))
      (jalr_tgt (getr regs rs1) (bv_signed imm)) mem rom) := by
  step_simp; rw [← b_addsext, w1, b_jalr]; rd_close rd

theorem step_ecall (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = true) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk { ms_regs := regs, ms_fregs := fp_regs, ms_pc_val := pc, ms_svc_pending := some (getr regs 17),
                ms_resv := none, ms_fcsr := fp_csr, ms_mem := mem, ms_rom := rom } := by
  step_simp; rfl

/-! ## Loads (PropExec.v:1840-2002) -/

theorem step_lbu (rd rs : reg) (imm : bv 12) (b : byte)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (Load SZ1 false rd rs imm, 4))
    (Hread : rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 1 = some [b]) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 (bv_unsigned b))) (v_addi pc 4) mem rom) := by
  have Hz : zext 64 (bv_extract 0 8 (le_bytes_to_word [b])) = Z_to_bv 64 (bv_unsigned b) := by
    rw [le_word_1, b_extract8_id]
    apply bv_eq; unfold zext
    rw [bv_zero_extend_unsigned 64 b (by decide),
      Z_to_bv_small 64 _ (u8_range b).1 (by have := (u8_range b).2; rw [bv_modulus_64]; omega)]
  step_simp; rd_close rd

theorem step_lb (rd rs : reg) (imm : bv 12) (b : byte)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (Load SZ1 true rd rs imm, 4))
    (Hread : rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 1 = some [b]) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_lb b)) (v_addi pc 4) mem rom) := by
  step_simp; rw [b_lb_val]; rd_close rd

theorem step_lh (rd rs : reg) (imm : bv 12) (bs : List byte) (v : word)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (Load SZ2 true rd rs imm, 4))
    (Hread : rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 2 = some bs)
    (Hv : bytes_le_to_Z bs = bv_unsigned v) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_lh v)) (v_addi pc 4) mem rom) := by
  step_simp; rw [le_word_v _ _ Hv, b_lh_val]; rd_close rd

omit [FPState] in
/-- A load of `k` bytes read back from `bs` fits in `8 k` bits, so the zero extension is the value. -/
theorem zext_extract_read (segs : List Segment) (mem : word → Option byte) (a : word) (k : Nat) (bs : List byte)
    (v : word) (Hread : rdn segs mem a k = some bs) (Hv : bytes_le_to_Z bs = bv_unsigned v) (hk : 8 * k ≤ 64) :
    zext 64 (bv_extract 0 (8 * k) v) = v := by
  have Hlen := rdn_length _ _ _ _ _ Hread
  have Hb := bytes_le_to_Z_bound bs
  have Hnn := bytes_le_to_Z_nonneg bs
  rw [Hlen, Hv] at Hb; rw [Hv] at Hnn
  apply bv_eq; unfold zext
  rw [bv_zero_extend_unsigned 64 _ hk, bv_extract0_unsigned]
  exact bv_wrap_small _ _ Hnn (by unfold bv_modulus; push_cast; exact Hb)

theorem step_lhu (rd rs : reg) (imm : bv 12) (bs : List byte) (v : word)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (Load SZ2 false rd rs imm, 4))
    (Hread : rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 2 = some bs)
    (Hv : bytes_le_to_Z bs = bv_unsigned v) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd v) (v_addi pc 4) mem rom) := by
  have Hz := zext_extract_read segs mem _ 2 bs v Hread Hv (by decide)
  step_simp; rw [le_word_v _ _ Hv, Hz]; rd_close rd

theorem step_lw (rd rs : reg) (imm : bv 12) (bs : List byte) (v : word)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (Load SZ4 true rd rs imm, 4))
    (Hread : rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 4 = some bs)
    (Hv : bytes_le_to_Z bs = bv_unsigned v) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_lw v)) (v_addi pc 4) mem rom) := by
  step_simp; rw [le_word_v _ _ Hv, b_lw_val]; rd_close rd

theorem step_lwu (rd rs : reg) (imm : bv 12) (bs : List byte) (v : word)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (Load SZ4 false rd rs imm, 4))
    (Hread : rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 4 = some bs)
    (Hv : bytes_le_to_Z bs = bv_unsigned v) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd v) (v_addi pc 4) mem rom) := by
  have Hz := zext_extract_read segs mem _ 4 bs v Hread Hv (by decide)
  step_simp; rw [le_word_v _ _ Hv, Hz]; rd_close rd

theorem step_ld (rd rs : reg) (imm : bv 12) (bs : List byte) (v : word)
    (Hfetch : fetch_word segs pc = some w) (Hecall : is_ecall w = false)
    (Hdecode : decode_any w = some (Load SZ8 true rd rs imm, 4))
    (Hread : rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 8 = some bs)
    (Hv : bytes_le_to_Z bs = bv_unsigned v) :
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd v) (v_addi pc 4) mem rom) := by
  have Hz : bv_extract 0 64 v = v := bv_eq _ _ (by rw [bv_extract0_unsigned, bv_wrap_bv_unsigned])
  step_simp; rw [le_word_v _ _ Hv, Hz]; rd_close rd

end LPS
