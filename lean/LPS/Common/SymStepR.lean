import LPS.Common.SeqExec2

/-!
# LPS `theories/Common/SymStepR.v` (f1006fe8): step lemmas over a state with an arbitrary LR/SC reservation

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Common/SymStepR.v` at f1006fe8 (image-INDEPENDENT; shared proof library): the state
shape `mkstR` (`mkst` at the entry FP state with the reservation exposed), `resv_inval_w`,
`load_result`, `eff_sx`, `msize_bytes`, `amo_msize`, `amo_nbytes`, `amo_store_bytes`, and the step
lemmas `stepR_*` for the integer instructions (reservation unchanged), loads, stores (reservation
invalidated on an exact address match), `lr`, the success path of `sc`, and the AMOs.

Conventions as SeqExec1. SymStepR.v's `Local Instance asanreflect_fx := PropExec.fx0` is used only by
`mkstR_None`, which names `@mkst fx0` explicitly. Rocq's `mod` is `Z.modulo`, `Z.eqb` is `==`.

Not ported (Ltac-only, no statement): the pipeline tactic `stepR_pipeline`; the step lemmas are proved
by a local `simp only` over the same definitions (`stepR_simp`).
-/

namespace LPS
open RiscvSemantics instr aluop mulop branch_cond msize awidth core

/-- The state shape: `mkst` with the reservation exposed. -/
def mkstR (regs : bvmap 5 word) (pc : word) (mem rom : word → Option byte) (rv : Option word) : machine_state :=
  { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := pc, ms_svc_pending := none, ms_resv := rv,
    ms_fcsr := Z_to_bv 32 0, ms_mem := mem, ms_rom := rom }

theorem mkstR_None : ∀ regs pc mem rom, mkstR regs pc mem rom none = @mkst fx0 regs pc mem rom :=
  fun _ _ _ _ => rfl

theorem mkstR_svc : ∀ regs pc mem rom rv, (mkstR regs pc mem rom rv).ms_svc_pending = none :=
  fun _ _ _ _ _ => rfl

/-- What a store / AMO to address `a` does to the reservation. -/
def resv_inval_w (rv : Option word) (a : word) : Option word :=
  match rv with
  | some r => if bv_unsigned r == bv_unsigned a then none else rv
  | none => none

/-- The value a load writes back, per width/sign, as a function of the bytes read. -/
def load_result (sz : msize) (sx : Bool) (bs : List byte) : word :=
  match sz with
  | SZ1 => if sx then sext 64 (bv_extract 0 8 (le_bytes_to_word bs)) else zext 64 (bv_extract 0 8 (le_bytes_to_word bs))
  | SZ2 => if sx then sext 64 (bv_extract 0 16 (le_bytes_to_word bs)) else zext 64 (bv_extract 0 16 (le_bytes_to_word bs))
  | SZ4 => if sx then sext 64 (bv_extract 0 32 (le_bytes_to_word bs)) else zext 64 (bv_extract 0 32 (le_bytes_to_word bs))
  | SZ8 => bv_extract 0 64 (le_bytes_to_word bs)

def eff_sx (sz : msize) (sx : Bool) : Bool :=
  match sz with | SZ8 => false | _ => sx

/-- SymStepR.v's `msize_bytes` (a `nat`); `LPS.msize_bytes` is Instr.v's (a `Z`), so this one is
    `SymStepR.msize_bytes`, its Rocq qualified name. -/
def SymStepR.msize_bytes (sz : msize) : Nat :=
  match sz with | SZ1 => 1 | SZ2 => 2 | SZ4 => 4 | SZ8 => 8

/-- Atomic widths as load/store widths. -/
def amo_msize (wd : awidth) : msize := match wd with | AW => SZ4 | AD => SZ8
def amo_nbytes (wd : awidth) : Nat := match wd with | AW => 4 | AD => 8

/-- The bytes an AMO writes: `amo_val` at the operand width. -/
def amo_store_bytes (op : amoop) (wd : awidth) (bs : List byte) (src : word) : List byte :=
  match wd with
  | AW => Z_to_le_bytes 4 (bv_unsigned (amo_val op (bv_extract 0 32 (le_bytes_to_word bs)) (low32 src)))
  | AD => Z_to_le_bytes 8 (bv_unsigned (amo_val op (bv_extract 0 64 (le_bytes_to_word bs)) src))

local macro "stepR_simp" : tactic => `(tactic| simp only [RiscvSemantics.step, step_accesses, ms_pc, mkstR,
  decode_exec_accesses, exec, interp_eff_accesses, drop_access_report, rget_getr, with_pc, b_npc4,
  load_val, store_val, width_bytes, ov_rdn, b_addsext, Bool.false_eq_true, ↓reduceIte, inval_resv,
  with_resv, write_to_mem_wbytes, *])

local macro "rd_close" rd:term : tactic =>
  `(tactic| (unfold rset regupd; rw [bv_eqb0_is_x0]; cases is_x0 $rd <;> rfl))

/-! ### Integer instructions: the reservation passes through -/

theorem stepR_opimm_gen : ∀ segs regs pc mem rom rv w op (rd rs : reg) (imm : bv 12),
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (OpImm op rd rs imm, 4) →
    RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
    MachineOk (mkstR (if bv_eqb rd 0 then regs else regupd regs rd (alu64 op (getr regs rs) (sext 64 imm)))
      (v_addi pc 4) mem rom rv) := by
  intro segs regs pc mem rom rv w op rd rs imm Hf He Hd
  stepR_simp; rd_close rd

theorem stepR_shiftimm_gen : ∀ segs regs pc mem rom rv w op (rd rs : reg) (sh : bv 6),
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (ShiftImm op rd rs sh, 4) →
    RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
    MachineOk (mkstR (if bv_eqb rd 0 then regs else regupd regs rd (alu64 op (getr regs rs) (zext 64 sh)))
      (v_addi pc 4) mem rom rv) := by
  intro segs regs pc mem rom rv w op rd rs sh Hf He Hd
  stepR_simp; rd_close rd

theorem stepR_op_gen : ∀ segs regs pc mem rom rv w op (rd rs1 rs2 : reg),
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (Op op rd rs1 rs2, 4) →
    RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
    MachineOk (mkstR (if bv_eqb rd 0 then regs else regupd regs rd (alu64 op (getr regs rs1) (getr regs rs2)))
      (v_addi pc 4) mem rom rv) := by
  intro segs regs pc mem rom rv w op rd rs1 rs2 Hf He Hd
  stepR_simp; rd_close rd

theorem stepR_opimm32_gen : ∀ segs regs pc mem rom rv w (rd rs : reg) (imm : bv 12),
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (OpImm32 rd rs imm, 4) →
    RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
    MachineOk (mkstR (if bv_eqb rd 0 then regs
                      else regupd regs rd (sext 64 (alu32 ALU_ADD (low32 (getr regs rs)) (sext 32 imm))))
      (v_addi pc 4) mem rom rv) := by
  intro segs regs pc mem rom rv w rd rs imm Hf He Hd
  stepR_simp; rd_close rd

theorem stepR_shiftimm32_gen : ∀ segs regs pc mem rom rv w op (rd rs : reg) (sh : bv 5),
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (ShiftImm32 op rd rs sh, 4) →
    RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
    MachineOk (mkstR (if bv_eqb rd 0 then regs
                      else regupd regs rd (sext 64 (alu32 op (low32 (getr regs rs)) (zext 32 sh))))
      (v_addi pc 4) mem rom rv) := by
  intro segs regs pc mem rom rv w op rd rs sh Hf He Hd
  stepR_simp; rd_close rd

theorem stepR_op32_gen : ∀ segs regs pc mem rom rv w op (rd rs1 rs2 : reg),
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (Op32 op rd rs1 rs2, 4) →
    RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
    MachineOk (mkstR (if bv_eqb rd 0 then regs
                      else regupd regs rd (sext 64 (alu32 op (low32 (getr regs rs1)) (low32 (getr regs rs2)))))
      (v_addi pc 4) mem rom rv) := by
  intro segs regs pc mem rom rv w op rd rs1 rs2 Hf He Hd
  stepR_simp; rd_close rd

theorem stepR_mul_gen : ∀ segs regs pc mem rom rv w op (rd rs1 rs2 : reg),
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (instr.Mul op rd rs1 rs2, 4) →
    RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
    MachineOk (mkstR (if bv_eqb rd 0 then regs else regupd regs rd (mul_div op (getr regs rs1) (getr regs rs2)))
      (v_addi pc 4) mem rom rv) := by
  intro segs regs pc mem rom rv w op rd rs1 rs2 Hf He Hd
  stepR_simp; rd_close rd

theorem stepR_mul32_gen : ∀ segs regs pc mem rom rv w op (rd rs1 rs2 : reg),
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (Mul32 op rd rs1 rs2, 4) →
    RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
    MachineOk (mkstR (if bv_eqb rd 0 then regs
                      else regupd regs rd (sext 64 (mul_div op (low32 (getr regs rs1)) (low32 (getr regs rs2)))))
      (v_addi pc 4) mem rom rv) := by
  intro segs regs pc mem rom rv w op rd rs1 rs2 Hf He Hd
  stepR_simp; rd_close rd

theorem stepR_lui : ∀ segs regs pc mem rom rv w (rd : reg) (imm : bv 20),
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (Lui rd imm, 4) →
    RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
    MachineOk (mkstR (if bv_eqb rd 0 then regs else regupd regs rd (v_lui (Z.shiftl (bv_signed imm) 12)))
      (v_addi pc 4) mem rom rv) := by
  intro segs regs pc mem rom rv w rd imm Hf He Hd
  stepR_simp; rw [b_lui]; rd_close rd

theorem stepR_auipc : ∀ segs regs pc mem rom rv w (rd : reg) (imm : bv 20),
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (Auipc rd imm, 4) →
    RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
    MachineOk (mkstR (if bv_eqb rd 0 then regs else regupd regs rd (v_auipc pc (Z.shiftl (bv_signed imm) 12)))
      (v_addi pc 4) mem rom rv) := by
  intro segs regs pc mem rom rv w rd imm Hf He Hd
  stepR_simp; rw [← b_addsext, b_auipc]; rd_close rd

theorem stepR_jal_link : ∀ segs regs pc mem rom rv w (rd : reg) (imm : bv 21),
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (Jal rd imm, 4) →
    RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
    MachineOk (mkstR (if bv_eqb rd 0 then regs else regupd regs rd (v_addi pc 4))
      (btgt pc (bv_signed imm)) mem rom rv) := by
  intro segs regs pc mem rom rv w rd imm Hf He Hd
  stepR_simp; rd_close rd

theorem stepR_jalr : ∀ segs regs pc mem rom rv w (rd rs1 : reg) (imm : bv 12),
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (Jalr rd rs1 imm, 4) →
    RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
    MachineOk (mkstR (if bv_eqb rd 0 then regs else regupd regs rd (v_addi pc 4))
      (v_jalr (getr regs rs1) (bv_signed imm)) mem rom rv) := by
  intro segs regs pc mem rom rv w rd rs1 imm Hf He Hd
  stepR_simp; rw [← b_addsext, w1, b_jalr]; rd_close rd

theorem stepR_branch_tk_gen : ∀ segs regs pc mem rom rv w c (rs1 rs2 : reg) (imm : bv 13),
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (Branch c rs1 rs2 imm, 4) →
    branch_taken c (getr regs rs1) (getr regs rs2) = true →
    RiscvSemantics.step segs (mkstR regs pc mem rom rv) = MachineOk (mkstR regs (btgt pc (bv_signed imm)) mem rom rv) := by
  intro segs regs pc mem rom rv w c rs1 rs2 imm Hf He Hd Hc
  stepR_simp; rfl

theorem stepR_branch_ft_gen : ∀ segs regs pc mem rom rv w c (rs1 rs2 : reg) (imm : bv 13),
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (Branch c rs1 rs2 imm, 4) →
    branch_taken c (getr regs rs1) (getr regs rs2) = false →
    RiscvSemantics.step segs (mkstR regs pc mem rom rv) = MachineOk (mkstR regs (v_addi pc 4) mem rom rv) := by
  intro segs regs pc mem rom rv w c rs1 rs2 imm Hf He Hd Hc
  stepR_simp

theorem stepR_fence : ∀ segs regs pc mem rom rv w a b c d e,
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (Fence a b c d e, 4) →
    RiscvSemantics.step segs (mkstR regs pc mem rom rv) = MachineOk (mkstR regs (v_addi pc 4) mem rom rv) := by
  intro segs regs pc mem rom rv w a b c d e Hf He Hd
  stepR_simp

theorem stepR_fencei : ∀ segs regs pc mem rom rv w a b c,
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (FenceI a b c, 4) →
    RiscvSemantics.step segs (mkstR regs pc mem rom rv) = MachineOk (mkstR regs (v_addi pc 4) mem rom rv) := by
  intro segs regs pc mem rom rv w a b c Hf He Hd
  stepR_simp

/-! ### Loads and stores -/

theorem stepR_load : ∀ segs regs pc mem rom rv w sz sx (rd rs : reg) (imm : bv 12) bs,
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (Load sz sx rd rs imm, 4) →
    rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) (SymStepR.msize_bytes sz) = some bs →
    RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
    MachineOk (mkstR (if bv_eqb rd 0 then regs else regupd regs rd (load_result sz sx bs)) (v_addi pc 4) mem rom rv) := by
  intro segs regs pc mem rom rv w sz sx rd rs imm bs Hf He Hd Hread
  cases sz <;> simp only [SymStepR.msize_bytes] at Hread <;> stepR_simp <;> cases sx <;> rd_close rd

/-- Store of any width, value exposed, reservation invalidated on an exact address match. -/
theorem stepR_store : ∀ segs regs pc mem rom rv w sz (rs1 rs2 : reg) (imm : bv 12),
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (Store sz rs1 rs2 imm, 4) →
    RiscvSemantics.store_ok segs mem (v_addi (getr regs rs1) (bv_signed imm)) (SymStepR.msize_bytes sz) = true →
    RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
    MachineOk (mkstR regs (v_addi pc 4)
      (wbytes mem (v_addi (getr regs rs1) (bv_signed imm)) (word_to_le_bytes (SymStepR.msize_bytes sz) (getr regs rs2))) rom
      (resv_inval_w rv (v_addi (getr regs rs1) (bv_signed imm)))) := by
  intro segs regs pc mem rom rv w sz rs1 rs2 imm Hf He Hd Hok
  have Hsb : ∀ u : word, Z_to_le_bytes 1 (bv_unsigned (bv_extract 0 8 u)) = word_to_le_bytes 1 u := by
    intro u; unfold word_to_le_bytes; rw [bv_extract0_unsigned]; exact Z_to_le_bytes_wrap 1 8 _ (by decide)
  cases sz <;> simp only [SymStepR.msize_bytes] at Hok <;>
    stepR_simp <;> (try simp only [store_bytes_low16, store_bytes_low32]) <;>
    (cases rv with
     | none => rfl
     | some r =>
       cases h : (bv_unsigned r == bv_unsigned (v_addi (getr regs rs1) (bv_signed imm))) <;>
         simp only [resv_inval_w, h, Bool.false_eq_true, ↓reduceIte] <;> rfl)

/-! ### A extension -/

/-- LR: load (like `lw`/`ld`) and reserve the address. -/
theorem stepR_lr : ∀ segs regs pc mem rom rv w wd aq rl (rd rs : reg) bs,
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (Lr wd aq rl rd rs, 4) →
    Z.modulo (bv_unsigned (getr regs rs)) (amo_bytes wd) = 0 →
    rdn segs mem (getr regs rs) (amo_nbytes wd) = some bs →
    RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
    MachineOk (mkstR (if bv_eqb rd 0 then regs else regupd regs rd (load_result (amo_msize wd) true bs))
      (v_addi pc 4) mem rom (some (getr regs rs))) := by
  intro segs regs pc mem rom rv w wd aq rl rd rs bs Hf He Hd Hal Hread
  have Hal' : amo_aligned wd (getr regs rs) = true := by unfold amo_aligned; rw [Hal]; rfl
  cases wd <;> simp only [amo_nbytes] at Hread <;> stepR_simp <;>
    (try simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, interp_eff_accesses, ov_rdn, Hread,
      width_bytes]) <;>
    rd_close rd

/-- SC, success path: the reservation is on the SC's own address. -/
theorem stepR_sc_ok : ∀ segs regs pc mem rom w wd aq rl (rd rs1 rs2 : reg) r,
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (Sc wd aq rl rd rs1 rs2, 4) →
    Z.modulo (bv_unsigned (getr regs rs1)) (amo_bytes wd) = 0 →
    r = getr regs rs1 →
    RiscvSemantics.store_ok segs mem (getr regs rs1) (amo_nbytes wd) = true →
    RiscvSemantics.step segs (mkstR regs pc mem rom (some r)) =
    MachineOk (mkstR (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 0)) (v_addi pc 4)
      (wbytes mem (getr regs rs1) (word_to_le_bytes (amo_nbytes wd) (getr regs rs2))) rom none) := by
  intro segs regs pc mem rom w wd aq rl rd rs1 rs2 r Hf He Hd Hal Hr Hok
  subst Hr
  have Hal' : amo_aligned wd (getr regs rs1) = true := by unfold amo_aligned; rw [Hal]; rfl
  cases wd <;> simp only [amo_nbytes] at Hok <;> stepR_simp <;>
    (try simp only [Bool.not_true, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte, store_bytes_low32,
      interp_eff_accesses, Hok, write_to_mem_wbytes, width_bytes]) <;>
    (unfold rset regupd w0 word_to_le_bytes; rw [bv_eqb0_is_x0]; cases is_x0 rd <;> rfl)

/-- AMO: load the old value, store `amo_val op old src`, `rd := old` (sign-extended for .w); reservation
    invalidated like a store. -/
theorem stepR_amo : ∀ segs regs pc mem rom rv w op wd aq rl (rd rs1 rs2 : reg) bs,
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (Amo op wd aq rl rd rs1 rs2, 4) →
    Z.modulo (bv_unsigned (getr regs rs1)) (amo_bytes wd) = 0 →
    rdn segs mem (getr regs rs1) (amo_nbytes wd) = some bs →
    RiscvSemantics.store_ok segs mem (getr regs rs1) (amo_nbytes wd) = true →
    RiscvSemantics.step segs (mkstR regs pc mem rom rv) =
    MachineOk (mkstR (if bv_eqb rd 0 then regs else regupd regs rd (load_result (amo_msize wd) true bs))
      (v_addi pc 4) (wbytes mem (getr regs rs1) (amo_store_bytes op wd bs (getr regs rs2))) rom
      (resv_inval_w rv (getr regs rs1))) := by
  intro segs regs pc mem rom rv w op wd aq rl rd rs1 rs2 bs Hf He Hd Hal Hread Hok
  have Hal' : amo_aligned wd (getr regs rs1) = true := by unfold amo_aligned; rw [Hal]; rfl
  cases wd <;> simp only [amo_nbytes] at Hread Hok <;> stepR_simp <;>
    (try simp only [Bool.not_true, Bool.false_eq_true, interp_eff_accesses, ov_rdn, Hread, Hok, ↓reduceIte,
      write_to_mem_wbytes, width_bytes]) <;>
    (cases rv with
     | none => (unfold rset regupd; rw [bv_eqb0_is_x0]; cases is_x0 rd <;> rfl)
     | some r =>
       cases h : (bv_unsigned r == bv_unsigned (getr regs rs1)) <;>
         simp only [resv_inval_w, h, Bool.false_eq_true, ↓reduceIte] <;>
         (unfold rset regupd; rw [bv_eqb0_is_x0]; cases is_x0 rd <;> rfl))

end LPS
