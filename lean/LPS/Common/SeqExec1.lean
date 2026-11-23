import LPS.Common.CatExec2

/-!
# LPS `theories/Common/SeqExec.v` (f1006fe8), part 1: calls, value-precise stores, `_at` steps, read-back, argv bounds

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Common/SeqExec.v` at f1006fe8 (image-INDEPENDENT symbolic-execution infrastructure for
compiled binaries with real stack frames; shared proof library), SeqExec.v:1-590 (`Section WithFP1`
through `WithFP3`): the jalr target shape `v_jalr`, the `jal`/`jalr` call step lemmas, the
value-precise store `step_sd_val`/`step_sd_at`, the `_at` (writeback pre-normalized) step lemmas, the
`wbytes` read-back `rdn_wbytes_hit`, the value simplifications (`v_addiw_small`, `land_255_small`, ...),
the `to_wexit` constructors `tw_write_ret`/`tw_exit_coden`, the generic argv-pointer bounds
`argv_ptr_bounds`, `step_jalr_x0`/`step_jalr_link` and `getr_zero`. Part 2 (SeqExec2) has the rest
(SeqExec.v:590-1072: M extension, narrow stores, `rdn` composition).

Conventions as PropExec1..7 and CatExec1..2: Rocq's `Context {fx : FPState}` is an instance argument
`[FPState]` (only on the lemmas that mention a machine state); `nth k l d` is `l.getD k d`, `firstn` is
`List.take`; Rocq's `(x <? y)%Z` is `decide (x < y)`. The step lemmas' proofs unfold the interpreter as
PropExec4's do (the local `step_simp` macro; the Ltac `step_pipeline` is not ported).

Not ported (Ltac-only, no statement): `reg_neq_tac`, `getr_resolve`, `regupd_resolve` and the three
`Goal ... Abort` smoke tests of those tactics (SeqExec.v:560-600); in Lean, `getr_same`/`getr_other`
(PropExec6) with `by decide` side conditions play their role.
-/

namespace LPS
open RiscvSemantics instr aluop mulop branch_cond msize core

local macro "step_simp" : tactic => `(tactic| simp only [RiscvSemantics.step, step_accesses, ms_pc, mkst,
  decode_exec_accesses, exec, interp_eff_accesses, drop_access_report, rget_getr, with_pc, b_npc4,
  load_val, width_bytes, ov_rdn, b_addsext, Bool.false_eq_true, ↓reduceIte, *])

local macro "rd_close" rd:term : tactic =>
  `(tactic| (unfold rset regupd; rw [bv_eqb0_is_x0]; cases is_x0 $rd <;> rfl))

/-! ### Value shapes -/

/-- The jalr target: (rs1 + imm) with bit 0 cleared. Definitionally `PropExec.jalr_tgt`. -/
def v_jalr (x : word) (imm : Int) : word := Z_to_bv 64 (jalr_tgtZ x imm)

/-! ### Per-instruction step lemmas -/

/-- Jal with a live link register: rd := pc + 4, jump to `btgt`. -/
theorem step_jal_link [FPState] : ∀ segs regs pc mem rom w (rd : reg) (imm : bv 21),
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (Jal rd imm, 4) →
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_addi pc 4))
      (btgt pc (bv_signed imm)) mem rom) := by
  intro segs regs pc mem rom w rd imm Hfetch Hecall Hdecode
  step_simp; rd_close rd

/-- Jalr: rd := pc + 4, jump to (rs1 + imm) & ~1 (`step_jalr_gen` with the `v_jalr` shape). -/
theorem step_jalr [FPState] : ∀ segs regs pc mem rom w (rd rs1 : reg) (imm : bv 12),
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (Jalr rd rs1 imm, 4) →
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_addi pc 4))
      (v_jalr (getr regs rs1) (bv_signed imm)) mem rom) :=
  fun segs regs pc mem rom w rd rs1 imm Hf He Hd => step_jalr_gen segs regs pc mem rom w rd rs1 imm Hf He Hd

/-! ### Value-precise store double -/

/-- Store double, stored VALUE exposed. -/
theorem step_sd_val [FPState] : ∀ segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12),
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (Store SZ8 rs1 rs2 imm, 4) →
    RiscvSemantics.store_ok segs mem (v_addi (getr regs rs1) (bv_signed imm)) 8 = true →
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst regs (v_addi pc 4)
      (wbytes mem (v_addi (getr regs rs1) (bv_signed imm)) (word_to_le_bytes 8 (getr regs rs2))) rom) := by
  intro segs regs pc mem rom w rs1 rs2 imm Hfetch Hecall Hdecode Hok
  simp only [RiscvSemantics.step, step_accesses, ms_pc, mkst, decode_exec_accesses, exec,
    drop_access_report, rget_getr, with_pc, b_npc4, b_addsext, Bool.false_eq_true,
    ↓reduceIte, Hfetch, Hecall, Hdecode]
  simp only [store_val, interp_eff_accesses, width_bytes, Hok, ↓reduceIte, write_to_mem_wbytes, word_to_le_bytes]
  rfl

/-- `step_sd_val` with the store address and value pre-normalized. -/
theorem step_sd_at [FPState] : ∀ segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12) (a v : word),
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (Store SZ8 rs1 rs2 imm, 4) →
    v_addi (getr regs rs1) (bv_signed imm) = a →
    getr regs rs2 = v →
    RiscvSemantics.store_ok segs mem a 8 = true →
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst regs (v_addi pc 4) (wbytes mem a (word_to_le_bytes 8 v)) rom) := by
  intro segs regs pc mem rom w rs1 rs2 imm a v Hf He Hd Ha Hv Hok
  rw [step_sd_val segs regs pc mem rom w rs1 rs2 imm Hf He Hd (by rw [Ha]; exact Hok), Ha, Hv]

/-- `step_addi` with the writeback value pre-normalized (keeps an evar step chain flat). -/
theorem step_addi_at [FPState] : ∀ segs regs pc mem rom w (rd rs : reg) (imm : bv 12) v,
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (OpImm ALU_ADD rd rs imm, 4) →
    bv_eqb rd 0 = false →
    v_addi (getr regs rs) (bv_signed imm) = v →
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom) := by
  intro segs regs pc mem rom w rd rs imm v Hf He Hd Hrd Hv
  rw [step_addi segs regs pc mem rom w rd rs imm Hf He Hd, Hrd, Hv]; rfl

theorem step_add_at [FPState] : ∀ segs regs pc mem rom w (rd rs1 rs2 : reg) v,
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (Op ALU_ADD rd rs1 rs2, 4) →
    bv_eqb rd 0 = false →
    v_add (getr regs rs1) (getr regs rs2) = v →
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom) := by
  intro segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv
  rw [step_add segs regs pc mem rom w rd rs1 rs2 Hf He Hd, Hrd, Hv]; rfl

theorem step_sub_at [FPState] : ∀ segs regs pc mem rom w (rd rs1 rs2 : reg) v,
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (Op ALU_SUB rd rs1 rs2, 4) →
    bv_eqb rd 0 = false →
    v_sub (getr regs rs1) (getr regs rs2) = v →
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom) := by
  intro segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv
  rw [step_sub segs regs pc mem rom w rd rs1 rs2 Hf He Hd, Hrd, Hv]; rfl

theorem step_lui_at [FPState] : ∀ segs regs pc mem rom w (rd : reg) (imm : bv 20) v,
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (Lui rd imm, 4) →
    bv_eqb rd 0 = false →
    v_lui (Z.shiftl (bv_signed imm) 12) = v →
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom) := by
  intro segs regs pc mem rom w rd imm v Hf He Hd Hrd Hv
  rw [step_lui segs regs pc mem rom w rd imm Hf He Hd, Hrd, Hv]; rfl

theorem step_auipc_at [FPState] : ∀ segs regs pc mem rom w (rd : reg) (imm : bv 20) v,
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (Auipc rd imm, 4) →
    bv_eqb rd 0 = false →
    v_auipc pc (Z.shiftl (bv_signed imm) 12) = v →
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom) := by
  intro segs regs pc mem rom w rd imm v Hf He Hd Hrd Hv
  rw [step_auipc segs regs pc mem rom w rd imm Hf He Hd, Hrd, Hv]; rfl

theorem step_addiw_at [FPState] : ∀ segs regs pc mem rom w (rd rs : reg) (imm : bv 12) v,
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (OpImm32 rd rs imm, 4) →
    bv_eqb rd 0 = false →
    v_addiw (getr regs rs) (bv_signed imm) = v →
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom) := by
  intro segs regs pc mem rom w rd rs imm v Hf He Hd Hrd Hv
  rw [step_addiw segs regs pc mem rom w rd rs imm Hf He Hd, Hrd, Hv]; rfl

theorem step_sltiu_at [FPState] : ∀ segs regs pc mem rom w (rd rs : reg) (imm : bv 12) v,
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (OpImm ALU_SLTU rd rs imm, 4) →
    bv_eqb rd 0 = false →
    v_sltiu (getr regs rs) (bv_signed imm) = v →
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom) := by
  intro segs regs pc mem rom w rd rs imm v Hf He Hd Hrd Hv
  rw [step_sltiu segs regs pc mem rom w rd rs imm Hf He Hd, Hrd, Hv]; rfl

theorem step_xori_at [FPState] : ∀ segs regs pc mem rom w (rd rs : reg) (imm : bv 12) v,
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (OpImm ALU_XOR rd rs imm, 4) →
    bv_eqb rd 0 = false →
    v_xori (getr regs rs) (bv_signed imm) = v →
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom) := by
  intro segs regs pc mem rom w rd rs imm v Hf He Hd Hrd Hv
  rw [step_xori segs regs pc mem rom w rd rs imm Hf He Hd, Hrd, Hv]; rfl

theorem step_mul_at [FPState] : ∀ segs regs pc mem rom w (rd rs1 rs2 : reg) v,
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (instr.Mul M_MUL rd rs1 rs2, 4) →
    bv_eqb rd 0 = false →
    v_mul (getr regs rs1) (getr regs rs2) = v →
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom) := by
  intro segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv
  rw [step_mul segs regs pc mem rom w rd rs1 rs2 Hf He Hd, Hrd, Hv]; rfl

theorem step_andi_at [FPState] : ∀ segs regs pc mem rom w (rd rs : reg) (imm : bv 12) v,
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (OpImm ALU_AND rd rs imm, 4) →
    bv_eqb rd 0 = false →
    v_andi (getr regs rs) (bv_signed imm) = v →
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom) := by
  intro segs regs pc mem rom w rd rs imm v Hf He Hd Hrd Hv
  rw [step_andi segs regs pc mem rom w rd rs imm Hf He Hd, Hrd, Hv]; rfl

theorem step_ori_at [FPState] : ∀ segs regs pc mem rom w (rd rs : reg) (imm : bv 12) v,
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (OpImm ALU_OR rd rs imm, 4) →
    bv_eqb rd 0 = false →
    v_ori (getr regs rs) (bv_signed imm) = v →
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom) := by
  intro segs regs pc mem rom w rd rs imm v Hf He Hd Hrd Hv
  rw [step_ori segs regs pc mem rom w rd rs imm Hf He Hd, Hrd, Hv]; rfl

theorem step_slli_at [FPState] : ∀ segs regs pc mem rom w (rd rs : reg) (sh : bv 6) v,
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (ShiftImm ALU_SLL rd rs sh, 4) →
    bv_eqb rd 0 = false →
    v_slli (getr regs rs) (bv_unsigned sh) = v →
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom) := by
  intro segs regs pc mem rom w rd rs sh v Hf He Hd Hrd Hv
  rw [step_slli segs regs pc mem rom w rd rs sh Hf He Hd, Hrd, Hv]; rfl

theorem step_srli_at [FPState] : ∀ segs regs pc mem rom w (rd rs : reg) (sh : bv 6) v,
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (ShiftImm ALU_SRL rd rs sh, 4) →
    bv_eqb rd 0 = false →
    v_srli (getr regs rs) (bv_unsigned sh) = v →
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom) := by
  intro segs regs pc mem rom w rd rs sh v Hf He Hd Hrd Hv
  rw [step_srli segs regs pc mem rom w rd rs sh Hf He Hd, Hrd, Hv]; rfl

theorem step_srai_at [FPState] : ∀ segs regs pc mem rom w (rd rs : reg) (sh : bv 6) v,
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (ShiftImm ALU_SRA rd rs sh, 4) →
    bv_eqb rd 0 = false →
    v_srai (getr regs rs) (bv_unsigned sh) = v →
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom) := by
  intro segs regs pc mem rom w rd rs sh v Hf He Hd Hrd Hv
  rw [step_srai segs regs pc mem rom w rd rs sh Hf He Hd, Hrd, Hv]; rfl

/-! ### `wbytes` read-back -/

/-- Bytes just written read straight back (no-overflow hypothesis: the walks are wrapping adds). -/
theorem rdn_wbytes_hit : ∀ segs (bs : List byte) m (a : word),
    bv_unsigned a + (bs.length : Int) ≤ 2 ^ 64 →
    rdn segs (wbytes m a bs) a bs.length = some bs := by
  intro segs bs
  induction bs with
  | nil => intro _ _ _; rfl
  | cons b rest ih =>
    intro m a hnw
    simp only [List.length_cons, Int.natCast_add, Int.natCast_one] at hnw
    have ha := u64_range a
    have ha1 := u64_range (a + 1)
    have hrest : bv_unsigned (a + 1) + (rest.length : Int) ≤ 2 ^ 64 := by
      cases rest with
      | nil => simp only [List.length_nil, Int.natCast_zero]; omega
      | cons b' rest' =>
        simp only [List.length_cons, Int.natCast_add, Int.natCast_one] at hnw ⊢
        rw [u_add1 _ (by omega)]; omega
    have hread : wbytes (fun x => if bv_eqb x a then some b else m x) (a + 1) rest a = some b := by
      cases rest with
      | nil => simp [wbytes, bv_eqb_refl]
      | cons b' rest' =>
        simp only [List.length_cons, Int.natCast_add, Int.natCast_one] at hnw hrest
        have hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1 := u_add1 _ (by omega)
        rw [wbytes_below _ _ _ _ (by simp only [List.length_cons, Int.natCast_add, Int.natCast_one]; omega)
          (by omega)]
        simp [bv_eqb_refl]
    show rdn segs (wbytes (fun x => if bv_eqb x a then some b else m x) (a + 1) rest) a (rest.length + 1) = _
    simp only [rdn, hread, ih _ _ hrest]

/-- Read a full 8-byte slot back. -/
theorem rdn_wbytes_hit8 : ∀ segs m (a v : word), bv_unsigned a + 8 ≤ 2 ^ 64 →
    rdn segs (wbytes m a (word_to_le_bytes 8 v)) a 8 = some (word_to_le_bytes 8 v) := by
  intro segs m a v Hnw
  have H := rdn_wbytes_hit segs (word_to_le_bytes 8 v) m a
  rw [length_N_to_le_bytes] at H
  exact H (by simpa using Hnw)

/-- Hypothesis-free: the `bv` bound is enforced by the type. -/
theorem bytes_le_to_Z_8 : ∀ v : word, bytes_le_to_Z (word_to_le_bytes 8 v) = bv_unsigned v := by
  intro v
  rw [bytes_le_N]
  have := u64_range v
  exact Int.emod_eq_of_lt this.1 this.2

/-! ### Value simplification -/

/-- Definitional: `c_ltu` IS the unsigned `Z.ltb`. -/
theorem c_ltu_ltb : ∀ x y : word, c_ltu x y = decide (bv_unsigned x < bv_unsigned y) := fun _ _ => rfl

theorem v_addiw_small : ∀ (x : word) (imm : Int),
    0 ≤ bv_unsigned x + imm → bv_unsigned x + imm < 2 ^ 31 → 0 ≤ imm →
    bv_unsigned (v_addiw x imm) = bv_unsigned x + imm := by
  intro x imm Hlo Hhi _
  unfold v_addiw
  rw [Z_to_bv_unsigned, bv_swrap_small 32 _ (by rw [bv_half_modulus_32]; omega)
    (by rw [bv_half_modulus_32]; omega)]
  exact bv_wrap_small 64 _ Hlo (by rw [bv_modulus_64]; omega)

/-- `sext.w` on an in-range value is the identity. -/
theorem v_addiw_id : ∀ x : word, bv_unsigned x < 2 ^ 31 → v_addiw x 0 = x := by
  intro x Hx
  apply bv_eq
  have := u64_range x
  rw [v_addiw_small x 0 (by omega) (by omega) (by omega)]
  omega

/-- `Z.land z 255` of a non-negative `z` is `z mod 256`. -/
private theorem Z.land_ones8 (z : Int) (h : 0 ≤ z) : Z.land z 255 = z % 256 := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
  rw [show (255 : Int) = ((2 ^ 8 - 1 : Nat) : Int) from rfl, Z.land_natCast, Nat.and_two_pow_sub_one_eq_mod]
  show ((m % 256 : Nat) : Int) = (m : Int) % 256
  omega

/-- Masking a small exit code with 255 is the identity. -/
theorem land_255_small : ∀ c : word, bv_unsigned c < 256 → bv_and c (Z_to_bv 64 255) = c := by
  intro c Hc
  apply bv_eq
  have hc := u64_range c
  unfold bv_and
  rw [Z_to_bv_unsigned, show bv_unsigned (Z_to_bv 64 255) = 255 from rfl, Z.land_ones8 _ hc.1,
    Int.emod_eq_of_lt hc.1 Hc]
  exact bv_wrap_small 64 _ hc.1 (by rw [bv_modulus_64]; omega)

/-! ### `to_wexit` constructors -/

/-- A write at the raw ecall post-state, continuing with the ACTUAL syscall return value. -/
theorem tw_write_ret [FPState] : ∀ segs regs pc mem rom buf bufs code,
    bv_unsigned (getr regs 17) = 64 → reg_get regs 10 = Z_to_bv 64 1 →
    ms_read_bytes { ms_regs := regs, ms_fregs := fp_regs, ms_pc_val := pc, ms_svc_pending := some (getr regs 17),
                    ms_resv := none, ms_fcsr := fp_csr, ms_mem := mem, ms_rom := rom }
      (reg_get regs 11) (reg_get regs 12) = some buf →
    1 ≤ buf.length →
    (∀ n, 1 ≤ n → n ≤ buf.length →
      to_wexit segs (mkst (regupd regs 10 (len_word (buf.take n))) (v_addi pc 4) mem rom) bufs code) →
    to_wexit segs { ms_regs := regs, ms_fregs := fp_regs, ms_pc_val := pc, ms_svc_pending := some (getr regs 17),
                    ms_resv := none, ms_fcsr := fp_csr, ms_mem := mem, ms_rom := rom } (buf :: bufs) code := by
  intro segs regs pc mem rom buf bufs code H17 H10 Hr Hnb Hcont
  refine .tw_write _ (getr regs 17) buf bufs code rfl H17 ?_ ?_ Hnb ?_
  · simp only [ms_gpr, arg_reg_0]; exact H10
  · simp only [ms_gpr, arg_reg_1, arg_reg_2]; exact Hr
  · intro n hn1 hn2
    rw [adv_set]
    exact Hcont n hn1 hn2

/-- Exit with an arbitrary small code at the raw ecall post-state. -/
theorem tw_exit_coden [FPState] : ∀ segs regs pc mem rom (c : word),
    bv_unsigned (getr regs 17) = 93 → reg_get regs 10 = c → bv_unsigned c < 256 →
    to_wexit segs { ms_regs := regs, ms_fregs := fp_regs, ms_pc_val := pc, ms_svc_pending := some (getr regs 17),
                    ms_resv := none, ms_fcsr := fp_csr, ms_mem := mem, ms_rom := rom } [] c := by
  intro segs regs pc mem rom c H17 H10 Hc
  have Hg : bv_and (ms_gpr { ms_regs := regs, ms_fregs := fp_regs, ms_pc_val := pc,
                             ms_svc_pending := some (getr regs 17), ms_resv := none, ms_fcsr := fp_csr,
                             ms_mem := mem, ms_rom := rom } 0) (Z_to_bv 64 255) = c := by
    simp only [ms_gpr, arg_reg_0]; rw [H10]; exact land_255_small c Hc
  rw [← Hg]
  exact .tw_exit _ (getr regs 17) rfl (.inl H17)

/-! ### Generic argv-pointer bounds -/

/-- Everything the initial stack layout can address fits in `[sp, sp + argv_layout_slack)`. -/
def argv_layout_slack : Int := 4300000

/-- Pure-`Z` arithmetic cores for `argv_ptr_bounds` (SeqExec.v's `Local` lemmas). -/
theorem argv_struct_arith : ∀ a e : Int, 0 ≤ a → a ≤ 1024 → 0 ≤ e → e ≤ 256 →
    8 + (a + 1) * 8 + (e + 1) * 8 + 160 ≤ 10424 := by
  intros; omega

theorem argv_sum_arith : ∀ a b : Int, a ≤ 10424 → b ≤ 2097152 → a + b ≤ 2107576 := by
  intros; omega

theorem argv_mod_arith : ∀ s m : Int, 0 ≤ s → 0 ≤ m → m ≤ 2107576 → s + 4300000 < 2 ^ 64 →
    0 ≤ s + m ∧ s + m < 2 ^ 64 := by
  intros; omega

theorem argv_final_arith : ∀ s m l : Int, 0 ≤ m → 0 ≤ l → m ≤ 2107576 → l ≤ 131071 →
    s + 4300000 < 2 ^ 64 → s ≤ s + m ∧ s + m + l + 1 < 2 ^ 64 := by
  intros; omega

theorem argv_ptr_bounds : ∀ (sp : word) av ev k,
    valid_argv av → valid_envp ev → k < av.length →
    bv_unsigned sp + argv_layout_slack < 2 ^ 64 →
    bv_unsigned sp ≤ bv_unsigned (cat_argv_ptr sp av ev k) ∧
    bv_unsigned (cat_argv_ptr sp av ev k) + ((av.getD k []).length : Int) + 1 < 2 ^ 64 := by
  intro sp av ev k Hva Hve Hk Hsp
  have HavZ := valid_argv_len av Hva
  have HnthZ := valid_argv_str_len av k Hva Hk
  have Htot := Hva.2.1
  have HevZ : (ev.length : Int) ≤ 256 := Hve.1
  rw [total_arg_bytes_Z] at Htot
  have Hfl := total_arg_bytes_firstn_le k av
  have HtotZ : ((total_arg_bytes_nat (av.take k) : Nat) : Int) ≤ 2097152 := by omega
  have HA : ((cat_struct_size av ev : Nat) : Int) ≤ 10424 := by
    have := argv_struct_arith _ _ (by omega) HavZ (by omega) HevZ
    unfold cat_struct_size auxv_size; omega
  have Hptr : cat_argv_ptr sp av ev k
      = sp + nat_to_word (cat_struct_size av ev + total_arg_bytes_nat (av.take k)) := by
    rw [cat_argv_ptr_offset sp av ev k Hk]; unfold cat_string_base
    rw [nat_to_word_add_merge]
  have HnZ : (((cat_struct_size av ev + total_arg_bytes_nat (av.take k)) : Nat) : Int) ≤ 2107576 := by
    have := argv_sum_arith _ _ HA HtotZ; omega
  have Hu64 := u64_range sp
  unfold argv_layout_slack at Hsp
  have Hm := argv_mod_arith _ _ Hu64.1 (Int.natCast_nonneg _) HnZ Hsp
  rw [Hptr, nat_to_word_unsigned_add sp _ Hm.2]
  exact argv_final_arith _ _ _ (Int.natCast_nonneg _) (Int.natCast_nonneg _) HnZ HnthZ Hsp

/-- Jalr with rd = x0 (RISC-V `ret` / tail jump) and the target named. -/
theorem step_jalr_x0 [FPState] : ∀ segs regs pc mem rom w (rs1 : reg) (imm : bv 12) tgt,
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (Jalr 0 rs1 imm, 4) →
    getr regs rs1 = tgt →
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst regs (v_jalr tgt (bv_signed imm)) mem rom) := by
  intro segs regs pc mem rom w rs1 imm tgt Hf He Hd Ht
  rw [step_jalr segs regs pc mem rom w 0 rs1 imm Hf He Hd, Ht]; rfl

/-- Jalr with a live link register and the target named. -/
theorem step_jalr_link [FPState] : ∀ segs regs pc mem rom w (rd rs1 : reg) (imm : bv 12) tgt,
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (Jalr rd rs1 imm, 4) →
    bv_eqb rd 0 = false →
    getr regs rs1 = tgt →
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (regupd regs rd (v_addi pc 4)) (v_jalr tgt (bv_signed imm)) mem rom) := by
  intro segs regs pc mem rom w rd rs1 imm tgt Hf He Hd Hrd Ht
  rw [step_jalr segs regs pc mem rom w rd rs1 imm Hf He Hd, Ht, Hrd]; rfl

/-! ### Register-lookup resolution -/

theorem getr_zero : ∀ regs, getr regs 0 = Z_to_bv 64 0 := fun _ => rfl

end LPS
