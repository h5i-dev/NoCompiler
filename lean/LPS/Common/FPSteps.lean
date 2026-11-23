import LPS.Common.SeqExec2

/-!
# LPS `theories/Common/FPSteps.v` (f1006fe8): single-step lemmas for the live F/D instructions

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Common/FPSteps.v` at f1006fe8 (image-INDEPENDENT, parametric in `segs`; shared proof
library): the rounding-mode-field invariant `frm_zero` and its preservation lemmas
(`fp_frm_zero_fx0`, `fp_fflags_bits_range`, `fp_u32_range`, `fp_Z_land_range_l`, `fp_Z_lor_range`,
`fp_u_Z2bv32`, `fp_frm_zero_accrue`, `fp_frm_zero_slice0_5`, `fp_resolve_rm`), and the step lemmas for
the F/D data movement (`fp_step_fld` .. `fp_step_fsgnj`), the havoc-valued arithmetic, conversions and
compares (`fp_step_fari`, `fp_step_fcvt_to_f`, `fp_step_fcvt_to_x`, `fp_step_fcmp`) and the two fcsr
CSR ops (`fp_step_frrm`, `fp_step_csrsi_fflags`).

Conventions as SeqExec1. The FP state is the `FPState` instance; as in Rocq, each step lemma takes it
as an explicit argument `fx` and writes the post state with an explicit instance
`@mkst (FPState.mkFP fregs' fcsr') ..`. Rocq's `2^n` with a `Z` exponent is `Z.pow 2 n`.

Not ported (Ltac-only, no statement): the pipeline tactic `fp_pipeline`; the step lemmas are proved
by a local `simp only` over the same definitions (`fp_simp`).
-/

namespace LPS
open RiscvSemantics instr msize core ffmt fariop fmvdir fcvt_ty fcmpop csrop rmode

/-! ### The rounding-mode-field invariant -/

def frm_zero (f : bv 32) : Prop := Z.land (Z.shiftr (bv_unsigned f) 5) 7 = 0

theorem fp_frm_zero_fx0 : frm_zero (@fp_csr fx0) := by unfold frm_zero; decide

theorem fp_fflags_bits_range : ∀ fl, 0 ≤ fflags_bits fl ∧ fflags_bits fl < 32 := by
  intro ⟨nv, dz, of_, uf, nx⟩
  have h0 : Z.shiftlZ 1 0 = 1 := rfl
  have h1 : Z.shiftlZ 1 1 = 2 := rfl
  have h2 : Z.shiftlZ 1 2 = 4 := rfl
  have h3 : Z.shiftlZ 1 3 = 8 := rfl
  have h4 : Z.shiftlZ 1 4 = 16 := rfl
  show 0 ≤ (if nx then Z.shiftlZ 1 0 else 0) + (if uf then Z.shiftlZ 1 1 else 0) + (if of_ then Z.shiftlZ 1 2 else 0)
      + (if dz then Z.shiftlZ 1 3 else 0) + (if nv then Z.shiftlZ 1 4 else 0) ∧
    (if nx then Z.shiftlZ 1 0 else 0) + (if uf then Z.shiftlZ 1 1 else 0) + (if of_ then Z.shiftlZ 1 2 else 0)
      + (if dz then Z.shiftlZ 1 3 else 0) + (if nv then Z.shiftlZ 1 4 else 0) < 32
  rw [h0, h1, h2, h3, h4]
  cases nv <;> cases dz <;> cases of_ <;> cases uf <;> cases nx <;>
    simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

theorem fp_u32_range : ∀ f : bv 32, 0 ≤ bv_unsigned f ∧ bv_unsigned f < 2 ^ 32 := by
  intro f
  have := bv_unsigned_in_range f
  exact ⟨this.1, by rw [show (2 : Int) ^ 32 = ((2 ^ 32 : Nat) : Int) from rfl]; exact this.2⟩

/-- `Z.pow 2 n` of a natural exponent (Lean-only helper). -/
private theorem Z.pow2_natCast (n : Nat) : Z.pow 2 (n : Int) = ((2 ^ n : Nat) : Int) := by
  simp only [Z.pow, show ¬ ((n : Int) < 0) by omega, ↓reduceIte, Int.toNat_natCast, Int.natCast_pow]; rfl

theorem fp_Z_land_range_l : ∀ n a b : Int, 0 ≤ n → 0 ≤ a ∧ a < Z.pow 2 n →
    0 ≤ Z.land a b ∧ Z.land a b < Z.pow 2 n := by
  intro n a b Hn Ha
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le Ha.1
  obtain ⟨n', rfl⟩ := Int.eq_ofNat_of_zero_le Hn
  rw [Z.pow2_natCast] at Ha ⊢
  have hm : m < 2 ^ n' := by have := Ha.2; omega
  cases b with
  | ofNat k =>
    show 0 ≤ ((m &&& k : Nat) : Int) ∧ ((m &&& k : Nat) : Int) < ((2 ^ n' : Nat) : Int)
    have := Nat.lt_of_le_of_lt (Nat.and_le_left (n := m) (m := k)) hm
    omega
  | negSucc k =>
    show 0 ≤ ((m ^^^ (m &&& k) : Nat) : Int) ∧ ((m ^^^ (m &&& k) : Nat) : Int) < ((2 ^ n' : Nat) : Int)
    have := Nat.xor_lt_two_pow hm (Nat.lt_of_le_of_lt (Nat.and_le_left (n := m) (m := k)) hm)
    omega

theorem fp_Z_lor_range : ∀ n a b : Int, 0 ≤ n → 0 ≤ a ∧ a < Z.pow 2 n → 0 ≤ b ∧ b < Z.pow 2 n →
    0 ≤ Z.lor a b ∧ Z.lor a b < Z.pow 2 n := by
  intro n a b Hn Ha Hb
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le Ha.1
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le Hb.1
  obtain ⟨n', rfl⟩ := Int.eq_ofNat_of_zero_le Hn
  rw [Z.pow2_natCast] at Ha Hb ⊢
  rw [Z.lor_natCast]
  have hm : m < 2 ^ n' := by have := Ha.2; omega
  have hk : k < 2 ^ n' := by have := Hb.2; omega
  have := Nat.or_lt_two_pow hm hk
  omega

theorem fp_u_Z2bv32 : ∀ z, 0 ≤ z ∧ z < 2 ^ 32 → bv_unsigned (Z_to_bv 32 z) = z := by
  intro z Hz
  rw [Z_to_bv_unsigned]
  exact bv_wrap_small 32 z Hz.1 (by rw [bv_modulus_32]; exact Hz.2)

/-- `Z.shiftr` of a natural number is the `Nat` shift (Lean-only helper). -/
private theorem Z.shiftr_natCast (m k : Nat) : Z.shiftr (m : Int) k = ((m >>> k : Nat) : Int) := rfl

/-- OR-ing flag bits (< 32) into fcsr keeps fcsr[7:5]. -/
theorem fp_frm_zero_accrue : ∀ (f : bv 32) (b : Int), 0 ≤ b ∧ b < 32 → frm_zero f →
    frm_zero (Z_to_bv 32 (Z.lor (bv_unsigned f) b)) := by
  intro f b Hb Hf
  unfold frm_zero at *
  have Hr := fp_u32_range f
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le Hr.1
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le Hb.1
  have hm32 : m < 2 ^ 32 := by have := Hr.2; omega
  have hk32 : k < 2 ^ 32 := by have := Hb.2; omega
  have hor := Nat.or_lt_two_pow hm32 hk32
  rw [hm] at Hf ⊢
  rw [Z.lor_natCast, fp_u_Z2bv32 _ (by omega), Z.shiftr_natCast, Nat.shiftRight_or_distrib,
    show k >>> 5 = 0 from by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt (by omega), Nat.or_zero]
  rw [Z.shiftr_natCast] at Hf
  exact Hf

/-- Writing the fflags slice (fcsr[4:0]) keeps fcsr[7:5]. -/
theorem fp_frm_zero_slice0_5 : ∀ (f : bv 32) (v : word), frm_zero f → frm_zero (slice_set f 0 5 v) := by
  intro f v Hf
  unfold frm_zero slice_set at *
  have Hr := fp_u32_range f
  have Hv := u64_range v
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le Hr.1
  obtain ⟨u, hu⟩ := Int.eq_ofNat_of_zero_le Hv.1
  have hmask : Z.shiftlZ (Z.ones 5) 0 = ((31 : Nat) : Int) := rfl
  have hl : Z.lnot ((31 : Nat) : Int) = Int.negSucc 31 := rfl
  have hsh : Z.shiftlZ (bv_unsigned v) 0 = (u : Int) := by rw [hu]; show (u : Int) * ((2 ^ 0 : Nat) : Int) = _; simp
  simp only [hmask, hl, hsh, hm]
  have hval : Z.lor (Z.land (m : Int) (Int.negSucc 31)) (Z.land (u : Int) ((31 : Nat) : Int)) =
      (((m ^^^ (m &&& 31)) ||| (u &&& 31) : Nat) : Int) := rfl
  have hm32 : m < 2 ^ 32 := by have := Hr.2; omega
  have hlt : (m ^^^ (m &&& 31)) ||| (u &&& 31) < 2 ^ 32 :=
    Nat.or_lt_two_pow (Nat.xor_lt_two_pow hm32 (Nat.lt_of_le_of_lt Nat.and_le_left hm32))
      (Nat.and_lt_two_pow u (by decide))
  rw [hval, fp_u_Z2bv32 _ (by omega), Z.shiftr_natCast, Nat.shiftRight_or_distrib, Nat.shiftRight_xor_distrib,
    show (u &&& 31) >>> 5 = 0 from by
      rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt (Nat.and_lt_two_pow u (by decide)),
    show (m &&& 31) >>> 5 = 0 from by
      rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt (Nat.and_lt_two_pow m (by decide)),
    Nat.xor_zero, Nat.or_zero]
  rw [hm, Z.shiftr_natCast] at Hf
  exact Hf

/-- With fcsr[7:5] = 0, every rm field a compiler emits (0..4, or 7 = DYN) resolves. -/
theorem fp_resolve_rm : ∀ (rm : bv 3) (f : bv 32), frm_zero f → (bv_unsigned rm ≤ 4 ∨ bv_unsigned rm = 7) →
    ∃ md, rmode_of_field (bv_unsigned rm) (Z.land (Z.shiftr (bv_unsigned f) 5) 7) = some md := by
  intro rm f Hf Hrm
  unfold frm_zero at Hf
  unfold rmode_of_field
  rw [Hf]
  have hr := bv_unsigned_range rm
  rcases (by omega : bv_unsigned rm = 0 ∨ bv_unsigned rm = 1 ∨ bv_unsigned rm = 2 ∨ bv_unsigned rm = 3 ∨
      bv_unsigned rm = 4 ∨ bv_unsigned rm = 7) with h | h | h | h | h | h <;>
    simp [h, rmode_of_Z]

/-! ### The step pipeline for FP instructions -/

local macro "fp_simp" : tactic => `(tactic| simp only [RiscvSemantics.step, step_accesses, ms_pc, mkst,
  decode_exec_accesses, exec, interp_eff_accesses, drop_access_report, rget_getr, with_pc, b_npc4,
  load_val, width_bytes, ov_rdn, b_addsext, Bool.false_eq_true, ↓reduceIte, fget, fset, with_fregs,
  with_fcsr, fread, fwrite, accrue, resolve_rm, frm_of, inval_resv, store_val, write_to_mem_wbytes, *])

/-! ### Data movement -/

/-- fld rd, imm(rs) -/
theorem fp_step_fld : ∀ (fx : FPState) segs regs pc mem rom w (rd rs : reg) (imm : bv 12) a bs,
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (FLoad FMT_D rd rs imm, 4) →
    v_addi (getr regs rs) (bv_signed imm) = a →
    rdn segs mem a 8 = some bs →
    RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
    MachineOk (@mkst (FPState.mkFP (bvmap_set rd (bv_extract 0 64 (le_bytes_to_word bs)) (@fp_regs fx)) (@fp_csr fx))
      regs (v_addi pc 4) mem rom) := by
  intro fx segs regs pc mem rom w rd rs imm a bs Hf He Hd Ha Hr
  subst Ha
  fp_simp

/-- flw rd, imm(rs) -/
theorem fp_step_flw : ∀ (fx : FPState) segs regs pc mem rom w (rd rs : reg) (imm : bv 12) a bs,
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (FLoad FMT_S rd rs imm, 4) →
    v_addi (getr regs rs) (bv_signed imm) = a →
    rdn segs mem a 4 = some bs →
    RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
    MachineOk (@mkst (FPState.mkFP (bvmap_set rd (nan_box (bv_extract 0 32 (le_bytes_to_word bs))) (@fp_regs fx))
      (@fp_csr fx)) regs (v_addi pc 4) mem rom) := by
  intro fx segs regs pc mem rom w rd rs imm a bs Hf He Hd Ha Hr
  subst Ha
  fp_simp

/-- fsd rs2, imm(rs1): an 8-byte store of the FP value. -/
theorem fp_step_fsd : ∀ (fx : FPState) segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12) a,
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (FStore FMT_D rs1 rs2 imm, 4) →
    v_addi (getr regs rs1) (bv_signed imm) = a →
    store_ok segs mem a 8 = true →
    RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
    MachineOk (@mkst fx regs (v_addi pc 4) (wbytes mem a (word_to_le_bytes 8 (reg_get (@fp_regs fx) rs2))) rom) := by
  intro fx segs regs pc mem rom w rs1 rs2 imm a Hf He Hd Ha Hok
  subst Ha
  fp_simp
  rfl

/-- fsw rs2, imm(rs1): a 4-byte store. -/
theorem fp_step_fsw : ∀ (fx : FPState) segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12) a,
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (FStore FMT_S rs1 rs2 imm, 4) →
    v_addi (getr regs rs1) (bv_signed imm) = a →
    store_ok segs mem a 4 = true →
    RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
    MachineOk (@mkst fx regs (v_addi pc 4)
      (wbytes mem a (Z_to_le_bytes 4 (bv_unsigned (low32 (reg_get (@fp_regs fx) rs2))))) rom) := by
  intro fx segs regs pc mem rom w rs1 rs2 imm a Hf He Hd Ha Hok
  subst Ha
  fp_simp

/-- fmv.x.d rd, fs: integer register := FP bit pattern. -/
theorem fp_step_fmv_x_d : ∀ (fx : FPState) segs regs pc mem rom w (rd rs1 : reg),
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (Fmv FMV_X_F FMT_D rd rs1, 4) →
    RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
    MachineOk (@mkst fx (if bv_eqb rd 0 then regs else regupd regs rd (reg_get (@fp_regs fx) rs1))
      (v_addi pc 4) mem rom) := by
  intro fx segs regs pc mem rom w rd rs1 Hf He Hd
  fp_simp
  unfold rset regupd; rw [bv_eqb0_is_x0]; cases is_x0 rd <;> rfl

/-- fmv.x.w rd, fs -/
theorem fp_step_fmv_x_w : ∀ (fx : FPState) segs regs pc mem rom w (rd rs1 : reg),
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (Fmv FMV_X_F FMT_S rd rs1, 4) →
    RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
    MachineOk (@mkst fx (if bv_eqb rd 0 then regs else regupd regs rd (sext 64 (low32 (reg_get (@fp_regs fx) rs1))))
      (v_addi pc 4) mem rom) := by
  intro fx segs regs pc mem rom w rd rs1 Hf He Hd
  fp_simp
  unfold rset regupd; rw [bv_eqb0_is_x0]; cases is_x0 rd <;> rfl

/-- fmv.d.x fd, rs -/
theorem fp_step_fmv_d_x : ∀ (fx : FPState) segs regs pc mem rom w (rd rs1 : reg),
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (Fmv FMV_F_X FMT_D rd rs1, 4) →
    RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
    MachineOk (@mkst (FPState.mkFP (bvmap_set rd (getr regs rs1) (@fp_regs fx)) (@fp_csr fx)) regs (v_addi pc 4) mem rom) := by
  intro fx segs regs pc mem rom w rd rs1 Hf He Hd
  fp_simp

/-- fmv.w.x fd, rs -/
theorem fp_step_fmv_w_x : ∀ (fx : FPState) segs regs pc mem rom w (rd rs1 : reg),
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (Fmv FMV_F_X FMT_S rd rs1, 4) →
    RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
    MachineOk (@mkst (FPState.mkFP (bvmap_set rd (nan_box (low32 (getr regs rs1))) (@fp_regs fx)) (@fp_csr fx))
      regs (v_addi pc 4) mem rom) := by
  intro fx segs regs pc mem rom w rd rs1 Hf He Hd
  fp_simp

/-- fsgnj / fsgnjn / fsgnjx (fmv.d, fneg.d, fabs.d are these). -/
theorem fp_step_fsgnj : ∀ (fx : FPState) segs regs pc mem rom w op fmt (rd rs1 rs2 : reg),
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (Fsgnj op fmt rd rs1 rs2, 4) →
    ∃ fr', RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
      MachineOk (@mkst (FPState.mkFP fr' (@fp_csr fx)) regs (v_addi pc 4) mem rom) := by
  intro fx segs regs pc mem rom w op fmt rd rs1 rs2 Hf He Hd
  cases fmt <;> exact ⟨_, by fp_simp; rfl⟩

/-! ### Arithmetic / conversions / compares (havoc-valued) -/

/-- The accrued fcsr keeps `frm_zero` (the `Hacc` of the Rocq proofs). -/
private theorem fp_acc (cs : bv 32) (Hz : frm_zero cs) :
    ∀ fl, frm_zero (Z_to_bv 32 (Z.lor (bv_unsigned cs) (fflags_bits fl))) :=
  fun fl => fp_frm_zero_accrue cs _ (fp_fflags_bits_range fl) Hz

/-- fadd/fsub/fmul/fdiv . s/d: new FP file, flags OR-ed into fcsr[4:0]. -/
theorem fp_step_fari : ∀ (fx : FPState) segs regs pc mem rom w op fmt (rd rs1 rs2 : reg) (rm : bv 3),
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (Fari op fmt rd rs1 rs2 rm, 4) →
    frm_zero (@fp_csr fx) → (bv_unsigned rm ≤ 4 ∨ bv_unsigned rm = 7) →
    ∃ fr' cs', frm_zero cs' ∧
      RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
      MachineOk (@mkst (FPState.mkFP fr' cs') regs (v_addi pc 4) mem rom) := by
  intro fx segs regs pc mem rom w op fmt rd rs1 rs2 rm Hf He Hd Hz Hrm
  obtain ⟨md, Hmd⟩ := fp_resolve_rm rm _ Hz Hrm
  have Hacc := fp_acc _ Hz
  fp_simp
  cases fmt <;> exact ⟨_, _, Hacc _, rfl⟩

/-- fcvt with an FP DESTINATION: new FP file, flags accrue. -/
theorem fp_step_fcvt_to_f : ∀ (fx : FPState) segs regs pc mem rom w dst src (rd rs1 : reg) (rm : bv 3),
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (Fcvt dst src rd rs1 rm, 4) →
    (dst = FC_S ∨ dst = FC_D) →
    frm_zero (@fp_csr fx) → (bv_unsigned rm ≤ 4 ∨ bv_unsigned rm = 7) →
    ∃ fr' cs', frm_zero cs' ∧
      RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
      MachineOk (@mkst (FPState.mkFP fr' cs') regs (v_addi pc 4) mem rom) := by
  intro fx segs regs pc mem rom w dst src rd rs1 rm Hf He Hd Hdst Hz Hrm
  obtain ⟨md, Hmd⟩ := fp_resolve_rm rm _ Hz Hrm
  have Hacc := fp_acc _ Hz
  rcases Hdst with rfl | rfl <;> cases src <;> fp_simp <;> exact ⟨_, _, Hacc _, rfl⟩

/-- fcvt with an INTEGER destination: integer rd := some word, flags accrue. -/
theorem fp_step_fcvt_to_x : ∀ (fx : FPState) segs regs pc mem rom w dst src (rd rs1 : reg) (rm : bv 3),
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (Fcvt dst src rd rs1 rm, 4) →
    (dst = FC_W ∨ dst = FC_WU ∨ dst = FC_L ∨ dst = FC_LU) →
    (src = FC_S ∨ src = FC_D) →
    frm_zero (@fp_csr fx) → (bv_unsigned rm ≤ 4 ∨ bv_unsigned rm = 7) →
    ∃ (v : word) (cs' : bv 32), frm_zero cs' ∧
      RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
      MachineOk (@mkst (FPState.mkFP (@fp_regs fx) cs') (if bv_eqb rd 0 then regs else regupd regs rd v)
        (v_addi pc 4) mem rom) := by
  intro fx segs regs pc mem rom w dst src rd rs1 rm Hf He Hd Hdst Hsrc Hz Hrm
  obtain ⟨md, Hmd⟩ := fp_resolve_rm rm _ Hz Hrm
  have Hacc := fp_acc _ Hz
  rcases Hdst with rfl | rfl | rfl | rfl <;> rcases Hsrc with rfl | rfl <;> fp_simp <;>
    (cases hx : is_x0 rd
     · exact ⟨_, _, Hacc _, by simp only [rset, regupd, bv_eqb0_is_x0, hx, Bool.false_eq_true, ↓reduceIte]; rfl⟩
     · exact ⟨Z_to_bv 64 0, _, Hacc _, by simp only [rset, bv_eqb0_is_x0, hx, ↓reduceIte]; rfl⟩)

/-- feq/flt/fle . s/d: integer rd := 0 or 1, flags accrue. -/
theorem fp_step_fcmp : ∀ (fx : FPState) segs regs pc mem rom w op fmt (rd rs1 rs2 : reg),
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (Fcmp op fmt rd rs1 rs2, 4) →
    frm_zero (@fp_csr fx) →
    ∃ (b : Bool) (cs' : bv 32), frm_zero cs' ∧
      RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
      MachineOk (@mkst (FPState.mkFP (@fp_regs fx) cs')
        (if bv_eqb rd 0 then regs else regupd regs rd (if b then Z_to_bv 64 1 else Z_to_bv 64 0))
        (v_addi pc 4) mem rom) := by
  intro fx segs regs pc mem rom w op fmt rd rs1 rs2 Hf He Hd Hz
  have Hacc := fp_acc _ Hz
  fp_simp
  cases hx : is_x0 rd
  · exact ⟨_, _, Hacc _, by simp only [rset, regupd, w0, w1, bv_eqb0_is_x0, hx, Bool.false_eq_true, ↓reduceIte]; rfl⟩
  · exact ⟨true, _, Hacc _, by simp only [rset, bv_eqb0_is_x0, hx, ↓reduceIte]; rfl⟩

/-! ### The two CSR instructions -/

/-- frrm rd (= csrrs rd, frm, x0): reads fcsr[7:5] = 0, writes nothing. -/
theorem fp_step_frrm : ∀ (fx : FPState) segs regs pc mem rom w (rd : reg),
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (Csr CSR_RS rd 0 2, 4) →
    frm_zero (@fp_csr fx) →
    RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
    MachineOk (@mkst fx (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 0)) (v_addi pc 4) mem rom) := by
  intro fx segs regs pc mem rom w rd Hf He Hd Hz
  unfold frm_zero at Hz
  have hs : csr_slice 2 = some (5, 3) := by decide
  have hro : csr_write_illegal false 2 = false := by decide
  have hx0 : is_x0 0 = true := rfl
  have hget : slice_get (@fp_csr fx) 5 3 = Z_to_bv 64 0 := by
    unfold slice_get; rw [show Z.shiftrZ (bv_unsigned (@fp_csr fx)) 5 = Z.shiftr (bv_unsigned (@fp_csr fx)) 5 from by
      unfold Z.shiftrZ Z.shiftlZ Z.shiftr; rfl, show Z.ones 3 = 7 from rfl, Hz]
  fp_simp
  simp only [exec_csr, hs, hget, Bool.not_true]
  unfold rset regupd; rw [bv_eqb0_is_x0]; cases is_x0 rd <;> rfl

/-- csrsi fflags, uimm (= csrrsi x0, fflags, uimm): sets flag bits only. -/
theorem fp_step_csrsi_fflags : ∀ (fx : FPState) segs regs pc mem rom w (uimm : bv 5),
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (CsrI CSR_RS 0 uimm 1, 4) →
    frm_zero (@fp_csr fx) →
    ∃ cs', frm_zero cs' ∧
      RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
      MachineOk (@mkst (FPState.mkFP (@fp_regs fx) cs') regs (v_addi pc 4) mem rom) := by
  intro fx segs regs pc mem rom w uimm Hf He Hd Hz
  have hs : csr_slice 1 = some (0, 5) := by decide
  have hro : ∀ b, csr_write_illegal b 1 = false := by intro b; cases b <;> decide
  have hx0 : is_x0 0 = true := rfl
  by_cases Eu : bv_unsigned uimm = 0
  · refine ⟨@fp_csr fx, Hz, ?_⟩
    fp_simp
    simp only [exec_csr, hs, hx0, beq_self_eq_true, Bool.not_true, rset, ↓reduceIte, Bool.false_eq_true,
      interp_eff_accesses]
  · refine ⟨slice_set (@fp_csr fx) 0 5 (bv_or (slice_get (@fp_csr fx) 0 5) (zext 64 uimm)),
      fp_frm_zero_slice0_5 _ _ Hz, ?_⟩
    have Eu' : (bv_unsigned uimm == 0) = false := by simpa using Eu
    fp_simp
    simp only [exec_csr, hs, hx0, Bool.not_false, rset, ↓reduceIte, interp_eff_accesses]
    rfl

end LPS
