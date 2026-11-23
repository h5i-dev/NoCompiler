import LPS.Common.SeqExec2

/-!
# LPS `theories/Common/StreamExec.v` (f1006fe8): value facts and syscall post-state collapses for streamcat

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Common/StreamExec.v` at f1006fe8 (image-INDEPENDENT, purely additive over
PropExec/CatExec/SeqExec; shared proof library): `v_lui_4096`, `c_lts_0_0`, the `write_to_mem`
frame/read-back lemmas (`write_to_mem_below`/`_above`, `rdn_wtm_out`, `rdn_write_to_mem`), and the
`mkst`-normal-form bridges for the read post-state (`adv_apply_write`, `adv_apply_delivered`).

Conventions as SeqExec1 (`Context {fx : FPState}` is an instance argument `[FPState]` of the two
bridges). Every item is ported under its Rocq name.
-/

namespace LPS
open RiscvSemantics

/-! ### Value facts used by the streamcat loops -/

theorem v_lui_4096 : v_lui 4096 = Z_to_bv 64 4096 := rfl

/-- `blez`/`bge x0,a0` outcome on a zero read return value. -/
theorem c_lts_0_0 : c_lts (Z_to_bv 64 0) (Z_to_bv 64 0) = false := by decide

/-! ### Round-trip: bytes just written to memory read straight back -/

/-- Below the written region, `write_to_mem` leaves memory unchanged. -/
theorem write_to_mem_below : ∀ data mem (buf a : word),
    bv_unsigned buf + (data.length : Int) ≤ 2 ^ 64 → bv_unsigned a < bv_unsigned buf →
    write_to_mem mem buf data a = mem a := by
  intro data mem buf a Hnw Ha
  rw [write_to_mem_wbytes]; exact wbytes_below _ _ _ _ Hnw Ha

/-- At/above the end of the written region, `write_to_mem` leaves memory alone. -/
theorem write_to_mem_above : ∀ data mem (buf a : word),
    bv_unsigned buf + (data.length : Int) ≤ bv_unsigned a →
    write_to_mem mem buf data a = mem a := by
  intro data mem buf a Ha
  rw [write_to_mem_wbytes]; exact wbytes_above _ _ _ _ Ha

/-- `rdn` reads through a disjoint `write_to_mem`. -/
theorem rdn_wtm_out : ∀ segs data m (buf a : word) (n : Nat),
    bv_unsigned a + (n : Int) ≤ 2 ^ 64 →
    bv_unsigned buf + (data.length : Int) ≤ 2 ^ 64 →
    (bv_unsigned buf + (data.length : Int) ≤ bv_unsigned a ∨ bv_unsigned a + (n : Int) ≤ bv_unsigned buf) →
    rdn segs (write_to_mem m buf data) a n = rdn segs m a n := by
  intro segs data m buf a n Hna Hnb Hd
  apply rdn_ext _ _ _ _ _ Hna
  intro x Hx
  rcases Hd with Hd | Hd
  · exact write_to_mem_above _ _ _ _ (by omega)
  · exact write_to_mem_below _ _ _ _ Hnb (by omega)

/-- `rdn` reads back exactly the bytes just written by `write_to_mem`. -/
theorem rdn_write_to_mem : ∀ segs data mem (buf : word),
    bv_unsigned buf + (data.length : Int) ≤ 2 ^ 64 →
    rdn segs (write_to_mem mem buf data) buf data.length = some data := by
  intro segs data mem buf Hnw
  rw [write_to_mem_wbytes]; exact rdn_wbytes_hit _ _ _ _ Hnw

/-! ### `mkst`-normal-form bridges for the syscall post-states -/

/-- `advance_past_svc` of `apply_effect` with a single-buffer write effect (the read post-state). -/
theorem adv_apply_write [FPState] : ∀ regs pc sv mem rom ret buf data,
    advance_past_svc (apply_effect
      { ms_regs := regs, ms_fregs := fp_regs, ms_pc_val := pc, ms_svc_pending := sv, ms_resv := none,
        ms_fcsr := fp_csr, ms_mem := mem, ms_rom := rom }
      (mkEffect ret [(buf, data)] [])) =
    mkst (regupd regs 10 ret) (v_addi pc 4) (write_to_mem mem buf data) rom := by
  intro regs pc sv mem rom ret buf data
  have h10 : bv_eqb (10 : reg) 0 = false := by decide
  simp only [advance_past_svc, apply_effect, set_reg, h10, Bool.false_eq_true, ↓reduceIte, ms_pc, mkst,
    regupd, b_npc4, mkEffect, mkEffectU, apply_writes, apply_copies, apply_zeros, apply_unmaps]

/-- The same bridge for the canonical `delivered_writes` shape. -/
theorem adv_apply_delivered [FPState] : ∀ regs pc sv mem rom ret buf data,
    advance_past_svc (apply_effect
      { ms_regs := regs, ms_fregs := fp_regs, ms_pc_val := pc, ms_svc_pending := sv, ms_resv := none,
        ms_fcsr := fp_csr, ms_mem := mem, ms_rom := rom }
      (mkEffect ret (delivered_writes buf data) [])) =
    mkst (regupd regs 10 ret) (v_addi pc 4) (write_to_mem mem buf data) rom := by
  intro regs pc sv mem rom ret buf data
  cases data with
  | cons b rest => exact adv_apply_write regs pc sv mem rom ret buf (b :: rest)
  | nil =>
    have h10 : bv_eqb (10 : reg) 0 = false := by decide
    simp only [advance_past_svc, apply_effect, set_reg, h10, Bool.false_eq_true, ↓reduceIte, ms_pc, mkst,
      regupd, b_npc4, mkEffect, mkEffectU, apply_writes, apply_copies, apply_zeros, apply_unmaps,
      delivered_writes, write_to_mem]

end LPS
