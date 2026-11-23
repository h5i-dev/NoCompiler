import LPS.Common.ExitSim1

/-!
# LPS `theories/Common/ExitSim.v` (f1006fe8), part 2: the argc overlay, the run level

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Common/ExitSim.v` at f1006fe8, after `End WithSegs`: the overlay that replaces the first
8 stack bytes by the little-endian argc (so `sim_c` can be closed for all argv by enumerating argc), and
the run-level packaging (`exit_omni_run`, `exit_obs_iff`, `exit_no_error_run`, `exit_must_exit_with`,
`exit_omni_run_code_unique`, `exit_omni_strong_equiv`, `exit_strong_equiv`). Conventions as ExitSim1.
`actual_mem_is_overlay` uses function extensionality, which is a theorem in Lean (`funext`).
-/

namespace LPS
open RiscvSemantics OmniRun

/-! ### Overlay + enumerate: closing `sim_c` for binaries that read only argc -/

def overlay_argc_bytes (sp : word) (argc : Nat) (base_mem : word → Option byte) : word → Option byte :=
  let bytes := word_le8 (nat_to_word argc)
  fun addr =>
    if bv_unsigned addr == bv_unsigned sp then bytes[0]?
    else if bv_unsigned addr == bv_unsigned sp + 1 then bytes[1]?
    else if bv_unsigned addr == bv_unsigned sp + 2 then bytes[2]?
    else if bv_unsigned addr == bv_unsigned sp + 3 then bytes[3]?
    else if bv_unsigned addr == bv_unsigned sp + 4 then bytes[4]?
    else if bv_unsigned addr == bv_unsigned sp + 5 then bytes[5]?
    else if bv_unsigned addr == bv_unsigned sp + 6 then bytes[6]?
    else if bv_unsigned addr == bv_unsigned sp + 7 then bytes[7]?
    else base_mem addr

theorem stm_at (sp : word) (bytes : List byte) (addr : word) (i : Nat) :
    i < bytes.length → bv_unsigned addr = bv_unsigned sp + (i : Int) → stack_to_mem sp bytes addr = bytes[i]? := by
  intro hi haddr
  unfold stack_to_mem
  rw [haddr]
  have h1 : bv_unsigned sp ≤ bv_unsigned sp + (i : Int) := by omega
  have h2 : bv_unsigned sp + (i : Int) - bv_unsigned sp = (i : Int) := by omega
  have h3 : (i : Int) < (bytes.length : Int) := by omega
  simp only [h1, ite_true, h2, h3, Int.toNat_natCast]

theorem build_stack_starts_with_argc :
    ∀ ph sp argv envp uid hw rnd,
      ∃ rest, build_stack_bytes ph sp argv envp uid hw rnd = word_le8 (nat_to_word argv.length) ++ rest := by
  intro ph sp argv envp uid hw rnd
  simp only [build_stack_bytes, List.append_assoc]
  exact ⟨_, rfl⟩

theorem word_le8_length : ∀ v, (word_le8 v).length = 8 := fun _ => rfl

theorem build_stack_min_length : ∀ ph sp argv envp uid hw rnd, 8 ≤ (build_stack_bytes ph sp argv envp uid hw rnd).length := by
  intro ph sp argv envp uid hw rnd
  obtain ⟨rest, hr⟩ := build_stack_starts_with_argc ph sp argv envp uid hw rnd
  rw [hr, List.length_append, word_le8_length]
  omega

/-- The `i`-th byte of the initial stack memory (`i < 8`) is the `i`-th byte of the little-endian argc. -/
theorem init_first8 :
    ∀ segs init_pc ph init_sp init_rnd argv envp addr (i : Nat) uid hw, i < 8 →
      bv_unsigned addr = bv_unsigned init_sp + (i : Int) →
        (init_machine_state segs init_pc ph init_sp init_rnd argv envp uid hw).ms_mem addr =
          (word_le8 (nat_to_word argv.length))[i]? := by
  intro segs init_pc ph init_sp init_rnd argv envp addr i uid hw hi haddr
  have hmin := build_stack_min_length ph init_sp argv envp uid hw init_rnd
  have hstk : stack_to_mem init_sp (entry_stack_image ph init_sp argv envp uid hw init_rnd) addr =
      (word_le8 (nat_to_word argv.length))[i]? := by
    rw [stack_to_mem_image_in_block _ _ _ _ _ _ _ _ (by unfold entry_block_top; omega),
      stm_at init_sp _ addr i (by omega) haddr]
    obtain ⟨rest, hr⟩ := build_stack_starts_with_argc ph init_sp argv envp uid hw init_rnd
    rw [hr]
    exact List.getElem?_append_left (by rw [word_le8_length]; exact hi)
  show (match stack_to_mem init_sp (entry_stack_image ph init_sp argv envp uid hw init_rnd) addr with
    | some b => some b
    | none =>
      if decide (bv_unsigned init_sp - stack_max_size ≤ bv_unsigned addr) && decide (bv_unsigned addr < bv_unsigned init_sp)
      then some (Z_to_bv 8 0) else none) = _
  rw [hstk]
  cases h : (word_le8 (nat_to_word argv.length))[i]? with
  | some b => rfl
  | none => rw [List.getElem?_eq_none_iff, word_le8_length] at h; omega

theorem actual_mem_is_overlay :
    ∀ segs init_pc ph init_sp init_rnd argv envp uid hw,
      (init_machine_state segs init_pc ph init_sp init_rnd argv envp uid hw).ms_mem =
        overlay_argc_bytes init_sp argv.length (init_machine_state segs init_pc ph init_sp init_rnd argv envp uid hw).ms_mem := by
  intro segs init_pc ph init_sp init_rnd argv envp uid hw
  funext addr
  simp only [overlay_argc_bytes]
  split
  · next h => exact init_first8 segs init_pc ph init_sp init_rnd argv envp addr 0 uid hw (by decide) (by simp at h; omega)
  split
  · next h => exact init_first8 segs init_pc ph init_sp init_rnd argv envp addr 1 uid hw (by decide) (by simp at h; omega)
  split
  · next h => exact init_first8 segs init_pc ph init_sp init_rnd argv envp addr 2 uid hw (by decide) (by simp at h; omega)
  split
  · next h => exact init_first8 segs init_pc ph init_sp init_rnd argv envp addr 3 uid hw (by decide) (by simp at h; omega)
  split
  · next h => exact init_first8 segs init_pc ph init_sp init_rnd argv envp addr 4 uid hw (by decide) (by simp at h; omega)
  split
  · next h => exact init_first8 segs init_pc ph init_sp init_rnd argv envp addr 5 uid hw (by decide) (by simp at h; omega)
  split
  · next h => exact init_first8 segs init_pc ph init_sp init_rnd argv envp addr 6 uid hw (by decide) (by simp at h; omega)
  split
  · next h => exact init_first8 segs init_pc ph init_sp init_rnd argv envp addr 7 uid hw (by decide) (by simp at h; omega)
  rfl

theorem machine_state_eta : ∀ ms : machine_state,
    ms = { ms_regs := ms.ms_regs, ms_fregs := ms.ms_fregs, ms_pc_val := ms.ms_pc_val,
           ms_svc_pending := ms.ms_svc_pending, ms_resv := ms.ms_resv, ms_fcsr := ms.ms_fcsr,
           ms_mem := ms.ms_mem, ms_rom := ms.ms_rom } := fun _ => rfl

/-- The "enumeration state": structural fields from the (argv-independent) initial state, `ms_mem`
    replaced by an overlay with a FREE argc and base. -/
def enum_state (segs : List Segment) (init_pc : Nat) (ph : PhdrInfo) (init_sp : word) (init_rnd : EntryDraw)
    (argc : Nat) (base : word → Option byte) (uid : word) (hw : word) : machine_state :=
  { ms_regs := (init_machine_state segs init_pc ph init_sp init_rnd [] [] uid hw).ms_regs,
    ms_fregs := (init_machine_state segs init_pc ph init_sp init_rnd [] [] uid hw).ms_fregs,
    ms_pc_val := (init_machine_state segs init_pc ph init_sp init_rnd [] [] uid hw).ms_pc_val,
    ms_svc_pending := (init_machine_state segs init_pc ph init_sp init_rnd [] [] uid hw).ms_svc_pending,
    ms_resv := (init_machine_state segs init_pc ph init_sp init_rnd [] [] uid hw).ms_resv,
    ms_fcsr := (init_machine_state segs init_pc ph init_sp init_rnd [] [] uid hw).ms_fcsr,
    ms_mem := overlay_argc_bytes init_sp argc base,
    ms_rom := (init_machine_state segs init_pc ph init_sp init_rnd [] [] uid hw).ms_rom }

/-- Bridge: the real initial state equals the enumeration state at `argc := length argv` and
    `base := its own memory`. -/
theorem init_eq_enum_state :
    ∀ segs init_pc ph init_sp init_rnd argv envp uid hw,
      init_machine_state segs init_pc ph init_sp init_rnd argv envp uid hw =
        enum_state segs init_pc ph init_sp init_rnd argv.length
          (init_machine_state segs init_pc ph init_sp init_rnd argv envp uid hw).ms_mem uid hw := by
  intro segs init_pc ph init_sp init_rnd argv envp uid hw
  unfold enum_state
  rw [← actual_mem_is_overlay]
  rfl

/-! ### Run-level packaging: the two facts, and the equivalence glue -/

/-- The run-level omni judgment of an exit-only binary. -/
theorem exit_omni_run :
    ∀ segs pc ph sp brk0 mb rnd lim code inp F,
      sim_c segs code F (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) = true →
        omni_run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp (exit_post code (in_fs inp)) := by
  intro segs pc ph sp brk0 mb rnd lim code inp F hsim
  exact to_exit_exec segs code _ (init_model (segments_reserved segs) brk0 mb sp lim inp) rfl rfl
    (sim_c_to_exit segs code F _ hsim)

theorem exit_obs_iff :
    ∀ segs pc ph sp brk0 mb rnd lim code inp F,
      sim_c segs code F (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) = true →
        ∀ tr, obs_trace segs (init_config segs pc ph sp brk0 mb rnd lim inp) tr ↔
          is_prefix tr [.ExitEv (bv_and code (Z_to_bv 64 255)) (in_fs inp)] := by
  intro segs pc ph sp brk0 mb rnd lim code inp F hsim tr
  apply exec_obs_iff
  exact exec_conseq segs _ _ _ (exit_omni_run segs pc ph sp brk0 mb rnd lim code inp F hsim)
    (fun _ _ h => ⟨h.1, exits_with_never_errors _ _ _ h.2⟩)

theorem exit_no_error_run :
    ∀ segs pc ph sp brk0 mb rnd lim code inp F,
      sim_c segs code F (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) = true →
        ¬ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp) := by
  intro segs pc ph sp brk0 mb rnd lim code inp F hsim
  exact exec_no_error segs _ (exec_conseq segs _ _ _ (exit_omni_run segs pc ph sp brk0 mb rnd lim code inp F hsim)
    (fun _ _ h => exits_with_never_errors _ _ _ h.2))

/-- The code half of `exit_post`, consumed and pinned. -/
theorem exit_must_exit_with :
    ∀ segs pc ph sp brk0 mb rnd lim code inp F,
      sim_c segs code F (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) = true →
        must_exit_with (bv_and code (Z_to_bv 64 255)) (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp := by
  intro segs pc ph sp brk0 mb rnd lim code inp F hsim
  apply (must_exit_with_iff _ _ _ _ _).2
  exact exec_conseq segs _ _ _ (exit_omni_run segs pc ph sp brk0 mb rnd lim code inp F hsim) (fun _ _ h => h.2)

theorem exit_omni_run_code_unique :
    ∀ segs pc ph sp brk0 mb rnd lim code inp F code',
      sim_c segs code F (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) = true →
        omni_run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp (exits_with code') →
          code' = bv_and code (Z_to_bv 64 255) := by
  intro segs pc ph sp brk0 mb rnd lim code inp F code' hsim hex
  have hrun := exit_omni_run segs pc ph sp brk0 mb rnd lim code inp F hsim
  obtain ⟨tr, o, hm, _, hx⟩ := exec_realizes segs _ _ hrun
  have hx' := exec_sound segs _ _ hex _ _ hm
  cases o with
  | OError _ => exact hx.elim
  | OHalt c' =>
    have e := hx.1.symm.trans hx'.1
    cases e
    rfl

/-- The omni equivalence for two exit-only binaries reaching the same exit code, at the two role
    budgets. -/
theorem exit_omni_strong_equiv :
    ∀ source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd code inp FR FA,
      sim_c source_segs code FR
          (init_machine_state source_segs rpc rph rsp rrnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) = true →
        sim_c target_segs code FA
            (init_machine_state target_segs apc aph asp arnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) = true →
          omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
            (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp := by
  intro source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd code inp FR FA hsource htarget
  refine ⟨?_, .inr ⟨?_, ?_⟩⟩
  · exact coexec_conseq source_segs _ _ _
      (exec_coexec source_segs _ _
        (exit_omni_run source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit code inp FR hsource))
      (fun tr o h => never_errors_covered source_segs _ _ (exits_with_never_errors _ _ _ h.2))
  · apply (trace_equiv_iff_omni _ _ _ _ _ _ _).1
    intro tr
    exact (exit_obs_iff source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit code inp FR hsource tr).trans
      (exit_obs_iff target_segs apc aph asp abrk amb arnd target_alloc_limit code inp FA htarget tr).symm
  · apply (bh_errors_iff _ _ _ _).1
    exact exit_no_error_run target_segs apc aph asp abrk amb arnd target_alloc_limit code inp FA htarget

/-- The `Equivalence`-level equivalence for two exit-only binaries reaching the same exit code. -/
theorem exit_strong_equiv :
    ∀ source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim code inp FR FA,
      sim_c source_segs code FR
          (init_machine_state source_segs rpc rph rsp rrnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) = true →
        sim_c target_segs code FA
            (init_machine_state target_segs apc aph asp arnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) = true →
          modeled (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp) ∧
            equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
              (run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp) := by
  intro source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim code inp FR FA
    hsource htarget
  refine ⟨no_error_run_modeled _ _ _ _ _ _ _ _ _
    (exit_no_error_run source_segs rpc rph rsp rbrk rmb rrnd rlim code inp FR hsource), .inr ⟨?_, ?_⟩⟩
  · intro tr
    exact (exit_obs_iff source_segs rpc rph rsp rbrk rmb rrnd rlim code inp FR hsource tr).trans
      (exit_obs_iff target_segs apc aph asp abrk amb arnd alim code inp FA htarget tr).symm
  · exact exit_no_error_run target_segs apc aph asp abrk amb arnd alim code inp FA htarget

end LPS
