import LPS.Common.CatSim2

/-!
# LPS `theories/Common/CatSim.v` (f1006fe8), part 3: the run level, the channel-parametric relation

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Common/CatSim.v` at f1006fe8 (shared proof library, not the trusted specification
there), after `End WithSegs` (CatSim.v:786-1253): the run-level packaging (`cat_omni_run_te`,
`cat_obs_iff_te`, `cat_no_error_run_te`, `cat_must_exit_with_te`, `cat_omni_run_te_code_unique`,
`cat_omni_strong_equiv_te`, `cat_strong_equiv_te`) and the channel-parametric `to_wexit_ch` with
`msteps_to_wexit_ch`, `to_wexit_ch_1`, `wevents_ch_1`. Conventions as CatSim1; `fdchan`,
`init_model_fdchan2` and the `write_ch_*` lemmas are in CatSim1, `sstep_write_ch_inv` in CatSim2.
Section `WithSegsCh`' variables `segs fd` are the leading explicit arguments of `to_wexit_ch` (`ch`
is not used by it).
-/

namespace LPS
open RiscvSemantics OmniRun

theorem init_model_fd1chan : ∀ reserved brk0 mb sp lim inp, fd1chan (init_model reserved brk0 mb sp lim inp) :=
  fun _ _ _ _ _ _ => rfl

/-! ### `to_wexit`-based entry points -/

/-- The run-level omni judgment of a write-then-exit binary. -/
theorem cat_omni_run_te :
    ∀ segs pc ph sp brk0 mb rnd lim inp bufs code,
      to_wexit segs (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) bufs code →
        bufs_modeled bufs →
          omni_run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp (wexit_post bufs code (in_fs inp)) := by
  intro segs pc ph sp brk0 mb rnd lim inp bufs code hte hbm
  exact to_wexit_exec segs _ bufs code hte (init_model (segments_reserved segs) brk0 mb sp lim inp) rfl rfl rfl hbm

theorem cat_obs_iff_te :
    ∀ segs pc ph sp brk0 mb rnd lim inp bufs code,
      to_wexit segs (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) bufs code →
        bufs_modeled bufs →
          ∀ tr, obs_trace segs (init_config segs pc ph sp brk0 mb rnd lim inp) tr ↔
            ∃ full, wpick (Z_to_bv 64 1) bufs full ∧ is_prefix tr (full ++ [.ExitEv code (in_fs inp)]) := by
  intro segs pc ph sp brk0 mb rnd lim inp bufs code hte hbm tr
  constructor
  · rintro ⟨tr', c, hstar, hp⟩
    obtain ⟨full, hw, hpref⟩ := to_wexit_star_only segs _ bufs code hte (init_model (segments_reserved segs) brk0 mb sp lim inp) rfl rfl rfl hbm tr' c hstar
    exact ⟨full, hw, is_prefix_trans _ _ _ hp hpref⟩
  · rintro ⟨full, hw, hp⟩
    obtain ⟨c, hstar⟩ := to_wexit_star_admits segs _ bufs code hte (init_model (segments_reserved segs) brk0 mb sp lim inp) full rfl rfl rfl hbm hw
    exact ⟨_, c, hstar, hp⟩

theorem cat_no_error_run_te :
    ∀ segs pc ph sp brk0 mb rnd lim inp bufs code,
      to_wexit segs (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) bufs code →
        bufs_modeled bufs → ¬ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp) := by
  intro segs pc ph sp brk0 mb rnd lim inp bufs code hte hbm
  exact exec_no_error segs _ (exec_conseq segs _ _ _ (cat_omni_run_te segs pc ph sp brk0 mb rnd lim inp bufs code hte hbm)
    (fun _ _ h => exits_with_never_errors _ _ _ h.2))

/-- The code half of `wexit_post`, consumed and pinned. -/
theorem cat_must_exit_with_te :
    ∀ segs pc ph sp brk0 mb rnd lim inp bufs code,
      to_wexit segs (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) bufs code →
        bufs_modeled bufs → must_exit_with code (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp := by
  intro segs pc ph sp brk0 mb rnd lim inp bufs code hte hbm
  apply (must_exit_with_iff _ _ _ _ _).2
  exact exec_conseq segs _ _ _ (cat_omni_run_te segs pc ph sp brk0 mb rnd lim inp bufs code hte hbm) (fun _ _ h => h.2)

theorem cat_omni_run_te_code_unique :
    ∀ segs pc ph sp brk0 mb rnd lim inp bufs code code',
      to_wexit segs (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) bufs code →
        bufs_modeled bufs → omni_run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp (exits_with code') →
          code' = code := by
  intro segs pc ph sp brk0 mb rnd lim inp bufs code code' hte hbm hex
  have hrun := cat_omni_run_te segs pc ph sp brk0 mb rnd lim inp bufs code hte hbm
  obtain ⟨tr, o, hm, _, hx⟩ := exec_realizes segs _ _ hrun
  have hx' := exec_sound segs _ _ hex _ _ hm
  cases o with
  | OError _ => exact hx.elim
  | OHalt c' =>
    have e := hx'.1.symm.trans hx.1
    cases e
    rfl

/-- The omni equivalence for two exit-after-writes binaries whose `to_wexit` derivations emit the same
    buffers and exit code, at the two role budgets. -/
theorem cat_omni_strong_equiv_te :
    ∀ source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd bufs code inp,
      to_wexit source_segs
          (init_machine_state source_segs rpc rph rsp rrnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) bufs code →
        to_wexit target_segs
            (init_machine_state target_segs apc aph asp arnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) bufs code →
          bufs_modeled bufs →
            omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
              (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp := by
  intro source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd bufs code inp hsource htarget hbm
  refine ⟨?_, .inr ⟨?_, ?_⟩⟩
  · exact coexec_conseq source_segs _ _ _
      (exec_coexec source_segs _ _
        (cat_omni_run_te source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp bufs code hsource hbm))
      (fun tr o h => never_errors_covered source_segs _ _ (exits_with_never_errors _ _ _ h.2))
  · apply (trace_equiv_iff_omni _ _ _ _ _ _ _).1
    intro tr
    exact (cat_obs_iff_te source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp bufs code hsource hbm tr).trans
      (cat_obs_iff_te target_segs apc aph asp abrk amb arnd target_alloc_limit inp bufs code htarget hbm tr).symm
  · apply (bh_errors_iff _ _ _ _).1
    exact cat_no_error_run_te target_segs apc aph asp abrk amb arnd target_alloc_limit inp bufs code htarget hbm

/-- The `Equivalence`-level equivalence for two exit-after-writes binaries whose `to_wexit` derivations
    emit the same buffers and exit code: both denote the same set of delivery choices. -/
theorem cat_strong_equiv_te :
    ∀ source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim bufs code inp,
      to_wexit source_segs
          (init_machine_state source_segs rpc rph rsp rrnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) bufs code →
        to_wexit target_segs
            (init_machine_state target_segs apc aph asp arnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) bufs code →
          bufs_modeled bufs →
            modeled (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp) ∧
              equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
                (run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp) := by
  intro source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim bufs code inp
    hsource htarget hbm
  refine ⟨no_error_run_modeled _ _ _ _ _ _ _ _ _
    (cat_no_error_run_te source_segs rpc rph rsp rbrk rmb rrnd rlim inp bufs code hsource hbm), .inr ⟨?_, ?_⟩⟩
  · intro tr
    exact (cat_obs_iff_te source_segs rpc rph rsp rbrk rmb rrnd rlim inp bufs code hsource hbm tr).trans
      (cat_obs_iff_te target_segs apc aph asp abrk amb arnd alim inp bufs code htarget hbm tr).symm
  · exact cat_no_error_run_te target_segs apc aph asp abrk amb arnd alim inp bufs code htarget hbm

/-! ### The channel-parametric `to_wexit` (CatSim.v's `Section WithSegsCh`) -/

inductive to_wexit_ch (segs : List Segment) (fd : word) : machine_state → List (List byte) → word → Prop where
  | twc_exit (ms x8) :
      ms.ms_svc_pending = some x8 → is_exit_no x8 →
      to_wexit_ch segs fd ms [] (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
  | twc_write (ms x8 buf bufs code) :
      ms.ms_svc_pending = some x8 → bv_unsigned x8 = 64 → ms_gpr ms 0 = fd →
      ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf → 1 ≤ buf.length →
      (∀ n, 1 ≤ n → n ≤ buf.length →
        to_wexit_ch segs fd (advance_past_svc (set_gpr0 ms (len_word (buf.take n)))) bufs code) →
      to_wexit_ch segs fd ms (buf :: bufs) code
  | twc_step (ms ms' bufs code) :
      ms.ms_svc_pending = none → RiscvSemantics.step segs ms = .MachineOk ms' → to_wexit_ch segs fd ms' bufs code →
      to_wexit_ch segs fd ms bufs code

theorem msteps_to_wexit_ch (segs : List Segment) (fd : word) :
    ∀ ms ms' bufs code, msteps segs ms ms' → to_wexit_ch segs fd ms' bufs code → to_wexit_ch segs fd ms bufs code := by
  intro ms ms' bufs code h
  induction h with
  | mst_refl => exact id
  | mst_step ms ms1 ms2 hsvc hstep _ ih => exact fun hw => .twc_step _ _ _ _ hsvc hstep (ih hw)

/-- The fd-1 development IS the instance `fd = ch = 1`. -/
theorem to_wexit_ch_1 : ∀ segs ms bufs code, to_wexit segs ms bufs code → to_wexit_ch segs (Z_to_bv 64 1) ms bufs code := by
  intro segs ms bufs code h
  induction h with
  | tw_exit ms x8 h1 h2 => exact .twc_exit ms x8 h1 h2
  | tw_write ms x8 buf bufs code h1 h2 h3 h4 h5 _ ih => exact .twc_write ms x8 buf bufs code h1 h2 h3 h4 h5 ih
  | tw_step ms ms' bufs code h1 h2 _ ih => exact .twc_step ms ms' bufs code h1 h2 ih

theorem wevents_ch_1 : ∀ bufs, wevents_ch (Z_to_bv 64 1) bufs = wevents bufs := by
  intro bufs
  induction bufs with
  | nil => rfl
  | cons b bs ih => simp only [wevents_ch, wevents, ih]

end LPS
