import LPS.Common.AllocSim3
import LPS.Common.ErrEscape
import LPS.LinuxProcessSem.Run5

/-!
# LPS `theories/Common/AllocMixSim.v` (f1006fe8): brk outcome sets with trace-silent erroring branches

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Common/AllocMixSim.v` at f1006fe8 (shared proof library, not the trusted specification
there). `AllocSim.to_outcomes` characterizes a brk-branching run whose every resolution terminates in a
(write buffers, exit code) outcome. A MAY-erroring source (some brk resolutions run into the explicit
error transition while others exit cleanly) does not fit: under the universal source-error rule such a
source does NOT free the target, so its trace set must still be characterized exactly.

`to_outcomes_mix` is `to_outcomes` plus an ERROR LEAF (`tom_fault`): a branch that runs a deterministic
instruction line into an illegal instruction contributes NO outcome and NO events, so the trace set of
the whole tree is still exactly the prefixes of the outcome traces of the surviving outcome set `U`
(nonempty, `alloc_mix_obs_iff`). The equivalence glue (`alloc_mix_strong_equiv`,
`alloc_mix_omni_strong_equiv`) pairs a may-erroring source (`to_outcomes_mix` with set `U`) with a
never-erroring target (`to_outcomes` with the SAME set `U`).

Section `WithSegs`' variable `segs` is the leading explicit argument of `to_outcomes_mix` and the
section's lemmas. Run.v's `reaches_unmodeled_reaches_error`/`no_error_no_unmodeled`, which this file
cites, are ported in LPS/LinuxProcessSem/Run5.lean. The proofs are Lean's.
-/

namespace LPS
open RiscvSemantics OmniRun

/-- `to_outcomes` with erroring branches: from `ms` under `model`, the non-error resolutions produce
    EXACTLY the outcome set `U`, and every other resolution runs a deterministic silent instruction
    line into the explicit error transition. -/
inductive to_outcomes_mix (segs : List Segment) :
    machine_state → Model → ((List (List byte) × word) → Prop) → Prop where
  | tom_out (ms model U) :
      to_outcomes segs ms model U →
      to_outcomes_mix segs ms model U
  | tom_fault (ms ms' model) (U : (List (List byte) × word) → Prop) :
      msteps segs ms ms' →
      ms'.ms_svc_pending = none →
      RiscvSemantics.step segs ms' = .MachineFault →
      (∀ o, ¬ U o) →
      to_outcomes_mix segs ms model U
  | tom_step (ms ms' model U) :
      ms.ms_svc_pending = none →
      RiscvSemantics.step segs ms = .MachineOk ms' →
      to_outcomes_mix segs ms' model U →
      to_outcomes_mix segs ms model U
  | tom_brk (ms model x8) (T : SyscallEffect → Model → (List (List byte) × word) → Prop)
      (U : (List (List byte) × word) → Prop) :
      ms.ms_svc_pending = some x8 →
      bv_unsigned x8 = 214 →
      (∀ eff model' evs, syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) →
        to_outcomes_mix segs (advance_past_svc (apply_effect ms eff)) model' (T eff model')) →
      (∀ o, U o ↔ ∃ eff model' evs, syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ∧ T eff model' o) →
      to_outcomes_mix segs ms model U

/-- Prepend a deterministic instruction run. -/
theorem tom_msteps (segs : List Segment) : ∀ ms ms' model U,
    msteps segs ms ms' → to_outcomes_mix segs ms' model U → to_outcomes_mix segs ms model U := by
  intro ms ms' model U H
  induction H with
  | mst_refl => exact id
  | mst_step ms ms1 ms2 hsvc hstep _ ih => exact fun Ht => .tom_step _ _ _ _ hsvc hstep (ih Ht)

/-- Rewire the outcome set along an extensional equivalence. -/
theorem tom_equiv (segs : List Segment) : ∀ ms model U V,
    to_outcomes_mix segs ms model U → (∀ o, V o ↔ U o) → to_outcomes_mix segs ms model V := by
  intro ms model U V Hto
  induction Hto generalizing V with
  | tom_out ms model U Hout =>
    intro HV; exact .tom_out _ _ _ (tou_equiv segs _ _ _ _ Hout HV)
  | tom_fault ms ms' model U Hm Hsvc Hill HU =>
    intro HV; exact .tom_fault _ _ _ _ Hm Hsvc Hill (fun o Ho => HU o ((HV o).1 Ho))
  | tom_step ms ms' model U Hsvc Hstep _ IH =>
    intro HV; exact .tom_step _ _ _ _ Hsvc Hstep (IH V HV)
  | tom_brk ms model x8 T U Hsvc Hno Hcont HU _ =>
    intro HV; exact .tom_brk ms model x8 T V Hsvc Hno Hcont (fun o => (HV o).trans (HU o))

/-- `tom_brk` specialized to a continuation family indexed by the resolved break value `r` (the mix
    analogue of `AllocSim.tou_brk_r`). -/
theorem tom_brk_r (segs : List Segment) : ∀ ms model x8 (T' : word → (List (List byte) × word) → Prop) U,
    ms.ms_svc_pending = some x8 → bv_unsigned x8 = 214 →
    (∀ r, brk_resolution_ok model (ms_gpr ms 0) r →
      to_outcomes_mix segs
        (advance_past_svc (apply_effect ms
          (mkEffectU r [] (brk_zeros (ms_gpr ms 0) r (m_vmmaps model).vm_brk)
            (brk_unmaps r (m_vmmaps model).vm_brk) [] [])))
        (brk_model (ms_gpr ms 0) r model) (T' r)) →
    (∀ o, U o ↔ ∃ r, brk_resolution_ok model (ms_gpr ms 0) r ∧ T' r o) →
    to_outcomes_mix segs ms model U := by
  intro ms model x8 T' U Hsvc Hno Hcont HU
  refine .tom_brk ms model x8 (fun eff _ => T' eff.eff_ret) U Hsvc Hno ?_ ?_
  · intro eff model' evs Hspec
    obtain ⟨Heff, _, Hok, rfl⟩ := (brk_ok_iff segs ms x8 model eff model' evs Hno).1 Hspec
    have H := Hcont eff.eff_ret Hok
    rw [← Heff] at H
    exact H
  · intro o
    rw [HU]
    constructor
    · rintro ⟨r, Hok, Ht⟩
      exact ⟨_, _, [], brk_ok_intro segs ms x8 model r Hno Hok, Ht⟩
    · rintro ⟨eff, model', evs, Hspec, Ht⟩
      obtain ⟨_, _, Hok, _⟩ := (brk_ok_iff segs ms x8 model eff model' evs Hno).1 Hspec
      exact ⟨eff.eff_ret, Hok, Ht⟩

/-- From a non-syscall state whose step is illegal, no `SNext` transition exists. -/
theorem illegal_no_snext (segs : List Segment) : ∀ ms model evs c',
    m_vm_lazy model = [] → ms.ms_svc_pending = none → RiscvSemantics.step segs ms = .MachineFault →
    ¬ sstep segs (mkCfg ms model) evs (.SNext c') := by
  intro ms model evs c' Hlazy Hsvc Hill Hss
  cases Hss with
  | sstep_instr _ _ _ _ _ _ hacc =>
    rw [mi_account_step_no_lazy segs ms model Hlazy, Hill] at hacc; cases hacc
  | sstep_syscall _ _ _ _ _ _ _ _ h => rw [Hsvc] at h; cases h
  | sstep_exit _ _ _ _ _ _ _ _ h => rw [Hsvc] at h; cases h
  | sstep_killed _ _ _ _ _ _ _ _ h => rw [Hsvc] at h; cases h

/-- Every `star` run inside a deterministic line into an illegal instruction is silent. -/
theorem err_chain_star_silent (segs : List Segment) : ∀ ms ms' model,
    msteps segs ms ms' → m_vm_lazy model = [] → ms'.ms_svc_pending = none →
    RiscvSemantics.step segs ms' = .MachineFault →
    ∀ tr c, star segs (mkCfg ms model) tr c → tr = [] := by
  intro ms ms' model Hm Hlazy
  induction Hm with
  | mst_refl ms0 =>
    intro Hsvc' Hill tr c Hstar
    cases Hstar with
    | star_refl => rfl
    | star_step _ evs c2 _ _ Hss _ => exact absurd Hss (illegal_no_snext segs ms0 model evs c2 Hlazy Hsvc' Hill)
  | mst_step ms0 ms1 ms2 Hsvc Hstep _ IH =>
    intro Hsvc' Hill tr c Hstar
    cases Hstar with
    | star_refl => rfl
    | star_step _ evs c2 tr2 _ Hss Hstar2 =>
      obtain ⟨rfl, Hc2⟩ := sstep_instr_inv segs ms0 model ms1 evs (.SNext c2) Hlazy Hsvc Hstep Hss
      cases Hc2
      exact (List.nil_append _).trans (IH Hsvc' Hill tr2 c Hstar2)

/-- Trace characterization, "only" direction: every `star` trace is either empty or a prefix of an
    outcome trace of the surviving set. -/
theorem tom_star_only (segs : List Segment) : ∀ ms model U,
    to_outcomes_mix segs ms model U → m_halted model = none → m_vm_lazy model = [] →
    ∀ tr c, star segs (mkCfg ms model) tr c →
      tr = [] ∨ ∃ o, U o ∧ is_prefix tr (outcome_trace (m_fs model) o) := by
  intro ms model U Hto
  induction Hto with
  | tom_out ms model U Hout =>
    intro Hh Hlazy tr c Hstar
    exact .inr (to_outcomes_star_only segs ms model U Hout Hh Hlazy tr c Hstar)
  | tom_fault ms ms' model U Hm Hsvc Hill _ =>
    intro _ Hlazy tr c Hstar
    exact .inl (err_chain_star_silent segs ms ms' model Hm Hlazy Hsvc Hill tr c Hstar)
  | tom_step ms ms' model U Hsvc Hstep _ IH =>
    intro Hh Hlazy tr c Hstar
    cases Hstar with
    | star_refl => exact .inl rfl
    | star_step _ evs c2 tr2 _ Hss Hstar2 =>
      obtain ⟨rfl, Hc2⟩ := sstep_instr_inv segs ms model ms' evs (.SNext c2) Hlazy Hsvc Hstep Hss
      cases Hc2
      rw [List.nil_append]
      exact IH Hh Hlazy tr2 c Hstar2
  | tom_brk ms model x8 T U Hsvc Hno _ HU IH =>
    intro Hh Hlazy tr c Hstar
    cases Hstar with
    | star_refl => exact .inl rfl
    | star_step _ evs c2 tr2 _ Hss Hstar2 =>
      obtain ⟨eff, model', Hspec, rfl, Hc2⟩ := sstep_brk_inv segs ms model x8 evs (.SNext c2) Hh Hlazy Hsvc Hno Hss
      cases Hc2
      obtain ⟨_, Hh', Hfs, _, Hlazy'⟩ := brk_step_shape segs ms x8 model eff model' [] Hh Hlazy Hno Hspec
      rw [List.nil_append]
      rcases IH eff model' [] Hspec Hh' (Hlazy'.trans Hlazy) tr2 c Hstar2 with H | ⟨o, Ho, Hp⟩
      · exact .inl H
      · refine .inr ⟨o, (HU o).2 ⟨eff, model', [], Hspec, Ho⟩, ?_⟩
        rw [Hfs] at Hp; exact Hp

/-- Trace characterization, "admits" direction: every outcome in the surviving set is realized by a
    full run. -/
theorem tom_star_admits (segs : List Segment) : ∀ ms model U,
    to_outcomes_mix segs ms model U → m_halted model = none → m_vm_lazy model = [] →
    ∀ o, U o → ∃ c, star segs (mkCfg ms model) (outcome_trace (m_fs model) o) c := by
  intro ms model U Hto
  induction Hto with
  | tom_out ms model U Hout =>
    intro Hh Hlazy o Ho
    exact to_outcomes_star_admits segs ms model U Hout Hh Hlazy o Ho
  | tom_fault ms ms' model U _ _ _ HU =>
    intro _ _ o Ho; exact absurd Ho (HU o)
  | tom_step ms ms' model U Hsvc Hstep _ IH =>
    intro Hh Hlazy o Ho
    obtain ⟨c, Hstar⟩ := IH Hh Hlazy o Ho
    have Hss : sstep segs (mkCfg ms model) [] (.SNext (mkCfg ms' model)) := by
      refine .sstep_instr ms model ms' model Hh Hsvc ?_
      rw [mi_account_step_no_lazy segs ms model Hlazy, Hstep]
    exact ⟨c, by simpa using star.star_step _ _ _ _ _ Hss Hstar⟩
  | tom_brk ms model x8 T U Hsvc Hno _ HU IH =>
    intro Hh Hlazy o Ho
    obtain ⟨eff, model', evs, Hspec, Ht⟩ := (HU o).1 Ho
    obtain ⟨rfl, Hh', Hfs, _, Hlazy'⟩ := brk_step_shape segs ms x8 model eff model' evs Hh Hlazy Hno Hspec
    obtain ⟨c, Hstar⟩ := IH eff model' [] Hspec Hh' (Hlazy'.trans Hlazy) o Ht
    have Hss := sstep.sstep_syscall ms model x8 eff model' model' [] Hh Hsvc Hspec Hh'
      (materialize_model_accesses_no_lazy _ _ (Hlazy'.trans Hlazy))
    have H := star.star_step _ _ _ _ _ Hss Hstar
    rw [List.nil_append, Hfs] at H
    exact ⟨c, H⟩

/-- Coverage: a may-erroring brk tree is nonetheless fully MODELED: the surviving subtree never errors,
    the erroring subtree ends in a genuine `MachineFault`, ordinary instructions are `MachineOk`, and brk
    is receptive. -/
theorem tom_no_unmodeled (segs : List Segment) : ∀ ms model U,
    to_outcomes_mix segs ms model U → m_halted model = none → m_vm_lazy model = [] →
    ¬ reaches_unmodeled segs (mkCfg ms model) := by
  intro ms model U Hto
  induction Hto with
  | tom_out ms model U Hout =>
    intro Hh Hlazy
    exact no_error_no_unmodeled segs _ (to_outcomes_no_error segs ms model U Hout Hh Hlazy)
  | tom_fault ms ms' model U Hm Hsvc Hill _ =>
    intro _ Hlazy
    exact msteps_fault_no_unmodeled segs ms ms' model Hm Hlazy Hsvc Hill
  | tom_step ms ms' model U Hsvc Hstep _ IH =>
    intro Hh Hlazy
    exact instr_no_unmodeled segs ms ms' model Hlazy Hsvc Hstep (IH Hh Hlazy)
  | tom_brk ms model x8 T U Hsvc Hno _ _ IH =>
    intro Hh Hlazy
    rintro ⟨tr, c, Hstar, Hun⟩
    cases Hstar with
    | star_refl =>
      rcases Hun with ⟨_, ⟨Hsvc', _⟩ | ⟨x8', Hsvc', Herr⟩⟩
      · change ms.ms_svc_pending = _ at Hsvc'
        rw [Hsvc] at Hsvc'; cases Hsvc'
      · change ms.ms_svc_pending = _ at Hsvc'
        rw [Hsvc] at Hsvc'; cases Hsvc'
        exact brk_no_unmodeled segs ms x8 model Hno Herr
    | star_step _ evs c2 tr2 _ Hss Hstar2 =>
      obtain ⟨eff, model', Hspec, _, Hc2⟩ := sstep_brk_inv segs ms model x8 evs (.SNext c2) Hh Hlazy Hsvc Hno Hss
      cases Hc2
      obtain ⟨_, Hh', _, _, Hlazy'⟩ := brk_step_shape segs ms x8 model eff model' [] Hh Hlazy Hno Hspec
      exact IH eff model' [] Hspec Hh' (Hlazy'.trans Hlazy) ⟨tr2, c, Hstar2, Hun⟩

/-! ### Run-level packaging and the equivalence glue -/

/-- The trace set of a may-erroring brk tree with a NONEMPTY surviving outcome set `U` is exactly the
    prefixes of `U`'s outcome traces (an erroring branch contributes only the empty trace, a prefix of
    every outcome trace). -/
theorem alloc_mix_obs_iff : ∀ segs pc ph sp brk0 mb rnd lim inp U,
    to_outcomes_mix segs (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved segs) brk0 mb sp lim inp) U →
    (∃ o, U o) →
    ∀ tr, obs_trace segs (init_config segs pc ph sp brk0 mb rnd lim inp) tr ↔
      ∃ o, U o ∧ is_prefix tr (outcome_trace (in_fs inp) o) := by
  intro segs pc ph sp brk0 mb rnd lim inp U Hto Hne tr
  constructor
  · rintro ⟨tr', c, Hstar, Hp⟩
    rcases tom_star_only segs _ _ U Hto rfl rfl tr' c Hstar with Htr' | ⟨o, Ho, Hp'⟩
    · subst Htr'
      obtain ⟨o, Ho⟩ := Hne
      refine ⟨o, Ho, ?_⟩
      cases tr with
      | nil => exact is_prefix_nil _
      | cons _ _ => exact Hp.elim
    · exact ⟨o, Ho, is_prefix_trans _ _ _ Hp Hp'⟩
  · rintro ⟨o, Ho, Hp⟩
    obtain ⟨c, Hstar⟩ := tom_star_admits segs _ _ U Hto rfl rfl o Ho
    exact ⟨_, c, Hstar, Hp⟩

/-- The `Equivalence`-level glue: a MAY-erroring source brk tree whose surviving outcome set is the
    (nonempty) `U`, against a never-erroring target realizing the SAME `U`: exact trace-set equality
    plus target no-error. -/
theorem alloc_mix_strong_equiv :
    ∀ source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim U inp,
      to_outcomes_mix source_segs
        (init_machine_state source_segs rpc rph rsp rrnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
        (init_model (segments_reserved source_segs) rbrk rmb rsp rlim inp) U →
      to_outcomes target_segs
        (init_machine_state target_segs apc aph asp arnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
        (init_model (segments_reserved target_segs) abrk amb asp alim inp) U →
      (∃ o, U o) →
      modeled (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp) ∧
        equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
          (run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp) := by
  intro source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim U inp
    Hsource Htarget Hne
  refine ⟨tom_no_unmodeled source_segs _ _ U Hsource rfl rfl, .inr ⟨?_, ?_⟩⟩
  · intro tr
    exact (alloc_mix_obs_iff source_segs rpc rph rsp rbrk rmb rrnd rlim inp U Hsource Hne tr).trans
      (alloc_obs_iff target_segs apc aph asp abrk amb arnd alim inp U Htarget tr).symm
  · exact alloc_no_error_run target_segs apc aph asp abrk amb arnd alim inp U Htarget

/-- The omni equivalence for a may-faulting brk mix against a never-faulting target with the same
    outcome set, at the two role budgets: the source is COVERED (its faults are modeled crashes) though
    not error-free, and the trace sets agree. Proved through `covered_iff`. -/
theorem alloc_mix_omni_strong_equiv :
    ∀ source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd U inp,
      to_outcomes_mix source_segs
        (init_machine_state source_segs rpc rph rsp rrnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
        (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp) U →
      to_outcomes target_segs
        (init_machine_state target_segs apc aph asp arnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
        (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp) U →
      (∃ o, U o) →
      omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
        (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp := by
  intro source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd U inp Hsource Htarget Hne
  refine ⟨(covered_iff source_segs _).1 (tom_no_unmodeled source_segs _ _ U Hsource rfl rfl), .inr ⟨?_, ?_⟩⟩
  · apply (trace_equiv_iff_omni _ _ _ _ _ _ _).1
    intro tr
    exact (alloc_mix_obs_iff source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp U Hsource Hne tr).trans
      (alloc_obs_iff target_segs apc aph asp abrk amb arnd target_alloc_limit inp U Htarget tr).symm
  · apply (bh_errors_iff _ _ _ _).1
    exact alloc_no_error_run target_segs apc aph asp abrk amb arnd target_alloc_limit inp U Htarget

end LPS
