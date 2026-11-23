import LPS.Common.AllocSim2

/-!
# LPS `theories/Common/AllocSim.v` (f1006fe8), part 3: `to_outcomes`, the omni reading, the run level

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Common/AllocSim.v` at f1006fe8 (shared proof library, not the trusted specification
there), `Section WithSegs` and after: `to_outcomes segs ms model U` (from machine state `ms` and model
`model`, the reachable set of (bufs, code) outcomes is EXACTLY `U`; leaves are `WallSim.to_wallexit`
retry loops, interior nodes are brk syscalls branching over every admissible resolution), its
structural lemmas (`tou_msteps`, `forget_vm_ranges_frame`, `brk_step_shape`, `sstep_brk_inv`), the
omni reading `to_outcomes_exec` with its corollaries (`_no_other_exit`, `_not_silent`, `_star_only`,
`_star_admits`, `_no_error`), the ergonomic constructors (`tou_brk_r`, `tou_wexit_eq`, `tou_equiv`),
then after `End WithSegs` the run-level packaging (`alloc_omni_run`, `alloc_obs_iff`,
`alloc_no_error_run`) and the equivalence glue (`alloc_omni_strong_equiv`, `alloc_strong_equiv`): two
binaries with the SAME outcome set are observably equivalent.

Conventions as AllocSim1. Section `WithSegs`' variable `segs` is the leading explicit argument of
`to_outcomes` and of the lemmas inside the section. The proofs are Lean's.
-/

namespace LPS
open RiscvSemantics OmniRun

/-! ### `to_outcomes`: the exact outcome set of a brk-branching run -/

inductive to_outcomes (segs : List Segment) :
    machine_state → Model → ((List (List byte) × word) → Prop) → Prop where
  | tou_wexit (ms model bufs code) (U : (List (List byte) × word) → Prop) :
      fd1chan model →
      to_wallexit segs (Z_to_bv 64 1) bufs code ms →
      bufs_modeled bufs →
      (∀ o, U o ↔ o = (bufs, code)) →
      to_outcomes segs ms model U
  | tou_step (ms ms' model U) :
      ms.ms_svc_pending = none →
      RiscvSemantics.step segs ms = .MachineOk ms' →
      to_outcomes segs ms' model U →
      to_outcomes segs ms model U
  | tou_brk (ms model x8) (T : SyscallEffect → Model → (List (List byte) × word) → Prop)
      (U : (List (List byte) × word) → Prop) :
      ms.ms_svc_pending = some x8 →
      bv_unsigned x8 = 214 →
      (∀ eff model' evs, syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) →
        to_outcomes segs (advance_past_svc (apply_effect ms eff)) model' (T eff model')) →
      (∀ o, U o ↔ ∃ eff model' evs, syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ∧ T eff model' o) →
      to_outcomes segs ms model U

/-- Prepend a deterministic instruction run. -/
theorem tou_msteps (segs : List Segment) : ∀ ms ms' model U,
    msteps segs ms ms' → to_outcomes segs ms' model U → to_outcomes segs ms model U := by
  intro ms ms' model U H
  induction H with
  | mst_refl => exact id
  | mst_step ms ms1 ms2 hsvc hstep _ ih => exact fun Ht => .tou_step _ _ _ _ hsvc hstep (ih Ht)

/-- Forgetting VM ranges preserves the non-VM state and cannot introduce sparse mappings. -/
theorem forget_vm_ranges_frame : ∀ ranges model,
    m_halted (forget_vm_ranges ranges model) = m_halted model ∧
    m_fs (forget_vm_ranges ranges model) = m_fs model ∧
    m_fds (forget_vm_ranges ranges model) = m_fds model ∧
    (m_vm_lazy model = [] → m_vm_lazy (forget_vm_ranges ranges model) = []) := by
  intro ranges
  induction ranges with
  | nil => intro model; exact ⟨rfl, rfl, rfl, id⟩
  | cons p ranges IH =>
    intro model
    obtain ⟨a, n⟩ := p
    obtain ⟨Hhalt, Hfs, Hfds, Hlazy⟩ := IH (vm_forget_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n) model)
    refine ⟨Hhalt, Hfs, Hfds, fun Hempty => Hlazy ?_⟩
    show maps_subtract (m_vm_lazy model) _ _ = []
    rw [Hempty]; rfl

/-- brk transitions keep the model running and the fs/fds untouched; from an eager-only model,
    lifecycle cleanup also leaves no lazy mappings. -/
theorem brk_step_shape (segs : List Segment) : ∀ ms x8 model eff model' evs,
    m_halted model = none → m_vm_lazy model = [] → bv_unsigned x8 = 214 →
    syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) →
    evs = [] ∧ m_halted model' = none ∧ m_fs model' = m_fs model ∧ m_fds model' = m_fds model ∧
      m_vm_lazy model' = m_vm_lazy model := by
  intro ms x8 model eff model' evs Hh Hlazy Hno Hs
  obtain ⟨_, rfl, _, rfl⟩ := (brk_ok_iff segs ms x8 model eff model' evs Hno).1 Hs
  obtain ⟨Hhalt, Hfs, Hfds, Hlazy'⟩ := forget_vm_ranges_frame (brk_unmaps eff.eff_ret (m_vmmaps model).vm_brk)
    (with_vmmaps (brk_model_next (m_vmmaps model) (ms_gpr ms 0) eff.eff_ret) model)
  refine ⟨rfl, Hhalt.trans Hh, Hfs, Hfds, ?_⟩
  rw [Hlazy]
  exact Hlazy' Hlazy

/-- One-step inversion at a brk ecall. -/
theorem sstep_brk_inv (segs : List Segment) : ∀ ms model x8 evs st,
    m_halted model = none → m_vm_lazy model = [] → ms.ms_svc_pending = some x8 → bv_unsigned x8 = 214 →
    sstep segs (mkCfg ms model) evs st →
    ∃ eff model', syscall_spec (sys_input segs ms x8) model (Ok eff model' []) ∧ evs = [] ∧
      st = .SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model') := by
  intro ms model x8 evs st Hh Hlazy Hsvc Hno Hss
  have Hx : ∀ y, ms.ms_svc_pending = some y → y = x8 := by
    intro y h; rw [Hsvc] at h; exact (Option.some.inj h).symm
  cases Hss with
  | sstep_instr _ _ _ _ _ h _ => rw [Hsvc] at h; cases h
  | sstep_instr_fault _ _ _ h _ => rw [Hsvc] at h; cases h
  | sstep_instr_unmodeled _ _ _ h _ => rw [Hsvc] at h; cases h
  | sstep_syscall _ _ y eff model' model'' _ _ hsvc hspec _ hmat =>
    rw [Hx y hsvc] at hspec
    obtain ⟨Hevs, _, _, _, Hlazy'⟩ := brk_step_shape segs ms _ model _ _ _ Hh Hlazy Hno hspec
    subst Hevs
    rw [materialize_model_accesses_no_lazy _ _ (Hlazy'.trans Hlazy)] at hmat
    cases hmat
    exact ⟨eff, model', hspec, rfl, rfl⟩
  | sstep_syscall_materialization_fault _ _ y _ _ _ _ hsvc hspec _ hmat =>
    rw [Hx y hsvc] at hspec
    obtain ⟨_, _, _, _, Hlazy'⟩ := brk_step_shape segs ms _ model _ _ _ Hh Hlazy Hno hspec
    rw [materialize_model_accesses_no_lazy _ _ (Hlazy'.trans Hlazy)] at hmat
    cases hmat
  | sstep_exit _ _ y _ _ _ _ _ hsvc hspec hhalt _ =>
    rw [Hx y hsvc] at hspec
    obtain ⟨_, Hm, _⟩ := brk_step_shape segs ms _ model _ _ _ Hh Hlazy Hno hspec
    rw [Hm] at hhalt; cases hhalt
  | sstep_killed _ _ y _ _ _ _ _ hsvc hspec hkill =>
    rw [Hx y hsvc] at hspec
    obtain ⟨_, Hm, _⟩ := brk_step_shape segs ms _ model _ _ _ Hh Hlazy Hno hspec
    rw [m_killed_of_m_halted_none _ Hm] at hkill; cases hkill
  | sstep_syscall_unmodeled _ _ y _ hsvc hspec =>
    rw [Hx y hsvc] at hspec
    exact absurd hspec (brk_no_unmodeled segs ms x8 model Hno)

/-! ### Trace characterization -/

def outcome_trace (fs : Fs) (o : List (List byte) × word) : List event :=
  wevents o.1 ++ [.ExitEv o.2 fs]

/-- The omni reading of a brk-branching run: every execution ends by halting with one of the outcomes,
    having emitted exactly that outcome's trace. -/
def outcomes_post (fs : Fs) (U : (List (List byte) × word) → Prop) : post :=
  fun tr o => ∃ out, U out ∧ tr = outcome_trace fs out ∧ exits_with out.2 tr o

theorem to_outcomes_exec (segs : List Segment) : ∀ ms model U,
    to_outcomes segs ms model U → m_halted model = none → m_vm_lazy model = [] →
    OmniRun.exec segs (mkCfg ms model) (outcomes_post (m_fs model) U) := by
  intro ms model U Hto
  induction Hto with
  | tou_wexit ms model bufs code U Hfd Hte Hbm HU =>
    intro Hh Hlazy
    refine exec_conseq segs _ _ _ (to_wallexit_exec segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1 bufs code ms model
      Hh Hlazy (fd1chan_fdchan model Hfd) Hbm Hte) ?_
    rintro tr o ⟨Heq, Hx⟩
    refine ⟨(bufs, code), (HU _).2 rfl, ?_, Hx⟩
    rw [Heq, wevents_ch_fd1]; rfl
  | tou_step ms ms' model U Hsvc Hstep _ IH =>
    intro Hh Hlazy
    refine exec_step_only segs _ _ [] (mkCfg ms' model) ?_
      (fun evs st Hss => sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss) ?_
    · refine .sstep_instr ms model ms' model Hh Hsvc ?_
      rw [mi_account_step_no_lazy segs ms model Hlazy, Hstep]
    · exact exec_conseq segs _ _ _ (IH Hh Hlazy) (fun tr o h => by simpa using h)
  | tou_brk ms model x8 T U Hsvc Hno _ HU IH =>
    intro Hh Hlazy
    refine .exec_step _ _ Hh ?_ ?_ ?_
    · obtain ⟨eff, model', Hspec⟩ := brk_receptive segs ms x8 model Hno
      obtain ⟨_, Hh', _, _, Hlazy'⟩ := brk_step_shape segs ms x8 model eff model' [] Hh Hlazy Hno Hspec
      exact ⟨[], _, .sstep_syscall ms model x8 eff model' model' [] Hh Hsvc Hspec Hh'
        (materialize_model_accesses_no_lazy _ _ (Hlazy'.trans Hlazy))⟩
    · intro evs Hss
      obtain ⟨_, _, _, _, Habs⟩ := sstep_brk_inv segs ms model x8 evs .SError Hh Hlazy Hsvc Hno Hss
      cases Habs
    · intro evs c' Hss
      obtain ⟨eff, model', Hspec, rfl, Hc'⟩ := sstep_brk_inv segs ms model x8 evs (.SNext c') Hh Hlazy Hsvc Hno Hss
      cases Hc'
      obtain ⟨_, Hh', Hfs, _, Hlazy'⟩ := brk_step_shape segs ms x8 model eff model' [] Hh Hlazy Hno Hspec
      refine exec_conseq segs _ _ _ (IH eff model' [] Hspec Hh' (Hlazy'.trans Hlazy)) ?_
      rintro tr o ⟨out, Hout, Heq, Hx⟩
      refine ⟨out, (HU out).2 ⟨eff, model', [], Hspec, Hout⟩, ?_, Hx⟩
      rw [List.nil_append, Heq, Hfs]

/-- Bites: no exit code outside the outcome set. -/
theorem to_outcomes_no_other_exit (segs : List Segment) : ∀ ms model U,
    to_outcomes segs ms model U → m_halted model = none → m_vm_lazy model = [] →
    ∀ code', (∀ o, U o → o.2 ≠ code') → ¬ OmniRun.exec segs (mkCfg ms model) (exits_with code') := by
  intro ms model U Hto Hh Hlazy code' Hne Hex
  obtain ⟨tr, o, Hm, out, Hout, _, Hx⟩ := exec_realizes segs _ _ (to_outcomes_exec segs ms model U Hto Hh Hlazy)
  have Hx' := exec_sound segs _ _ Hex _ _ Hm
  cases o with
  | OError _ => exact Hx.elim
  | OHalt c' =>
    have e := Hx.1.symm.trans Hx'.1
    cases e
    exact Hne out Hout rfl

/-- ... and no silence. -/
theorem to_outcomes_not_silent (segs : List Segment) : ∀ ms model U,
    to_outcomes segs ms model U → m_halted model = none → m_vm_lazy model = [] →
    ¬ cosafe segs (mkCfg ms model) (fun tr => tr = []) := by
  intro ms model U Hto Hh Hlazy Hc
  obtain ⟨tr, o, Hm, out, _, Heq, Hx⟩ := exec_realizes segs _ _ (to_outcomes_exec segs ms model U Hto Hh Hlazy)
  cases o with
  | OError _ => exact Hx.elim
  | OHalt c' =>
    have Hnil := cosafe_star segs _ _ _ _ Hc (mexec_halt_star segs _ _ _ Hm c' rfl).1
    rw [Heq] at Hnil
    simp [outcome_trace] at Hnil

theorem to_outcomes_star_only (segs : List Segment) : ∀ ms model U,
    to_outcomes segs ms model U → m_halted model = none → m_vm_lazy model = [] →
    ∀ tr c, star segs (mkCfg ms model) tr c → ∃ o, U o ∧ is_prefix tr (outcome_trace (m_fs model) o) := by
  intro ms model U Hto Hh Hlazy tr c Hstar
  obtain ⟨tr', o, _, out, Hout, Heq, _⟩ := exec_realizes segs _ _
    (exec_star segs _ _ _ _ (to_outcomes_exec segs ms model U Hto Hh Hlazy) Hstar)
  refine ⟨out, Hout, ?_⟩
  rw [← Heq]
  exact is_prefix_app _ _

theorem to_outcomes_star_admits (segs : List Segment) : ∀ ms model U,
    to_outcomes segs ms model U → m_halted model = none → m_vm_lazy model = [] →
    ∀ o, U o → ∃ c, star segs (mkCfg ms model) (outcome_trace (m_fs model) o) c := by
  intro ms model U Hto
  induction Hto with
  | tou_wexit ms model bufs code U Hfd Hte Hbm HU =>
    intro Hh Hlazy o Ho
    cases (HU o).1 Ho
    obtain ⟨c, Hs⟩ := to_wallexit_star_admits segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1 bufs code ms model
      Hh Hlazy (fd1chan_fdchan model Hfd) Hbm Hte
    rw [wevents_ch_fd1] at Hs
    exact ⟨c, Hs⟩
  | tou_step ms ms' model U Hsvc Hstep _ IH =>
    intro Hh Hlazy o Ho
    obtain ⟨c, Hstar⟩ := IH Hh Hlazy o Ho
    have Hss : sstep segs (mkCfg ms model) [] (.SNext (mkCfg ms' model)) := by
      refine .sstep_instr ms model ms' model Hh Hsvc ?_
      rw [mi_account_step_no_lazy segs ms model Hlazy, Hstep]
    exact ⟨c, by simpa using star.star_step _ _ _ _ _ Hss Hstar⟩
  | tou_brk ms model x8 T U Hsvc Hno _ HU IH =>
    intro Hh Hlazy o Ho
    obtain ⟨eff, model', evs, Hspec, Ht⟩ := (HU o).1 Ho
    obtain ⟨rfl, Hh', Hfs, _, Hlazy'⟩ := brk_step_shape segs ms x8 model eff model' evs Hh Hlazy Hno Hspec
    obtain ⟨c, Hstar⟩ := IH eff model' [] Hspec Hh' (Hlazy'.trans Hlazy) o Ht
    have Hss := sstep.sstep_syscall ms model x8 eff model' model' [] Hh Hsvc Hspec Hh'
      (materialize_model_accesses_no_lazy _ _ (Hlazy'.trans Hlazy))
    have H := star.star_step _ _ _ _ _ Hss Hstar
    rw [List.nil_append, Hfs] at H
    exact ⟨c, H⟩

/-! ### No-error characterization -/

theorem to_outcomes_no_error (segs : List Segment) : ∀ ms model U,
    to_outcomes segs ms model U → m_halted model = none → m_vm_lazy model = [] →
    ¬ reaches_error segs (mkCfg ms model) := by
  intro ms model U Hto Hh Hlazy
  exact exec_no_error segs _ (exec_conseq segs _ _ _ (to_outcomes_exec segs ms model U Hto Hh Hlazy)
    (fun _ _ ⟨_, _, _, Hx⟩ => exits_with_never_errors _ _ _ Hx))

/-! ### Ergonomic brk node: everything in terms of the resolved break value `r` -/

/-- `tou_brk` specialized to a continuation family indexed by the resolved break `r`. -/
theorem tou_brk_r (segs : List Segment) : ∀ ms model x8 (T' : word → (List (List byte) × word) → Prop) U,
    ms.ms_svc_pending = some x8 → bv_unsigned x8 = 214 →
    (∀ r, brk_resolution_ok model (ms_gpr ms 0) r →
      to_outcomes segs
        (advance_past_svc (apply_effect ms
          (mkEffectU r [] (brk_zeros (ms_gpr ms 0) r (m_vmmaps model).vm_brk)
            (brk_unmaps r (m_vmmaps model).vm_brk) [] [])))
        (brk_model (ms_gpr ms 0) r model) (T' r)) →
    (∀ o, U o ↔ ∃ r, brk_resolution_ok model (ms_gpr ms 0) r ∧ T' r o) →
    to_outcomes segs ms model U := by
  intro ms model x8 T' U Hsvc Hno Hcont HU
  refine .tou_brk ms model x8 (fun eff _ => T' eff.eff_ret) U Hsvc Hno ?_ ?_
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

/-- Singleton leaf, ergonomic form. -/
theorem tou_wexit_eq (segs : List Segment) : ∀ ms model bufs code,
    fd1chan model → to_wallexit segs (Z_to_bv 64 1) bufs code ms → bufs_modeled bufs →
    to_outcomes segs ms model (fun o => o = (bufs, code)) :=
  fun ms model bufs code Hfd Hte Hbm => .tou_wexit ms model bufs code _ Hfd Hte Hbm (fun _ => Iff.rfl)

/-- Rewire the outcome set along an extensional equivalence. -/
theorem tou_equiv (segs : List Segment) : ∀ ms model U V,
    to_outcomes segs ms model U → (∀ o, V o ↔ U o) → to_outcomes segs ms model V := by
  intro ms model U V Hto
  induction Hto generalizing V with
  | tou_wexit ms model bufs code U Hfd Hte Hbm HU =>
    intro HV
    exact .tou_wexit ms model bufs code V Hfd Hte Hbm (fun o => (HV o).trans (HU o))
  | tou_step ms ms' model U Hsvc Hstep _ IH =>
    intro HV
    exact .tou_step _ _ _ _ Hsvc Hstep (IH V HV)
  | tou_brk ms model x8 T U Hsvc Hno Hcont HU _ =>
    intro HV
    exact .tou_brk ms model x8 T V Hsvc Hno Hcont (fun o => (HV o).trans (HU o))

/-! ### Run-level packaging and the equivalence glue -/

/-- The run-level omni judgment of a brk-branching run. -/
theorem alloc_omni_run : ∀ segs pc ph sp brk0 mb rnd lim inp U,
    to_outcomes segs (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved segs) brk0 mb sp lim inp) U →
    omni_run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp (outcomes_post (in_fs inp) U) := by
  intro segs pc ph sp brk0 mb rnd lim inp U Hto
  exact to_outcomes_exec segs _ _ U Hto rfl rfl

theorem alloc_obs_iff : ∀ segs pc ph sp brk0 mb rnd lim inp U,
    to_outcomes segs (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved segs) brk0 mb sp lim inp) U →
    ∀ tr, obs_trace segs (init_config segs pc ph sp brk0 mb rnd lim inp) tr ↔
      ∃ o, U o ∧ is_prefix tr (outcome_trace (in_fs inp) o) := by
  intro segs pc ph sp brk0 mb rnd lim inp U Hto tr
  constructor
  · rintro ⟨tr', c, Hstar, Hp⟩
    obtain ⟨o, Ho, Hp'⟩ := to_outcomes_star_only segs _ _ U Hto rfl rfl tr' c Hstar
    exact ⟨o, Ho, is_prefix_trans _ _ _ Hp Hp'⟩
  · rintro ⟨o, Ho, Hp⟩
    obtain ⟨c, Hstar⟩ := to_outcomes_star_admits segs _ _ U Hto rfl rfl o Ho
    exact ⟨_, c, Hstar, Hp⟩

theorem alloc_no_error_run : ∀ segs pc ph sp brk0 mb rnd lim inp U,
    to_outcomes segs (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved segs) brk0 mb sp lim inp) U →
    ¬ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp) := by
  intro segs pc ph sp brk0 mb rnd lim inp U Hto
  exact exec_no_error segs _ (exec_conseq segs _ _ _ (alloc_omni_run segs pc ph sp brk0 mb rnd lim inp U Hto)
    (fun _ _ ⟨_, _, _, Hx⟩ => exits_with_never_errors _ _ _ Hx))

/-- The omni equivalence for two brk-allocating binaries with the SAME outcome set `U`, at the two role
    budgets. -/
theorem alloc_omni_strong_equiv :
    ∀ source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd U inp,
      to_outcomes source_segs
        (init_machine_state source_segs rpc rph rsp rrnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
        (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp) U →
      to_outcomes target_segs
        (init_machine_state target_segs apc aph asp arnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
        (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp) U →
      omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
        (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp := by
  intro source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd U inp Hsource Htarget
  refine ⟨?_, .inr ⟨?_, ?_⟩⟩
  · exact coexec_conseq source_segs _ _ _
      (exec_coexec source_segs _ _
        (alloc_omni_run source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp U Hsource))
      (fun _ _ ⟨_, _, _, Hx⟩ => never_errors_covered source_segs _ _ (exits_with_never_errors _ _ _ Hx))
  · apply (trace_equiv_iff_omni _ _ _ _ _ _ _).1
    intro tr
    exact (alloc_obs_iff source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp U Hsource tr).trans
      (alloc_obs_iff target_segs apc aph asp abrk amb arnd target_alloc_limit inp U Htarget tr).symm
  · apply (bh_errors_iff _ _ _ _).1
    exact alloc_no_error_run target_segs apc aph asp abrk amb arnd target_alloc_limit inp U Htarget

/-- The `Equivalence`-level equivalence for two brk-allocating binaries with the SAME outcome set `U`
    (each run at ITS quantified break base: `U` must be base-independent). -/
theorem alloc_strong_equiv :
    ∀ source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim U inp,
      to_outcomes source_segs
        (init_machine_state source_segs rpc rph rsp rrnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
        (init_model (segments_reserved source_segs) rbrk rmb rsp rlim inp) U →
      to_outcomes target_segs
        (init_machine_state target_segs apc aph asp arnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
        (init_model (segments_reserved target_segs) abrk amb asp alim inp) U →
      modeled (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp) ∧
        equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
          (run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp) := by
  intro source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim U inp
    Hsource Htarget
  refine ⟨no_error_run_modeled _ _ _ _ _ _ _ _ _
    (alloc_no_error_run source_segs rpc rph rsp rbrk rmb rrnd rlim inp U Hsource), .inr ⟨?_, ?_⟩⟩
  · intro tr
    exact (alloc_obs_iff source_segs rpc rph rsp rbrk rmb rrnd rlim inp U Hsource tr).trans
      (alloc_obs_iff target_segs apc aph asp abrk amb arnd alim inp U Htarget tr).symm
  · exact alloc_no_error_run target_segs apc aph asp abrk amb arnd alim inp U Htarget

end LPS
