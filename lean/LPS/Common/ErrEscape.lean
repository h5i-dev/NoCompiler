import LPS.Common.CatSim3
import LPS.Common.PropExec5

/-!
# LPS `theories/Common/ErrEscape.v` (f1006fe8): the source-error escape glue

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Common/ErrEscape.v` at f1006fe8 (image-INDEPENDENT proof library, not the trusted
specification there): a deterministic straight line of ordinary instructions (`msteps`, CatSim2) ending
in an illegal one (`MachineFault`, e.g. a load from an unmapped address) errors on every execution
(`msteps_illegal_exec`, `msteps_illegal_all_traces_error`), is covered (`msteps_fault_no_unmodeled`),
and so discharges `Equivalence.equiv` / `omni_strong_equiv` against ANY target (`err_escape_*`).

Conventions as PropExec4/5 and CatSim1. Rocq's `Context {fx : FPState}` is an instance argument
`[FPState]` of the two lemmas that use it (`step_lbu_fault`, `step_ld_fault`, whose proofs unfold the
interpreter as PropExec4's step lemmas do; the Ltac `step_pipeline` is not ported). The section
variable `segs` of `WithSegs`, `OmniWithSegs`, `AllErrorWithSegs`, `NoUnmodeledWithSegs` is the
leading explicit argument.
-/

namespace LPS
open RiscvSemantics OmniRun instr msize core

/-! ### Faulting loads -/

/-- A byte load from an unreadable address is an illegal instruction. -/
theorem step_lbu_fault [FPState] : ∀ segs regs pc mem rom w rd rs (imm : bv 12) (isz : Int),
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (Load SZ1 false rd rs imm, isz) →
    rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 1 = none →
    RiscvSemantics.step segs (mkst regs pc mem rom) = .MachineFault := by
  intro segs regs pc mem rom w rd rs imm isz Hfetch Hecall Hdecode Hread
  simp only [RiscvSemantics.step, step_accesses, ms_pc, mkst, decode_exec_accesses, exec, interp_eff_accesses,
    rget_getr, load_val, width_bytes, ov_rdn, b_addsext, Bool.false_eq_true, ↓reduceIte, Hfetch, Hecall,
    Hdecode, Hread]
  rfl

/-- A double load from an unreadable address is an illegal instruction. -/
theorem step_ld_fault [FPState] : ∀ segs regs pc mem rom w rd rs (imm : bv 12) (isz : Int),
    fetch_word segs pc = some w → is_ecall w = false →
    decode_any w = some (Load SZ8 true rd rs imm, isz) →
    rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 8 = none →
    RiscvSemantics.step segs (mkst regs pc mem rom) = .MachineFault := by
  intro segs regs pc mem rom w rd rs imm isz Hfetch Hecall Hdecode Hread
  simp only [RiscvSemantics.step, step_accesses, ms_pc, mkst, decode_exec_accesses, exec, interp_eff_accesses,
    rget_getr, load_val, width_bytes, ov_rdn, b_addsext, Bool.false_eq_true, ↓reduceIte, Hfetch, Hecall,
    Hdecode, Hread]
  rfl

/-! ### `msteps` into an illegal step reaches the error transition -/

/-- The ordinary-instruction transition (Lean-only helper). -/
theorem instr_sstep_cat (segs : List Segment) (ms ms' : machine_state) (model : Model) (hh : m_halted model = none)
    (hlazy : m_vm_lazy model = []) (hsvc : ms.ms_svc_pending = none)
    (hstep : RiscvSemantics.step segs ms = .MachineOk ms') :
    sstep segs (mkCfg ms model) [] (.SNext (mkCfg ms' model)) := by
  refine .sstep_instr ms model ms' model hh hsvc ?_
  rw [mi_account_step_no_lazy segs ms model hlazy, hstep]

/-- The fault transition (Lean-only helper). -/
theorem fault_sstep_cat (segs : List Segment) (ms : machine_state) (model : Model) (hh : m_halted model = none)
    (hlazy : m_vm_lazy model = []) (hsvc : ms.ms_svc_pending = none)
    (hill : RiscvSemantics.step segs ms = .MachineFault) :
    sstep segs (mkCfg ms model) [] .SError := by
  refine .sstep_instr_fault ms model hh hsvc ?_
  rw [mi_account_step_no_lazy segs ms model hlazy, hill]

/-- A faulting state has no `SNext` successor (Lean-only helper). -/
theorem fault_no_next_cat (segs : List Segment) (ms : machine_state) (model : Model) (hlazy : m_vm_lazy model = [])
    (hsvc : ms.ms_svc_pending = none) (hill : RiscvSemantics.step segs ms = .MachineFault) :
    ∀ evs c', ¬ sstep segs (mkCfg ms model) evs (.SNext c') := by
  intro evs c' hss
  have hacc := mi_account_step_no_lazy segs ms model hlazy
  rw [hill] at hacc
  cases hss with
  | sstep_instr _ _ _ _ _ _ h => rw [hacc] at h; cases h
  | sstep_syscall _ _ _ _ _ _ _ _ h => rw [hsvc] at h; cases h
  | sstep_exit _ _ _ _ _ _ _ _ h => rw [hsvc] at h; cases h
  | sstep_killed _ _ _ _ _ _ _ _ h => rw [hsvc] at h; cases h

/-- An `msteps` run is a silent `star` (the model is untouched). -/
theorem msteps_star_nil (segs : List Segment) : ∀ ms ms' model, m_halted model = none → m_vm_lazy model = [] →
    msteps segs ms ms' → star segs (mkCfg ms model) [] (mkCfg ms' model) := by
  intro ms ms' model hh hlazy h
  induction h with
  | mst_refl => exact .star_refl _
  | mst_step ms ms1 ms2 hsvc hstep _ ih =>
    exact star.star_step _ [] _ [] _ (instr_sstep_cat segs ms ms1 model hh hlazy hsvc hstep) ih

/-- Straight line of instructions, then an illegal one: error reached. -/
theorem msteps_illegal_error (segs : List Segment) : ∀ ms ms' model, m_halted model = none → m_vm_lazy model = [] →
    msteps segs ms ms' → ms'.ms_svc_pending = none → RiscvSemantics.step segs ms' = .MachineFault →
    reaches_error segs (mkCfg ms model) := by
  intro ms ms' model hh hlazy hm hsvc hill
  exact ⟨[], mkCfg ms' model, [], msteps_star_nil segs ms ms' model hh hlazy hm,
    fault_sstep_cat segs ms' model hh hlazy hsvc hill⟩

/-! ### The omni reading: one judgment for the whole escape -/

/-- The faulting state: its only transition is the error one, taken from itself. -/
theorem illegal_exec (segs : List Segment) : ∀ ms model, m_halted model = none → m_vm_lazy model = [] →
    ms.ms_svc_pending = none → RiscvSemantics.step segs ms = .MachineFault →
    OmniRun.exec segs (mkCfg ms model) (fun tr o => tr = [] ∧ o = OError (mkCfg ms model)) := by
  intro ms model hh hlazy hsvc hill
  refine .exec_step _ _ hh ⟨[], .SError, fault_sstep_cat segs ms model hh hlazy hsvc hill⟩ ?_ ?_
  · intro evs hss
    have hacc := mi_account_step_no_lazy segs ms model hlazy
    rw [hill] at hacc
    cases hss with
    | sstep_instr_fault => exact ⟨rfl, rfl⟩
    | sstep_instr_unmodeled _ _ _ _ h => rw [hacc] at h; cases h
    | sstep_syscall_materialization_fault _ _ _ _ _ _ _ h => rw [hsvc] at h; cases h
    | sstep_syscall_unmodeled _ _ _ _ h => rw [hsvc] at h; cases h
  · intro evs c' hss
    exact (fault_no_next_cat segs ms model hlazy hsvc hill evs c' hss).elim

/-- One ordinary instruction in front of any omni judgment. -/
theorem instr_exec (segs : List Segment) : ∀ ms ms' model (Q : post), m_halted model = none → m_vm_lazy model = [] →
    ms.ms_svc_pending = none → RiscvSemantics.step segs ms = .MachineOk ms' →
    OmniRun.exec segs (mkCfg ms' model) Q → OmniRun.exec segs (mkCfg ms model) Q := by
  intro ms ms' model Q hh hlazy hsvc hstep hex
  refine exec_step_only segs _ _ [] (mkCfg ms' model) (instr_sstep_cat segs ms ms' model hh hlazy hsvc hstep)
    (fun evs st hss => sstep_instr_inv segs ms model ms' evs st hlazy hsvc hstep hss) ?_
  exact exec_conseq segs _ _ _ hex (fun tr o h => by simpa using h)

theorem msteps_exec (segs : List Segment) : ∀ ms ms' model (Q : post), m_halted model = none → m_vm_lazy model = [] →
    msteps segs ms ms' → OmniRun.exec segs (mkCfg ms' model) Q → OmniRun.exec segs (mkCfg ms model) Q := by
  intro ms ms' model Q hh hlazy hm hex
  induction hm with
  | mst_refl => exact hex
  | mst_step ms0 ms1 ms2 hsvc hstep _ ih => exact instr_exec segs ms0 ms1 model Q hh hlazy hsvc hstep (ih hex)

/-- THE judgment: a deterministic instruction path ending in an illegal instruction errors, on every
    execution, from that instruction's configuration. -/
theorem msteps_illegal_exec (segs : List Segment) : ∀ ms ms' model, m_halted model = none → m_vm_lazy model = [] →
    msteps segs ms ms' → ms'.ms_svc_pending = none → RiscvSemantics.step segs ms' = .MachineFault →
    OmniRun.exec segs (mkCfg ms model) (fun tr o => tr = [] ∧ o = OError (mkCfg ms' model)) := by
  intro ms ms' model hh hlazy hm hsvc hill
  exact msteps_exec segs ms ms' model _ hh hlazy hm (illegal_exec segs ms' model hh hlazy hsvc hill)

/-- The faulting configuration is covered: the fault is a `MachineFault`, not the model giving up. -/
theorem fault_covered_at (segs : List Segment) : ∀ ms model, m_vm_lazy model = [] → ms.ms_svc_pending = none →
    RiscvSemantics.step segs ms = .MachineFault → ¬ unmodeled_at segs (mkCfg ms model) := by
  rintro ms model hlazy hsvc hfault ⟨_, ⟨_, hum⟩ | ⟨x8, hsvc', _⟩⟩
  · change mi_account_step segs ms model = _ at hum
    rw [mi_account_step_no_lazy segs ms model hlazy, hfault] at hum
    cases hum
  · change ms.ms_svc_pending = _ at hsvc'
    rw [hsvc] at hsvc'; cases hsvc'

/-- What the one judgment yields: the escape ... -/
theorem msteps_illegal_errors (segs : List Segment) : ∀ ms ms' model, m_halted model = none → m_vm_lazy model = [] →
    msteps segs ms ms' → ms'.ms_svc_pending = none → RiscvSemantics.step segs ms' = .MachineFault →
    OmniRun.exec segs (mkCfg ms model) errors := by
  intro ms ms' model hh hlazy hm hsvc hill
  exact exec_conseq segs _ _ _ (msteps_illegal_exec segs ms ms' model hh hlazy hm hsvc hill)
    (fun tr o h => by rw [h.2]; trivial)

/-- ... and coverage, without a separate walk of the path. -/
theorem msteps_illegal_covered (segs : List Segment) : ∀ ms ms' model, m_halted model = none → m_vm_lazy model = [] →
    msteps segs ms ms' → ms'.ms_svc_pending = none → RiscvSemantics.step segs ms' = .MachineFault →
    OmniRun.coexec segs (mkCfg ms model) (covered segs) := by
  intro ms ms' model hh hlazy hm hsvc hill
  apply exec_coexec
  exact exec_conseq segs _ _ _ (msteps_illegal_exec segs ms ms' model hh hlazy hm hsvc hill)
    (fun tr o h => by rw [h.2]; exact fault_covered_at segs ms' model hlazy hsvc hill)

/-- Bites: the judgment NAMES the outcome, so it does not exit with any code ... -/
theorem msteps_illegal_no_exit (segs : List Segment) : ∀ ms ms' model, m_halted model = none → m_vm_lazy model = [] →
    msteps segs ms ms' → ms'.ms_svc_pending = none → RiscvSemantics.step segs ms' = .MachineFault →
    ∀ code, ¬ OmniRun.exec segs (mkCfg ms model) (exits_with code) := by
  intro ms ms' model hh hlazy hm hsvc hill code hex
  obtain ⟨tr, o, hm', _, ho⟩ := exec_realizes segs _ _ (msteps_illegal_exec segs ms ms' model hh hlazy hm hsvc hill)
  have := exec_sound segs _ _ hex _ _ hm'
  rw [ho] at this
  exact this

/-- ... and it is not error-free. -/
theorem msteps_illegal_not_never_errors (segs : List Segment) : ∀ ms ms' model, m_halted model = none →
    m_vm_lazy model = [] → msteps segs ms ms' → ms'.ms_svc_pending = none →
    RiscvSemantics.step segs ms' = .MachineFault → ¬ OmniRun.coexec segs (mkCfg ms model) never_errors := by
  intro ms ms' model hh hlazy hm hsvc hill hco
  obtain ⟨tr, o, hm', _, ho⟩ := exec_realizes segs _ _ (msteps_illegal_exec segs ms ms' model hh hlazy hm hsvc hill)
  have := coexec_sound segs _ _ _ hm' _ hco
  rw [ho] at this
  exact this trivial

/-! ### Universal error for deterministic instruction paths -/

/-- An illegal ordinary-instruction state has exactly the error step, so all its executions error. -/
theorem illegal_all_traces_error (segs : List Segment) : ∀ ms model, m_halted model = none → m_vm_lazy model = [] →
    ms.ms_svc_pending = none → RiscvSemantics.step segs ms = .MachineFault → all_traces_error segs (mkCfg ms model) := by
  intro ms model hh hlazy hsvc hill
  exact .all_traces_error_intro _ ⟨[], .SError, fault_sstep_cat segs ms model hh hlazy hsvc hill⟩
    (fun evs c' hss => (fault_no_next_cat segs ms model hlazy hsvc hill evs c' hss).elim)

/-- Prepending the unique ordinary instruction transition preserves the universal error property. -/
theorem instr_all_traces_error (segs : List Segment) : ∀ ms ms' model, m_halted model = none →
    m_vm_lazy model = [] → ms.ms_svc_pending = none → RiscvSemantics.step segs ms = .MachineOk ms' →
    all_traces_error segs (mkCfg ms' model) → all_traces_error segs (mkCfg ms model) := by
  intro ms ms' model hh hlazy hsvc hstep hall
  refine .all_traces_error_intro _ ⟨[], _, instr_sstep_cat segs ms ms' model hh hlazy hsvc hstep⟩ ?_
  intro evs c' hss
  obtain ⟨_, hto⟩ := sstep_instr_inv segs ms model ms' evs (.SNext c') hlazy hsvc hstep hss
  cases hto
  exact hall

/-- Prepend any deterministic sequence of ordinary instructions to an all-error configuration. -/
theorem msteps_all_traces_error (segs : List Segment) : ∀ ms ms' model, m_halted model = none →
    m_vm_lazy model = [] → msteps segs ms ms' → all_traces_error segs (mkCfg ms' model) →
    all_traces_error segs (mkCfg ms model) := by
  intro ms ms' model hh hlazy hm hall
  induction hm with
  | mst_refl => exact hall
  | mst_step ms0 ms1 ms2 hsvc hstep _ ih => exact instr_all_traces_error segs ms0 ms1 model hh hlazy hsvc hstep (ih hall)

/-- A deterministic instruction path ending in an illegal instruction has no non-error trace. -/
theorem msteps_illegal_all_traces_error (segs : List Segment) : ∀ ms ms' model, m_halted model = none →
    m_vm_lazy model = [] → msteps segs ms ms' → ms'.ms_svc_pending = none →
    RiscvSemantics.step segs ms' = .MachineFault → all_traces_error segs (mkCfg ms model) := by
  intro ms ms' model hh hlazy hm hsvc hill
  exact (all_traces_error_iff segs _).2 (msteps_illegal_errors segs ms ms' model hh hlazy hm hsvc hill)

/-! ### Coverage: the deterministic fault path is MODELED -/

/-- A configuration with no `SNext` successor is only `star`-reachable from itself. -/
theorem star_stuck_refl (segs : List Segment) : ∀ c tr c', (∀ evs c2, ¬ sstep segs c evs (.SNext c2)) →
    star segs c tr c' → c' = c := by
  intro c tr c' hno hstar
  cases hstar with
  | star_refl => rfl
  | star_step _ evs c2 _ _ hss _ => exact (hno evs c2 hss).elim

/-- The faulting state itself is covered. -/
theorem fault_no_unmodeled (segs : List Segment) : ∀ ms model, m_vm_lazy model = [] → ms.ms_svc_pending = none →
    RiscvSemantics.step segs ms = .MachineFault → ¬ reaches_unmodeled segs (mkCfg ms model) := by
  rintro ms model hlazy hsvc hfault ⟨tr, c, hstar, hun⟩
  rw [star_stuck_refl segs _ tr c (fault_no_next_cat segs ms model hlazy hsvc hfault) hstar] at hun
  exact fault_covered_at segs ms model hlazy hsvc hfault hun

/-- One ordinary instruction in front of a covered configuration. -/
theorem instr_no_unmodeled (segs : List Segment) : ∀ ms ms' model, m_vm_lazy model = [] →
    ms.ms_svc_pending = none → RiscvSemantics.step segs ms = .MachineOk ms' →
    ¬ reaches_unmodeled segs (mkCfg ms' model) → ¬ reaches_unmodeled segs (mkCfg ms model) := by
  rintro ms ms' model hlazy hsvc hstep hnext ⟨tr, c, hstar, hun⟩
  cases hstar with
  | star_refl =>
    rcases hun with ⟨_, ⟨_, hum⟩ | ⟨x8, hsvc', _⟩⟩
    · change mi_account_step segs ms model = _ at hum
      rw [mi_account_step_no_lazy segs ms model hlazy, hstep] at hum
      cases hum
    · change ms.ms_svc_pending = _ at hsvc'
      rw [hsvc] at hsvc'; cases hsvc'
  | star_step _ evs c2 tr2 _ hss hrest =>
    obtain ⟨_, hc2⟩ := sstep_instr_inv segs ms model ms' evs (.SNext c2) hlazy hsvc hstep hss
    cases hc2
    exact hnext ⟨tr2, c, hrest, hun⟩

/-- A deterministic instruction path ending in a genuine fault never reaches an uncovered
    configuration. -/
theorem msteps_fault_no_unmodeled (segs : List Segment) : ∀ ms ms' model, msteps segs ms ms' →
    m_vm_lazy model = [] → ms'.ms_svc_pending = none → RiscvSemantics.step segs ms' = .MachineFault →
    ¬ reaches_unmodeled segs (mkCfg ms model) := by
  intro ms ms' model hm hlazy hsvc hfault
  cases hh : m_halted model with
  | some code =>
    -- a halted model takes no transition, and a halted configuration is not one the model declined
    rintro ⟨tr, c, hstar, hun⟩
    cases hstar with
    | star_refl =>
      have := hun.1
      change m_halted model = none at this
      rw [hh] at this; cases this
    | star_step _ _ _ _ _ hss _ =>
      have := sstep_from_running segs _ _ _ hss
      change m_halted model = none at this
      rw [hh] at this; cases this
  | none =>
    exact coexec_covered segs _ (msteps_illegal_covered segs ms ms' model hh hlazy hm hsvc hfault)

/-! ### Equivalence-level escape -/

/-- The omni escape, per run: the source's judgment at any budget ... -/
theorem err_escape_omni_run : ∀ segs pc ph sp brk0 mb rnd lim inp ms',
    msteps segs (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) ms' →
    ms'.ms_svc_pending = none → RiscvSemantics.step segs ms' = .MachineFault →
    omni_run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp errors := by
  intro segs pc ph sp brk0 mb rnd lim inp ms' hm hsvc hill
  exact msteps_illegal_errors segs _ ms' _ rfl rfl hm hsvc hill

/-- ... its coverage ... -/
theorem err_escape_omni_covered : ∀ segs pc ph sp brk0 mb rnd lim inp ms',
    msteps segs (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) ms' →
    ms'.ms_svc_pending = none → RiscvSemantics.step segs ms' = .MachineFault →
    omni_corun (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp (covered segs) := by
  intro segs pc ph sp brk0 mb rnd lim inp ms' hm hsvc hill
  exact msteps_illegal_covered segs _ ms' _ rfl rfl hm hsvc hill

/-- ... `OmniEquivalence.omni_equiv` against ANY target run ... -/
theorem err_escape_omni_equiv : ∀ segs pc ph sp brk0 mb rnd lim inp T limT et ms',
    msteps segs (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) ms' →
    ms'.ms_svc_pending = none → RiscvSemantics.step segs ms' = .MachineFault →
    omni_equiv (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) T limT et inp := by
  intro segs pc ph sp brk0 mb rnd lim inp T limT et ms' hm hsvc hill
  exact .inl (err_escape_omni_run segs pc ph sp brk0 mb rnd lim inp ms' hm hsvc hill)

/-- ... and the packaged `OmniEquivalence.omni_strong_equiv`: a source that deterministically faults,
    against any target image and entry. -/
theorem err_escape_omni_strong_equiv : ∀ segs pc ph sp brk0 mb rnd inp T et ms',
    msteps segs (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) ms' →
    ms'.ms_svc_pending = none → RiscvSemantics.step segs ms' = .MachineFault →
    omni_strong_equiv (mkImage segs pc ph) T (mkEntry sp brk0 mb rnd) et inp := by
  intro segs pc ph sp brk0 mb rnd inp T et ms' hm hsvc hill
  exact ⟨err_escape_omni_covered segs pc ph sp brk0 mb rnd _ inp ms' hm hsvc hill,
    err_escape_omni_equiv segs pc ph sp brk0 mb rnd _ inp T _ et ms' hm hsvc hill⟩

/-- If the SOURCE deterministically runs into a faulting instruction, `equiv` holds against ANY target
    behavior. -/
theorem err_escape_equiv : ∀ segs pc ph sp brk0 mb rnd lim inp (target : behavior) ms',
    msteps segs (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) ms' →
    ms'.ms_svc_pending = none → RiscvSemantics.step segs ms' = .MachineFault →
    equiv (run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp) target := by
  intro segs pc ph sp brk0 mb rnd lim inp target ms' hm hsvc hill
  exact .inl ((bh_all_errors_iff _ _ _ _).2 (err_escape_omni_run segs pc ph sp brk0 mb rnd lim inp ms' hm hsvc hill))

/-- ... and the same run is MODELED: it dies, but at a `MachineFault`. -/
theorem err_escape_modeled : ∀ segs pc ph sp brk0 mb rnd lim inp ms',
    msteps segs (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) ms' →
    ms'.ms_svc_pending = none → RiscvSemantics.step segs ms' = .MachineFault →
    modeled (run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp) := by
  intro segs pc ph sp brk0 mb rnd lim inp ms' hm hsvc hill
  exact (modeled_iff _ _ _ _).2 (err_escape_omni_covered segs pc ph sp brk0 mb rnd lim inp ms' hm hsvc hill)

/-- The packaged escape: both clauses of `Equivalence.strong_equiv` for a source that deterministically
    faults, against ANY target. -/
theorem err_escape_strong_equiv : ∀ segs pc ph sp brk0 mb rnd lim inp (target : behavior) ms',
    msteps segs (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) ms' →
    ms'.ms_svc_pending = none → RiscvSemantics.step segs ms' = .MachineFault →
    modeled (run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp) ∧
      equiv (run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp) target := by
  intro segs pc ph sp brk0 mb rnd lim inp target ms' hm hsvc hill
  exact ⟨err_escape_modeled segs pc ph sp brk0 mb rnd lim inp ms' hm hsvc hill,
    err_escape_equiv segs pc ph sp brk0 mb rnd lim inp target ms' hm hsvc hill⟩

end LPS
