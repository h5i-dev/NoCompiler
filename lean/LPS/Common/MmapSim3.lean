import LPS.Common.MmapSim2

/-!
# LPS `theories/Common/MmapSim.v` (f1006fe8), part 3: `tmw`, the branching mmap node, and the run level

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Common/MmapSim.v` at f1006fe8 (image-INDEPENDENT proof library), from `tmw` to the end:
`tmw segs ms model bf cf bs cs` (a deterministic prefix of instruction steps reaching an mmap ecall of
the modeled register shape, whose failure resolutions all land in `twm _ _ bf cf` and whose grants all
land in `twm _ _ bs cs`, with at least one admissible grant address), `msteps_tmw`, the raw-ecall
constructor `tmw_mmap_rec`, the one-step inversion `sstep_mmap_inv`, the omni reading `tmw_exec` with
`tmw_star_admits_fail`/`_succ`, `two_traces`, `tmw_star_only`, `tmw_no_error` and the refutations
(`twm_exec_not_errors`, `twm_exec_code_unique`, `tmw_exec_not_errors`, `tmw_exec_not_fail_only`,
`tmw_exec_not_succ_only`); then after `End WithSegs` the run-level packaging (`two_traces_prefix_closed`,
`mmap_obs_iff_te`, `mmap_no_error_run_te`, `mmap_omni_run_te`) and the equivalence glue
(`mmap_omni_strong_equiv_te`, `mmap_strong_equiv_te`): two such binaries with the same `(bf, cf)` and
`(bs, cs)` are observably equivalent.

Conventions as MmapSim1/MmapSim2. The proofs are Lean's. Lean-only helpers (all private): the
register-name facts `arg_reg_3'`..`arg_reg_5'` (the `a3`..`a5` analogues of PropExec1's
`arg_reg_0`..`arg_reg_2`), `exec_instr_step'` (one silent instruction step of the omni judgment), and the
transitions `instr_sstep`, `mmap_fail_sstep` (the ENOMEM resolution) and `mmap_succ_sstep` (a grant).
-/

namespace LPS
open RiscvSemantics OmniRun

private theorem arg_reg_3' : Z_to_bv 5 (10 + ((3 : Nat) : Int)) = (13 : reg) := by decide
private theorem arg_reg_4' : Z_to_bv 5 (10 + ((4 : Nat) : Int)) = (14 : reg) := by decide
private theorem arg_reg_5' : Z_to_bv 5 (10 + ((5 : Nat) : Int)) = (15 : reg) := by decide

/-! ### tmw: deterministic prefix, then the branching mmap -/

inductive tmw (segs : List Segment) : machine_state → Model → List (List byte) → word → List (List byte) → word → Prop where
  | tmw_mmap (ms model x8 bf cf bs cs) :
      ms.ms_svc_pending = some x8 → bv_unsigned x8 = 222 → mmap_args_ok ms →
      (∀ e, e ∈ mmap_errnos → twm segs (advance_past_svc (set_gpr0 ms (errno_ret e))) model bf cf) →
      (∀ a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true →
        twm segs (advance_past_svc (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
          (mmap_model a (page_round_up (ms_gpr ms 1)) model) bs cs) →
      (∃ a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true) →
      tmw segs ms model bf cf bs cs
  | tmw_step (ms ms' model bf cf bs cs) :
      ms.ms_svc_pending = none → RiscvSemantics.step segs ms = .MachineOk ms' →
      tmw segs ms' model bf cf bs cs → tmw segs ms model bf cf bs cs

theorem msteps_tmw (segs : List Segment) : ∀ ms ms' model bf cf bs cs,
    msteps segs ms ms' → tmw segs ms' model bf cf bs cs → tmw segs ms model bf cf bs cs := by
  intro ms ms' model bf cf bs cs H
  induction H with
  | mst_refl => exact id
  | mst_step ms ms1 ms2 hsvc hstep _ ih => exact fun hw => .tmw_step _ _ _ _ _ _ _ hsvc hstep (ih hw)

/-- Raw-ecall-record constructor for the mmap node: the two continuations are collapsed to `mkst` form
    (`adv_set` / `adv_mmap_grant`). -/
theorem tmw_mmap_rec [FPState] (segs : List Segment) : ∀ regs pc mem rom model bf cf bs cs,
    bv_unsigned (getr regs 17) = 222 →
    reg_get regs 11 ≠ Z_to_bv 64 0 → reg_get regs 12 = Z_to_bv 64 3 → reg_get regs 13 = Z_to_bv 64 34 →
    reg_get regs 14 = Z_to_bv 64 (-1) → reg_get regs 15 = Z_to_bv 64 0 →
    (∀ e, e ∈ mmap_errnos → twm segs (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem rom) model bf cf) →
    (∀ a, grant_ok (reg_get regs 10) model a (page_round_up_Z (bv_unsigned (reg_get regs 11))) = true →
      twm segs (mkst (regupd regs 10 a) (v_addi pc 4) (zfill a (page_round_up (reg_get regs 11)) mem) rom)
        (mmap_model a (page_round_up (reg_get regs 11)) model) bs cs) →
    (∃ a, grant_ok (reg_get regs 10) model a (page_round_up_Z (bv_unsigned (reg_get regs 11))) = true) →
    tmw segs { ms_regs := regs, ms_fregs := fp_regs, ms_pc_val := pc, ms_svc_pending := some (getr regs 17),
               ms_resv := none, ms_fcsr := fp_csr, ms_mem := mem, ms_rom := rom } model bf cf bs cs := by
  intro regs pc mem rom model bf cf bs cs H17 H11 H12 H13 H14 H15 Hfail Hsucc Hex
  refine .tmw_mmap _ _ (getr regs 17) _ _ _ _ rfl H17 ?_ ?_ ?_ ?_
  · simp only [mmap_args_ok, ms_gpr, arg_reg_1, arg_reg_2, arg_reg_3', arg_reg_4', arg_reg_5']
    exact ⟨H11, H12, H13, H14, H15⟩
  · intro e he; rw [adv_set]; exact Hfail e he
  · intro a hg
    simp only [ms_gpr, arg_reg_0, arg_reg_1] at hg ⊢
    rw [adv_mmap_grant]
    exact Hsucc a hg
  · simp only [ms_gpr, arg_reg_0, arg_reg_1]; exact Hex

/-! ### One-step inversion for the mmap configuration -/

theorem sstep_mmap_inv (segs : List Segment) : ∀ ms model x8 evs st,
    m_halted model = none → m_vm_lazy model = [] → ms.ms_svc_pending = some x8 → bv_unsigned x8 = 222 →
    mmap_args_ok ms → sstep segs (mkCfg ms model) evs st →
    evs = [] ∧
      ((∃ e, e ∈ mmap_errnos ∧ st = .SNext (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model)) ∨
       (∃ a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ∧
          st = .SNext (mkCfg (advance_past_svc (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
            (mmap_model a (page_round_up (ms_gpr ms 1)) model)))) := by
  intro ms model x8 evs st Hh Hlazy Hsvc Hno Hargs Hss
  have Hx : ∀ y, ms.ms_svc_pending = some y → y = x8 := by
    intro y h; rw [Hsvc] at h; exact (Option.some.inj h).symm
  -- every admissible outcome keeps the model running and eager-only
  have Hshape : ∀ eff model' evs0, syscall_spec (sys_input segs ms x8) model (Ok eff model' evs0) →
      m_halted model' = none ∧ m_vm_lazy model' = [] := by
    intro eff model' evs0 hspec
    obtain ⟨_, (⟨_, _, _, rfl⟩ | ⟨a, _, _, rfl⟩)⟩ := mmap_ok_inv segs ms x8 model _ _ _ Hno Hargs hspec
    · exact ⟨Hh, Hlazy⟩
    · exact ⟨(mmap_model_halted _ _ _).trans Hh, (mmap_model_lazy _ _ _).trans Hlazy⟩
  cases Hss with
  | sstep_instr _ _ _ _ _ h _ => rw [Hsvc] at h; cases h
  | sstep_instr_fault _ _ _ h _ => rw [Hsvc] at h; cases h
  | sstep_instr_unmodeled _ _ _ h _ => rw [Hsvc] at h; cases h
  | sstep_syscall _ _ y eff model' model'' _ _ hsvc hspec _ hmat =>
    rw [Hx y hsvc] at hspec
    rw [materialize_model_accesses_no_lazy _ _ (Hshape _ _ _ hspec).2] at hmat
    cases hmat
    obtain ⟨rfl, (⟨e, he, rfl, rfl⟩ | ⟨a, hg, rfl, rfl⟩)⟩ := mmap_ok_inv segs ms x8 model _ _ _ Hno Hargs hspec
    · exact ⟨rfl, .inl ⟨e, he, by rw [apply_effect_no_write]⟩⟩
    · exact ⟨rfl, .inr ⟨a, hg, rfl⟩⟩
  | sstep_syscall_materialization_fault _ _ y _ _ _ _ hsvc hspec _ hmat =>
    rw [Hx y hsvc] at hspec
    rw [materialize_model_accesses_no_lazy _ _ (Hshape _ _ _ hspec).2] at hmat
    cases hmat
  | sstep_exit _ _ y _ _ _ _ _ hsvc hspec hhalt _ =>
    rw [Hx y hsvc] at hspec
    rw [(Hshape _ _ _ hspec).1] at hhalt; cases hhalt
  | sstep_killed _ _ y _ _ _ _ _ hsvc hspec hkill =>
    rw [Hx y hsvc] at hspec
    rw [m_killed_of_m_halted_none _ (Hshape _ _ _ hspec).1] at hkill; cases hkill
  | sstep_syscall_unmodeled _ _ y _ hsvc hspec =>
    rw [Hx y hsvc] at hspec
    exact absurd hspec (mmap_no_unmodeled segs ms x8 model Hno Hargs)

/-! ### The omni reading of `tmw` -/

/-- Every execution takes one of the two branches at the mmap node and then runs its `twm` line. -/
def tmw_post (bf : List (List byte)) (cf : word) (bs : List (List byte)) (cs : word) (fs : Fs) : post :=
  fun tr o => (tr = wevents bf ++ [.ExitEv cf fs] ∧ exits_with cf tr o) ∨
              (tr = wevents bs ++ [.ExitEv cs fs] ∧ exits_with cs tr o)

/-- One silent instruction step of the omni judgment (Lean-only helper). -/
private theorem exec_instr_step' (segs : List Segment) (ms ms' : machine_state) (model : Model) (Q : post)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = []) (Hsvc : ms.ms_svc_pending = none)
    (Hstep : RiscvSemantics.step segs ms = .MachineOk ms') (H : OmniRun.exec segs (mkCfg ms' model) Q) :
    OmniRun.exec segs (mkCfg ms model) Q := by
  refine exec_step_only segs _ _ [] (mkCfg ms' model) ?_
    (fun evs st Hss => sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss) ?_
  · refine .sstep_instr ms model ms' model Hh Hsvc ?_
    rw [mi_account_step_no_lazy segs ms model Hlazy, Hstep]
  · exact exec_conseq segs _ _ _ H (fun tr o h => by simpa using h)

/-- The silent instruction transition (Lean-only helper). -/
private theorem instr_sstep (segs : List Segment) (ms ms' : machine_state) (model : Model)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = []) (Hsvc : ms.ms_svc_pending = none)
    (Hstep : RiscvSemantics.step segs ms = .MachineOk ms') : sstep segs (mkCfg ms model) [] (.SNext (mkCfg ms' model)) := by
  refine .sstep_instr ms model ms' model Hh Hsvc ?_
  rw [mi_account_step_no_lazy segs ms model Hlazy, Hstep]

/-- The ENOMEM failure transition at the mmap node (Lean-only helper). -/
private theorem mmap_fail_sstep (segs : List Segment) (ms : machine_state) (model : Model) (x8 : word)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = []) (Hsvc : ms.ms_svc_pending = some x8)
    (Hno : bv_unsigned x8 = 222) (Hargs : mmap_args_ok ms) :
    sstep segs (mkCfg ms model) [] (.SNext (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret ENOMEM))) model)) := by
  rw [← apply_effect_no_write]
  exact .sstep_syscall ms model x8 _ model model [] Hh Hsvc
    (mmap_fail_ok segs ms x8 model ENOMEM Hno Hargs ENOMEM_in_mmap_errnos) Hh
    (materialize_model_accesses_no_lazy _ _ Hlazy)

/-- The grant transition at the mmap node (Lean-only helper). -/
private theorem mmap_succ_sstep (segs : List Segment) (ms : machine_state) (model : Model) (x8 a : word)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = []) (Hsvc : ms.ms_svc_pending = some x8)
    (Hno : bv_unsigned x8 = 222) (Hargs : mmap_args_ok ms)
    (Hg : grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true) :
    sstep segs (mkCfg ms model) []
      (.SNext (mkCfg (advance_past_svc (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
        (mmap_model a (page_round_up (ms_gpr ms 1)) model))) :=
  .sstep_syscall ms model x8 _ _ _ [] Hh Hsvc (mmap_succ_ok segs ms x8 model a Hno Hargs Hg)
    ((mmap_model_halted _ _ _).trans Hh)
    (materialize_model_accesses_no_lazy _ _ ((mmap_model_lazy _ _ _).trans Hlazy))

theorem tmw_exec (segs : List Segment) : ∀ ms model bf cf bs cs, tmw segs ms model bf cf bs cs →
    bufs_modeled bf → bufs_modeled bs → m_halted model = none → m_vm_lazy model = [] → fd1chan model →
    OmniRun.exec segs (mkCfg ms model) (tmw_post bf cf bs cs (m_fs model)) := by
  intro ms model bf cf bs cs Hte
  induction Hte with
  | tmw_mmap ms model x8 bf cf bs cs Hsvc Hno Hargs Hfail Hsucc _ =>
    intro Hbf Hbs Hh Hlazy Hfd
    refine .exec_step _ _ Hh ⟨_, _, mmap_fail_sstep segs ms model x8 Hh Hlazy Hsvc Hno Hargs⟩ ?_ ?_
    · intro evs Hss
      obtain ⟨_, (⟨e, _, Habs⟩ | ⟨a, _, Habs⟩)⟩ := sstep_mmap_inv segs ms model x8 evs .SError Hh Hlazy Hsvc Hno Hargs Hss
        <;> cases Habs
    · intro evs c' Hss
      obtain ⟨rfl, (⟨e, He, Hc'⟩ | ⟨a, Hg, Hc'⟩)⟩ :=
        sstep_mmap_inv segs ms model x8 evs (.SNext c') Hh Hlazy Hsvc Hno Hargs Hss <;> cases Hc'
      · -- failure: the first straight line
        exact exec_conseq segs _ _ _ (twm_exec segs _ _ _ _ (Hfail e He) Hbf Hh Hlazy Hfd)
          (fun tr o ⟨Heq, Hx⟩ => .inl ⟨by simpa using Heq, Hx⟩)
      · -- success: the second, at the mapped model
        exact exec_conseq segs _ _ _ (twm_exec segs _ _ _ _ (Hsucc a Hg) Hbs ((mmap_model_halted _ _ _).trans Hh)
          ((mmap_model_lazy _ _ _).trans Hlazy) (mmap_model_fd1chan _ _ _ Hfd))
          (fun tr o ⟨Heq, Hx⟩ => .inr ⟨by simpa [mmap_model_fs] using Heq, Hx⟩)
  | tmw_step ms ms' model bf cf bs cs Hsvc Hstep _ IH =>
    intro Hbf Hbs Hh Hlazy Hfd
    exact exec_instr_step' segs ms ms' model _ Hh Hlazy Hsvc Hstep (IH Hbf Hbs Hh Hlazy Hfd)

theorem tmw_star_admits_fail (segs : List Segment) : ∀ ms model bf cf bs cs, tmw segs ms model bf cf bs cs →
    bufs_modeled bf → m_halted model = none → m_vm_lazy model = [] → fd1chan model →
    ∃ c, star segs (mkCfg ms model) (wevents bf ++ [.ExitEv cf (m_fs model)]) c := by
  intro ms model bf cf bs cs Hte
  induction Hte with
  | tmw_mmap ms model x8 bf cf bs cs Hsvc Hno Hargs Hfail _ _ =>
    intro Hbm Hh Hlazy Hfd
    obtain ⟨c, Hstar⟩ := twm_star_admits segs _ _ _ _ (Hfail ENOMEM ENOMEM_in_mmap_errnos) Hbm Hh Hlazy Hfd
    exact ⟨c, by simpa using star.star_step _ _ _ _ _ (mmap_fail_sstep segs ms model x8 Hh Hlazy Hsvc Hno Hargs) Hstar⟩
  | tmw_step ms ms' model bf cf bs cs Hsvc Hstep _ IH =>
    intro Hbm Hh Hlazy Hfd
    obtain ⟨c, Hstar⟩ := IH Hbm Hh Hlazy Hfd
    exact ⟨c, by simpa using star.star_step _ _ _ _ _ (instr_sstep segs ms ms' model Hh Hlazy Hsvc Hstep) Hstar⟩

theorem tmw_star_admits_succ (segs : List Segment) : ∀ ms model bf cf bs cs, tmw segs ms model bf cf bs cs →
    bufs_modeled bs → m_halted model = none → m_vm_lazy model = [] → fd1chan model →
    ∃ c, star segs (mkCfg ms model) (wevents bs ++ [.ExitEv cs (m_fs model)]) c := by
  intro ms model bf cf bs cs Hte
  induction Hte with
  | tmw_mmap ms model x8 bf cf bs cs Hsvc Hno Hargs _ Hsucc Hex =>
    intro Hbm Hh Hlazy Hfd
    obtain ⟨a, Hg⟩ := Hex
    obtain ⟨c, Hstar⟩ := twm_star_admits segs _ _ _ _ (Hsucc a Hg) Hbm ((mmap_model_halted _ _ _).trans Hh)
      ((mmap_model_lazy _ _ _).trans Hlazy) (mmap_model_fd1chan _ _ _ Hfd)
    rw [mmap_model_fs] at Hstar
    exact ⟨c, by simpa using star.star_step _ _ _ _ _ (mmap_succ_sstep segs ms model x8 a Hh Hlazy Hsvc Hno Hargs Hg) Hstar⟩
  | tmw_step ms ms' model bf cf bs cs Hsvc Hstep _ IH =>
    intro Hbm Hh Hlazy Hfd
    obtain ⟨c, Hstar⟩ := IH Hbm Hh Hlazy Hfd
    exact ⟨c, by simpa using star.star_step _ _ _ _ _ (instr_sstep segs ms ms' model Hh Hlazy Hsvc Hstep) Hstar⟩

/-- The two candidate traces. -/
def two_traces (bf : List (List byte)) (cf : word) (bs : List (List byte)) (cs : word) (fs : Fs) (tr : List event) :
    Prop :=
  is_prefix tr (wevents bf ++ [.ExitEv cf fs]) ∨ is_prefix tr (wevents bs ++ [.ExitEv cs fs])

theorem tmw_star_only (segs : List Segment) : ∀ ms model bf cf bs cs, tmw segs ms model bf cf bs cs →
    bufs_modeled bf → bufs_modeled bs → m_halted model = none → m_vm_lazy model = [] → fd1chan model →
    ∀ tr c, star segs (mkCfg ms model) tr c → two_traces bf cf bs cs (m_fs model) tr := by
  intro ms model bf cf bs cs Hte Hbf Hbs Hh Hlazy Hfd tr c Hstar
  obtain ⟨tr', o, _, (⟨Heq, _⟩ | ⟨Heq, _⟩)⟩ :=
    exec_realizes segs _ _ (exec_star segs _ _ _ _ (tmw_exec segs ms model bf cf bs cs Hte Hbf Hbs Hh Hlazy Hfd) Hstar)
  · exact .inl (Heq ▸ is_prefix_app _ _)
  · exact .inr (Heq ▸ is_prefix_app _ _)

/-! ### No-error characterization and refutations -/

/-- No-error: a corollary of `tmw_exec`. -/
theorem tmw_no_error (segs : List Segment) : ∀ ms model bf cf bs cs,
    m_halted model = none → m_vm_lazy model = [] → fd1chan model → tmw segs ms model bf cf bs cs →
    bufs_modeled bf → bufs_modeled bs → ¬ reaches_error segs (mkCfg ms model) := by
  intro ms model bf cf bs cs Hh Hlazy Hfd Hte Hbf Hbs
  apply exec_no_error
  refine exec_conseq segs _ _ _ (tmw_exec segs ms model bf cf bs cs Hte Hbf Hbs Hh Hlazy Hfd) ?_
  rintro tr o (⟨_, Hx⟩ | ⟨_, Hx⟩) <;> exact exits_with_never_errors _ _ _ Hx

theorem twm_exec_not_errors (segs : List Segment) : ∀ ms model bufs code, twm segs ms model bufs code →
    bufs_modeled bufs → m_halted model = none → m_vm_lazy model = [] → fd1chan model →
    ¬ OmniRun.exec segs (mkCfg ms model) OmniRun.errors := by
  intro ms model bufs code Hte Hbm Hh Hlazy Hfd Hex
  obtain ⟨tr, o, Hm, Herr⟩ := exec_realizes segs _ _ Hex
  obtain ⟨_, Hx⟩ := exec_sound segs _ _ (twm_exec segs ms model bufs code Hte Hbm Hh Hlazy Hfd) _ _ Hm
  exact exits_with_never_errors _ _ _ Hx Herr

theorem twm_exec_code_unique (segs : List Segment) : ∀ ms model bufs code, twm segs ms model bufs code →
    bufs_modeled bufs → m_halted model = none → m_vm_lazy model = [] → fd1chan model →
    ∀ code', OmniRun.exec segs (mkCfg ms model) (exits_with code') → code' = code := by
  intro ms model bufs code Hte Hbm Hh Hlazy Hfd code' Hex
  obtain ⟨tr, o, Hm, _, Hx⟩ := exec_realizes segs _ _ (twm_exec segs ms model bufs code Hte Hbm Hh Hlazy Hfd)
  have Hx' := exec_sound segs _ _ Hex _ _ Hm
  cases o with
  | OHalt c' =>
    obtain ⟨Hc, _⟩ := Hx
    obtain ⟨Hc', _⟩ := Hx'
    rw [Hc] at Hc'
    exact (Option.some.inj Hc').symm
  | OError c' => exact Hx.elim

theorem tmw_exec_not_errors (segs : List Segment) : ∀ ms model bf cf bs cs, tmw segs ms model bf cf bs cs →
    bufs_modeled bf → bufs_modeled bs → m_halted model = none → m_vm_lazy model = [] → fd1chan model →
    ¬ OmniRun.exec segs (mkCfg ms model) OmniRun.errors := by
  intro ms model bf cf bs cs Hte Hbf Hbs Hh Hlazy Hfd Hex
  obtain ⟨tr, o, Hm, Herr⟩ := exec_realizes segs _ _ Hex
  rcases exec_sound segs _ _ (tmw_exec segs ms model bf cf bs cs Hte Hbf Hbs Hh Hlazy Hfd) _ _ Hm with
    ⟨_, Hx⟩ | ⟨_, Hx⟩ <;> exact exits_with_never_errors _ _ _ Hx Herr

/-- The single-trace reading of the failure tail is refuted whenever the success trace is not a prefix
    of it: the success branch is realised. -/
theorem tmw_exec_not_fail_only (segs : List Segment) : ∀ ms model bf cf bs cs, tmw segs ms model bf cf bs cs →
    bufs_modeled bs → m_halted model = none → m_vm_lazy model = [] → fd1chan model →
    ¬ is_prefix (wevents bs ++ [.ExitEv cs (m_fs model)]) (wevents bf ++ [.ExitEv cf (m_fs model)]) →
    ¬ OmniRun.exec segs (mkCfg ms model) (twm_post bf cf (m_fs model)) := by
  intro ms model bf cf bs cs Hte Hbs Hh Hlazy Hfd Hnp Hex
  obtain ⟨c, Hstar⟩ := tmw_star_admits_succ segs ms model bf cf bs cs Hte Hbs Hh Hlazy Hfd
  obtain ⟨tr', o, _, Heq, _⟩ := exec_realizes segs _ _ (exec_star segs _ _ _ _ Hex Hstar)
  exact Hnp (Heq ▸ is_prefix_app _ _)

theorem tmw_exec_not_succ_only (segs : List Segment) : ∀ ms model bf cf bs cs, tmw segs ms model bf cf bs cs →
    bufs_modeled bf → m_halted model = none → m_vm_lazy model = [] → fd1chan model →
    ¬ is_prefix (wevents bf ++ [.ExitEv cf (m_fs model)]) (wevents bs ++ [.ExitEv cs (m_fs model)]) →
    ¬ OmniRun.exec segs (mkCfg ms model) (twm_post bs cs (m_fs model)) := by
  intro ms model bf cf bs cs Hte Hbf Hh Hlazy Hfd Hnp Hex
  obtain ⟨c, Hstar⟩ := tmw_star_admits_fail segs ms model bf cf bs cs Hte Hbf Hh Hlazy Hfd
  obtain ⟨tr', o, _, Heq, _⟩ := exec_realizes segs _ _ (exec_star segs _ _ _ _ Hex Hstar)
  exact Hnp (Heq ▸ is_prefix_app _ _)

/-! ### Run-level packaging and the equivalence glue -/

theorem two_traces_prefix_closed : ∀ bf cf bs cs fs tr tr',
    two_traces bf cf bs cs fs tr → is_prefix tr' tr → two_traces bf cf bs cs fs tr' := by
  rintro bf cf bs cs fs tr tr' (H | H) Hp
  · exact .inl (is_prefix_trans _ _ _ Hp H)
  · exact .inr (is_prefix_trans _ _ _ Hp H)

theorem mmap_obs_iff_te : ∀ segs pc ph sp brk0 mb rnd lim inp bf cf bs cs,
    tmw segs (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved segs) brk0 mb sp lim inp) bf cf bs cs →
    bufs_modeled bf → bufs_modeled bs →
    ∀ tr, obs_trace segs (init_config segs pc ph sp brk0 mb rnd lim inp) tr ↔ two_traces bf cf bs cs (in_fs inp) tr := by
  intro segs pc ph sp brk0 mb rnd lim inp bf cf bs cs Hte Hbf Hbs tr
  constructor
  · rintro ⟨tr', c, Hstar, Hp⟩
    exact two_traces_prefix_closed _ _ _ _ _ _ _ (tmw_star_only segs _ _ bf cf bs cs Hte Hbf Hbs rfl rfl rfl tr' c Hstar) Hp
  · rintro (Hp | Hp)
    · obtain ⟨c, Hstar⟩ := tmw_star_admits_fail segs _ _ bf cf bs cs Hte Hbf rfl rfl rfl
      exact ⟨_, c, Hstar, Hp⟩
    · obtain ⟨c, Hstar⟩ := tmw_star_admits_succ segs _ _ bf cf bs cs Hte Hbs rfl rfl rfl
      exact ⟨_, c, Hstar, Hp⟩

theorem mmap_no_error_run_te : ∀ segs pc ph sp brk0 mb rnd lim inp bf cf bs cs,
    tmw segs (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved segs) brk0 mb sp lim inp) bf cf bs cs →
    bufs_modeled bf → bufs_modeled bs → ¬ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp) := by
  intro segs pc ph sp brk0 mb rnd lim inp bf cf bs cs Hte Hbf Hbs
  exact tmw_no_error segs _ _ bf cf bs cs rfl rfl rfl Hte Hbf Hbs

/-- The run-level omni judgment of a fail-or-succeed mmap run. -/
theorem mmap_omni_run_te : ∀ segs pc ph sp brk0 mb rnd lim inp bf cf bs cs,
    tmw segs (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
      (init_model (segments_reserved segs) brk0 mb sp lim inp) bf cf bs cs →
    bufs_modeled bf → bufs_modeled bs →
    omni_run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp (tmw_post bf cf bs cs (in_fs inp)) := by
  intro segs pc ph sp brk0 mb rnd lim inp bf cf bs cs Hte Hbf Hbs
  exact tmw_exec segs _ _ bf cf bs cs Hte Hbf Hbs rfl rfl rfl

theorem mmap_omni_strong_equiv_te :
    ∀ source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd bf cf bs cs inp,
      tmw source_segs
        (init_machine_state source_segs rpc rph rsp rrnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
        (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp) bf cf bs cs →
      tmw target_segs
        (init_machine_state target_segs apc aph asp arnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
        (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp) bf cf bs cs →
      bufs_modeled bf → bufs_modeled bs →
      omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
        (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp := by
  intro source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd bf cf bs cs inp
    Hsource Htarget Hbf Hbs
  refine ⟨?_, .inr ⟨?_, ?_⟩⟩
  · refine coexec_conseq source_segs _ _ _
      (exec_coexec source_segs _ _
        (mmap_omni_run_te source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp bf cf bs cs Hsource Hbf Hbs)) ?_
    rintro tr o (⟨_, Hx⟩ | ⟨_, Hx⟩) <;> exact never_errors_covered source_segs _ _ (exits_with_never_errors _ _ _ Hx)
  · apply (trace_equiv_iff_omni _ _ _ _ _ _ _).1
    intro tr
    exact (mmap_obs_iff_te source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp bf cf bs cs
      Hsource Hbf Hbs tr).trans
      (mmap_obs_iff_te target_segs apc aph asp abrk amb arnd target_alloc_limit inp bf cf bs cs Htarget Hbf Hbs tr).symm
  · apply (bh_errors_iff _ _ _ _).1
    exact mmap_no_error_run_te target_segs apc aph asp abrk amb arnd target_alloc_limit inp bf cf bs cs Htarget Hbf Hbs

/-- The `Equivalence`-level equivalence for two one-mmap binaries whose failure tails and success tails
    agree. -/
theorem mmap_strong_equiv_te :
    ∀ source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim bf cf bs cs inp,
      tmw source_segs
        (init_machine_state source_segs rpc rph rsp rrnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
        (init_model (segments_reserved source_segs) rbrk rmb rsp rlim inp) bf cf bs cs →
      tmw target_segs
        (init_machine_state target_segs apc aph asp arnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
        (init_model (segments_reserved target_segs) abrk amb asp alim inp) bf cf bs cs →
      bufs_modeled bf → bufs_modeled bs →
      modeled (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp) ∧
        equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
          (run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp) := by
  intro source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim bf cf bs cs inp
    Hsource Htarget Hbf Hbs
  refine ⟨no_error_run_modeled _ _ _ _ _ _ _ _ _
    (mmap_no_error_run_te source_segs rpc rph rsp rbrk rmb rrnd rlim inp bf cf bs cs Hsource Hbf Hbs), .inr ⟨?_, ?_⟩⟩
  · intro tr
    exact (mmap_obs_iff_te source_segs rpc rph rsp rbrk rmb rrnd rlim inp bf cf bs cs Hsource Hbf Hbs tr).trans
      (mmap_obs_iff_te target_segs apc aph asp abrk amb arnd alim inp bf cf bs cs Htarget Hbf Hbs tr).symm
  · exact mmap_no_error_run_te target_segs apc aph asp abrk amb arnd alim inp bf cf bs cs Htarget Hbf Hbs

end LPS
