import LPS.Common.FileSim1

/-!
# LPS `theories/Common/FileSim.v` (f1006fe8), part 2: `to_fout`, the exact (exit code, final fs) outcome set

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Common/FileSim.v` at f1006fe8 (shared proof library, not the trusted specification
there), FileSim.v:505-1028: `fout_trace`, and `Section WithSegs`: the judgment `to_fout segs ms model U`
(the reachable set of (code, fs) outcomes is EXACTLY `U`; leaves are exit ecalls, interior nodes
event-free never-halting never-erroring syscalls branching over every admissible resolution), its glue
(`tfo_msteps`, `tfo_equiv`, `to_fout_nonempty`), the one-step inversion `sstep_fsys_inv`, the omni
reading `to_fout_exec` with `fout_post`, `to_fout_star_only`/`to_fout_star_admits`, the no-error
invariant (`to_fout_progress`, `fon_path`, ..., `to_fout_no_error`), the escape plumbing
(`star_syscall_nil`, `reaches_error_star`, `spec_err_error`, `msteps_spec_err_error`), and the
ergonomic nodes `tfo_exit_code`, `tfo_sys_det`.

Section `WithSegs`' variable `segs` is the leading explicit argument of the items that use it.

Not ported: `spec_err_all_traces_error` and `msteps_spec_err_all_traces_error`. Their proof is that a
syscall whose relational spec admits `Unmodeled` admits no `Ok` outcome, which FileSim.v reads off the
verified checker (`Checks.ExecutableSpecs.check_syscall_complete_unmodeled` and
`check_syscall_complete_ok`: one checker verdict per effect). That checker (the dispatcher over every
arm, with the soundness and completeness proofs of every arm) is not ported to Lean, and the fact is not
derivable from the relational spec without it.
-/

namespace LPS
open RiscvSemantics OmniRun InputStream

def fout_trace (o : word × Fs) : List event := [.ExitEv o.1 o.2]

/-- `to_fout segs ms model U`: from `ms` and `model`, the reachable set of (code, fs) outcomes is
    exactly `U`. -/
inductive to_fout (segs : List Segment) : machine_state → Model → ((word × Fs) → Prop) → Prop where
  | tfo_exit (ms model x8) (U : (word × Fs) → Prop) :
      ms.ms_svc_pending = some x8 → is_exit_no x8 →
      (∀ o, U o ↔ o = (bv_and (ms_gpr ms 0) (Z_to_bv 64 255), m_fs model)) →
      to_fout segs ms model U
  | tfo_step (ms ms' model U) :
      ms.ms_svc_pending = none → RiscvSemantics.step segs ms = .MachineOk ms' →
      to_fout segs ms' model U → to_fout segs ms model U
  | tfo_sys (ms model x8) (T : SyscallEffect → Model → (word × Fs) → Prop) (U : (word × Fs) → Prop) :
      ms.ms_svc_pending = some x8 →
      ¬ syscall_spec (sys_input segs ms x8) model Unmodeled →
      (∃ eff model' evs, syscall_spec (sys_input segs ms x8) model (Ok eff model' evs)) →
      (∀ eff model' evs, syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) →
        evs = [] ∧ m_halted model' = none ∧ m_vm_lazy model' = []) →
      (∀ eff model' evs, syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) →
        to_fout segs (advance_past_svc (apply_effect ms eff)) model' (T eff model')) →
      (∀ o, U o ↔ ∃ eff model' evs, syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ∧ T eff model' o) →
      to_fout segs ms model U

section
variable (segs : List Segment)

/-- Prepend a deterministic instruction run. -/
theorem tfo_msteps : ∀ ms ms' model U, msteps segs ms ms' → to_fout segs ms' model U → to_fout segs ms model U := by
  intro ms ms' model U H
  induction H with
  | mst_refl => exact id
  | mst_step ms ms1 ms2 hsvc hstep _ ih => exact fun h => .tfo_step _ _ _ _ hsvc hstep (ih h)

/-- Rewire the outcome set along an extensional equivalence. -/
theorem tfo_equiv : ∀ ms model U V, to_fout segs ms model U → (∀ o, V o ↔ U o) → to_fout segs ms model V := by
  intro ms model U V hto
  induction hto generalizing V with
  | tfo_exit ms model x8 U hsvc hx8 hU =>
    intro hV; exact .tfo_exit ms model x8 V hsvc hx8 (fun o => (hV o).trans (hU o))
  | tfo_step ms ms' model U hsvc hstep _ ih =>
    intro hV; exact .tfo_step _ _ _ _ hsvc hstep (ih V hV)
  | tfo_sys ms model x8 T U hsvc hne hrec hshape hcont hU _ =>
    intro hV; exact .tfo_sys ms model x8 T V hsvc hne hrec hshape hcont (fun o => (hV o).trans (hU o))

/-- Every `to_fout` outcome set is inhabited. -/
theorem to_fout_nonempty : ∀ ms model U, to_fout segs ms model U → ∃ o, U o := by
  intro ms model U hto
  induction hto with
  | tfo_exit ms model x8 U _ _ hU => exact ⟨_, (hU _).2 rfl⟩
  | tfo_step _ _ _ _ _ _ _ ih => exact ih
  | tfo_sys ms model x8 T U _ _ hrec _ _ hU ih =>
    obtain ⟨eff, model', evs, hspec⟩ := hrec
    obtain ⟨o, ho⟩ := ih eff model' evs hspec
    exact ⟨o, (hU o).2 ⟨eff, model', evs, hspec, ho⟩⟩

/-- One-step inversion at a `tfo_sys` ecall. -/
theorem sstep_fsys_inv : ∀ ms model x8 evs st, m_halted model = none → m_vm_lazy model = [] →
    ms.ms_svc_pending = some x8 → ¬ syscall_spec (sys_input segs ms x8) model Unmodeled →
    (∀ eff model' evs', syscall_spec (sys_input segs ms x8) model (Ok eff model' evs') →
      evs' = [] ∧ m_halted model' = none ∧ m_vm_lazy model' = []) →
    sstep segs (mkCfg ms model) evs st →
    ∃ eff model', syscall_spec (sys_input segs ms x8) model (Ok eff model' []) ∧ evs = [] ∧
      st = .SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model') := by
  intro ms model x8 evs st hh hlazy hsvc hne hshape hss
  cases hss with
  | sstep_instr _ _ _ _ _ h => rw [hsvc] at h; cases h
  | sstep_instr_fault _ _ _ h => rw [hsvc] at h; cases h
  | sstep_instr_unmodeled _ _ _ h => rw [hsvc] at h; cases h
  | sstep_syscall _ _ x eff model' model'' evs0 _ h hspec _ hmat =>
    rw [hsvc] at h; cases h
    obtain ⟨rfl, _, hlazy'⟩ := hshape eff model' _ hspec
    rw [materialize_model_accesses_no_lazy _ _ hlazy'] at hmat
    cases hmat
    exact ⟨eff, model', hspec, rfl, rfl⟩
  | sstep_syscall_materialization_fault _ _ x eff model' evs0 _ h hspec _ hmat =>
    rw [hsvc] at h; cases h
    obtain ⟨_, _, hlazy'⟩ := hshape eff model' evs0 hspec
    rw [materialize_model_accesses_no_lazy _ _ hlazy'] at hmat
    cases hmat
  | sstep_exit _ _ x eff model' evs0 code _ h hspec hcode _ =>
    rw [hsvc] at h; cases h
    obtain ⟨_, hm, _⟩ := hshape eff model' evs0 hspec
    rw [hm] at hcode; cases hcode
  | sstep_killed _ _ x eff model' evs0 sig _ h hspec hk =>
    rw [hsvc] at h; cases h
    obtain ⟨_, hm, _⟩ := hshape eff model' evs0 hspec
    rw [m_killed_of_m_halted_none _ hm] at hk; cases hk
  | sstep_syscall_unmodeled _ _ x _ h hspec =>
    rw [hsvc] at h; cases h
    exact (hne hspec).elim

end

/-! ### Trace characterization -/

/-- The omni reading of a file-copying run: every execution halts with one of the outcomes, having
    emitted exactly its exit event. -/
def fout_post (U : (word × Fs) → Prop) : post :=
  fun tr o => ∃ out, U out ∧ tr = fout_trace out ∧ exits_with out.1 tr o

section
variable (segs : List Segment)

/-- The exit leaf's transition (Lean-only helper). -/
private theorem tfo_exit_sstep (ms : machine_state) (model : Model) (x8 : word) (hh : m_halted model = none)
    (hsvc : ms.ms_svc_pending = some x8) (hx8 : is_exit_no x8) :
    sstep segs (mkCfg ms model) [.ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
      (.SNext (mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))) := by
  have hx8' : is_exit_no (sys_input segs ms x8).in_sysno := hx8
  exact sstep.sstep_exit ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
    (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model) [] (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
    hh hsvc (exit_dispatch_ok _ model hx8') rfl (m_killed_with_halted _ _)

private theorem instr_sstep_f (ms ms' : machine_state) (model : Model)
    (hh : m_halted model = none) (hlazy : m_vm_lazy model = []) (hsvc : ms.ms_svc_pending = none)
    (hstep : RiscvSemantics.step segs ms = .MachineOk ms') :
    sstep segs (mkCfg ms model) [] (.SNext (mkCfg ms' model)) := by
  refine .sstep_instr ms model ms' model hh hsvc ?_
  rw [mi_account_step_no_lazy segs ms model hlazy, hstep]

theorem to_fout_exec : ∀ ms model U, to_fout segs ms model U → m_halted model = none → m_vm_lazy model = [] →
    OmniRun.exec segs (mkCfg ms model) (fout_post U) := by
  intro ms model U hto
  induction hto with
  | tfo_exit ms model x8 U hsvc hx8 hU =>
    intro hh _
    refine exec_step_only segs _ _ _ _ (tfo_exit_sstep segs ms model x8 hh hsvc hx8)
      (fun evs st hss => sstep_exit_inv segs ms model x8 evs st hh hsvc hx8 hss) ?_
    refine .exec_halt _ _ (by simp [mkCfg, m_halted_with_halted]) ⟨_, (hU _).2 rfl, by simp [fout_trace], ?_⟩
    exact ⟨m_halted_with_halted _ _, m_killed_with_halted _ _⟩
  | tfo_step ms ms' model U hsvc hstep _ ih =>
    intro hh hlazy
    exact exec_step_only segs _ _ _ _ (instr_sstep_f segs ms ms' model hh hlazy hsvc hstep)
      (fun evs st hss => sstep_instr_inv segs ms model ms' evs st hlazy hsvc hstep hss)
      (exec_conseq segs _ _ _ (ih hh hlazy) (fun tr o h => by simpa using h))
  | tfo_sys ms model x8 T U hsvc hne hrec hshape _ hU ih =>
    intro hh hlazy
    refine .exec_step _ _ hh ?_ ?_ ?_
    · obtain ⟨eff, model', evs, hspec⟩ := hrec
      obtain ⟨rfl, hh', hlazy'⟩ := hshape eff model' evs hspec
      exact ⟨[], _, .sstep_syscall ms model x8 eff model' model' [] hh hsvc hspec hh'
        (materialize_model_accesses_no_lazy _ _ hlazy')⟩
    · intro evs hss
      obtain ⟨_, _, _, _, habs⟩ := sstep_fsys_inv segs ms model x8 evs .SError hh hlazy hsvc hne hshape hss
      cases habs
    · intro evs c' hss
      obtain ⟨eff, model', hspec, rfl, hc'⟩ := sstep_fsys_inv segs ms model x8 evs _ hh hlazy hsvc hne hshape hss
      cases hc'
      obtain ⟨_, hh', hlazy'⟩ := hshape eff model' [] hspec
      refine exec_conseq segs _ _ _ (ih eff model' [] hspec hh' hlazy') ?_
      rintro tr o ⟨out, hout, heq, hx⟩
      exact ⟨out, (hU out).2 ⟨eff, model', [], hspec, hout⟩, by simpa using heq, hx⟩

theorem to_fout_star_only : ∀ ms model U, to_fout segs ms model U → m_halted model = none → m_vm_lazy model = [] →
    ∀ tr c, star segs (mkCfg ms model) tr c → ∃ o, U o ∧ is_prefix tr (fout_trace o) := by
  intro ms model U hto hh hlazy tr c hstar
  obtain ⟨tr', o, _, out, hout, heq, _⟩ :=
    exec_realizes segs _ _ (exec_star segs _ _ _ _ (to_fout_exec segs ms model U hto hh hlazy) hstar)
  exact ⟨out, hout, by rw [← heq]; exact is_prefix_app _ _⟩

theorem to_fout_star_admits : ∀ ms model U, to_fout segs ms model U → m_halted model = none → m_vm_lazy model = [] →
    ∀ o, U o → ∃ c, star segs (mkCfg ms model) (fout_trace o) c := by
  intro ms model U hto
  induction hto with
  | tfo_exit ms model x8 U hsvc hx8 hU =>
    intro hh _ o ho
    rw [(hU o).1 ho]
    exact ⟨_, star_one segs _ _ _ (tfo_exit_sstep segs ms model x8 hh hsvc hx8)⟩
  | tfo_step ms ms' model U hsvc hstep _ ih =>
    intro hh hlazy o ho
    obtain ⟨c, hstar⟩ := ih hh hlazy o ho
    exact ⟨c, star.star_step _ [] _ _ _ (instr_sstep_f segs ms ms' model hh hlazy hsvc hstep) hstar⟩
  | tfo_sys ms model x8 T U hsvc _ _ hshape _ hU ih =>
    intro hh hlazy o ho
    obtain ⟨eff, model', evs, hspec, ht⟩ := (hU o).1 ho
    obtain ⟨rfl, hh', hlazy'⟩ := hshape eff model' evs hspec
    obtain ⟨c, hstar⟩ := ih eff model' [] hspec hh' hlazy' o ht
    exact ⟨c, star.star_step _ [] _ _ _ (.sstep_syscall ms model x8 eff model' model' [] hh hsvc hspec hh'
      (materialize_model_accesses_no_lazy _ _ hlazy')) hstar⟩

/-! ### No-error characterization -/

theorem to_fout_progress : ∀ ms model U, to_fout segs ms model U → m_halted model = none → m_vm_lazy model = [] →
    ∀ evs st, sstep segs (mkCfg ms model) evs st →
      ∃ ms' model', st = .SNext (mkCfg ms' model') ∧
        (m_halted model' ≠ none ∨ (m_halted model' = none ∧ m_vm_lazy model' = [] ∧ ∃ U', to_fout segs ms' model' U')) := by
  intro ms model U hto
  induction hto with
  | tfo_exit ms model x8 U hsvc hx8 _ =>
    intro hh _ evs st hss
    obtain ⟨_, rfl⟩ := sstep_exit_inv segs ms model x8 evs st hh hsvc hx8 hss
    exact ⟨_, _, rfl, .inl (by simp [m_halted_with_halted])⟩
  | tfo_step ms ms' model U hsvc hstep hto _ =>
    intro hh hlazy evs st hss
    obtain ⟨_, rfl⟩ := sstep_instr_inv segs ms model ms' evs st hlazy hsvc hstep hss
    exact ⟨_, _, rfl, .inr ⟨hh, hlazy, U, hto⟩⟩
  | tfo_sys ms model x8 T U hsvc hne _ hshape hcont _ _ =>
    intro hh hlazy evs st hss
    obtain ⟨eff, model', hspec, _, rfl⟩ := sstep_fsys_inv segs ms model x8 evs st hh hlazy hsvc hne hshape hss
    obtain ⟨_, hh', hlazy'⟩ := hshape eff model' [] hspec
    exact ⟨_, _, rfl, .inr ⟨hh', hlazy', T eff model', hcont eff model' [] hspec⟩⟩

def fon_path (c : config) : Prop :=
  (m_halted c.cfg_model = none ∧ m_vm_lazy c.cfg_model = [] ∧ ∃ U, to_fout segs c.cfg_ms c.cfg_model U) ∨
  m_halted c.cfg_model ≠ none

theorem fon_path_step : ∀ c evs c', fon_path segs c → sstep segs c evs (.SNext c') → fon_path segs c' := by
  rintro ⟨ms, model⟩ evs ⟨ms', model'⟩ hop hss
  rcases hop with ⟨hh, hlazy, U, hto⟩ | hh
  · obtain ⟨ms'', model'', hst, hcase⟩ := to_fout_progress segs ms model U hto hh hlazy evs _ hss
    cases hst
    rcases hcase with hhz | ⟨hhz, hlazy', U', hto'⟩
    · exact .inr hhz
    · exact .inl ⟨hhz, hlazy', U', hto'⟩
  · exact absurd (sstep_from_running segs _ _ _ hss) hh

theorem fon_path_no_error : ∀ c evs, fon_path segs c → ¬ sstep segs c evs .SError := by
  rintro ⟨ms, model⟩ evs hop hss
  rcases hop with ⟨hh, hlazy, U, hto⟩ | hh
  · obtain ⟨_, _, hst, _⟩ := to_fout_progress segs ms model U hto hh hlazy evs _ hss
    cases hst
  · exact hh (sstep_from_running segs _ _ _ hss)

theorem star_fon_path : ∀ c tr c', fon_path segs c → star segs c tr c' → fon_path segs c' :=
  star_inv segs (fon_path segs) (fon_path_step segs)

theorem to_fout_no_error : ∀ ms model U, to_fout segs ms model U → m_halted model = none → m_vm_lazy model = [] →
    ¬ reaches_error segs (mkCfg ms model) := by
  intro ms model U hto hh hlazy
  exact exec_no_error segs _ (exec_conseq segs _ _ _ (to_fout_exec segs ms model U hto hh hlazy)
    (fun _ _ ⟨_, _, _, hx⟩ => exits_with_never_errors _ _ _ hx))

/-! ### Escape plumbing: reach a syscall-Unmodeled through a star with silent syscalls -/

theorem star_syscall_nil : ∀ ms model x8 eff model', m_halted model = none → ms.ms_svc_pending = some x8 →
    syscall_spec (sys_input segs ms x8) model (Ok eff model' []) → m_halted model' = none → m_vm_lazy model' = [] →
    star segs (mkCfg ms model) [] (mkCfg (advance_past_svc (apply_effect ms eff)) model') := by
  intro ms model x8 eff model' hh hsvc hspec hh' hlazy
  exact star_one segs _ _ _ (.sstep_syscall ms model x8 eff model' model' [] hh hsvc hspec hh'
    (materialize_model_accesses_no_lazy _ _ hlazy))

theorem reaches_error_star : ∀ c tr c', star segs c tr c' → reaches_error segs c' → reaches_error segs c := by
  rintro c tr c' hstar ⟨tr2, c2, evs, hstar2, hss⟩
  exact ⟨tr ++ tr2, c2, evs, star_trans segs _ _ _ _ _ hstar hstar2, hss⟩

theorem spec_err_error : ∀ ms model x8, m_halted model = none → ms.ms_svc_pending = some x8 →
    syscall_spec (sys_input segs ms x8) model Unmodeled → reaches_error segs (mkCfg ms model) := by
  intro ms model x8 hh hsvc hspec
  exact ⟨[], mkCfg ms model, [], .star_refl _, .sstep_syscall_unmodeled ms model x8 hh hsvc hspec⟩

theorem msteps_spec_err_error : ∀ ms ms' model x8, m_halted model = none → m_vm_lazy model = [] →
    msteps segs ms ms' → ms'.ms_svc_pending = some x8 → syscall_spec (sys_input segs ms' x8) model Unmodeled →
    reaches_error segs (mkCfg ms model) := by
  intro ms ms' model x8 hh hlazy hm hsvc hspec
  exact reaches_error_star segs _ _ _ (msteps_star_nil segs ms ms' model hh hlazy hm)
    (spec_err_error segs ms' model x8 hh hsvc hspec)

/-! ### Ergonomic nodes -/

/-- Exit leaf with a small literal code. -/
theorem tfo_exit_code : ∀ ms model x8 code, ms.ms_svc_pending = some x8 → is_exit_no x8 → ms_gpr ms 0 = code →
    bv_and code (Z_to_bv 64 255) = code → to_fout segs ms model (fun o => o = (code, m_fs model)) := by
  intro ms model x8 code hsvc hx8 hg hland
  refine .tfo_exit ms model x8 _ hsvc hx8 ?_
  intro o
  rw [hg, hland]

/-- A syscall with a UNIQUE admissible outcome: sequential composition. -/
theorem tfo_sys_det : ∀ ms model x8 eff model' U, ms.ms_svc_pending = some x8 →
    syscall_spec (sys_input segs ms x8) model (Ok eff model' []) →
    (∀ eff2 m2 evs2, syscall_spec (sys_input segs ms x8) model (Ok eff2 m2 evs2) →
      eff2 = eff ∧ m2 = model' ∧ evs2 = []) →
    ¬ syscall_spec (sys_input segs ms x8) model Unmodeled →
    m_halted model' = none → m_vm_lazy model' = [] →
    to_fout segs (advance_past_svc (apply_effect ms eff)) model' U → to_fout segs ms model U := by
  intro ms model x8 eff model' U hsvc hok huniq hne hh' hlazy' hcont
  refine .tfo_sys ms model x8 (fun _ _ => U) U hsvc hne ⟨eff, model', [], hok⟩ ?_ ?_ ?_
  · intro eff2 m2 evs2 hs
    obtain ⟨_, rfl, rfl⟩ := huniq eff2 m2 evs2 hs
    exact ⟨rfl, hh', hlazy'⟩
  · intro eff2 m2 evs2 hs
    obtain ⟨rfl, rfl, _⟩ := huniq eff2 m2 evs2 hs
    exact hcont
  · intro o
    exact ⟨fun ho => ⟨eff, model', [], hok, ho⟩, fun ⟨_, _, _, _, ht⟩ => ht⟩

end

end LPS
