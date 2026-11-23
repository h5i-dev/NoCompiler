import LPS.Common.SimInv

/-!
# LPS `theories/Common/ExitSim.v` (f1006fe8), part 1: exit-only binaries, the configuration level

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Common/ExitSim.v` at f1006fe8 (shared proof library, not the trusted specification
there), up to `End WithSegs`: the exit-syscall facts read off the relational spec, the deterministic
straight line `to_exit segs code ms` to an exit ecall, its executable witness `sim_c`, the one-step
inversions of `sstep` on the configurations of that line, and the omni judgment `to_exit_exec`
(`OmniRun.exec` with the exact trace and exit code as postcondition) with its corollaries. Part 2
(ExitSim2) has the argc overlay and the run-level packaging.

Section `WithSegs`' variables `segs code` are the leading explicit arguments of the definitions and
lemmas that use them. Rocq's `Z.eqb` is `==` on `Int`; `nth_error l i` is `l[i]?`. The proofs are
Lean's: Rocq's `autorewrite with model` is the State5 lemmas, named.
-/

namespace LPS
open RiscvSemantics OmniRun

/-! ### Exit-syscall spec facts, derived directly from the relational spec -/

def is_exit_no (no : word) : Prop := bv_unsigned no = 93 ∨ bv_unsigned no = 94

theorem syscall_spec_exit :
    ∀ i m o, is_exit_no i.in_sysno → (syscall_spec i m o ↔ exit_spec (in_arg i 0) i m o) := by
  intro i m o h
  have hl : lookup_arm spec_table (bv_unsigned i.in_sysno) =
      some (mkSpecArm (bv_unsigned i.in_sysno) (fun i => exit_spec (in_arg i 0) i)) := by
    rcases h with h | h <;> rw [h] <;> simp [spec_table, lookup_arm, mkSpecArm]
  simp only [syscall_spec, dispatch, hl]
  exact Iff.rfl

/-- The unique admissible exit outcome exists. -/
theorem exit_dispatch_ok :
    ∀ i m, is_exit_no i.in_sysno →
      syscall_spec i m (Ok (mkEffect (Z_to_bv 64 0) [] []) (with_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)) m) []) := by
  intro i m hno
  apply (syscall_spec_exit i m _ hno).2
  show (do set_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)); ret_only (Z_to_bv 64 0)) i m _
  exact ⟨(), _, [], [], rfl, rfl, rfl⟩

/-- Every admissible exit outcome IS that unique one. -/
theorem exit_dispatch_ok_inv :
    ∀ i m eff m' evs, is_exit_no i.in_sysno → syscall_spec i m (Ok eff m' evs) →
      eff = mkEffect (Z_to_bv 64 0) [] [] ∧ m' = with_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)) m ∧ evs = [] := by
  intro i m eff m' evs hno hspec
  have h := (syscall_spec_exit i m _ hno).1 hspec
  change (do set_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)); ret_only (Z_to_bv 64 0)) i m _ at h
  obtain ⟨x, m1, e1, e2, h1, h2, h3⟩ := h
  cases h1
  cases h2
  exact ⟨rfl, rfl, h3⟩

/-- Exit never takes the error transition. -/
theorem exit_dispatch_no_unmodeled : ∀ i m, is_exit_no i.in_sysno → ¬ syscall_spec i m Unmodeled := by
  intro i m hno hspec
  have h := (syscall_spec_exit i m _ hno).1 hspec
  change (do set_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)); ret_only (Z_to_bv 64 0)) i m _ at h
  rcases h with h | ⟨x, m1, e1, _, h2⟩
  · cases h
  · cases h2

/-- `in_arg (sys_input segs ms x8) 0` is `ms_gpr ms 0` (a0). -/
theorem in_arg0_sys_input : ∀ segs ms x8, in_arg (sys_input segs ms x8) 0 = ms_gpr ms 0 := fun _ _ _ => rfl

theorem in_sysno_sys_input : ∀ segs ms x8, (sys_input segs ms x8).in_sysno = x8 := fun _ _ _ => rfl

/-! ### `to_exit`: the deterministic straight line to the exit ecall -/

inductive to_exit (segs : List Segment) (code : word) : machine_state → Prop where
  | te_here (ms x8) : ms.ms_svc_pending = some x8 → is_exit_no x8 → ms_gpr ms 0 = code → to_exit segs code ms
  | te_step (ms ms') :
      ms.ms_svc_pending = none → RiscvSemantics.step segs ms = .MachineOk ms' → to_exit segs code ms' →
      to_exit segs code ms

/-- A fuel-bounded executable witness for `to_exit`. -/
def sim_c (segs : List Segment) (code : word) : Nat → machine_state → Bool
  | 0, _ => false
  | fuel' + 1, ms =>
    match ms.ms_svc_pending with
    | some x8 => ((bv_unsigned x8 == 93) || (bv_unsigned x8 == 94)) && bv_eqb (ms_gpr ms 0) code
    | none =>
      match RiscvSemantics.step segs ms with
      | .MachineOk ms' => sim_c segs code fuel' ms'
      | .MachineFault | .MachineUnmodeled => false

theorem sim_c_to_exit (segs : List Segment) (code : word) :
    ∀ fuel ms, sim_c segs code fuel ms = true → to_exit segs code ms := by
  intro fuel
  induction fuel with
  | zero => intro ms h; simp [sim_c] at h
  | succ fuel ih =>
    intro ms h
    simp only [sim_c] at h
    cases hsvc : ms.ms_svc_pending with
    | some x8 =>
      rw [hsvc] at h
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
      exact .te_here ms x8 hsvc h.1 ((bv_eqb_eq _ _).1 h.2)
    | none =>
      rw [hsvc] at h
      cases hstep : RiscvSemantics.step segs ms with
      | MachineOk ms' => rw [hstep] at h; exact .te_step ms ms' hsvc hstep (ih ms' h)
      | MachineFault => rw [hstep] at h; exact nomatch h
      | MachineUnmodeled => rw [hstep] at h; exact nomatch h

/-! ### Propositional-execution bridges into `sim_c` -/

/-- One executable step: an ordinary (non-syscall) instruction. -/
theorem sim_step (segs : List Segment) (code : word) :
    ∀ fuel ms ms', ms.ms_svc_pending = none → RiscvSemantics.step segs ms = .MachineOk ms' →
      sim_c segs code fuel ms' = true → sim_c segs code (fuel + 1) ms = true := by
  intro fuel ms ms' hsvc hstep hrec
  simp only [sim_c, hsvc, hstep]
  exact hrec

/-- A configuration whose pending syscall is exit/exit_group with a0 = code passes `sim_c` at once. -/
theorem sim_c_exit_now (segs : List Segment) (code : word) :
    ∀ fuel ms x8, ms.ms_svc_pending = some x8 → ((bv_unsigned x8 == 93) || (bv_unsigned x8 == 94)) = true →
      bv_eqb (ms_gpr ms 0) code = true → sim_c segs code (fuel + 1) ms = true := by
  intro fuel ms x8 hsvc hx8 hcode
  simp only [sim_c, hsvc, hx8, hcode, Bool.true_and]

/-- Closing the run: at `ms` (svc not pending) the next instruction is the `ecall` (0x73); a7 selects
    exit/exit_group and a0 carries `code`. -/
theorem sim_ecall_exit (segs : List Segment) (code : word) :
    ∀ fuel ms, ms.ms_svc_pending = none → fetch_word segs (ms_pc ms) = some 0x73 →
      ((bv_unsigned (ms_reg ms 17) == 93) || (bv_unsigned (ms_reg ms 17) == 94)) = true →
      bv_eqb (ms_gpr ms 0) code = true → sim_c segs code (fuel + 2) ms = true := by
  intro fuel ms hsvc hfetch hcheck hcode
  have hstep : RiscvSemantics.step segs ms = .MachineOk { ms with ms_svc_pending := some (ms_reg ms 17) } := by
    simp only [RiscvSemantics.step, step_accesses, hfetch]
    rfl
  exact sim_step segs code (fuel + 1) ms _ hsvc hstep
    (sim_c_exit_now segs code fuel _ (ms_reg ms 17) rfl hcheck hcode)

/-! ### One-step inversions of `sstep` on the two kinds of on-path configurations -/

/-- From a non-syscall state that steps to `ms'`, the ONLY transition is the deterministic instruction
    step; no events, no error. -/
theorem sstep_instr_inv (segs : List Segment) :
    ∀ ms model ms' evs st, m_vm_lazy model = [] → ms.ms_svc_pending = none →
      RiscvSemantics.step segs ms = .MachineOk ms' → sstep segs (mkCfg ms model) evs st →
        evs = [] ∧ st = .SNext (mkCfg ms' model) := by
  intro ms model ms' evs st hlazy hsvc hstep hss
  have hacc := mi_account_step_no_lazy segs ms model hlazy
  rw [hstep] at hacc
  cases hss with
  | sstep_instr _ _ ms'' model'' _ _ h => rw [hacc] at h; cases h; exact ⟨rfl, rfl⟩
  | sstep_instr_fault _ _ _ _ h => rw [hacc] at h; cases h
  | sstep_instr_unmodeled _ _ _ _ h => rw [hacc] at h; cases h
  | sstep_syscall _ _ _ _ _ _ _ _ h => rw [hsvc] at h; cases h
  | sstep_syscall_materialization_fault _ _ _ _ _ _ _ h => rw [hsvc] at h; cases h
  | sstep_exit _ _ _ _ _ _ _ _ h => rw [hsvc] at h; cases h
  | sstep_killed _ _ _ _ _ _ _ _ h => rw [hsvc] at h; cases h
  | sstep_syscall_unmodeled _ _ _ _ h => rw [hsvc] at h; cases h

/-- From an exit ecall configuration, the ONLY transition is `sstep_exit`: it emits the single `ExitEv`
    and halts the model. -/
theorem sstep_exit_inv (segs : List Segment) :
    ∀ ms model x8 evs st, m_halted model = none → ms.ms_svc_pending = some x8 → is_exit_no x8 →
      sstep segs (mkCfg ms model) evs st →
        evs = [.ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)] ∧
          st = .SNext (mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model)) := by
  intro ms model x8 evs st hh hsvc hx8 hss
  cases hss with
  | sstep_instr _ _ _ _ _ h => rw [hsvc] at h; cases h
  | sstep_instr_fault _ _ _ h => rw [hsvc] at h; cases h
  | sstep_instr_unmodeled _ _ _ h => rw [hsvc] at h; cases h
  | sstep_syscall _ _ x eff model' model'' evs0 _ h hspec hh' =>
    rw [hsvc] at h; cases h
    obtain ⟨_, rfl, _⟩ := exit_dispatch_ok_inv _ _ _ _ _ hx8 hspec
    exact absurd hh' (by simp [m_halted_with_halted])
  | sstep_syscall_materialization_fault _ _ x eff model' evs0 _ h hspec hh' =>
    rw [hsvc] at h; cases h
    obtain ⟨_, rfl, _⟩ := exit_dispatch_ok_inv _ _ _ _ _ hx8 hspec
    exact absurd hh' (by simp [m_halted_with_halted])
  | sstep_exit _ _ x eff model' evs0 code _ h hspec hcode _ =>
    rw [hsvc] at h; cases h
    obtain ⟨_, rfl, rfl⟩ := exit_dispatch_ok_inv _ _ _ _ _ hx8 hspec
    rw [m_halted_with_halted] at hcode
    cases hcode
    exact ⟨rfl, rfl⟩
  | sstep_killed _ _ x eff model' evs0 sig _ h hspec hk =>
    rw [hsvc] at h; cases h
    obtain ⟨_, rfl, _⟩ := exit_dispatch_ok_inv _ _ _ _ _ hx8 hspec
    rw [m_killed_with_halted] at hk
    cases hk
  | sstep_syscall_unmodeled _ _ x _ h hspec =>
    rw [hsvc] at h; cases h
    exact (exit_dispatch_no_unmodeled _ _ hx8 hspec).elim

/-- A run cannot leave a halted configuration. -/
theorem star_halted_nil (segs : List Segment) :
    ∀ c tr c', m_halted c.cfg_model ≠ none → star segs c tr c' → tr = [] ∧ c' = c := by
  intro c tr c' hh hstar
  cases hstar with
  | star_refl => exact ⟨rfl, rfl⟩
  | star_step _ _ _ _ _ hss _ => exact absurd (sstep_from_running segs _ _ _ hss) hh

/-! ### The omni reading: one induction over `to_exit` -/

def exit_post (code : word) (fs : Fs) : post :=
  fun tr o => tr = [.ExitEv (bv_and code (Z_to_bv 64 255)) fs] ∧ exits_with (bv_and code (Z_to_bv 64 255)) tr o

theorem to_exit_exec (segs : List Segment) (code : word) :
    ∀ ms model, m_halted model = none → m_vm_lazy model = [] → to_exit segs code ms →
      OmniRun.exec segs (mkCfg ms model) (exit_post code (m_fs model)) := by
  intro ms model hh hlazy hte
  induction hte with
  | te_here ms x8 hsvc hx8 hgpr =>
    subst hgpr
    have hx8' : is_exit_no (sys_input segs ms x8).in_sysno := hx8
    refine exec_step_only segs _ _ [.ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
      (mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model)) ?_
      (fun evs st hss => sstep_exit_inv segs ms model x8 evs st hh hsvc hx8 hss) ?_
    · exact sstep.sstep_exit ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
        (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model) [] (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
        hh hsvc (exit_dispatch_ok _ model hx8') rfl (m_killed_with_halted _ _)
    · exact .exec_halt _ _ (by simp [mkCfg, m_halted_with_halted])
        ⟨by simp, m_halted_with_halted _ _, m_killed_with_halted _ _⟩
  | te_step ms ms' hsvc hstep _ ih =>
    refine exec_step_only segs _ _ [] (mkCfg ms' model) ?_
      (fun evs st hss => sstep_instr_inv segs ms model ms' evs st hlazy hsvc hstep hss) ?_
    · refine .sstep_instr ms model ms' model hh hsvc ?_
      rw [mi_account_step_no_lazy segs ms model hlazy, hstep]
    · exact ih

/-! ### Trace characterisation of an exit-only run: corollaries of `to_exit_exec` -/

theorem to_exit_star_only (segs : List Segment) (code : word) :
    ∀ ms model, m_halted model = none → m_vm_lazy model = [] → to_exit segs code ms →
      ∀ tr c, star segs (mkCfg ms model) tr c →
        tr = [] ∨ tr = [.ExitEv (bv_and code (Z_to_bv 64 255)) (m_fs model)] := by
  intro ms model hh hlazy hte tr c hstar
  obtain ⟨tr', o, _, heq, _⟩ :=
    exec_realizes segs _ _ (exec_star segs _ _ _ _ (to_exit_exec segs code ms model hh hlazy hte) hstar)
  rcases List.append_eq_singleton_iff.1 heq with ⟨h, _⟩ | ⟨h, _⟩
  · exact .inl h
  · exact .inr h

theorem to_exit_star_admits (segs : List Segment) (code : word) :
    ∀ ms model, m_halted model = none → m_vm_lazy model = [] → to_exit segs code ms →
      ∃ c, star segs (mkCfg ms model) [.ExitEv (bv_and code (Z_to_bv 64 255)) (m_fs model)] c := by
  intro ms model hh hlazy hte
  obtain ⟨tr, o, hm, heq, hx⟩ := exec_realizes segs _ _ (to_exit_exec segs code ms model hh hlazy hte)
  cases o with
  | OError c' => exact hx.elim
  | OHalt c' =>
    subst heq
    exact ⟨c', (mexec_halt_star segs _ _ _ hm c' rfl).1⟩

/-! ### No-error characterisation: no reachable configuration takes the error step -/

/-- On-path invariant: still on the straight line, or already halted. -/
def on_path (segs : List Segment) (code : word) (c : config) : Prop :=
  (m_halted c.cfg_model = none ∧ m_vm_lazy c.cfg_model = [] ∧ to_exit segs code c.cfg_ms) ∨
    m_halted c.cfg_model ≠ none

theorem on_path_step (segs : List Segment) (code : word) :
    ∀ c evs c', on_path segs code c → sstep segs c evs (.SNext c') → on_path segs code c' := by
  rintro ⟨ms, model⟩ evs c' hop hss
  rcases hop with ⟨hh, hlazy, hte⟩ | hh
  · cases hte with
    | te_here _ x8 hsvc hx8 _ =>
      obtain ⟨_, hc⟩ := sstep_exit_inv segs ms model x8 evs _ hh hsvc hx8 hss
      cases hc
      exact .inr (by simp [mkCfg, m_halted_with_halted])
    | te_step _ ms0' hsvc hstep hte =>
      obtain ⟨_, hc⟩ := sstep_instr_inv segs ms model ms0' evs _ hlazy hsvc hstep hss
      cases hc
      exact .inl ⟨hh, hlazy, hte⟩
  · exact absurd (sstep_from_running segs _ _ _ hss) hh

theorem on_path_no_error (segs : List Segment) (code : word) :
    ∀ c evs, on_path segs code c → ¬ sstep segs c evs .SError := by
  rintro ⟨ms, model⟩ evs hop hss
  rcases hop with ⟨hh, hlazy, hte⟩ | hh
  · cases hte with
    | te_here _ x8 hsvc hx8 _ =>
      exact nomatch (sstep_exit_inv segs ms model x8 evs _ hh hsvc hx8 hss).2
    | te_step _ ms0' hsvc hstep _ =>
      exact nomatch (sstep_instr_inv segs ms model ms0' evs _ hlazy hsvc hstep hss).2
  · exact hh (sstep_from_running segs _ _ _ hss)

theorem star_on_path (segs : List Segment) (code : word) :
    ∀ c tr c', on_path segs code c → star segs c tr c' → on_path segs code c' :=
  star_inv segs (on_path segs code) (on_path_step segs code)

theorem to_exit_no_error (segs : List Segment) (code : word) :
    ∀ ms model, m_halted model = none → m_vm_lazy model = [] → to_exit segs code ms →
      ¬ reaches_error segs (mkCfg ms model) := by
  intro ms model hh hlazy hte
  exact exec_no_error segs _ (exec_conseq segs _ _ _ (to_exit_exec segs code ms model hh hlazy hte)
    (fun tr o h => exits_with_never_errors _ _ _ h.2))

end LPS
