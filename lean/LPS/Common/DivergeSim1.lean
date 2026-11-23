import LPS.Common.PropExec5
import LPS.Common.CatSim1

/-!
# LPS `theories/Common/DivergeSim.v` (f1006fe8), part 1: silently diverging branches

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Common/DivergeSim.v` at f1006fe8 (image-INDEPENDENT proof library), up to
`End WithSegs` (DivergeSim.v:1-659): a configuration set closed under the one deterministic silent step
(`silent_loop`) emits nothing, never errors and refutes `all_traces_error`; the reach-style
`to_spin` into a one-step fixpoint (the self-jump `j .`), its smart constructors, the proof-facing
`spin_*` facts, and the executable witness `spin_c`. Part 2 (DivergeSim2) has the worked examples.
No coinduction is needed (as in the source).

What changed and why:
- `is_prefix_app_mono` (DivergeSim.v:114) has exactly the statement of CatSim.v's lemma of the same
  name; both are `LPS.is_prefix_app_mono` here, so this file imports CatSim1's instead of redeclaring it.
- DivergeSim.v's `v_addi_0` is `v_addi_0_div` here: PropExec.v has a lemma of the same name (not yet
  ported; it will land as `LPS.v_addi_0`).
- `mi_account_step_halted` is proved directly from `mi_account_step`'s definition (DivergeSim.v cites
  Run.v's `mi_account_step_model_frame`, not ported), and `silent_loop_no_unmodeled` inlines Run.v's
  `no_error_no_unmodeled` (not ported) through Run3's `unmodeled_at_sstep_error`.
- The Ltacs `div_vm_refl` and `prove_to_spin` are not ported (proof scripts: a concrete `spin_c` goal
  closes by `decide` here).
- Section `WithSegs`' variable `segs` is the leading explicit argument; `Context {fx : FPState}` is an
  instance argument of `step_j_self`, the one lemma that uses it. Rocq's `Z.eqb` is `==`.
-/

namespace LPS
open RiscvSemantics instr core

/-! ### Prefix-order helpers -/

theorem is_prefix_nil_inv {A : Type} : ∀ (tr : List A), is_prefix tr [] → tr = [] := by
  intro tr h
  cases tr with
  | nil => rfl
  | cons _ _ => exact h.elim

/-! ### Accounted-step plumbing -/

/-- An instruction that touches no memory materializes nothing, whatever the lazy ledger holds. -/
theorem materialize_model_accesses_nil : ∀ m, materialize_model_accesses m [] = some m := by
  intro m
  obtain ⟨fd, ⟨maps, lazy, mat⟩, io, fs, proc, lim, time⟩ := m
  simp [materialize_model_accesses, materialize_accesses, newly_materialized_pages, accesses_pages,
    with_vm_backing, m_vm_lazy, m_vm_materialized, m_vmmaps]

/-- Read an accounted step off a raw access report. -/
theorem mi_account_step_of_accesses : ∀ segs ms model ms' ranges,
    RiscvSemantics.step_accesses segs ms = .MachineOk (mkAccessReport ms' ranges) →
    mi_account_step segs ms model =
      match materialize_model_accesses model ranges with
      | some model' => .MachineOk (ms', model')
      | none => .MachineFault := by
  intro segs ms model ms' ranges h
  unfold mi_account_step
  rw [h]
  rfl

/-- An access-free instruction steps the machine and leaves the model alone. -/
theorem mi_account_step_no_access : ∀ segs ms model ms',
    RiscvSemantics.step_accesses segs ms = .MachineOk (mkAccessReport ms' []) →
    mi_account_step segs ms model = .MachineOk (ms', model) := by
  intro segs ms model ms' h
  rw [mi_account_step_of_accesses segs ms model ms' [] h, materialize_model_accesses_nil]

/-- An accounted instruction step preserves haltedness. -/
theorem mi_account_step_halted : ∀ segs ms model ms' model',
    mi_account_step segs ms model = .MachineOk (ms', model') → m_halted model' = m_halted model := by
  intro segs ms model ms' model' h
  unfold mi_account_step at h
  cases hs : step_accesses segs ms with
  | MachineOk report =>
    rw [hs] at h
    simp only at h
    cases hm : materialize_model_accesses model report.accessed_ranges with
    | none => rw [hm] at h; cases h
    | some m2 =>
      rw [hm] at h
      cases h
      unfold materialize_model_accesses at hm
      split at hm
      · cases hm; rfl
      · cases hm
  | MachineFault => rw [hs] at h; cases h
  | MachineUnmodeled => rw [hs] at h; cases h

/-! ### The self-jump instruction: the accounted one-step fixpoint -/

theorem v_addi_0_div : ∀ a : word, v_addi a 0 = a := by
  intro a; unfold v_addi; rw [Int.add_zero]; exact Z_to_bv_bv_unsigned a

/-- A decoded `Jal x0 imm` with `bv_signed imm = 0` is a one-step fixpoint with an EMPTY access report,
    for an arbitrary machine state with no pending syscall. -/
theorem self_jump_step_accesses : ∀ segs (ms : machine_state) w (rd : reg) (imm : bv 21) sz,
    ms.ms_svc_pending = none → fetch_word segs (ms_pc ms) = some w → is_ecall w = false →
    decode_any w = some (Jal rd imm, sz) → is_x0 rd = true → bv_signed imm = 0 →
    RiscvSemantics.step_accesses segs ms = .MachineOk (mkAccessReport ms []) := by
  intro segs ms w rd imm sz hsvc hfetch hecall hdecode hx0 himm
  simp only [step_accesses, hfetch, decode_exec_accesses, hecall, Bool.false_eq_true, ↓reduceIte, hdecode, exec,
    rset, hx0, interp_eff_accesses, with_pc, b_addsext, himm, v_addi_0_div]
  obtain ⟨regs, fregs, pc, svc, resv, fcsr, mem, rom⟩ := ms
  simp only at hsvc
  subst hsvc
  rfl

/-- The same, at the accounted level: a fixpoint of `mi_account_step` with the model UNCHANGED. -/
theorem self_jump_account_fix : ∀ segs ms model w (rd : reg) (imm : bv 21) sz,
    ms.ms_svc_pending = none → fetch_word segs (ms_pc ms) = some w → is_ecall w = false →
    decode_any w = some (Jal rd imm, sz) → is_x0 rd = true → bv_signed imm = 0 →
    mi_account_step segs ms model = .MachineOk (ms, model) := by
  intro segs ms model w rd imm sz h1 h2 h3 h4 h5 h6
  exact mi_account_step_no_access segs ms model ms (self_jump_step_accesses segs ms w rd imm sz h1 h2 h3 h4 h5 h6)

/-- The `mkst` spelling, for symbolic straight-line proofs. -/
theorem step_j_self [FPState] : ∀ segs regs pc mem rom w (rd : reg) (imm : bv 21) sz,
    fetch_word segs pc = some w → is_ecall w = false → decode_any w = some (Jal rd imm, sz) →
    is_x0 rd = true → bv_signed imm = 0 →
    RiscvSemantics.step segs (mkst regs pc mem rom) = .MachineOk (mkst regs pc mem rom) := by
  intro segs regs pc mem rom w rd imm sz hf he hd hx0 hi
  unfold RiscvSemantics.step
  rw [self_jump_step_accesses segs (mkst regs pc mem rom) w rd imm sz rfl hf he hd hx0 hi]
  rfl

/-! ### `silent_loop`: a step-closed set of effect-free configurations -/

def silent_loop (segs : List Segment) (P : config → Prop) : Prop :=
  ∀ c, P c → m_halted c.cfg_model = none ∧ c.cfg_ms.ms_svc_pending = none ∧
    ∃ ms' model', mi_account_step segs c.cfg_ms c.cfg_model = .MachineOk (ms', model') ∧ P (mkCfg ms' model')

/-- The finite-cycle instance is DEFINITIONAL. -/
theorem silent_loop_cycle (segs : List Segment) : ∀ (cs : List config),
    (∀ c, c ∈ cs → m_halted c.cfg_model = none ∧ c.cfg_ms.ms_svc_pending = none ∧
      ∃ ms' model', mi_account_step segs c.cfg_ms c.cfg_model = .MachineOk (ms', model') ∧ mkCfg ms' model' ∈ cs) →
    silent_loop segs (fun c => c ∈ cs) :=
  fun _ h => h

/-- From a `silent_loop` configuration the ONLY transition is the silent instruction step. -/
theorem silent_loop_sstep (segs : List Segment) : ∀ P c evs to, silent_loop segs P → P c → sstep segs c evs to →
    evs = [] ∧ ∃ c', to = .SNext c' ∧ P c' := by
  intro P c evs to hloop hp hstep
  obtain ⟨hh, hsvc, ms', model', hacc, hp'⟩ := hloop c hp
  obtain ⟨ms, model⟩ := c
  change m_halted model = none at hh
  change ms.ms_svc_pending = none at hsvc
  change mi_account_step segs ms model = _ at hacc
  cases hstep with
  | sstep_instr _ _ ms2 model2 _ _ h => rw [hacc] at h; cases h; exact ⟨rfl, _, rfl, hp'⟩
  | sstep_instr_fault _ _ _ _ h => rw [hacc] at h; cases h
  | sstep_instr_unmodeled _ _ _ _ h => rw [hacc] at h; cases h
  | sstep_syscall _ _ _ _ _ _ _ _ h => rw [hsvc] at h; cases h
  | sstep_syscall_materialization_fault _ _ _ _ _ _ _ h => rw [hsvc] at h; cases h
  | sstep_exit _ _ _ _ _ _ _ _ h => rw [hsvc] at h; cases h
  | sstep_killed _ _ _ _ _ _ _ _ h => rw [hsvc] at h; cases h
  | sstep_syscall_unmodeled _ _ _ _ h => rw [hsvc] at h; cases h

/-- One-level case analysis on a `star` derivation. -/
theorem star_case (segs : List Segment) : ∀ c tr c', star segs c tr c' →
    (tr = [] ∧ c' = c) ∨ ∃ evs c2 tr2, sstep segs c evs (.SNext c2) ∧ star segs c2 tr2 c' ∧ tr = evs ++ tr2 := by
  intro c tr c' h
  cases h with
  | star_refl => exact .inl ⟨rfl, rfl⟩
  | star_step _ evs c2 tr2 _ hs ht => exact .inr ⟨evs, c2, tr2, hs, ht, rfl⟩

/-- A finite run from inside the loop emits nothing and stays inside. -/
theorem silent_loop_star (segs : List Segment) : ∀ P, silent_loop segs P →
    ∀ c tr c', star segs c tr c' → P c → tr = [] ∧ P c' := by
  intro P hloop c tr c' hstar
  induction hstar with
  | star_refl => exact fun hp => ⟨rfl, hp⟩
  | star_step c1 evs c2 tr c3 hstep _ ih =>
    intro hp
    obtain ⟨rfl, c2', heq, hp2⟩ := silent_loop_sstep segs P c1 evs _ hloop hp hstep
    cases heq
    obtain ⟨rfl, hp3⟩ := ih hp2
    exact ⟨rfl, hp3⟩

theorem silent_loop_star_nil (segs : List Segment) : ∀ P c tr c', silent_loop segs P → P c → star segs c tr c' →
    tr = [] :=
  fun P c tr c' hloop hp hstar => (silent_loop_star segs P hloop c tr c' hstar hp).1

/-- No error transition is reachable from inside the loop. -/
theorem silent_loop_no_error (segs : List Segment) : ∀ P c, silent_loop segs P → P c → ¬ reaches_error segs c := by
  rintro P c hloop hp ⟨tr, c2, evs, hstar, herr⟩
  obtain ⟨_, hp2⟩ := silent_loop_star segs P hloop c tr c2 hstar hp
  obtain ⟨_, c', heq, _⟩ := silent_loop_sstep segs P c2 evs _ hloop hp2 herr
  cases heq

/-- ... and a fortiori nothing unmodeled is reachable. -/
theorem silent_loop_no_unmodeled (segs : List Segment) : ∀ P c, silent_loop segs P → P c →
    ¬ reaches_unmodeled segs c := by
  rintro P c hloop hp ⟨tr, c', hstar, hun⟩
  obtain ⟨evs, hss⟩ := unmodeled_at_sstep_error segs _ hun
  exact silent_loop_no_error segs P c hloop hp ⟨tr, c', evs, hstar, hss⟩

/-- The loop's observation set is exactly {[]}. -/
theorem silent_loop_obs_iff (segs : List Segment) : ∀ P c, silent_loop segs P → P c →
    ∀ tr, obs_trace segs c tr ↔ tr = [] := by
  intro P c hloop hp tr
  constructor
  · rintro ⟨tr', c2, hstar, hpre⟩
    rw [silent_loop_star_nil segs P c tr' c2 hloop hp hstar] at hpre
    exact is_prefix_nil_inv tr hpre
  · rintro rfl
    exact obs_trace_nil segs c

/-- The loop is an infinite NON-erroring execution, so it refutes `all_traces_error`. -/
theorem silent_loop_not_all_errors (segs : List Segment) : ∀ P c, silent_loop segs P → P c →
    ¬ all_traces_error segs c := by
  intro P c hloop hp hall
  induction hall with
  | all_traces_error_intro c _ _ ih =>
    obtain ⟨hh, hsvc, ms', model', hacc, hp'⟩ := hloop c hp
    obtain ⟨ms, model⟩ := c
    exact ih [] (mkCfg ms' model') (.sstep_instr ms model ms' model' hh hsvc hacc) hp'

/-! ### `to_spin`: a deterministic straight line into a one-step fixpoint -/

inductive to_spin (segs : List Segment) : machine_state → Model → Prop where
  | ts_spin (ms model) :
      ms.ms_svc_pending = none → mi_account_step segs ms model = .MachineOk (ms, model) → to_spin segs ms model
  | ts_step (ms model ms' model') :
      ms.ms_svc_pending = none → mi_account_step segs ms model = .MachineOk (ms', model') → to_spin segs ms' model' →
      to_spin segs ms model

theorem ts_spin_no_access (segs : List Segment) : ∀ ms model, ms.ms_svc_pending = none →
    RiscvSemantics.step_accesses segs ms = .MachineOk (mkAccessReport ms []) → to_spin segs ms model :=
  fun ms model hsvc hstep => .ts_spin ms model hsvc (mi_account_step_no_access segs ms model ms hstep)

theorem ts_step_no_access (segs : List Segment) : ∀ ms model ms', ms.ms_svc_pending = none →
    RiscvSemantics.step_accesses segs ms = .MachineOk (mkAccessReport ms' []) → to_spin segs ms' model →
    to_spin segs ms model :=
  fun ms model ms' hsvc hstep hspin => .ts_step ms model ms' model hsvc (mi_account_step_no_access segs ms model ms' hstep) hspin

theorem ts_spin_no_lazy (segs : List Segment) : ∀ ms model, ms.ms_svc_pending = none → m_vm_lazy model = [] →
    RiscvSemantics.step segs ms = .MachineOk ms → to_spin segs ms model := by
  intro ms model hsvc hlazy hstep
  refine .ts_spin ms model hsvc ?_
  rw [mi_account_step_no_lazy segs ms model hlazy, hstep]

theorem ts_step_no_lazy (segs : List Segment) : ∀ ms model ms', ms.ms_svc_pending = none → m_vm_lazy model = [] →
    RiscvSemantics.step segs ms = .MachineOk ms' → to_spin segs ms' model → to_spin segs ms model := by
  intro ms model ms' hsvc hlazy hstep hspin
  refine .ts_step ms model ms' model hsvc ?_ hspin
  rw [mi_account_step_no_lazy segs ms model hlazy, hstep]

/-- Entering the spin on the literal self-jump instruction. -/
theorem ts_spin_of_step_j (segs : List Segment) : ∀ ms model w (rd : reg) (imm : bv 21) sz,
    ms.ms_svc_pending = none → fetch_word segs (ms_pc ms) = some w → is_ecall w = false →
    decode_any w = some (Jal rd imm, sz) → is_x0 rd = true → bv_signed imm = 0 → to_spin segs ms model :=
  fun ms model w rd imm sz h1 h2 h3 h4 h5 h6 =>
    ts_spin_no_access segs ms model h1 (self_jump_step_accesses segs ms w rd imm sz h1 h2 h3 h4 h5 h6)

/-- The set a `to_spin` derivation stays inside. -/
def spinning (segs : List Segment) (c : config) : Prop := to_spin segs c.cfg_ms c.cfg_model ∧ m_halted c.cfg_model = none

theorem spinning_silent_loop (segs : List Segment) : silent_loop segs (spinning segs) := by
  rintro ⟨ms, model⟩ ⟨hspin, hh⟩
  change to_spin segs ms model at hspin
  change m_halted model = none at hh
  cases hspin with
  | ts_spin _ _ hsvc hfix => exact ⟨hh, hsvc, ms, model, hfix, .ts_spin ms model hsvc hfix, hh⟩
  | ts_step _ _ ms' model' hsvc hacc hspin' =>
    exact ⟨hh, hsvc, ms', model', hacc, hspin', by
      show m_halted model' = none; rw [mi_account_step_halted segs ms model ms' model' hacc]; exact hh⟩

/-! ### The proof-facing trio at a spin state -/

theorem spin_star_nil (segs : List Segment) : ∀ ms model tr c', to_spin segs ms model → m_halted model = none →
    star segs (mkCfg ms model) tr c' → tr = [] :=
  fun ms model tr c' hspin hh hstar =>
    silent_loop_star_nil segs (spinning segs) (mkCfg ms model) tr c' (spinning_silent_loop segs) ⟨hspin, hh⟩ hstar

theorem spin_obs_iff (segs : List Segment) : ∀ ms model, to_spin segs ms model → m_halted model = none →
    ∀ tr, obs_trace segs (mkCfg ms model) tr ↔ tr = [] :=
  fun ms model hspin hh => silent_loop_obs_iff segs (spinning segs) (mkCfg ms model) (spinning_silent_loop segs) ⟨hspin, hh⟩

theorem spin_no_error_run (segs : List Segment) : ∀ ms model, to_spin segs ms model → m_halted model = none →
    ¬ reaches_error segs (mkCfg ms model) :=
  fun ms model hspin hh => silent_loop_no_error segs (spinning segs) (mkCfg ms model) (spinning_silent_loop segs) ⟨hspin, hh⟩

theorem spin_no_sstep_error (segs : List Segment) : ∀ ms model, to_spin segs ms model → m_halted model = none →
    ∀ evs, ¬ sstep segs (mkCfg ms model) evs .SError := by
  intro ms model hspin hh evs herr
  obtain ⟨_, c', heq, _⟩ :=
    silent_loop_sstep segs (spinning segs) (mkCfg ms model) evs .SError (spinning_silent_loop segs) ⟨hspin, hh⟩ herr
  cases heq

theorem spin_no_unmodeled (segs : List Segment) : ∀ ms model, to_spin segs ms model → m_halted model = none →
    ¬ reaches_unmodeled segs (mkCfg ms model) :=
  fun ms model hspin hh =>
    silent_loop_no_unmodeled segs (spinning segs) (mkCfg ms model) (spinning_silent_loop segs) ⟨hspin, hh⟩

/-- The spin refutes the vacuity escape. -/
theorem spin_not_all_errors (segs : List Segment) : ∀ ms model, to_spin segs ms model → m_halted model = none →
    ¬ all_traces_error segs (mkCfg ms model) :=
  fun ms model hspin hh =>
    silent_loop_not_all_errors segs (spinning segs) (mkCfg ms model) (spinning_silent_loop segs) ⟨hspin, hh⟩

/-! ### A run that reaches a spin with prefix `P` contributes exactly the prefixes of `P` -/

theorem obs_trace_of_star (segs : List Segment) : ∀ c0 evs c tr, star segs c0 evs c → is_prefix tr evs →
    obs_trace segs c0 tr :=
  fun _ evs c _ hstar hpre => ⟨evs, c, hstar, hpre⟩

theorem spin_reach_obs (segs : List Segment) : ∀ c0 P ms model, star segs c0 P (mkCfg ms model) →
    to_spin segs ms model → m_halted model = none →
    (∀ tr, is_prefix tr P → obs_trace segs c0 tr) ∧ (∀ tr c', star segs (mkCfg ms model) tr c' → P ++ tr = P) := by
  intro c0 P ms model hstar hspin hh
  refine ⟨fun tr hpre => obs_trace_of_star segs c0 P _ tr hstar hpre, ?_⟩
  intro tr c' htail
  rw [spin_star_nil segs ms model tr c' hspin hh htail, List.append_nil]

/-! ### Executable witness -/

/-- Recognize the literal self-jump (no pending syscall, `Jal x0 imm` with `bv_signed imm = 0`). -/
def is_self_jump (segs : List Segment) (ms : machine_state) : Bool :=
  match ms.ms_svc_pending with
  | some _ => false
  | none =>
    match fetch_word segs (ms_pc ms) with
    | some w =>
      if is_ecall w then false else
      match decode_any w with
      | some (Jal rd imm, _) => is_x0 rd && (bv_signed imm == 0)
      | _ => false
    | none => false

theorem is_self_jump_to_spin (segs : List Segment) : ∀ ms model, is_self_jump segs ms = true → to_spin segs ms model := by
  intro ms model h
  cases hsvc : ms.ms_svc_pending with
  | some _ => simp only [is_self_jump, hsvc] at h; cases h
  | none =>
    cases hfetch : fetch_word segs (ms_pc ms) with
    | none => simp only [is_self_jump, hsvc, hfetch] at h; cases h
    | some w =>
      cases hecall : is_ecall w with
      | true => simp only [is_self_jump, hsvc, hfetch, hecall, ↓reduceIte] at h; cases h
      | false =>
        cases hdecode : decode_any w with
        | none => simp only [is_self_jump, hsvc, hfetch, hecall, hdecode, Bool.false_eq_true, ↓reduceIte] at h
        | some p =>
          obtain ⟨i, sz⟩ := p
          simp only [is_self_jump, hsvc, hfetch, hecall, hdecode, Bool.false_eq_true, ↓reduceIte] at h
          cases i with
          | Jal rd imm =>
            simp only [Bool.and_eq_true, beq_iff_eq] at h
            exact ts_spin_of_step_j segs ms model w rd imm sz hsvc hfetch hecall hdecode h.1 h.2
          | _ => simp at h

/-- Fuel-bounded executable straight-line-to-spin check (mirroring `ExitSim.sim_c`). -/
def spin_c (segs : List Segment) : Nat → machine_state → Model → Bool
  | 0, _, _ => false
  | fuel' + 1, ms, model =>
    if is_self_jump segs ms then true
    else
      match ms.ms_svc_pending with
      | some _ => false
      | none =>
        match mi_account_step segs ms model with
        | .MachineOk (ms', model') => spin_c segs fuel' ms' model'
        | _ => false

theorem spin_c_to_spin (segs : List Segment) : ∀ fuel ms model, spin_c segs fuel ms model = true → to_spin segs ms model := by
  intro fuel
  induction fuel with
  | zero => intro ms model h; simp [spin_c] at h
  | succ fuel ih =>
    intro ms model h
    simp only [spin_c] at h
    cases hj : is_self_jump segs ms with
    | true => exact is_self_jump_to_spin segs ms model hj
    | false =>
      rw [hj] at h
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      cases hsvc : ms.ms_svc_pending with
      | some _ => rw [hsvc] at h; cases h
      | none =>
        rw [hsvc] at h
        cases hacc : mi_account_step segs ms model with
        | MachineOk p =>
          obtain ⟨ms', model'⟩ := p
          rw [hacc] at h
          exact .ts_step ms model ms' model' hsvc hacc (ih ms' model' h)
        | MachineFault => rw [hacc] at h; cases h
        | MachineUnmodeled => rw [hacc] at h; cases h

end LPS
