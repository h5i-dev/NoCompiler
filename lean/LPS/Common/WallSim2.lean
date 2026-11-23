import LPS.Common.WallSim1

/-!
# LPS `theories/Common/WallSim.v` (f1006fe8), part 2: `to_wallexit`, the omni reading, the run level

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Common/WallSim.v` at f1006fe8, WallSim.v:450-932: the exit-after-writes relation
`to_wallexit` whose every write is a `to_wall` retry node, its structural lemmas (`to_wall_k_ex_mut`,
`to_wall_tail_k_ex`, `to_wallexit_bufs_nonempty`, `twe_step`, `msteps_to_wallexit`), the omni reading
(`to_wall_exec_mut`, `to_wexit_nil_exec_aux`, `to_wexit_nil_exec`, `to_wallexit_exec`) and its
corollaries (`to_wallexit_star_admits`, `_no_other_exit`, `_trace_unique`, `_not_silent`,
`_star_only`, `_no_error`), then after `End WithSegsCh`: `wexit1`, `wevents_ch_fd1` and the run-level
packaging (`wall_omni_run`, `wall_obs_iff`, `wall_no_error_run`, `wall_omni_strong_equiv`,
`wall_strong_equiv`).

Conventions as WallSim1 (section variables `segs fd ch` and `Hfd32` are leading explicit arguments of
the items that use them). Rocq's `Forall P l` is `∀ x ∈ l, P x`. Rocq's `Abbreviation wexit1` is a
Lean `abbrev`.
-/

namespace LPS
open RiscvSemantics OmniRun

/-! ### `to_wallexit`: an exit-after-writes run whose every write is a retry loop -/

def to_wallexit (segs : List Segment) (fd : word) : List (List byte) → word → machine_state → Prop
  | [], code, ms => to_wexit segs ms [] code
  | buf :: rest, code, ms => 1 ≤ buf.length ∧ to_wall_tail segs fd ms buf (to_wallexit segs fd rest code)

/-- Every finite wall derivation bottoms out in a continuation state. -/
theorem to_wall_k_ex_mut (segs : List Segment) (fd : word) :
    (∀ ms rest k, to_wall segs fd ms rest k → ∃ ms', k ms') ∧
    (∀ ms rest k, to_wall_tail segs fd ms rest k → ∃ ms', k ms') :=
  to_wall_mutind segs fd (fun _ _ k => ∃ ms', k ms') (fun _ _ k => ∃ ms', k ms')
    (fun _ _ rest _ _ _ _ _ Hnb _ IH => IH rest.length Hnb (Nat.le_refl _))
    (fun ms _ Hk => ⟨ms, Hk⟩)
    (fun _ _ _ _ _ IH => IH)
    (fun _ _ _ _ _ _ _ IH => IH)

theorem to_wall_tail_k_ex (segs : List Segment) (fd : word) :
    ∀ ms rest k, to_wall_tail segs fd ms rest k → ∃ ms', k ms' := (to_wall_k_ex_mut segs fd).2

theorem to_wallexit_bufs_nonempty (segs : List Segment) (fd : word) :
    ∀ bufs code ms, to_wallexit segs fd bufs code ms → ∀ b ∈ bufs, 1 ≤ b.length := by
  intro bufs
  induction bufs with
  | nil => intro _ _ _ b hb; simp at hb
  | cons buf rest IH =>
    intro code ms Hw b hb
    obtain ⟨Hnb, Hw⟩ := Hw
    rcases List.mem_cons.1 hb with rfl | hb
    · exact Hnb
    · obtain ⟨ms', Hk⟩ := to_wall_tail_k_ex segs fd _ _ _ Hw
      exact IH code ms' Hk b hb

/-- Single-instruction prepend. -/
theorem twe_step (segs : List Segment) (fd : word) :
    ∀ ms ms' bufs code, ms.ms_svc_pending = none → RiscvSemantics.step segs ms = .MachineOk ms' →
      to_wallexit segs fd bufs code ms' → to_wallexit segs fd bufs code ms := by
  intro ms ms' bufs code Hsvc Hstep Hw
  cases bufs with
  | nil => exact .tw_step _ _ _ _ Hsvc Hstep Hw
  | cons buf rest => exact ⟨Hw.1, .twt_step _ _ _ _ Hsvc Hstep Hw.2⟩

theorem msteps_to_wallexit (segs : List Segment) (fd : word) :
    ∀ ms ms' bufs code, msteps segs ms ms' → to_wallexit segs fd bufs code ms' → to_wallexit segs fd bufs code ms := by
  intro ms ms' bufs code Hms Hw
  cases bufs with
  | nil => exact msteps_to_wexit segs ms ms' [] code Hms Hw
  | cons buf rest => exact ⟨Hw.1, msteps_to_wall_tail segs fd _ _ _ _ Hms Hw.2⟩

/-! ### The omni reading -/

theorem to_wall_exec_mut (segs : List Segment) (fd ch : word) (Hfd32 : fd32 fd = fd) :
    ∀ model (Q : post), m_halted model = none → m_vm_lazy model = [] → fdchan fd ch model →
      (∀ ms rest k, to_wall segs fd ms rest k → buf_modeled rest →
        (∀ ms', k ms' → OmniRun.exec segs (mkCfg ms' model) Q) →
        OmniRun.exec segs (mkCfg ms model) (fun tr o => ∃ tr', tr = rest.map (event.WriteEv ch) ++ tr' ∧ Q tr' o)) ∧
      (∀ ms rest k, to_wall_tail segs fd ms rest k → buf_modeled rest →
        (∀ ms', k ms' → OmniRun.exec segs (mkCfg ms' model) Q) →
        OmniRun.exec segs (mkCfg ms model) (fun tr o => ∃ tr', tr = rest.map (event.WriteEv ch) ++ tr' ∧ Q tr' o)) := by
  intro model Q Hh Hlazy Hfdc
  apply to_wall_mutind segs fd
  · -- twl_write: every delivered length is covered by the IH
    intro ms x8 rest k Hsvc Hno Hg Hr Hnb Hcont IH Hbm HK
    have Hw : to_wall segs fd ms rest k := .twl_write ms x8 rest k Hsvc Hno Hg Hr Hnb Hcont
    refine .exec_step _ _ Hh ?_ ?_ ?_
    · exact ⟨_, _, twl_write_sstep segs fd ch Hfd32 ms model x8 rest rest.length Hh Hlazy Hfdc Hsvc Hno Hg Hr Hbm
        Hnb (Nat.le_refl _)⟩
    · intro evs Hss
      obtain ⟨n, _, _, _, Habs, _⟩ := sstep_to_wall_inv segs fd ch Hfd32 ms rest k model evs .SError Hh Hlazy Hfdc Hbm Hw Hss
      cases Habs
    · intro evs c' Hss
      obtain ⟨n, Hn1, Hn2, rfl, Hc', _⟩ :=
        sstep_to_wall_inv segs fd ch Hfd32 ms rest k model evs (.SNext c') Hh Hlazy Hfdc Hbm Hw Hss
      cases Hc'
      refine exec_conseq segs _ _ _ (IH n Hn1 Hn2 (buf_modeled_skipn n rest Hbm) HK) ?_
      rintro tr o ⟨tr', rfl, HQ⟩
      refine ⟨tr', ?_, HQ⟩
      rw [← List.append_assoc, ← List.map_append, List.take_append_drop]
  · -- twt_done: the continuation's own judgment
    intro ms k Hk _ HK
    exact exec_conseq segs _ _ _ (HK ms Hk) (fun tr o HQ => ⟨tr, by simp, HQ⟩)
  · -- twt_more
    intro ms rest k _ _ IH Hbm HK
    exact IH Hbm HK
  · -- twt_step: one silent instruction
    intro ms ms' rest k Hsvc Hstep _ IH Hbm HK
    refine exec_step_only segs _ _ [] (mkCfg ms' model) ?_
      (fun evs st Hss => sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss) ?_
    · refine .sstep_instr ms model ms' model Hh Hsvc ?_
      rw [mi_account_step_no_lazy segs ms model Hlazy, Hstep]
    · exact exec_conseq segs _ _ _ (IH Hbm HK) (fun tr o h => by simpa using h)

/-- The exit straight line at the bottom of every `to_wallexit` (needs no channel assumption). -/
theorem to_wexit_nil_exec_aux (segs : List Segment) :
    ∀ ms bufs code model, m_halted model = none → m_vm_lazy model = [] → to_wexit segs ms bufs code → bufs = [] →
      OmniRun.exec segs (mkCfg ms model) (fun tr o => tr = [.ExitEv code (m_fs model)] ∧ exits_with code tr o) := by
  intro ms bufs code model Hh Hlazy Hte
  induction Hte with
  | tw_exit ms x8 Hsvc Hx8 =>
    intro _
    refine exec_step_only segs _ _ _ _ (tw_exit_sstep segs ms model x8 Hh Hsvc Hx8)
      (fun evs st Hss => sstep_exit_inv segs ms model x8 evs st Hh Hsvc Hx8 Hss) ?_
    refine .exec_halt _ _ (by simp [mkCfg, m_halted_with_halted]) ⟨by simp, ?_⟩
    exact ⟨m_halted_with_halted _ _, m_killed_with_halted _ _⟩
  | tw_write => intro Hb; cases Hb
  | tw_step ms ms' bufs code Hsvc Hstep _ IH =>
    intro Hb
    refine exec_step_only segs _ _ [] (mkCfg ms' model) ?_
      (fun evs st Hss => sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss) ?_
    · refine .sstep_instr ms model ms' model Hh Hsvc ?_
      rw [mi_account_step_no_lazy segs ms model Hlazy, Hstep]
    · exact exec_conseq segs _ _ _ (IH Hb) (fun tr o h => by simpa using h)

theorem to_wexit_nil_exec (segs : List Segment) :
    ∀ ms code model, m_halted model = none → m_vm_lazy model = [] → to_wexit segs ms [] code →
      OmniRun.exec segs (mkCfg ms model) (fun tr o => tr = [.ExitEv code (m_fs model)] ∧ exits_with code tr o) :=
  fun ms code model Hh Hlazy Hte => to_wexit_nil_exec_aux segs ms [] code model Hh Hlazy Hte rfl

/-- THE judgment for a retry-loop run: exactly the full-delivery trace, then the exit. -/
theorem to_wallexit_exec (segs : List Segment) (fd ch : word) (Hfd32 : fd32 fd = fd) :
    ∀ bufs code ms model, m_halted model = none → m_vm_lazy model = [] → fdchan fd ch model →
      bufs_modeled bufs → to_wallexit segs fd bufs code ms →
      OmniRun.exec segs (mkCfg ms model)
        (fun tr o => tr = wevents_ch ch bufs ++ [.ExitEv code (m_fs model)] ∧ exits_with code tr o) := by
  intro bufs
  induction bufs with
  | nil =>
    intro code ms model Hh Hlazy _ _ Hw
    simpa [wevents_ch] using to_wexit_nil_exec segs ms code model Hh Hlazy Hw
  | cons buf rest IH =>
    intro code ms model Hh Hlazy Hfdc Hbm Hw
    obtain ⟨_, Hw⟩ := Hw
    have Hb : buf_modeled buf := Hbm buf (List.mem_cons_self ..)
    have Hbs : bufs_modeled rest := fun b h => Hbm b (List.mem_cons_of_mem _ h)
    refine exec_conseq segs _ _ _ ((to_wall_exec_mut segs fd ch Hfd32 model _ Hh Hlazy Hfdc).2 ms buf
      (to_wallexit segs fd rest code) Hw Hb (fun ms' Hk => IH code ms' model Hh Hlazy Hfdc Hbs Hk)) ?_
    rintro tr o ⟨tr', rfl, Heq, Hx⟩
    refine ⟨?_, Hx⟩
    rw [Heq]
    simp [wevents_ch, List.append_assoc]

/-! ### Corollaries of `to_wallexit_exec` -/

theorem to_wallexit_star_admits (segs : List Segment) (fd ch : word) (Hfd32 : fd32 fd = fd) :
    ∀ bufs code ms model, m_halted model = none → m_vm_lazy model = [] → fdchan fd ch model →
      bufs_modeled bufs → to_wallexit segs fd bufs code ms →
      ∃ c, star segs (mkCfg ms model) (wevents_ch ch bufs ++ [.ExitEv code (m_fs model)]) c := by
  intro bufs code ms model Hh Hlazy Hfdc Hbm Hw
  obtain ⟨tr, o, Hm, Heq, Hx⟩ := exec_realizes segs _ _ (to_wallexit_exec segs fd ch Hfd32 bufs code ms model Hh Hlazy Hfdc Hbm Hw)
  cases o with
  | OError _ => exact Hx.elim
  | OHalt c' =>
    subst Heq
    exact ⟨c', (mexec_halt_star segs _ _ _ Hm c' rfl).1⟩

/-- The judgment does not exit with any other code. -/
theorem to_wallexit_no_other_exit (segs : List Segment) (fd ch : word) (Hfd32 : fd32 fd = fd) :
    ∀ bufs code ms model, m_halted model = none → m_vm_lazy model = [] → fdchan fd ch model →
      bufs_modeled bufs → to_wallexit segs fd bufs code ms →
      ∀ code', code' ≠ code → ¬ OmniRun.exec segs (mkCfg ms model) (exits_with code') := by
  intro bufs code ms model Hh Hlazy Hfdc Hbm Hw code' Hne Hex
  obtain ⟨tr, o, Hm, _, Hx⟩ := exec_realizes segs _ _ (to_wallexit_exec segs fd ch Hfd32 bufs code ms model Hh Hlazy Hfdc Hbm Hw)
  have Hx' := exec_sound segs _ _ Hex _ _ Hm
  cases o with
  | OError _ => exact Hx.elim
  | OHalt c' =>
    have e := Hx'.1.symm.trans Hx.1
    cases e
    exact Hne rfl

/-- Its trace is no other list. -/
theorem to_wallexit_trace_unique (segs : List Segment) (fd ch : word) (Hfd32 : fd32 fd = fd) :
    ∀ bufs code ms model, m_halted model = none → m_vm_lazy model = [] → fdchan fd ch model →
      bufs_modeled bufs → to_wallexit segs fd bufs code ms →
      ∀ tr', tr' ≠ wevents_ch ch bufs ++ [.ExitEv code (m_fs model)] →
      ¬ OmniRun.exec segs (mkCfg ms model) (fun tr _ => tr = tr') := by
  intro bufs code ms model Hh Hlazy Hfdc Hbm Hw tr' Hne Hex
  obtain ⟨tr, o, Hm, Heq, _⟩ := exec_realizes segs _ _ (to_wallexit_exec segs fd ch Hfd32 bufs code ms model Hh Hlazy Hfdc Hbm Hw)
  have Heq' := exec_sound segs _ _ Hex _ _ Hm
  exact Hne (Heq'.symm.trans Heq)

/-- It does not stay silent. -/
theorem to_wallexit_not_silent (segs : List Segment) (fd ch : word) (Hfd32 : fd32 fd = fd) :
    ∀ bufs code ms model, m_halted model = none → m_vm_lazy model = [] → fdchan fd ch model →
      bufs_modeled bufs → to_wallexit segs fd bufs code ms →
      ¬ cosafe segs (mkCfg ms model) (fun tr => tr = []) := by
  intro bufs code ms model Hh Hlazy Hfdc Hbm Hw Hc
  obtain ⟨c', Hstar⟩ := to_wallexit_star_admits segs fd ch Hfd32 bufs code ms model Hh Hlazy Hfdc Hbm Hw
  have Hnil := cosafe_star segs _ _ _ _ Hc Hstar
  simp at Hnil

theorem to_wallexit_star_only (segs : List Segment) (fd ch : word) (Hfd32 : fd32 fd = fd) :
    ∀ bufs code ms model, m_halted model = none → m_vm_lazy model = [] → fdchan fd ch model →
      bufs_modeled bufs → to_wallexit segs fd bufs code ms →
      ∀ tr c, star segs (mkCfg ms model) tr c → is_prefix tr (wevents_ch ch bufs ++ [.ExitEv code (m_fs model)]) := by
  intro bufs code ms model Hh Hlazy Hfdc Hbm Hw tr c Hstar
  obtain ⟨tr', o, _, Heq, _⟩ := exec_realizes segs _ _
    (exec_star segs _ _ _ _ (to_wallexit_exec segs fd ch Hfd32 bufs code ms model Hh Hlazy Hfdc Hbm Hw) Hstar)
  rw [← Heq]
  exact is_prefix_app _ _

theorem to_wallexit_no_error (segs : List Segment) (fd ch : word) (Hfd32 : fd32 fd = fd) :
    ∀ ms model bufs code, m_halted model = none → m_vm_lazy model = [] → fdchan fd ch model →
      bufs_modeled bufs → to_wallexit segs fd bufs code ms → ¬ reaches_error segs (mkCfg ms model) := by
  intro ms model bufs code Hh Hlazy Hfdc Hbm Hw
  exact exec_no_error segs _ (exec_conseq segs _ _ _
    (to_wallexit_exec segs fd ch Hfd32 bufs code ms model Hh Hlazy Hfdc Hbm Hw)
    (fun tr o h => exits_with_never_errors _ _ _ h.2))

/-! ### fd 1, and the run-level packaging -/

/-- `to_wallexit` at fd 1, in `CatSim.to_wexit`'s argument order. -/
abbrev wexit1 (segs : List Segment) (ms : machine_state) (bufs : List (List byte)) (code : word) : Prop :=
  to_wallexit segs (Z_to_bv 64 1) bufs code ms

/-- The generic-channel event list at fd 1 is `CatSim.wevents`. -/
theorem wevents_ch_fd1 : ∀ bufs, wevents_ch (Z_to_bv 64 1) bufs = wevents bufs := by
  intro bufs
  induction bufs with
  | nil => rfl
  | cons b bs ih => simp only [wevents_ch, wevents, ih]

/-- The run-level omni judgment of a retry-loop run. -/
theorem wall_omni_run : ∀ fd ch, fd32 fd = fd →
    ∀ segs pc ph sp brk0 mb rnd lim inp bufs code,
      fdchan fd ch (init_model (segments_reserved segs) brk0 mb sp lim inp) → bufs_modeled bufs →
      to_wallexit segs fd bufs code
        (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) →
      omni_run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp
        (fun tr o => tr = wevents_ch ch bufs ++ [.ExitEv code (in_fs inp)] ∧ exits_with code tr o) := by
  intro fd ch Hfd32 segs pc ph sp brk0 mb rnd lim inp bufs code Hfdc Hbm Hw
  exact to_wallexit_exec segs fd ch Hfd32 bufs code _ (init_model (segments_reserved segs) brk0 mb sp lim inp)
    rfl rfl Hfdc Hbm Hw

theorem wall_obs_iff : ∀ fd ch, fd32 fd = fd →
    ∀ segs pc ph sp brk0 mb rnd lim inp bufs code,
      fdchan fd ch (init_model (segments_reserved segs) brk0 mb sp lim inp) → bufs_modeled bufs →
      to_wallexit segs fd bufs code
        (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) →
      ∀ tr, obs_trace segs (init_config segs pc ph sp brk0 mb rnd lim inp) tr ↔
        is_prefix tr (wevents_ch ch bufs ++ [.ExitEv code (in_fs inp)]) := by
  intro fd ch Hfd32 segs pc ph sp brk0 mb rnd lim inp bufs code Hfdc Hbm Hw tr
  apply exec_obs_iff
  exact exec_conseq segs _ _ _ (wall_omni_run fd ch Hfd32 segs pc ph sp brk0 mb rnd lim inp bufs code Hfdc Hbm Hw)
    (fun tr' o h => ⟨h.1, exits_with_never_errors _ _ _ h.2⟩)

theorem wall_no_error_run : ∀ fd ch, fd32 fd = fd →
    ∀ segs pc ph sp brk0 mb rnd lim inp bufs code,
      fdchan fd ch (init_model (segments_reserved segs) brk0 mb sp lim inp) → bufs_modeled bufs →
      to_wallexit segs fd bufs code
        (init_machine_state segs pc ph sp rnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) →
      ¬ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp) := by
  intro fd ch Hfd32 segs pc ph sp brk0 mb rnd lim inp bufs code Hfdc Hbm Hw
  exact exec_no_error segs _ (exec_conseq segs _ _ _
    (wall_omni_run fd ch Hfd32 segs pc ph sp brk0 mb rnd lim inp bufs code Hfdc Hbm Hw)
    (fun _ _ h => exits_with_never_errors _ _ _ h.2))

/-- The omni equivalence for two retry-loop exit-after-writes binaries emitting the same buffers and
    exit code, at the two role budgets. -/
theorem wall_omni_strong_equiv :
    ∀ source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd bufs code inp,
      to_wallexit source_segs (Z_to_bv 64 1) bufs code
          (init_machine_state source_segs rpc rph rsp rrnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) →
        to_wallexit target_segs (Z_to_bv 64 1) bufs code
            (init_machine_state target_segs apc aph asp arnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) →
          bufs_modeled bufs →
            omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
              (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp := by
  intro source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd bufs code inp Hsource Htarget Hbm
  have HfdS : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1)
      (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp) := ⟨rfl, rfl⟩
  have HfdT : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1)
      (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp) := ⟨rfl, rfl⟩
  refine ⟨?_, .inr ⟨?_, ?_⟩⟩
  · exact coexec_conseq source_segs _ _ _
      (exec_coexec source_segs _ _
        (wall_omni_run _ _ fd32_1 source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp bufs code HfdS Hbm
          Hsource))
      (fun tr o h => never_errors_covered source_segs _ _ (exits_with_never_errors _ _ _ h.2))
  · apply (trace_equiv_iff_omni _ _ _ _ _ _ _).1
    intro tr
    exact (wall_obs_iff _ _ fd32_1 source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp bufs code HfdS Hbm
        Hsource tr).trans
      (wall_obs_iff _ _ fd32_1 target_segs apc aph asp abrk amb arnd target_alloc_limit inp bufs code HfdT Hbm
        Htarget tr).symm
  · apply (bh_errors_iff _ _ _ _).1
    exact wall_no_error_run _ _ fd32_1 target_segs apc aph asp abrk amb arnd target_alloc_limit inp bufs code HfdT
      Hbm Htarget

/-- The `Equivalence`-level equivalence for two retry-loop exit-after-writes binaries emitting the same
    buffers and exit code. -/
theorem wall_strong_equiv :
    ∀ source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim bufs code inp,
      to_wallexit source_segs (Z_to_bv 64 1) bufs code
          (init_machine_state source_segs rpc rph rsp rrnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) →
        to_wallexit target_segs (Z_to_bv 64 1) bufs code
            (init_machine_state target_segs apc aph asp arnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap) →
          bufs_modeled bufs →
            modeled (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp) ∧
              equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
                (run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp) := by
  intro source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim bufs code inp
    Hsource Htarget Hbm
  have HfdS : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1)
      (init_model (segments_reserved source_segs) rbrk rmb rsp rlim inp) := ⟨rfl, rfl⟩
  have HfdT : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1)
      (init_model (segments_reserved target_segs) abrk amb asp alim inp) := ⟨rfl, rfl⟩
  refine ⟨no_error_run_modeled _ _ _ _ _ _ _ _ _
    (wall_no_error_run _ _ fd32_1 source_segs rpc rph rsp rbrk rmb rrnd rlim inp bufs code HfdS Hbm Hsource),
    .inr ⟨?_, ?_⟩⟩
  · intro tr
    exact (wall_obs_iff _ _ fd32_1 source_segs rpc rph rsp rbrk rmb rrnd rlim inp bufs code HfdS Hbm Hsource tr).trans
      (wall_obs_iff _ _ fd32_1 target_segs apc aph asp abrk amb arnd alim inp bufs code HfdT Hbm Htarget tr).symm
  · exact wall_no_error_run _ _ fd32_1 target_segs apc aph asp abrk amb arnd alim inp bufs code HfdT Hbm Htarget

end LPS
