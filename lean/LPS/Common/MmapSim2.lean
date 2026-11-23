import LPS.Common.MmapSim1

/-!
# LPS `theories/Common/MmapSim.v` (f1006fe8), part 2: `twm`, the writes/munmap/exit line, and its omni reading

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Common/MmapSim.v` at f1006fe8 (image-INDEPENDENT proof library), `Section WithSegs` up to
`twm_star_only`: the mutual judgment `twm`/`twm_pend`/`twm_tail` (ExitSim's `to_wexit` extended with a
`munmap` rule of the modeled shape and threading the model; a write node is WallSim's put-style retry
loop inlined, its trace contribution the full buffer), its combined minimality scheme `twm_mutind`, the
`msteps` glue, the raw-ecall constructors (`twm_write_ret`, `twm_tail_write_rec`, `twm_munmap_rec`,
`twm_exit_coden`), the one-step inversion `sstep_munmap_inv`, and the omni reading `twm_exec_mut`/
`twm_exec` with `twm_star_admits`/`twm_star_only`. Part 1 is MmapSim1, part 3 (MmapSim3) has `tmw`.

Conventions as MmapSim1 and WallSim1: Section `WithSegs`' variable `segs` is the leading explicit
argument of the judgments and of the section's lemmas; `Context {fx : FPState}` is an instance argument
of the raw-ecall constructors. Rocq's `Scheme twm_min/twm_pend_min/twm_tail_min` + `Combined Scheme
twm_mutind` are one Lean theorem `twm_mutind` (the combined statement, proved by the mutual recursors);
the three separate minimality schemes are its projections and are not stated on their own. The
constructors are `twm.twm_exit` etc. The proofs are Lean's; the write transition is CatSim2's
`tw_write_sstep` and the exit transition its `tw_exit_sstep` (Lean-only helpers of the CatSim port).
Lean-only helper here: the private `exec_instr_step` (one silent instruction step of the omni judgment).
-/

namespace LPS
open RiscvSemantics OmniRun

/-! ### twm: writes/munmap/exit straight line, model threaded -/

mutual
inductive twm (segs : List Segment) : machine_state → Model → List (List byte) → word → Prop where
  | twm_exit (ms model x8) :
      ms.ms_svc_pending = some x8 → is_exit_no x8 →
      twm segs ms model [] (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
  | twm_write (ms model buf bufs code) :
      1 ≤ buf.length → twm_pend segs ms model buf bufs code → twm segs ms model (buf :: bufs) code
  | twm_munmap (ms model x8 bufs code) :
      ms.ms_svc_pending = some x8 → bv_unsigned x8 = 215 → munmap_args_ok ms model →
      twm segs (advance_past_svc (apply_effect ms (munmap_eff ms)))
        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) bufs code →
      twm segs ms model bufs code
  | twm_step (ms ms' model bufs code) :
      ms.ms_svc_pending = none → RiscvSemantics.step segs ms = .MachineOk ms' →
      twm segs ms' model bufs code → twm segs ms model bufs code
/-- The put-style retry loop realizing one buffer: a write-pending state offering the remainder `rest`;
    the environment delivers any nonempty prefix, the loop reissues on the rest. -/
inductive twm_pend (segs : List Segment) : machine_state → Model → List byte → List (List byte) → word → Prop where
  | twmp_write (ms model x8 rest bufs code) :
      ms.ms_svc_pending = some x8 → bv_unsigned x8 = 64 → ms_gpr ms 0 = Z_to_bv 64 1 →
      ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some rest → 1 ≤ rest.length →
      (∀ n, 1 ≤ n → n ≤ rest.length →
        twm_tail segs (advance_past_svc (set_gpr0 ms (len_word (rest.take n)))) model (rest.drop n) bufs code) →
      twm_pend segs ms model rest bufs code
inductive twm_tail (segs : List Segment) : machine_state → Model → List byte → List (List byte) → word → Prop where
  | twmt_done (ms model bufs code) : twm segs ms model bufs code → twm_tail segs ms model [] bufs code
  | twmt_more (ms model rest bufs code) :
      1 ≤ rest.length → twm_pend segs ms model rest bufs code → twm_tail segs ms model rest bufs code
  | twmt_step (ms ms' model rest bufs code) :
      ms.ms_svc_pending = none → RiscvSemantics.step segs ms = .MachineOk ms' →
      twm_tail segs ms' model rest bufs code → twm_tail segs ms model rest bufs code
end

/-- Rocq's `Combined Scheme twm_mutind` (of the three minimality schemes). -/
theorem twm_mutind (segs : List Segment)
    (P : machine_state → Model → List (List byte) → word → Prop)
    (P0 P1 : machine_state → Model → List byte → List (List byte) → word → Prop)
    (f_exit : ∀ ms model x8, ms.ms_svc_pending = some x8 → is_exit_no x8 →
      P ms model [] (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)))
    (f_write : ∀ ms model buf bufs code, 1 ≤ buf.length → twm_pend segs ms model buf bufs code →
      P0 ms model buf bufs code → P ms model (buf :: bufs) code)
    (f_munmap : ∀ ms model x8 bufs code, ms.ms_svc_pending = some x8 → bv_unsigned x8 = 215 →
      munmap_args_ok ms model →
      twm segs (advance_past_svc (apply_effect ms (munmap_eff ms)))
        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) bufs code →
      P (advance_past_svc (apply_effect ms (munmap_eff ms)))
        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) bufs code →
      P ms model bufs code)
    (f_step : ∀ ms ms' model bufs code, ms.ms_svc_pending = none → RiscvSemantics.step segs ms = .MachineOk ms' →
      twm segs ms' model bufs code → P ms' model bufs code → P ms model bufs code)
    (f_pwrite : ∀ ms model x8 rest bufs code, ms.ms_svc_pending = some x8 → bv_unsigned x8 = 64 →
      ms_gpr ms 0 = Z_to_bv 64 1 → ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some rest → 1 ≤ rest.length →
      (∀ n, 1 ≤ n → n ≤ rest.length →
        twm_tail segs (advance_past_svc (set_gpr0 ms (len_word (rest.take n)))) model (rest.drop n) bufs code) →
      (∀ n, 1 ≤ n → n ≤ rest.length →
        P1 (advance_past_svc (set_gpr0 ms (len_word (rest.take n)))) model (rest.drop n) bufs code) →
      P0 ms model rest bufs code)
    (f_done : ∀ ms model bufs code, twm segs ms model bufs code → P ms model bufs code → P1 ms model [] bufs code)
    (f_more : ∀ ms model rest bufs code, 1 ≤ rest.length → twm_pend segs ms model rest bufs code →
      P0 ms model rest bufs code → P1 ms model rest bufs code)
    (f_tstep : ∀ ms ms' model rest bufs code, ms.ms_svc_pending = none →
      RiscvSemantics.step segs ms = .MachineOk ms' → twm_tail segs ms' model rest bufs code →
      P1 ms' model rest bufs code → P1 ms model rest bufs code) :
    (∀ ms model bufs code, twm segs ms model bufs code → P ms model bufs code) ∧
    (∀ ms model rest bufs code, twm_pend segs ms model rest bufs code → P0 ms model rest bufs code) ∧
    (∀ ms model rest bufs code, twm_tail segs ms model rest bufs code → P1 ms model rest bufs code) :=
  ⟨fun _ _ _ _ h => twm.rec (motive_1 := fun ms model bufs code _ => P ms model bufs code)
      (motive_2 := fun ms model rest bufs code _ => P0 ms model rest bufs code)
      (motive_3 := fun ms model rest bufs code _ => P1 ms model rest bufs code)
      f_exit f_write f_munmap f_step f_pwrite f_done f_more f_tstep h,
   fun _ _ _ _ _ h => twm_pend.rec (motive_1 := fun ms model bufs code _ => P ms model bufs code)
      (motive_2 := fun ms model rest bufs code _ => P0 ms model rest bufs code)
      (motive_3 := fun ms model rest bufs code _ => P1 ms model rest bufs code)
      f_exit f_write f_munmap f_step f_pwrite f_done f_more f_tstep h,
   fun _ _ _ _ _ h => twm_tail.rec (motive_1 := fun ms model bufs code _ => P ms model bufs code)
      (motive_2 := fun ms model rest bufs code _ => P0 ms model rest bufs code)
      (motive_3 := fun ms model rest bufs code _ => P1 ms model rest bufs code)
      f_exit f_write f_munmap f_step f_pwrite f_done f_more f_tstep h⟩

theorem msteps_twm (segs : List Segment) : ∀ ms ms' model bufs code,
    msteps segs ms ms' → twm segs ms' model bufs code → twm segs ms model bufs code := by
  intro ms ms' model bufs code H
  induction H with
  | mst_refl => exact id
  | mst_step ms ms1 ms2 hsvc hstep _ ih => exact fun hw => .twm_step _ _ _ _ _ hsvc hstep (ih hw)

theorem msteps_twm_tail (segs : List Segment) : ∀ ms ms' model rest bufs code,
    msteps segs ms ms' → twm_tail segs ms' model rest bufs code → twm_tail segs ms model rest bufs code := by
  intro ms ms' model rest bufs code H
  induction H with
  | mst_refl => exact id
  | mst_step ms ms1 ms2 hsvc hstep _ ih => exact fun hw => .twmt_step _ _ _ _ _ _ hsvc hstep (ih hw)

/-! ### Ergonomic raw-ecall-record constructors -/

/-- A write at the raw ecall post-state; the continuation is the caller's put-loop obligation. -/
theorem twm_write_ret [FPState] (segs : List Segment) : ∀ regs pc mem rom model buf bufs code,
    bv_unsigned (getr regs 17) = 64 → reg_get regs 10 = Z_to_bv 64 1 →
    ms_read_bytes { ms_regs := regs, ms_fregs := fp_regs, ms_pc_val := pc, ms_svc_pending := some (getr regs 17),
                    ms_resv := none, ms_fcsr := fp_csr, ms_mem := mem, ms_rom := rom }
      (reg_get regs 11) (reg_get regs 12) = some buf →
    1 ≤ buf.length →
    (∀ n, 1 ≤ n → n ≤ buf.length →
      twm_tail segs (mkst (regupd regs 10 (len_word (buf.take n))) (v_addi pc 4) mem rom) model (buf.drop n) bufs code) →
    twm segs { ms_regs := regs, ms_fregs := fp_regs, ms_pc_val := pc, ms_svc_pending := some (getr regs 17),
               ms_resv := none, ms_fcsr := fp_csr, ms_mem := mem, ms_rom := rom } model (buf :: bufs) code := by
  intro regs pc mem rom model buf bufs code H17 H10 Hr Hnb Hcont
  refine .twm_write _ _ _ _ _ Hnb (.twmp_write _ _ (getr regs 17) _ _ _ rfl H17 ?_ ?_ Hnb ?_)
  · simp only [ms_gpr, arg_reg_0]; exact H10
  · simp only [ms_gpr, arg_reg_1, arg_reg_2]; exact Hr
  · intro n hn1 hn2
    rw [adv_set]
    exact Hcont n hn1 hn2

/-- The reissued write at the raw ecall post-state, INSIDE a retry loop. -/
theorem twm_tail_write_rec [FPState] (segs : List Segment) : ∀ regs pc mem rom model rest bufs code,
    bv_unsigned (getr regs 17) = 64 → reg_get regs 10 = Z_to_bv 64 1 →
    ms_read_bytes { ms_regs := regs, ms_fregs := fp_regs, ms_pc_val := pc, ms_svc_pending := some (getr regs 17),
                    ms_resv := none, ms_fcsr := fp_csr, ms_mem := mem, ms_rom := rom }
      (reg_get regs 11) (reg_get regs 12) = some rest →
    1 ≤ rest.length →
    (∀ n, 1 ≤ n → n ≤ rest.length →
      twm_tail segs (mkst (regupd regs 10 (len_word (rest.take n))) (v_addi pc 4) mem rom) model (rest.drop n) bufs code) →
    twm_tail segs { ms_regs := regs, ms_fregs := fp_regs, ms_pc_val := pc, ms_svc_pending := some (getr regs 17),
                    ms_resv := none, ms_fcsr := fp_csr, ms_mem := mem, ms_rom := rom } model rest bufs code := by
  intro regs pc mem rom model rest bufs code H17 H10 Hr Hnb Hcont
  refine .twmt_more _ _ _ _ _ Hnb (.twmp_write _ _ (getr regs 17) _ _ _ rfl H17 ?_ ?_ Hnb ?_)
  · simp only [ms_gpr, arg_reg_0]; exact H10
  · simp only [ms_gpr, arg_reg_1, arg_reg_2]; exact Hr
  · intro n hn1 hn2
    rw [adv_set]
    exact Hcont n hn1 hn2

/-- A munmap at the raw ecall post-state: a0 := 0, mapping dropped, the range now unmapped. -/
theorem twm_munmap_rec [FPState] (segs : List Segment) : ∀ regs pc mem rom model bufs code (a nlen : word),
    bv_unsigned (getr regs 17) = 215 → reg_get regs 10 = a → reg_get regs 11 = nlen →
    Z.modulo (bv_unsigned a) page_size = 0 → nlen ≠ Z_to_bv 64 0 →
    bv_unsigned a + page_round_up_Z (bv_unsigned nlen) ≤ TASK_SIZE →
    map_has (m_vmmaps model).vm_maps a (page_round_up nlen) = true →
    twm segs (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) (unfill a (page_round_up nlen) mem) rom)
      (munmap_model a (page_round_up nlen) model) bufs code →
    twm segs { ms_regs := regs, ms_fregs := fp_regs, ms_pc_val := pc, ms_svc_pending := some (getr regs 17),
               ms_resv := none, ms_fcsr := fp_csr, ms_mem := mem, ms_rom := rom } model bufs code := by
  intro regs pc mem rom model bufs code a nlen H17 Ha Hn Hal Hlen Hnw Hhas Hcont
  refine .twm_munmap _ _ (getr regs 17) _ _ rfl H17 ?_ ?_
  · simp only [munmap_args_ok, ms_gpr, arg_reg_0, arg_reg_1]; rw [Ha, Hn]; exact ⟨Hal, Hlen, Hnw, Hhas⟩
  · simp only [munmap_eff, ms_gpr, arg_reg_0, arg_reg_1]; rw [Ha, Hn, adv_munmap]; exact Hcont

/-- Exit with an arbitrary small code at the raw ecall post-state. -/
theorem twm_exit_coden [FPState] (segs : List Segment) : ∀ regs pc mem rom model (c : word),
    bv_unsigned (getr regs 17) = 93 → reg_get regs 10 = c → bv_unsigned c < 256 →
    twm segs { ms_regs := regs, ms_fregs := fp_regs, ms_pc_val := pc, ms_svc_pending := some (getr regs 17),
               ms_resv := none, ms_fcsr := fp_csr, ms_mem := mem, ms_rom := rom } model [] c := by
  intro regs pc mem rom model c H17 H10 Hc
  have Hg : bv_and (reg_get regs 10) (Z_to_bv 64 255) = c := by rw [H10]; exact land_255_small c Hc
  rw [← Hg]
  exact .twm_exit _ _ (getr regs 17) rfl (.inl H17)

/-! ### One-step inversion for a munmap configuration -/

theorem sstep_munmap_inv (segs : List Segment) : ∀ ms model x8 evs st,
    m_halted model = none → m_vm_lazy model = [] → ms.ms_svc_pending = some x8 → bv_unsigned x8 = 215 →
    munmap_args_ok ms model → sstep segs (mkCfg ms model) evs st →
    evs = [] ∧ st = .SNext (mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                    (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)) := by
  intro ms model x8 evs st Hh Hlazy Hsvc Hno Hargs Hss
  have Hx : ∀ y, ms.ms_svc_pending = some y → y = x8 := by
    intro y h; rw [Hsvc] at h; exact (Option.some.inj h).symm
  cases Hss with
  | sstep_instr _ _ _ _ _ h _ => rw [Hsvc] at h; cases h
  | sstep_instr_fault _ _ _ h _ => rw [Hsvc] at h; cases h
  | sstep_instr_unmodeled _ _ _ h _ => rw [Hsvc] at h; cases h
  | sstep_syscall _ _ y eff model' model'' _ _ hsvc hspec _ hmat =>
    rw [Hx y hsvc] at hspec
    obtain ⟨rfl, rfl, rfl⟩ := munmap_ok_inv segs ms x8 model _ _ _ Hno Hargs hspec
    rw [materialize_model_accesses_no_lazy _ _ (munmap_model_no_lazy _ _ _ Hlazy)] at hmat
    cases hmat
    exact ⟨rfl, rfl⟩
  | sstep_syscall_materialization_fault _ _ y _ _ _ _ hsvc hspec _ hmat =>
    rw [Hx y hsvc] at hspec
    obtain ⟨rfl, rfl, rfl⟩ := munmap_ok_inv segs ms x8 model _ _ _ Hno Hargs hspec
    rw [materialize_model_accesses_no_lazy _ _ (munmap_model_no_lazy _ _ _ Hlazy)] at hmat
    cases hmat
  | sstep_exit _ _ y _ _ _ _ _ hsvc hspec hhalt _ =>
    rw [Hx y hsvc] at hspec
    obtain ⟨_, rfl, _⟩ := munmap_ok_inv segs ms x8 model _ _ _ Hno Hargs hspec
    rw [munmap_model_halted, Hh] at hhalt; cases hhalt
  | sstep_killed _ _ y _ _ _ _ _ hsvc hspec hkill =>
    rw [Hx y hsvc] at hspec
    obtain ⟨_, rfl, _⟩ := munmap_ok_inv segs ms x8 model _ _ _ Hno Hargs hspec
    rw [m_killed_of_m_halted_none _ ((munmap_model_halted _ _ _).trans Hh)] at hkill; cases hkill
  | sstep_syscall_unmodeled _ _ y _ hsvc hspec =>
    rw [Hx y hsvc] at hspec
    exact absurd hspec (munmap_no_unmodeled segs ms x8 model Hno Hargs)

/-! ### The omni reading of `twm` -/

def twm_post (bufs : List (List byte)) (code : word) (fs : Fs) : post :=
  fun tr o => tr = wevents bufs ++ [.ExitEv code fs] ∧ exits_with code tr o

def twm_rest_post (rest : List byte) (bufs : List (List byte)) (code : word) (fs : Fs) : post :=
  fun tr o => tr = rest.map (event.WriteEv (Z_to_bv 64 1)) ++ wevents bufs ++ [.ExitEv code fs] ∧ exits_with code tr o

/-- One silent instruction step of the omni judgment (Lean-only helper). -/
private theorem exec_instr_step (segs : List Segment) (ms ms' : machine_state) (model : Model) (Q : post)
    (Hh : m_halted model = none) (Hlazy : m_vm_lazy model = []) (Hsvc : ms.ms_svc_pending = none)
    (Hstep : RiscvSemantics.step segs ms = .MachineOk ms') (H : OmniRun.exec segs (mkCfg ms' model) Q) :
    OmniRun.exec segs (mkCfg ms model) Q := by
  refine exec_step_only segs _ _ [] (mkCfg ms' model) ?_
    (fun evs st Hss => sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss) ?_
  · refine .sstep_instr ms model ms' model Hh Hsvc ?_
    rw [mi_account_step_no_lazy segs ms model Hlazy, Hstep]
  · exact exec_conseq segs _ _ _ H (fun tr o h => by simpa using h)

theorem twm_exec_mut (segs : List Segment) :
    (∀ ms model bufs code, twm segs ms model bufs code → bufs_modeled bufs →
      m_halted model = none → m_vm_lazy model = [] → fd1chan model →
      OmniRun.exec segs (mkCfg ms model) (twm_post bufs code (m_fs model))) ∧
    (∀ ms model rest bufs code, twm_pend segs ms model rest bufs code → buf_modeled rest → bufs_modeled bufs →
      m_halted model = none → m_vm_lazy model = [] → fd1chan model →
      OmniRun.exec segs (mkCfg ms model) (twm_rest_post rest bufs code (m_fs model))) ∧
    (∀ ms model rest bufs code, twm_tail segs ms model rest bufs code → buf_modeled rest → bufs_modeled bufs →
      m_halted model = none → m_vm_lazy model = [] → fd1chan model →
      OmniRun.exec segs (mkCfg ms model) (twm_rest_post rest bufs code (m_fs model))) := by
  apply twm_mutind segs
  · -- twm_exit
    intro ms model x8 Hsvc Hx8 _ Hh _ _
    refine exec_step_only segs _ _ _ _ (tw_exit_sstep segs ms model x8 Hh Hsvc Hx8)
      (fun evs st Hss => sstep_exit_inv segs ms model x8 evs st Hh Hsvc Hx8 Hss) ?_
    refine .exec_halt _ _ (by show m_halted (with_halted _ model) ≠ none; simp [m_halted_with_halted]) ?_
    exact ⟨by simp [wevents], m_halted_with_halted _ _, m_killed_with_halted _ _⟩
  · -- twm_write: the wall node contributes the full buffer
    intro ms model buf bufs code _ _ IH Hbm Hh Hlazy Hfd
    refine exec_conseq segs _ _ _ (IH (Hbm buf (List.mem_cons_self ..))
      (fun b hb => Hbm b (List.mem_cons_of_mem _ hb)) Hh Hlazy Hfd) ?_
    rintro tr o ⟨Heq, Hx⟩
    exact ⟨by rw [Heq]; simp [wevents, List.append_assoc], Hx⟩
  · -- twm_munmap
    intro ms model x8 bufs code Hsvc Hno Hargs _ IH Hbm Hh Hlazy Hfd
    have Hh' := (munmap_model_halted (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model).trans Hh
    have Hlazy' := munmap_model_no_lazy (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model Hlazy
    refine exec_step_only segs _ _ [] _
      (.sstep_syscall ms model x8 _ _ _ [] Hh Hsvc (munmap_ok segs ms x8 model Hno Hargs) Hh'
        (materialize_model_accesses_no_lazy _ _ Hlazy'))
      (fun evs st Hss => sstep_munmap_inv segs ms model x8 evs st Hh Hlazy Hsvc Hno Hargs Hss) ?_
    exact exec_conseq segs _ _ _ (IH Hbm Hh' Hlazy' (munmap_model_fd1chan _ _ _ Hfd))
      (fun tr o h => by simpa [munmap_model_fs] using h)
  · -- twm_step
    intro ms ms' model bufs code Hsvc Hstep _ IH Hbm Hh Hlazy Hfd
    exact exec_instr_step segs ms ms' model _ Hh Hlazy Hsvc Hstep (IH Hbm Hh Hlazy Hfd)
  · -- twmp_write: every delivered length is a successor
    intro ms model x8 rest bufs code Hsvc Hno Hg Hr Hnb _ IH Hbr Hbm Hh Hlazy Hfd
    refine .exec_step _ _ Hh ⟨_, _, tw_write_sstep segs ms model x8 rest rest.length Hh Hlazy Hfd Hsvc Hno Hg Hr Hbr
      Hnb (Nat.le_refl _)⟩ ?_ ?_
    · intro evs Hss
      obtain ⟨n, _, _, _, Habs⟩ := sstep_write_inv segs ms model x8 rest evs .SError Hh Hlazy Hfd Hsvc Hno Hg Hr Hbr Hnb Hss
      cases Habs
    · intro evs c' Hss
      obtain ⟨n, Hn1, Hn2, rfl, Hc'⟩ :=
        sstep_write_inv segs ms model x8 rest evs (.SNext c') Hh Hlazy Hfd Hsvc Hno Hg Hr Hbr Hnb Hss
      cases Hc'
      refine exec_conseq segs _ _ _ (IH n Hn1 Hn2 (buf_modeled_skipn n rest Hbr) Hbm Hh Hlazy Hfd) ?_
      rintro tr o ⟨Heq, Hx⟩
      refine ⟨?_, Hx⟩
      rw [Heq]
      simp only [← List.append_assoc, ← List.map_append, List.take_append_drop]
  · -- twmt_done
    intro ms model bufs code _ IH _ Hbm Hh Hlazy Hfd
    exact exec_conseq segs _ _ _ (IH Hbm Hh Hlazy Hfd) (fun tr o ⟨Heq, Hx⟩ => ⟨by simpa using Heq, Hx⟩)
  · -- twmt_more
    intro ms model rest bufs code _ _ IH Hbr Hbm Hh Hlazy Hfd
    exact IH Hbr Hbm Hh Hlazy Hfd
  · -- twmt_step
    intro ms ms' model rest bufs code Hsvc Hstep _ IH Hbr Hbm Hh Hlazy Hfd
    exact exec_instr_step segs ms ms' model _ Hh Hlazy Hsvc Hstep (IH Hbr Hbm Hh Hlazy Hfd)

theorem twm_exec (segs : List Segment) : ∀ ms model bufs code, twm segs ms model bufs code → bufs_modeled bufs →
    m_halted model = none → m_vm_lazy model = [] → fd1chan model →
    OmniRun.exec segs (mkCfg ms model) (twm_post bufs code (m_fs model)) :=
  (twm_exec_mut segs).1

theorem twm_star_admits (segs : List Segment) : ∀ ms model bufs code, twm segs ms model bufs code →
    bufs_modeled bufs → m_halted model = none → m_vm_lazy model = [] → fd1chan model →
    ∃ c, star segs (mkCfg ms model) (wevents bufs ++ [.ExitEv code (m_fs model)]) c := by
  intro ms model bufs code Hte Hbm Hh Hlazy Hfd
  obtain ⟨tr, o, Hm, Heq, Hx⟩ := exec_realizes segs _ _ (twm_exec segs ms model bufs code Hte Hbm Hh Hlazy Hfd)
  cases o with
  | OHalt c' =>
    subst Heq
    exact ⟨c', (mexec_halt_star segs _ _ _ Hm c' rfl).1⟩
  | OError c' => exact Hx.elim

theorem twm_star_only (segs : List Segment) : ∀ ms model bufs code, twm segs ms model bufs code →
    bufs_modeled bufs → m_halted model = none → m_vm_lazy model = [] → fd1chan model →
    ∀ tr c, star segs (mkCfg ms model) tr c → is_prefix tr (wevents bufs ++ [.ExitEv code (m_fs model)]) := by
  intro ms model bufs code Hte Hbm Hh Hlazy Hfd tr c Hstar
  obtain ⟨tr', o, _, Heq, _⟩ :=
    exec_realizes segs _ _ (exec_star segs _ _ _ _ (twm_exec segs ms model bufs code Hte Hbm Hh Hlazy Hfd) Hstar)
  rw [← Heq]
  exact is_prefix_app _ _

end LPS
