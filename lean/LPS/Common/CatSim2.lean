import LPS.Common.CatSim1

/-!
# LPS `theories/Common/CatSim.v` (f1006fe8), part 2: `to_wexit`, the configuration level

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Common/CatSim.v` at f1006fe8 (shared proof library, not the trusted specification
there), its `Section WithSegs` (CatSim.v:396-784): the ret-oblivious write-then-exit relation
`to_wexit`, the instruction runs `msteps`, the one-step inversions of a write configuration, the omni
judgment `to_wexit_exec` and its corollaries `to_wexit_star_admits`, `to_wexit_star_only`,
`to_wexit_no_error`. Conventions as CatSim1.

Section `WithSegs`' variable `segs` is the leading explicit argument. The channel-parametric
inversion `sstep_write_ch_inv` (CatSim.v:1163, Section `WithSegsCh`, whose variables `segs fd ch` and
hypothesis `Hfd32` are its leading explicit arguments) is here, before the fd-1 ones, which are proved
as its instances; `sstep_write_ch_next_inv` (its `SNext` half, the analogue of CatSim.v's
`sstep_write_next_inv`) is a Lean-only helper.
-/

namespace LPS
open RiscvSemantics OmniRun

/-! ### `to_wexit`: the machine-deterministic straight line of writes then exit -/

inductive to_wexit (segs : List Segment) : machine_state → List (List byte) → word → Prop where
  | tw_exit (ms x8) :
      ms.ms_svc_pending = some x8 → is_exit_no x8 → to_wexit segs ms [] (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
  | tw_write (ms x8 buf bufs code) :
      ms.ms_svc_pending = some x8 → bv_unsigned x8 = 64 → ms_gpr ms 0 = Z_to_bv 64 1 →
      ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf → 1 ≤ buf.length →
      (∀ n, 1 ≤ n → n ≤ buf.length →
        to_wexit segs (advance_past_svc (set_gpr0 ms (len_word (buf.take n)))) bufs code) →
      to_wexit segs ms (buf :: bufs) code
  | tw_step (ms ms' bufs code) :
      ms.ms_svc_pending = none → RiscvSemantics.step segs ms = .MachineOk ms' → to_wexit segs ms' bufs code →
      to_wexit segs ms bufs code

/-! ### `msteps`: a run of ordinary (non-syscall) instruction steps -/

inductive msteps (segs : List Segment) : machine_state → machine_state → Prop where
  | mst_refl (ms) : msteps segs ms ms
  | mst_step (ms ms' ms'') :
      ms.ms_svc_pending = none → RiscvSemantics.step segs ms = .MachineOk ms' → msteps segs ms' ms'' →
      msteps segs ms ms''

theorem msteps_one (segs : List Segment) :
    ∀ ms ms', ms.ms_svc_pending = none → RiscvSemantics.step segs ms = .MachineOk ms' → msteps segs ms ms' :=
  fun ms ms' hsvc hstep => .mst_step ms ms' ms' hsvc hstep (.mst_refl _)

theorem msteps_trans (segs : List Segment) :
    ∀ ms ms' ms'', msteps segs ms ms' → msteps segs ms' ms'' → msteps segs ms ms'' := by
  intro ms ms' ms'' h
  induction h with
  | mst_refl => exact id
  | mst_step ms ms1 ms2 hsvc hstep _ ih => exact fun h2 => .mst_step _ _ _ hsvc hstep (ih h2)

theorem msteps_to_wexit (segs : List Segment) :
    ∀ ms ms' bufs code, msteps segs ms ms' → to_wexit segs ms' bufs code → to_wexit segs ms bufs code := by
  intro ms ms' bufs code h
  induction h with
  | mst_refl => exact id
  | mst_step ms ms1 ms2 hsvc hstep _ ih => exact fun hw => .tw_step _ _ _ _ hsvc hstep (ih hw)

/-- Every buffer a `to_wexit` derivation writes is nonempty. -/
theorem to_wexit_bufs_nonempty (segs : List Segment) :
    ∀ ms bufs code, to_wexit segs ms bufs code → ∀ b ∈ bufs, 1 ≤ b.length := by
  intro ms bufs code h
  induction h with
  | tw_exit => intro b hb; cases hb
  | tw_write ms x8 buf bufs code _ _ _ _ hnb _ ih =>
    intro b hb
    rcases List.mem_cons.1 hb with rfl | hb
    · exact hnb
    · exact ih buf.length hnb (Nat.le_refl _) b hb
  | tw_step _ _ _ _ _ _ _ ih => exact ih

/-! ### One-step inversion for a write configuration -/

/-- The `SNext` half (Lean-only helper; CatSim.v's `sstep_write_next_inv` at a general channel). -/
theorem sstep_write_ch_next_inv (segs : List Segment) (fd ch : word) (Hfd32 : fd32 fd = fd) :
    ∀ ms model x8 buf evs c', m_halted model = none → m_vm_lazy model = [] → fdchan fd ch model →
      ms.ms_svc_pending = some x8 → bv_unsigned x8 = 64 → ms_gpr ms 0 = fd →
      ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf → 1 ≤ buf.length →
      sstep segs (mkCfg ms model) evs (.SNext c') →
        ∃ n, 1 ≤ n ∧ n ≤ buf.length ∧ evs = (buf.take n).map (event.WriteEv ch) ∧
          c' = mkCfg (advance_past_svc (set_gpr0 ms (len_word (buf.take n)))) model := by
  intro ms model x8 buf evs c' hh hlazy hfdc hsvc hno hg hr hnb hss
  cases hss with
  | sstep_instr _ _ _ _ _ h => rw [hsvc] at h; cases h
  | sstep_syscall _ _ x eff model' model'' evs0 _ h hspec _ hmat =>
    rw [hsvc] at h; cases h
    obtain ⟨n, hn1, hn2, rfl, rfl, rfl⟩ := write_ch_ok_inv segs ms x8 model fd ch eff model' _ buf hfdc Hfd32 hno hg hr hnb hspec
    rw [materialize_model_accesses_no_lazy _ _ hlazy] at hmat
    cases hmat
    exact ⟨n, hn1, hn2, rfl, by rw [apply_effect_copyins_no_write]⟩
  | sstep_exit _ _ x eff model' evs0 code _ h hspec hcode _ =>
    rw [hsvc] at h; cases h
    obtain ⟨n, _, _, _, rfl, _⟩ := write_ch_ok_inv segs ms x8 model fd ch eff model' _ buf hfdc Hfd32 hno hg hr hnb hspec
    rw [hh] at hcode; cases hcode
  | sstep_killed _ _ x eff model' evs0 sig _ h hspec hk =>
    rw [hsvc] at h; cases h
    obtain ⟨n, _, _, _, rfl, _⟩ := write_ch_ok_inv segs ms x8 model fd ch eff model' _ buf hfdc Hfd32 hno hg hr hnb hspec
    rw [m_killed_of_m_halted_none _ hh] at hk; cases hk

theorem sstep_write_ch_inv (segs : List Segment) (fd ch : word) (Hfd32 : fd32 fd = fd) :
    ∀ ms model x8 buf evs st, m_halted model = none → m_vm_lazy model = [] → fdchan fd ch model →
      ms.ms_svc_pending = some x8 → bv_unsigned x8 = 64 → ms_gpr ms 0 = fd →
      ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf → buf_modeled buf → 1 ≤ buf.length →
      sstep segs (mkCfg ms model) evs st →
        ∃ n, 1 ≤ n ∧ n ≤ buf.length ∧ evs = (buf.take n).map (event.WriteEv ch) ∧
          st = .SNext (mkCfg (advance_past_svc (set_gpr0 ms (len_word (buf.take n)))) model) := by
  intro ms model x8 buf evs st hh hlazy hfdc hsvc hno hg hr hcnt hnb hss
  cases st with
  | SNext c' =>
    obtain ⟨n, hn1, hn2, hevs, hc'⟩ :=
      sstep_write_ch_next_inv segs fd ch Hfd32 ms model x8 buf evs c' hh hlazy hfdc hsvc hno hg hr hnb hss
    exact ⟨n, hn1, hn2, hevs, by rw [hc']⟩
  | SError =>
    exfalso
    cases hss with
    | sstep_instr_fault _ _ _ h => rw [hsvc] at h; cases h
    | sstep_instr_unmodeled _ _ _ h => rw [hsvc] at h; cases h
    | sstep_syscall_materialization_fault _ _ x eff model' evs0 _ h hspec _ hmat =>
      rw [hsvc] at h; cases h
      obtain ⟨n, _, _, _, rfl, _⟩ :=
        write_ch_ok_inv segs ms x8 model fd ch eff model' _ buf hfdc Hfd32 hno hg hr hnb hspec
      rw [materialize_model_accesses_no_lazy _ _ hlazy] at hmat; cases hmat
    | sstep_syscall_unmodeled _ _ x _ h hspec =>
      rw [hsvc] at h; cases h
      exact write_ch_no_unmodeled segs ms x8 model fd ch buf hfdc Hfd32 hno hg hr hcnt hnb hspec

/-- The step that actually HAPPENED, inverted (fd 1). -/
theorem sstep_write_next_inv (segs : List Segment) :
    ∀ ms model x8 buf evs c', m_halted model = none → m_vm_lazy model = [] → fd1chan model →
      ms.ms_svc_pending = some x8 → bv_unsigned x8 = 64 → ms_gpr ms 0 = Z_to_bv 64 1 →
      ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf → 1 ≤ buf.length →
      sstep segs (mkCfg ms model) evs (.SNext c') →
        ∃ n, 1 ≤ n ∧ n ≤ buf.length ∧ evs = (buf.take n).map (event.WriteEv (Z_to_bv 64 1)) ∧
          c' = mkCfg (advance_past_svc (set_gpr0 ms (len_word (buf.take n)))) model :=
  fun ms model x8 buf evs c' hh hlazy hfd =>
    sstep_write_ch_next_inv segs _ _ fd32_one ms model x8 buf evs c' hh hlazy (fd1chan_fdchan _ hfd)

theorem sstep_write_inv (segs : List Segment) :
    ∀ ms model x8 buf evs st, m_halted model = none → m_vm_lazy model = [] → fd1chan model →
      ms.ms_svc_pending = some x8 → bv_unsigned x8 = 64 → ms_gpr ms 0 = Z_to_bv 64 1 →
      ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf → buf_modeled buf → 1 ≤ buf.length →
      sstep segs (mkCfg ms model) evs st →
        ∃ n, 1 ≤ n ∧ n ≤ buf.length ∧ evs = (buf.take n).map (event.WriteEv (Z_to_bv 64 1)) ∧
          st = .SNext (mkCfg (advance_past_svc (set_gpr0 ms (len_word (buf.take n)))) model) :=
  fun ms model x8 buf evs st hh hlazy hfd =>
    sstep_write_ch_inv segs _ _ fd32_one ms model x8 buf evs st hh hlazy (fd1chan_fdchan _ hfd)

/-! ### Trace characterization -/

def wevents : List (List byte) → List event
  | [] => []
  | buf :: rest => buf.map (event.WriteEv (Z_to_bv 64 1)) ++ wevents rest

/-! ### The omni reading: one induction over `to_wexit` -/

def wexit_post (bufs : List (List byte)) (code : word) (fs : Fs) : post :=
  fun tr o => (∃ full, wpick (Z_to_bv 64 1) bufs full ∧ tr = full ++ [.ExitEv code fs]) ∧ exits_with code tr o

/-- The exit transition of a `tw_exit` configuration (Lean-only helper). -/
theorem tw_exit_sstep (segs : List Segment) (ms : machine_state) (model : Model) (x8 : word)
    (hh : m_halted model = none) (hsvc : ms.ms_svc_pending = some x8) (hx8 : is_exit_no x8) :
    sstep segs (mkCfg ms model) [.ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
      (.SNext (mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))) :=
  sstep.sstep_exit ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
    (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model) [] (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
    hh hsvc (exit_dispatch_ok (sys_input segs ms x8) model hx8) rfl (m_killed_with_halted _ _)

/-- The full-delivery write transition of a `tw_write` configuration, at any `n` (Lean-only helper). -/
theorem tw_write_sstep (segs : List Segment) (ms : machine_state) (model : Model) (x8 : word) (buf : List byte)
    (n : Nat) (hh : m_halted model = none) (hlazy : m_vm_lazy model = []) (hfd : fd1chan model)
    (hsvc : ms.ms_svc_pending = some x8) (hno : bv_unsigned x8 = 64) (hg : ms_gpr ms 0 = Z_to_bv 64 1)
    (hr : ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = some buf) (hb : buf_modeled buf) (hn1 : 1 ≤ n)
    (hn2 : n ≤ buf.length) :
    sstep segs (mkCfg ms model) ((buf.take n).map (event.WriteEv (Z_to_bv 64 1)))
      (.SNext (mkCfg (advance_past_svc (set_gpr0 ms (len_word (buf.take n)))) model)) := by
  rw [← apply_effect_copyins_no_write ms (len_word (buf.take n)) [(ms_gpr ms 1, n)]]
  exact sstep.sstep_syscall ms model x8 _ model model _ hh hsvc
    (write1_ok_n segs ms x8 model buf n hfd hno hg hr hb hn1 hn2) hh
    (materialize_model_accesses_no_lazy _ _ hlazy)

theorem to_wexit_exec (segs : List Segment) :
    ∀ ms bufs code, to_wexit segs ms bufs code →
      ∀ model, m_halted model = none → m_vm_lazy model = [] → fd1chan model → bufs_modeled bufs →
        OmniRun.exec segs (mkCfg ms model) (wexit_post bufs code (m_fs model)) := by
  intro ms bufs code hte
  induction hte with
  | tw_exit ms x8 hsvc hx8 =>
    intro model hh hlazy _ _
    refine exec_step_only segs _ _ _ _ (tw_exit_sstep segs ms model x8 hh hsvc hx8)
      (fun evs st hss => sstep_exit_inv segs ms model x8 evs st hh hsvc hx8 hss) ?_
    refine .exec_halt _ _ (by simp [mkCfg, m_halted_with_halted]) ⟨⟨[], .wp_nil, by simp⟩, ?_⟩
    exact ⟨m_halted_with_halted _ _, m_killed_with_halted _ _⟩
  | tw_write ms x8 buf bufs code hsvc hno hg hr hnb _ ih =>
    intro model hh hlazy hfd hbm
    have hb : buf_modeled buf := hbm buf (List.mem_cons_self ..)
    have hbs : bufs_modeled bufs := fun b h => hbm b (List.mem_cons_of_mem _ h)
    refine .exec_step _ _ hh ?_ ?_ ?_
    · exact ⟨_, _, tw_write_sstep segs ms model x8 buf buf.length hh hlazy hfd hsvc hno hg hr hb hnb (Nat.le_refl _)⟩
    · intro evs hss
      obtain ⟨n, _, _, _, habs⟩ := sstep_write_inv segs ms model x8 buf evs .SError hh hlazy hfd hsvc hno hg hr hb hnb hss
      cases habs
    · intro evs c' hss
      obtain ⟨n, hn1, hn2, rfl, hc'⟩ :=
        sstep_write_inv segs ms model x8 buf evs (.SNext c') hh hlazy hfd hsvc hno hg hr hb hnb hss
      cases hc'
      refine exec_conseq segs _ _ _ (ih n hn1 hn2 model hh hlazy hfd hbs) ?_
      rintro tr o ⟨⟨full, hpick, rfl⟩, hx⟩
      exact ⟨⟨_ ++ full, .wp_cons buf bufs n full hn1 hn2 hpick, by simp⟩, hx⟩
  | tw_step ms ms' bufs code hsvc hstep _ ih =>
    intro model hh hlazy hfd hbm
    refine exec_step_only segs _ _ [] (mkCfg ms' model) ?_
      (fun evs st hss => sstep_instr_inv segs ms model ms' evs st hlazy hsvc hstep hss) ?_
    · refine .sstep_instr ms model ms' model hh hsvc ?_
      rw [mi_account_step_no_lazy segs ms model hlazy, hstep]
    · exact exec_conseq segs _ _ _ (ih model hh hlazy hfd hbm) (fun tr o h => by simpa using h)

theorem to_wexit_star_admits (segs : List Segment) :
    ∀ ms bufs code, to_wexit segs ms bufs code →
      ∀ model full, m_halted model = none → m_vm_lazy model = [] → fd1chan model → bufs_modeled bufs →
        wpick (Z_to_bv 64 1) bufs full → ∃ c, star segs (mkCfg ms model) (full ++ [.ExitEv code (m_fs model)]) c := by
  intro ms bufs code hte
  induction hte with
  | tw_exit ms x8 hsvc hx8 =>
    intro model full hh _ _ _ hpick
    cases hpick
    exact ⟨_, star_one segs _ _ _ (tw_exit_sstep segs ms model x8 hh hsvc hx8)⟩
  | tw_write ms x8 buf bufs code hsvc hno hg hr hnb _ ih =>
    intro model full hh hlazy hfd hbm hpick
    have hb : buf_modeled buf := hbm buf (List.mem_cons_self ..)
    have hbs : bufs_modeled bufs := fun b h => hbm b (List.mem_cons_of_mem _ h)
    cases hpick with
    | wp_cons _ _ n tr hn1 hn2 hpick' =>
      obtain ⟨c, hstar⟩ := ih n hn1 hn2 model tr hh hlazy hfd hbs hpick'
      refine ⟨c, ?_⟩
      rw [List.append_assoc]
      exact .star_step _ _ _ _ _ (tw_write_sstep segs ms model x8 buf n hh hlazy hfd hsvc hno hg hr hb hn1 hn2) hstar
  | tw_step ms ms' bufs code hsvc hstep _ ih =>
    intro model full hh hlazy hfd hbm hpick
    obtain ⟨c, hstar⟩ := ih model full hh hlazy hfd hbm hpick
    refine ⟨c, ?_⟩
    have hs : sstep segs (mkCfg ms model) [] (.SNext (mkCfg ms' model)) := by
      refine .sstep_instr ms model ms' model hh hsvc ?_
      rw [mi_account_step_no_lazy segs ms model hlazy, hstep]
    simpa using star.star_step _ _ _ _ _ hs hstar

theorem to_wexit_star_only (segs : List Segment) :
    ∀ ms bufs code, to_wexit segs ms bufs code →
      ∀ model, m_halted model = none → m_vm_lazy model = [] → fd1chan model → bufs_modeled bufs →
        ∀ tr c, star segs (mkCfg ms model) tr c →
          ∃ full, wpick (Z_to_bv 64 1) bufs full ∧ is_prefix tr (full ++ [.ExitEv code (m_fs model)]) := by
  intro ms bufs code hte model hh hlazy hfd hbm tr c hstar
  obtain ⟨tr', o, _, ⟨full, hpick, heq⟩, _⟩ :=
    exec_realizes segs _ _ (exec_star segs _ _ _ _ (to_wexit_exec segs ms bufs code hte model hh hlazy hfd hbm) hstar)
  exact ⟨full, hpick, by rw [← heq]; exact is_prefix_app _ _⟩

/-! ### No-error characterization: a corollary of `to_wexit_exec` -/

theorem to_wexit_no_error (segs : List Segment) :
    ∀ ms model bufs code, m_halted model = none → m_vm_lazy model = [] → fd1chan model →
      to_wexit segs ms bufs code → bufs_modeled bufs → ¬ reaches_error segs (mkCfg ms model) := by
  intro ms model bufs code hh hlazy hfd hte hbm
  exact exec_no_error segs _ (exec_conseq segs _ _ _ (to_wexit_exec segs ms bufs code hte model hh hlazy hfd hbm)
    (fun tr o h => exits_with_never_errors _ _ _ h.2))

end LPS
