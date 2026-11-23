import LPS.LinuxProcessSem.Run1
import LPS.LinuxProcessSem.Specs

/-!
# LPS `theories/LinuxProcessSem/Run.v` (f1006fe8), part 2: the step relation and the behaviours

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/Run.v` at f1006fe8 (TRUST BOUNDARY there): `sstep`, `star`, `obs_trace`,
`reaches_error`, `all_traces_error`, `run`; the spurious-failure configuration (`InjectedArm`,
`injected_table`, `spurious_refusal_cfg`, `sstep_cfg`, `run_scfg`); the budget refusal. Section
variables as in Run1 (here only `mi_loaded_segments`, written `segs`).
-/

namespace LPS
open RiscvSemantics

/-- One step of the process (Run.v's `sstep`, section variable `mi_loaded_segments`). -/
inductive sstep (segs : List Segment) : config → List event → step_to → Prop where
  | sstep_instr (ms model ms' model') :
      m_halted model = none → ms.ms_svc_pending = none →
      mi_account_step segs ms model = .MachineOk (ms', model') →
      sstep segs (mkCfg ms model) [] (.SNext (mkCfg ms' model'))
  | sstep_instr_fault (ms model) :
      m_halted model = none → ms.ms_svc_pending = none → mi_account_step segs ms model = .MachineFault →
      sstep segs (mkCfg ms model) [] .SError
  | sstep_instr_unmodeled (ms model) :
      m_halted model = none → ms.ms_svc_pending = none → mi_account_step segs ms model = .MachineUnmodeled →
      sstep segs (mkCfg ms model) [] .SError
  | sstep_syscall (ms model x8 eff model' model'' evs) :
      m_halted model = none → ms.ms_svc_pending = some x8 →
      syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) → m_halted model' = none →
      materialize_model_accesses model' (syscall_effect_accesses eff) = some model'' →
      sstep segs (mkCfg ms model) evs (.SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model''))
  | sstep_syscall_materialization_fault (ms model x8 eff model' evs) :
      m_halted model = none → ms.ms_svc_pending = some x8 →
      syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) → m_halted model' = none →
      materialize_model_accesses model' (syscall_effect_accesses eff) = none →
      sstep segs (mkCfg ms model) [] .SError
  | sstep_exit (ms model x8 eff model' evs code) :
      m_halted model = none → ms.ms_svc_pending = some x8 →
      syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) → m_halted model' = some code →
      m_killed model' = none →
      sstep segs (mkCfg ms model) (evs ++ [.ExitEv code (m_fs model')]) (.SNext (mkCfg ms model'))
  | sstep_killed (ms model x8 eff model' evs sig) :
      m_halted model = none → ms.ms_svc_pending = some x8 →
      syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) → m_killed model' = some sig →
      sstep segs (mkCfg ms model) (evs ++ [.KillEv sig (m_fs model')]) (.SNext (mkCfg ms model'))
  | sstep_syscall_unmodeled (ms model x8) :
      m_halted model = none → ms.ms_svc_pending = some x8 →
      syscall_spec (sys_input segs ms x8) model Unmodeled →
      sstep segs (mkCfg ms model) [] .SError

inductive star (segs : List Segment) : config → List event → config → Prop where
  | star_refl (c) : star segs c [] c
  | star_step (c1 evs c2 tr c3) : sstep segs c1 evs (.SNext c2) → star segs c2 tr c3 → star segs c1 (evs ++ tr) c3

def obs_trace (segs : List Segment) (c0 : config) (tr : List event) : Prop :=
  ∃ tr' c, star segs c0 tr' c ∧ is_prefix tr tr'

def decl_off_frame : Prop :=
  ∀ i m eff m' evs, syscall_spec i m (Ok eff m' evs) → m_abort_terminal m = false → m_sigabrt_pending m = false →
    m_abort_terminal m' = false ∧ m_sigabrt_pending m' = false ∧ m_killed m' = none ∧ ∀ sig fs, event.KillEv sig fs ∉ evs

def decl_off_frame_one_sided : Prop :=
  ∀ i m eff m' evs, syscall_spec i m (Ok eff m' evs) → m_abort_terminal m = false →
    m_abort_terminal m' = false ∧ m_killed m' = none ∧ ∀ sig fs, event.KillEv sig fs ∉ evs

def reaches_error (segs : List Segment) (c0 : config) : Prop := ∃ tr c evs, star segs c0 tr c ∧ sstep segs c evs .SError

def unmodeled_at (segs : List Segment) (c : config) : Prop :=
  m_halted c.cfg_model = none ∧
    ((c.cfg_ms.ms_svc_pending = none ∧ mi_account_step segs c.cfg_ms c.cfg_model = .MachineUnmodeled) ∨
     (∃ x8, c.cfg_ms.ms_svc_pending = some x8 ∧ syscall_spec (sys_input segs c.cfg_ms x8) c.cfg_model Unmodeled))

def reaches_unmodeled (segs : List Segment) (c0 : config) : Prop := ∃ tr c, star segs c0 tr c ∧ unmodeled_at segs c

/-- Every run from `c` errs (inductive: every run is finite and ends in an error). -/
inductive all_traces_error (segs : List Segment) : config → Prop where
  | all_traces_error_intro (c) :
      (∃ evs to, sstep segs c evs to) →
      (∀ evs c', sstep segs c evs (.SNext c') → all_traces_error segs c') →
      all_traces_error segs c

/-- Run.v's `run`: the behaviour of an image from an entry draw on an input. -/
def run (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) : behavior :=
  match img, en with
  | ⟨segs, pc, ph⟩, ⟨sp, brk0, mbase, rnd⟩ =>
    let c0 := init_config segs pc ph sp brk0 mbase rnd lim inp
    { bh_traces := obs_trace segs c0, bh_errors := reaches_error segs c0, bh_all_errors := all_traces_error segs c0,
      bh_unmodeled := reaches_unmodeled segs c0 }

structure InjectedArm where
  ia_no : Int
  ia_family : SpuriousFamily
  ia_errnos : List Int

def mkInjectedArm := @InjectedArm.mk

/-- Run.v's `injected_table`, same arms in the same order. -/
def injected_table : List InjectedArm :=
  [mkInjectedArm 17 .FamFs getcwd_errnos,
   mkInjectedArm 23 .FamFd dup_errnos,
   mkInjectedArm 35 .FamFs unlinkat_errnos,
   mkInjectedArm 48 .FamFs faccessat_errnos,
   mkInjectedArm 56 .FamFs openat_errnos,
   mkInjectedArm 59 .FamFd pipe2_errnos,
   mkInjectedArm 101 .FamIntr [EINTR],
   mkInjectedArm 144 .FamCred (setid_errnos true),
   mkInjectedArm 146 .FamCred (setid_errnos true),
   mkInjectedArm 147 .FamCred (setid_errnos true),
   mkInjectedArm 149 .FamCred (setid_errnos true),
   mkInjectedArm 157 .FamCred [EPERM],
   mkInjectedArm 198 .FamFd socket_errnos,
   mkInjectedArm 199 .FamFd (socketpair_reserve_errnos ++ socketpair_create_errnos),
   mkInjectedArm 200 .FamNet bind_errnos,
   mkInjectedArm 201 .FamNet listen_errnos,
   mkInjectedArm 202 .FamFd accept_errnos,
   mkInjectedArm 214 .FamAlloc [],
   mkInjectedArm 216 .FamAlloc mremap_errnos,
   mkInjectedArm 220 .FamFd clone_errnos,
   mkInjectedArm 222 .FamAlloc mmap_errnos,
   mkInjectedArm 226 .FamAlloc mprotect_errnos,
   mkInjectedArm 242 .FamFd accept_errnos,
   mkInjectedArm 278 .FamIntr getrandom_errnos,
   mkInjectedArm 435 .FamFd clone_errnos]

def lookup_injected : List InjectedArm → Int → Option InjectedArm
  | [], _ => none
  | a :: r, n => if a.ia_no == n then some a else lookup_injected r n

def injected_arm (no : Int) : Option InjectedArm := lookup_injected injected_table no

def ret_in_errnos (es : List Int) (r : word) : Bool := es.any fun e => bv_eqb r (errno_ret e)

def brk_refusal_b (m : Model) (req ret : word) : Bool :=
  let h := m_vmmaps m
  let b := h.vm_brk
  !(w_is0 req) && !(decide (bv_unsigned req < bv_unsigned (min_brk h))) && !(bv_eqb req b) && bv_eqb ret b

def refusal_b (i : SyscallInput) (m : Model) (ret : word) : Bool :=
  let no := bv_unsigned i.in_sysno
  if no == 214 then brk_refusal_b m (in_arg i 0) ret
  else match injected_arm no with
    | some a => ret_in_errnos a.ia_errnos ret
    | none => false

def alloc_mark_sysnos : List Int := [214, 216, 222, 226]

def alloc_budget_refused_b (i : SyscallInput) (m : Model) : Bool :=
  let no := bv_unsigned i.in_sysno
  if no == 214 then brk_budget_refused_b m (in_arg i 0)
  else if no == 216 then mremap_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) m
  else if no == 222 then
    mmap_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) m
  else if no == 226 then mprotect_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2) m
  else false

def injected_family_off (cfg : SpuriousCfg) (i : SyscallInput) : Bool :=
  match injected_arm (bv_unsigned i.in_sysno) with
  | some a => !(family_may_fail cfg a.ia_family)
  | none => false

def spurious_refusal_cfg (cfg : SpuriousCfg) (i : SyscallInput) (m : Model) (eff : SyscallEffect) : Prop :=
  injected_family_off cfg i = true ∧ refusal_b i m eff.eff_ret = true ∧
    ∃ eff' m' evs', syscall_spec i m (Ok eff' m' evs') ∧ refusal_b i m eff'.eff_ret = false

def refusal_decided (cfg : SpuriousCfg) (i : SyscallInput) (m : Model) : Prop :=
  injected_family_off cfg i = true →
    (∃ eff' m' evs', syscall_spec i m (Ok eff' m' evs') ∧ refusal_b i m eff'.eff_ret = false) ∨
    (∀ eff' m' evs', syscall_spec i m (Ok eff' m' evs') → refusal_b i m eff'.eff_ret = true)

/-- `sstep` under a spurious-failure configuration (Run.v's `sstep_cfg`, section `StepCfg`'s `segs`). -/
inductive sstep_cfg (segs : List Segment) (cfg : SpuriousCfg) : config → List event → step_to → Prop where
  | sstep_cfg_instr (ms model ms' model') :
      m_halted model = none → ms.ms_svc_pending = none →
      mi_account_step segs ms model = .MachineOk (ms', model') →
      sstep_cfg segs cfg (mkCfg ms model) [] (.SNext (mkCfg ms' model'))
  | sstep_cfg_instr_fault (ms model) :
      m_halted model = none → ms.ms_svc_pending = none → mi_account_step segs ms model = .MachineFault →
      sstep_cfg segs cfg (mkCfg ms model) [] .SError
  | sstep_cfg_instr_unmodeled (ms model) :
      m_halted model = none → ms.ms_svc_pending = none → mi_account_step segs ms model = .MachineUnmodeled →
      sstep_cfg segs cfg (mkCfg ms model) [] .SError
  | sstep_cfg_syscall (ms model x8 eff model' model'' evs) :
      m_halted model = none → ms.ms_svc_pending = some x8 →
      syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) →
      ¬ spurious_refusal_cfg cfg (sys_input segs ms x8) model eff → m_halted model' = none →
      materialize_model_accesses model' (syscall_effect_accesses eff) = some model'' →
      sstep_cfg segs cfg (mkCfg ms model) evs (.SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model''))
  | sstep_cfg_syscall_materialization_fault (ms model x8 eff model' evs) :
      m_halted model = none → ms.ms_svc_pending = some x8 →
      syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) →
      ¬ spurious_refusal_cfg cfg (sys_input segs ms x8) model eff → m_halted model' = none →
      materialize_model_accesses model' (syscall_effect_accesses eff) = none →
      sstep_cfg segs cfg (mkCfg ms model) [] .SError
  | sstep_cfg_exit (ms model x8 eff model' evs code) :
      m_halted model = none → ms.ms_svc_pending = some x8 →
      syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) → m_halted model' = some code →
      m_killed model' = none →
      sstep_cfg segs cfg (mkCfg ms model) (evs ++ [.ExitEv code (m_fs model')]) (.SNext (mkCfg ms model'))
  | sstep_cfg_killed (ms model x8 eff model' evs sig) :
      m_halted model = none → ms.ms_svc_pending = some x8 →
      syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) → m_killed model' = some sig →
      sstep_cfg segs cfg (mkCfg ms model) (evs ++ [.KillEv sig (m_fs model')]) (.SNext (mkCfg ms model'))
  | sstep_cfg_syscall_unmodeled (ms model x8) :
      m_halted model = none → ms.ms_svc_pending = some x8 →
      syscall_spec (sys_input segs ms x8) model Unmodeled →
      sstep_cfg segs cfg (mkCfg ms model) [] .SError

inductive star_cfg (segs : List Segment) (cfg : SpuriousCfg) : config → List event → config → Prop where
  | star_cfg_refl (c) : star_cfg segs cfg c [] c
  | star_cfg_step (c1 evs c2 tr c3) :
      sstep_cfg segs cfg c1 evs (.SNext c2) → star_cfg segs cfg c2 tr c3 → star_cfg segs cfg c1 (evs ++ tr) c3

def obs_trace_cfg (segs : List Segment) (cfg : SpuriousCfg) (c0 : config) (tr : List event) : Prop :=
  ∃ tr' c, star_cfg segs cfg c0 tr' c ∧ is_prefix tr tr'

def reaches_error_cfg (segs : List Segment) (cfg : SpuriousCfg) (c0 : config) : Prop :=
  ∃ tr c evs, star_cfg segs cfg c0 tr c ∧ sstep_cfg segs cfg c evs .SError

inductive all_traces_error_cfg (segs : List Segment) (cfg : SpuriousCfg) : config → Prop where
  | all_traces_error_cfg_intro (c) :
      (∃ evs to, sstep_cfg segs cfg c evs to) →
      (∀ evs c', sstep_cfg segs cfg c evs (.SNext c') → all_traces_error_cfg segs cfg c') →
      all_traces_error_cfg segs cfg c

def reaches_unmodeled_cfg (segs : List Segment) (cfg : SpuriousCfg) (c0 : config) : Prop :=
  ∃ tr c, star_cfg segs cfg c0 tr c ∧ unmodeled_at segs c

def run_scfg (cfg : SpuriousCfg) (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) : behavior :=
  match img, en with
  | ⟨segs, pc, ph⟩, ⟨sp, brk0, mbase, rnd⟩ =>
    let c0 := init_config segs pc ph sp brk0 mbase rnd lim inp
    { bh_traces := obs_trace_cfg segs cfg c0, bh_errors := reaches_error_cfg segs cfg c0,
      bh_all_errors := all_traces_error_cfg segs cfg c0, bh_unmodeled := reaches_unmodeled_cfg segs cfg c0 }

def behavior_equiv (b1 b2 : behavior) : Prop :=
  (∀ tr, b1.bh_traces tr ↔ b2.bh_traces tr) ∧ (b1.bh_errors ↔ b2.bh_errors) ∧ (b1.bh_all_errors ↔ b2.bh_all_errors) ∧
    (b1.bh_unmodeled ↔ b2.bh_unmodeled)

def run_nospurious (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) : behavior :=
  run_scfg (alloc_only_cfg false) img lim en inp

def run_cfg (alloc_may_fail : Bool) (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) : behavior :=
  if alloc_may_fail then run img lim en inp else run_nospurious img lim en inp

def budget_refused_at (segs : List Segment) (c : config) : Prop :=
  m_halted c.cfg_model = none ∧
    ((c.cfg_ms.ms_svc_pending = none ∧
        ∃ report, step_accesses segs c.cfg_ms = .MachineOk report ∧
          materialize_model_accesses c.cfg_model report.accessed_ranges = none) ∨
     (∃ x8, c.cfg_ms.ms_svc_pending = some x8 ∧
        (alloc_budget_refused_b (sys_input segs c.cfg_ms x8) c.cfg_model = true ∨
         ∃ eff model' evs, syscall_spec (sys_input segs c.cfg_ms x8) c.cfg_model (Ok eff model' evs) ∧
           m_halted model' = none ∧ materialize_model_accesses model' (syscall_effect_accesses eff) = none)))

def reaches_budget_refused (segs : List Segment) (c0 : config) : Prop :=
  ∃ tr c, star segs c0 tr c ∧ budget_refused_at segs c

def reaches_budget_refused_cfg (segs : List Segment) (cfg : SpuriousCfg) (c0 : config) : Prop :=
  ∃ tr c, star_cfg segs cfg c0 tr c ∧ budget_refused_at segs c

def run_budget_refused (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) : Prop :=
  match img, en with
  | ⟨segs, pc, ph⟩, ⟨sp, brk0, mbase, rnd⟩ => reaches_budget_refused segs (init_config segs pc ph sp brk0 mbase rnd lim inp)

def run_scfg_budget_refused (cfg : SpuriousCfg) (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) : Prop :=
  match img, en with
  | ⟨segs, pc, ph⟩, ⟨sp, brk0, mbase, rnd⟩ =>
    reaches_budget_refused_cfg segs cfg (init_config segs pc ph sp brk0 mbase rnd lim inp)

end LPS
