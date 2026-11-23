import LPS.LinuxProcessSem.RiscvSemantics2
import LPS.LinuxProcessSem.StackLayout
import LPS.LinuxProcessSem.Sys.Fs.Namei

/-!
# LPS `theories/LinuxProcessSem/Run.v` (f1006fe8), part 1: configurations, the initial state, valid inputs

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/Run.v` at f1006fe8 (TRUST BOUNDARY there): its definitions that do not
mention `syscall_spec` (the step relation and the behaviours are Run2). Section `WithMemImage`'s variables
become leading arguments of the definitions that use them, in their declaration order
(`mi_loaded_segments`, `mi_init_pc`, `mi_phdrs`, `mi_init_sp`, `mi_init_brk`, `mi_mmap_base`, `mi_draw`,
`mi_alloc_limit`), as Rocq's section closing does.
-/

namespace LPS
open RiscvSemantics

def is_prefix {A : Type} : List A → List A → Prop
  | [], _ => True
  | _ :: _, [] => False
  | x :: xs, y :: ys => x = y ∧ is_prefix xs ys

/-- What a run admits: its observable traces (prefix-closed), whether some run errs, whether all do,
    whether some run leaves the model. -/
structure behavior where
  bh_traces : List event → Prop
  bh_errors : Prop
  bh_all_errors : Prop
  bh_unmodeled : Prop

def mkBehavior := @behavior.mk

def syscall_args (ms : machine_state) : List word :=
  [ms_gpr ms 0, ms_gpr ms 1, ms_gpr ms 2, ms_gpr ms 3, ms_gpr ms 4, ms_gpr ms 5]

def apply_writes (mem : word → Option byte) : List (word × List byte) → word → Option byte
  | [] => mem
  | (a, bs) :: r => apply_writes (write_to_mem mem a bs) r

def zeros_cover (zs : List (word × word)) (a : word) : Bool :=
  zs.any fun z => decide (bv_unsigned z.1 ≤ bv_unsigned a) && decide (bv_unsigned a < bv_unsigned z.1 + bv_unsigned z.2)

def apply_zeros (mem : word → Option byte) (zs : List (word × word)) : word → Option byte :=
  match zs with
  | [] => mem
  | _ => fun a => if zeros_cover zs a then some (Z_to_bv 8 0) else mem a

def apply_unmaps (mem : word → Option byte) (us : List (word × word)) : word → Option byte :=
  match us with
  | [] => mem
  | _ => fun a => if zeros_cover us a then none else mem a

def apply_copy (before mem : word → Option byte) (c : MemCopy) : word → Option byte :=
  fun a =>
    if decide (bv_unsigned c.copy_dst ≤ bv_unsigned a) && decide (bv_unsigned a < bv_unsigned c.copy_dst + bv_unsigned c.copy_len)
    then before (Z_to_bv 64 (bv_unsigned c.copy_src + (bv_unsigned a - bv_unsigned c.copy_dst)))
    else mem a

def apply_copies (before : word → Option byte) : (word → Option byte) → List MemCopy → word → Option byte
  | mem, [] => mem
  | mem, c :: r => apply_copies before (apply_copy before mem c) r

def apply_effect (ms : machine_state) (eff : SyscallEffect) : machine_state :=
  let ms' := set_reg ms 10 eff.eff_ret
  { ms_regs := ms'.ms_regs, ms_fregs := ms'.ms_fregs, ms_pc_val := ms'.ms_pc_val,
    ms_svc_pending := ms'.ms_svc_pending, ms_resv := ms'.ms_resv, ms_fcsr := ms'.ms_fcsr,
    ms_mem := apply_writes (apply_copies ms'.ms_mem (apply_zeros (apply_unmaps ms'.ms_mem eff.eff_unmaps) eff.eff_zeros)
      eff.eff_copies) eff.eff_writes,
    ms_rom := ms'.ms_rom }

def advance_past_svc (ms : machine_state) : machine_state :=
  { ms_regs := ms.ms_regs, ms_fregs := ms.ms_fregs, ms_pc_val := ms_pc ms + Z_to_bv 64 4, ms_svc_pending := none,
    ms_resv := ms.ms_resv, ms_fcsr := ms.ms_fcsr, ms_mem := ms.ms_mem, ms_rom := ms.ms_rom }

structure config where
  cfg_ms : machine_state
  cfg_model : Model

def mkCfg := @config.mk

def segment_reservation (s : Segment) : word × word :=
  let lo := page_round_down_Z (s.seg_base : Int)
  let hi := page_round_up_Z ((s.seg_base : Int) + (s.seg_size : Int))
  (Z_to_bv 64 lo, Z_to_bv 64 (hi - lo))

def segments_reserved (segs : List Segment) : List (word × word) := segs.map segment_reservation

inductive step_to where
  | SNext (c : config)
  | SError

def mi_account_step (mi_loaded_segments : List Segment) (ms : machine_state) (model : Model) :
    machine_result (machine_state × Model) :=
  match step_accesses mi_loaded_segments ms with
  | .MachineOk report =>
    match materialize_model_accesses model report.accessed_ranges with
    | some model' => .MachineOk (report.access_value, model')
    | none => .MachineFault
  | .MachineFault => .MachineFault
  | .MachineUnmodeled => .MachineUnmodeled

def sys_input (mi_loaded_segments : List Segment) (ms : machine_state) (x8 : word) : SyscallInput :=
  mkInput x8 (syscall_args ms) (ms_read_byte ms) (ms_writable_byte mi_loaded_segments ms)

def entry_block_top (sp : word) (bytes : List byte) : Int := bv_unsigned sp + (bytes.length : Int)
def entry_page_top (sp : word) (bytes : List byte) : Int := page_round_up_Z (entry_block_top sp bytes)
def entry_slack_len (sp : word) (bytes : List byte) : Nat := (entry_page_top sp bytes - entry_block_top sp bytes).toNat
def entry_slack (sp : word) (bytes : List byte) (slack : word → byte) : List byte :=
  (List.range (entry_slack_len sp bytes)).map fun (k : Nat) => slack (Z_to_bv 64 (entry_block_top sp bytes + (k : Int)))
def entry_stack_image (ph : PhdrInfo) (sp : word) (argv envp : List (List byte)) (uid hwcap : word) (draw : EntryDraw) :
    List byte :=
  let bytes := build_stack_bytes ph sp argv envp uid hwcap draw
  bytes ++ entry_slack sp bytes draw.ed_slack

/-- Run.v's `init_machine_state` (section variables `mi_loaded_segments mi_init_pc mi_phdrs mi_init_sp
    mi_draw`, the ones it uses). -/
def init_machine_state (mi_loaded_segments : List Segment) (mi_init_pc : Nat) (mi_phdrs : PhdrInfo)
    (mi_init_sp : word) (mi_draw : EntryDraw) (argv envp : List (List byte)) (uid hwcap : word) : machine_state :=
  let regs := bvmap_set (2 : reg) mi_init_sp (bvmap_set (10 : reg) (Z_to_bv 64 0) bvmap_empty)
  { ms_regs := regs, ms_fregs := bvmap_empty, ms_pc_val := Z_to_bv 64 (mi_init_pc : Int), ms_svc_pending := none,
    ms_resv := none, ms_fcsr := Z_to_bv 32 0,
    ms_mem :=
      let stk := stack_to_mem mi_init_sp (entry_stack_image mi_phdrs mi_init_sp argv envp uid hwcap mi_draw)
      fun addr =>
        match stk addr with
        | some b => some b
        | none =>
          if decide (bv_unsigned mi_init_sp - stack_max_size ≤ bv_unsigned addr) && decide (bv_unsigned addr < bv_unsigned mi_init_sp)
          then some (Z_to_bv 8 0) else none,
    ms_rom := fun addr =>
      match memory_read mi_loaded_segments addr 1 with
      | some (b :: _) => some b
      | _ => none }

def init_config (mi_loaded_segments : List Segment) (mi_init_pc : Nat) (mi_phdrs : PhdrInfo) (mi_init_sp mi_init_brk
    mi_mmap_base : word) (mi_draw : EntryDraw) (mi_alloc_limit : Int) (inp : ProcInput) : config :=
  mkCfg (init_machine_state mi_loaded_segments mi_init_pc mi_phdrs mi_init_sp mi_draw inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
    (init_model (segments_reserved mi_loaded_segments) mi_init_brk mi_mmap_base mi_init_sp mi_alloc_limit inp)

structure ExecEntry where
  en_sp : word
  en_brk : word
  en_mmap_base : word
  en_draw : EntryDraw

def mkEntry := @ExecEntry.mk

inductive SpuriousFamily where
  | FamAlloc | FamFs | FamFd | FamNet | FamCred | FamIntr
  deriving DecidableEq

structure SpuriousCfg where
  sc_alloc : Bool
  sc_fs : Bool
  sc_fd : Bool
  sc_net : Bool
  sc_cred : Bool
  sc_intr : Bool
  deriving DecidableEq

def mkSpuriousCfg := @SpuriousCfg.mk
def may_fail_cfg : SpuriousCfg := mkSpuriousCfg true true true true true true
def forced_only_cfg : SpuriousCfg := mkSpuriousCfg false false false false false false
def alloc_only_cfg (alloc_may_fail : Bool) : SpuriousCfg := mkSpuriousCfg alloc_may_fail true true true true true

def family_may_fail (cfg : SpuriousCfg) : SpuriousFamily → Bool
  | .FamAlloc => cfg.sc_alloc
  | .FamFs => cfg.sc_fs
  | .FamFd => cfg.sc_fd
  | .FamNet => cfg.sc_net
  | .FamCred => cfg.sc_cred
  | .FamIntr => cfg.sc_intr

def cfg_le (cfg1 cfg2 : SpuriousCfg) : Prop := ∀ f, family_may_fail cfg1 f = true → family_may_fail cfg2 f = true

/-! ### Valid entries and inputs (Run.v, after `run_scfg_budget_refused`) -/

def valid_sp (sp : word) : Prop :=
  sp_window_lo ≤ bv_unsigned sp ∧ bv_unsigned sp ≤ sp_window_hi ∧ Z.modulo (bv_unsigned sp) 16 = 0
def valid_brk (segs : List Segment) (brk : word) : Prop :=
  reserved_top (segments_reserved segs) ≤ bv_unsigned brk ∧
    bv_unsigned brk ≤ reserved_top (segments_reserved segs) + brk_aslr_max ∧ Z.modulo (bv_unsigned brk) page_size = 0
def valid_mmap_base (mbase : word) : Prop :=
  mmap_base_min ≤ bv_unsigned mbase ∧ bv_unsigned mbase ≤ mmap_base_max ∧ Z.modulo (bv_unsigned mbase) page_size = 0
def valid_sp_va (v : VaSize) (sp : word) : Prop :=
  va_sp_window_lo v ≤ bv_unsigned sp ∧ bv_unsigned sp ≤ va_sp_window_hi v ∧ Z.modulo (bv_unsigned sp) 16 = 0
def valid_mmap_base_va (v : VaSize) (mbase : word) : Prop :=
  va_mmap_base_min v ≤ bv_unsigned mbase ∧ bv_unsigned mbase ≤ va_mmap_base_max v ∧ Z.modulo (bv_unsigned mbase) page_size = 0
def total_arg_bytes (args : List (List byte)) : Int := args.foldr (fun a acc => (a.length : Int) + 1 + acc) 0
def valid_argv (argv : List (List byte)) : Prop :=
  (1 ≤ (argv.length : Int) ∧ (argv.length : Int) ≤ 1024) ∧ total_arg_bytes argv ≤ 2097152 ∧
    (∀ a ∈ argv, (a.length : Int) ≤ 131071) ∧ (∀ a ∈ argv, Z_to_bv 8 0 ∉ a) ∧
    (∀ a ∈ argv.tail, path_has_slash a = false ∧ path_eqb a dotdot_path = false)
def valid_envp (envp : List (List byte)) : Prop :=
  (envp.length : Int) ≤ 256 ∧ total_arg_bytes envp ≤ 131072 ∧ (∀ e ∈ envp, (e.length : Int) ≤ 131071) ∧
    (∀ e ∈ envp, Z_to_bv 8 0 ∉ e)
def entry_stack_span (argv envp : List (List byte)) : Int :=
  8 + 8 * (argv.length : Int) + 8 + 8 * (envp.length : Int) + 8 + (auxv_size : Int) + total_arg_bytes argv +
    total_arg_bytes envp + 7 + 16
def entry_stack_fits (sp : word) (argv envp : List (List byte)) : Prop :=
  bv_unsigned sp + entry_stack_span argv envp ≤ sp_window_hi
def entry_stack_fits_va (v : VaSize) (sp : word) (argv envp : List (List byte)) : Prop :=
  bv_unsigned sp + entry_stack_span argv envp ≤ va_sp_window_hi v
def entry_stack_span_max : Int := 2238671
def valid_entry_va (v : VaSize) (img : Image) (en : ExecEntry) (inp : ProcInput) : Prop :=
  match img, en with
  | ⟨segs, _, _⟩, ⟨sp, brk0, mbase, _⟩ =>
    valid_sp_va v sp ∧ valid_brk segs brk0 ∧ valid_mmap_base_va v mbase ∧ entry_stack_fits_va v sp inp.in_argv inp.in_envp
def valid_entry (img : Image) (en : ExecEntry) (inp : ProcInput) : Prop := valid_entry_va inp.in_va_size img en inp
def valid_id (u : word) : Prop := bv_unsigned u < 2 ^ 32 - 1
def valid_creds (inp : ProcInput) : Prop := valid_id inp.in_uid ∧ valid_id inp.in_gid
def valid_nofile (n : word) : Prop := bv_unsigned n ≤ 2 ^ 31 - 64
def valid_sigmask (inp : ProcInput) : Prop := bv_and inp.in_sigmask (Z_to_bv 64 sig_kernel_only_mask) = Z_to_bv 64 0
def valid_hwcap (h : word) : Prop := h = hwcap_rv64gc ∨ h = hwcap_rv64gcv
def valid_urandom (inp : ProcInput) : Prop := stream_infinite inp.in_urandom

/-- The common conjuncts of the `valid_input*` family (Run.v spells each out in full; each definition
    below is that same conjunction, in the same order, with its own hwcap / abort / VA-size clauses). -/
def valid_input (inp : ProcInput) : Prop :=
  valid_argv inp.in_argv ∧ valid_envp inp.in_envp ∧ valid_fs (in_fs inp) ∧ fs_keys_relative inp.in_image_fs ∧
    valid_creds inp ∧ valid_nofile inp.in_nofile ∧ valid_sigmask inp ∧ valid_hwcap inp.in_hwcap ∧
    inp.in_abort_terminal = false ∧ inp.in_va_size = .Sv48 ∧ valid_urandom inp
def valid_input_abort (inp : ProcInput) : Prop :=
  valid_argv inp.in_argv ∧ valid_envp inp.in_envp ∧ valid_fs (in_fs inp) ∧ fs_keys_relative inp.in_image_fs ∧
    valid_creds inp ∧ valid_nofile inp.in_nofile ∧ valid_sigmask inp ∧ valid_hwcap inp.in_hwcap ∧
    inp.in_abort_terminal = true ∧ inp.in_va_size = .Sv48 ∧ valid_urandom inp
def valid_input_either (inp : ProcInput) : Prop :=
  valid_argv inp.in_argv ∧ valid_envp inp.in_envp ∧ valid_fs (in_fs inp) ∧ fs_keys_relative inp.in_image_fs ∧
    valid_creds inp ∧ valid_nofile inp.in_nofile ∧ valid_sigmask inp ∧ valid_hwcap inp.in_hwcap ∧
    inp.in_va_size = .Sv48 ∧ valid_urandom inp
def valid_input_sv39 (inp : ProcInput) : Prop :=
  valid_argv inp.in_argv ∧ valid_envp inp.in_envp ∧ valid_fs (in_fs inp) ∧ fs_keys_relative inp.in_image_fs ∧
    valid_creds inp ∧ valid_nofile inp.in_nofile ∧ valid_sigmask inp ∧ valid_hwcap inp.in_hwcap ∧
    inp.in_abort_terminal = false ∧ inp.in_va_size = .Sv39 ∧ valid_urandom inp
def valid_input_sv57 (inp : ProcInput) : Prop :=
  valid_argv inp.in_argv ∧ valid_envp inp.in_envp ∧ valid_fs (in_fs inp) ∧ fs_keys_relative inp.in_image_fs ∧
    valid_creds inp ∧ valid_nofile inp.in_nofile ∧ valid_sigmask inp ∧ valid_hwcap inp.in_hwcap ∧
    inp.in_abort_terminal = false ∧ inp.in_va_size = .Sv57 ∧ valid_urandom inp
def valid_input_va_any (inp : ProcInput) : Prop :=
  valid_argv inp.in_argv ∧ valid_envp inp.in_envp ∧ valid_fs (in_fs inp) ∧ fs_keys_relative inp.in_image_fs ∧
    valid_creds inp ∧ valid_nofile inp.in_nofile ∧ valid_sigmask inp ∧ valid_hwcap inp.in_hwcap ∧
    inp.in_abort_terminal = false ∧ valid_urandom inp
def valid_input_hwcap_rv64gc (inp : ProcInput) : Prop :=
  valid_argv inp.in_argv ∧ valid_envp inp.in_envp ∧ valid_fs (in_fs inp) ∧ fs_keys_relative inp.in_image_fs ∧
    valid_creds inp ∧ valid_nofile inp.in_nofile ∧ valid_sigmask inp ∧ inp.in_hwcap = hwcap_rv64gc ∧
    inp.in_abort_terminal = false ∧ inp.in_va_size = .Sv48 ∧ valid_urandom inp
def valid_input_hwcap_rv64gcv (inp : ProcInput) : Prop :=
  valid_argv inp.in_argv ∧ valid_envp inp.in_envp ∧ valid_fs (in_fs inp) ∧ fs_keys_relative inp.in_image_fs ∧
    valid_creds inp ∧ valid_nofile inp.in_nofile ∧ valid_sigmask inp ∧ inp.in_hwcap = hwcap_rv64gcv ∧
    inp.in_abort_terminal = false ∧ inp.in_va_size = .Sv48 ∧ valid_urandom inp
def valid_input_abort_hwcap_rv64gc (inp : ProcInput) : Prop :=
  valid_argv inp.in_argv ∧ valid_envp inp.in_envp ∧ valid_fs (in_fs inp) ∧ fs_keys_relative inp.in_image_fs ∧
    valid_creds inp ∧ valid_nofile inp.in_nofile ∧ valid_sigmask inp ∧ inp.in_hwcap = hwcap_rv64gc ∧
    inp.in_abort_terminal = true ∧ inp.in_va_size = .Sv48 ∧ valid_urandom inp
def valid_input_abort_hwcap_rv64gcv (inp : ProcInput) : Prop :=
  valid_argv inp.in_argv ∧ valid_envp inp.in_envp ∧ valid_fs (in_fs inp) ∧ fs_keys_relative inp.in_image_fs ∧
    valid_creds inp ∧ valid_nofile inp.in_nofile ∧ valid_sigmask inp ∧ inp.in_hwcap = hwcap_rv64gcv ∧
    inp.in_abort_terminal = true ∧ inp.in_va_size = .Sv48 ∧ valid_urandom inp

end LPS
