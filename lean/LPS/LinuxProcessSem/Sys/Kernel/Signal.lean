import LPS.LinuxProcessSem.Sys.Uapi
import LPS.LinuxProcessSem.Sys.Uaccess

/-!
# LPS `theories/LinuxProcessSem/Sys/Kernel/Signal.v` (f1006fe8): rt_sigaction, rt_sigprocmask, sigaltstack, tkill, tgkill

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/Sys/Kernel/Signal.v` at f1006fe8 (TRUST BOUNDARY there). Definitions; lemmas
when a proof needs them.
-/

namespace LPS

def sig32 (sig : word) : word := abi_low32 sig
def sigaction_accepted (sig : word) : Bool := let s := bv_unsigned sig; s == 2 || s == 15
def sig_valid (sig : word) : Bool := let s := bv_unsigned sig; decide (1 ≤ s) && decide (s ≤ 64)
def sig_kernel_only (sig : word) : Bool := let s := bv_unsigned sig; s == 9 || s == 19
def sa_flags_accepted : Int := 0xC8000807
def sa_flags_ok (fl : word) : Bool := Z.ldiff (bv_unsigned fl) sa_flags_accepted == 0
def sigaction_flags (mp : word → Option byte) (act : word) : Option word :=
  if (readable_bytes mp act (Z_to_bv 64 24)).length == 24 then read_u64 mp (bv_add act (Z_to_bv 64 8)) else none
def rt_sigaction_spec (sig act oact ss : word) : Sys SyscallEffect :=
  if !(bv_eqb ss (Z_to_bv 64 8)) then err_ret EINVAL
  else if !(w_is0 oact) then unmodeled
  else if w_is0 act then (if sig_valid sig then ret_only (Z_to_bv 64 0) else err_ret EINVAL)
  else do
    let i ← input
    match sigaction_flags i.in_mem act with
    | none => err_ret EFAULT
    | some fl =>
      if !(sig_valid sig) then err_ret EINVAL
      else if sig_kernel_only sig then err_ret EINVAL
      else if !(sa_flags_ok fl) then unmodeled
      else if sigaction_accepted sig then ret_only (Z_to_bv 64 0)
      else unmodeled
def how_valid (how : word) : Bool := let h := bv_unsigned how; h == SIG_BLOCK || h == SIG_UNBLOCK || h == SIG_SETMASK
def sigset_at (mp : word → Option byte) (p : word) : Option word :=
  match read_bytes_map mp p (Z_to_bv 64 NSIG_BYTES) with
  | some bs => some (le_bytes_to_word bs)
  | none => none
def sigmask_strip (w : word) : word := bv_and w (Z_to_bv 64 (Z.lxor (Z.ones 64) sig_kernel_only_mask))
def sigmask_apply (how old new : word) : word :=
  if bv_unsigned how == SIG_BLOCK then bv_or old new
  else if bv_unsigned how == SIG_UNBLOCK then bv_and old (bv_not new)
  else new
def mask_launchable (w : word) : Prop := bv_and w (Z_to_bv 64 sig_kernel_only_mask) = Z_to_bv 64 0
def write_oset (oset old : word) : Sys SyscallEffect :=
  if !(access_okb oset NSIG_BYTES) then err_ret EFAULT
  else do
    let i ← input
    match read_bytes_map i.in_wmem oset (Z_to_bv 64 NSIG_BYTES) with
    | some _ => Sys.pure (mkEffect (Z_to_bv 64 0) [(oset, Z_to_le_bytes NSIG_BYTES.toNat (bv_unsigned old))] [])
    | none => unmodeled
def sigabrt_blocked (mask : word) : Bool := !(w_is0 (bv_and mask (Z_to_bv 64 sigabrt_mask)))
def sigmask_deliver_model (new : word) (m : Model) : Model :=
  if m_sigabrt_pending m && !(sigabrt_blocked new) then with_killed (Z_to_bv 64 SIGABRT) (with_sigmask new m)
  else with_sigmask new m
def set_sigmask_deliver (new : word) : Sys Unit := modify (sigmask_deliver_model new)
def rt_sigprocmask_spec (how nset oset ss : word) : Sys SyscallEffect :=
  if !(bv_eqb ss (Z_to_bv 64 NSIG_BYTES)) then err_ret EINVAL
  else do
    let m ← get_model
    let old := m_sigmask m
    if w_is0 nset then (if w_is0 oset then ret_only (Z_to_bv 64 0) else write_oset oset old)
    else do
      let i ← input
      match sigset_at i.in_mem nset with
      | none => err_ret EFAULT
      | some raw =>
        record_copyins [(nset, NSIG_BYTES.toNat)]
          (if !(how_valid how) then err_ret EINVAL
           else do
             set_sigmask_deliver (sigmask_apply how old (sigmask_strip raw))
             if w_is0 oset then ret_only (Z_to_bv 64 0) else write_oset oset old)
def ss_sp_of (bs : List byte) : word := le_bytes_to_word (bs.take 8)
def ss_flags_of (bs : List byte) : word := le_bytes_to_word ((bs.drop SS_FLAGS_OFF.toNat).take 4)
def ss_size_of (bs : List byte) : word := le_bytes_to_word (bs.drop SS_SIZE_OFF.toNat)
def ss_mode (fl : word) : Int := Z.ldiff (bv_unsigned fl) SS_AUTODISARM
def ss_mode_ok (fl : word) : Bool := let md := ss_mode fl; md == 0 || md == SS_ONSTACK || md == SS_DISABLE
def ss_disabling (fl : word) : Bool := ss_mode fl == SS_DISABLE
def sigaltstack_at (mp : word → Option byte) (uss : word) : Option (List byte) :=
  read_bytes_map mp uss (Z_to_bv 64 SIGALTSTACK_BYTES)
def sigaltstack_spec (uss uoss : word) : Sys SyscallEffect := do
  let m ← get_model
  if m_sigaltstack_installed m then unmodeled
  else if !(w_is0 uoss) then unmodeled
  else if w_is0 uss then ret_only (Z_to_bv 64 0)
  else do
    let i ← input
    match sigaltstack_at i.in_mem uss with
    | none => err_ret EFAULT
    | some bs =>
      let fl := ss_flags_of bs
      if !(ss_mode_ok fl) then err_ret EINVAL
      else if ss_disabling fl then ret_only (Z_to_bv 64 0)
      else if w_is0 (ss_sp_of bs) && w_is0 (ss_size_of bs) then unmodeled
      else if bv_unsigned (ss_size_of bs) < MINSIGSTKSZ then err_ret ENOMEM
      else do set_sigaltstack_installed; ret_only (Z_to_bv 64 0)
def pid_positive (p : word) : Bool := let v := bv_unsigned p; decide (1 ≤ v) && decide (v < 2 ^ 31)
def tkill_sig_valid (sig : word) : Bool := decide (bv_unsigned sig ≤ 64)
def send_sigabrt : Sys SyscallEffect := do
  let m ← get_model
  (if sigabrt_blocked (m_sigmask m) then set_sigabrt_pending else set_killed (Z_to_bv 64 SIGABRT))
  ret_only (Z_to_bv 64 0)
def tkill_self (pid sig : word) : Sys SyscallEffect := do
  let m ← get_model
  if !(m_abort_terminal m) then unmodeled
  else
    match m_tid m with
    | none => unmodeled
    | some t =>
      if !(bv_eqb pid t) then unmodeled
      else if !(tkill_sig_valid sig) then err_ret EINVAL
      else if bv_eqb sig (Z_to_bv 64 SIGABRT) then send_sigabrt
      else unmodeled
def tkill_spec (pid sig : word) : Sys SyscallEffect := do
  let m ← get_model
  if !(m_abort_terminal m) then unmodeled
  else if !(pid_positive pid) then err_ret EINVAL
  else tkill_self pid sig
def tgkill_spec (tgid pid sig : word) : Sys SyscallEffect := do
  let m ← get_model
  if !(m_abort_terminal m) then unmodeled
  else if !(pid_positive pid && pid_positive tgid) then err_ret EINVAL
  else
    match m_tid m with
    | none => unmodeled
    | some t =>
      if !(bv_eqb pid t) then unmodeled
      else if !(bv_eqb tgid t) then err_ret ESRCH
      else tkill_self pid sig

end LPS
