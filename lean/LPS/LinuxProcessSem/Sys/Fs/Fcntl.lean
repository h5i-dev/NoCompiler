import LPS.LinuxProcessSem.Sys.Fs.Open

/-!
# LPS `theories/LinuxProcessSem/Sys/Fs/Fcntl.v` (f1006fe8): fcntl

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/Sys/Fs/Fcntl.v` at f1006fe8 (TRUST BOUNDARY there). Every definition,
same names, argument order and case structure. The three closed `Remark`s (Rocq `vm_compute`) are
ported, proved by `decide`.
-/

namespace LPS

def setfl_acted_on : Int :=
  O_APPEND + O_NONBLOCK + FASYNC + O_DIRECT + O_NOATIME

def setfl_noop_on (e : FdEntry) (arg : word) : Bool :=
  match e with
  | .FdChannel _ => false
  | .FdFile _ _ | .FdFileW _ _ | .FdFileRW _ _ | .FdDir | .FdSocket _ =>
      Z.land (bv_unsigned arg) setfl_acted_on == 0
  | .FdFileA _ _ => false
  | .FdDevNull _ _ => false
  | .FdUrandom => false
  | .FdPipe _ _ => false

-- modeled_open_flags_clear_of_setfl (Fcntl.v:288-304): ported when a proof needs it.

theorem open_ignored_flags_clear_of_setfl_current :
    Z.land open_ignored_flags (O_APPEND + FASYNC) = 0 := by decide

theorem setfl_acted_on_fits_32 : setfl_acted_on < 2 ^ 32 := by decide

def socket_f_flags : Int := O_RDWR

theorem socket_f_flags_clear_of_setfl :
    Z.land socket_f_flags setfl_acted_on = 0 := by decide

def getfl_f_flags (e : FdEntry) : Option word :=
  match e with
  | .FdSocket _ => some (Z_to_bv 64 socket_f_flags)
  | .FdChannel _ | .FdFile _ _ | .FdFileW _ _ | .FdDir => none
  | .FdFileRW _ _ => none
  | .FdFileA _ _ => none
  | .FdDevNull _ _ => none
  | .FdUrandom => none
  | .FdPipe _ _ => none

def fcntl_spec (fd cmd arg : word) : Sys SyscallEffect := do
  let m ← get_model
  match fd_lookup (m_fds m) fd with
  | none => err_ret EBADF
  | some e =>
      if bv_eqb cmd F_SETFD then ret_only (Z_to_bv 64 0)
      else if bv_eqb cmd F_SETFL && setfl_noop_on e arg
      then ret_only (Z_to_bv 64 0)
      else if bv_eqb cmd F_GETFL then
        match getfl_f_flags e with
        | some fl => ret_only fl
        | none => unmodeled
      else unmodeled

end LPS
