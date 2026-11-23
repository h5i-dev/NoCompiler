import LPS.LinuxProcessSem.Sys.Uapi

/-!
# LPS `theories/LinuxProcessSem/Sys/Fs/File.v` (f1006fe8): dup, dup3

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/Sys/Fs/File.v` at f1006fe8 (TRUST BOUNDARY there).
-/

namespace LPS

def lowest_fd (fds : List (word × FdEntry)) : Sys word :=
  choose fun fd => fd_lookup fds fd = none ∧ fd = alloc_fd fds

def dup_modeled_entry : FdEntry → Bool
  | .FdChannel _ | .FdDir => true
  | .FdFile _ _ | .FdFileW _ _ | .FdSocket _ => false
  | .FdFileA _ _ => false
  | .FdFileRW _ _ => false
  | .FdPipe _ _ => false
  | .FdDevNull _ _ => true
  | .FdUrandom => true

def dup_errnos : List Int := [ENOMEM, EMFILE]

def dup_spec (oldfd : word) : Sys SyscallEffect := do
  let m ← get_model
  match fd_lookup (m_fds m) oldfd with
  | none => err_ret EBADF
  | some e =>
    if !(dup_modeled_entry e) then unmodeled
    else
      alt (do let er ← errno_from dup_errnos; err_ret er)
        (do let fd ← lowest_fd (m_fds m); set_fds (fd_insert (m_fds m) fd e); ret_only fd)

def dup3_flags_ok (flags : word) : Bool := Z.ldiff (bv_unsigned (flag32 flags)) O_CLOEXEC == 0
def dup3_newfd_under_limit (newfd : word) (m : Model) : Bool := decide (bv_unsigned newfd < bv_unsigned (m_nofile m))

def dup3_spec (oldfd newfd flags : word) : Sys SyscallEffect := do
  let m ← get_model
  if !(dup3_flags_ok flags) then err_ret EINVAL
  else if bv_eqb oldfd newfd then err_ret EINVAL
  else if !(dup3_newfd_under_limit newfd m) then err_ret EBADF
  else
    match fd_lookup (m_fds m) oldfd with
    | none => err_ret EBADF
    | some e =>
      if !(dup_modeled_entry e) then unmodeled
      else
        match fd_lookup (m_fds m) newfd with
        | none =>
          if bv_unsigned newfd < NR_OPEN_DEFAULT then do set_fds (fd_insert (m_fds m) newfd e); ret_only newfd
          else unmodeled
        | some _ => do set_fds (fd_insert (m_fds m) newfd e); ret_only newfd

end LPS
