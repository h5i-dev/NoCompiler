import LPS.LinuxProcessSem.Sys.Uapi
import LPS.LinuxProcessSem.Sys.Uaccess
import LPS.LinuxProcessSem.Sys.Fs.File

/-!
# LPS `theories/LinuxProcessSem/Sys/Fs/Pipe.v` (f1006fe8): pipe2

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/Sys/Fs/Pipe.v` at f1006fe8 (TRUST BOUNDARY there). Definitions; lemmas
when a proof needs them.
-/

namespace LPS

def pipe2_flags_mask : Int := O_CLOEXEC + O_NONBLOCK + O_DIRECT + O_EXCL
def pipe2_errnos : List Int := [EMFILE, ENFILE, ENOMEM]
def pipe2_spec (fildes flags : word) : Sys SyscallEffect := do
  let i ← input
  let m ← get_model
  if !(Z.ldiff (bv_unsigned flags) pipe2_flags_mask == 0) then err_ret EINVAL
  else if !(w_is0 flags) then unmodeled
  else
    let id := pipe_new_id (m_pipes m)
    match pipe_lookup (m_pipes m) id with
    | some _ => unmodeled
    | none =>
      let injected : Sys SyscallEffect := do let e ← errno_from pipe2_errnos; err_ret e
      if !(access_okb fildes 8) then alt injected (err_ret EFAULT)
      else match read_bytes_map i.in_wmem fildes (Z_to_bv 64 8) with
        | some _ =>
          alt injected (do
            let fdr ← lowest_fd (m_fds m)
            let fds1 := fd_insert (m_fds m) fdr (.FdPipe id false)
            let fdw ← lowest_fd fds1
            set_fds (fd_insert fds1 fdw (.FdPipe id true))
            set_pipes (pipe_insert (m_pipes m) id ([], 0))
            Sys.pure (mkEffect (Z_to_bv 64 0) [(fildes, pipe_fd_bytes fdr fdw)] []))
        | none =>
          match read_bytes_map i.in_wmem fildes (Z_to_bv 64 1) with
          | none => alt injected (err_ret EFAULT)
          | some _ => unmodeled

end LPS
