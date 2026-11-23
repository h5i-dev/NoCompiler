import LPS.LinuxProcessSem.Sys.Syscall

/-!
# LPS `theories/LinuxProcessSem/Sys/Fs/Sync.v` (f1006fe8): fsync

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/Sys/Fs/Sync.v` at f1006fe8 (TRUST BOUNDARY there). Definitions; lemmas
when a proof needs them.
-/

namespace LPS

def fsync_spec (fd : word) : Sys SyscallEffect := do
  let m ← get_model
  match fd_lookup (m_fds m) fd with
  | none => err_ret EBADF
  | some (.FdChannel _) => err_ret EINVAL
  | some (.FdSocket _) => err_ret EINVAL
  | some (.FdPipe _ _) => err_ret EINVAL
  | some (.FdDevNull _ _) => err_ret EINVAL
  | some .FdUrandom => err_ret EINVAL
  | some (.FdFile _ _) => ret_only (Z_to_bv 64 0)
  | some (.FdFileW _ _) => ret_only (Z_to_bv 64 0)
  | some (.FdFileA _ _) => ret_only (Z_to_bv 64 0)
  | some (.FdFileRW _ _) => ret_only (Z_to_bv 64 0)
  | some .FdDir => ret_only (Z_to_bv 64 0)

end LPS
