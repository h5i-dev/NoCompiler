import LPS.LinuxProcessSem.Sys.Uapi

/-!
# LPS `theories/LinuxProcessSem/Sys/Fs/Readdir.v` (f1006fe8): getdents64

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/Sys/Fs/Readdir.v` at f1006fe8 (TRUST BOUNDARY there). Definitions; lemmas
when a proof needs them.
-/

namespace LPS

def getdents64_errnos : List Int := [ENOENT]
def dirent64_min_reclen : Int := 24
def getdents64_ctx_count (count : word) : Int := sint32 count
def getdents64_no_room (count : word) : Bool := decide (getdents64_ctx_count count < dirent64_min_reclen)
def getdents64_spec (fd count : word) : Sys SyscallEffect := do
  let m ← get_model
  match fd_lookup (m_fds m) fd with
  | none => err_ret EBADF
  | some .FdDir =>
    if getdents64_no_room count then alt (do let e ← errno_from getdents64_errnos; err_ret e) (err_ret EINVAL)
    else unmodeled
  | some _ => err_ret ENOTDIR

end LPS
