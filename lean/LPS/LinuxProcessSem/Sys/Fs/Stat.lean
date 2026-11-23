import LPS.LinuxProcessSem.Sys.Uapi

/-!
# LPS `theories/LinuxProcessSem/Sys/Fs/Stat.v` (f1006fe8): readlinkat, newfstatat, fstat

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/Sys/Fs/Stat.v` at f1006fe8 (TRUST BOUNDARY there). Definitions; lemmas
when a proof needs them.
-/

namespace LPS

def readlinkat_spec (dirfd : word) : Sys SyscallEffect := if !(bv_eqb dirfd AT_FDCWD32) then unmodeled else err_ret EINVAL
def modeled_statat_flags (flag : word) : Bool := let fl := bv_unsigned flag; fl == 0 || fl == AT_SYMLINK_NOFOLLOW
def newfstatat_core_spec (dirfd pathp flag : word) : Sys SyscallEffect := do
  let i ← input
  let m ← get_model
  if !(modeled_statat_flags flag) then unmodeled
  else
    match read_cstr i.in_mem pathp with
    | .CstrTooLong => err_ret ENAMETOOLONG
    | .CstrFault => err_ret EFAULT
    | .CstrOk p =>
      if path_eqb p [] then err_ret ENOENT
      else if !(bv_eqb dirfd AT_FDCWD32) then unmodeled
      else if path_eqb p dot_path then unmodeled
      else match fs_lookup (m_fs m) p with
        | none => err_ret ENOENT
        | some _ => unmodeled
def newfstatat_spec (dirfd pathp flag : word) : Sys SyscallEffect := do
  let i ← input
  record_copyins [(pathp, cstr_access_len_aux i.in_mem pathp path_max)] (newfstatat_core_spec dirfd pathp flag)
def fstat_file_spec (p : path) (statbuf : word) : Sys SyscallEffect := do
  let i ← input
  let m ← get_model
  match fs_lookup (m_fs m) p with
  | none => unmodeled
  | some data =>
    if !(access_okb statbuf STAT_SIZE) then err_ret EFAULT
    else
      match read_bytes_map i.in_wmem statbuf (Z_to_bv 64 STAT_SIZE) with
      | none => unmodeled
      | some _ =>
        match statpin_lookup (m_statpins m) p with
        | some b0 =>
          if !(stat_buf_wf b0) then unmodeled
          else do
            let bs ← choose fun bs : List byte =>
              stat_buf_wf bs = true ∧ stat_size_ok data.length bs = true ∧ stat_stable_eqb bs b0 = true
            Sys.pure (mkEffect (Z_to_bv 64 0) [(statbuf, bs)] [])
        | none => do
          let bs ← choose fun bs : List byte => stat_buf_wf bs = true ∧ stat_size_ok data.length bs = true
          set_statpin p bs
          Sys.pure (mkEffect (Z_to_bv 64 0) [(statbuf, bs)] [])
def fstat_chrdev_spec (p : path) (ok : List byte → Bool) (statbuf : word) : Sys SyscallEffect := do
  let i ← input
  let m ← get_model
  if !(access_okb statbuf STAT_SIZE) then err_ret EFAULT
  else
    match read_bytes_map i.in_wmem statbuf (Z_to_bv 64 STAT_SIZE) with
    | none => unmodeled
    | some _ =>
      match statpin_lookup (m_statpins m) p with
      | some b0 =>
        if !(stat_buf_wf b0 && ok b0) then unmodeled
        else do
          let bs ← choose fun bs : List byte => stat_buf_wf bs = true ∧ ok bs = true ∧ stat_stable_eqb bs b0 = true
          Sys.pure (mkEffect (Z_to_bv 64 0) [(statbuf, bs)] [])
      | none => do
        let bs ← choose fun bs : List byte => stat_buf_wf bs = true ∧ ok bs = true
        set_statpin p bs
        Sys.pure (mkEffect (Z_to_bv 64 0) [(statbuf, bs)] [])
def fstat_devnull_spec (statbuf : word) : Sys SyscallEffect := fstat_chrdev_spec devnull_path stat_devnull_ok statbuf
def fstat_urandom_spec (statbuf : word) : Sys SyscallEffect := fstat_chrdev_spec urandom_path stat_urandom_ok statbuf
def fstat_spec (fd statbuf : word) : Sys SyscallEffect := do
  let m ← get_model
  match fd_lookup (m_fds m) fd with
  | none => err_ret EBADF
  | some (.FdChannel _) => unmodeled
  | some (.FdFile p _) => fstat_file_spec p statbuf
  | some (.FdFileW p _) => fstat_file_spec p statbuf
  | some (.FdFileA p _) => fstat_file_spec p statbuf
  | some (.FdFileRW p _) => fstat_file_spec p statbuf
  | some .FdDir => unmodeled
  | some (.FdSocket _) => unmodeled
  | some (.FdPipe _ _) => unmodeled
  | some (.FdDevNull _ _) => fstat_devnull_spec statbuf
  | some .FdUrandom => fstat_urandom_spec statbuf

end LPS
