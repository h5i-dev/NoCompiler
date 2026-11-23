import LPS.LinuxProcessSem.Sys.Uapi

/-!
# LPS `theories/LinuxProcessSem/Sys/Fs/Locks.v` (f1006fe8): flock

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/Sys/Fs/Locks.v` at f1006fe8 (TRUST BOUNDARY there). Definitions; lemmas
when a proof needs them.
-/

namespace LPS

def flock_mand_b (cmd : word) : Bool := !(Z.land (bv_unsigned cmd) LOCK_MAND == 0)
def flock_base (cmd : word) : Int := Z.ldiff (bv_unsigned cmd) LOCK_NB
def flock_cmd_ok_b (cmd : word) : Bool := let b := flock_base cmd; b == LOCK_SH || b == LOCK_EX || b == LOCK_UN
def flock_unlock_b (cmd : word) : Bool := flock_base cmd == LOCK_UN
def path_openers : List (word × FdEntry) → path → Nat
  | [], _ => 0
  | (_, .FdFile q _) :: r, p => (if path_eqb q p then 1 else 0) + path_openers r p
  | (_, .FdFileW q _) :: r, p => (if path_eqb q p then 1 else 0) + path_openers r p
  | (_, .FdFileA q _) :: r, p => (if path_eqb q p then 1 else 0) + path_openers r p
  | (_, .FdFileRW q _) :: r, p => (if path_eqb q p then 1 else 0) + path_openers r p
  | (_, _) :: r, p => path_openers r p
def flock_sole_opener (fds : List (word × FdEntry)) (p : path) : Bool := path_openers fds p == 1
def flock_spec (fd cmd : word) : Sys SyscallEffect := do
  let m ← get_model
  if flock_mand_b cmd then ret_only (Z_to_bv 64 0)
  else if !(flock_cmd_ok_b cmd) then err_ret EINVAL
  else
    match fd_lookup (m_fds m) fd with
    | none => err_ret EBADF
    | some e =>
      if flock_unlock_b cmd then ret_only (Z_to_bv 64 0)
      else
        match e with
        | .FdFile p _ | .FdFileW p _ | .FdFileA p _ | .FdFileRW p _ =>
          if flock_sole_opener (m_fds m) p then ret_only (Z_to_bv 64 0) else unmodeled
        | _ => unmodeled

end LPS
