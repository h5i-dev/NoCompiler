import LPS.LinuxProcessSem.Sys.Uapi
import LPS.LinuxProcessSem.Sys.Uaccess

/-!
# LPS `theories/LinuxProcessSem/Sys/Kernel/Groups.v` (f1006fe8): getgroups, setgroups

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/Sys/Kernel/Groups.v` at f1006fe8 (TRUST BOUNDARY there). Definitions; lemmas
when a proof needs them.
-/

namespace LPS

def getgroups_spec (gidsetsize : word) : Sys SyscallEffect :=
  let n := sint32 gidsetsize
  if n < 0 then err_ret EINVAL
  else do
    let m ← get_model
    let ng : Int := (m_creds m).cr_groups.length
    if NGROUPS_MAX < ng then unmodeled
    else if n == 0 then ret_only (Z_to_bv 64 ng)
    else if n < ng then err_ret EINVAL
    else if ng == 0 then ret_only (Z_to_bv 64 0)
    else unmodeled
def setgroups_spec : Sys SyscallEffect := do
  let m ← get_model
  if creds_privileged (m_creds m) then unmodeled else err_ret EPERM

end LPS
