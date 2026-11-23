import LPS.LinuxProcessSem.Sys.Uapi

/-!
# LPS `theories/LinuxProcessSem/Sys/Kernel/Exit.v` (f1006fe8): exit, wait4

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/Sys/Kernel/Exit.v` at f1006fe8 (TRUST BOUNDARY there). Definitions; lemmas
when a proof needs them.
-/

namespace LPS

def exit_spec (code : word) : Sys SyscallEffect := do
  set_halted (bv_and code (Z_to_bv 64 255)); ret_only (Z_to_bv 64 0)
def WAIT_ANY32 : Int := 2 ^ 32 - 1
def wait4_spec (upid _stat_addr options rusage : word) : Sys SyscallEffect :=
  if !(bv_unsigned upid == WAIT_ANY32) then unmodeled
  else if !(bv_unsigned options == WNOHANG) then unmodeled
  else if !(w_is0 rusage) then unmodeled
  else do
    let m ← get_model
    if m_has_children m then unmodeled else err_ret ECHILD

end LPS
