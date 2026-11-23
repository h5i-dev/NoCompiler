import LPS.LinuxProcessSem.Sys.Uapi
import LPS.LinuxProcessSem.Sys.Uaccess

/-!
# LPS `theories/LinuxProcessSem/Sys/Kernel/Time/Time.v` (f1006fe8): gettimeofday

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/Sys/Kernel/Time/Time.v` at f1006fe8 (TRUST BOUNDARY there). Definitions; lemmas
when a proof needs them.
-/

namespace LPS

def timeval_ok_b (bs : List byte) : Bool :=
  bs.length == 16 && decide (tv_frac_of bs < 1000000) && decide (tv_sec_of bs < KTIME_SEC_MAX)
def gettimeofday_spec (tv tz : word) : Sys SyscallEffect :=
  if !(w_is0 tz) then unmodeled
  else if w_is0 tv then unmodeled
  else do
    let i ← input
    match copy_bytes_map i.in_wmem tv 16 with
    | none => if !(access_okb tv 8) then err_ret EFAULT else unmodeled
    | some _ => do
      let bs ← choose fun bs : List byte => timeval_ok_b bs = true
      Sys.pure (mkEffect (Z_to_bv 64 0) [(tv, bs)] [])

end LPS
