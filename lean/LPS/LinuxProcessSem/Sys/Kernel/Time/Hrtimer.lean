import LPS.LinuxProcessSem.Sys.Uapi
import LPS.LinuxProcessSem.Sys.Uaccess

/-!
# LPS `theories/LinuxProcessSem/Sys/Kernel/Time/Hrtimer.v` (f1006fe8): nanosleep

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/Sys/Kernel/Time/Hrtimer.v` at f1006fe8 (TRUST BOUNDARY there). Definitions; lemmas
when a proof needs them.
-/

namespace LPS

def timespec_valid_b (bs : List byte) : Bool := decide (tv_sec_of bs < 2 ^ 63) && decide (tv_frac_of bs < 1000000000)
def nanosleep_rem_ok_b (bs : List byte) : Bool :=
  bs.length == 16 && decide (tv_frac_of bs < 1000000000) && decide (0 < timespec_ns bs) &&
    decide (timespec_ns bs < CLOCK_NS_ENVELOPE)
def nanosleep_clock (prev : word) (req rem : List byte) : word :=
  Z_to_bv 64 (max (bv_unsigned prev) (min (bv_unsigned prev + timespec_ktime req) KTIME_MAX - timespec_ns rem))
def nanosleep_spec (rqtp rmtp : word) : Sys SyscallEffect := do
  let i ← input
  match read_bytes_map i.in_mem rqtp (Z_to_bv 64 16) with
  | none => unmodeled
  | some req =>
    record_copyins [(rqtp, 16)]
      (if !(timespec_valid_b req) then err_ret EINVAL
       else do
         let m ← get_model
         let slept : Sys SyscallEffect := do set_clock (nanosleep_clock (m_clock m) req []); ret_only (Z_to_bv 64 0)
         if w_is0 rmtp then alt slept (err_ret EINTR)
         else
           match read_bytes_map i.in_wmem rmtp (Z_to_bv 64 16) with
           | none => unmodeled
           | some _ =>
             alt slept (do
               let rem ← choose fun rem : List byte => nanosleep_rem_ok_b rem = true
               set_clock (nanosleep_clock (m_clock m) req rem)
               Sys.pure (mkEffect (errno_ret EINTR) [(rmtp, rem)] [])))

end LPS
