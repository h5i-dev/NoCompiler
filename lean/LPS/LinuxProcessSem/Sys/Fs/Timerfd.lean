import LPS.LinuxProcessSem.Sys.Uapi

/-!
# LPS `theories/LinuxProcessSem/Sys/Fs/Timerfd.v` (f1006fe8): timerfd_create

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/Sys/Fs/Timerfd.v` at f1006fe8 (TRUST BOUNDARY there). Definitions; lemmas
when a proof needs them.
-/

namespace LPS

def timerfd_create_einval_b (clkid flags : word) : Bool :=
  !(Z.ldiff (bv_unsigned flags) TFD_CREATE_FLAGS == 0) ||
    !(bv_unsigned clkid == CLOCK_REALTIME || (bv_unsigned clkid == CLOCK_MONOTONIC ||
      (bv_unsigned clkid == CLOCK_BOOTTIME || (bv_unsigned clkid == CLOCK_REALTIME_ALARM ||
        bv_unsigned clkid == CLOCK_BOOTTIME_ALARM))))
def timerfd_create_spec (clkid flags : word) : Sys SyscallEffect :=
  if timerfd_create_einval_b clkid flags then err_ret EINVAL else unmodeled

end LPS
