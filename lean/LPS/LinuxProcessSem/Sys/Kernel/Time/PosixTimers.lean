import LPS.LinuxProcessSem.Sys.Uapi
import LPS.LinuxProcessSem.Sys.Uaccess

/-!
# LPS `theories/LinuxProcessSem/Sys/Kernel/Time/PosixTimers.v` (f1006fe8): clock_gettime

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/Sys/Kernel/Time/PosixTimers.v` at f1006fe8 (TRUST BOUNDARY there). Definitions; lemmas
when a proof needs them.
-/

namespace LPS

def timespec_ok_b (bs : List byte) (prev : word) : Bool :=
  bs.length == 16 && decide (tv_frac_of bs < 1000000000) && decide (bv_unsigned prev ≤ timespec_ns bs) &&
    decide (timespec_ns bs < CLOCK_NS_ENVELOPE)
def realtime_ok_b (bs : List byte) : Bool :=
  bs.length == 16 && decide (tv_frac_of bs < 1000000000) && decide (timespec_ns bs < CLOCK_NS_ENVELOPE)
def cputime_ok_b (bs : List byte) : Bool :=
  bs.length == 16 && decide (tv_frac_of bs < 1000000000) && decide (-CLOCK_NS_ENVELOPE ≤ timespec_ns_signed bs) &&
    decide (timespec_ns_signed bs < CLOCK_NS_ENVELOPE)
def clockid_percall_b (clkid : word) : Bool :=
  bv_unsigned clkid == CLOCK_REALTIME || bv_unsigned clkid == CLOCK_MONOTONIC_RAW ||
    bv_unsigned clkid == CLOCK_REALTIME_COARSE || bv_unsigned clkid == CLOCK_MONOTONIC_COARSE ||
    bv_unsigned clkid == CLOCK_BOOTTIME
def clock_gettime_spec (clkid tp : word) : Sys SyscallEffect :=
  if clockid_percall_b clkid then do
    let i ← input
    match read_bytes_map i.in_wmem tp (Z_to_bv 64 16) with
    | none => unmodeled
    | some _ => do
      let bs ← choose fun bs : List byte => realtime_ok_b bs = true
      Sys.pure (mkEffect (Z_to_bv 64 0) [(tp, bs)] [])
  else if bv_unsigned clkid == CLOCK_PROCESS_CPUTIME_ID then do
    let i ← input
    match read_bytes_map i.in_wmem tp (Z_to_bv 64 16) with
    | none => unmodeled
    | some _ => do
      let bs ← choose fun bs : List byte => cputime_ok_b bs = true
      Sys.pure (mkEffect (Z_to_bv 64 0) [(tp, bs)] [])
  else if !(bv_unsigned clkid == CLOCK_MONOTONIC) then unmodeled
  else do
    let m ← get_model
    if !(decide (bv_unsigned (m_clock m) < CLOCK_NS_ENVELOPE)) then unmodeled
    else do
      let i ← input
      match read_bytes_map i.in_wmem tp (Z_to_bv 64 16) with
      | none => unmodeled
      | some _ => do
        let bs ← choose fun bs : List byte => timespec_ok_b bs (m_clock m) = true
        set_clock (Z_to_bv 64 (timespec_ns bs))
        Sys.pure (mkEffect (Z_to_bv 64 0) [(tp, bs)] [])

end LPS
