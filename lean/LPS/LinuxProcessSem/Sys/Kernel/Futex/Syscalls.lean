import LPS.LinuxProcessSem.Sys.Uapi
import LPS.LinuxProcessSem.Sys.Uaccess

/-!
# LPS `theories/LinuxProcessSem/Sys/Kernel/Futex/Syscalls.v` (f1006fe8): futex

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/Sys/Kernel/Futex/Syscalls.v` at f1006fe8 (TRUST BOUNDARY there). Definitions; lemmas
when a proof needs them.
-/

namespace LPS

def futex_aligned_b (uaddr : word) : Bool := Z.modulo (bv_unsigned uaddr) FUTEX_WORD_SIZE == 0
def futex_key_check (uaddr : word) (k : Sys SyscallEffect) : Sys SyscallEffect :=
  if !(futex_aligned_b uaddr) then err_ret EINVAL
  else if !(access_okb uaddr FUTEX_WORD_SIZE) then err_ret EFAULT
  else k
def futex_wake_private_spec (uaddr : word) : Sys SyscallEffect := futex_key_check uaddr (ret_only (Z_to_bv 64 0))
def FUTEX_WORD_SIZE_nat : Nat := 4
def futex_wait_private_spec (uaddr val : word) : Sys SyscallEffect :=
  futex_key_check uaddr (do
    let i ← input
    match read_bytes_map i.in_mem uaddr (Z_to_bv 64 FUTEX_WORD_SIZE) with
    | none => unmodeled
    | some uval =>
      record_copyins [(uaddr, FUTEX_WORD_SIZE_nat)]
        (if bv_eqb (le_bytes_to_word uval) val then unmodeled else err_ret EAGAIN))
def futex_spec (uaddr op val utime : word) : Sys SyscallEffect :=
  if bv_eqb op (Z_to_bv 64 FUTEX_WAKE_PRIVATE) then futex_wake_private_spec uaddr
  else if bv_eqb op (Z_to_bv 64 FUTEX_WAIT_PRIVATE) then
    (if !(w_is0 utime) then unmodeled else futex_wait_private_spec uaddr (abi_low32 val))
  else unmodeled
def futex_wait_reads_b (uaddr op utime : word) : Bool :=
  bv_eqb op (Z_to_bv 64 FUTEX_WAIT_PRIVATE) && w_is0 utime && futex_aligned_b uaddr && access_okb uaddr FUTEX_WORD_SIZE

end LPS
