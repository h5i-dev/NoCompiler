import LPS.LinuxProcessSem.Sys.Uapi
import LPS.LinuxProcessSem.Sys.Uaccess

/-!
# LPS `theories/LinuxProcessSem/Sys/Kernel/Sched/Syscalls.v` (f1006fe8): sched_*

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/Sys/Kernel/Sched/Syscalls.v` at f1006fe8 (TRUST BOUNDARY there). Definitions; lemmas
when a proof needs them.
-/

namespace LPS

def affinity_len_einval_b (len : word) : Bool :=
  let l := bv_unsigned (abi_low32 len)
  Z.modulo (l * 8) (2 ^ 32) == 0 || !(Z.modulo l 8 == 0)
def sched_getaffinity_spec (len : word) : Sys SyscallEffect := if affinity_len_einval_b len then err_ret EINVAL else unmodeled
def sched_valid_policy_b (pol : Int) : Bool :=
  pol == SCHED_NORMAL || pol == SCHED_FIFO || pol == SCHED_RR || pol == SCHED_BATCH || pol == SCHED_IDLE ||
    pol == SCHED_DEADLINE
def sched_rt_policy_b (pol : Int) : Bool := pol == SCHED_FIFO || pol == SCHED_RR
def sched_targets_self_b (pid : word) (m : Model) : Bool :=
  w_is0 (pid32 pid) || match m_tid m with
    | some tid => bv_eqb (pid32 pid) tid
    | none => false
def sched_setscheduler_answer (pol prio : Int) : Option word :=
  if !(Z.land pol SCHED_RESET_ON_FORK == 0) then none
  else if pol == SCHED_EXT then none
  else if !(sched_valid_policy_b pol) then some (errno_ret EINVAL)
  else if MAX_RT_PRIO - 1 < prio then some (errno_ret EINVAL)
  else if pol == SCHED_DEADLINE then some (errno_ret EINVAL)
  else if xor (sched_rt_policy_b pol) (!(prio == 0)) then some (errno_ret EINVAL)
  else if pol == SCHED_IDLE then some (Z_to_bv 64 0)
  else none
def sched_setscheduler_spec (pid policy param : word) : Sys SyscallEffect :=
  if sint32 policy < 0 then err_ret EINVAL
  else if w_is0 param || decide (sint32 pid < 0) then err_ret EINVAL
  else do
    let i ← input
    let m ← get_model
    match read_bytes_map i.in_mem param (Z_to_bv 64 4) with
    | none => if !(access_okb param 4) then err_ret EFAULT else unmodeled
    | some bs =>
      record_copyins [(param, 4)]
        (if !(sched_targets_self_b pid m) then unmodeled
         else match sched_setscheduler_answer (bv_unsigned (abi_low32 policy)) (bv_unsigned (le_bytes_to_word bs)) with
           | some r => ret_only r
           | none => unmodeled)
def sched_yield_spec : Sys SyscallEffect := ret_only (Z_to_bv 64 0)

end LPS
