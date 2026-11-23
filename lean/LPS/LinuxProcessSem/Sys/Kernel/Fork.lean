import LPS.LinuxProcessSem.Sys.Syscall

/-!
# LPS `theories/LinuxProcessSem/Sys/Kernel/Fork.v` (f1006fe8): set_tid_address, clone, clone3

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/Sys/Kernel/Fork.v` at f1006fe8 (TRUST BOUNDARY there). Definitions; lemmas
when a proof needs them.
-/

namespace LPS

def PID_MAX_ENVELOPE : Int := 2 ^ 22
def set_tid_address_spec : Sys SyscallEffect := do
  let m ← get_model
  match m_tid m with
  | some tid => ret_only tid
  | none => do
    let tid ← choose fun tid : word => 0 < bv_unsigned tid ∧ bv_unsigned tid < PID_MAX_ENVELOPE
    set_tid tid
    ret_only tid
def SIGCHLD : Int := 17
def clone_errnos : List Int := [EAGAIN, ENOMEM, EMFILE, EACCES]
def clone_fork_flags_b (flags : word) : Bool := bv_eqb flags (Z_to_bv 64 SIGCHLD)
def clone_no_shared_file_b (fds : List (word × FdEntry)) : Bool :=
  fds.all fun e => match e.2 with
    | .FdFile _ _ | .FdFileW _ _ | .FdFileA _ _ | .FdFileRW _ _ | .FdSocket _ => false
    | .FdChannel _ | .FdDir => true
    | .FdPipe _ _ => false
    | .FdDevNull _ _ => true
    | .FdUrandom => true
def clone_pid_ok_b (m : Model) (r : word) : Bool :=
  decide (0 < bv_unsigned r) && decide (bv_unsigned r < PID_MAX_ENVELOPE) &&
    (match m_tid m with
     | none => true
     | some t0 => !(bv_eqb r t0))
def clone_resolve : Sys SyscallEffect := do
  let m ← get_model
  if !(clone_no_shared_file_b (m_fds m)) then unmodeled
  else
    alt (do let e ← errno_from clone_errnos; err_ret e)
      (do let pid ← choose fun p => clone_pid_ok_b m p = true; modify with_children; ret_only pid)
def clone_spec (flags : word) : Sys SyscallEffect := if clone_fork_flags_b flags then clone_resolve else unmodeled
def CLONE_ARGS_SIZE : Int := 88
def clone_args_field (bs : List byte) (k : Nat) : word := le_bytes_to_word ((bs.drop (8 * k)).take 8)
def clone3_fork_args_b (bs : List byte) : Bool :=
  w_is0 (clone_args_field bs 0) && w_is0 (clone_args_field bs 1) && w_is0 (clone_args_field bs 2) &&
    w_is0 (clone_args_field bs 3) && bv_eqb (clone_args_field bs 4) (Z_to_bv 64 SIGCHLD) &&
    w_is0 (clone_args_field bs 5) && w_is0 (clone_args_field bs 6) && w_is0 (clone_args_field bs 7) &&
    w_is0 (clone_args_field bs 8) && w_is0 (clone_args_field bs 9) && w_is0 (clone_args_field bs 10)
def CLONE_ARGS_SIZE_nat : Nat := 88
def clone3_resolve (uargs : word) : Sys SyscallEffect := record_copyins [(uargs, CLONE_ARGS_SIZE_nat)] clone_resolve
def clone3_spec (uargs size : word) : Sys SyscallEffect :=
  if !(bv_eqb size (Z_to_bv 64 CLONE_ARGS_SIZE)) then unmodeled
  else do
    let i ← input
    match read_bytes_map i.in_mem uargs (Z_to_bv 64 CLONE_ARGS_SIZE) with
    | none => unmodeled
    | some bs => if clone3_fork_args_b bs then clone3_resolve uargs else unmodeled

end LPS
