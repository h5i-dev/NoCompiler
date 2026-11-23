import LPS.LinuxProcessSem.Sys.Uapi
import LPS.LinuxProcessSem.Sys.Uaccess

/-!
# LPS `theories/LinuxProcessSem/Sys/Fs/EventPoll.v` (f1006fe8): epoll_create1, epoll_ctl, epoll_pwait

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/Sys/Fs/EventPoll.v` at f1006fe8 (TRUST BOUNDARY there). Definitions; lemmas
when a proof needs them.
-/

namespace LPS

def EPOLL_CLOEXEC : Int := O_CLOEXEC
def EPOLL_CTL_DEL : Int := 2
def epoll_event_bytes : Int := 16
def EP_MAX_EVENTS : Int := 134217727
def fd_can_poll : FdEntry → Option Bool
  | .FdFile _ _ | .FdFileW _ _ | .FdFileA _ _ | .FdFileRW _ _ | .FdDir => some false
  | .FdSocket _ | .FdPipe _ _ => some true
  | .FdChannel _ => none
  | .FdDevNull _ _ => none
  | .FdUrandom => none
def epoll_create1_outcome (flags32 : word) : Option word :=
  if Z.land (bv_unsigned flags32) (Z.modulo (Z.lnot EPOLL_CLOEXEC) (2 ^ 32)) == 0 then none
  else some (errno_ret EINVAL)
def epoll_create1_spec (flags32 : word) : Sys SyscallEffect :=
  match epoll_create1_outcome flags32 with
  | none => unmodeled
  | some r => Sys.pure (mkEffect r [] [])
def copy_from_user_ok (mp : word → Option byte) (a : word) (len : Int) : Bool :=
  access_okb a len && match read_bytes_map mp a (Z_to_bv 64 len) with
    | some _ => true
    | none => false
def ep_op_has_event (op32 : word) : Bool := !(bv_unsigned op32 == EPOLL_CTL_DEL)
def epoll_ctl_outcome (i : SyscallInput) (m : Model) (epfd : word) (op32 : word) (tfd : word) (event : word) :
    Option word :=
  let after_copy :=
    match fd_lookup (m_fds m) epfd with
    | none => some (errno_ret EBADF)
    | some _ =>
      match fd_lookup (m_fds m) tfd with
      | none => some (errno_ret EBADF)
      | some te =>
        match fd_can_poll te with
        | some false => some (errno_ret EPERM)
        | some true => some (errno_ret EINVAL)
        | none => none
  if ep_op_has_event op32 then
    if copy_from_user_ok i.in_mem event epoll_event_bytes then after_copy else some (errno_ret EFAULT)
  else after_copy
def epoll_ctl_spec (epfd op32 tfd event : word) : Sys SyscallEffect := do
  let i ← input
  let m ← get_model
  match epoll_ctl_outcome i m epfd op32 tfd event with
  | none => unmodeled
  | some r => Sys.pure (mkEffect r [] [])
inductive EpollSigmask where
  | EpSigNone | EpSigBadSize | EpSigFault | EpSigReal
def epoll_sigmask (mp : word → Option byte) (umask sigsetsize : word) : EpollSigmask :=
  if w_is0 umask then .EpSigNone
  else if !(bv_unsigned sigsetsize == kernel_sigset_bytes) then .EpSigBadSize
  else if copy_from_user_ok mp umask kernel_sigset_bytes then .EpSigReal
  else .EpSigFault
def epoll_pwait_outcome (i : SyscallInput) (m : Model) (epfd events maxevents32 sigmask sigsetsize : word) :
    Option word :=
  match epoll_sigmask i.in_mem sigmask sigsetsize with
  | .EpSigBadSize => some (errno_ret EINVAL)
  | .EpSigFault => some (errno_ret EFAULT)
  | .EpSigReal => none
  | .EpSigNone =>
    match fd_lookup (m_fds m) epfd with
    | none => some (errno_ret EBADF)
    | some _ =>
      let n := sint32 maxevents32
      if n ≤ 0 then some (errno_ret EINVAL)
      else if EP_MAX_EVENTS < n then some (errno_ret EINVAL)
      else if access_okb events (n * epoll_event_bytes) then some (errno_ret EINVAL)
      else some (errno_ret EFAULT)
def epoll_pwait_spec (epfd events maxevents32 sigmask sigsetsize : word) : Sys SyscallEffect := do
  let i ← input
  let m ← get_model
  match epoll_pwait_outcome i m epfd events maxevents32 sigmask sigsetsize with
  | none => unmodeled
  | some r => Sys.pure (mkEffect r [] [])

end LPS
