import LPS.LinuxProcessSem.Sys.Uapi

/-!
# LPS `theories/LinuxProcessSem/Sys/Fs/Ioctl.v` (f1006fe8): ioctl

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/Sys/Fs/Ioctl.v` at f1006fe8 (TRUST BOUNDARY there). Definitions; lemmas
when a proof needs them.
-/

namespace LPS

def tty_only_request (req : word) : Bool :=
  bv_eqb req TCGETS || bv_eqb req TCSETS || bv_eqb req TIOCSCTTY || bv_eqb req TIOCGWINSZ ||
    bv_eqb req TIOCSWINSZ || bv_eqb req TIOCNOTTY || bv_eqb req TIOCGPTN || bv_eqb req TIOCSPTLCK
def ioctl_spec (fd req : word) : Sys SyscallEffect := do
  let m ← get_model
  match fd_lookup (m_fds m) fd with
  | none => err_ret EBADF
  | some (.FdChannel _) | some (.FdFile _ _) | some (.FdFileW _ _) | some (.FdFileA _ _) | some (.FdFileRW _ _)
  | some .FdDir | some (.FdSocket _) | some (.FdPipe _ _) | some (.FdDevNull _ _) =>
    if tty_only_request req then err_ret ENOTTY else unmodeled
  | some .FdUrandom => unmodeled

end LPS
