import LPS.LinuxProcessSem.Sys.Uapi

/-!
# LPS `theories/LinuxProcessSem/Sys/Fs/EventFd.v` (f1006fe8): eventfd2

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/Sys/Fs/EventFd.v` at f1006fe8 (TRUST BOUNDARY there). Definitions; lemmas
when a proof needs them.
-/

namespace LPS

def eventfd2_einval_b (flags : word) : Bool := !(Z.ldiff (bv_unsigned flags) EFD_FLAGS_SET == 0)
def eventfd2_spec (flags : word) : Sys SyscallEffect := if eventfd2_einval_b flags then err_ret EINVAL else unmodeled

end LPS
