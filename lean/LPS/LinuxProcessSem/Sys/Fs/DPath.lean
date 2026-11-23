import LPS.LinuxProcessSem.Sys.Uapi

/-!
# LPS `theories/LinuxProcessSem/Sys/Fs/DPath.v` (f1006fe8): getcwd

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/Sys/Fs/DPath.v` at f1006fe8 (TRUST BOUNDARY there). Rocq's
`x <- c ;; k` is `do let x ← c; k` (Monad.lean's instance is Monad.v's `bind`).
-/

namespace LPS

def getcwd_errnos : List Int := [ENOMEM, ENOENT, ENAMETOOLONG]

def getcwd_spec (size : word) : Sys SyscallEffect :=
  if 1 < bv_unsigned size then unmodeled
  else alt (do let e ← errno_from getcwd_errnos; err_ret e) (err_ret ERANGE)

end LPS
