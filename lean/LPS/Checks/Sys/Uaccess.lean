import LPS.Checks.Sys.Prelude

/-!
# LPS `theories/LinuxProcessSem/Checks/Sys/Uaccess.v` (f1006fe8): PARTIAL port

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/Checks/Sys/Uaccess.v` at f1006fe8 (the user-buffer boundary
checkers). PARTIAL: only `check_access_ok_zero`, which `Checks/Sys/Fs/ReadWrite.v`'s `check_write`
uses. Not ported: `check_efault_or` and the lemmas, and the Ltacs `ok_zero_cases`, `ok_zero_split`.
-/

namespace LPS

def check_access_ok_zero (buf count : word) (eff : SyscallEffect) (m : Model) (k : check_result) :
    check_result :=
  if access_okb buf (bv_unsigned count) then k else check_ret_only eff (errno_ret EFAULT) m []

end LPS
