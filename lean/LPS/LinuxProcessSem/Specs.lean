import LPS.LinuxProcessSem.Sys.SyscallTable

/-!
# LPS `theories/LinuxProcessSem/Specs.v` (f1006fe8): the dispatcher

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/Specs.v` at f1006fe8 (TRUST BOUNDARY there). Specs.v re-exports every
Sys module and defines `modeled_sysnos` and `syscall_spec`; here the import of
LPS.LinuxProcessSem.Sys.SyscallTable (which imports every Sys module) stands for the re-export. Specs.v's
header (the representation and fail-closed conventions every spec follows) is not repeated; read it at
the source.
-/

namespace LPS

def modeled_sysnos : List Int := arm_numbers spec_table

/-- Dispatch on the unsigned syscall number; a number outside `modeled_sysnos` is `unmodeled`
    (fail-closed). -/
def syscall_spec : Sys SyscallEffect := dispatch spec_table

end LPS
