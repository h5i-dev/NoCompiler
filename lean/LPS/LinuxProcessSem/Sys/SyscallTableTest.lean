import LPS.LinuxProcessSem.Sys.SyscallTable

/-!
# Test: the Lean `spec_table` has the Rocq table's arms, in order

LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs, PBC),
`theories/LinuxProcessSem/Sys/SyscallTable.v` at f1006fe8. The list below is the Rocq table's syscall
numbers in order (extracted from the `mkSpecArm N%Z` lines), so a dropped, duplicated or reordered
arm fails this check.
-/

namespace LPS

example : arm_numbers spec_table =
    [17, 19, 20, 21, 22, 23, 24, 25, 29, 32, 35, 46, 48, 56, 57, 59, 61, 62, 63, 64, 65, 66, 67, 68, 72, 73, 78, 79, 80, 82, 83, 85, 93, 94, 96, 98, 101, 113, 119, 123, 124, 130, 131, 132, 134, 135, 144, 146, 147, 149, 157, 158, 159, 160, 167, 169, 172, 174, 175, 176, 177, 178, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 214, 215, 216, 220, 222, 226, 233, 242, 260, 261, 278, 435, 439] := by
  decide

example : spec_table.length = 90 := by decide

end LPS
