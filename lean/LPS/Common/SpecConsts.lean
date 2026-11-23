import LPS.LinuxProcessSem.Sys.Uaccess

/-!
# LPS `theories/Common/SpecConsts.v` (f1006fe8): bounds on the spec's constants

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Common/SpecConsts.v` at f1006fe8 (shared proof library): its two lemmas.

`theories/Common/CertRefl.v` is not ported: it is two Ltac2 tactics that close a goal by a cast to
`native_compute` / `vm_compute`, i.e. Rocq's form of what Lean calls `native_decide`, which this port does
not use (no extension of the trusted base).
-/

namespace LPS

theorem rw_bytes_max_ge17 : (131072 : Int) ≤ rw_bytes_max := by unfold rw_bytes_max; omega

theorem rw_bytes_max_nonneg : (0 : Int) ≤ rw_bytes_max := by have := rw_bytes_max_ge17; omega

end LPS
