import LPS.LinuxProcessSem.Run3

/-!
# LPS `theories/LinuxProcessSem/Run.v` (f1006fe8), part 5: two more lemmas, for `Common/AllocMixSim.v`

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/Run.v` at f1006fe8 (TRUST BOUNDARY there): the lemmas
`reaches_unmodeled_reaches_error` and `no_error_no_unmodeled` (Run.v:829-839), which
`Common/AllocMixSim.v` uses and Run3 does not have. Same names and statements; Section variable
`mi_loaded_segments` is the leading explicit argument `segs`. The proofs are Lean's.
-/

namespace LPS

theorem reaches_unmodeled_reaches_error (segs : List Segment) :
    ∀ c0, reaches_unmodeled segs c0 → reaches_error segs c0 := by
  rintro c0 ⟨tr, c, Hstar, Hun⟩
  obtain ⟨evs, Hss⟩ := unmodeled_at_sstep_error segs c Hun
  exact ⟨tr, c, evs, Hstar, Hss⟩

theorem no_error_no_unmodeled (segs : List Segment) :
    ∀ c0, ¬ reaches_error segs c0 → ¬ reaches_unmodeled segs c0 :=
  fun c0 H Hun => H (reaches_unmodeled_reaches_error segs c0 Hun)

end LPS
