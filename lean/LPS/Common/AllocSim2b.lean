import LPS.Common.AllocSim3
import LPS.Common.MmapSim3

/-!
# LPS `theories/Common/AllocSim2.v` (f1006fe8): mixed-allocator equivalence glue

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Common/AllocSim2.v` at f1006fe8 (shared proof library, not the trusted specification
there; image-INDEPENDENT). The Lean file is named `AllocSim2b` because LPS/Common/AllocSim2.lean is
already part 2 of the port of `Common/AllocSim.v`; this module is the whole of the DIFFERENT Rocq file
`Common/AllocSim2.v`.

Glue for the allocator-divergence examples: a SOURCE binary whose behaviour is an `AllocSim.to_outcomes`
set (brk branching) and a TARGET binary characterized by a `MmapSim.tmw` derivation (one mmap with a
failure tail and a success tail). When the source's outcome set is exactly the two-element set
`{(bf, cf), (bs, cs)}` matching the target's two tails (`two_outcomes`), the two binaries are observably
equivalent (`alloc_mmap_strong_equiv`, and `alloc_mmap_omni_strong_equiv` at the two role budgets):
allocation emits no trace events, so each side's trace set is the prefixes of the same two candidate
traces. Everything is ported; the proofs are Lean's.
-/

namespace LPS
open RiscvSemantics OmniRun

/-- The two-element outcome set of a fail/succeed allocator run. -/
def two_outcomes (bf : List (List byte)) (cf : word) (bs : List (List byte)) (cs : word) :
    (List (List byte) × word) → Prop :=
  fun o => o = (bf, cf) ∨ o = (bs, cs)

/-- `Equivalence.equiv` for a brk-allocating source whose outcome set is `two_outcomes bf cf bs cs` and an
    mmap-allocating target with the same failure tail `(bf, cf)` and success tail `(bs, cs)`. -/
theorem alloc_mmap_strong_equiv :
    ∀ source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim bf cf bs cs inp,
      to_outcomes source_segs
        (init_machine_state source_segs rpc rph rsp rrnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
        (init_model (segments_reserved source_segs) rbrk rmb rsp rlim inp) (two_outcomes bf cf bs cs) →
      tmw target_segs
        (init_machine_state target_segs apc aph asp arnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
        (init_model (segments_reserved target_segs) abrk amb asp alim inp) bf cf bs cs →
      bufs_modeled bf → bufs_modeled bs →
      modeled (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp) ∧
        equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
          (run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp) := by
  intro source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim bf cf bs cs inp
    Hsource Htarget Hbf Hbs
  refine ⟨no_error_run_modeled _ _ _ _ _ _ _ _ _
    (alloc_no_error_run source_segs rpc rph rsp rbrk rmb rrnd rlim inp _ Hsource), .inr ⟨?_, ?_⟩⟩
  · intro tr
    show obs_trace source_segs _ tr ↔ obs_trace target_segs _ tr
    rw [alloc_obs_iff source_segs rpc rph rsp rbrk rmb rrnd rlim inp _ Hsource tr,
      mmap_obs_iff_te target_segs apc aph asp abrk amb arnd alim inp bf cf bs cs Htarget Hbf Hbs tr]
    unfold two_traces two_outcomes outcome_trace
    constructor
    · rintro ⟨o, (rfl | rfl), Hp⟩
      · exact .inl Hp
      · exact .inr Hp
    · rintro (Hp | Hp)
      · exact ⟨(bf, cf), .inl rfl, Hp⟩
      · exact ⟨(bs, cs), .inr rfl, Hp⟩
  · exact mmap_no_error_run_te target_segs apc aph asp abrk amb arnd alim inp bf cf bs cs Htarget Hbf Hbs

/-- The omni equivalence of a brk-branching source against an mmap-branching target with the same two
    outcomes, at the two role budgets. -/
theorem alloc_mmap_omni_strong_equiv :
    ∀ source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd bf cf bs cs inp,
      to_outcomes source_segs
        (init_machine_state source_segs rpc rph rsp rrnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
        (init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp) (two_outcomes bf cf bs cs) →
      tmw target_segs
        (init_machine_state target_segs apc aph asp arnd inp.in_argv inp.in_envp inp.in_uid inp.in_hwcap)
        (init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp) bf cf bs cs →
      bufs_modeled bf → bufs_modeled bs →
      omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
        (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp := by
  intro source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd bf cf bs cs inp
    Hsource Htarget Hbf Hbs
  apply (strong_equiv_iff _ _ _ _ _).1
  exact alloc_mmap_strong_equiv source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit
    target_segs apc aph asp abrk amb arnd target_alloc_limit bf cf bs cs inp Hsource Htarget Hbf Hbs

end LPS
