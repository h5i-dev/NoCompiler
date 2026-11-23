import LPS.Common.DivergeSim1

/-!
# LPS `theories/Common/DivergeSim.v` (f1006fe8), part 2: the worked examples

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Common/DivergeSim.v` at f1006fe8, after `End WithSegs` (DivergeSim.v:660-834): the toy
two-branch obligation in the shape of an mmap-refusal case-split (`spin_branch_toy_obs_iff`,
`spin_branch_toy_no_error`). Rocq's module `SelfJumpImage` (DivergeSim.v's second worked example, over the
literal `j .` image) is in `Examples/LPS/Common/DivergeSimSpin.lean`: nothing binary-specific outside Examples.

Section `TwoBranchToy`'s variables `segs c0 evs_g c_g c_r T P` and its hypotheses `Hsplit .. HP_r` are
explicit arguments of the two theorems, in that order. The Rocq `Example`s are `theorem`s; the
concrete facts Rocq closes by the Ltac `div_vm_refl` (a `vm_compute` cast) and `prove_to_spin` are
closed by `decide` (kernel evaluation, no `native_decide`). Conventions as DivergeSim1.
-/

namespace LPS
open RiscvSemantics instr core

/-! ### Worked example 1: a toy two-branch obligation -/

theorem spin_branch_toy_obs_iff (segs : List Segment) (c0 : config) (evs_g : List event) (c_g c_r : config)
    (T : List event) (P : config → Prop)
    (Hsplit : ∀ evs to, sstep segs c0 evs to → (evs = evs_g ∧ to = .SNext c_g) ∨ (evs = [] ∧ to = .SNext c_r))
    (Hstep_g : sstep segs c0 evs_g (.SNext c_g))
    (Hg_obs : ∀ tr, obs_trace segs c_g tr ↔ is_prefix tr T)
    (_Hg_noerr : ¬ reaches_error segs c_g)
    (Hloop : silent_loop segs P) (HP_r : P c_r) :
    ∀ tr, obs_trace segs c0 tr ↔ is_prefix tr (evs_g ++ T) := by
  intro tr
  constructor
  · rintro ⟨tr', cend, hstar, hpre⟩
    rcases star_case segs c0 tr' cend hstar with ⟨rfl, _⟩ | ⟨evs, c2, tr2, hstep, htail, rfl⟩
    · rw [is_prefix_nil_inv tr hpre]; exact is_prefix_nil _
    · rcases Hsplit evs _ hstep with ⟨rfl, heq⟩ | ⟨rfl, heq⟩
      · -- grant branch: the tail is one of its observations
        cases heq
        have hobs2 : obs_trace segs c_g tr2 := ⟨tr2, cend, htail, is_prefix_refl _⟩
        exact is_prefix_trans _ _ _ hpre (is_prefix_app_mono _ _ _ ((Hg_obs tr2).1 hobs2))
      · -- refusal branch: the tail collapses
        cases heq
        rw [silent_loop_star_nil segs P c_r tr2 cend Hloop HP_r htail] at hpre
        rw [is_prefix_nil_inv tr hpre]; exact is_prefix_nil _
  · intro hpre
    obtain ⟨tr'', cend, hstar, hpreT⟩ := (Hg_obs T).2 (is_prefix_refl T)
    exact ⟨evs_g ++ tr'', cend, .star_step _ _ _ _ _ Hstep_g hstar,
      is_prefix_trans _ _ _ hpre (is_prefix_app_mono _ _ _ hpreT)⟩

theorem spin_branch_toy_no_error (segs : List Segment) (c0 : config) (evs_g : List event) (c_g c_r : config)
    (_T : List event) (P : config → Prop)
    (Hsplit : ∀ evs to, sstep segs c0 evs to → (evs = evs_g ∧ to = .SNext c_g) ∨ (evs = [] ∧ to = .SNext c_r))
    (_Hstep_g : sstep segs c0 evs_g (.SNext c_g))
    (_Hg_obs : ∀ tr, obs_trace segs c_g tr ↔ is_prefix tr _T)
    (Hg_noerr : ¬ reaches_error segs c_g)
    (Hloop : silent_loop segs P) (HP_r : P c_r) :
    ¬ reaches_error segs c0 := by
  rintro ⟨tr, cerr, evs, hstar, herr⟩
  rcases star_case segs c0 tr cerr hstar with ⟨_, rfl⟩ | ⟨evs1, c2, tr2, hstep, htail, _⟩
  · rcases Hsplit evs .SError herr with ⟨_, heq⟩ | ⟨_, heq⟩ <;> cases heq
  · rcases Hsplit evs1 _ hstep with ⟨_, heq⟩ | ⟨_, heq⟩ <;> cases heq
    · exact Hg_noerr ⟨tr2, cerr, evs, htail, herr⟩
    · exact silent_loop_no_error segs P c_r Hloop HP_r ⟨tr2, cerr, evs, htail, herr⟩


end LPS
