import LPS.EquivalenceDefinition.OmniEquivalence

/-!
# LPS `theories/Common/SimInv.v` (f1006fe8): the path-invariant / no-error combinator

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/Common/SimInv.v` at f1006fe8 (shared proof library, not the trusted specification
there): an invariant preserved by every `sstep` to a `SNext` successor and excluding the `SError`
transition gives `¬ reaches_error` (`inv_no_reaches_error`) and the omni safety judgment
`coexec … never_errors` (`inv_coexec`, by `coexec.coinduct` where Rocq uses `cofix`).

Not ported: the Ltac proof kit `norm_fd32` and `fd32_ok` (tactics for the `fd32` ABI truncation; no
lemma content of their own).
-/

namespace LPS
open RiscvSemantics OmniRun

/-- `Inv` is preserved along any `star` run, given that it is preserved by every single `sstep` to a
    `SNext` successor. -/
theorem star_inv (segs : List Segment) (Inv : config → Prop)
    (Hstep : ∀ c evs c', Inv c → sstep segs c evs (.SNext c') → Inv c') :
    ∀ c tr c', Inv c → star segs c tr c' → Inv c' := by
  intro c tr c' hinv hstar
  induction hstar with
  | star_refl => exact hinv
  | star_step c1 evs c2 tr c3 hss _ ih => exact ih (Hstep _ _ _ hinv hss)

/-- An invariant preserved by `sstep`-to-`SNext` that excludes the `SError` transition: no
    configuration satisfying it reaches the error step. -/
theorem inv_no_reaches_error (segs : List Segment) (Inv : config → Prop)
    (Hstep : ∀ c evs c', Inv c → sstep segs c evs (.SNext c') → Inv c')
    (Hnoerr : ∀ c evs, Inv c → ¬ sstep segs c evs .SError) :
    ∀ c, Inv c → ¬ reaches_error segs c := by
  rintro c hinv ⟨tr, c', evs, hstar, hss⟩
  exact Hnoerr _ _ (star_inv segs Inv Hstep _ _ _ hinv hstar) hss

/-- The same invariant delivers the omni safety judgment directly, by coinduction along the
    preservation clause. -/
theorem inv_coexec (segs : List Segment) (Inv : config → Prop)
    (Hstep : ∀ c evs c', Inv c → sstep segs c evs (.SNext c') → Inv c')
    (Hnoerr : ∀ c evs, Inv c → ¬ sstep segs c evs .SError) :
    ∀ c, Inv c → OmniRun.coexec segs c never_errors := by
  intro c hinv
  refine coexec.coinduct segs (fun c Q => Inv c ∧ ∀ tr o, ¬ is_error o → Q tr o) ?_ c never_errors
    ⟨hinv, fun _ _ h => h⟩
  rintro c Q ⟨hinv, hQ⟩
  cases hh : m_halted c.cfg_model with
  | some code => exact .inl ⟨by simp, hQ _ _ id⟩
  | none =>
    exact .inr ⟨rfl, fun evs hss => (Hnoerr c evs hinv hss).elim,
      fun evs c' hss => ⟨Hstep _ _ _ hinv hss, fun _ _ h => hQ _ _ h⟩⟩

/-- The bridge from the library's `¬ reaches_error` shape to the omni one. -/
theorem no_error_run_corun :
    ∀ (segs : List Segment) (pc : Nat) (ph : PhdrInfo) (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int)
      (inp : ProcInput),
      ¬ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp) →
        omni_corun (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp never_errors :=
  fun segs _ _ _ _ _ _ _ _ h => no_error_coexec segs _ h

/-- Turn a source `¬ reaches_error` proof into the source-coverage conjunct of
    `Equivalence.strong_equiv`. -/
theorem no_error_run_modeled :
    ∀ (segs : List Segment) (pc : Nat) (ph : PhdrInfo) (sp brk0 mb : word) (rnd : EntryDraw) (lim : Int)
      (inp : ProcInput),
      ¬ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp) →
        modeled (run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp) := by
  intro segs pc ph sp brk0 mb rnd lim inp h
  apply (modeled_iff _ _ _ _).2
  exact coexec_conseq segs _ _ _ (no_error_run_corun segs pc ph sp brk0 mb rnd lim inp h)
    (never_errors_covered segs)

end LPS
