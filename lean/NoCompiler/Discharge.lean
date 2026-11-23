import NoCompiler.Spec

/-!
# Discharging a callee assumption (docs/design/generator.md, section 2)

The generator proves a caller assuming a callee's theorem at some specification `sp₂`; the callee is proved
later, at `sp₁`, possibly another rung or the library's spec. `VerifiedImg.of_implies`: a theorem at `sp₁`
is a theorem at `sp₂` when every `sp₂`-entry is an `sp₁`-entry (the precondition, for some argument) whose
permission lies inside `sp₂`'s and whose ending implies `sp₂`'s. `Reach.mono_perm`: a run that is safe under
a permission is safe under a larger one (the same steps: a step's result does not depend on the permission).
-/

namespace NoCompiler

theorem Reach.mono_perm {c : Code} {P Q : Perm} {D : Dom} {R : State → Prop} (hle : P.le Q) :
    ∀ {s}, Reach c P D R s → Reach c Q D R s := by
  intro s h
  induction h with
  | done hq => exact .done hq
  | step hd hex _ ih =>
    obtain ⟨s₁, st⟩ := hex
    exact .step hd ⟨s₁, Step.mono hle st⟩ (fun s' st' => ih s' (Step.restrict st st'))

/-- `sp₁` implies `sp₂` (argument map `f`): for an `sp₂`-entry with argument `b`, `sp₁`'s precondition holds
    at `f b s`, `sp₁`'s permission is inside `sp₂`'s, and every `sp₁`-ending is an `sp₂`-ending. -/
structure Spec.Implies {α β : Type} (sp₁ : Spec α) (sp₂ : Spec β) (f : β → State → α) : Prop where
  pre : ∀ b s, sp₂.pre b s → sp₁.pre (f b s) s
  perm : ∀ b s, sp₂.pre b s → (sp₁.perm (f b s) s).le (sp₂.perm b s)
  done : ∀ b s s', sp₂.pre b s → sp₁.Done (f b s) s s' → sp₂.Done b s s'

theorem VerifiedImg.of_implies {α β : Type} {c : Code} {D : Dom} {e : Word} {sp₁ : Spec α} {sp₂ : Spec β}
    {f : β → State → α} (h : VerifiedImg c D e sp₁) (hi : Spec.Implies sp₁ sp₂ f) : VerifiedImg c D e sp₂ := by
  intro b s he hpre
  have hr := Reach.mono_perm (hi.perm b s hpre) (h (f b s) s he (hi.pre b s hpre))
  exact Reach.mono (fun t ht => ⟨ht.1, hi.done b s t hpre ht.2⟩) hr

/-- The same specification: implication with the identity. -/
theorem Spec.Implies.refl {α : Type} (sp : Spec α) : Spec.Implies sp sp (fun a _ => a) :=
  ⟨fun _ _ h => h, fun _ _ _ => Perm.le_refl _, fun _ _ _ _ h => h⟩

end NoCompiler
