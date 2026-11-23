import NoCompiler.Lib.Word

/-!
# Library: loop rules

Generic forms of `Reach.loop` (Step.lean: one invariant, a `Nat` measure) for the loops machine
code has: any well-founded measure, a lexicographic (outer, inner) measure for nested loops, a
count-down or count-up register, and the same rules for `Exec` (a run to the region's exit).
Namespace `NoCompiler.Lib`. Round 7, B's row.
-/

namespace NoCompiler.Lib
open NoCompiler

variable {c : Code} {P : Perm} {D : Dom}

/-- A loop whose measure decreases in any well-founded relation. -/
theorem reach_loop_wf {β : Type} [r : WellFoundedRelation β] {Q : State → Prop}
    (I : State → Prop) (μ : State → β)
    (body : ∀ s, I s → Reach c P D (fun s' => Q s' ∨ (I s' ∧ r.rel (μ s') (μ s))) s) :
    ∀ s, I s → Reach c P D Q s := by
  intro s hs
  have wf := (invImage μ r).wf
  induction s using wf.induction with
  | _ s ih =>
    refine Reach.trans (body s hs) ?_
    rintro s' (hq | ⟨hi, hlt⟩)
    · exact .done hq
    · exact ih s' hlt hi

/-- A loop with a lexicographic measure: each iteration decreases the outer measure, or keeps it
    and decreases the inner one (two nested loops seen from the outer head). -/
theorem reach_loop_lex {Q : State → Prop} (I : State → Prop) (μ₁ μ₂ : State → Nat)
    (body : ∀ s, I s → Reach c P D (fun s' => Q s' ∨
      (I s' ∧ (μ₁ s' < μ₁ s ∨ (μ₁ s' = μ₁ s ∧ μ₂ s' < μ₂ s)))) s) :
    ∀ s, I s → Reach c P D Q s := by
  intro s hs
  induction h₁ : μ₁ s using Nat.strongRecOn generalizing s with
  | _ n₁ ih₁ =>
    induction h₂ : μ₂ s using Nat.strongRecOn generalizing s with
    | _ n₂ ih₂ =>
      refine Reach.trans (body s hs) ?_
      rintro s' (hq | ⟨hi, hlt | ⟨heq, hlt⟩⟩)
      · exact .done hq
      · exact ih₁ _ (h₁ ▸ hlt) s' hi rfl
      · exact ih₂ _ (h₂ ▸ hlt) s' hi (heq.trans h₁) rfl

/-- A loop counting a register down: each iteration lowers its value. -/
theorem reach_loop_down {Q : State → Prop} (I : State → Prop) (r : Reg)
    (body : ∀ s, I s → Reach c P D (fun s' => Q s' ∨ (I s' ∧ (s'.reg r).toNat < (s.reg r).toNat)) s) :
    ∀ s, I s → Reach c P D Q s :=
  Reach.loop I (fun s => (s.reg r).toNat) body

/-- A loop counting a register up to a bound `n`: each iteration raises its value, which stays
    at most `n`. -/
theorem reach_loop_up {Q : State → Prop} (I : State → Prop) (r : Reg) (n : Nat)
    (body : ∀ s, I s → Reach c P D (fun s' => Q s' ∨
      (I s' ∧ (s.reg r).toNat < (s'.reg r).toNat ∧ (s'.reg r).toNat ≤ n)) s) :
    ∀ s, I s → Reach c P D Q s :=
  Reach.loop I (fun s => n - (s.reg r).toNat) (fun s hs =>
    Reach.mono (fun _ h => h.imp id fun ⟨hi, hlt, hle⟩ => ⟨hi, by omega⟩) (body s hs))

/-- Running to the region's exit, through an intermediate condition. -/
theorem exec_trans {Q₁ Q : State → Prop} {s : State} (h : Reach c P D Q₁ s)
    (k : ∀ s', Q₁ s' → Exec c P D Q s') : Exec c P D Q s :=
  Reach.trans h k

/-- A loop whose every iteration either runs to the region's exit or comes back to the head
    with the invariant and a smaller measure. -/
theorem exec_loop {Q : State → Prop} (I : State → Prop) (μ : State → Nat)
    (body : ∀ s, I s → Reach c P D (fun s' => (Final D s' ∧ Q s') ∨ (I s' ∧ μ s' < μ s)) s) :
    ∀ s, I s → Exec c P D Q s :=
  Reach.loop I μ body

/-- A weaker invariant at the head suffices when the body re-establishes the stronger one. -/
theorem reach_loop_of_imp {Q : State → Prop} (I J : State → Prop) (μ : State → Nat)
    (hIJ : ∀ s, I s → J s)
    (body : ∀ s, J s → Reach c P D (fun s' => Q s' ∨ (I s' ∧ μ s' < μ s)) s) :
    ∀ s, I s → Reach c P D Q s :=
  Reach.loop I μ (fun s hs => body s (hIJ s hs))

end NoCompiler.Lib
