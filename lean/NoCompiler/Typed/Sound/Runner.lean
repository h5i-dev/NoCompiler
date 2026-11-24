import NoCompiler.Typed.SemPartial

/-
What a run of a checked function has to establish, abstracted over total and partial
correctness, so that the per-instruction part of the soundness proof is written once.

A `Runner` gives the predicate `R` to prove at the current state, `next` for the state one
instruction later, and `later` for a state after a callee returned (or a final one).
`Runner.total` is `Reach` (all three the same, Theorems A-C). `Runner.fuel n` is `ReachP` with
`n + 1` steps of fuel: one step leaves `n`; a call (its instruction, then the callee's run)
leaves at most `n`. The callee judgment is `VerifiedImg` for total runs and `VerifiedImgP` for
partial ones.

No checker definitions here.
-/
namespace NoCompiler

structure Runner (c : Code) (P : Perm) (D : Dom) (Q : State → Prop) where
  R : State → Prop
  next : State → Prop
  later : State → Prop
  /-- The callee judgment this kind of run accepts. -/
  callee : {α : Type} → Dom → Word → Spec α → Prop
  later_next : ∀ s, later s → next s
  done : ∀ s, Q s → R s
  done_later : ∀ s, Q s → later s
  exec : ∀ {s s₁ : State} {i : Instr}, D.mem s.pc → s.exit = none → c.instr s.pc = some i →
    InstrOk P i s → exec i s = some s₁ → next s₁ → R s
  sys : ∀ {s : State}, D.mem s.pc → s.exit = none → c.instr s.pc = some .ecall → SysOk P s →
    (∃ s', Sys s s') → (∀ s', Sys s s' → next s') → R s
  /-- A call: the instruction at `s` enters the callee at `s₁`, whose whole run is one step. -/
  call : ∀ {α : Type} {Dg : Dom} {entry : Word} {sp : Spec α} {s s₁ : State} {i : Instr},
    D.mem s.pc → s.exit = none → c.instr s.pc = some i → InstrOk P i s →
    NoCompiler.exec i s = some s₁ → callee Dg entry sp → ∀ a, Entry Dg entry s₁ → sp.pre a s₁ → Dg.sub D →
    (sp.perm a s₁).le P →
    (∀ s', sp.Done a s₁ s' → (∀ x, ¬ (sp.perm a s₁).writable x → s'.mem x = s₁.mem x) →
      later s') →
    R s

variable {c : Code} {P : Perm} {D : Dom} {Q : State → Prop}

namespace Runner

/-- What `exec` leaves must satisfy `next`; a fault never does (as `Reach.opt`). -/
def optR (rn : Runner c P D Q) : Option State → Prop
  | none => False
  | some s => rn.next s

@[simp] theorem optR_some (rn : Runner c P D Q) {s : State} : rn.optR (some s) = rn.next s := rfl
@[simp] theorem optR_none (rn : Runner c P D Q) : rn.optR none = False := rfl

/-- Step over one instruction other than ECALL, in `Reach.exec_step`'s shape. -/
theorem exec' (rn : Runner c P D Q) {s : State} {i : Instr} (hd : D.mem s.pc) (hx : s.exit = none)
    (hi : c.instr s.pc = some i) (hok : InstrOk P i s) (h : rn.optR (NoCompiler.exec i s)) :
    rn.R s := by
  cases hxs : NoCompiler.exec i s with
  | none => rw [hxs] at h; exact h.elim
  | some s₁ => rw [hxs] at h; exact rn.exec hd hx hi hok hxs h

end Runner

-- never unfolded by unification (a goal `optR (exec i s)` would reduce through `exec`)
attribute [irreducible] Runner.optR

/-- Total runs: `Reach` (the checker's Theorems A-C). -/
def Runner.total (c : Code) (P : Perm) (D : Dom) (Q : State → Prop) : Runner c P D Q where
  R := Reach c P D Q
  next := Reach c P D Q
  later := Reach c P D Q
  callee := fun Dg entry sp => VerifiedImg c Dg entry sp
  later_next := fun _ h => h
  done := fun _ h => .done h
  done_later := fun _ h => .done h
  exec := fun hd hx hi hok hs h => Reach.exec_step hd hx hi hok (by rw [hs, Reach.opt_some]; exact h)
  sys := fun hd hx hi hok hex h => Reach.sys_step hd hx hi hok hex h
  call := fun hd hx hi hok hs hg a he hpre hD hP k =>
    Reach.exec_step hd hx hi hok (by rw [hs, Reach.opt_some]; exact VerifiedImg.call hg a he hpre hD hP k)

namespace ReachP

/-- Composition needing the continuation only up to the fuel the first part had. -/
theorem bind_le {P₁ P₂ : Perm} {D₁ D₂ : Dom} {Q₁ Q₂ : State → Prop} {N s}
    (h : ReachP c P₁ D₁ Q₁ N s) (hP : P₁.le P₂) (hD : D₁.sub D₂)
    (k : ∀ m ≤ N, ∀ s', Q₁ s' → ReachP c P₂ D₂ Q₂ m s') : ReachP c P₂ D₂ Q₂ N s := by
  induction h with
  | zero => exact .zero
  | done hq => exact k _ (Nat.le_refl _) _ hq
  | step hd hex _ ih =>
    obtain ⟨s₁, h₁⟩ := hex
    exact .step (hD _ hd) ⟨s₁, h₁.mono hP⟩
      (fun s' h' => ih s' (h₁.restrict h') (fun m hm => k m (Nat.le_succ_of_le hm)))

end ReachP

/-- Partial runs with `n + 1` steps of fuel. -/
def Runner.fuel (c : Code) (P : Perm) (D : Dom) (Q : State → Prop) (n : Nat) : Runner c P D Q where
  R := ReachP c P D Q (n + 1)
  next := ReachP c P D Q n
  later := fun s => ∀ m ≤ n, ReachP c P D Q m s
  callee := fun Dg entry sp => VerifiedImgP c Dg entry sp
  later_next := fun _ h => h n (Nat.le_refl n)
  done := fun _ h => .done h
  done_later := fun _ h m _ => by
    cases m with
    | zero => exact .zero
    | succ m => exact .done h
  exec := fun hd hx hi hok hs h => ReachP.exec_step hd hx hi hok hs h
  sys := fun hd hx hi hok hex h => ReachP.sys_step hd hx hi hok hex h
  call := fun hd hx hi hok hs hg a he hpre hD hP k =>
    ReachP.exec_step hd hx hi hok hs
      (ReachP.bind_le (hg.frame a _ he hpre n) hP hD
        (fun m hm s' ⟨⟨_, hdn⟩, hfr⟩ => k s' hdn hfr m hm))

end NoCompiler
