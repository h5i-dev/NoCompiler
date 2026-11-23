import NoCompiler.Typed.SemPartial

/-
What a run of a checked function has to establish, abstracted over total and partial
correctness, so that the per-instruction part of the soundness proof is written once.

A `Runner` gives the predicate `R` to prove at the current state, `next` for the state one
instruction later, and `later` for a state after a callee returned. `Runner.total` is `Reach`
(all three the same, Theorems A-C). `Runner.fuel n` is `ReachP` with `n + 1` steps of fuel:
one step leaves `n`, a call leaves at most `n` (the callee takes at least one step, since its
entry lies in its domain). The callee judgment is `VerifiedImg` for total runs and
`VerifiedImgP` for partial ones; a total callee is accepted by both (`ofTotal`).

No checker definitions here.
-/
namespace NoCompiler

structure Runner (c : Code) (P : Perm) (D : Dom) (Q : State → Prop) where
  R : State → Prop
  next : State → Prop
  later : State → Prop
  /-- The callee judgment this kind of run accepts. -/
  callee : {α : Type} → Dom → Word → Spec α → Prop
  ofTotal : ∀ {α : Type} {Dg : Dom} {entry : Word} {sp : Spec α}, VerifiedImg c Dg entry sp →
    callee Dg entry sp
  later_next : ∀ s, later s → next s
  done : ∀ s, Q s → R s
  exec : ∀ {s s₁ : State} {i : Instr}, D.mem s.pc → s.exit = none → c.instr s.pc = some i →
    InstrOk P i s → exec i s = some s₁ → next s₁ → R s
  sys : ∀ {s : State}, D.mem s.pc → s.exit = none → c.instr s.pc = some .ecall → SysOk P s →
    (∃ s', Sys s s') → (∀ s', Sys s s' → next s') → R s
  call : ∀ {α : Type} {Dg : Dom} {entry : Word} {sp : Spec α} {s : State},
    callee Dg entry sp → ∀ a, Entry Dg entry s → Dg.mem entry → sp.pre a s → Dg.sub D →
    (sp.perm a s).le P →
    (∀ s', sp.Done a s s' → (∀ x, ¬ (sp.perm a s).writable x → s'.mem x = s.mem x) → later s') →
    R s

variable {c : Code} {P : Perm} {D : Dom} {Q : State → Prop}

/-- Total runs: `Reach` (the checker's Theorems A-C). -/
def Runner.total (c : Code) (P : Perm) (D : Dom) (Q : State → Prop) : Runner c P D Q where
  R := Reach c P D Q
  next := Reach c P D Q
  later := Reach c P D Q
  callee := fun Dg entry sp => VerifiedImg c Dg entry sp
  ofTotal := fun h => h
  later_next := fun _ h => h
  done := fun _ h => .done h
  exec := fun hd hx hi hok hs h => Reach.exec_step hd hx hi hok (by rw [hs, Reach.opt_some]; exact h)
  sys := fun hd hx hi hok hex h => Reach.sys_step hd hx hi hok hex h
  call := fun hg a he _ hpre hD hP k => VerifiedImg.call hg a he hpre hD hP k

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
  ofTotal := fun h => h.toP
  later_next := fun _ h => h n (Nat.le_refl n)
  done := fun _ h => .done h
  exec := fun hd hx hi hok hs h => ReachP.exec_step hd hx hi hok hs h
  sys := fun hd hx hi hok hex h => ReachP.sys_step hd hx hi hok hex h
  call := by
    intro α Dg entry sp s hg a he hent hpre hD hP k
    have h := hg.frame a s he hpre (n + 1)
    cases h with
    | done hq =>
      -- the callee cannot stop at its entry: the entry is in its domain and the run is live
      exfalso
      rcases hq.1.1 with hn | hn
      · exact hn (he.pc ▸ hent)
      · exact hn he.live
    | step hd hex hs =>
      obtain ⟨s₁, h₁⟩ := hex
      exact .step (hD _ hd) ⟨s₁, h₁.mono hP⟩ (fun s' h' =>
        ReachP.bind_le (hs s' (h₁.restrict h')) hP hD
          (fun m hm s'' ⟨⟨_, hdn⟩, hfr⟩ => k s'' hdn hfr m hm))

end NoCompiler
