import NoCompiler.Typed.Sem
import NoCompiler.Lemmas

/-
The partial meaning of a signature (docs/Tab 1.md, 署名の意味, the row 部分; decision 1, I19):
a `partial` function promises everything a total one does except termination. Every run
stays in the function and faults never, as long as it runs; if it ends (returns to `ra` or
ends the process), the exit conditions hold.

Step-indexed: `ReachP c P D Q n s` says the first `n` steps from `s` are safe and every state
among them where the run stops has `Q`. `ExecP` is that for every `n`. A total proof gives a
partial one (`ReachP.of_reach`, `Meets.toP`), so a partial function may call total ones, and
partial ones through `VerifiedImgP.call`.

Part of the trusted base: what a checked `partial` function guarantees is `MeetsP`.
-/
namespace NoCompiler

/-- The first `n` steps from `s` stay in `D`, take a step allowed by `P` whenever they have
    not stopped, and stop only where `Q` holds. -/
inductive ReachP (c : Code) (P : Perm) (D : Dom) (Q : State → Prop) : Nat → State → Prop
  | zero {s : State} : ReachP c P D Q 0 s
  | done {n : Nat} {s : State} : Q s → ReachP c P D Q (n + 1) s
  | step {n : Nat} {s : State} :
      D.mem s.pc → (∃ s', Step c P s s') → (∀ s', Step c P s s' → ReachP c P D Q n s') →
      ReachP c P D Q (n + 1) s

/-- Partial execution: every prefix of every run is safe, and where it leaves `D` (or ends
    the process) `Q` holds. -/
def ExecP (c : Code) (P : Perm) (D : Dom) (Q : State → Prop) (s : State) : Prop :=
  ∀ n, ReachP c P D (fun s => Final D s ∧ Q s) n s

/-- `VerifiedImg` without termination. -/
def VerifiedImgP {α : Type} (c : Code) (D : Dom) (entry : Word) (sp : Spec α) : Prop :=
  ∀ a s, Entry D entry s → sp.pre a s → ExecP c (sp.perm a s) D (sp.Done a s) s

namespace ReachP
variable {c : Code} {P : Perm} {D : Dom}

theorem mono {Q Q' : State → Prop} (hq : ∀ s, Q s → Q' s) {n s} (h : ReachP c P D Q n s) :
    ReachP c P D Q' n s := by
  induction h with
  | zero => exact .zero
  | done h => exact .done (hq _ h)
  | step hd hex _ ih => exact .step hd hex ih

/-- A total run gives every prefix. -/
theorem of_reach {Q : State → Prop} {s} (h : Reach c P D Q s) : ∀ n, ReachP c P D Q n s := by
  induction h with
  | done hq => intro n; cases n with
    | zero => exact .zero
    | succ n => exact .done hq
  | step hd hex _ ih => intro n; cases n with
    | zero => exact .zero
    | succ n => exact .step hd hex (fun s' h' => ih s' h' n)

/-- Sequential composition, into a larger region and permission (calls). -/
theorem bind {P₁ P₂ : Perm} {D₁ D₂ : Dom} {Q₁ Q₂ : State → Prop} {n s}
    (h : ReachP c P₁ D₁ Q₁ n s) (hP : P₁.le P₂) (hD : D₁.sub D₂)
    (k : ∀ m s', Q₁ s' → ReachP c P₂ D₂ Q₂ m s') : ReachP c P₂ D₂ Q₂ n s := by
  induction h with
  | zero => exact .zero
  | done hq => exact k _ _ hq
  | step hd hex _ ih =>
    obtain ⟨s₁, h₁⟩ := hex
    exact .step (hD _ hd) ⟨s₁, h₁.mono hP⟩ (fun s' h' => ih s' (h₁.restrict h'))

/-- Carry an invariant of every step into the goal. -/
theorem inv {Q I : State → Prop} (hI : ∀ u u', I u → Step c P u u' → I u') {n s}
    (h : ReachP c P D Q n s) (hs : I s) : ReachP c P D (fun u => Q u ∧ I u) n s := by
  induction h with
  | zero => exact .zero
  | done hq => exact .done ⟨hq, hs⟩
  | step hd hex _ ih => exact .step hd hex (fun s' h' => ih s' h' (hI _ _ hs h'))

/-- Memory outside the writable bytes is unchanged where the run stops. -/
theorem frame {Q : State → Prop} {n s} (h : ReachP c P D Q n s) :
    ReachP c P D (fun u => Q u ∧ ∀ x, ¬ P.writable x → u.mem x = s.mem x) n s :=
  inv (I := fun u => ∀ x, ¬ P.writable x → u.mem x = s.mem x)
    (fun _ _ hu hs x hx => (hs.frame x hx).trans (hu x hx)) h (fun _ _ => rfl)

/-- Step over one instruction other than ECALL. -/
theorem exec_step {Q : State → Prop} {n : Nat} {s s₁ : State} {i : Instr}
    (hd : D.mem s.pc) (hx : s.exit = none) (hi : c.instr s.pc = some i) (hok : InstrOk P i s)
    (hs : exec i s = some s₁) (h : ReachP c P D Q n s₁) : ReachP c P D Q (n + 1) s := by
  refine .step hd ⟨s₁, .exec hx hi hok hs⟩ (fun s' h' => ?_)
  cases h' with
  | exec _ hi' _ hx' => rw [hi] at hi'; cases hi'; rw [hs] at hx'; cases hx'; exact h
  | sys _ hi' _ _ => rw [hi] at hi'; cases hi'; exact absurd hs (by simp [exec_ecall])

/-- Step over an ECALL: every outcome the environment allows has to continue. -/
theorem sys_step {Q : State → Prop} {n : Nat} {s : State}
    (hd : D.mem s.pc) (hx : s.exit = none) (hi : c.instr s.pc = some .ecall) (hok : SysOk P s)
    (hex : ∃ s', Sys s s') (h : ∀ s', Sys s s' → ReachP c P D Q n s') :
    ReachP c P D Q (n + 1) s := by
  obtain ⟨s₁, h₁⟩ := hex
  refine .step hd ⟨s₁, .sys hx hi hok h₁⟩ (fun s' h' => ?_)
  cases h' with
  | exec _ hi' _ hx' => rw [hi] at hi'; cases hi'; simp [exec_ecall] at hx'
  | sys _ _ _ hy => exact h _ hy

end ReachP

variable {c : Code} {α : Type}

/-- A total proof is a partial one. -/
theorem VerifiedImg.toP {D : Dom} {entry : Word} {sp : Spec α} (h : VerifiedImg c D entry sp) :
    VerifiedImgP c D entry sp :=
  fun a s he hpre => ReachP.of_reach (h a s he hpre)

/-- The frame property of a partially verified function. -/
theorem VerifiedImgP.frame {D : Dom} {entry : Word} {sp : Spec α} (h : VerifiedImgP c D entry sp)
    (a : α) (s : State) (he : Entry D entry s) (hpre : sp.pre a s) (n : Nat) :
    ReachP c (sp.perm a s) D
      (fun s' => (Final D s' ∧ sp.Done a s s') ∧
        ∀ x, ¬ (sp.perm a s).writable x → s'.mem x = s.mem x) n s :=
  (h a s he hpre n).frame

/-- The call rule for partial callers: inside a caller with region `D` and permission `P`, a
    call to a (partially) verified function continues from every way the callee can end. -/
theorem VerifiedImgP.call {Dg D : Dom} {entry : Word} {sp : Spec α} {P : Perm}
    {Q : State → Prop} {s : State} (hg : VerifiedImgP c Dg entry sp) (a : α)
    (he : Entry Dg entry s) (hpre : sp.pre a s) (hD : Dg.sub D) (hP : (sp.perm a s).le P)
    (k : ∀ m s', sp.Done a s s' → (∀ x, ¬ (sp.perm a s).writable x → s'.mem x = s.mem x) →
      ReachP c P D Q m s') (n : Nat) : ReachP c P D Q n s :=
  ReachP.bind (hg.frame a s he hpre n) hP hD (fun m s' ⟨⟨_, hd⟩, hm⟩ => k m s' hd hm)

namespace Typed

/-- ⟦σ⟧, partial: the function at `entry` meets its signature except for termination. -/
def MeetsP (c : Code) (D : Dom) (entry : Word) (T : TokEnv) (σ : Sig) : Prop :=
  VerifiedImgP c D entry (σ.spec T)

theorem Meets.toP {c : Code} {D : Dom} {entry : Word} {T : TokEnv} {σ : Sig}
    (h : Meets c D entry T σ) : MeetsP c D entry T σ := VerifiedImg.toP h

end Typed

end NoCompiler
