import NoCompiler.Lib.Loop

/-!
# Library: call rules

Generic forms of `VerifiedImg.call` (Spec.lean) for the calls machine code makes: a split form
with one continuation for the callee's return and one for its exit; a callee that never returns
(its spec's `post` is false: the caller's code after the call is never reached, the R2 rule of
docs/isa/profile.md); a callee that never exits; and `Region.within`, the containment the
callee's permission needs inside the caller's. Namespace `NoCompiler.Lib`. Round 7, B's row.
-/

namespace NoCompiler.Lib
open NoCompiler

variable {c : Code} {α : Type}

/-- The call rule with the callee's two endings apart: it returned to `ra` with the registers
    preserved and its postcondition, or the process ended with its exit condition. -/
theorem call_split {Dg D : Dom} {entry : Word} {sp : Spec α} {P : Perm} {Q : State → Prop}
    {s : State} (hg : VerifiedImg c Dg entry sp) (a : α) (he : Entry Dg entry s)
    (hpre : sp.pre a s) (hD : Dg.sub D) (hP : (sp.perm a s).le P)
    (kret : ∀ s', s'.exit = none → s'.pc = s.reg Reg.ra → Preserved s s' → sp.post a s s' →
      (∀ x, ¬ (sp.perm a s).writable x → s'.mem x = s.mem x) → Reach c P D Q s')
    (kexit : ∀ s', s'.exit ≠ none → sp.onExit a s s' → Reach c P D Q s') : Reach c P D Q s :=
  hg.call a he hpre hD hP fun s' hd hm => by
    rcases hd with ⟨hx, hpc, hpr, hpo⟩ | ⟨hx, ho⟩
    · exact kret s' hx hpc hpr hpo hm
    · exact kexit s' hx ho

/-- A call to a function that never returns (its `post` is false: `abort`, `exit`): only the
    process's end has to be handled; what follows the call is never reached. -/
theorem call_noreturn {Dg D : Dom} {entry : Word} {sp : Spec α} {P : Perm} {Q : State → Prop}
    {s : State} (hg : VerifiedImg c Dg entry sp) (a : α) (he : Entry Dg entry s)
    (hpre : sp.pre a s) (hD : Dg.sub D) (hP : (sp.perm a s).le P)
    (hnr : ∀ s', ¬ sp.post a s s')
    (kexit : ∀ s', s'.exit ≠ none → sp.onExit a s s' → Reach c P D Q s') : Reach c P D Q s :=
  call_split hg a he hpre hD hP (fun s' _ _ _ hpo _ => absurd hpo (hnr s')) kexit

/-- A call to a function that never ends the process (its `onExit` is false): only its return
    has to be handled. -/
theorem call_noexit {Dg D : Dom} {entry : Word} {sp : Spec α} {P : Perm} {Q : State → Prop}
    {s : State} (hg : VerifiedImg c Dg entry sp) (a : α) (he : Entry Dg entry s)
    (hpre : sp.pre a s) (hD : Dg.sub D) (hP : (sp.perm a s).le P)
    (hne : ∀ s', ¬ sp.onExit a s s')
    (kret : ∀ s', s'.exit = none → s'.pc = s.reg Reg.ra → Preserved s s' → sp.post a s s' →
      (∀ x, ¬ (sp.perm a s).writable x → s'.mem x = s.mem x) → Reach c P D Q s') :
    Reach c P D Q s :=
  call_split hg a he hpre hD hP kret (fun s' _ ho => absurd ho (hne s'))

/-! ## Containment of regions, for the callee's permission inside the caller's -/

theorem within_iff (r r' : Region) : r.within r' ↔ (r.base - r'.base).toNat + r.size ≤ r'.size :=
  Iff.rfl

/-- Containment is transitive. -/
theorem within_trans {r r' r'' : Region} (h : r.within r') (h' : r'.within r'') : r.within r'' := by
  unfold Region.within at *
  have e : r.base - r''.base = (r.base - r'.base) + (r'.base - r''.base) := by bv_omega
  rw [e, BitVec.toNat_add]
  exact Nat.le_trans (Nat.add_le_add_right (Nat.mod_le _ _) _) (by omega)

/-- A region covered by another lies within it. -/
theorem within_of_covers {r r' : Region} (h : r'.covers r.base r.size) : r.within r' := h

/-- A sub-range of a region lies within it. -/
theorem within_sub (a : Word) {n : Nat} (j len : Nat) (hj : j + len ≤ n) :
    (⟨a + BitVec.ofNat 64 j, len⟩ : Region).within ⟨a, n⟩ :=
  Region.covers_sub (Region.covers_self a n) j len hj

/-- An empty region lies within any region that reaches its base. -/
theorem within_empty {a : Word} {r : Region} (h : (a - r.base).toNat ≤ r.size) :
    (⟨a, 0⟩ : Region).within r := by
  unfold Region.within; simpa using h

/-- A permission with no regions allows nothing beyond any other. -/
theorem le_of_empty (Q : Perm) : ({ rd := [], wr := [] } : Perm).le Q :=
  Perm.le_of (by simp) (by simp)

end NoCompiler.Lib
