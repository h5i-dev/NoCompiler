import NoCompiler.Discharge
import NoCompiler.Linux.ProcSpec

/-!
# Callee specifications from the library (round 7, C's row)

A caller's proof uses a callee's theorem at the specification the call needs; the library proves the callee
at its own (stronger) one. D's `VerifiedImg.of_implies` (NoCompiler/Discharge.lean) bridges the two at the
machine level. Here:

* `Spec.Implies.trans`, and `Spec.Implies.of_post`: the common case: the same argument, the
  callee's permission inside the caller's, its `post`/`onExit` implying the caller's;
* the process-level twin: `SpecP.Implies`, `VerifiedProc.of_implies`, `.refl`, `.trans`, `.of_post`
  (the kernel holds the permission, so only the precondition and the ending are compared);
* `VerifiedProc.call_of_implies`: the call rule through an implication, for a callee proved in the
  library at `sp₁` and called where `sp₂` is what the caller can establish and use.
-/
namespace NoCompiler

theorem Spec.Implies.trans {α β γ : Type} {sp₁ : Spec α} {sp₂ : Spec β} {sp₃ : Spec γ}
    {f : β → State → α} {g : γ → State → β} (h₁ : Spec.Implies sp₁ sp₂ f) (h₂ : Spec.Implies sp₂ sp₃ g) :
    Spec.Implies sp₁ sp₃ (fun c s => f (g c s) s) :=
  ⟨fun c s h => h₁.pre _ s (h₂.pre c s h),
   fun c s h => Perm.le_trans (h₁.perm _ s (h₂.pre c s h)) (h₂.perm c s h),
   fun c s s' h hd => h₂.done c s s' h (h₁.done _ s s' (h₂.pre c s h) hd)⟩

/-- Same argument; the precondition, permission and endings compared directly. -/
theorem Spec.Implies.of_post {α : Type} {sp₁ sp₂ : Spec α}
    (hpre : ∀ a s, sp₂.pre a s → sp₁.pre a s)
    (hperm : ∀ a s, sp₂.pre a s → (sp₁.perm a s).le (sp₂.perm a s))
    (hpost : ∀ a s s', sp₂.pre a s → sp₁.post a s s' → sp₂.post a s s')
    (hexit : ∀ a s s', sp₂.pre a s → sp₁.onExit a s s' → sp₂.onExit a s s') :
    Spec.Implies sp₁ sp₂ (fun a _ => a) :=
  ⟨hpre, hperm, fun a s s' h hd => by
    rcases hd with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2⟩
    · exact .inl ⟨h1, h2, h3, hpost a s s' h h4⟩
    · exact .inr ⟨h1, hexit a s s' h h2⟩⟩

namespace Linux

theorem PReachK.mono {c : Code} {D : Dom} {Q R : State × Kern → Prop} (hQ : ∀ y, Q y → R y) :
    ∀ {x}, PReachK c D Q x → PReachK c D R x :=
  PReachK.bind (fun _ h => h) (fun y h => .done (hQ y h))

/-- `sp₁` implies `sp₂` at the process level (argument map `f`). -/
structure SpecP.Implies {α β : Type} (sp₁ : SpecP α) (sp₂ : SpecP β) (f : β → State → Kern → α) : Prop where
  pre : ∀ b s k, sp₂.pre b s k → sp₁.pre (f b s k) s k
  done : ∀ b s k y, sp₂.pre b s k → sp₁.Done (f b s k) (s, k) y → sp₂.Done b (s, k) y

theorem VerifiedProc.of_implies {α β : Type} {c : Code} {D : Dom} {e : Word} {sp₁ : SpecP α} {sp₂ : SpecP β}
    {f : β → State → Kern → α} (h : VerifiedProc c D e sp₁) (hi : SpecP.Implies sp₁ sp₂ f) :
    VerifiedProc c D e sp₂ := fun b s k he hpre =>
  PReachK.mono (fun y ⟨hf, hd⟩ => ⟨hf, hi.done b s k y hpre hd⟩) (h (f b s k) s k he (hi.pre b s k hpre))

theorem SpecP.Implies.refl {α : Type} (sp : SpecP α) : SpecP.Implies sp sp (fun a _ _ => a) :=
  ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩

theorem SpecP.Implies.trans {α β γ : Type} {sp₁ : SpecP α} {sp₂ : SpecP β} {sp₃ : SpecP γ}
    {f : β → State → Kern → α} {g : γ → State → Kern → β} (h₁ : SpecP.Implies sp₁ sp₂ f)
    (h₂ : SpecP.Implies sp₂ sp₃ g) : SpecP.Implies sp₁ sp₃ (fun c s k => f (g c s k) s k) :=
  ⟨fun c s k h => h₁.pre _ s k (h₂.pre c s k h),
   fun c s k y h hd => h₂.done c s k y h (h₁.done _ s k y (h₂.pre c s k h) hd)⟩

/-- Same argument; the precondition and the endings compared directly. -/
theorem SpecP.Implies.of_post {α : Type} {sp₁ sp₂ : SpecP α}
    (hpre : ∀ a s k, sp₂.pre a s k → sp₁.pre a s k)
    (hpost : ∀ a x y, sp₂.pre a x.1 x.2 → sp₁.post a x y → sp₂.post a x y)
    (hexit : ∀ a x y, sp₂.pre a x.1 x.2 → sp₁.onExit a x y → sp₂.onExit a x y) :
    SpecP.Implies sp₁ sp₂ (fun a _ _ => a) :=
  ⟨hpre, fun a s k y h hd => by
    rcases hd with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2⟩
    · exact .inl ⟨h1, h2, h3, hpost a (s, k) y h h4⟩
    · exact .inr ⟨h1, hexit a (s, k) y h h2⟩⟩

/-- The call rule through an implication: a callee proved at `sp₁`, used at `sp₂`. -/
theorem VerifiedProc.call_of_implies {α β : Type} {c : Code} {Dg D : Dom} {entry : Word} {sp₁ : SpecP α}
    {sp₂ : SpecP β} {f : β → State → Kern → α} {R : State × Kern → Prop} {s : State} {k : Kern}
    (hg : VerifiedProc c Dg entry sp₁) (hi : SpecP.Implies sp₁ sp₂ f) (b : β)
    (he : Entry Dg entry s) (hpre : sp₂.pre b s k) (hD : Dg.sub D)
    (kont : ∀ y, sp₂.Done b (s, k) y → PReachK c D R y) : PReachK c D R (s, k) :=
  VerifiedProc.call (hg.of_implies hi) b he hpre hD kont

end Linux
end NoCompiler
