import NoCompiler.VC.ExploreS
import NoCompiler.VC.Frame

/-!
# Calls and the top-level rule for structured runs (round 4, QUEUE-C 2 (iii))

* `SReach.trans`, `CallQS` and `SReach.of_exploreCalls`: as `Reach.trans`, `CallQ` and
  `Reach.of_exploreCalls` (NoCompiler/VC/Frame.lean), for structured runs.
* `VerifiedImg.callS`: the call rule in the structured semantics: the callee's run is a call node
  (`SReach.call`), which a caller sees only through what the callee guarantees.
* `VerifiedImg.ofS`: a function whose every run from its entry is a structured run under `Ps`
  is verified, when `Ps` with the frame is within the specification's permission (T1,
  `SExec.sound`).
-/
namespace NoCompiler

namespace Struct

theorem SReach.trans {c : Code} {fr : Frame} {sp0 : Word} {P : Perm} {D : Dom} {Q₁ Q₂ : State → Prop}
    {s : State} (h : SReach c fr sp0 P D Q₁ s) (k : ∀ s', Q₁ s' → SReach c fr sp0 P D Q₂ s') :
    SReach c fr sp0 P D Q₂ s := by
  induction h with
  | done hq => exact k _ hq
  | step hd hex _ ih => exact .step hd hex ih
  | call hr hd _ ih => exact .call hr hd ih

theorem writable_of_le {P Q : Perm} (h : P.le Q) {x : Word} (hx : P.writable x) : Q.writable x := by
  obtain ⟨r, hr, hm⟩ := hx
  rcases h.write x 1 (.inr ⟨r, hr, by unfold Region.covers; unfold Region.mem at hm; omega⟩) with h0 | ⟨r', hr', hc⟩
  · cases h0
  · exact ⟨r', hr', by unfold Region.covers at hc; unfold Region.mem; omega⟩

end Struct

open Struct in
/-- The call rule, structured: a call to a verified function is a call node; the caller goes on
    from every way the callee can end. -/
theorem VerifiedImg.callS {α : Type} {c : Code} {fr : Frame} {sp0 : Word} {Dg D : Dom} {entry : Word}
    {sp : Spec α} {P : Perm} {Q : State → Prop} {s : State} (hg : VerifiedImg c Dg entry sp) (a : α)
    (he : Entry Dg entry s) (hpre : sp.pre a s) (hD : Dg.sub D) (hP : (sp.perm a s).le P)
    (k : ∀ s', sp.Done a s s' → (∀ x, ¬ (sp.perm a s).writable x → s'.mem x = s.mem x) →
      SReach c fr sp0 P D Q s') : SReach c fr sp0 P D Q s := by
  have hr : Reach c P D (fun s' => sp.Done a s s' ∧ ∀ x, ¬ (sp.perm a s).writable x → s'.mem x = s.mem x) s :=
    Reach.bind (hg.frame a s he hpre) hP hD (fun s' ⟨_, hd, hm⟩ => .done ⟨hd, hm⟩)
  refine .call hr (fun s' ⟨hd, hm⟩ => ?_) (fun s' ⟨hd, hm⟩ => k s' hd hm)
  rcases hd with ⟨hx, hpc, hpres, _⟩ | ⟨hx, _⟩
  · exact .inl ⟨hx, hpc, hpres, fun x hx' => hm x (fun hw => hx' (writable_of_le hP hw))⟩
  · exact .inr hx

/-- The top-level rule: structured runs from the entry make a verified function (T1). -/
theorem VerifiedImg.ofS {α : Type} {c : Code} {D : Dom} {entry : Word} {sp : Spec α}
    (fr : Struct.Frame) (Ps : α → State → Perm)
    (hle : ∀ a s, ((Ps a s).withFrame fr (s.reg 2)).le (sp.perm a s))
    (h : ∀ a s, Entry D entry s → sp.pre a s → Struct.SExec c fr (s.reg 2) (Ps a s) D (sp.Done a s) s) :
    VerifiedImg c D entry sp := by
  intro a s he hpre
  exact Reach.bind (Struct.SExec.sound (h a s he hpre)) (hle a s) (fun _ h => h) (fun _ h => .done h)

namespace VC.M
open Struct

/-- At a callee's entry the rest of the structured run, elsewhere `Q`. -/
def CallQS (c : Code) (fr : Frame) (sp0 : Word) (P : Perm) (D : Dom) (Q : State → Prop) (ces : List Word)
    (s : State) : Prop :=
  if s.pc ∈ ces then SReach c fr sp0 P D Q s else Q s

theorem SReach.of_exploreCalls {c : Code} {fr : Frame} {sp0 : Word} {P : Perm} {D : Dom}
    {Q : State → Prop} {facts : List Fact}
    {cuts ces : List Word} {fuel k : Nat} {p : Word} {s : State} {fetch : Nat → List (BitVec 32)}
    (hb : 4 * c.words.size < 2 ^ 64) (hfe : ∀ k, fetch k = c.words.toList.drop k)
    (hk : p = c.base + BitVec.ofNat 64 (4 * k)) (hpc : s.pc = p) (hx : s.exit = none)
    (hf : ∀ f ∈ facts, f.den (ρOf s) P)
    (hvc : exploreVCS (ρOf s) s.mem P fr sp0 (fun s' => s'.trace = s.trace → CallQS c fr sp0 P D Q ces s')
      facts c D (cuts ++ ces) fuel k p fetch) :
    SReach c fr sp0 P D Q s :=
  Struct.SReach.trans (SReach.of_exploreAtT hb hfe hk hpc hx hf hvc) fun s' h => by
    unfold CallQS at h
    split at h
    · exact h
    · exact .done h

theorem CallQS.call {c : Code} {fr : Frame} {sp0 : Word} {P : Perm} {D : Dom} {Q : State → Prop}
    {ces : List Word} {s : State} (h : s.pc ∈ ces) (hr : SReach c fr sp0 P D Q s) :
    CallQS c fr sp0 P D Q ces s := by
  simp only [CallQS, h, ite_true]; exact hr

theorem CallQS.other {c : Code} {fr : Frame} {sp0 : Word} {P : Perm} {D : Dom} {Q : State → Prop}
    {ces : List Word} {s : State} (h : s.pc ∉ ces) (hq : Q s) : CallQS c fr sp0 P D Q ces s := by
  simp only [CallQS, h, ite_false]; exact hq

/-- A return end, structured (as `CallQ.ret`). -/
theorem CallQS.ret {c : Code} {fr : Frame} {sp0 : Word} {P : Perm} {D Dc : Dom} {Q : State → Prop}
    {ces : List Word} {entry : Word} {s0 s' : State} {X : Word} {τ : List Event} (he : Entry D entry s0)
    (hcalls : ces.all (fun x => decide (D.mem x)) = true) (hX : X = s0.reg 1)
    (hq : s'.trace = τ → Q (s'.setPc (s0.reg 1))) :
    NoCompiler.aligned (X &&& ~~~1) 4 ∧
      ((s'.setPc (X &&& ~~~1)).trace = τ → CallQS c fr sp0 P Dc Q ces (s'.setPc (X &&& ~~~1))) := by
  have hm : s0.reg 1 &&& ~~~1 = s0.reg 1 := and_not_one_of_aligned he.retAligned
  subst hX
  rw [hm]
  refine ⟨he.retAligned, fun ht => CallQS.other (fun hm' => he.ret ?_) (hq (by simpa using ht))⟩
  exact of_decide_eq_true (List.all_eq_true.1 hcalls _ hm')

end VC.M
end NoCompiler
