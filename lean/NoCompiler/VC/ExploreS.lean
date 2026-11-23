import NoCompiler.VC.Explore
import NoCompiler.SFrameStack

/-!
# Explore in the structured semantics (round 4, QUEUE-C 2 (i), (ii))

`SReach.of_explore`: the same paths and obligations as `Reach.of_explore`, concluding a structured
run (`Struct.SReach`, NoCompiler/SSem.lean) instead of a machine run, so that T2 to T4
(NoCompiler/SFrame*.lean) apply to it. The only difference is an access marked as a slot candidate
(`Ob.canReadS`/`canWriteS`: an `ld`/`sd` with base `sp`): in the structured semantics it needs
either the permission or to be at a slot (`Ob.denS`), a slot step needing no permission.
-/
namespace NoCompiler

namespace Struct

/-- The structured run from the result of a step. -/
def SReach.opt (c : Code) (fr : Frame) (sp0 : Word) (P : Perm) (D : Dom) (Q : State → Prop) :
    Option State → Prop
  | none => False
  | some s => SReach c fr sp0 P D Q s

@[simp] theorem SReach.opt_some {c : Code} {fr : Frame} {sp0 : Word} {P : Perm} {D : Dom}
    {Q : State → Prop} {s : State} : SReach.opt c fr sp0 P D Q (some s) = SReach c fr sp0 P D Q s := rfl

attribute [irreducible] SReach.opt

/-- One instruction other than ECALL, permitted or a slot access. -/
theorem SReach.exec_step {c : Code} {fr : Frame} {sp0 : Word} {P : Perm} {D : Dom} {Q : State → Prop}
    {s : State} {i : Instr} (hd : D.mem s.pc) (hx : s.exit = none) (hi : c.instr s.pc = some i)
    (hok : InstrOk P i s ∨ slotAccess fr sp0 s i = true) (h : SReach.opt c fr sp0 P D Q (exec i s)) :
    SReach c fr sp0 P D Q s := by
  cases hxs : exec i s with
  | none => rw [hxs] at h; unfold SReach.opt at h; exact h.elim
  | some s₁ =>
    rw [hxs, SReach.opt_some] at h
    have hst : SStep c fr sp0 P s s₁ := hok.elim (fun h => .step (.exec hx hi h hxs)) (fun h => .slot hx hi h hxs)
    refine .step hd ⟨s₁, hst⟩ (fun s' h' => ?_)
    cases h' with
    | slot _ hi' _ hx' => rw [hi] at hi'; cases hi'; rw [hxs] at hx'; cases hx'; exact h
    | step h' =>
      cases h' with
      | exec _ hi' _ hx' => rw [hi] at hi'; cases hi'; rw [hxs] at hx'; cases hx'; exact h
      | sys _ hi' _ _ => rw [hi] at hi'; cases hi'; exact absurd hxs (by simp [exec_ecall])

end Struct

namespace VC.M

/-- An obligation in the structured semantics: a slot candidate at a slot needs no permission. -/
def Ob.denS (ρ : Nat → Word) (μ : Word → Byte) (P : Perm) (fr : Struct.Frame) (sp0 : Word) : Ob → Prop
  | .canReadS a w => P.canRead (a.den ρ μ) w ∨ (w = 8 ∧ fr.isSlot sp0 (a.den ρ μ) = true)
  | .canWriteS a w => P.canWrite (a.den ρ μ) w ∨ (w = 8 ∧ fr.isSlot sp0 (a.den ρ μ) = true)
  | o => o.den ρ μ P

def GOb.denS (ρ : Nat → Word) (μ : Word → Byte) (P : Perm) (fr : Struct.Frame) (sp0 : Word) (g : GOb) : Prop :=
  (∀ x ∈ g.cs, x.den ρ μ) → g.o.denS ρ μ P fr sp0

/-- A machine obligation is a structured one under the permission with the frame. -/
theorem Ob.den_of_denS {ρ : Nat → Word} {μ : Word → Byte} {P : Perm} {fr : Struct.Frame} {sp0 : Word}
    {o : Ob} (h : o.denS ρ μ P fr sp0) : o.den ρ μ (P.withFrame fr sp0) := by
  have hfr : ∀ a w, w = 8 → fr.isSlot sp0 a = true → (P.withFrame fr sp0).canWrite a w := by
    intro a w hw hs; subst hw
    exact .inr ⟨_, by simp [Perm.withFrame], Struct.isSlot_covers hs⟩
  cases o with
  | canReadS a w =>
    rcases h with h | h
    · exact (P.le_withFrame fr sp0).read _ _ h
    · exact Perm.canRead_of_canWrite (hfr _ _ h.1 h.2)
  | canWriteS a w =>
    rcases h with h | h
    · exact (P.le_withFrame fr sp0).write _ _ h
    · exact hfr _ _ h.1 h.2
  | aligned a w => exact h
  | canRead a w => exact (P.le_withFrame fr sp0).read _ _ h
  | canWrite a w => exact (P.le_withFrame fr sp0).write _ _ h

/-- `sstep_sound` in the structured semantics: the step exists, matches, and is permitted or a
    slot access. -/
theorem sstep_soundS {ρ : Nat → Word} {μ : Word → Byte} {P : Perm} {fr : Struct.Frame} {sp0 : Word}
    {S S' : SState} {s : State} {i : Instr} {obs : List Ob} (hm : Matches ρ μ S s)
    (h : sstep i S = some (S', obs)) (hob : ∀ o ∈ obs, o.denS ρ μ P fr sp0) :
    ∃ s', exec i s = some s' ∧ (InstrOk P i s ∨ Struct.slotAccess fr sp0 s i = true) ∧ Matches ρ μ S' s' := by
  obtain ⟨s', he, _, hm'⟩ := sstep_sound (P := P.withFrame fr sp0) hm h (fun o ho => Ob.den_of_denS (hob o ho))
  refine ⟨s', he, ?_, hm'⟩
  have hr := hm.2.2.1
  cases i with
  | load op rd rs1 off =>
    simp only [sstep, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h
    have h2 := hob _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    split at h2
    · rename_i hc
      obtain ⟨hs2, rfl⟩ := hc
      simp only [Ob.denS, addr_den hr] at h2
      rcases h2 with h2 | ⟨_, h2⟩
      · exact .inl h2
      · right; simp [Struct.slotAccess, hs2, h2]
    · simp only [Ob.denS, Ob.den, addr_den hr] at h2
      exact .inl h2
  | store op rs1 rs2 off =>
    simp only [sstep, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h
    have h2 := hob _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    split at h2
    · rename_i hc
      obtain ⟨hs2, rfl⟩ := hc
      simp only [Ob.denS, addr_den hr] at h2
      rcases h2 with h2 | ⟨_, h2⟩
      · exact .inl h2
      · right; simp [Struct.slotAccess, hs2, h2]
    · simp only [Ob.denS, Ob.den, addr_den hr] at h2
      exact .inl h2
  | ecall => simp [sstep] at h
  | _ => exact .inl trivial

theorem SReach.of_explore {fr : Struct.Frame} {sp0 : Word} {strict : Bool} {ρ : Nat → Word} {μ : Word → Byte} {c : Code} {P : Perm} {D : Dom}
    {Q : State → Prop} {cuts : List Word} {τ : List Event} {fetch : Nat → List (BitVec 32)}
    (hb : 4 * c.words.size < 2 ^ 64) (hfe : ∀ k, fetch k = c.words.toList.drop k) :
    ∀ {fuel : Nat} {first : Bool} {k : Nat} {ws : List (BitVec 32)} {S : SState} {cs : List Cond}
      {ends : List PEnd} {obs : List GOb} {s : State},
      explore c D cuts fetch strict fuel first k ws S cs = some (ends, obs) →
      c.words.toList.drop k = ws → S.pc = c.base + BitVec.ofNat 64 (4 * k) → Matches ρ μ S s →
      s.exit = none → s.trace = τ → (∀ x ∈ cs, x.den ρ μ) → (∀ o ∈ obs, o.denS ρ μ P fr sp0) →
      (∀ e ∈ ends, e.Next ρ μ (fun s' => s'.trace = τ → Q s')) → Struct.SReach c fr sp0 P D Q s
  | 0, _, _, _, _, _, _, _, _, h, _, _, _, _, _, _, _, _ => by simp [explore] at h
  | fuel + 1, first, k, ws, S, cs, ends, obs, s, h, hd, hpc, hm, hx, ht, hcs, hob, hN => by
    simp only [explore] at h
    split at h
    · -- a cut point
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      exact .done (hN _ (List.mem_singleton_self _) hcs s hm hx ht)
    split at h
    case isFalse => simp at h
    rename_i hD
    have hD' : D.mem s.pc := by rw [hm.2.1]; exact hD
    have hpcS : s.pc = S.pc := hm.2.1
    split at h
    · simp at h
    rename_i w ws'
    have hk : k < c.words.toList.length := by
      apply Nat.lt_of_not_le; intro hc
      rw [List.drop_eq_nil_of_le hc] at hd; simp at hd
    have hsz : c.words.toList.length = c.words.size := by simp
    have hk4 : 4 * (k + 1) < 2 ^ 64 := by omega
    have hw : c.words.toList[k]? = some w := by rw [← List.head?_drop, hd]; rfl
    have hfetch : ∀ i, decode w = some i → c.instr s.pc = some i := fun i hi => by
      rw [hpcS, hpc]; unfold Code.instr
      rw [Code.fetch_index c k (by omega), hw]; exact hi
    have hd₁ : c.words.toList.drop (k + 1) = ws' := by rw [← List.drop_drop, hd]; rfl
    have hpc₁ : S.pc + 4 = c.base + BitVec.ofNat 64 (4 * (k + 1)) := by rw [hpc]; exact pc_succ hk4
    split at h
    · -- a conditional branch
      rename_i op rs1 rs2 off hi
      split at h
      case isFalse => simp at h
      rename_i hal
      split at h
      case h_2 => simp at h
      rename_i k' hk'
      unfold both at h
      split at h
      case h_2 => simp at h
      rename_i e₁ o₁ e₂ o₂ h₁ h₂
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      have hra := (hm.2.2.1 rs1).symm
      have hrb := (hm.2.2.1 rs2).symm
      refine Struct.SReach.exec_step hD' hx (hfetch _ hi) (.inl trivial) ?_
      simp only [exec, jumpTo]
      cases hc : evalBr op (s.reg rs1) (s.reg rs2)
      · simp only [Bool.false_eq_true, ite_false, Struct.SReach.opt_some]
        rw [hpcS]
        exact SReach.of_explore hb hfe h₂ hd₁ hpc₁ (matches_setPc hm _) (by simpa using hx) (by simpa using ht)
          (fun x hx' => by
            simp only [List.mem_cons] at hx'
            rcases hx' with rfl | hx'
            · simp only [Cond.den]; rw [hra, hrb]; exact hc
            · exact hcs x hx')
          (fun o ho => hob o (List.mem_append_right _ ho))
          (fun e he => hN e (List.mem_append_right _ he))
      · rw [hpcS]
        simp only [ite_true, hal, Struct.SReach.opt_some]
        exact SReach.of_explore hb hfe h₁ (hfe _).symm (wordIdx_sound hk') (matches_setPc hm _) (by simpa using hx) (by simpa using ht)
          (fun x hx' => by
            simp only [List.mem_cons] at hx'
            rcases hx' with rfl | hx'
            · simp only [Cond.den]; rw [hra, hrb]; exact hc
            · exact hcs x hx')
          (fun o ho => hob o (List.mem_append_left _ ho))
          (fun e he => hN e (List.mem_append_left _ he))
    · -- jal
      rename_i rd off hi
      split at h
      case isFalse => simp at h
      rename_i hal
      split at h
      case h_2 => simp at h
      rename_i k' hk'
      split at h
      · simp at h
      refine Struct.SReach.exec_step hD' hx (hfetch _ hi) (.inl trivial) ?_
      simp only [exec, jumpTo]
      rw [hpcS]
      simp only [hal, ite_true, Struct.SReach.opt_some]
      exact SReach.of_explore hb hfe h (hfe _).symm (wordIdx_sound hk')
        (matches_setReg_setPc hm rd _ _ (by first | rfl | (rw [hpcS]; rfl)) _) (by simpa using hx) (by simpa using ht) hcs hob hN
    · -- jalr: the return, or a jump to a known address
      rename_i rd rs1 off hi
      split at h
      · rename_i hc; obtain ⟨rfl, rfl, rfl⟩ := hc
        simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hal, hq⟩ := hN _ (List.mem_singleton_self _) hcs s hm hx
        have h1 := (hm.2.2.1 1).symm
        rw [h1] at hal hq
        refine Struct.SReach.exec_step hD' hx (hfetch _ hi) (.inl trivial) ?_
        have hz : s.reg 1 + BitVec.signExtend 64 (0 : BitVec 12) = s.reg 1 := by
          rw [show BitVec.signExtend 64 (0 : BitVec 12) = 0 by decide]; bv_omega
        simp only [exec, jumpTo, setReg_x0', hz, hal, ite_true, Struct.SReach.opt_some]
        exact .done (hq (by simpa using ht))
      · split at h
        case h_2 => simp at h
        rename_i v hv
        split at h
        case isFalse => simp at h
        rename_i hal
        split at h
        case h_2 => simp at h
        rename_i k' hk'
        split at h
        · simp at h
        have hrs : s.reg rs1 = v := by rw [hm.2.2.1 rs1, hv]; rfl
        refine Struct.SReach.exec_step hD' hx (hfetch _ hi) (.inl trivial) ?_
        simp only [exec, jumpTo, hrs]
        simp only [hal, ite_true, Struct.SReach.opt_some]
        exact SReach.of_explore hb hfe h (hfe _).symm (wordIdx_sound hk')
          (matches_setReg_setPc hm rd _ _ (by first | rfl | (rw [hpcS]; rfl)) _) (by simpa using hx) (by simpa using ht) hcs hob hN
    · -- a straight-line instruction
      rename_i i _ _ _ hi
      split at h
      case h_2 => simp at h
      rename_i S₁ o₁ hst
      cases hr : explore c D cuts fetch strict fuel false (k + 1) ws' S₁ cs with
      | none => rw [hr] at h; simp at h
      | some p =>
        obtain ⟨e₂, o₂⟩ := p
        rw [hr] at h; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨s₁, he, hok, hm₁⟩ := sstep_soundS (P := P) (fr := fr) (sp0 := sp0) hm hst
          (fun o ho => hob ⟨cs, o⟩ (List.mem_append_left _ (List.mem_map_of_mem ho)) hcs)
        have hS₁ : S₁.pc = c.base + BitVec.ofNat 64 (4 * (k + 1)) := by
          rw [← hpc₁]
          cases i <;> simp only [sstep, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hst <;>
            (try obtain ⟨rfl, rfl⟩ := hst) <;> rfl
        exact Struct.SReach.exec_step hD' hx (hfetch _ hi) hok
          (by rw [he, Struct.SReach.opt_some]
              exact SReach.of_explore hb hfe hr hd₁ hS₁ hm₁ ((exec_exit he).trans hx) ((exec_trace he).trans ht) hcs
                (fun o ho => hob o (List.mem_append_right _ ho)) hN)
    · simp at h


/-- What the checker proves on the machine holds in the structured semantics (a slot candidate by
    its permission). -/
theorem Ob.denS_of_den {ρ : Nat → Word} {μ : Word → Byte} {P : Perm} {fr : Struct.Frame} {sp0 : Word}
    {o : Ob} (h : o.den ρ μ P) : o.denS ρ μ P fr sp0 := by
  cases o <;> first | exact .inl h | exact h

/-- Every obligation, structured, as one conjunction. -/
def allObS (ρ : Nat → Word) (μ : Word → Byte) (P : Perm) (fr : Struct.Frame) (sp0 : Word) : List GOb → Prop
  | [] => True
  | o :: os => o.denS ρ μ P fr sp0 ∧ allObS ρ μ P fr sp0 os

theorem allObS_mem {ρ : Nat → Word} {μ : Word → Byte} {P : Perm} {fr : Struct.Frame} {sp0 : Word} :
    ∀ {os : List GOb}, allObS ρ μ P fr sp0 os → ∀ o ∈ os, o.denS ρ μ P fr sp0
  | [], _, _, h => by simp at h
  | _ :: _, ⟨h₁, h₂⟩, _, h => by
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact h₁
    · exact allObS_mem h₂ _ h

/-- `exploreVC` in the structured semantics. -/
def exploreVCS (ρ : Nat → Word) (μ : Word → Byte) (P : Perm) (fr : Struct.Frame) (sp0 : Word)
    (Q : State → Prop) (facts : List Fact) (c : Code) (D : Dom) (cuts : List Word) (fuel k : Nat) (p : Word)
    (fetch : Nat → List (BitVec 32) := fun k => c.words.toList.drop k) (strict : Bool := false) : Prop :=
  match exploreR c D cuts fetch fuel k p facts strict with
  | some (ends, res) => allObS ρ μ P fr sp0 res ∧ allNext ρ μ Q ends
  | none => False

/-- `Reach.of_exploreAtT` concluding a structured run. -/
theorem SReach.of_exploreAtT {c : Code} {strict : Bool} {P : Perm} {fr : Struct.Frame} {sp0 : Word} {D : Dom}
    {Q : State → Prop} {facts : List Fact}
    {cuts : List Word} {fuel k : Nat} {p : Word} {s : State} {fetch : Nat → List (BitVec 32)}
    (hb : 4 * c.words.size < 2 ^ 64) (hfe : ∀ k, fetch k = c.words.toList.drop k)
    (hk : p = c.base + BitVec.ofNat 64 (4 * k)) (hpc : s.pc = p) (hx : s.exit = none)
    (hf : ∀ f ∈ facts, f.den (ρOf s) P)
    (hvc : exploreVCS (ρOf s) s.mem P fr sp0 (fun s' => s'.trace = s.trace → Q s') facts c D cuts fuel k p fetch strict) :
    Struct.SReach c fr sp0 P D Q s := by
  unfold exploreVCS exploreR at hvc
  cases h : explore c D cuts fetch strict fuel true k (fetch k) (SState.init p) [] with
  | none => rw [h] at hvc; exact hvc.elim
  | some r =>
    obtain ⟨ends, obs⟩ := r
    rw [h] at hvc
    simp only [Option.map_some] at hvc
    refine SReach.of_explore (τ := s.trace) hb hfe h (hfe k).symm hk (matches_init hpc) hx rfl (by simp)
      (fun o ho => ?_) (allNext_mem hvc.2)
    cases hc : o.o.check facts
    · exact allObS_mem hvc.1 o (List.mem_filter.2 ⟨ho, by simp [hc]⟩)
    · exact fun _ => Ob.denS_of_den (Ob.check_sound hf hc)

end VC.M
end NoCompiler
