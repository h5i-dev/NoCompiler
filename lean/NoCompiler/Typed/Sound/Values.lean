import NoCompiler.Typed.Sound.Main

/-
Functional correctness on top of the type check (design note, 手書きの機能証明に対して型が与えるもの).

For a leaf function the checker accepts, `Fn.check_sound_val` gives a stronger specification:
the signature's post together with an extra property `X` of the final state, from a value
invariant `J` that the proof supplies per point. `J` only has to be preserved along one machine
step between typed states, and at each such step the checker's invariant `Inv` holds on both
sides (`Fn.Typed`): register relations, bounds, alignment, capabilities and the frame are
already there, so `J` carries only what the types do not say (the values in memory).

The step lemma `Fn.step_typed` is the checker's one-step soundness (`Fn.runStep` with a runner
that remembers the step); `Reach.inv_dom` carries `J` through the run that `Fn.check_sound`
already gives.
-/
namespace NoCompiler.Reach
variable {c : Code} {P : Perm} {D : Dom}

/-- `inv` with the invariant preserved only by steps from states in the region (the only
    steps a `Reach` takes). -/
theorem inv_dom {Q I : State → Prop} (hI : ∀ u u', D.mem u.pc → I u → Step c P u u' → I u') {s}
    (h : Reach c P D Q s) (hs : I s) : Reach c P D (fun u => Q u ∧ I u) s := by
  induction h with
  | done hq => exact .done ⟨hq, hs⟩
  | step hd hex _ ih => exact .step hd hex (fun s' h' => ih s' h' (hI _ _ hd hs h'))
end NoCompiler.Reach

namespace NoCompiler.Typed

variable {f : Fn} {T : TokEnv}

/-- A typed state of `f`'s run from `s0` with argument `a`: at a point `k` that has a type `S`,
    the checker's invariant holds (for some valuation and token footprints). -/
def Fn.Typed (f : Fn) (T : TokEnv) (a : Val × TokFp) (s0 : State) (k : Nat) (s : State) : Prop :=
  ∃ S ι F, f.tyAt k = some S ∧ k < f.size ∧ s.pc = f.pcOf k ∧
    Inv f T ((f.sig.spec T).perm a s0) s0 (f.entryVal a.1 s0) S s ι F ∧ f.UnitFrame T a s0 F

/-- One machine step of a leaf function from a typed state: to a typed state, or out of the
    region with `Done` (the return). -/
theorem Fn.step_typed (hst : f.StructSpec) {c : Code} (hinstr : ∀ k < f.size, f.instr c k = true)
    (hnc : f.callees = []) {D : Dom} (hDf : ∀ k < f.size, D.mem (f.pcOf k))
    {a : Val × TokFp} {s0 : State} (he : Entry D f.entry s0) {k : Nat} {s : State}
    (ht : f.Typed T a s0 k s) {s' : State} (hstep : Step c ((f.sig.spec T).perm a s0) s s') :
    (∃ k', f.Typed T a s0 k' s') ∨ (Final D s' ∧ (f.sig.spec T).Done a s0 s') := by
  obtain ⟨S, ι, F, hS, hk, hpc, hI, hUF⟩ := ht
  have hsD : D.mem s.pc := hpc ▸ hDf k hk
  let G : State → Prop := fun u =>
    (∃ k', f.Typed T a s0 k' u) ∨ (Final D u ∧ (f.sig.spec T).Done a s0 u)
  let rn : Runner c ((f.sig.spec T).perm a s0) D (fun u => Final D u ∧ (f.sig.spec T).Done a s0 u) :=
    { R := fun u => u = s → ∀ u', Step c ((f.sig.spec T).perm a s0) u u' → G u'
      next := G
      later := G
      callee := fun _ _ _ => False
      later_next := fun _ h => h
      done := by
        intro u hq hu
        subst hu
        exact absurd hq.1 (by simp [Final, hsD, hI.live])
      done_later := fun _ hq => .inr hq
      exec := by
        intro u u₁ i _ _ hi _ hx hn _ u' hs'
        cases hs' with
        | exec _ hi' _ hx' =>
          rw [hi] at hi'; cases hi'; rw [hx] at hx'; cases hx'; exact hn
        | sys _ hi' _ _ =>
          rw [hi] at hi'; cases hi'; rw [exec_ecall] at hx; cases hx
      sys := by
        intro u _ _ hi _ _ hn _ u' hs'
        cases hs' with
        | exec _ hi' _ hx' =>
          rw [hi] at hi'; cases hi'; rw [exec_ecall] at hx'; cases hx'
        | sys _ _ _ hsys => exact hn _ hsys
      call := by
        intro _ _ _ _ _ _ _ _ _ _ _ _ hg
        exact hg.elim }
  have hcall : ∀ p ∈ f.callees, aligned p.1 4 ∧ ∃ Dg, rn.callee Dg p.1 (p.2.spec T) ∧ Dg.sub D ∧
      ∀ j < f.size, ¬ Dg.mem (f.pcOf j) := by simp [hnc]
  have hR : rn.R s := f.runStep hst hinstr hDf he rn hcall (fun r x h => f.entryVal_reg hst a.1 s0 h)
    (fun x h => f.entryVal_param hst a.1 s0 h) hS hk hpc hI hUF
    (fun F1 S1 s1 ι1 k' hpc' hI1 hUF1 hag he' => by
      unfold Fn.edge at he'
      split at he'
      · simp only [Bool.and_eq_true] at he'
        exact absurd (hI1.ent he'.2) (by simp [Constr.holds, Constr.eval])
      · rename_i S2 hS2
        obtain ⟨hk', hI2, -⟩ := f.edgeOk_sound hst he' hI1 hag
        exact .inl ⟨k', S2, _, F1, hS2, hk', hpc', hI2, hUF1⟩)
  exact hR rfl s' hstep

/-- **Functional correctness from the type check** (leaf functions). A function the checker
    accepts meets its signature with the extra post `X`, given a value invariant `J a s0 k s` at
    each point `k` that holds at the entry, is preserved by each step between typed states (both
    states satisfy the checker's invariant, `Fn.Typed`), and gives `X` at the return. -/
theorem Fn.check_sound_val (f : Fn) (c : Code) (T : TokEnv) (h : f.check c = true)
    (hnc : f.callees = []) (hp : f.sig.isPartial = false) {D : Dom}
    (hDf : ∀ k < f.size, D.mem (f.pcOf k))
    (J : (Val × TokFp) → State → Nat → State → Prop)
    (X : (Val × TokFp) → State → State → Prop)
    (h0 : ∀ a s0, Entry D f.entry s0 → (f.sig.spec T).pre a s0 → J a s0 0 s0)
    (hJ : ∀ a s0, Entry D f.entry s0 → (f.sig.spec T).pre a s0 → ∀ k s k' s',
      f.Typed T a s0 k s → J a s0 k s → Step c ((f.sig.spec T).perm a s0) s s' →
      f.Typed T a s0 k' s' → J a s0 k' s')
    (hX : ∀ a s0, Entry D f.entry s0 → (f.sig.spec T).pre a s0 → ∀ k s s',
      f.Typed T a s0 k s → J a s0 k s → Step c ((f.sig.spec T).perm a s0) s s' →
      Final D s' → (f.sig.spec T).Done a s0 s' → X a s0 s') :
    VerifiedImg c D f.entry
      { f.sig.spec T with post := fun a s s' => (f.sig.spec T).post a s s' ∧ X a s s' } := by
  intro a s0 he hpre
  have hM := f.check_sound c T h hp hDf (by simp [hnc]) a s0 he hpre
  unfold Fn.check at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨hso, hentry⟩, hinstr⟩ := h
  have hst := Fn.structOk_spec hso
  have hI0 := f.entry_inv (T := T) hst he hpre
  have ht0 : f.Typed T a s0 0 s0 := by
    unfold Fn.edge at hentry
    split at hentry
    · simp only [Bool.and_eq_true] at hentry
      exact absurd (hI0.ent hentry.2) (by simp [Constr.holds, Constr.eval])
    · rename_i S0 hS0
      obtain ⟨hk0, hI1, -⟩ := f.edgeOk_sound hst hentry hI0 (ιpre := f.entryVal a.1 s0) (fun _ _ => rfl)
      exact ⟨S0, _, a.2, hS0, hk0, by simp [Fn.pcOf, he.pc], hI1, Fn.unitFrame_entry a s0⟩
  have notFinal : ∀ {k u}, f.Typed T a s0 k u → ¬ Final D u := by
    rintro k u ⟨S, ι, F, -, hk, hpc, hI, -⟩ hf
    rcases hf with hf | hf
    · exact hf (hpc ▸ hDf k hk)
    · exact hf hI.live
  let I : State → Prop := fun u =>
    ((D.mem u.pc ∧ u.exit = none) → ∃ k, f.Typed T a s0 k u ∧ J a s0 k u) ∧
    (Final D u → (f.sig.spec T).Done a s0 u → X a s0 u)
  have hI0' : I s0 := ⟨fun _ => ⟨0, ht0, h0 a s0 he hpre⟩, fun hf => absurd hf (notFinal ht0)⟩
  have hpres : ∀ u u', D.mem u.pc → I u → Step c ((f.sig.spec T).perm a s0) u u' → I u' := by
    intro u u' hd hu hs
    obtain ⟨-, -, -, hl⟩ := hs.instrOk
    obtain ⟨k, htk, hJk⟩ := hu.1 ⟨hd, hl⟩
    rcases f.step_typed hst hinstr hnc hDf he htk hs with ⟨k', ht'⟩ | ⟨hf, hdone⟩
    · exact ⟨fun _ => ⟨k', ht', hJ a s0 he hpre k u k' u' htk hJk hs ht'⟩,
        fun hf => absurd hf (notFinal ht')⟩
    · refine ⟨fun hdl => absurd hf ?_, fun _ hd2 => hX a s0 he hpre k u u' htk hJk hs hf hd2⟩
      rintro (h1 | h1)
      · exact h1 hdl.1
      · exact h1 hdl.2
  unfold Exec at hM ⊢
  refine Reach.mono ?_ (Reach.inv_dom hpres hM hI0')
  rintro u ⟨⟨hfin, hdone⟩, -, hx⟩
  refine ⟨hfin, ?_⟩
  rcases hdone with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2⟩
  · exact .inl ⟨h1, h2, h3, h4, hx hfin (.inl ⟨h1, h2, h3, h4⟩)⟩
  · exact .inr ⟨h1, h2⟩

end NoCompiler.Typed
