import NoCompiler.Typed.Sound.Congr

/-
One instruction at a time (the proof's Lemmas 2, 3, 5, 6): the type after an
instruction, as the checker computes it, holds of the state after it.
-/
namespace NoCompiler.Typed

variable {f : Fn} {T : TokEnv} {P : Perm} {s0 : State} {ι0 : Val}

theorem STy.reg_setReg_type {S : STy} {rd r : Reg} {e : Option IExpr} {e' : IExpr}
    (h : (S.setReg rd e).regs.lookup r = some e') (hne : rd ≠ 0) :
    (r = rd ∧ e = some e') ∨ (r ≠ rd ∧ (r, e') ∈ S.regs) := by
  have hm := lookup_mem h
  unfold STy.setReg at hm; rw [if_neg hne] at hm
  cases e with
  | some e0 =>
    simp only [List.mem_cons, List.mem_filter, bne_iff_ne, ne_eq] at hm
    rcases hm with hm | ⟨hm, hne'⟩
    · cases hm; exact .inl ⟨rfl, rfl⟩
    · exact .inr ⟨hne', hm⟩
  | none =>
    simp only [List.mem_filter, bne_iff_ne, ne_eq] at hm
    exact .inr ⟨hm.2, hm.1⟩

/-- Writing a register: the new type and facts hold under the new valuation, which
    agrees with the old one on the type's and the protected variables. -/
theorem Inv.write {S : STy} {s : State} {ι ι' : Val} {F : TokFp} (hI : Inv f T P s0 ι0 S s ι F)
    {rd : Reg} (hrd : rd ≠ 2) {v : Word} {e : Option IExpr} {ps : List Constr}
    (hag : ∀ x ≤ S.maxVar, ι' x = ι x) (hp : ∀ x ∈ f.protectedVars, ι' x = ι x)
    (he : ∀ e', e = some e' → rd ≠ 0 → HasInt ι' v e') (hps : ∀ p ∈ ps, p.holds ι') (pc : Word) :
    Inv f T P s0 ι0 ((S.setReg rd e).addFacts ps) ((s.setReg rd v).setPc pc) ι' F := by
  have hI' := hI.congr hag hp
  by_cases h0 : rd = 0
  · subst h0
    have hs : s.setReg 0 v = s := by simp [State.setReg]
    have hS : S.setReg 0 e = S := by simp [STy.setReg]
    rw [hs, hS]
    refine ⟨?_, hI'.regs, hI'.prot, hI'.valid, hI'.sep, hI'.stack, hI'.perm, hI'.ids, hI'.sp, hI'.live,
      hI'.depth, hI'.slots, hI'.stackW, hI'.spAl, hI'.stackLe⟩
    intro p hp'; rcases List.mem_append.1 hp' with h | h
    · exact hps p h
    · exact hI'.facts p h
  · refine ⟨?_, ?_, hI'.prot, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hI'.stackW, hI'.spAl, hI'.stackLe⟩
    · intro p hp'; rcases List.mem_append.1 hp' with h | h
      · exact hps p h
      · exact hI'.facts p (by simp only [STy.setReg, if_neg h0] at h; exact h)
    · intro p hp'
      have hp'' : p ∈ (S.setReg rd e).regs := hp'
      simp only [STy.setReg, if_neg h0] at hp''
      simp only [State.setPc_reg, State.reg_setReg]
      split
      · rename_i hz
        have hm : p ∈ S.regs := by
          cases e with
          | some e0 =>
            simp only [List.mem_cons, List.mem_filter] at hp''
            rcases hp'' with h | ⟨h, -⟩
            · subst h; exact absurd hz h0
            · exact h
          | none => simp only [List.mem_filter] at hp''; exact hp''.1
        have := hI'.regs p hm
        simp only [State.reg, hz, if_true] at this; exact this
      · split
        · rename_i hz hq
          cases e with
          | some e0 =>
            simp only [List.mem_cons, List.mem_filter, bne_iff_ne] at hp''
            rcases hp'' with hp'' | ⟨-, hne⟩
            · subst hp''; exact he e0 rfl h0
            · exact absurd hq hne
          | none => simp only [List.mem_filter, bne_iff_ne] at hp''; exact absurd hq hp''.2
        · cases e with
          | some e0 =>
            simp only [List.mem_cons, List.mem_filter] at hp''
            rcases hp'' with hp'' | ⟨hm, -⟩
            · subst hp''; rename_i hq; exact absurd rfl hq
            · exact hI'.regs p hm
          | none => simp only [List.mem_filter] at hp''; exact hI'.regs p hp''.1
    · simpa [STy.addFacts, STy.setReg, h0] using hI'.valid
    · simpa [STy.addFacts, STy.setReg, h0] using hI'.sep
    · simpa [STy.addFacts, STy.setReg, h0] using hI'.stack
    · simpa [STy.addFacts, STy.setReg, h0] using hI'.perm
    · simpa [STy.addFacts, STy.setReg, h0] using hI'.ids
    · simp only [State.setPc_reg]; rw [State.reg_setReg_other _ _ _ _ (Ne.symm hrd |> fun h => by
        intro e; exact hrd e.symm)]; simpa [STy.addFacts, STy.setReg, h0] using hI.sp
    · simp [hI.live]
    · simpa [STy.addFacts, STy.setReg, h0] using hI'.depth
    · simpa [STy.addFacts, STy.setReg, h0] using hI'.slots

theorem Fn.freshAt_gt (f : Fn) (S : STy) : S.maxVar < f.freshAt S := by
  unfold Fn.freshAt; omega

theorem Fn.freshAt_ge (f : Fn) (S : STy) : f.fresh ≤ f.freshAt S := by
  unfold Fn.freshAt; omega

/-- Set variables from `x` on; agree below. -/
def setFrom (ι : Val) (x : Nat) (vs : List Int) : Val := fun (y : Nat) =>
  if x ≤ y ∧ y - x < vs.length then vs[y - x]?.getD 0 else ι y

theorem setFrom_below {ι : Val} {x y : Nat} {vs : List Int} (h : y < x) : setFrom ι x vs y = ι y := by
  unfold setFrom; rw [if_neg (by omega)]

theorem setFrom_at {ι : Val} {x : Nat} {vs : List Int} (i : Nat) (h : i < vs.length) :
    setFrom ι x vs (x + i) = vs[i]?.getD 0 := by
  unfold setFrom; rw [if_pos (by omega)]; congr; omega

/-- Fresh variables keep the invariant's view: below the fresh point, and protected. -/
theorem setFrom_fresh (hprot : ∀ x ∈ f.protectedVars, x < f.fresh) (S : STy) (ι : Val)
    (vs : List Int) :
    (∀ y : Nat, y ≤ S.maxVar → setFrom ι (f.freshAt S) vs y = ι y) ∧
    (∀ y : Nat, y ∈ f.protectedVars → setFrom ι (f.freshAt S) vs y = ι y) ∧
    (∀ y : Nat, y < f.fresh → setFrom ι (f.freshAt S) vs y = ι y) := by
  have h1 := f.freshAt_gt S; have h2 := f.freshAt_ge S
  refine ⟨fun y hy => setFrom_below (by omega), fun y hy => setFrom_below ?_,
    fun y hy => setFrom_below (by omega)⟩
  exact Nat.lt_of_lt_of_le (hprot y hy) h2

end NoCompiler.Typed

namespace NoCompiler.Typed

variable {f : Fn} {T : TokEnv} {P : Perm} {s0 : State} {ι0 : Val}

theorem STy.addFacts_nil (S : STy) : S.addFacts [] = S := by simp [STy.addFacts]

/-- A register gets an exact type. -/
theorem Inv.exact {S : STy} {s : State} {ι : Val} {F : TokFp} (hI : Inv f T P s0 ι0 S s ι F)
    {rd : Reg} (hrd : rd ≠ 2) {v : Word} {e : IExpr} (he : HasInt ι v e) (pc : Word) :
    Inv f T P s0 ι0 (S.setReg rd (some e)) ((s.setReg rd v).setPc pc) ι F := by
  have := hI.write (e := some e) (ps := []) hrd (ι' := ι) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun e' h _ => by simp only [Option.some.injEq] at h; subst h; exact he) (by simp) pc
  rwa [STy.addFacts_nil] at this

/-- A register becomes a fresh word. -/
theorem Inv.any (hprot : ∀ x ∈ f.protectedVars, x < f.fresh) {S : STy} {s : State} {ι : Val}
    {F : TokFp} (hI : Inv f T P s0 ι0 S s ι F) {rd : Reg} (hrd : rd ≠ 2) (v : Word) (pc : Word) :
    ∃ ι', (∀ y : Nat, y < f.fresh → ι' y = ι y) ∧
      Inv f T P s0 ι0 (Fn.anyWord S rd (f.freshAt S)) ((s.setReg rd v).setPc pc) ι' F := by
  obtain ⟨h1, h2, h3⟩ := setFrom_fresh hprot S ι [(v.toNat : Int)]
  have hx := setFrom_at (ι := ι) (x := f.freshAt S) (vs := [(v.toNat : Int)]) 0 (by simp)
  simp only [Nat.add_zero, List.getElem?_cons_zero, Option.getD_some] at hx
  unfold Fn.anyWord
  refine ⟨_, h3, hI.write (e := some (.var (f.freshAt S)))
    (ps := [.le (.lit 0) (.var (f.freshAt S)), .lt (.var (f.freshAt S)) (.lit (2 ^ 64))])
    hrd h1 h2 (fun e' he _ => ?_) ?_ pc⟩
  · simp only [Option.some.injEq] at he; subst he; exact hasInt_toNat _ _ _ hx
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    have := v.isLt
    rcases hp with rfl | rfl <;> simp [Constr.holds, Constr.eval, Constr.lt, hx] <;> omega

end NoCompiler.Typed
