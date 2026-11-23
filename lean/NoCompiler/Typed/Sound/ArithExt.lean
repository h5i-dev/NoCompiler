import NoCompiler.Typed.Sound.Step

/-
Soundness of `Fn.arithExt` (NoCompiler/Typed/ArithExt.lean), in the shape `Fn.arith_sound`
needs. Owned by agent U: each new rule there gets its case here.
-/
namespace NoCompiler.Typed

variable {f : Fn} {T : TokEnv} {P : Perm} {s0 : State} {ι0 : Val}

/-- A register-writing instruction writes its register and goes on. -/
theorem writesReg_exec {i : Instr} {rd : Reg} (hw : writesReg i = some rd) {s s' : State}
    (hx : exec i s = some s') : ∃ v, s' = (s.setReg rd v).setPc (s.pc + 4) := by
  cases i <;> simp only [writesReg, Option.some.injEq, reduceCtorEq] at hw <;> subst hw <;>
    simp only [exec, Option.some.injEq] at hx <;> exact ⟨_, hx.symm⟩

theorem Fn.arithExt_sound (hprot : ∀ x ∈ f.protectedVars, x < f.fresh) {S S' : STy} {s s' : State}
    {ι : Val} {F : TokFp} (hI : Inv f T P s0 ι0 S s ι F) {i : Instr} {rd : Reg}
    (hw : writesReg i = some rd) (hrd : rd ≠ 2) (ha : f.arithExt S i = some S')
    (hx : exec i s = some s') :
    ∃ ι', (∀ y : Nat, y < f.fresh → ι' y = ι y) ∧ Inv f T P s0 ι0 S' s' ι' F ∧ s'.pc = s.pc + 4 := by
  unfold Fn.arithExt at ha
  rw [hw] at ha
  simp only [Option.some.injEq] at ha; subst ha
  obtain ⟨v, rfl⟩ := writesReg_exec hw hx
  obtain ⟨ι', h1, h2⟩ := hI.any hprot hrd v _
  exact ⟨ι', h1, h2, by simp⟩

end NoCompiler.Typed
