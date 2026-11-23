import NoCompiler.Typed.Sound.ArithI
import NoCompiler.Typed.Sound.ArithCmp
import NoCompiler.Typed.Sound.ArithDiv
import NoCompiler.Typed.Sound.ArithSh
import NoCompiler.Typed.Sound.ArithConst

/-
Soundness of `Fn.arithExt` (NoCompiler/Typed/ArithExt.lean), in the shape `Fn.arith_sound`
needs. Owned by agent U. The rules by class: Sound/ArithI, ArithCmp, ArithDiv, ArithSh,
ArithConst.lean; their common part: ArithBase, ArithFacts, WordFacts.lean.
-/
namespace NoCompiler.Typed

variable {f : Fn} {T : TokEnv} {P : Perm} {s0 : State} {ι0 : Val}

/-- The rules not in `arith`, by class (ArithI/Cmp/Div/Sh.lean). -/
theorem Fn.arith2_sound (hprot : ∀ x ∈ f.protectedVars, x < f.fresh) {S S' : STy} {s s' : State}
    {ι : Val} {F : TokFp} (hI : Inv f T P s0 ι0 S s ι F) {i : Instr} {rd : Reg}
    (hw : writesReg i = some rd) (hrd : rd ≠ 2) (ha : f.arith2 S i = some S')
    (hx : exec i s = some s') :
    ∃ ι', (∀ y : Nat, y < f.fresh → ι' y = ι y) ∧ Inv f T P s0 ι0 S' s' ι' F ∧ s'.pc = s.pc + 4 := by
  unfold Fn.arith2 at ha
  split at ha
  · rename_i S1 h1
    simp only [Option.some.injEq] at ha; subst ha
    exact f.arith2I_sound hprot hI hw hrd h1 hx
  · split at ha
    · rename_i S1 h1
      simp only [Option.some.injEq] at ha; subst ha
      exact f.arith2Cmp_sound hprot hI hw hrd h1 hx
    · split at ha
      · rename_i S1 h1
        simp only [Option.some.injEq] at ha; subst ha
        exact f.arith2Div_sound hprot hI hw hrd h1 hx
      · exact f.arith2Sh_sound hprot hI hw hrd ha hx

theorem Fn.arithExt_sound (hprot : ∀ x ∈ f.protectedVars, x < f.fresh) {S S' : STy} {s s' : State}
    {ι : Val} {F : TokFp} (hI : Inv f T P s0 ι0 S s ι F) {i : Instr} {rd : Reg}
    (hw : writesReg i = some rd) (hrd : rd ≠ 2) (ha : f.arithExt S i = some S')
    (hx : exec i s = some s') :
    ∃ ι', (∀ y : Nat, y < f.fresh → ι' y = ι y) ∧ Inv f T P s0 ι0 S' s' ι' F ∧ s'.pc = s.pc + 4 := by
  unfold Fn.arithExt at ha
  split at ha
  · rename_i S1 h1
    simp only [Option.some.injEq] at ha; subst ha
    exact Fn.fold_sound hI hw hrd h1 hx
  · split at ha
    · rename_i S1 h1
      simp only [Option.some.injEq] at ha; subst ha
      exact f.andConst_sound hprot hI hw hrd h1 hx
    · split at ha
      · rename_i S1 h1
        simp only [Option.some.injEq] at ha; subst ha
        exact f.arith2_sound hprot hI hw hrd h1 hx
      · rw [hw] at ha
        simp only [Option.some.injEq] at ha; subst ha
        obtain ⟨v, rfl⟩ := writesReg_exec hw hx
        obtain ⟨ι', h1, h2⟩ := hI.any hprot hrd v _
        exact ⟨ι', h1, h2, by simp⟩

end NoCompiler.Typed
