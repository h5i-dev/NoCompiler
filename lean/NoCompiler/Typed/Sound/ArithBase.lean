import NoCompiler.Typed.Sound.Step
import NoCompiler.Typed.Sound.WordFacts

/-
The arithmetic rules' common part: register writes, fresh variables (`Inv.fresh`), the
representatives (`urep`/`srep`), constant folding, the sign-extended low word.
-/
namespace NoCompiler.Typed

variable {f : Fn} {T : TokEnv} {P : Perm} {s0 : State} {ι0 : Val}

/-- A register-writing instruction writes its register and goes on. -/
theorem writesReg_exec {i : Instr} {rd : Reg} (hw : writesReg i = some rd) {s s' : State}
    (hx : exec i s = some s') : ∃ v, s' = (s.setReg rd v).setPc (s.pc + 4) := by
  cases i <;> simp only [writesReg, Option.some.injEq, reduceCtorEq] at hw <;> subst hw <;>
    simp only [exec, Option.some.injEq] at hx <;> exact ⟨_, hx.symm⟩

theorem STy.reg_maxVar' {S : STy} {r : Reg} {e : IExpr} (h : S.reg r = some e) :
    e.maxVar ≤ S.maxVar := by
  unfold STy.reg at h
  split at h
  · cases h; simp [IExpr.maxVar, IExpr.lit]
  · exact STy.le_maxVar_reg (p := (r, e)) (lookup_mem h)

/-- `exec` of a register-writing instruction writes `Fn.pureVal` of its source registers. -/
theorem exec_pureVal {i : Instr} {rd : Reg} {s s' : State} {v : Word}
    (hw : writesReg i = some rd)
    (hv : Fn.pureVal i (s.reg (Fn.srcRegs i).1) (s.reg (Fn.srcRegs i).2) = some v)
    (hx : exec i s = some s') : s' = (s.setReg rd v).setPc (s.pc + 4) := by
  cases i <;> simp_all [writesReg, Fn.pureVal, Fn.srcRegs, exec]

/-- The generic rule: `rd` becomes `e` and the facts `ps` are added, both over fresh
    variables `x, x+1, …` (`x = f.freshAt S`) with witness values `vs`. -/
theorem Inv.fresh (hprot : ∀ x ∈ f.protectedVars, x < f.fresh) {S : STy} {s : State} {ι : Val}
    {F : TokFp} (hI : Inv f T P s0 ι0 S s ι F) {rd : Reg} (hrd : rd ≠ 2) (vs : List Int)
    (e : IExpr) (ps : List Constr) (v : Word)
    (hv : HasInt (setFrom ι (f.freshAt S) vs) v e)
    (hps : ∀ p ∈ ps, p.holds (setFrom ι (f.freshAt S) vs)) (pc : Word) :
    ∃ ι', (∀ y : Nat, y < f.fresh → ι' y = ι y) ∧
      Inv f T P s0 ι0 ((S.setReg rd (some e)).addFacts ps) ((s.setReg rd v).setPc pc) ι' F := by
  obtain ⟨h1, h2, h3⟩ := setFrom_fresh hprot S ι vs
  exact ⟨_, h3, hI.write hrd h1 h2 (fun e' he _ => by
    simp only [Option.some.injEq] at he; subst he; exact hv) hps pc⟩

/-- `Inv.fresh` in the shape of the arithmetic lemmas' conclusion. -/
theorem Inv.fresh4 (hprot : ∀ x ∈ f.protectedVars, x < f.fresh) {S : STy} {s : State} {ι : Val}
    {F : TokFp} (hI : Inv f T P s0 ι0 S s ι F) {rd : Reg} (hrd : rd ≠ 2) (vs : List Int)
    (e : IExpr) (ps : List Constr) (v : Word)
    (hv : HasInt (setFrom ι (f.freshAt S) vs) v e)
    (hps : ∀ p ∈ ps, p.holds (setFrom ι (f.freshAt S) vs)) :
    ∃ ι', (∀ y : Nat, y < f.fresh → ι' y = ι y) ∧
      Inv f T P s0 ι0 ((S.setReg rd (some e)).addFacts ps) ((s.setReg rd v).setPc (s.pc + 4)) ι' F ∧
      ((s.setReg rd v).setPc (s.pc + 4)).pc = s.pc + 4 := by
  obtain ⟨ι', g1, g2⟩ := hI.fresh hprot hrd vs e ps v hv hps (s.pc + 4)
  exact ⟨ι', g1, g2, by simp⟩

/-- An expression of the type before keeps its value under the fresh valuation. -/
theorem Fn.eval_setFrom_old {S : STy} {e : IExpr} (h : e.maxVar ≤ S.maxVar) (ι : Val)
    (vs : List Int) : e.eval (setFrom ι (f.freshAt S) vs) = e.eval ι :=
  IExpr.eval_congr_max (fun y hy => setFrom_below (by have := f.freshAt_gt S; omega))


/-! ### Representatives and comparisons -/

theorem Fn.urep_spec {S : STy} {s : State} {ι : Val} {F : TokFp} (hI : Inv f T P s0 ι0 S s ι F)
    {e : IExpr} {w : Word} (hre : HasInt ι w e) (hem : e.maxVar ≤ S.maxVar) {x : Var} {ι' : Val}
    (hag : ∀ y ≤ S.maxVar, ι' y = ι y) (hx : ι' x = w.toNat) :
    (Fn.urep S x e).1.eval ι' = w.toNat ∧ ∀ p ∈ (Fn.urep S x e).2, p.holds ι' := by
  have hev : e.eval ι' = e.eval ι := IExpr.eval_congr_max (fun y hy => hag y (by omega))
  have hw := w.isLt
  unfold Fn.urep
  split
  · rename_i hin
    have hin := hI.ent hin
    simp only [Constr.holds, Constr.eval, Bool.and_eq_true, decide_eq_true_eq, Constr.lt,
      IExpr.eval_lit, IExpr.eval_add] at hin
    have ht := hre.toNat_eq hin.1 (by omega)
    exact ⟨by rw [hev]; omega, by simp⟩
  · refine ⟨by simp [hx], ?_⟩
    intro p hp
    unfold HasInt at hre
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;>
      simp only [Constr.holds, Constr.eval, decide_eq_true_eq, Constr.lt, Constr.eqMod,
        IExpr.eval_var, IExpr.eval_lit, IExpr.eval_add, IExpr.eval_sub, hx, hev] <;> omega

theorem Fn.srep_spec {S : STy} {s : State} {ι : Val} {F : TokFp} (hI : Inv f T P s0 ι0 S s ι F)
    {e : IExpr} {w : Word} (hre : HasInt ι w e) (hem : e.maxVar ≤ S.maxVar) {x : Var} {ι' : Val}
    (hag : ∀ y ≤ S.maxVar, ι' y = ι y) (hx : ι' x = w.toInt) :
    (Fn.srep S x e).1.eval ι' = w.toInt ∧ ∀ p ∈ (Fn.srep S x e).2, p.holds ι' := by
  have hev : e.eval ι' = e.eval ι := IExpr.eval_congr_max (fun y hy => hag y (by omega))
  have hw := w.isLt
  have hc := BitVec.toInt_eq_toNat_cond w
  unfold HasInt at hre
  unfold Fn.srep
  split
  · rename_i hin
    have hin := hI.ent hin
    simp only [Constr.holds, Constr.eval, Bool.and_eq_true, decide_eq_true_eq, Constr.lt,
      IExpr.eval_lit, IExpr.eval_add] at hin
    refine ⟨?_, by simp⟩
    rw [hev]; split at hc <;> omega
  · refine ⟨by simp [hx], ?_⟩
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;>
      simp only [Constr.holds, Constr.eval, decide_eq_true_eq, Constr.lt, Constr.eqMod,
        IExpr.eval_var, IExpr.eval_lit, IExpr.eval_add, IExpr.eval_sub, hx, hev] <;>
      split at hc <;> omega

theorem Fn.fold_sound {S S' : STy} {s s' : State} {ι : Val} {F : TokFp}
    (hI : Inv f T P s0 ι0 S s ι F) {i : Instr} {rd : Reg}
    (hw : writesReg i = some rd) (hrd : rd ≠ 2) (ha : Fn.fold S i = some S')
    (hx : exec i s = some s') :
    ∃ ι', (∀ y : Nat, y < f.fresh → ι' y = ι y) ∧ Inv f T P s0 ι0 S' s' ι' F ∧ s'.pc = s.pc + 4 := by
  unfold Fn.fold at ha
  rw [hw] at ha
  split at ha
  · rename_i rd' c1 c2 hrd' h1 h2
    cases hrd'
    cases hp : Fn.pureVal i (BitVec.ofInt 64 c1) (BitVec.ofInt 64 c2) with
    | none => rw [hp] at ha; cases ha
    | some v =>
      rw [hp] at ha
      simp only [Option.map_some, Option.some.injEq] at ha
      subst ha
      have e1 := eq_ofInt_of_hasInt (STy.reg_hasInt hI.regs h1)
      have e2 := eq_ofInt_of_hasInt (STy.reg_hasInt hI.regs h2)
      rw [← e1, ← e2] at hp
      have := exec_pureVal hw hp hx
      subst this
      exact ⟨ι, fun _ _ => rfl, hI.exact hrd (hasInt_toNat' (by simp [IExpr.eval_lit])) _, by simp⟩
  · cases ha

theorem setFrom_x {ι : Val} {x : Nat} {v : Int} {vs : List Int} :
    setFrom ι x (v :: vs) x = v := by
  have := setFrom_at (ι := ι) (x := x) (vs := v :: vs) 0 (by simp)
  simpa using this

theorem setFrom_x1 {ι : Val} {x : Nat} {v w : Int} {vs : List Int} :
    setFrom ι x (v :: w :: vs) (x + 1) = w := by
  have := setFrom_at (ι := ι) (x := x) (vs := v :: w :: vs) 1 (by simp)
  simpa using this

theorem setFrom_x2 {ι : Val} {x : Nat} {v w z : Int} {vs : List Int} :
    setFrom ι x (v :: w :: z :: vs) (x + 2) = z := by
  have := setFrom_at (ι := ι) (x := x) (vs := v :: w :: z :: vs) 2 (by simp)
  simpa using this

theorem Fn.urep_fst_of_nil {S : STy} {x : Var} {e : IExpr} (h : (Fn.urep S x e).2 = []) :
    (Fn.urep S x e).1 = e := by
  unfold Fn.urep at *; split <;> simp_all

theorem Fn.urep_nil_ent {S : STy} {x : Var} {e : IExpr} (h : (Fn.urep S x e).2 = []) :
    S.ent (.and (.le (.lit 0) e) (.lt e (.lit (2 ^ 64)))) = true := by
  unfold Fn.urep at h
  split at h
  · assumption
  · simp at h

theorem IExpr.maxVar_smul' (k : Int) (a : IExpr) : (a.smul k).maxVar = a.maxVar := by
  unfold IExpr.maxVar IExpr.smul
  simp only
  generalize a.terms = ts
  induction ts with
  | nil => rfl
  | cons t r ih => simp only [List.map_cons, List.foldr_cons]; rw [ih]

/-- The type `word32` gives a sign-extended 32-bit value `z` that is `e` modulo 2^32. -/
theorem Inv.word32' (hprot : ∀ x ∈ f.protectedVars, x < f.fresh) {S : STy} {s : State} {ι : Val}
    {F : TokFp} (hI : Inv f T P s0 ι0 S s ι F) {rd : Reg} (hrd : rd ≠ 2) {e : IExpr}
    (hem : e.maxVar ≤ S.maxVar) (z : BitVec 32) (hz : ((z.toNat : Int) - e.eval ι) % 2 ^ 32 = 0) :
    ∃ ι', (∀ y : Nat, y < f.fresh → ι' y = ι y) ∧
      Inv f T P s0 ι0 (Fn.word32 S rd (f.freshAt S) e) ((s.setReg rd (z.signExtend 64)).setPc (s.pc + 4)) ι' F ∧
      ((s.setReg rd (z.signExtend 64)).setPc (s.pc + 4)).pc = s.pc + 4 := by
  have hc := BitVec.toInt_eq_toNat_cond z
  have hl := z.isLt
  have hse : (z.signExtend 64).toInt = z.toInt := BitVec.toInt_signExtend_of_le (by omega)
  unfold Fn.word32
  refine hI.fresh4 hprot hrd [z.toInt] (.var (f.freshAt S)) _ (z.signExtend 64) ?_ (fun p hp => ?_)
  · unfold HasInt
    simp only [IExpr.eval_var, setFrom_x]
    have hc' := BitVec.toInt_eq_toNat_cond (z.signExtend 64)
    have hl' := (z.signExtend 64).isLt
    rw [hse] at hc'
    split at hc <;> split at hc' <;> omega
  · have hev := Fn.eval_setFrom_old (f := f) hem ι [z.toInt]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;>
      simp only [Constr.holds, Constr.eval, Constr.lt, decide_eq_true_eq, IExpr.eval_var,
        IExpr.eval_lit, IExpr.eval_add, IExpr.eval_sub, setFrom_x, hev] <;> split at hc <;> omega

end NoCompiler.Typed
