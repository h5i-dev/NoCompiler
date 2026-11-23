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

/-- A register typed by a constant holds exactly that constant (mod 2^64). -/
theorem eq_ofInt_of_hasInt {ι : Val} {w : Word} {c : Int} (h : HasInt ι w (.mk c [])) :
    w = BitVec.ofInt 64 c := by
  unfold HasInt at h
  simp only [IExpr.eval, List.map_nil, List.sum_nil, Int.add_zero] at h
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt]
  have hw := w.isLt
  have : ((w.toNat : Int) % 2 ^ 64) = (w.toNat : Int) := Int.emod_eq_of_lt (by omega) (by omega)
  rw [this] at h
  omega

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

theorem lessFact_holds {ι : Val} {x : Var} {a b : IExpr} {p : Prop} [Decidable p]
    (hx : ι x = if p then 1 else 0) (hp : p ↔ a.eval ι < b.eval ι) :
    (Fn.lessFact x a b).holds ι := by
  unfold Fn.lessFact
  simp only [Constr.holds, Constr.eval, Constr.lt, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, IExpr.eval_var, IExpr.eval_lit, IExpr.eval_add, hx]
  by_cases h : p
  · simp only [h, ite_true]; left; exact ⟨trivial, by have := hp.1 h; omega⟩
  · simp only [h, ite_false]; right; exact ⟨trivial, by have := mt hp.2 h; omega⟩

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


theorem bool64_toNat (b : Bool) : ((bool64 b).toNat : Int) = if b = true then 1 else 0 := by
  cases b <;> simp [bool64]

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

/-- The comparisons (`slt`, `sltu`, `slti`, `sltiu`) and `xori rd, rs, −1`. -/
theorem Fn.arith2_sound (hprot : ∀ x ∈ f.protectedVars, x < f.fresh) {S S' : STy} {s s' : State}
    {ι : Val} {F : TokFp} (hI : Inv f T P s0 ι0 S s ι F) {i : Instr} {rd : Reg}
    (hw : writesReg i = some rd) (hrd : rd ≠ 2) (ha : f.arith2 S i = some S')
    (hx : exec i s = some s') :
    ∃ ι', (∀ y : Nat, y < f.fresh → ι' y = ι y) ∧ Inv f T P s0 ι0 S' s' ι' F ∧ s'.pc = s.pc + 4 := by
  have hag := (setFrom_fresh hprot S ι)
  cases i with
  | iop op rd' rs imm =>
    simp only [writesReg, Option.some.injEq] at hw; subst hw
    simp only [exec, Option.some.injEq] at hx; subst hx
    cases op
    case xori =>
      simp only [Fn.arith2] at ha
      split at ha
      · rename_i h1
        cases hr : S.reg rs with
        | none => simp [hr] at ha
        | some e =>
          simp only [hr, Option.map_some, Option.some.injEq] at ha; subst ha
          refine ⟨ι, fun _ _ => rfl, hI.exact hrd ?_ _, by simp⟩
          have hre := STy.reg_hasInt hI.regs hr
          have him : imm.signExtend 64 = BitVec.allOnes 64 := by
            apply BitVec.eq_of_toInt_eq
            rw [BitVec.toInt_signExtend_of_le (by omega), h1]; decide
          simp only [evalI, him, BitVec.xor_allOnes]
          unfold HasInt at *
          rw [BitVec.toNat_not]
          simp only [IExpr.eval_sub, IExpr.eval_lit]
          have := (s.reg rs).isLt
          omega
      · cases ha
    case sltiu =>
      simp only [Fn.arith2] at ha
      cases hr : S.reg rs with
      | none => simp [hr] at ha
      | some e =>
        simp only [hr, Option.map_some, Option.some.injEq] at ha; subst ha
        have hre := STy.reg_hasInt hI.regs hr
        have hem := STy.reg_maxVar' hr
        let vs : List Int := [((evalI .sltiu (s.reg rs) (imm.signExtend 64)).toNat : Int), ((s.reg rs).toNat : Int)]
        refine hI.fresh4 hprot hrd vs (.var (f.freshAt S)) _
          (evalI .sltiu (s.reg rs) (imm.signExtend 64))
          (hasInt_toNat _ _ _ (by simp [vs, setFrom_x])) (fun p hp => ?_)
        have hu := Fn.urep_spec (x := f.freshAt S + 1) hI hre hem (hag vs).1 (by simp [vs, setFrom_x1])
        simp only [List.mem_append, List.mem_singleton] at hp
        rcases hp with hp | rfl
        · exact hu.2 p hp
        · refine lessFact_holds (p := (s.reg rs).toNat < (imm.signExtend 64).toNat) ?_ ?_
          · simp only [vs, setFrom_x, evalI, bool64_toNat, BitVec.ult, decide_eq_true_eq]
          · simp [hu.1]
    case slti =>
      simp only [Fn.arith2] at ha
      cases hr : S.reg rs with
      | none => simp [hr] at ha
      | some e =>
        simp only [hr, Option.map_some, Option.some.injEq] at ha; subst ha
        have hre := STy.reg_hasInt hI.regs hr
        have hem := STy.reg_maxVar' hr
        let vs : List Int := [((evalI .slti (s.reg rs) (imm.signExtend 64)).toNat : Int), (s.reg rs).toInt]
        refine hI.fresh4 hprot hrd vs (.var (f.freshAt S)) _
          (evalI .slti (s.reg rs) (imm.signExtend 64))
          (hasInt_toNat _ _ _ (by simp [vs, setFrom_x])) (fun p hp => ?_)
        have hu := Fn.srep_spec (x := f.freshAt S + 1) hI hre hem (hag vs).1 (by simp [vs, setFrom_x1])
        simp only [List.mem_append, List.mem_singleton] at hp
        rcases hp with hp | rfl
        · exact hu.2 p hp
        · refine lessFact_holds (p := (s.reg rs).toInt < imm.toInt) ?_ ?_
          · simp only [vs, setFrom_x, evalI, bool64_toNat, BitVec.slt, decide_eq_true_eq,
              BitVec.toInt_signExtend_of_le (show 12 ≤ 64 by omega)]
          · simp [hu.1]
    all_goals simp [Fn.arith2] at ha
  | rop op rd' a b =>
    simp only [writesReg, Option.some.injEq] at hw; subst hw
    simp only [exec, Option.some.injEq] at hx; subst hx
    cases op
    case sltu =>
      simp only [Fn.arith2] at ha
      cases h1 : S.reg a with
      | none => simp [h1] at ha
      | some e1 =>
      cases h2 : S.reg b with
      | none => simp [h1, h2] at ha
      | some e2 =>
        simp only [h1, h2, Option.some.injEq] at ha; subst ha
        let vs : List Int := [((evalR .sltu (s.reg a) (s.reg b)).toNat : Int), ((s.reg a).toNat : Int),
          ((s.reg b).toNat : Int)]
        refine hI.fresh4 hprot hrd vs (.var (f.freshAt S)) _
          (evalR .sltu (s.reg a) (s.reg b))
          (hasInt_toNat _ _ _ (by simp [vs, setFrom_x])) (fun p hp => ?_)
        have u1 := Fn.urep_spec (x := f.freshAt S + 1) hI (STy.reg_hasInt hI.regs h1) (STy.reg_maxVar' h1)
          (hag vs).1 (by simp [vs, setFrom_x1])
        have u2 := Fn.urep_spec (x := f.freshAt S + 2) hI (STy.reg_hasInt hI.regs h2) (STy.reg_maxVar' h2)
          (hag vs).1 (by simp [vs, setFrom_x2])
        simp only [List.mem_append, List.mem_singleton] at hp
        rcases hp with (hp | hp) | rfl
        · exact u1.2 p hp
        · exact u2.2 p hp
        · refine lessFact_holds (p := (s.reg a).toNat < (s.reg b).toNat) ?_ ?_
          · simp only [vs, setFrom_x, evalR, bool64_toNat, BitVec.ult, decide_eq_true_eq]
          · simp [u1.1, u2.1]
    case slt =>
      simp only [Fn.arith2] at ha
      cases h1 : S.reg a with
      | none => simp [h1] at ha
      | some e1 =>
      cases h2 : S.reg b with
      | none => simp [h1, h2] at ha
      | some e2 =>
        simp only [h1, h2, Option.some.injEq] at ha; subst ha
        let vs : List Int := [((evalR .slt (s.reg a) (s.reg b)).toNat : Int), (s.reg a).toInt,
          (s.reg b).toInt]
        refine hI.fresh4 hprot hrd vs (.var (f.freshAt S)) _
          (evalR .slt (s.reg a) (s.reg b))
          (hasInt_toNat _ _ _ (by simp [vs, setFrom_x])) (fun p hp => ?_)
        have u1 := Fn.srep_spec (x := f.freshAt S + 1) hI (STy.reg_hasInt hI.regs h1) (STy.reg_maxVar' h1)
          (hag vs).1 (by simp [vs, setFrom_x1])
        have u2 := Fn.srep_spec (x := f.freshAt S + 2) hI (STy.reg_hasInt hI.regs h2) (STy.reg_maxVar' h2)
          (hag vs).1 (by simp [vs, setFrom_x2])
        simp only [List.mem_append, List.mem_singleton] at hp
        rcases hp with (hp | hp) | rfl
        · exact u1.2 p hp
        · exact u2.2 p hp
        · refine lessFact_holds (p := (s.reg a).toInt < (s.reg b).toInt) ?_ ?_
          · simp only [vs, setFrom_x, evalR, bool64_toNat, BitVec.slt, decide_eq_true_eq]
          · simp [u1.1, u2.1]
    all_goals simp [Fn.arith2] at ha
  | _ => simp [Fn.arith2] at ha

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
      exact f.arith2_sound hprot hI hw hrd h1 hx
    · rw [hw] at ha
      simp only [Option.some.injEq] at ha; subst ha
      obtain ⟨v, rfl⟩ := writesReg_exec hw hx
      obtain ⟨ι', h1, h2⟩ := hI.any hprot hrd v _
      exact ⟨ι', h1, h2, by simp⟩

end NoCompiler.Typed
