import NoCompiler.Typed.Sound.Arith

/-
Lemma 3 (branches): the facts the checker adds on each edge of a branch hold of the
state that takes that edge. Lemma 1 (representatives) for `u(e)` and `s(e)`.
-/
namespace NoCompiler.Typed

variable {f : Fn} {T : TokEnv} {P : Perm} {s0 : State} {ι0 : Val}

theorem Inv.setPc {S : STy} {s : State} {ι : Val} {F : TokFp} (hI : Inv f T P s0 ι0 S s ι F)
    (pc : Word) : Inv f T P s0 ι0 S (s.setPc pc) ι F :=
  ⟨hI.facts, by simpa using hI.regs, hI.prot, by simpa using hI.valid, hI.sep, hI.stack,
    hI.perm, hI.ids, by simpa using hI.sp, by simpa using hI.live⟩

theorem Inv.addFacts {S : STy} {s : State} {ι : Val} {F : TokFp} (hI : Inv f T P s0 ι0 S s ι F)
    {ps : List Constr} (hps : ∀ p ∈ ps, p.holds ι) : Inv f T P s0 ι0 (S.addFacts ps) s ι F := by
  refine ⟨?_, hI.regs, hI.prot, hI.valid, hI.sep, hI.stack, hI.perm, hI.ids, hI.sp, hI.live⟩
  intro p hp; rcases List.mem_append.1 hp with h | h
  · exact hps p h
  · exact hI.facts p h

/-- `u(e)`: its value is the word's unsigned value, and its facts hold. -/
theorem urep_sound {S : STy} {x : Var} {e : IExpr} {ι ι' : Val} {w : Word}
    (hh : ∀ p ∈ S.hyps, p.holds ι) (hw : HasInt ι w e) (he : ∀ y ≤ e.maxVar, ι' y = ι y)
    (hx : ι' x = w.toNat) :
    (Fn.urep S x e).1.eval ι' = w.toNat ∧ ∀ p ∈ (Fn.urep S x e).2, p.holds ι' := by
  have hev : e.eval ι' = e.eval ι := IExpr.eval_congr_max he
  have := w.isLt
  unfold Fn.urep
  split
  · rename_i hin
    have hin := STy.ent_sound hin hh
    simp only [Constr.holds, Constr.eval, Bool.and_eq_true, decide_eq_true_eq, Constr.lt,
      IExpr.eval_lit, IExpr.eval_add] at hin
    exact ⟨by rw [hev, hw.toNat_eq hin.1 (by omega)], by simp⟩
  · refine ⟨by simp [hx], ?_⟩
    intro p hp
    unfold HasInt at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;>
      simp only [Constr.holds, Constr.eval, decide_eq_true_eq, Constr.lt, Constr.eqMod,
        IExpr.eval_var, IExpr.eval_lit, IExpr.eval_add, IExpr.eval_sub, hx, hev] <;> omega

/-- `s(e)`: its value is the word's signed value, and its facts hold. -/
theorem srep_sound {S : STy} {x : Var} {e : IExpr} {ι ι' : Val} {w : Word}
    (hh : ∀ p ∈ S.hyps, p.holds ι) (hw : HasInt ι w e) (he : ∀ y ≤ e.maxVar, ι' y = ι y)
    (hx : ι' x = w.toInt) :
    (Fn.srep S x e).1.eval ι' = w.toInt ∧ ∀ p ∈ (Fn.srep S x e).2, p.holds ι' := by
  have hev : e.eval ι' = e.eval ι := IExpr.eval_congr_max he
  have hti := BitVec.toInt_eq_toNat_cond w
  have := w.isLt
  unfold HasInt at hw
  unfold Fn.srep
  split
  · rename_i hin
    have hin := STy.ent_sound hin hh
    simp only [Constr.holds, Constr.eval, Bool.and_eq_true, decide_eq_true_eq, Constr.lt,
      IExpr.eval_lit, IExpr.eval_add] at hin
    refine ⟨?_, by simp⟩
    rw [hev, hti]; split <;> omega
  · refine ⟨by simp [hx], ?_⟩
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;>
      simp only [Constr.holds, Constr.eval, decide_eq_true_eq, Constr.lt, Constr.eqMod,
        IExpr.eval_var, IExpr.eval_lit, IExpr.eval_add, IExpr.eval_sub, hx, hev, hti] <;>
      split <;> omega

theorem beq_word_iff {ι : Val} {x y : Word} {e1 e2 : IExpr} (h1 : HasInt ι x e1)
    (h2 : HasInt ι y e2) : x = y ↔ (Constr.eqMod e1 e2).holds ι := by
  unfold HasInt at h1 h2
  simp only [Constr.holds, Constr.eqMod, Constr.eval, decide_eq_true_eq, IExpr.eval_sub]
  have := x.isLt; have := y.isLt
  constructor
  · intro e; subst e; omega
  · intro h; apply BitVec.eq_of_toNat_eq; omega

/-- Lemma 3. -/
theorem Fn.branch_sound (hprot : ∀ x ∈ f.protectedVars, x < f.fresh) {S : STy} {s : State}
    {ι : Val} {F : TokFp} (hI : Inv f T P s0 ι0 S s ι F) {rs1 rs2 : Reg} {e1 e2 : IExpr}
    (h1 : S.reg rs1 = some e1) (h2 : S.reg rs2 = some e2) (op : BrOp) :
    ∃ ι', (∀ y : Nat, y < f.fresh → ι' y = ι y) ∧ (∀ y : Nat, y ≤ S.maxVar → ι' y = ι y) ∧
      (evalBr op (s.reg rs1) (s.reg rs2) = true → ∀ p ∈ (f.branchFacts S op e1 e2).1, p.holds ι') ∧
      (evalBr op (s.reg rs1) (s.reg rs2) = false → ∀ p ∈ (f.branchFacts S op e1 e2).2, p.holds ι') := by
  have k1 := STy.reg_hasInt hI.regs h1
  have k2 := STy.reg_hasInt hI.regs h2
  have m1 := STy.reg_maxVar h1
  have m2 := STy.reg_maxVar h2
  have hh := hI.hyps
  have hgt := f.freshAt_gt S
  -- the fresh values: unsigned for the unsigned comparisons, signed for the signed ones
  let signed := op == .blt || op == .bge
  let v1 : Int := if signed then (s.reg rs1).toInt else (s.reg rs1).toNat
  let v2 : Int := if signed then (s.reg rs2).toInt else (s.reg rs2).toNat
  obtain ⟨a1, a2, a3⟩ := setFrom_fresh hprot S ι [v1, v2]
  have x0 := setFrom_at (ι := ι) (x := f.freshAt S) (vs := [v1, v2]) 0 (by simp)
  have x1 := setFrom_at (ι := ι) (x := f.freshAt S) (vs := [v1, v2]) 1 (by simp)
  simp only [Nat.add_zero, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] at x0 x1
  refine ⟨_, a3, a1, ?_⟩
  have ag1 : ∀ y ≤ e1.maxVar, setFrom ι (f.freshAt S) [v1, v2] y = ι y := fun y hy => a1 y (by omega)
  have ag2 : ∀ y ≤ e2.maxVar, setFrom ι (f.freshAt S) [v1, v2] y = ι y := fun y hy => a1 y (by omega)
  have ev1 : e1.eval (setFrom ι (f.freshAt S) [v1, v2]) = e1.eval ι := IExpr.eval_congr_max ag1
  have ev2 : e2.eval (setFrom ι (f.freshAt S) [v1, v2]) = e2.eval ι := IExpr.eval_congr_max ag2
  have k1' := k1.of_eq ev1.symm
  have k2' := k2.of_eq ev2.symm
  have eqm := beq_word_iff k1' k2'
  cases op with
  | beq =>
    simp only [Fn.branchFacts, evalBr, Bool.beq_eq_decide_eq, decide_eq_true_eq, decide_eq_false_iff_not,
      List.mem_singleton, forall_eq]
    exact ⟨fun h => eqm.1 h, fun h => by simpa [Constr.holds, Constr.eval] using fun h' => h (eqm.2 h')⟩
  | bne =>
    simp only [Fn.branchFacts, evalBr, bne, Bool.not_eq_true', Bool.not_eq_false',
      Bool.beq_eq_decide_eq, decide_eq_true_eq, decide_eq_false_iff_not, List.mem_singleton, forall_eq]
    exact ⟨fun h => by simpa [Constr.holds, Constr.eval] using fun h' => h (eqm.2 h'), fun h => eqm.1 h⟩
  | bltu | bgeu =>
    have u1 := urep_sound (x := f.freshAt S) hh k1 ag1 (by rw [x0]; simp [v1, signed])
    have u2 := urep_sound (x := f.freshAt S + 1) hh k2 ag2 (by rw [x1]; simp [v2, signed])
    simp only [Fn.branchFacts, evalBr, BitVec.ult_eq_decide, Bool.not_eq_true', Bool.not_eq_false',
      decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_eq_eq_not, Bool.not_true,
      beq_self_eq_true, ite_true, show (BrOp.bgeu == BrOp.bltu) = false from rfl, Bool.false_eq_true,
      ite_false]
    refine ⟨fun h p hp => ?_, fun h p hp => ?_⟩ <;>
    · simp only [List.mem_append, List.mem_singleton] at hp
      rcases hp with (hp | hp) | hp
      · exact u1.2 p hp
      · exact u2.2 p hp
      · subst hp
        simp only [Constr.holds, Constr.eval, Constr.lt, decide_eq_true_eq, IExpr.eval_add,
          IExpr.eval_lit, u1.1, u2.1]
        try simp only [Bool.not_false, Bool.not_true, decide_eq_true_eq, decide_eq_false_iff_not] at h
        omega
  | blt | bge =>
    have u1 := srep_sound (x := f.freshAt S) hh k1 ag1 (by rw [x0]; simp [v1, signed])
    have u2 := srep_sound (x := f.freshAt S + 1) hh k2 ag2 (by rw [x1]; simp [v2, signed])
    simp only [Fn.branchFacts, evalBr, BitVec.slt_eq_decide, Bool.not_eq_true', Bool.not_eq_false',
      decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_eq_eq_not, Bool.not_true,
      beq_self_eq_true, ite_true, show (BrOp.bge == BrOp.blt) = false from rfl, Bool.false_eq_true,
      ite_false]
    refine ⟨fun h p hp => ?_, fun h p hp => ?_⟩ <;>
    · simp only [List.mem_append, List.mem_singleton] at hp
      rcases hp with (hp | hp) | hp
      · exact u1.2 p hp
      · exact u2.2 p hp
      · subst hp
        simp only [Constr.holds, Constr.eval, Constr.lt, decide_eq_true_eq, IExpr.eval_add,
          IExpr.eval_lit, u1.1, u2.1]
        try simp only [Bool.not_false, Bool.not_true, decide_eq_true_eq, decide_eq_false_iff_not] at h
        omega

end NoCompiler.Typed
