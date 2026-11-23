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


theorem minMaxFact_holds {ι : Val} {isMax : Bool} {x : Var} {a b : IExpr} {v : Int}
    (hx : ι x = v) (hor : v = a.eval ι ∨ v = b.eval ι)
    (hord : if isMax then a.eval ι ≤ v ∧ b.eval ι ≤ v else v ≤ a.eval ι ∧ v ≤ b.eval ι) :
    (Fn.minMaxFact isMax x a b).holds ι := by
  unfold Fn.minMaxFact
  cases isMax <;>
    simp only [Constr.holds, Constr.eval, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
      IExpr.eval_var, hx, if_true, if_false, Bool.false_eq_true] at hord ⊢ <;> omega

theorem hasInt_toInt (ι : Val) (w : Word) (x : Var) (h : ι x = w.toInt) : HasInt ι w (.var x) := by
  unfold HasInt
  simp only [IExpr.eval_var, h]
  have hc := BitVec.toInt_eq_toNat_cond w
  have := w.isLt
  split at hc <;> omega

theorem zext32_toNat (w : Word) : (zext32 w).toNat = w.toNat % 2 ^ 32 := by
  unfold zext32
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))

theorem zexth_toNat (w : Word) : ((w.setWidth 16).setWidth 64).toNat = w.toNat % 2 ^ 16 := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))

/-- The low-bits facts hold for `x := w mod 2^n`. -/
theorem lowFacts_holds {ι : Val} {x : Var} {e : IExpr} {n : Nat} (hn : n ≤ 64) {w : Word}
    (hre : HasInt ι w e) (hx : ι x = ((w.toNat % 2 ^ n : Nat) : Int)) :
    ∀ p ∈ Fn.lowFacts x e n, p.holds ι := by
  intro p hp
  unfold Fn.lowFacts at hp
  unfold HasInt at hre
  generalize hM : ((2 ^ n : Nat) : Int) = M
  have hd : M ∣ (2 ^ 64 : Int) := by
    rw [← hM, show (2 ^ 64 : Int) = ((2 ^ 64 : Nat) : Int) by norm_cast]
    exact Int.natCast_dvd_natCast.2 (Nat.pow_dvd_pow 2 hn)
  have hW : ((w.toNat : Int) % M) = e.eval ι % M := by
    rw [← Int.emod_emod_of_dvd _ hd, ← Int.emod_emod_of_dvd (e.eval ι) hd, hre]
  have hx' : ι x = (w.toNat : Int) % M := by rw [hx, ← hM, Int.natCast_emod]
  have hpos : (0 : Int) < M := by rw [← hM]; exact_mod_cast Nat.two_pow_pos n
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · simp only [Constr.holds, Constr.eval, decide_eq_true_eq, IExpr.eval_sub, IExpr.eval_var, hM]
    rw [hx', Int.sub_emod, Int.emod_emod_of_dvd _ (Int.dvd_refl _), ← hW, Int.sub_self, Int.zero_emod]
  · simp only [Constr.holds, Constr.eval, decide_eq_true_eq, IExpr.eval_var, IExpr.eval_lit, hx']
    exact Int.emod_nonneg _ (by omega)
  · simp only [Constr.holds, Constr.eval, Constr.lt, decide_eq_true_eq, IExpr.eval_var,
      IExpr.eval_lit, IExpr.eval_add, hx']
    have := Int.emod_lt_of_pos (w.toNat : Int) hpos
    have hM' : ((2 : Int) ^ n) = M := by rw [← hM]; norm_cast
    rw [hM']; omega

theorem quotFacts_holds {ι : Val} {x : Var} {u : IExpr} {c : Int} (hc : 0 < c)
    (hx : ι x = u.eval ι / c) : ∀ p ∈ Fn.quotFacts x u c, p.holds ι := by
  intro p hp
  have hd := Int.emod_add_mul_ediv (u.eval ι) c
  have h0 := Int.emod_nonneg (u.eval ι) (by omega : c ≠ 0)
  have h1 := Int.emod_lt_of_pos (u.eval ι) hc
  unfold Fn.quotFacts at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;>
    simp only [Constr.holds, Constr.eval, Constr.lt, decide_eq_true_eq, IExpr.eval_sub,
      IExpr.eval_smul, IExpr.eval_var, IExpr.eval_lit, IExpr.eval_add, hx] <;> omega

theorem remFacts_holds {ι : Val} {x : Var} {u : IExpr} {c : Int} (hc : 0 < c)
    (hx : ι x = u.eval ι % c) : ∀ p ∈ Fn.remFacts x u c, p.holds ι := by
  intro p hp
  have h0 := Int.emod_nonneg (u.eval ι) (by omega : c ≠ 0)
  have h1 := Int.emod_lt_of_pos (u.eval ι) hc
  have hcn : ((c.toNat : Nat) : Int) = c := Int.toNat_of_nonneg (by omega)
  unfold Fn.remFacts at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · simp only [Constr.holds, Constr.eval, decide_eq_true_eq, IExpr.eval_sub, IExpr.eval_var, hcn, hx]
    rw [Int.sub_emod, Int.emod_emod_of_dvd _ (Int.dvd_refl _), Int.sub_self, Int.zero_emod]
  · simp only [Constr.holds, Constr.eval, decide_eq_true_eq, IExpr.eval_var, IExpr.eval_lit, hx]; omega
  · simp only [Constr.holds, Constr.eval, Constr.lt, decide_eq_true_eq, IExpr.eval_var,
      IExpr.eval_lit, IExpr.eval_add, hx]; omega

/-- A register typed by the literal `c` holds `c mod 2^64`. -/
theorem toNat_of_lit {ι : Val} {w : Word} {c : Int} (h : HasInt ι w (.mk c [])) :
    (w.toNat : Int) = c % 2 ^ 64 := by
  have := eq_ofInt_of_hasInt h
  subst this
  rw [BitVec.toNat_ofInt]
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))

/-- A word typed by an expression in `[0, 1]` is `0` or `1`. -/
theorem bit_of_isBit {ι : Val} {w : Word} {e : IExpr} (h : HasInt ι w e)
    (hb : (Fn.isBit e).holds ι) : (w = 0 ∧ e.eval ι = 0) ∨ (w = 1 ∧ e.eval ι = 1) := by
  unfold Fn.isBit at hb
  simp only [Constr.holds, Constr.eval, Bool.and_eq_true, decide_eq_true_eq, IExpr.eval_lit] at hb
  have ht := h.toNat_eq hb.1 (by omega)
  rcases (show e.eval ι = 0 ∨ e.eval ι = 1 by omega) with h0 | h1
  · left; exact ⟨BitVec.eq_of_toNat_eq (by simp; omega), h0⟩
  · right; exact ⟨BitVec.eq_of_toNat_eq (by simp; omega), h1⟩

theorem bitTable_holds {ι : Val} {g : Nat → Nat → Nat} {x : Var} {a b : IExpr} {p q : Nat}
    (hp : p = 0 ∨ p = 1) (hq : q = 0 ∨ q = 1) (ha : a.eval ι = p) (hb : b.eval ι = q)
    (hx : ι x = g p q) : (Fn.bitTable g x a b).holds ι := by
  unfold Fn.bitTable
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;>
    simp [Constr.holds, Constr.eval, ha, hb, hx]

theorem boundFacts_holds {ι : Val} {x : Var} {b : Int} {n : Nat} (hx : ι x = n) (hb : (n : Int) ≤ b) :
    ∀ p ∈ Fn.boundFacts x b, p.holds ι := by
  intro p hp
  simp only [Fn.boundFacts, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;>
    simp only [Constr.holds, Constr.eval, decide_eq_true_eq, IExpr.eval_var, IExpr.eval_lit, hx] <;> omega

theorem Fn.urep_fst_of_nil {S : STy} {x : Var} {e : IExpr} (h : (Fn.urep S x e).2 = []) :
    (Fn.urep S x e).1 = e := by
  unfold Fn.urep at *; split <;> simp_all

theorem Fn.urep_nil_ent {S : STy} {x : Var} {e : IExpr} (h : (Fn.urep S x e).2 = []) :
    S.ent (.and (.le (.lit 0) e) (.lt e (.lit (2 ^ 64)))) = true := by
  unfold Fn.urep at h
  split at h
  · assumption
  · simp at h

theorem divBound_holds {ι : Val} {isDiv : Bool} {x : Var} {ua ub : IExpr} {r A B : Nat}
    (hx : ι x = r) (ha : ua.eval ι = A) (hb : ub.eval ι = B) (hr : r < 2 ^ 64) (hra : r ≤ A)
    (hrb : isDiv = false → r < B) : ∀ p ∈ Fn.divBound isDiv x ua ub, p.holds ι := by
  intro p hp
  cases isDiv
  · simp only [Fn.divBound, Bool.false_eq_true, ite_false, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hp
    have := hrb rfl
    rcases hp with rfl | rfl | rfl | rfl <;>
      simp only [Constr.holds, Constr.eval, Constr.lt, decide_eq_true_eq, IExpr.eval_var,
        IExpr.eval_lit, IExpr.eval_add, hx, ha, hb] <;> omega
  · simp only [Fn.divBound, ite_true, List.append_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hp
    rcases hp with rfl | rfl | rfl <;>
      simp only [Constr.holds, Constr.eval, Constr.lt, decide_eq_true_eq, IExpr.eval_var,
        IExpr.eval_lit, IExpr.eval_add, hx, ha] <;> omega

/-- Products agree modulo 2^32 when the factors do. -/
theorem mod32_mul {A B a b : Int} (hA : (A - a) % 2 ^ 32 = 0) (hB : (B - b) % 2 ^ 32 = 0) :
    (A * B - a * b) % 2 ^ 32 = 0 := by
  have hA' := Int.dvd_of_emod_eq_zero hA
  have hB' := Int.dvd_of_emod_eq_zero hB
  have : A * B - a * b = A * (B - b) + (A - a) * b := by
    rw [Int.mul_sub, Int.sub_mul]; omega
  rw [this]
  exact Int.emod_eq_zero_of_dvd (Int.dvd_add (Int.dvd_trans hB' (Int.dvd_mul_left _ _))
    (Int.dvd_trans hA' (Int.dvd_mul_right _ _)))

theorem IExpr.maxVar_smul' (k : Int) (a : IExpr) : (a.smul k).maxVar = a.maxVar := by
  unfold IExpr.maxVar IExpr.smul
  simp only
  generalize a.terms = ts
  induction ts with
  | nil => rfl
  | cons t r ih => simp only [List.map_cons, List.foldr_cons]; rw [ih]

theorem w32_mul_mod {x y : Word} {E1 E2 : Int} (hx : (x.toNat : Int) % 2 ^ 64 = E1 % 2 ^ 64)
    (hy : (y.toNat : Int) % 2 ^ 64 = E2 % 2 ^ 64) :
    (((x.setWidth 32 * y.setWidth 32).toNat : Int) - E1 * E2) % 2 ^ 32 = 0 := by
  rw [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_setWidth]
  generalize hP : x.toNat % 2 ^ 32 * (y.toNat % 2 ^ 32) = P
  have hPc : ((P : Nat) : Int) = ((x.toNat % 2 ^ 32 : Nat) : Int) * ((y.toNat % 2 ^ 32 : Nat) : Int) := by
    rw [← hP, Int.natCast_mul]
  have k := mod32_mul (A := ((x.toNat % 2 ^ 32 : Nat) : Int)) (a := E1)
    (B := ((y.toNat % 2 ^ 32 : Nat) : Int)) (b := E2) (by omega) (by omega)
  rw [← hPc] at k
  generalize E1 * E2 = Q at k ⊢
  omega

theorem w32_shl_mod {x : Word} {E : Int} (n : Nat) (hx : (x.toNat : Int) % 2 ^ 64 = E % 2 ^ 64) :
    ((((x.setWidth 32) <<< n).toNat : Int) - ((2 ^ n : Nat) : Int) * E) % 2 ^ 32 = 0 := by
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, Nat.shiftLeft_eq]
  generalize hP : x.toNat % 2 ^ 32 * 2 ^ n = P
  generalize hN : 2 ^ n = N at hP ⊢
  have hPc : ((P : Nat) : Int) = ((x.toNat % 2 ^ 32 : Nat) : Int) * ((N : Nat) : Int) := by
    rw [← hP, Int.natCast_mul]
  have k := mod32_mul (A := ((x.toNat % 2 ^ 32 : Nat) : Int)) (a := E) (B := ((N : Nat) : Int))
    (b := ((N : Nat) : Int)) (by omega) (by simp)
  rw [← hPc] at k
  rw [Int.mul_comm ((N : Nat) : Int) E]
  generalize E * ((N : Nat) : Int) = Q at k ⊢
  omega

theorem bitcount_le (x : Word) :
    (evalU .clz x).toNat ≤ 64 ∧ (evalU .ctz x).toNat ≤ 64 ∧ (evalU .cpop x).toNat ≤ 64 ∧
    (evalU .clzw x).toNat ≤ 32 ∧ (evalU .ctzw x).toNat ≤ 32 ∧ (evalU .cpopw x).toNat ≤ 32 := by
  have c64 : ∀ y : BitVec 64, y.clz.toNat ≤ 64 := fun y => by
    have := BitVec.le_def.1 (BitVec.clz_le (x := y)); simpa using this
  have c32 : ∀ y : BitVec 32, y.clz.toNat ≤ 32 := fun y => by
    have := BitVec.le_def.1 (BitVec.clz_le (x := y)); simpa using this
  have p64 : ∀ y : BitVec 64, y.cpop.toNat ≤ 64 := fun y => by
    unfold BitVec.cpop; rw [BitVec.toNat_ofNat]
    exact Nat.le_trans (Nat.mod_le _ _) (BitVec.cpopNatRec_zero_le y 64)
  have p32 : ∀ y : BitVec 32, y.cpop.toNat ≤ 32 := fun y => by
    unfold BitVec.cpop; rw [BitVec.toNat_ofNat]
    exact Nat.le_trans (Nat.mod_le _ _) (BitVec.cpopNatRec_zero_le y 32)
  simp only [evalU, BitVec.ctz, BitVec.toNat_setWidth]
  refine ⟨c64 _, c64 _, p64 _, ?_, ?_, ?_⟩ <;>
    exact Nat.le_trans (Nat.mod_le _ _) (by first | exact c32 _ | exact p32 _)

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

theorem nat_and_eq_zero {a b j : Nat} (ha : a < 2 ^ j) (hb : b % 2 ^ j = 0) : a &&& b = 0 := by
  have h1 : a = a &&& (2 ^ j - 1) := (Nat.and_two_pow_sub_one_of_lt_two_pow ha).symm
  rw [h1, Nat.and_assoc, Nat.and_comm (2 ^ j - 1) b, Nat.and_two_pow_sub_one_eq_mod, hb, Nat.and_zero]

theorem bv_disjoint {w c : Word} (h : w &&& c = 0#64) : w ||| c = w + c ∧ w ^^^ c = w + c := by
  have ho := (BitVec.add_eq_or_of_and_eq_zero w c h).symm
  refine ⟨ho, ?_⟩
  rw [← ho]
  ext i hi
  have := congrArg (fun z => z.getLsbD i) h
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero] at this
  simp only [BitVec.getElem_xor, BitVec.getElem_or]
  rw [← BitVec.getLsbD_eq_getElem, ← BitVec.getLsbD_eq_getElem]
  cases hw : w.getLsbD i <;> cases hc : c.getLsbD i <;> simp_all

/-- The result of `disjConst`: under the invariant, `w op c` for `op` or/xor is `e + cu`. -/
theorem disjConst_val {ι : Val} {S : STy} (hh : ∀ p ∈ S.hyps, p.holds ι) {e : IExpr} {w c : Word}
    (hw : HasInt ι w e) {cu : Nat} (hc : c.toNat = cu) (hcu : cu ≠ 0)
    (hr : S.ent (.and (.le (.lit 0) e) (.lt e (.lit (2 ^ 64)))) = true)
    (hd : ((cu % 2 ^ Fn.tz cu == 0 && S.ent (.lt e (.lit (2 ^ Fn.tz cu)))) ||
       (decide (cu < 2 ^ (cu.log2 + 1)) && S.ent (.dvd (2 ^ (cu.log2 + 1)) e))) = true) :
    HasInt ι (w ||| c) (e.add (.lit cu)) ∧ HasInt ι (w ^^^ c) (e.add (.lit cu)) := by
  have hr := STy.ent_sound hr hh
  simp only [Constr.holds, Constr.eval, Constr.lt, IExpr.eval_add, IExpr.eval_lit, Bool.and_eq_true,
    decide_eq_true_eq] at hr
  have hwn : (w.toNat : Int) = e.eval ι := hw.toNat_eq hr.1 (by omega)
  have hand : w &&& c = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, hc, BitVec.toNat_zero]
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hd
    rcases hd with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have h2 := STy.ent_sound h2 hh
      simp only [Constr.holds, Constr.eval, Constr.lt, IExpr.eval_add, IExpr.eval_lit,
        decide_eq_true_eq] at h2
      exact nat_and_eq_zero (by have : ((2 ^ Fn.tz cu : Nat) : Int) = 2 ^ Fn.tz cu := by norm_cast
                                omega) h1
    · have h2 := STy.ent_sound h2 hh
      simp only [Constr.holds, Constr.eval, decide_eq_true_eq] at h2
      rw [Nat.and_comm]
      refine nat_and_eq_zero h1 ?_
      have : ((2 ^ (cu.log2 + 1) : Nat) : Int) ∣ (w.toNat : Int) := by
        rw [hwn]; exact Int.dvd_of_emod_eq_zero (by exact_mod_cast h2)
      exact Nat.mod_eq_zero_of_dvd (Int.natCast_dvd_natCast.1 this)
  obtain ⟨ho, hx⟩ := bv_disjoint hand
  have hs : HasInt ι (w + c) (e.add (.lit cu)) :=
    hasInt_add hw (by unfold HasInt; rw [hc, IExpr.eval_lit])
  exact ⟨ho ▸ hs, hx ▸ hs⟩

theorem Fn.disjConst_sound {S S' : STy} {s : State} {ι : Val} {F : TokFp}
    (hI : Inv f T P s0 ι0 S s ι F) {rd : Reg} (hrd : rd ≠ 2) {e : IExpr} {w c : Word}
    (hw : HasInt ι w e) {cu : Nat} (hc : c.toNat = cu) (ha : Fn.disjConst S rd e cu = some S')
    {v : Word} (hv : v = w ||| c ∨ v = w ^^^ c) :
    ∃ ι', (∀ y : Nat, y < f.fresh → ι' y = ι y) ∧
      Inv f T P s0 ι0 S' ((s.setReg rd v).setPc (s.pc + 4)) ι' F ∧
      ((s.setReg rd v).setPc (s.pc + 4)).pc = s.pc + 4 := by
  unfold Fn.disjConst at ha
  by_cases h0 : cu = 0
  · rw [if_pos h0] at ha
    simp only [Option.some.injEq] at ha; subst ha
    refine ⟨ι, fun _ _ => rfl, hI.exact hrd ?_ _, by simp⟩
    have : c = 0#64 := BitVec.eq_of_toNat_eq (by rw [hc, h0]; rfl)
    subst this
    rcases hv with rfl | rfl <;> simpa using hw
  · rw [if_neg h0] at ha
    split at ha
    · rename_i hr
      dsimp only at ha
      split at ha
      · rename_i hd
        simp only [Option.some.injEq] at ha; subst ha
        have hval := disjConst_val hI.hyps hw hc h0 hr hd
        refine ⟨ι, fun _ _ => rfl, hI.exact hrd ?_ _, by simp⟩
        rcases hv with rfl | rfl
        · exact hval.1
        · exact hval.2
      · cases ha
    · cases ha

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
      · cases hr : S.reg rs with
        | none => simp [hr] at ha
        | some e =>
          simp only [hr, Option.bind_some] at ha
          exact Fn.disjConst_sound hI hrd (STy.reg_hasInt hI.regs hr) rfl ha (Or.inr rfl)
    case ori =>
      simp only [Fn.arith2] at ha
      cases hr : S.reg rs with
      | none => simp [hr] at ha
      | some e =>
        simp only [hr, Option.bind_some] at ha
        exact Fn.disjConst_sound hI hrd (STy.reg_hasInt hI.regs hr) rfl ha (Or.inl rfl)
    case andi =>
      simp only [Fn.arith2] at ha
      split at ha
      · rename_i k hk
        have hm : imm.signExtend 64 = BitVec.allOnes 64 <<< k := by
          have := List.find?_some hk; simpa using this
        cases hr : S.reg rs with
        | none => simp [hr] at ha
        | some e =>
          simp only [hr, Option.map_some, Option.some.injEq] at ha; subst ha
          have hre := STy.reg_hasInt hI.regs hr
          have hem := STy.reg_maxVar' hr
          have hv : (evalI .andi (s.reg rs) (imm.signExtend 64)).toNat =
              (s.reg rs).toNat / 2 ^ k * 2 ^ k := by
            simp only [evalI, hm, ← BitVec.shiftLeft_ushiftRight, BitVec.toNat_shiftLeft,
              BitVec.toNat_ushiftRight, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
            apply Nat.mod_eq_of_lt
            exact Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) (s.reg rs).isLt
          have hpk : (0 : Int) < 2 ^ k := by have := Nat.two_pow_pos k; exact_mod_cast this
          let vs : List Int := [(((s.reg rs).toNat / 2 ^ k : Nat) : Int), ((s.reg rs).toNat : Int)]
          refine hI.fresh4 hprot hrd vs ((IExpr.var (f.freshAt S)).smul (2 ^ k)) _
            (evalI .andi (s.reg rs) (imm.signExtend 64)) ?_ (fun p hp => ?_)
          · unfold HasInt
            rw [hv, IExpr.eval_smul, IExpr.eval_var]
            simp only [vs, setFrom_x]
            push_cast; rw [Int.mul_comm]
          · have hu := Fn.urep_spec (x := f.freshAt S + 1) hI hre hem (hag vs).1 (by simp [vs, setFrom_x1])
            simp only [List.mem_append] at hp
            rcases hp with hp | hp
            · exact hu.2 p hp
            · refine quotFacts_holds hpk ?_ p hp
              rw [hu.1]
              simp only [vs, setFrom_x]
              rw [Int.natCast_ediv]; norm_cast
      · split at ha
        · rename_i k hk
          have hk' := List.find?_some hk
          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hk'
          obtain ⟨hk1, hm⟩ := hk'
          have hk12 : k < 12 := List.mem_range.1 (List.mem_of_find?_eq_some hk)
          cases hr : S.reg rs with
          | none => simp [hr] at ha
          | some e =>
            simp only [hr, Option.bind_some] at ha
            split at ha
            · rename_i hrange
              simp only [Option.some.injEq] at ha; subst ha
              have hre := STy.reg_hasInt hI.regs hr
              have hem := STy.reg_maxVar' hr
              have hr' := hI.ent hrange
              simp only [Constr.holds, Constr.eval, Constr.lt, IExpr.eval_add, IExpr.eval_lit,
                Bool.and_eq_true, decide_eq_true_eq] at hr'
              have hn : ((s.reg rs).toNat : Int) = e.eval ι := hre.toNat_eq hr'.1 (by omega)
              let n := (s.reg rs).toNat
              have hv : (evalI .andi (s.reg rs) (imm.signExtend 64)).toNat = 2 ^ k * (n / 2 ^ k % 2) := by
                simp only [evalI, hm, BitVec.and_twoPow]
                have hb := Nat.mod_two_eq_zero_or_one (n / 2 ^ k)
                have ht : (s.reg rs).getLsbD k = decide (n / 2 ^ k % 2 = 1) := by
                  rw [← BitVec.testBit_toNat, Nat.testBit_eq_decide_div_mod_eq]
                rw [ht]
                rcases hb with hb | hb
                · simp [hb]
                · simp only [hb, decide_true, ite_true, BitVec.toNat_twoPow, Nat.mul_one]
                  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))
              have hpk : (0 : Int) < 2 ^ k := by have := Nat.two_pow_pos k; exact_mod_cast this
              let vs : List Int := [((n / 2 ^ k % 2 : Nat) : Int), ((n / 2 ^ k : Nat) : Int)]
              refine hI.fresh4 hprot hrd vs ((IExpr.var (f.freshAt S)).smul (2 ^ k)) _
                (evalI .andi (s.reg rs) (imm.signExtend 64)) ?_ (fun p hp => ?_)
              · unfold HasInt
                rw [hv, IExpr.eval_smul, IExpr.eval_var]
                simp only [vs, setFrom_x]
                push_cast; rfl
              · have hev := Fn.eval_setFrom_old (f := f) hem ι vs
                simp only [List.mem_append] at hp
                rcases hp with hp | hp
                · refine quotFacts_holds hpk ?_ p hp
                  rw [hev, ← hn]
                  simp only [vs, setFrom_x1]
                  rw [Int.natCast_ediv]; norm_cast
                · refine remFacts_holds (by decide) ?_ p hp
                  simp only [IExpr.eval_var, vs, setFrom_x, setFrom_x1]
                  rw [Int.natCast_emod]; rfl
            · cases ha
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
    case max =>
      simp only [Fn.arith2] at ha
      cases h1 : S.reg a with
      | none => simp [h1] at ha
      | some e1 =>
      cases h2 : S.reg b with
      | none => simp [h1, h2] at ha
      | some e2 =>
        simp only [h1, h2, Option.some.injEq, ite_true, ite_false, Bool.false_eq_true] at ha; subst ha
        let vs : List Int := [(evalR .max (s.reg a) (s.reg b)).toInt, (s.reg a).toInt, (s.reg b).toInt]
        refine hI.fresh4 hprot hrd vs (.var (f.freshAt S)) _ (evalR .max (s.reg a) (s.reg b))
          (hasInt_toInt _ _ _ (by simp [vs, setFrom_x])) (fun p hp => ?_)
        have u1 := Fn.srep_spec (x := f.freshAt S + 1) hI (STy.reg_hasInt hI.regs h1) (STy.reg_maxVar' h1)
          (hag vs).1 (by simp [vs, setFrom_x1])
        have u2 := Fn.srep_spec (x := f.freshAt S + 2) hI (STy.reg_hasInt hI.regs h2) (STy.reg_maxVar' h2)
          (hag vs).1 (by simp [vs, setFrom_x2])
        simp only [List.mem_append, List.mem_singleton] at hp
        rcases hp with (hp | hp) | rfl
        · exact u1.2 p hp
        · exact u2.2 p hp
        · refine minMaxFact_holds (v := (evalR .max (s.reg a) (s.reg b)).toInt) (by simp [vs, setFrom_x]) ?_ ?_
          · rw [u1.1, u2.1]; simp only [evalR]; split <;> simp
          · rw [u1.1, u2.1]; simp only [evalR, BitVec.slt, decide_eq_true_eq]
            have hc : (s.reg a).toInt < (s.reg b).toInt ∨ ¬ ((s.reg a).toInt < (s.reg b).toInt) := Classical.em _
            rcases hc with hc | hc <;> simp [hc] <;> omega
    case min =>
      simp only [Fn.arith2] at ha
      cases h1 : S.reg a with
      | none => simp [h1] at ha
      | some e1 =>
      cases h2 : S.reg b with
      | none => simp [h1, h2] at ha
      | some e2 =>
        simp only [h1, h2, Option.some.injEq, ite_true, ite_false, Bool.false_eq_true] at ha; subst ha
        let vs : List Int := [(evalR .min (s.reg a) (s.reg b)).toInt, (s.reg a).toInt, (s.reg b).toInt]
        refine hI.fresh4 hprot hrd vs (.var (f.freshAt S)) _ (evalR .min (s.reg a) (s.reg b))
          (hasInt_toInt _ _ _ (by simp [vs, setFrom_x])) (fun p hp => ?_)
        have u1 := Fn.srep_spec (x := f.freshAt S + 1) hI (STy.reg_hasInt hI.regs h1) (STy.reg_maxVar' h1)
          (hag vs).1 (by simp [vs, setFrom_x1])
        have u2 := Fn.srep_spec (x := f.freshAt S + 2) hI (STy.reg_hasInt hI.regs h2) (STy.reg_maxVar' h2)
          (hag vs).1 (by simp [vs, setFrom_x2])
        simp only [List.mem_append, List.mem_singleton] at hp
        rcases hp with (hp | hp) | rfl
        · exact u1.2 p hp
        · exact u2.2 p hp
        · refine minMaxFact_holds (v := (evalR .min (s.reg a) (s.reg b)).toInt) (by simp [vs, setFrom_x]) ?_ ?_
          · rw [u1.1, u2.1]; simp only [evalR]; split <;> simp
          · rw [u1.1, u2.1]; simp only [evalR, BitVec.slt, decide_eq_true_eq]
            have hc : (s.reg a).toInt < (s.reg b).toInt ∨ ¬ ((s.reg a).toInt < (s.reg b).toInt) := Classical.em _
            rcases hc with hc | hc <;> simp [hc] <;> omega
    case maxu =>
      simp only [Fn.arith2] at ha
      cases h1 : S.reg a with
      | none => simp [h1] at ha
      | some e1 =>
      cases h2 : S.reg b with
      | none => simp [h1, h2] at ha
      | some e2 =>
        simp only [h1, h2, Option.some.injEq, ite_true, ite_false, Bool.false_eq_true] at ha; subst ha
        let vs : List Int := [((evalR .maxu (s.reg a) (s.reg b)).toNat : Int), ((s.reg a).toNat : Int), ((s.reg b).toNat : Int)]
        refine hI.fresh4 hprot hrd vs (.var (f.freshAt S)) _ (evalR .maxu (s.reg a) (s.reg b))
          (hasInt_toNat _ _ _ (by simp [vs, setFrom_x])) (fun p hp => ?_)
        have u1 := Fn.urep_spec (x := f.freshAt S + 1) hI (STy.reg_hasInt hI.regs h1) (STy.reg_maxVar' h1)
          (hag vs).1 (by simp [vs, setFrom_x1])
        have u2 := Fn.urep_spec (x := f.freshAt S + 2) hI (STy.reg_hasInt hI.regs h2) (STy.reg_maxVar' h2)
          (hag vs).1 (by simp [vs, setFrom_x2])
        simp only [List.mem_append, List.mem_singleton] at hp
        rcases hp with (hp | hp) | rfl
        · exact u1.2 p hp
        · exact u2.2 p hp
        · refine minMaxFact_holds (v := ((evalR .maxu (s.reg a) (s.reg b)).toNat : Int)) (by simp [vs, setFrom_x]) ?_ ?_
          · rw [u1.1, u2.1]; simp only [evalR]; split <;> simp
          · rw [u1.1, u2.1]; simp only [evalR, BitVec.ult, decide_eq_true_eq]
            have hc : (s.reg a).toNat < (s.reg b).toNat ∨ ¬ ((s.reg a).toNat < (s.reg b).toNat) := Classical.em _
            rcases hc with hc | hc <;> simp [hc] <;> omega
    case minu =>
      simp only [Fn.arith2] at ha
      cases h1 : S.reg a with
      | none => simp [h1] at ha
      | some e1 =>
      cases h2 : S.reg b with
      | none => simp [h1, h2] at ha
      | some e2 =>
        simp only [h1, h2, Option.some.injEq, ite_true, ite_false, Bool.false_eq_true] at ha; subst ha
        let vs : List Int := [((evalR .minu (s.reg a) (s.reg b)).toNat : Int), ((s.reg a).toNat : Int), ((s.reg b).toNat : Int)]
        refine hI.fresh4 hprot hrd vs (.var (f.freshAt S)) _ (evalR .minu (s.reg a) (s.reg b))
          (hasInt_toNat _ _ _ (by simp [vs, setFrom_x])) (fun p hp => ?_)
        have u1 := Fn.urep_spec (x := f.freshAt S + 1) hI (STy.reg_hasInt hI.regs h1) (STy.reg_maxVar' h1)
          (hag vs).1 (by simp [vs, setFrom_x1])
        have u2 := Fn.urep_spec (x := f.freshAt S + 2) hI (STy.reg_hasInt hI.regs h2) (STy.reg_maxVar' h2)
          (hag vs).1 (by simp [vs, setFrom_x2])
        simp only [List.mem_append, List.mem_singleton] at hp
        rcases hp with (hp | hp) | rfl
        · exact u1.2 p hp
        · exact u2.2 p hp
        · refine minMaxFact_holds (v := ((evalR .minu (s.reg a) (s.reg b)).toNat : Int)) (by simp [vs, setFrom_x]) ?_ ?_
          · rw [u1.1, u2.1]; simp only [evalR]; split <;> simp
          · rw [u1.1, u2.1]; simp only [evalR, BitVec.ult, decide_eq_true_eq]
            have hc : (s.reg a).toNat < (s.reg b).toNat ∨ ¬ ((s.reg a).toNat < (s.reg b).toNat) := Classical.em _
            rcases hc with hc | hc <;> simp [hc] <;> omega
    case divu | remu =>
      simp only [Fn.arith2] at ha
      cases h1 : S.reg a with
      | none => simp [h1] at ha
      | some e1 =>
      cases h2 : S.reg b with
      | none => simp [h1, h2] at ha
      | some e2 =>
        obtain ⟨c, ts⟩ := e2
        cases ts with
        | cons t ts =>
          simp only [h1, h2] at ha
          split at ha
          · rename_i hc
            obtain ⟨hnil, hpos⟩ := hc
            have hpos := hI.ent hpos
            rw [Fn.urep_fst_of_nil hnil] at hpos
            simp only [Constr.holds, Constr.eval, Constr.lt, IExpr.eval_add, IExpr.eval_lit,
              decide_eq_true_eq] at hpos
            have hbpos : 0 < (s.reg b).toNat := by
              have hr := hI.ent (Fn.urep_nil_ent hnil)
              simp only [Constr.holds, Constr.eval, Constr.lt, IExpr.eval_add, IExpr.eval_lit,
                Bool.and_eq_true, decide_eq_true_eq] at hr
              have := (STy.reg_hasInt hI.regs h2).toNat_eq hr.1 (by omega)
              omega
            have hbne : s.reg b ≠ 0 := fun h0 => by rw [h0] at hbpos; simp at hbpos
            first
            | (simp only [ite_true, Option.some.injEq] at ha; subst ha
               let vs : List Int := [((evalR .divu (s.reg a) (s.reg b)).toNat : Int),
                 ((s.reg a).toNat : Int), ((s.reg b).toNat : Int)]
               refine hI.fresh4 hprot hrd vs (.var (f.freshAt S)) _ (evalR .divu (s.reg a) (s.reg b))
                 (hasInt_toNat _ _ _ (by simp [vs, setFrom_x])) (fun p hp => ?_)
               have u1 := Fn.urep_spec (x := f.freshAt S + 1) hI (STy.reg_hasInt hI.regs h1)
                 (STy.reg_maxVar' h1) (hag vs).1 (by simp [vs, setFrom_x1])
               have u2 := Fn.urep_spec (x := f.freshAt S + 2) hI (STy.reg_hasInt hI.regs h2)
                 (STy.reg_maxVar' h2) (hag vs).1 (by simp [vs, setFrom_x2])
               simp only [List.mem_append] at hp
               rcases hp with hp | hp
               · exact u1.2 p hp
               · refine divBound_holds (r := (evalR .divu (s.reg a) (s.reg b)).toNat)
                   (by simp [vs, setFrom_x]) u1.1 u2.1 (BitVec.isLt _) ?_ (fun h => by cases h) p hp
                 simp only [evalR, rvDivu, hbne, if_false, BitVec.toNat_udiv]
                 exact Nat.div_le_self _ _)
            | (simp only [Bool.false_eq_true, ite_false, Option.some.injEq] at ha; subst ha
               let vs : List Int := [((evalR .remu (s.reg a) (s.reg b)).toNat : Int),
                 ((s.reg a).toNat : Int), ((s.reg b).toNat : Int)]
               refine hI.fresh4 hprot hrd vs (.var (f.freshAt S)) _ (evalR .remu (s.reg a) (s.reg b))
                 (hasInt_toNat _ _ _ (by simp [vs, setFrom_x])) (fun p hp => ?_)
               have u1 := Fn.urep_spec (x := f.freshAt S + 1) hI (STy.reg_hasInt hI.regs h1)
                 (STy.reg_maxVar' h1) (hag vs).1 (by simp [vs, setFrom_x1])
               have u2 := Fn.urep_spec (x := f.freshAt S + 2) hI (STy.reg_hasInt hI.regs h2)
                 (STy.reg_maxVar' h2) (hag vs).1 (by simp [vs, setFrom_x2])
               simp only [List.mem_append] at hp
               rcases hp with hp | hp
               · exact u1.2 p hp
               · refine divBound_holds (r := (evalR .remu (s.reg a) (s.reg b)).toNat)
                   (by simp [vs, setFrom_x]) u1.1 u2.1 (BitVec.isLt _) ?_ ?_ p hp
                 · simp only [evalR, rvRemu, hbne, if_false, BitVec.toNat_umod]
                   exact Nat.mod_le _ _
                 · intro _
                   simp only [evalR, rvRemu, hbne, if_false, BitVec.toNat_umod]
                   exact Nat.mod_lt _ hbpos)
          · cases ha
        | nil =>
        simp only [h1, h2] at ha
        split at ha
        · rename_i hcpos
          have hb := toNat_of_lit (STy.reg_hasInt hI.regs h2)
          have hbne : s.reg b ≠ 0 := by
            intro h0; rw [h0] at hb; simp at hb; omega
          first
          | (simp only [ite_true, Option.some.injEq] at ha; subst ha
             let vs : List Int := [((evalR .divu (s.reg a) (s.reg b)).toNat : Int), ((s.reg a).toNat : Int)]
             refine hI.fresh4 hprot hrd vs (.var (f.freshAt S)) _ (evalR .divu (s.reg a) (s.reg b))
               (hasInt_toNat _ _ _ (by simp [vs, setFrom_x])) (fun p hp => ?_)
             have u1 := Fn.urep_spec (x := f.freshAt S + 1) hI (STy.reg_hasInt hI.regs h1) (STy.reg_maxVar' h1)
               (hag vs).1 (by simp [vs, setFrom_x1])
             simp only [List.mem_append] at hp
             rcases hp with hp | hp
             · exact u1.2 p hp
             · refine quotFacts_holds hcpos ?_ p hp
               rw [u1.1, ← hb]
               simp only [vs, setFrom_x, evalR, rvDivu, hbne, if_false, BitVec.toNat_udiv]
               push_cast; rfl)
          | (simp only [Bool.false_eq_true, ite_false, Option.some.injEq] at ha; subst ha
             let vs : List Int := [((evalR .remu (s.reg a) (s.reg b)).toNat : Int), ((s.reg a).toNat : Int)]
             refine hI.fresh4 hprot hrd vs (.var (f.freshAt S)) _ (evalR .remu (s.reg a) (s.reg b))
               (hasInt_toNat _ _ _ (by simp [vs, setFrom_x])) (fun p hp => ?_)
             have u1 := Fn.urep_spec (x := f.freshAt S + 1) hI (STy.reg_hasInt hI.regs h1) (STy.reg_maxVar' h1)
               (hag vs).1 (by simp [vs, setFrom_x1])
             simp only [List.mem_append] at hp
             rcases hp with hp | hp
             · exact u1.2 p hp
             · refine remFacts_holds hcpos ?_ p hp
               rw [u1.1, ← hb]
               simp only [vs, setFrom_x, evalR, rvRemu, hbne, if_false, BitVec.toNat_umod]
               push_cast; rfl)
        · cases ha
    case xor =>
      simp only [Fn.arith2] at ha
      cases h1 : S.reg a with
      | none => simp [h1] at ha
      | some e1 =>
      cases h2 : S.reg b with
      | none => simp [h1, h2] at ha
      | some e2 =>
        simp only [h1, h2, Option.some.injEq] at ha; subst ha
        have k1 := STy.reg_hasInt hI.regs h1
        have k2 := STy.reg_hasInt hI.regs h2
        let vs : List Int := [((evalR .xor (s.reg a) (s.reg b)).toNat : Int)]
        refine hI.fresh4 hprot hrd vs (.var (f.freshAt S)) _ (evalR .xor (s.reg a) (s.reg b))
          (hasInt_toNat _ _ _ (by simp [vs, setFrom_x])) (fun p hp => ?_)
        have ev1 := Fn.eval_setFrom_old (f := f) (STy.reg_maxVar' h1) ι vs
        have ev2 := Fn.eval_setFrom_old (f := f) (STy.reg_maxVar' h2) ι vs
        have hv : setFrom ι (f.freshAt S) vs (f.freshAt S) = ((s.reg a ^^^ s.reg b).toNat : Int) := by
          simp [vs, setFrom_x, evalR]
        have hiff : (s.reg a ^^^ s.reg b).toNat = 0 ↔ (s.reg a).toNat = (s.reg b).toNat := by
          constructor
          · intro h
            have : s.reg a ^^^ s.reg b = 0#64 := BitVec.eq_of_toNat_eq (by simpa using h)
            rw [BitVec.xor_eq_zero_iff] at this; rw [this]
          · intro h
            rw [BitVec.eq_of_toNat_eq h, BitVec.xor_self]; rfl
        unfold HasInt at k1 k2
        have ha' := (s.reg a).isLt; have hb' := (s.reg b).isLt
        have hx' := (s.reg a ^^^ s.reg b).isLt
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl
        · simp only [Constr.holds, Constr.eval, decide_eq_true_eq, IExpr.eval_var, IExpr.eval_lit, hv]; omega
        · simp only [Constr.holds, Constr.eval, Constr.lt, decide_eq_true_eq, IExpr.eval_var,
            IExpr.eval_lit, IExpr.eval_add, hv]; omega
        · simp only [Constr.holds, Constr.eval, Constr.eqMod, Bool.or_eq_true, Bool.and_eq_true,
            Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not, IExpr.eval_var,
            IExpr.eval_lit, IExpr.eval_sub, hv, ev1, ev2]
          by_cases h : (s.reg a).toNat = (s.reg b).toNat
          · left; exact ⟨by have := hiff.2 h; omega, by omega⟩
          · right; exact ⟨by intro h'; exact h (hiff.1 (by omega)), by omega⟩
    case and =>
      simp only [Fn.arith2] at ha
      cases h1 : S.reg a with
      | none => simp [h1] at ha
      | some e1 =>
      cases h2 : S.reg b with
      | none => simp [h1, h2] at ha
      | some e2 =>
        simp only [h1, h2] at ha
        split at ha
        · rename_i hbits
          simp only [Bool.and_eq_true] at hbits
          simp only [Option.some.injEq] at ha; subst ha
          have k1 := STy.reg_hasInt hI.regs h1
          have k2 := STy.reg_hasInt hI.regs h2
          let vs : List Int := [((evalR .and (s.reg a) (s.reg b)).toNat : Int)]
          refine hI.fresh4 hprot hrd vs (.var (f.freshAt S)) _ _
            (hasInt_toNat _ _ _ (by simp [vs, setFrom_x])) (fun p hp => ?_)
          simp only [List.mem_singleton] at hp; subst hp
          have ev1 := Fn.eval_setFrom_old (f := f) (STy.reg_maxVar' h1) ι vs
          have ev2 := Fn.eval_setFrom_old (f := f) (STy.reg_maxVar' h2) ι vs
          rcases bit_of_isBit k1 (hI.ent hbits.1) with ⟨ea, va⟩ | ⟨ea, va⟩ <;>
          rcases bit_of_isBit k2 (hI.ent hbits.2) with ⟨eb, vb⟩ | ⟨eb, vb⟩ <;>
          · first
            | exact bitTable_holds (p := 0) (q := 0) (by decide) (by decide) (by rw [ev1, va]; rfl) (by rw [ev2, vb]; rfl)
                (by simp [vs, setFrom_x, evalR, ea, eb])
            | exact bitTable_holds (p := 0) (q := 1) (by decide) (by decide) (by rw [ev1, va]; rfl) (by rw [ev2, vb]; rfl)
                (by simp [vs, setFrom_x, evalR, ea, eb])
            | exact bitTable_holds (p := 1) (q := 0) (by decide) (by decide) (by rw [ev1, va]; rfl) (by rw [ev2, vb]; rfl)
                (by simp [vs, setFrom_x, evalR, ea, eb])
            | exact bitTable_holds (p := 1) (q := 1) (by decide) (by decide) (by rw [ev1, va]; rfl) (by rw [ev2, vb]; rfl)
                (by simp [vs, setFrom_x, evalR, ea, eb])
        · cases ha
    case or =>
      simp only [Fn.arith2] at ha
      cases h1 : S.reg a with
      | none => simp [h1] at ha
      | some e1 =>
      cases h2 : S.reg b with
      | none => simp [h1, h2] at ha
      | some e2 =>
        simp only [h1, h2] at ha
        split at ha
        · rename_i hbits
          simp only [Bool.and_eq_true] at hbits
          simp only [Option.some.injEq] at ha; subst ha
          have k1 := STy.reg_hasInt hI.regs h1
          have k2 := STy.reg_hasInt hI.regs h2
          let vs : List Int := [((evalR .or (s.reg a) (s.reg b)).toNat : Int)]
          refine hI.fresh4 hprot hrd vs (.var (f.freshAt S)) _ _
            (hasInt_toNat _ _ _ (by simp [vs, setFrom_x])) (fun p hp => ?_)
          simp only [List.mem_singleton] at hp; subst hp
          have ev1 := Fn.eval_setFrom_old (f := f) (STy.reg_maxVar' h1) ι vs
          have ev2 := Fn.eval_setFrom_old (f := f) (STy.reg_maxVar' h2) ι vs
          rcases bit_of_isBit k1 (hI.ent hbits.1) with ⟨ea, va⟩ | ⟨ea, va⟩ <;>
          rcases bit_of_isBit k2 (hI.ent hbits.2) with ⟨eb, vb⟩ | ⟨eb, vb⟩ <;>
          · first
            | exact bitTable_holds (p := 0) (q := 0) (by decide) (by decide) (by rw [ev1, va]; rfl) (by rw [ev2, vb]; rfl)
                (by simp [vs, setFrom_x, evalR, ea, eb])
            | exact bitTable_holds (p := 0) (q := 1) (by decide) (by decide) (by rw [ev1, va]; rfl) (by rw [ev2, vb]; rfl)
                (by simp [vs, setFrom_x, evalR, ea, eb])
            | exact bitTable_holds (p := 1) (q := 0) (by decide) (by decide) (by rw [ev1, va]; rfl) (by rw [ev2, vb]; rfl)
                (by simp [vs, setFrom_x, evalR, ea, eb])
            | exact bitTable_holds (p := 1) (q := 1) (by decide) (by decide) (by rw [ev1, va]; rfl) (by rw [ev2, vb]; rfl)
                (by simp [vs, setFrom_x, evalR, ea, eb])
        · cases ha
    all_goals simp [Fn.arith2] at ha
  | rwop op rd' a b =>
    simp only [writesReg, Option.some.injEq] at hw; subst hw
    simp only [exec, Option.some.injEq] at hx; subst hx
    have zx : ∀ (n : Nat) (vs : List Int), vs = [(((s.reg a).toNat % 2 ^ 32 : Nat) : Int)] →
        HasInt (setFrom ι (f.freshAt S) vs) (zext32 (s.reg a)) (.var (f.freshAt S)) := by
      intro n vs h; subst h; exact hasInt_toNat _ _ _ (by simp [setFrom_x, zext32_toNat])
    cases op
    case mulw =>
      simp only [Fn.arith2] at ha
      cases h1 : S.reg a with
      | none => simp [h1] at ha
      | some e1 =>
      cases h2 : S.reg b with
      | none => simp [h1, h2] at ha
      | some e2 =>
        have ha' := STy.reg_hasInt hI.regs h1
        have hb' := STy.reg_hasInt hI.regs h2
        unfold HasInt at ha' hb'
        have hm := w32_mul_mod ha' hb'
        obtain ⟨c2, ts2⟩ := e2
        cases ts2 with
        | nil =>
          simp only [h1, h2, Option.some.injEq] at ha; subst ha
          simp only [evalRW, w32]
          refine hI.word32' hprot hrd (by rw [IExpr.maxVar_smul']; exact STy.reg_maxVar' h1) _ ?_
          rw [IExpr.eval_smul, Int.mul_comm]
          simpa [IExpr.eval] using hm
        | cons t ts =>
          obtain ⟨c1, ts1⟩ := e1
          cases ts1 with
          | cons t' ts' => simp [h1, h2] at ha
          | nil =>
            simp only [h1, h2, Option.some.injEq] at ha; subst ha
            simp only [evalRW, w32]
            refine hI.word32' hprot hrd (by rw [IExpr.maxVar_smul']; exact STy.reg_maxVar' h2) _ ?_
            rw [IExpr.eval_smul]
            simpa [IExpr.eval] using hm
    case adduw | sh1adduw | sh2adduw | sh3adduw =>
      simp only [Fn.arith2] at ha
      cases h1 : S.reg a with
      | none => simp [h1] at ha
      | some e1 =>
      cases h2 : S.reg b with
      | none => simp [h1, h2] at ha
      | some e2 =>
        simp only [h1, h2, Option.some.injEq] at ha; subst ha
        let vs : List Int := [(((s.reg a).toNat % 2 ^ 32 : Nat) : Int)]
        have hz := zx 0 vs rfl
        have he2 : HasInt (setFrom ι (f.freshAt S) vs) (s.reg b) e2 :=
          (STy.reg_hasInt hI.regs h2).of_eq (Fn.eval_setFrom_old (STy.reg_maxVar' h2) ι vs).symm
        refine hI.fresh4 hprot hrd vs _ _ _ ?_
          (lowFacts_holds (by omega) (STy.reg_hasInt hI.regs h1 |>.of_eq
            (Fn.eval_setFrom_old (STy.reg_maxVar' h1) ι vs).symm) (by simp [vs, setFrom_x]))
        simp only [evalRW]
        first
          | exact hasInt_add (by simpa using hasInt_shl hz 0) he2
          | exact hasInt_add (hasInt_shl hz _) he2
    all_goals simp [Fn.arith2] at ha
  | shift op rd' rs sh =>
    simp only [writesReg, Option.some.injEq] at hw; subst hw
    simp only [exec, Option.some.injEq] at hx; subst hx
    cases op
    case slliuw =>
      simp only [Fn.arith2] at ha
      cases hr : S.reg rs with
      | none => simp [hr] at ha
      | some e =>
        simp only [hr, Option.map_some, Option.some.injEq] at ha; subst ha
        let vs : List Int := [(((s.reg rs).toNat % 2 ^ 32 : Nat) : Int)]
        have hz : HasInt (setFrom ι (f.freshAt S) vs) (zext32 (s.reg rs)) (.var (f.freshAt S)) :=
          hasInt_toNat _ _ _ (by simp [vs, setFrom_x, zext32_toNat])
        refine hI.fresh4 hprot hrd vs _ _ _ ?_
          (lowFacts_holds (by omega) (STy.reg_hasInt hI.regs hr |>.of_eq
            (Fn.eval_setFrom_old (STy.reg_maxVar' hr) ι vs).symm) (by simp [vs, setFrom_x]))
        simp only [evalSh]
        exact hasInt_shl hz _
    case srai =>
      simp only [Fn.arith2] at ha
      cases hr : S.reg rs with
      | none => simp [hr] at ha
      | some e =>
        simp only [hr, Option.map_some, Option.some.injEq] at ha; subst ha
        let vs : List Int := [(evalSh .srai (s.reg rs) sh.toNat).toInt, (s.reg rs).toInt]
        refine hI.fresh4 hprot hrd vs (.var (f.freshAt S)) _ (evalSh .srai (s.reg rs) sh.toNat)
          (hasInt_toInt _ _ _ (by simp [vs, setFrom_x])) (fun p hp => ?_)
        have u1 := Fn.srep_spec (x := f.freshAt S + 1) hI (STy.reg_hasInt hI.regs hr) (STy.reg_maxVar' hr)
          (hag vs).1 (by simp [vs, setFrom_x1])
        simp only [List.mem_append] at hp
        rcases hp with hp | hp
        · exact u1.2 p hp
        · refine quotFacts_holds (by have := Nat.two_pow_pos sh.toNat; exact_mod_cast this) ?_ p hp
          rw [u1.1]
          simp only [vs, setFrom_x, evalSh, BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]
          norm_cast
    all_goals simp [Fn.arith2] at ha
  | shiftw op rd' rs sh =>
    simp only [writesReg, Option.some.injEq] at hw; subst hw
    simp only [exec, Option.some.injEq] at hx; subst hx
    cases op
    case slliw =>
      simp only [Fn.arith2] at ha
      cases hr : S.reg rs with
      | none => simp [hr] at ha
      | some e =>
        simp only [hr, Option.map_some, Option.some.injEq] at ha; subst ha
        have hre := STy.reg_hasInt hI.regs hr
        unfold HasInt at hre
        simp only [evalShW]
        refine hI.word32' hprot hrd (by rw [IExpr.maxVar_smul']; exact STy.reg_maxVar' hr) _ ?_
        rw [IExpr.eval_smul]
        have := w32_shl_mod sh.toNat hre
        rw [Int.natCast_pow] at this
        exact this
    case srliw =>
      simp only [Fn.arith2] at ha
      split at ha
      · rename_i hsh
        cases hr : S.reg rs with
        | none => simp [hr] at ha
        | some e =>
          simp only [hr, Option.map_some, Option.some.injEq] at ha; subst ha
          -- the shifted low word, below 2^31
          have hy : (((s.reg rs).setWidth 32) >>> sh.toNat).toNat = (s.reg rs).toNat % 2 ^ 32 / 2 ^ sh.toNat := by
            rw [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow]
          have hylt : (((s.reg rs).setWidth 32) >>> sh.toNat).toNat < 2 ^ 31 := by
            rw [hy]
            have h32 := Nat.mod_lt (s.reg rs).toNat (show 0 < 2 ^ 32 by decide)
            have hp2 : 2 ≤ 2 ^ sh.toNat := by
              calc 2 = 2 ^ 1 := rfl
                _ ≤ 2 ^ sh.toNat := Nat.pow_le_pow_right (by decide) hsh
            refine Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_le h32 ?_)
            calc 2 ^ 32 = 2 * 2 ^ 31 := by decide
              _ ≤ 2 ^ sh.toNat * 2 ^ 31 := Nat.mul_le_mul_right _ hp2
          have hv : (evalShW .srliw (s.reg rs) sh.toNat).toInt =
              (((s.reg rs).toNat % 2 ^ 32 / 2 ^ sh.toNat : Nat) : Int) := by
            simp only [evalShW]
            rw [BitVec.toInt_signExtend_of_le (by omega), BitVec.toInt_eq_toNat_cond, if_pos (by omega), hy]
          let vs : List Int := [(evalShW .srliw (s.reg rs) sh.toNat).toInt,
            (((s.reg rs).toNat % 2 ^ 32 : Nat) : Int)]
          refine hI.fresh4 hprot hrd vs (.var (f.freshAt S)) _ (evalShW .srliw (s.reg rs) sh.toNat)
            (hasInt_toInt _ _ _ (by simp [vs, setFrom_x])) (fun p hp => ?_)
          simp only [List.mem_append] at hp
          rcases hp with hp | hp
          · exact lowFacts_holds (by omega) ((STy.reg_hasInt hI.regs hr).of_eq
              (Fn.eval_setFrom_old (STy.reg_maxVar' hr) ι vs).symm) (by simp [vs, setFrom_x1]) p hp
          · refine quotFacts_holds (by have := Nat.two_pow_pos sh.toNat; exact_mod_cast this) ?_ p hp
            have e0 : setFrom ι (f.freshAt S) vs (f.freshAt S) = (evalShW .srliw (s.reg rs) sh.toNat).toInt := by
              simp [vs, setFrom_x]
            have e1 : setFrom ι (f.freshAt S) vs (f.freshAt S + 1) = (((s.reg rs).toNat % 2 ^ 32 : Nat) : Int) := by
              simp [vs, setFrom_x1]
            rw [IExpr.eval_var, e0, e1, hv, Int.natCast_ediv]
            norm_cast
      · cases ha
    all_goals (simp only [Fn.arith2, reduceCtorEq] at ha)
  | uop op rd' rs =>
    simp only [writesReg, Option.some.injEq] at hw; subst hw
    simp only [exec, Option.some.injEq] at hx; subst hx
    cases op
    case clz | ctz | cpop | clzw | ctzw | cpopw =>
      simp only [Fn.arith2, Option.some.injEq] at ha; subst ha
      have hb := bitcount_le (s.reg rs)
      refine hI.fresh4 hprot hrd [_] (.var (f.freshAt S)) _ _
        (hasInt_toNat _ _ _ setFrom_x) (boundFacts_holds setFrom_x ?_)
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hb
      omega
    case zexth =>
      simp only [Fn.arith2] at ha
      cases hr : S.reg rs with
      | none => simp [hr] at ha
      | some e =>
        simp only [hr, Option.map_some, Option.some.injEq] at ha; subst ha
        let vs : List Int := [(((s.reg rs).toNat % 2 ^ 16 : Nat) : Int)]
        refine hI.fresh4 hprot hrd vs _ _ _ ?_
          (lowFacts_holds (by omega) (STy.reg_hasInt hI.regs hr |>.of_eq
            (Fn.eval_setFrom_old (STy.reg_maxVar' hr) ι vs).symm) (by simp [vs, setFrom_x]))
        simp only [evalU]
        exact hasInt_toNat _ _ _ (by simp [vs, setFrom_x, zexth_toNat]; omega)
    all_goals simp [Fn.arith2] at ha
  | _ => simp [Fn.arith2] at ha


theorem Fn.andConstOf_sound (hprot : ∀ x ∈ f.protectedVars, x < f.fresh) {S S' : STy} {s : State}
    {ι : Val} {F : TokFp} (hI : Inv f T P s0 ι0 S s ι F) {rd : Reg} (hrd : rd ≠ 2) {e : IExpr}
    {c : Int} {w wc : Word} (hw : HasInt ι w e) (hem : e.maxVar ≤ S.maxVar)
    (hc : HasInt ι wc ⟨c, []⟩) (ha : Fn.andConstOf S rd (f.freshAt S) e c = some S') :
    ∃ ι', (∀ y : Nat, y < f.fresh → ι' y = ι y) ∧
      Inv f T P s0 ι0 S' ((s.setReg rd (w &&& wc)).setPc (s.pc + 4)) ι' F ∧
      ((s.setReg rd (w &&& wc)).setPc (s.pc + 4)).pc = s.pc + 4 := by
  have hag := setFrom_fresh hprot S ι
  have hcI := toNat_of_lit hc
  have hcu : wc.toNat = (c % 2 ^ 64).toNat := by omega
  unfold Fn.andConstOf at ha
  dsimp only at ha
  split at ha
  · rename_i k hk
    have hk' := List.find?_some hk
    simp only [beq_iff_eq] at hk'
    simp only [Option.some.injEq] at ha; subst ha
    have hv : (w &&& wc).toNat = w.toNat % 2 ^ k := by
      rw [BitVec.toNat_and, hcu, hk', Nat.and_two_pow_sub_one_eq_mod]
    have hk64 : k < 64 := List.mem_range.1 (List.mem_of_find?_eq_some hk)
    let vs : List Int := [((w.toNat % 2 ^ k : Nat) : Int)]
    exact hI.fresh4 hprot hrd vs (.var (f.freshAt S)) _ _
      (hasInt_toNat _ _ _ (by simp [vs, setFrom_x, hv]))
      (lowFacts_holds (by omega) (hw.of_eq (Fn.eval_setFrom_old hem ι vs).symm) (by simp [vs, setFrom_x]))
  · split at ha
    · rename_i k hk
      have hk' := List.find?_some hk
      simp only [beq_iff_eq] at hk'
      have hk64 : k < 64 := List.mem_range.1 (List.mem_of_find?_eq_some hk)
      simp only [Option.some.injEq] at ha; subst ha
      have hm : wc = BitVec.allOnes 64 <<< k := by
        apply BitVec.eq_of_toNat_eq
        rw [hcu, BitVec.toNat_shiftLeft, BitVec.toNat_allOnes, Nat.shiftLeft_eq]
        have hp1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
        have hp2 : 2 ^ k ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by omega)
        generalize 2 ^ k = Pk at hk' hp1 hp2 ⊢
        omega
      have hv : (w &&& wc).toNat = w.toNat / 2 ^ k * 2 ^ k := by
        rw [hm, ← BitVec.shiftLeft_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
          Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
        apply Nat.mod_eq_of_lt
        exact Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) w.isLt
      have hpk : (0 : Int) < 2 ^ k := by have := Nat.two_pow_pos k; exact_mod_cast this
      let vs : List Int := [((w.toNat / 2 ^ k : Nat) : Int), (w.toNat : Int)]
      refine hI.fresh4 hprot hrd vs ((IExpr.var (f.freshAt S)).smul (2 ^ k)) _ (w &&& wc) ?_ (fun p hp => ?_)
      · unfold HasInt
        rw [hv, IExpr.eval_smul, IExpr.eval_var]
        simp only [vs, setFrom_x]
        push_cast; rw [Int.mul_comm]
      · have hu := Fn.urep_spec (x := f.freshAt S + 1) hI hw hem (hag vs).1 (by simp [vs, setFrom_x1])
        simp only [List.mem_append] at hp
        rcases hp with hp | hp
        · exact hu.2 p hp
        · refine quotFacts_holds hpk ?_ p hp
          rw [hu.1]
          simp only [vs, setFrom_x]
          rw [Int.natCast_ediv]; norm_cast
    · cases ha

theorem Fn.andConst_sound (hprot : ∀ x ∈ f.protectedVars, x < f.fresh) {S S' : STy} {s s' : State}
    {ι : Val} {F : TokFp} (hI : Inv f T P s0 ι0 S s ι F) {i : Instr} {rd : Reg}
    (hw : writesReg i = some rd) (hrd : rd ≠ 2) (ha : f.andConst S i = some S')
    (hx : exec i s = some s') :
    ∃ ι', (∀ y : Nat, y < f.fresh → ι' y = ι y) ∧ Inv f T P s0 ι0 S' s' ι' F ∧ s'.pc = s.pc + 4 := by
  cases i with
  | rop op rd' a b =>
    simp only [writesReg, Option.some.injEq] at hw; subst hw
    simp only [exec, Option.some.injEq] at hx; subst hx
    cases op
    case and =>
      simp only [Fn.andConst] at ha
      cases h1 : S.reg a with
      | none => simp [h1] at ha
      | some e1 =>
      cases h2 : S.reg b with
      | none => simp [h1, h2] at ha
      | some e2 =>
        obtain ⟨c2, ts2⟩ := e2
        cases ts2 with
        | nil =>
          simp only [h1, h2] at ha
          exact f.andConstOf_sound hprot hI hrd (STy.reg_hasInt hI.regs h1) (STy.reg_maxVar' h1)
            (STy.reg_hasInt hI.regs h2) ha
        | cons t ts =>
          obtain ⟨c1, ts1⟩ := e1
          cases ts1 with
          | cons t' ts' => simp [h1, h2] at ha
          | nil =>
            simp only [h1, h2] at ha
            have := f.andConstOf_sound hprot hI hrd (STy.reg_hasInt hI.regs h2) (STy.reg_maxVar' h2)
              (STy.reg_hasInt hI.regs h1) ha
            simp only [evalR]
            rw [BitVec.and_comm]
            exact this
    case or | xor =>
      simp only [Fn.andConst] at ha
      cases h1 : S.reg a with
      | none => simp [h1] at ha
      | some e1 =>
      cases h2 : S.reg b with
      | none => simp [h1, h2] at ha
      | some e2 =>
        obtain ⟨c2, ts2⟩ := e2
        cases ts2 with
        | nil =>
          simp only [h1, h2] at ha
          have hcI := toNat_of_lit (STy.reg_hasInt hI.regs h2)
          have hc : (s.reg b).toNat = (c2 % 2 ^ 64).toNat := by omega
          first
          | exact Fn.disjConst_sound hI hrd (STy.reg_hasInt hI.regs h1) hc ha (Or.inl rfl)
          | exact Fn.disjConst_sound hI hrd (STy.reg_hasInt hI.regs h1) hc ha (Or.inr rfl)
        | cons t ts =>
          obtain ⟨c1, ts1⟩ := e1
          cases ts1 with
          | cons t' ts' => simp [h1, h2] at ha
          | nil =>
            simp only [h1, h2] at ha
            have hcI := toNat_of_lit (STy.reg_hasInt hI.regs h1)
            have hc : (s.reg a).toNat = (c1 % 2 ^ 64).toNat := by omega
            first
            | exact Fn.disjConst_sound hI hrd (STy.reg_hasInt hI.regs h2) hc ha
                (Or.inl (by simp only [evalR]; exact BitVec.or_comm _ _))
            | exact Fn.disjConst_sound hI hrd (STy.reg_hasInt hI.regs h2) hc ha
                (Or.inr (by simp only [evalR]; exact BitVec.xor_comm _ _))
    all_goals simp [Fn.andConst] at ha
  | _ => simp [Fn.andConst] at ha
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
