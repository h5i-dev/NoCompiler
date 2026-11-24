import NoCompiler.Typed.Sound.ArithBase

/-
The facts the ArithExt rules add hold for the values computed (comparisons, min/max, low
bits, quotients, remainders, 0/1 tables, bounds, disjoint constants).
-/
namespace NoCompiler.Typed

variable {f : Fn} {T : TokEnv} {P : Perm} {s0 : State} {ι0 : Val}

theorem lessFact_holds {ι : Val} {x : Var} {a b : IExpr} {p : Prop} [Decidable p]
    (hx : ι x = if p then 1 else 0) (hp : p ↔ a.eval ι < b.eval ι) :
    (Fn.lessFact x a b).holds ι := by
  unfold Fn.lessFact
  simp only [Constr.holds, Constr.eval, Constr.lt, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, IExpr.eval_var, IExpr.eval_lit, IExpr.eval_add, hx]
  by_cases h : p
  · simp only [h, ite_true]; left; exact ⟨trivial, by have := hp.1 h; omega⟩
  · simp only [h, ite_false]; right; exact ⟨trivial, by have := mt hp.2 h; omega⟩

theorem minMaxFact_holds {ι : Val} {isMax : Bool} {x : Var} {a b : IExpr} {v : Int}
    (hx : ι x = v) (hor : v = a.eval ι ∨ v = b.eval ι)
    (hord : if isMax then a.eval ι ≤ v ∧ b.eval ι ≤ v else v ≤ a.eval ι ∧ v ≤ b.eval ι) :
    (Fn.minMaxFact isMax x a b).holds ι := by
  unfold Fn.minMaxFact
  cases isMax <;>
    simp only [Constr.holds, Constr.eval, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
      IExpr.eval_var, hx, if_true, if_false, Bool.false_eq_true] at hord ⊢ <;> omega

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
    simp [Constr.holds, Constr.eval, IExpr.eval_sub, IExpr.eval_lit, IExpr.eval_var, ha, hb, hx]

theorem boundFacts_holds {ι : Val} {x : Var} {b : Int} {n : Nat} (hx : ι x = n) (hb : (n : Int) ≤ b) :
    ∀ p ∈ Fn.boundFacts x b, p.holds ι := by
  intro p hp
  simp only [Fn.boundFacts, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;>
    simp only [Constr.holds, Constr.eval, decide_eq_true_eq, IExpr.eval_var, IExpr.eval_lit, hx] <;> omega

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

end NoCompiler.Typed
