import NoCompiler.Typed.Sound.Step

/-
Lemma 2 (arithmetic): every register-writing instruction the checker types.
-/
namespace NoCompiler.Typed

variable {f : Fn} {T : TokEnv} {P : Perm} {s0 : State} {ι0 : Val}

theorem lui_toInt (imm : BitVec 20) : (imm.setWidth 32 <<< 12).toInt = imm.toInt * 4096 := by
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toInt_eq_toNat_cond, BitVec.toNat_shiftLeft,
    BitVec.toNat_setWidth]
  have := imm.isLt
  rw [Nat.mod_eq_of_lt (by omega : imm.toNat < 2 ^ 32), Nat.shiftLeft_eq]
  split <;> split <;> omega

theorem hasInt_lui (ι : Val) (imm : BitVec 20) :
    HasInt ι ((imm.setWidth 32 <<< 12).signExtend 64) (.lit (imm.toInt * 4096)) := by
  have := hasInt_signExtend (by omega) ι (imm.setWidth 32 <<< 12)
  rwa [lui_toInt] at this

/-- The instructions whose only effect is a register write, and the register. -/
def writesReg : Instr → Option Reg
  | .lui rd _ | .auipc rd _ | .iop _ rd _ _ | .addiw rd _ _ | .shift _ rd _ _
  | .shiftw _ rd _ _ | .rop _ rd _ _ | .rwop _ rd _ _ | .uop _ rd _ => some rd
  | _ => none

set_option hygiene false in
/-- The default rule: the register is a fresh word. -/
local macro "arith_any" : tactic => `(tactic| (
  simp only [Fn.arith, Option.some.injEq] at ha; subst ha
  simp only [exec, Option.some.injEq] at hx; subst hx
  obtain ⟨ι', h1, h2⟩ := hI.any hprot hrd _ _
  exact ⟨ι', h1, h2, by simp⟩))

theorem STy.reg_maxVar {S : STy} {r : Reg} {e : IExpr} (h : S.reg r = some e) :
    e.maxVar ≤ S.maxVar := by
  unfold STy.reg at h
  split at h
  · cases h; simp [IExpr.maxVar, IExpr.lit]
  · exact STy.le_maxVar_reg (p := (r, e)) (lookup_mem h)

/-- Two register operands with types, or the default rule. -/
theorem Inv.bin (hprot : ∀ x ∈ f.protectedVars, x < f.fresh) {S S' : STy} {s : State} {ι : Val}
    {F : TokFp} (hI : Inv f T P s0 ι0 S s ι F) {rd a b : Reg} (hrd : rd ≠ 2) (v : Word) (pc : Word)
    (G : IExpr → IExpr → IExpr)
    (hG : ∀ e1 e2, S.reg a = some e1 → S.reg b = some e2 → HasInt ι v (G e1 e2))
    (ha : (match S.reg a, S.reg b with
        | some e1, some e2 => S.setReg rd (some (G e1 e2))
        | _, _ => Fn.anyWord S rd (f.freshAt S)) = S') :
    ∃ ι', (∀ y : Nat, y < f.fresh → ι' y = ι y) ∧ Inv f T P s0 ι0 S' ((s.setReg rd v).setPc pc) ι' F := by
  subst ha
  cases h1 : S.reg a with
  | none => exact hI.any hprot hrd v pc
  | some e1 =>
    cases h2 : S.reg b with
    | none => exact hI.any hprot hrd v pc
    | some e2 => exact ⟨ι, fun _ _ => rfl, hI.exact hrd (hG e1 e2 h1 h2) pc⟩

theorem Fn.arith_sound (hprot : ∀ x ∈ f.protectedVars, x < f.fresh) {S S' : STy} {s s' : State}
    {ι : Val} {F : TokFp} (hI : Inv f T P s0 ι0 S s ι F) {i : Instr} {rd : Reg}
    (hw : writesReg i = some rd) (hrd : rd ≠ 2) (ha : f.arith S i = some S')
    (hx : exec i s = some s') :
    ∃ ι', (∀ y : Nat, y < f.fresh → ι' y = ι y) ∧ Inv f T P s0 ι0 S' s' ι' F ∧ s'.pc = s.pc + 4 := by
  cases i with
  | lui rd' imm =>
    simp only [writesReg, Option.some.injEq] at hw; subst hw
    simp only [Fn.arith, Option.some.injEq] at ha; subst ha
    simp only [exec, Option.some.injEq] at hx; subst hx
    exact ⟨ι, fun _ _ => rfl, hI.exact hrd (hasInt_lui ι imm) _, by simp⟩
  | auipc rd' imm =>
    simp only [writesReg, Option.some.injEq] at hw; subst hw; arith_any
  | iop op rd' rs imm =>
    simp only [writesReg, Option.some.injEq] at hw; subst hw
    cases op
    case addi =>
      simp only [Fn.arith] at ha
      cases hr : S.reg rs with
      | none => rw [hr] at ha; simp only [Option.some.injEq] at ha; subst ha
                simp only [exec, Option.some.injEq] at hx; subst hx
                obtain ⟨ι', h1, h2⟩ := hI.any hprot hrd _ _
                exact ⟨ι', h1, h2, by simp⟩
      | some e =>
        rw [hr] at ha; simp only [Option.some.injEq] at ha; subst ha
        simp only [exec, Option.some.injEq] at hx; subst hx
        refine ⟨ι, fun _ _ => rfl, hI.exact hrd ?_ _, by simp⟩
        simp only [evalI]
        exact hasInt_add (STy.reg_hasInt hI.regs hr) (hasInt_signExtend (by omega) ι imm)
    case andi =>
      simp only [Fn.arith] at ha
      split at ha
      · rename_i hpos
        simp only [Option.some.injEq] at ha; subst ha
        simp only [exec, Option.some.injEq] at hx; subst hx
        simp only [evalI]
        obtain ⟨h1, h2, h3⟩ := setFrom_fresh hprot S ι [((s.reg rs &&& imm.signExtend 64).toNat : Int)]
        have hx := setFrom_at (ι := ι) (x := f.freshAt S)
          (vs := [((s.reg rs &&& imm.signExtend 64).toNat : Int)]) 0 (by simp)
        simp only [Nat.add_zero, List.getElem?_cons_zero, Option.getD_some] at hx
        refine ⟨_, h3, hI.write (e := some (.var (f.freshAt S)))
          (ps := [.le (.lit 0) (.var (f.freshAt S)), .le (.var (f.freshAt S)) (.lit imm.toInt)])
          hrd h1 h2 (fun e' he _ => ?_) ?_ _, by simp⟩
        · simp only [Option.some.injEq] at he; subst he; exact hasInt_toNat _ _ _ hx
        · have hse := hasInt_signExtend (by omega) ι imm
          have hlt := (imm.signExtend 64).isLt
          have hv := hse.toNat_eq (by simpa using hpos) (by
            simp only [IExpr.eval_lit]; have := BitVec.toInt_lt (x := imm); omega)
          simp only [IExpr.eval_lit] at hv
          have hand : (s.reg rs &&& imm.signExtend 64).toNat ≤ (imm.signExtend 64).toNat := by
            rw [BitVec.toNat_and]; exact Nat.and_le_right
          intro p hp
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl <;>
            simp only [Constr.holds, Constr.eval, decide_eq_true_eq, IExpr.eval_var, IExpr.eval_lit, hx] <;>
            omega
      · simp only [Option.some.injEq] at ha; subst ha
        simp only [exec, Option.some.injEq] at hx; subst hx
        obtain ⟨ι', h1, h2⟩ := hI.any hprot hrd _ _
        exact ⟨ι', h1, h2, by simp⟩
    all_goals arith_any
  | addiw rd' rs imm =>
    simp only [writesReg, Option.some.injEq] at hw; subst hw; arith_any
  | shift op rd' rs sh =>
    simp only [writesReg, Option.some.injEq] at hw; subst hw
    cases op
    case slli =>
      simp only [Fn.arith] at ha
      simp only [exec, Option.some.injEq] at hx; subst hx
      cases hr : S.reg rs with
      | none => rw [hr] at ha; simp only [Option.some.injEq] at ha; subst ha
                obtain ⟨ι', h1, h2⟩ := hI.any hprot hrd _ _
                exact ⟨ι', h1, h2, by simp⟩
      | some e =>
        rw [hr] at ha; simp only [Option.some.injEq] at ha; subst ha
        have := hasInt_shl (STy.reg_hasInt hI.regs hr) sh.toNat
        exact ⟨ι, fun _ _ => rfl, hI.exact hrd this _, by simp⟩
    case srli =>
      simp only [Fn.arith] at ha
      simp only [exec, Option.some.injEq] at hx; subst hx
      simp only [evalSh]
      cases hr : S.reg rs with
      | none => rw [hr] at ha; simp only [Option.some.injEq] at ha; subst ha
                obtain ⟨ι', h1, h2⟩ := hI.any hprot hrd _ _
                exact ⟨ι', h1, h2, by simp⟩
      | some e =>
        rw [hr] at ha; simp only [Option.some.injEq] at ha; subst ha
        have hre := STy.reg_hasInt hI.regs hr
        have hrm := STy.reg_maxVar hr
        generalize hxv : f.freshAt S = x at *
        have hxS : S.maxVar < x := hxv ▸ f.freshAt_gt S
        have hdmN := (Nat.div_add_mod (s.reg rs).toNat (2 ^ sh.toNat)).symm
        have hmodN := Nat.mod_lt (s.reg rs).toNat (Nat.two_pow_pos sh.toNat)
        have hv : (s.reg rs >>> sh.toNat).toNat = (s.reg rs).toNat / 2 ^ sh.toNat := by
          rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
        generalize (s.reg rs).toNat / 2 ^ sh.toNat = q at hdmN hv
        generalize (s.reg rs).toNat % 2 ^ sh.toNat = r at hdmN hmodN
        have hdm : ((s.reg rs).toNat : Int) = (2 : Int) ^ sh.toNat * (q : Int) + (r : Int) := by
          exact_mod_cast hdmN
        have hmod : (r : Int) < (2 : Int) ^ sh.toNat := by exact_mod_cast hmodN
        let vs : List Int := [(q : Int), (r : Int), ((s.reg rs).toNat : Int)]
        obtain ⟨h1, h2, h3⟩ := setFrom_fresh hprot S ι vs
        rw [hxv] at h1 h2 h3
        have e0 : setFrom ι x vs x = (q : Int) := by
          have := setFrom_at (ι := ι) (x := x) (vs := vs) 0 (by simp [vs]); simpa [vs] using this
        have e1 : setFrom ι x vs (x + 1) = (r : Int) := by
          have := setFrom_at (ι := ι) (x := x) (vs := vs) 1 (by simp [vs]); simpa [vs] using this
        have e2 : setFrom ι x vs (x + 2) = ((s.reg rs).toNat : Int) := by
          have := setFrom_at (ι := ι) (x := x) (vs := vs) 2 (by simp [vs]); simpa [vs] using this
        have hev : e.eval (setFrom ι x vs) = e.eval ι :=
          IExpr.eval_congr_max (fun y hy => h1 y (by omega))
        have hw := (s.reg rs).isLt
        refine ⟨setFrom ι x vs, h3, ?_, by simp⟩
        unfold Fn.urep
        split
        · rename_i hin
          have hin := hI.ent hin
          simp only [Constr.holds, Constr.eval, Bool.and_eq_true, decide_eq_true_eq, Constr.lt,
            IExpr.eval_lit, IExpr.eval_add] at hin
          have ht := hre.toNat_eq hin.1 (by omega)
          refine hI.write hrd h1 h2 (fun e' he _ => ?_) ?_ _
          · simp only [Option.some.injEq] at he; subst he
            refine hasInt_toNat _ _ _ ?_; rw [e0, hv]
          · intro p hp
            simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hp
            rcases hp with rfl | rfl | rfl | rfl <;>
              simp only [Constr.holds, Constr.eval, decide_eq_true_eq, Constr.lt, IExpr.eval_var,
                IExpr.eval_lit, IExpr.eval_add, IExpr.eval_smul, e0, e1, hev] <;> omega
        · refine hI.write hrd h1 h2 (fun e' he _ => ?_) ?_ _
          · simp only [Option.some.injEq] at he; subst he
            refine hasInt_toNat _ _ _ ?_; rw [e0, hv]
          · intro p hp
            simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
              or_false] at hp
            unfold HasInt at hre
            rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
              simp only [Constr.holds, Constr.eval, decide_eq_true_eq, Constr.lt, Constr.eqMod,
                IExpr.eval_var, IExpr.eval_lit, IExpr.eval_add, IExpr.eval_smul, IExpr.eval_sub,
                e0, e1, e2, hev] <;> omega
    all_goals arith_any
  | shiftw op rd' rs sh =>
    simp only [writesReg, Option.some.injEq] at hw; subst hw; arith_any
  | rop op rd' a b =>
    simp only [writesReg, Option.some.injEq] at hw; subst hw
    simp only [exec, Option.some.injEq] at hx; subst hx
    cases op
    case add =>
      simp only [Fn.arith, Option.some.injEq] at ha
      obtain ⟨ι', h1, h2⟩ := hI.bin hprot hrd (evalR .add (s.reg a) (s.reg b)) (s.pc + 4)
        (fun e1 e2 => e1.add e2) (fun e1 e2 h1 h2 => by
          simp only [evalR]; exact hasInt_add (STy.reg_hasInt hI.regs h1) (STy.reg_hasInt hI.regs h2)) ha
      exact ⟨ι', h1, h2, by simp⟩
    case sub =>
      simp only [Fn.arith, Option.some.injEq] at ha
      obtain ⟨ι', h1, h2⟩ := hI.bin hprot hrd (evalR .sub (s.reg a) (s.reg b)) (s.pc + 4)
        (fun e1 e2 => e1.sub e2) (fun e1 e2 h1 h2 => by
          simp only [evalR]; exact hasInt_sub (STy.reg_hasInt hI.regs h1) (STy.reg_hasInt hI.regs h2)) ha
      exact ⟨ι', h1, h2, by simp⟩
    case sh1add =>
      simp only [Fn.arith, Option.some.injEq] at ha
      obtain ⟨ι', h1, h2⟩ := hI.bin hprot hrd (evalR .sh1add (s.reg a) (s.reg b)) (s.pc + 4)
        (fun e1 e2 => (e1.smul (2 ^ 1)).add e2) (fun e1 e2 h1 h2 => by
          simp only [evalR]
          exact hasInt_add (hasInt_shl (STy.reg_hasInt hI.regs h1) 1) (STy.reg_hasInt hI.regs h2)) ha
      exact ⟨ι', h1, h2, by simp⟩
    case sh2add =>
      simp only [Fn.arith, Option.some.injEq] at ha
      obtain ⟨ι', h1, h2⟩ := hI.bin hprot hrd (evalR .sh2add (s.reg a) (s.reg b)) (s.pc + 4)
        (fun e1 e2 => (e1.smul (2 ^ 2)).add e2) (fun e1 e2 h1 h2 => by
          simp only [evalR]
          exact hasInt_add (hasInt_shl (STy.reg_hasInt hI.regs h1) 2) (STy.reg_hasInt hI.regs h2)) ha
      exact ⟨ι', h1, h2, by simp⟩
    case sh3add =>
      simp only [Fn.arith, Option.some.injEq] at ha
      obtain ⟨ι', h1, h2⟩ := hI.bin hprot hrd (evalR .sh3add (s.reg a) (s.reg b)) (s.pc + 4)
        (fun e1 e2 => (e1.smul (2 ^ 3)).add e2) (fun e1 e2 h1 h2 => by
          simp only [evalR]
          exact hasInt_add (hasInt_shl (STy.reg_hasInt hI.regs h1) 3) (STy.reg_hasInt hI.regs h2)) ha
      exact ⟨ι', h1, h2, by simp⟩
    case mul =>
      simp only [Fn.arith] at ha
      simp only [evalR]
      cases h1 : S.reg a with
      | none => simp only [h1, Option.some.injEq] at ha; subst ha
                obtain ⟨ι', h1, h2⟩ := hI.any hprot hrd _ _; exact ⟨ι', h1, h2, by simp⟩
      | some e1 =>
        cases h2 : S.reg b with
        | none =>
          simp only [h1, h2, Option.some.injEq] at ha; subst ha
          obtain ⟨ι', h1, h2⟩ := hI.any hprot hrd _ _; exact ⟨ι', h1, h2, by simp⟩
        | some e2 =>
          have k1 := STy.reg_hasInt hI.regs h1
          have k2 := STy.reg_hasInt hI.regs h2
          obtain ⟨c2, ts2⟩ := e2
          cases ts2 with
          | nil =>
            simp only [h1, h2, Option.some.injEq] at ha; subst ha
            exact ⟨ι, fun _ _ => rfl, hI.exact hrd (hasInt_mul k1 k2) _, by simp⟩
          | cons t2 r2 =>
            obtain ⟨c1, ts1⟩ := e1
            cases ts1 with
            | nil =>
              simp only [h1, h2, Option.some.injEq] at ha; subst ha
              exact ⟨ι, fun _ _ => rfl, hI.exact hrd (hasInt_mul' k1 k2) _, by simp⟩
            | cons t1 r1 =>
              simp only [h1, h2, Option.some.injEq] at ha; subst ha
              obtain ⟨ι', h1, h2⟩ := hI.any hprot hrd _ _; exact ⟨ι', h1, h2, by simp⟩
    all_goals (simp only [Fn.arith, Option.some.injEq] at ha; subst ha
               obtain ⟨ι', h1, h2⟩ := hI.any hprot hrd _ _; exact ⟨ι', h1, h2, by simp⟩)
  | rwop op rd' a b =>
    simp only [writesReg, Option.some.injEq] at hw; subst hw; arith_any
  | uop op rd' a =>
    simp only [writesReg, Option.some.injEq] at hw; subst hw; arith_any
  | _ => simp [writesReg] at hw

end NoCompiler.Typed
