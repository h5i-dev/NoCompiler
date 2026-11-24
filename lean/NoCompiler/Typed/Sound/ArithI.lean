import NoCompiler.Typed.Sound.ArithFacts

/-
The immediate forms of ArithExt (Fn.arith2I): xori −1, ori/xori with a disjoint constant,
andi masks and single bits, sltiu, slti.
-/
namespace NoCompiler.Typed

variable {f : Fn} {T : TokEnv} {P : Perm} {s0 : State} {ι0 : Val}

theorem Fn.arith2I_sound (hprot : ∀ x ∈ f.protectedVars, x < f.fresh) {S S' : STy} {s s' : State}
    {ι : Val} {F : TokFp} (hI : Inv f T P s0 ι0 S s ι F) {i : Instr} {rd : Reg}
    (hw : writesReg i = some rd) (hrd : rd ≠ 2) (ha : f.arith2I S i = some S')
    (hx : exec i s = some s') :
    ∃ ι', (∀ y : Nat, y < f.fresh → ι' y = ι y) ∧ Inv f T P s0 ι0 S' s' ι' F ∧ s'.pc = s.pc + 4 := by
  have hag := (setFrom_fresh hprot S ι)
  cases i with
  | iop op rd' rs imm =>
    simp only [writesReg, Option.some.injEq] at hw; subst hw
    simp only [exec, Option.some.injEq] at hx; subst hx
    cases op
    case xori =>
      simp only [Fn.arith2I] at ha
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
      simp only [Fn.arith2I] at ha
      cases hr : S.reg rs with
      | none => simp [hr] at ha
      | some e =>
        simp only [hr, Option.bind_some] at ha
        exact Fn.disjConst_sound hI hrd (STy.reg_hasInt hI.regs hr) rfl ha (Or.inl rfl)
    case andi =>
      simp only [Fn.arith2I] at ha
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
      simp only [Fn.arith2I] at ha
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
      simp only [Fn.arith2I] at ha
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
    all_goals simp [Fn.arith2I] at ha
  | _ => simp [Fn.arith2I] at ha

end NoCompiler.Typed
