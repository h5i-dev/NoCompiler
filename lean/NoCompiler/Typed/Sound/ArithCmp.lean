import NoCompiler.Typed.Sound.ArithFacts

/-
Comparisons and min/max of two registers (Fn.arith2Cmp).
-/
namespace NoCompiler.Typed

variable {f : Fn} {T : TokEnv} {P : Perm} {s0 : State} {ι0 : Val}

theorem Fn.arith2Cmp_sound (hprot : ∀ x ∈ f.protectedVars, x < f.fresh) {S S' : STy} {s s' : State}
    {ι : Val} {F : TokFp} (hI : Inv f T P s0 ι0 S s ι F) {i : Instr} {rd : Reg}
    (hw : writesReg i = some rd) (hrd : rd ≠ 2) (ha : f.arith2Cmp S i = some S')
    (hx : exec i s = some s') :
    ∃ ι', (∀ y : Nat, y < f.fresh → ι' y = ι y) ∧ Inv f T P s0 ι0 S' s' ι' F ∧ s'.pc = s.pc + 4 := by
  have hag := (setFrom_fresh hprot S ι)
  cases i with
  | rop op rd' a b =>
    simp only [writesReg, Option.some.injEq] at hw; subst hw
    simp only [exec, Option.some.injEq] at hx; subst hx
    cases op
    case sltu =>
      simp only [Fn.arith2Cmp] at ha
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
      simp only [Fn.arith2Cmp] at ha
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
      simp only [Fn.arith2Cmp] at ha
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
      simp only [Fn.arith2Cmp] at ha
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
      simp only [Fn.arith2Cmp] at ha
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
      simp only [Fn.arith2Cmp] at ha
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
    all_goals simp [Fn.arith2Cmp] at ha
  | _ => simp [Fn.arith2Cmp] at ha

end NoCompiler.Typed
