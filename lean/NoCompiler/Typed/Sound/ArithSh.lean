import NoCompiler.Typed.Sound.ArithFacts

/-
The .uw forms, shifts, word forms and unary operations of ArithExt (Fn.arith2Sh).
-/
namespace NoCompiler.Typed

variable {f : Fn} {T : TokEnv} {P : Perm} {s0 : State} {ι0 : Val}

theorem Fn.arith2Sh_sound (hprot : ∀ x ∈ f.protectedVars, x < f.fresh) {S S' : STy} {s s' : State}
    {ι : Val} {F : TokFp} (hI : Inv f T P s0 ι0 S s ι F) {i : Instr} {rd : Reg}
    (hw : writesReg i = some rd) (hrd : rd ≠ 2) (ha : f.arith2Sh S i = some S')
    (hx : exec i s = some s') :
    ∃ ι', (∀ y : Nat, y < f.fresh → ι' y = ι y) ∧ Inv f T P s0 ι0 S' s' ι' F ∧ s'.pc = s.pc + 4 := by
  have hag := (setFrom_fresh hprot S ι)
  cases i with
  | rwop op rd' a b =>
    simp only [writesReg, Option.some.injEq] at hw; subst hw
    simp only [exec, Option.some.injEq] at hx; subst hx
    have zx : ∀ (n : Nat) (vs : List Int), vs = [(((s.reg a).toNat % 2 ^ 32 : Nat) : Int)] →
        HasInt (setFrom ι (f.freshAt S) vs) (zext32 (s.reg a)) (.var (f.freshAt S)) := by
      intro n vs h; subst h; exact hasInt_toNat _ _ _ (by simp [setFrom_x, zext32_toNat])
    cases op
    case mulw =>
      simp only [Fn.arith2Sh] at ha
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
      simp only [Fn.arith2Sh] at ha
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
    all_goals simp [Fn.arith2Sh] at ha
  | shift op rd' rs sh =>
    simp only [writesReg, Option.some.injEq] at hw; subst hw
    simp only [exec, Option.some.injEq] at hx; subst hx
    cases op
    case slliuw =>
      simp only [Fn.arith2Sh] at ha
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
      simp only [Fn.arith2Sh] at ha
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
    all_goals simp [Fn.arith2Sh] at ha
  | shiftw op rd' rs sh =>
    simp only [writesReg, Option.some.injEq] at hw; subst hw
    simp only [exec, Option.some.injEq] at hx; subst hx
    cases op
    case slliw =>
      simp only [Fn.arith2Sh] at ha
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
      simp only [Fn.arith2Sh] at ha
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
    all_goals (simp only [Fn.arith2Sh, reduceCtorEq] at ha)
  | uop op rd' rs =>
    simp only [writesReg, Option.some.injEq] at hw; subst hw
    simp only [exec, Option.some.injEq] at hx; subst hx
    cases op
    case clz | ctz | cpop | clzw | ctzw | cpopw =>
      simp only [Fn.arith2Sh, Option.some.injEq] at ha; subst ha
      have hb := bitcount_le (s.reg rs)
      refine hI.fresh4 hprot hrd [_] (.var (f.freshAt S)) _ _
        (hasInt_toNat _ _ _ setFrom_x) (boundFacts_holds setFrom_x ?_)
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hb
      omega
    case zexth =>
      simp only [Fn.arith2Sh] at ha
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
    all_goals simp [Fn.arith2Sh] at ha
  | _ => simp [Fn.arith2Sh] at ha

end NoCompiler.Typed
