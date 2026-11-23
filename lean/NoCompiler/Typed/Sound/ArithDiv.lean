import NoCompiler.Typed.Sound.ArithFacts

/-
Division and remainder, the xor zero test, and/or of 0/1 values (Fn.arith2Div).
-/
namespace NoCompiler.Typed

variable {f : Fn} {T : TokEnv} {P : Perm} {s0 : State} {ι0 : Val}

theorem Fn.arith2Div_sound (hprot : ∀ x ∈ f.protectedVars, x < f.fresh) {S S' : STy} {s s' : State}
    {ι : Val} {F : TokFp} (hI : Inv f T P s0 ι0 S s ι F) {i : Instr} {rd : Reg}
    (hw : writesReg i = some rd) (hrd : rd ≠ 2) (ha : f.arith2Div S i = some S')
    (hx : exec i s = some s') :
    ∃ ι', (∀ y : Nat, y < f.fresh → ι' y = ι y) ∧ Inv f T P s0 ι0 S' s' ι' F ∧ s'.pc = s.pc + 4 := by
  have hag := (setFrom_fresh hprot S ι)
  cases i with
  | rop op rd' a b =>
    simp only [writesReg, Option.some.injEq] at hw; subst hw
    simp only [exec, Option.some.injEq] at hx; subst hx
    cases op
    case divu | remu =>
      simp only [Fn.arith2Div] at ha
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
      simp only [Fn.arith2Div] at ha
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
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
          List.mem_filter, decide_eq_true_eq] at hp
        rcases hp with (rfl | rfl | rfl) | ⟨k, ⟨-, hk⟩, rfl⟩
        rotate_left 3
        · -- xor then mask: 2^k ∣ x ⇔ 2^k ∣ a − b
          have hiffk := xor_dvd_iff k1 k2 hk
          simp only [Fn.xorBitFact, Constr.holds, Constr.eval, Bool.or_eq_true, Bool.and_eq_true,
            Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not, IExpr.eval_var,
            IExpr.eval_sub, hv, ev1, ev2]
          have hc : (((2 ^ k : Nat) : Int)) = 2 ^ k := by norm_cast
          rw [hc]
          by_cases h : (e1.eval ι - e2.eval ι) % 2 ^ k = 0
          · left; exact ⟨hiffk.2 h, h⟩
          · right; exact ⟨fun h' => h (hiffk.1 h'), h⟩
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
      simp only [Fn.arith2Div] at ha
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
      simp only [Fn.arith2Div] at ha
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
    all_goals simp [Fn.arith2Div] at ha
  | _ => simp [Fn.arith2Div] at ha

end NoCompiler.Typed
