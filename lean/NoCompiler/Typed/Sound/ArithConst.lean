import NoCompiler.Typed.Sound.ArithFacts

/-
`and`/`or`/`xor` with a constant register (Fn.andConst).
-/
namespace NoCompiler.Typed

variable {f : Fn} {T : TokEnv} {P : Perm} {s0 : State} {ι0 : Val}

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
    have hw' := hw.of_eq (Fn.eval_setFrom_old (f := f) hem ι vs).symm
    have hxv : setFrom ι (f.freshAt S) vs (f.freshAt S) = ((w.toNat % 2 ^ k : Nat) : Int) := by
      simp [vs, setFrom_x]
    refine hI.fresh4 hprot hrd vs (.var (f.freshAt S)) _ _
      (hasInt_toNat _ _ _ (by simp [vs, setFrom_x, hv])) (fun p hp => ?_)
    rcases List.mem_append.1 hp with hp | hp
    · exact lowFacts_holds (by omega) hw' hxv p hp
    · split at hp
      · rename_i y hy
        obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hp
        obtain ⟨q, hq, hqd⟩ := List.mem_filterMap.1 (List.mem_of_mem_take hd)
        have hqe := xorBitOf_eq hqd
        have hqι : q.holds (setFrom ι (f.freshAt S) vs) :=
          (Constr.holds_congr (fun z hz => (setFrom_below (Nat.lt_of_le_of_lt
            (Nat.le_trans hz (STy.le_maxVar_fact hq)) (f.freshAt_gt S))).symm)).1 (hI.facts q hq)
        rw [hqe] at hqι
        exact xorZeroFact_holds (by omega) (by rw [← IExpr.asVar_eq hy]; exact hw') hxv hqι
      · simp at hp
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

end NoCompiler.Typed
