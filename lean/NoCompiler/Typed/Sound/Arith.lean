import NoCompiler.Typed.Sound.ArithExt

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

set_option hygiene false in
/-- The default rule: the register is a fresh word. -/
local macro "arith_any" : tactic => `(tactic| (
  simp only [Fn.arith] at ha
  exact f.arithExt_sound hprot hI (by simp [writesReg]) hrd ha hx))

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

/-! ### 32-bit operations -/

theorem IExpr.maxVar_le {e : IExpr} {n : Nat} (h : ∀ x ∈ e.vars, x ≤ n) : e.maxVar ≤ n := by
  unfold IExpr.maxVar
  unfold IExpr.vars at h
  generalize e.terms = ts at *
  induction ts with
  | nil => simp
  | cons t r ih =>
    simp only [List.map_cons, List.mem_cons, forall_eq_or_imp] at h
    simp only [List.foldr_cons]
    have := ih h.2
    have := h.1
    simp only [Var] at *
    omega

/-- Sums and differences of typed expressions stay below the type's variables. -/
theorem IExpr.maxVar_bin {a b : IExpr} {n : Nat} (ha : a.maxVar ≤ n) (hb : b.maxVar ≤ n) :
    (a.add b).maxVar ≤ n ∧ (a.sub b).maxVar ≤ n := by
  constructor <;> apply IExpr.maxVar_le <;> intro x hx <;>
    simp only [IExpr.vars_add, IExpr.vars_sub, List.mem_append] at hx <;>
    rcases hx with hx | hx
  all_goals first
    | exact Nat.le_trans (IExpr.le_maxVar hx) ha
    | exact Nat.le_trans (IExpr.le_maxVar hx) hb

theorem toInt_setWidth32_mod (z : Word) :
    ((z.setWidth 32).toInt - (z.toNat : Int)) % 2 ^ 32 = 0 := by
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_setWidth]
  split <;> omega

theorem addw_mod (x y : Word) :
    ((x.setWidth 32 + y.setWidth 32).toInt - ((x.toNat : Int) + y.toNat)) % 2 ^ 32 = 0 := by
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_setWidth]
  have := x.isLt; have := y.isLt
  split <;> omega

theorem subw_mod (x y : Word) :
    ((x.setWidth 32 - y.setWidth 32).toInt - ((x.toNat : Int) - y.toNat)) % 2 ^ 32 = 0 := by
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_setWidth]
  have := x.isLt; have := y.isLt
  split <;> omega

/-- The 32-bit rule: a word whose signed value is `e` modulo 2^32 and in the 32-bit range. -/
theorem Inv.word32 (hprot : ∀ x ∈ f.protectedVars, x < f.fresh) {S : STy} {s : State} {ι : Val}
    {F : TokFp} (hI : Inv f T P s0 ι0 S s ι F) {rd : Reg} (hrd : rd ≠ 2) {e : IExpr}
    (hem : e.maxVar ≤ S.maxVar) (v : Word) (hv : (v.toInt - e.eval ι) % 2 ^ 32 = 0)
    (hlo : -2 ^ 31 ≤ v.toInt) (hhi : v.toInt < 2 ^ 31) (pc : Word) :
    ∃ ι', (∀ y : Nat, y < f.fresh → ι' y = ι y) ∧
      Inv f T P s0 ι0 (Fn.word32 S rd (f.freshAt S) e) ((s.setReg rd v).setPc pc) ι' F := by
  obtain ⟨h1, h2, h3⟩ := setFrom_fresh hprot S ι [v.toInt]
  have hx := setFrom_at (ι := ι) (x := f.freshAt S) (vs := [v.toInt]) 0 (by simp)
  simp only [Nat.add_zero, List.getElem?_cons_zero, Option.getD_some] at hx
  have hev : e.eval (setFrom ι (f.freshAt S) [v.toInt]) = e.eval ι :=
    IExpr.eval_congr_max (fun y hy => h1 y (by omega))
  unfold Fn.word32
  refine ⟨_, h3, hI.write (e := some (.var (f.freshAt S))) hrd h1 h2 (fun e' he _ => ?_) ?_ pc⟩
  · simp only [Option.some.injEq] at he; subst he
    unfold HasInt; simp only [IExpr.eval_var, hx]
    have hc := BitVec.toInt_eq_toNat_cond v; have hl := v.isLt
    split at hc <;> omega
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;>
      simp only [Constr.holds, Constr.eval, Constr.lt, decide_eq_true_eq, IExpr.eval_var,
        IExpr.eval_lit, IExpr.eval_add, IExpr.eval_sub, hx, hev] <;> omega

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
        -- the value, and the quotient of the mask fact (any integer when there is none)
        let w : Int := ((s.reg rs &&& imm.signExtend 64).toNat : Int)
        let qv : Int := match S.reg rs with
          | some e => match (List.range 13).find? (fun k => imm.toInt == 2 ^ k - 1) with
            | some k => (e.eval ι - w) / 2 ^ k
            | none => 0
          | none => 0
        obtain ⟨h1, h2, h3⟩ := setFrom_fresh hprot S ι [w, qv]
        have hx := setFrom_at (ι := ι) (x := f.freshAt S) (vs := [w, qv]) 0 (by simp)
        have hx1 := setFrom_at (ι := ι) (x := f.freshAt S) (vs := [w, qv]) 1 (by simp)
        simp only [Nat.add_zero, List.getElem?_cons_zero, Option.getD_some,
          List.getElem?_cons_succ] at hx hx1
        have hse := hasInt_signExtend (by omega) ι imm
        have hlt := (imm.signExtend 64).isLt
        have hv := hse.toNat_eq (by simpa using hpos.1) (by
          simp only [IExpr.eval_lit]; have := BitVec.toInt_lt (x := imm); omega)
        simp only [IExpr.eval_lit] at hv
        have hand : (s.reg rs &&& imm.signExtend 64).toNat ≤ (imm.signExtend 64).toNat := by
          rw [BitVec.toNat_and]; exact Nat.and_le_right
        refine ⟨_, h3, hI.write (e := some (.var (f.freshAt S))) hrd h1 h2 (fun e' he _ => ?_) ?_ _, by simp⟩
        · simp only [Option.some.injEq] at he; subst he; exact hasInt_toNat _ _ _ hx
        · intro p hp
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with (rfl | rfl) | hp
          · simp only [Constr.holds, Constr.eval, decide_eq_true_eq, IExpr.eval_var, IExpr.eval_lit, hx]
            omega
          · simp only [Constr.holds, Constr.eval, decide_eq_true_eq, IExpr.eval_var, IExpr.eval_lit, hx]
            omega
          · -- the mask facts
            split at hp
            · rename_i e hr
              split at hp
              · rename_i k hk
                have hk' := List.find?_some hk
                have hkr := List.mem_range.1 (List.mem_of_find?_eq_some hk)
                simp only [beq_iff_eq] at hk'
                have hre := STy.reg_hasInt hI.regs hr
                have hev : e.eval (setFrom ι (f.freshAt S) [w, qv]) = e.eval ι :=
                  IExpr.eval_congr_max (fun y hy => h1 y (by
                    have := STy.reg_maxVar hr; omega))
                have hmask : (imm.signExtend 64).toNat = 2 ^ k - 1 := by
                  have h2k : 1 ≤ 2 ^ k := Nat.one_le_two_pow
                  have h1' : ((imm.signExtend 64).toNat : Int) + 1 = ((2 ^ k : Nat) : Int) := by
                    rw [hv, hk']; push_cast; omega
                  have : (imm.signExtend 64).toNat + 1 = 2 ^ k := by exact_mod_cast h1'
                  omega
                have hmod : (s.reg rs &&& imm.signExtend 64).toNat = (s.reg rs).toNat % 2 ^ k := by
                  rw [BitVec.toNat_and, hmask, Nat.and_two_pow_sub_one_eq_mod]
                -- e ≡ w (mod 2^64) and 2^k ∣ 2^64, so 2^k ∣ e − w
                unfold HasInt at hre
                have hd : ((2 ^ k : Nat) : Int) ∣ (2 ^ 64 : Int) := by
                  rw [← c64]; exact Int.natCast_dvd_natCast.2 (Nat.pow_dvd_pow 2 (by omega))
                have hW : ((s.reg rs).toNat : Int) % ((2 ^ k : Nat) : Int) =
                    e.eval ι % ((2 ^ k : Nat) : Int) := by
                  rw [← Int.emod_emod_of_dvd _ hd, ← Int.emod_emod_of_dvd (e.eval ι) hd, hre]
                have hwv : w = ((s.reg rs).toNat : Int) % ((2 ^ k : Nat) : Int) := by
                  show ((s.reg rs &&& imm.signExtend 64).toNat : Int) = _
                  rw [hmod, Int.natCast_emod]
                have hdvd : ((2 ^ k : Nat) : Int) ∣ e.eval ι - w := by
                  apply Int.dvd_of_emod_eq_zero
                  rw [Int.sub_emod, hwv, Int.emod_emod_of_dvd _ (Int.dvd_refl _), hW, Int.sub_self,
                    Int.zero_emod]
                have hq : qv = (e.eval ι - w) / 2 ^ k := by
                  show (match S.reg rs with
                    | some e => match (List.range 13).find? (fun k => imm.toInt == 2 ^ k - 1) with
                      | some k => (e.eval ι - w) / 2 ^ k
                      | none => 0
                    | none => 0) = _
                  rw [hr]; simp only [hk]
                rcases List.mem_append.1 hp with hp | hp
                rotate_left
                · -- the zero test of an xor result
                  split at hp
                  · rename_i y hy
                    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hp
                    obtain ⟨q, hq, hqd⟩ := List.mem_filterMap.1 (List.mem_of_mem_take hd)
                    have hqι : q.holds (setFrom ι (f.freshAt S) [w, qv]) :=
                      (Constr.holds_congr (fun z hz => (h1 z
                        (Nat.le_trans hz (STy.le_maxVar_fact hq))).symm)).1 (hI.facts q hq)
                    rw [xorBitOf_eq hqd] at hqι
                    have hre' : HasInt (setFrom ι (f.freshAt S) [w, qv]) (s.reg rs) (.var y) := by
                      rw [← IExpr.asVar_eq hy]; unfold HasInt; rw [hev]; exact hre
                    refine xorZeroFact_holds (by omega) hre' ?_ hqι
                    rw [hx]; show ((s.reg rs &&& imm.signExtend 64).toNat : Int) = _
                    rw [hmod]
                  · simp at hp
                simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
                rcases hp with rfl | rfl
                · simp only [Constr.holds, Constr.eval, decide_eq_true_eq, IExpr.eval_var, IExpr.eval_sub]
                  rw [hev, hx]
                  rw [hwv, Int.sub_emod, Int.emod_emod_of_dvd _ (Int.dvd_refl _), hW, Int.sub_self,
                    Int.zero_emod]
                · simp only [Constr.holds, Constr.eval, decide_eq_true_eq, IExpr.eval_var,
                    IExpr.eval_add, IExpr.eval_smul]
                  rw [hev, hx, hx1, hq]
                  have hd' : (2 : Int) ^ k ∣ e.eval ι - w := by exact_mod_cast hdvd
                  rw [Int.mul_ediv_cancel' hd']; omega
              · simp at hp
            · simp at hp
      · exact f.arithExt_sound hprot hI (by simp [writesReg]) hrd ha hx
    all_goals arith_any
  | addiw rd' rs imm =>
    simp only [writesReg, Option.some.injEq] at hw; subst hw
    simp only [Fn.arith] at ha
    simp only [exec, Option.some.injEq] at hx; subst hx
    cases hr : S.reg rs with
    | none => rw [hr] at ha; simp only [Option.some.injEq] at ha; subst ha
              obtain ⟨ι', h1, h2⟩ := hI.any hprot hrd _ _; exact ⟨ι', h1, h2, by simp⟩
    | some e =>
      rw [hr] at ha; simp only [Option.some.injEq] at ha; subst ha
      have k := hasInt_add (STy.reg_hasInt hI.regs hr) (hasInt_signExtend (by omega) ι imm)
      have hm := toInt_setWidth32_mod (s.reg rs + imm.signExtend 64)
      unfold HasInt at k
      have hlo := BitVec.le_toInt ((s.reg rs + imm.signExtend 64).setWidth 32)
      have hhi := BitVec.toInt_lt (x := (s.reg rs + imm.signExtend 64).setWidth 32)
      simp only [show (32 - 1 : Nat) = 31 from rfl] at hlo hhi
      obtain ⟨ι', h1, h2⟩ := hI.word32 hprot hrd (e := e.add (.lit imm.toInt))
        (by have := STy.reg_maxVar hr; simp only [IExpr.maxVar, IExpr.add, IExpr.lit, List.append_nil] at this ⊢; exact this)
        (sext32 (s.reg rs + imm.signExtend 64))
        (by unfold sext32; rw [BitVec.toInt_signExtend_of_le (by omega)]; omega)
        (by unfold sext32; rw [BitVec.toInt_signExtend_of_le (by omega)]; omega)
        (by unfold sext32; rw [BitVec.toInt_signExtend_of_le (by omega)]; omega) _
      exact ⟨ι', h1, h2, by simp⟩
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
    all_goals (simp only [Fn.arith] at ha
               exact f.arithExt_sound hprot hI (by simp [writesReg]) hrd ha (by simp [exec]))
  | rwop op rd' a b =>
    simp only [writesReg, Option.some.injEq] at hw; subst hw
    cases op
    case addw =>
      simp only [Fn.arith] at ha
      simp only [exec, Option.some.injEq] at hx; subst hx
      cases h1 : S.reg a with
      | none => rw [h1] at ha; simp only [Option.some.injEq] at ha; subst ha
                obtain ⟨ι', h1, h2⟩ := hI.any hprot hrd _ _; exact ⟨ι', h1, h2, by simp⟩
      | some e1 =>
      cases h2 : S.reg b with
      | none => rw [h1, h2] at ha; simp only [Option.some.injEq] at ha; subst ha
                obtain ⟨ι', h1, h2⟩ := hI.any hprot hrd _ _; exact ⟨ι', h1, h2, by simp⟩
      | some e2 =>
        rw [h1, h2] at ha; simp only [Option.some.injEq] at ha; subst ha
        have k1 := STy.reg_hasInt hI.regs h1
        have k2 := STy.reg_hasInt hI.regs h2
        unfold HasInt at k1 k2
        have m1 := STy.reg_maxVar h1
        have m2 := STy.reg_maxVar h2
        have hm := addw_mod (s.reg a) (s.reg b)
        have hlo := BitVec.le_toInt ((s.reg a).setWidth 32 + (s.reg b).setWidth 32)
        have hhi := BitVec.toInt_lt (x := (s.reg a).setWidth 32 + (s.reg b).setWidth 32)
        simp only [show (32 - 1 : Nat) = 31 from rfl] at hlo hhi
        have ht : (evalRW .addw (s.reg a) (s.reg b)).toInt =
            ((s.reg a).setWidth 32 + (s.reg b).setWidth 32).toInt := by
          simp only [evalRW, w32]; rw [BitVec.toInt_signExtend_of_le (by omega)]
        obtain ⟨ι', g1, g2⟩ := hI.word32 hprot hrd (e := e1.add e2)
          (IExpr.maxVar_bin m1 m2).1
          (evalRW .addw (s.reg a) (s.reg b)) (by rw [ht]; simp only [IExpr.eval_add]; omega)
          (by rw [ht]; omega) (by rw [ht]; omega) _
        exact ⟨ι', g1, g2, by simp⟩
    case subw =>
      simp only [Fn.arith] at ha
      simp only [exec, Option.some.injEq] at hx; subst hx
      cases h1 : S.reg a with
      | none => rw [h1] at ha; simp only [Option.some.injEq] at ha; subst ha
                obtain ⟨ι', h1, h2⟩ := hI.any hprot hrd _ _; exact ⟨ι', h1, h2, by simp⟩
      | some e1 =>
      cases h2 : S.reg b with
      | none => rw [h1, h2] at ha; simp only [Option.some.injEq] at ha; subst ha
                obtain ⟨ι', h1, h2⟩ := hI.any hprot hrd _ _; exact ⟨ι', h1, h2, by simp⟩
      | some e2 =>
        rw [h1, h2] at ha; simp only [Option.some.injEq] at ha; subst ha
        have k1 := STy.reg_hasInt hI.regs h1
        have k2 := STy.reg_hasInt hI.regs h2
        unfold HasInt at k1 k2
        have m1 := STy.reg_maxVar h1
        have m2 := STy.reg_maxVar h2
        have hm := subw_mod (s.reg a) (s.reg b)
        have hlo := BitVec.le_toInt ((s.reg a).setWidth 32 - (s.reg b).setWidth 32)
        have hhi := BitVec.toInt_lt (x := (s.reg a).setWidth 32 - (s.reg b).setWidth 32)
        simp only [show (32 - 1 : Nat) = 31 from rfl] at hlo hhi
        have ht : (evalRW .subw (s.reg a) (s.reg b)).toInt =
            ((s.reg a).setWidth 32 - (s.reg b).setWidth 32).toInt := by
          simp only [evalRW, w32]; rw [BitVec.toInt_signExtend_of_le (by omega)]
        obtain ⟨ι', g1, g2⟩ := hI.word32 hprot hrd (e := e1.sub e2)
          (IExpr.maxVar_bin m1 m2).2
          (evalRW .subw (s.reg a) (s.reg b)) (by rw [ht]; simp only [IExpr.eval_sub]; omega)
          (by rw [ht]; omega) (by rw [ht]; omega) _
        exact ⟨ι', g1, g2, by simp⟩
    all_goals arith_any
  | uop op rd' a =>
    simp only [writesReg, Option.some.injEq] at hw; subst hw; arith_any
  | _ => simp [writesReg] at hw

end NoCompiler.Typed
