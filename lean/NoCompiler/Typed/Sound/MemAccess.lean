import NoCompiler.Typed.Sound.Branch
import NoCompiler.Typed.Sound.Addr

/-
Accesses (Lemmas 5 and 6, common part): an access the checker accepts lies in a held
capability, inside its footprint, aligned; the address, possibly through its unsigned
representative (I20).
-/
namespace NoCompiler.Typed

variable {f : Fn} {T : TokEnv} {P : Perm} {s0 : State} {ι0 : Val}

/-- What an accepted access check gives. -/
theorem inCap_sound {S : STy} {ι : Val} {F : TokFp} {m : Word → Byte} {a : IExpr} {w : Nat}
    {c : HCap} {needRw : Bool} (h : Fn.inCap S a w c needRw = true) (hh : ∀ p ∈ S.hyps, p.holds ι)
    (hv : c.cap.valid T ι F m) {A : Word} (hA : HasInt ι A a) (hw : 0 < w) :
    ∃ b, c.cap.kind = .bytes b ∧ (needRw = true → b.mode = .rw) ∧ c.cap.guard.eval ι = true ∧
      0 ≤ b.base.eval ι ∧ 0 ≤ b.len.eval ι ∧ b.base.eval ι + b.len.eval ι ≤ 2 ^ 64 ∧
      (∀ fd ∈ b.fields, Cap.Field.holds ι m b fd) ∧
      b.base.eval ι ≤ a.eval ι ∧ a.eval ι + w ≤ b.base.eval ι + b.len.eval ι ∧
      (A.toNat : Int) = a.eval ι ∧ a.eval ι % w = 0 := by
  unfold Fn.inCap at h
  split at h
  · rename_i b hk
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at h
    obtain ⟨⟨hrw, hg⟩, hin⟩ := h
    have hg := STy.ent_sound hg hh
    have hin := STy.ent_sound hin hh
    simp only [Constr.holds, Constr.eval, Bool.and_eq_true, decide_eq_true_eq, IExpr.eval_add,
      IExpr.eval_lit] at hin
    have hv := hv hg
    rw [hk] at hv
    obtain ⟨h0, h1, h2, hf, -⟩ := hv
    refine ⟨b, hk, fun hn => by rcases hrw with h | h <;> simp_all, hg, h0, h1, h2, hf, hin.1, hin.2.1,
      hA.toNat_eq (by omega) (by omega), hin.2.2⟩
  · cases h

/-- The bytes of an accepted access are in the capability's footprint. -/
theorem access_fp {ι : Val} {F : TokFp} {c : HCap} {b : BytesCap} (hk : c.cap.kind = .bytes b)
    (hg : c.cap.guard.eval ι = true) (h0 : 0 ≤ b.base.eval ι) (h1 : 0 ≤ b.len.eval ι)
    (h2 : b.base.eval ι + b.len.eval ι ≤ 2 ^ 64) {A : Word} {w : Nat}
    (hlo : b.base.eval ι ≤ A.toNat) (hhi : (A.toNat : Int) + w ≤ b.base.eval ι + b.len.eval ι) :
    ∀ i < w, c.cap.fp ι F (A + BitVec.ofNat 64 i) := by
  intro i hi
  unfold Cap.fp Cap.regions
  rw [if_pos hg, hk]
  refine ⟨_, List.mem_singleton_self _, ?_⟩
  have := toNat_add_ofNat (A := A) (i := i) (by omega)
  rw [region_mem_iff h0 h1 h2]; omega

theorem ldRange_sound (ι : Val) (op : LdOp) (m : Word → Byte) (A : Word) (x : Var)
    (hx : ι x = ldInt op (loadVal op m A)) : ∀ p ∈ Fn.ldRange x op, p.holds ι := by
  intro p hp
  cases op <;> simp only [Fn.ldRange, List.mem_cons, List.not_mem_nil, or_false] at hp <;>
    simp only [loadVal, ldInt, read8, read16, read32, read64] at hx
  all_goals rcases hp with rfl | rfl
  all_goals simp only [Constr.holds, Constr.eval, Constr.lt, decide_eq_true_eq, IExpr.eval_var,
    IExpr.eval_lit, IExpr.eval_add, hx]
  -- unsigned loads
  all_goals first
    | (have := readLE_lt m A 1; rw [BitVec.toNat_ofNat]; omega)
    | (have := readLE_lt m A 2; rw [BitVec.toNat_ofNat]; omega)
    | (have := readLE_lt m A 4; rw [BitVec.toNat_ofNat]; omega)
    | (have := (BitVec.ofNat 64 (readLE m A 8)).isLt; omega)
    | (rw [BitVec.toInt_signExtend_of_le (by omega)];
       first | (have := BitVec.le_toInt (BitVec.ofNat 8 (readLE m A 1)); simp at this; omega)
             | (have := BitVec.toInt_lt (x := BitVec.ofNat 8 (readLE m A 1)); simp at this; omega)
             | (have := BitVec.le_toInt (BitVec.ofNat 16 (readLE m A 2)); simp at this; omega)
             | (have := BitVec.toInt_lt (x := BitVec.ofNat 16 (readLE m A 2)); simp at this; omega)
             | (have := BitVec.le_toInt (BitVec.ofNat 32 (readLE m A 4)); simp at this; omega)
             | (have := BitVec.toInt_lt (x := BitVec.ofNat 32 (readLE m A 4)); simp at this; omega))

theorem constOff_sound {a b : IExpr} {k : Nat} (h : Fn.constOff a b = some k) (ι : Val) :
    a.eval ι = b.eval ι + k := by
  unfold Fn.constOff at h
  split at h
  · rename_i c hc
    split at h
    · cases h
      have := congrArg (Lin.eval ι) hc
      rw [IExpr.eval_toLin, IExpr.eval_sub] at this
      simp [Lin.eval, Lin.evalT] at this
      omega
    · cases h
  · cases h

theorem ea_hasInt {ι : Val} {S : STy} {s : State} {rs : Reg} {e : IExpr} (off : BitVec 12)
    (hr : ∀ p ∈ S.regs, HasInt ι (s.reg p.1) p.2) (he : S.reg rs = some e) :
    HasInt ι (ea s rs off) (e.add (.lit off.toInt)) :=
  hasInt_add (STy.reg_hasInt hr he) (hasInt_signExtend (by omega) ι off)

/-- The address of an accepted access, possibly through its unsigned representative. -/
theorem Fn.addr_sound (hprot : ∀ x ∈ f.protectedVars, x < f.fresh) {S S1 : STy} {s : State}
    {ι : Val} {F : TokFp} (hI : Inv f T P s0 ι0 S s ι F) {rs : Reg} {off : BitVec 12} {w : Nat}
    {needRw : Bool} {a : IExpr} {c : HCap} (h : f.addr S rs off w needRw = some (S1, a, c)) :
    ∃ ι1, (∀ y : Nat, y < f.fresh → ι1 y = ι y) ∧ Inv f T P s0 ι0 S1 s ι1 F ∧
      HasInt ι1 (ea s rs off) a ∧ c ∈ S1.caps ∧ Fn.inCap S1 a w c needRw = true ∧
      S1.caps = S.caps ∧ S1.regs = S.regs := by
  unfold Fn.addr at h
  cases he : S.reg rs with
  | none => simp [he] at h
  | some e =>
    simp only [he, Option.bind_eq_bind, Option.bind_some] at h
    have hA := ea_hasInt off hI.regs he
    cases hc : S.caps.find? (fun c => Fn.inCap S (e.add (.lit off.toInt)) w c needRw) with
    | some c' =>
      simp only [hc, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      have h2 := List.find?_some hc
      exact ⟨ι, fun _ _ => rfl, hI, hA, List.mem_of_find?_eq_some hc, h2, rfl, rfl⟩
    | none =>
      simp only [hc] at h
      have hm : (e.add (.lit off.toInt)).maxVar ≤ S.maxVar := by
        have := STy.reg_maxVar he
        simp only [IExpr.maxVar, IExpr.add, IExpr.lit, List.append_nil] at this ⊢; exact this
      obtain ⟨g1, g2, g3⟩ := setFrom_fresh hprot S ι [((ea s rs off).toNat : Int)]
      have hx := setFrom_at (ι := ι) (x := f.freshAt S) (vs := [((ea s rs off).toNat : Int)]) 0 (by simp)
      simp only [Nat.add_zero, List.getElem?_cons_zero, Option.getD_some] at hx
      have hu := urep_sound (x := f.freshAt S) hI.hyps hA (fun y hy => g1 y (by omega)) hx
      cases hc1 : (S.addFacts (Fn.urep S (f.freshAt S) (e.add (.lit off.toInt))).2).caps.find?
          (fun c => Fn.inCap (S.addFacts (Fn.urep S (f.freshAt S) (e.add (.lit off.toInt))).2)
            (Fn.urep S (f.freshAt S) (e.add (.lit off.toInt))).1 w c needRw) with
      | none => simp [hc1] at h
      | some c' =>
        simp only [hc1, Option.bind_some, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        have h2 := List.find?_some hc1
        refine ⟨_, g3, (hI.congr g1 g2).addFacts hu.2, ?_, List.mem_of_find?_eq_some hc1,
          h2, rfl, rfl⟩
        exact hasInt_toNat' hu.1

end NoCompiler.Typed
