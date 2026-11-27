import NoCompiler.Typed.Sound.Runner
import NoCompiler.Typed.Sound.CallPre
import NoCompiler.Typed.Sound.CallPost

/-
Lemma 8: a call as one step (`VerifiedImg.call`), by `jal ra` and by `jalr ra` through a known constant (I21).
-/
namespace NoCompiler.Typed

variable {f : Fn} {T : TokEnv} {P : Perm} {s0 : State} {ι0 : Val}

theorem Fn.pcOf_succ (f : Fn) (k : Nat) : f.pcOf k + 4 = f.pcOf (k + 1) := by
  unfold Fn.pcOf; apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (4 : Word).toNat = 4 from rfl]; omega

theorem Fn.pcOf_target (f : Fn) {n : Nat} (hn : n ≤ 64) {k k' : Nat} {off : BitVec n}
    (h : Fn.target k off.toInt = some k') : f.pcOf k + off.signExtend 64 = f.pcOf k' := by
  unfold Fn.target at h
  split at h
  · rename_i hc
    simp only [Option.some.injEq] at h; subst h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    unfold Fn.pcOf; apply BitVec.eq_of_toNat_eq
    have hs := hasInt_signExtend hn (fun _ => 0) off
    unfold HasInt at hs; simp only [IExpr.eval_lit] at hs
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    have := (off.signExtend 64).isLt
    omega
  · cases h

theorem Fn.pcOf_aligned (hst : f.StructSpec) (k : Nat) : aligned (f.pcOf k) 4 := by
  unfold aligned Fn.pcOf
  have := hst.entryAligned
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem Fn.edge_lt {k : Option Nat} {S : STy} {k' : Nat} (h : f.edge k S k' = true) : k' < f.size := by
  unfold Fn.edge at h
  split at h
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1
  · unfold Fn.edgeOk at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1.1

/-- Lemma 8: a call of the callee at `t` (by `jal ra` or `jalr ra`), its whole run as one
    step (`VerifiedImg.call`), and the continuation after it returns. -/
theorem Fn.callAt_step (hst : f.StructSpec) {c : Code} {D : Dom} {Q : State → Prop} (rn : Runner c P D Q)
    {S : STy} {s : State} {ι : Val} {Ft : TokFp} {k : Nat} {i : Instr} {t : Word}
    (hI : Inv f T P s0 ι0 S s ι Ft) (hd : D.mem s.pc) (hpc : s.pc = f.pcOf k)
    (hi : c.instr s.pc = some i) (hiok : InstrOk P i s)
    (hxi : aligned t 4 → exec i s = some ((s.setReg 1 (s.pc + 4)).setPc t))
    (hk : f.callAt k S t = true)
    (hcall : ∀ p ∈ f.callees, aligned p.1 4 ∧ ∃ Dg, rn.callee Dg p.1 (p.2.spec T) ∧ Dg.sub D ∧
      ∀ j < f.size, ¬ Dg.mem (f.pcOf j))
    {a : Val × TokFp} (hP : P = (f.sig.spec T).perm a s0) (hι0p : ∀ x ∈ f.sig.params, ι0 x = a.1 x)
    (hUF : f.UnitFrame T a s0 Ft)
    (hexit : ∀ s', s'.exit ≠ none → rn.later s')
    (cont : ∀ (F1 : TokFp) S1 s' ι1, s'.pc = f.pcOf (k + 1) → Inv f T P s0 ι0 S1 s' ι1 F1 →
      f.UnitFrame T a s0 F1 → (∀ y : Nat, y < f.fresh → ι1 y = ι y) → f.edge (some k) S1 (k + 1) = true →
      rn.later s') :
    rn.R s := by
  unfold Fn.callAt at hk
  cases hg : f.callees.lookup t with
  | none => rw [hg] at hk; cases hk
  | some g =>
  rw [hg] at hk
  simp only at hk
  cases hθ : Fn.callInst S g with
  | none => rw [hθ] at hk; cases hk
  | some θ =>
  rw [hθ] at hk
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hk
  obtain ⟨⟨⟨hin, hpre⟩, hstk⟩, hk⟩ := hk
  cases hls : Fn.lends S g θ with
  | none => rw [hls] at hk; cases hk
  | some ls =>
  rw [hls] at hk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
  obtain ⟨⟨⟨⟨hap, htx⟩, huq⟩, hids⟩, hedge⟩ := hk
  have hgm := lookup_mem hg
  obtain ⟨hal, Dg, hmeets, hDg, hret⟩ := hcall _ hgm
  have hok := Fn.calleeOk_spec (hst.callees _ hgm)
  have hk1 := Fn.edge_lt hedge
  have hregs1 : ∀ r : Reg, r ≠ 1 → ((s.setReg 1 (s.pc + 4)).setPc t).reg r = s.reg r := by
    intro r hr; simp [State.reg_setReg_other _ _ _ _ hr]
  have hmem1 : ((s.setReg 1 (s.pc + 4)).setPc t).mem = s.mem := by simp
  obtain ⟨hpre', hle⟩ := f.callee_pre hst hI hok
    (fun p hp => by have := hin p hp; revert this; cases S.reg p.1 <;> simp) hpre hstk hls hap _
    hregs1 hmem1
  have hspn := hI.sp_toNat hst
  have hra : ((s.setReg 1 (s.pc + 4)).setPc t).reg 1 = f.pcOf (k + 1) := by
    simp only [State.setPc_reg]
    rw [State.reg_setReg_same _ _ _ (by decide), hpc, f.pcOf_succ]
  refine rn.call hd hI.live hi hiok (hxi hal) hmeets (IExpr.upd ι θ, Ft)
    ⟨by simp, by simp [hI.live], ?_, ?_, ?_⟩ hpre' hDg hle ?_
  · rw [hra]; exact hret _ hk1
  · rw [hra]; exact f.pcOf_aligned hst _
  · unfold aligned
    rw [hregs1 2 (by decide), hspn.1]
    have := hI.spAl; have := hspn.2.2; have := hspn.2.1; have := hI.stackLe
    omega
  · intro s2 hdone hfr
    rcases hdone with ⟨hlive, hpc2, hpres, hpost⟩ | ⟨hex, -⟩
    · obtain ⟨ι', F1, g1, hI', hUF1⟩ := f.afterCall_inv hst hI hok hθ hstk hls htx huq hP hι0p hUF hids hregs1 hmem1 hpres
        hlive hpost hfr
      refine cont F1 _ _ ι' ?_ hI' hUF1 g1 hedge
      rw [hpc2]; exact hra
    · exact hexit s2 hex

theorem Fn.call_step (hst : f.StructSpec) {c : Code} {D : Dom} {Q : State → Prop} (rn : Runner c P D Q)
    {S : STy} {s : State} {ι : Val} {Ft : TokFp} {k : Nat} {off : BitVec 21}
    (hI : Inv f T P s0 ι0 S s ι Ft) (hd : D.mem s.pc) (hpc : s.pc = f.pcOf k)
    (hi : c.instr s.pc = some (.jal 1 off)) (hk : f.callOk k S off = true)
    (hcall : ∀ p ∈ f.callees, aligned p.1 4 ∧ ∃ Dg, rn.callee Dg p.1 (p.2.spec T) ∧ Dg.sub D ∧
      ∀ j < f.size, ¬ Dg.mem (f.pcOf j))
    {a : Val × TokFp} (hP : P = (f.sig.spec T).perm a s0) (hι0p : ∀ x ∈ f.sig.params, ι0 x = a.1 x)
    (hUF : f.UnitFrame T a s0 Ft)
    (hexit : ∀ s', s'.exit ≠ none → rn.later s')
    (cont : ∀ (F1 : TokFp) S1 s' ι1, s'.pc = f.pcOf (k + 1) → Inv f T P s0 ι0 S1 s' ι1 F1 →
      f.UnitFrame T a s0 F1 → (∀ y : Nat, y < f.fresh → ι1 y = ι y) → f.edge (some k) S1 (k + 1) = true →
      rn.later s') :
    rn.R s :=
  f.callAt_step hst rn hI hd hpc hi trivial
    (fun hal => by simp only [exec, jumpTo, hpc, hal, if_true]) hk hcall hP hι0p hUF hexit cont

theorem IExpr.eval_of_terms_nil {e : IExpr} (h : e.terms.isEmpty = true) (ι : Val) :
    e.eval ι = e.const := by
  obtain ⟨c, ts⟩ := e
  simp only [List.isEmpty_iff] at h
  subst h; simp [IExpr.eval]

/-- A word whose type is a constant is that constant. -/
theorem ofInt_const_eq {ι : Val} {w : Word} {e : IExpr} (h : HasInt ι w e)
    (hnil : e.terms.isEmpty = true) : BitVec.ofInt 64 e.const = w := by
  unfold HasInt at h
  rw [IExpr.eval_of_terms_nil hnil] at h
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt]
  have := w.isLt
  have e1 : (w.toNat : Int) % 2 ^ 64 = w.toNat := Int.emod_eq_of_lt (by omega) (by omega)
  have e2 : e.const % ((2 ^ 64 : Nat) : Int) = e.const % 2 ^ 64 := by norm_cast
  rw [e2, ← h, e1]; simp

/-- A word satisfying the case disjunction is one of the enumerated words. -/
theorem regCallCases_mem {ι : Val} {w : Word} {e : IExpr} {xs : List Word}
    (ht : HasInt ι w e) (h : (Fn.regCallCases e xs).holds ι) : w ∈ xs := by
  induction xs with
  | nil => simp [Fn.regCallCases, Constr.holds, Constr.eval, IExpr.eval_lit] at h
  | cons base rest ih =>
    simp only [Fn.regCallCases, List.foldr_cons, Constr.holds, Constr.eval,
      Bool.or_eq_true] at h
    rcases h with he | he
    · have hm : (e.eval ι - (IExpr.lit base.toNat).eval ι) % 2 ^ 64 = 0 := by
        simp only [Constr.eqMod, Constr.eval, decide_eq_true_eq, IExpr.eval_sub] at he
        exact_mod_cast he
      have hx := ofInt_const_eq (ht.congr hm) (by rfl : (IExpr.lit base.toNat).terms.isEmpty = true)
      have hbase : BitVec.ofInt 64 (base.toNat : Int) = base := by
        apply BitVec.eq_of_toNat_eq
        have hrange : (base.toNat : Int) < 2 ^ 64 := by exact_mod_cast base.isLt
        have ht := toNat_ofInt_of (a := (base.toNat : Int)) (by omega) hrange
        exact_mod_cast ht
      rw [IExpr.lit] at hx
      simp only at hx
      have heq : w = base := hx.symm.trans hbase
      exact heq.symm ▸ List.Mem.head _
    · exact .tail _ (ih he)

/-- I21: `jalr ra, off(rs)` with a proved set of possible targets. -/
theorem Fn.callReg_step (hst : f.StructSpec) {c : Code} {D : Dom} {Q : State → Prop} (rn : Runner c P D Q)
    {S : STy} {s : State} {ι : Val} {Ft : TokFp} {k : Nat} {rs : Reg} {off : BitVec 12}
    (hI : Inv f T P s0 ι0 S s ι Ft) (hd : D.mem s.pc) (hpc : s.pc = f.pcOf k)
    (hi : c.instr s.pc = some (.jalr 1 rs off)) (hk : f.callRegOk k S rs off = true)
    (hcall : ∀ p ∈ f.callees, aligned p.1 4 ∧ ∃ Dg, rn.callee Dg p.1 (p.2.spec T) ∧ Dg.sub D ∧
      ∀ j < f.size, ¬ Dg.mem (f.pcOf j))
    {a : Val × TokFp} (hP : P = (f.sig.spec T).perm a s0) (hι0p : ∀ x ∈ f.sig.params, ι0 x = a.1 x)
    (hUF : f.UnitFrame T a s0 Ft)
    (hexit : ∀ s', s'.exit ≠ none → rn.later s')
    (cont : ∀ (F1 : TokFp) S1 s' ι1, s'.pc = f.pcOf (k + 1) → Inv f T P s0 ι0 S1 s' ι1 F1 →
      f.UnitFrame T a s0 F1 → (∀ y : Nat, y < f.fresh → ι1 y = ι y) → f.edge (some k) S1 (k + 1) = true →
      rn.later s') :
    rn.R s := by
  unfold Fn.callRegOk at hk
  cases hr : S.reg rs with
  | none => rw [hr] at hk; cases hk
  | some e =>
  simp only [hr] at hk
  have ht := STy.reg_hasInt hI.regs hr
  have htarget : f.callAt k S (Fn.regCallTarget (s.reg rs) off) = true := by
    by_cases hn : e.terms.isEmpty = true
    · simp only [hn, if_true] at hk
      rwa [ofInt_const_eq ht hn] at hk
    · simp only [hn] at hk
      have hcases := STy.ent_sound hk hI.hyps
      have hw := regCallCases_mem ht hcases
      exact (List.mem_filter.1 hw).2
  exact f.callAt_step hst rn hI hd hpc hi trivial
    (fun hal => by
      unfold Fn.regCallTarget at hal
      simp only [Fn.regCallTarget, exec, jumpTo, hal, if_true]) htarget hcall hP hι0p hUF hexit cont

end NoCompiler.Typed
