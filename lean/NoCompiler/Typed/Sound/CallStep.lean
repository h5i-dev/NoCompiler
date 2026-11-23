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
  · cases h
  · unfold Fn.edgeOk at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1.1

/-- Lemma 8: a call of the callee at `t` (by `jal ra` or `jalr ra`), its whole run as one
    step (`VerifiedImg.call`), and the continuation after it returns. -/
theorem Fn.callAt_step (hst : f.StructSpec) {c : Code} {D : Dom} {Q : State → Prop}
    {S : STy} {s : State} {ι : Val} {Ft : TokFp} {k : Nat} {i : Instr} {t : Word}
    (hI : Inv f T P s0 ι0 S s ι Ft) (hd : D.mem s.pc) (hpc : s.pc = f.pcOf k)
    (hi : c.instr s.pc = some i) (hiok : InstrOk P i s)
    (hxi : aligned t 4 → exec i s = some ((s.setReg 1 (s.pc + 4)).setPc t))
    (hk : f.callAt k S t = true)
    (hcall : ∀ p ∈ f.callees, aligned p.1 4 ∧ ∃ Dg, Meets c Dg p.1 T p.2 ∧ Dg.sub D ∧
      ∀ j < f.size, ¬ Dg.mem (f.pcOf j))
    (hexit : ∀ s', s'.exit ≠ none → Reach c P D Q s')
    (cont : ∀ (F1 : TokFp) S1 s' ι1, s'.pc = f.pcOf (k + 1) → Inv f T P s0 ι0 S1 s' ι1 F1 →
      (∀ y : Nat, y < f.fresh → ι1 y = ι y) → f.edge (some k) S1 (k + 1) = true →
      Reach c P D Q s') :
    Reach c P D Q s := by
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
  have huniq : ∀ t ∈ g.tokNames, (S.caps.filter fun c => c.cap.kind == .token t).length = 1 := by
    simpa [List.all_eq_true] using huq
  have hgm := lookup_mem hg
  obtain ⟨hal, Dg, hmeets, hDg, hret⟩ := hcall _ hgm
  have hok := Fn.calleeOk_spec (hst.callees _ hgm)
  have hk1 := Fn.edge_lt hedge
  refine Reach.exec_step hd hI.live hi hiok ?_
  rw [hxi hal, Reach.opt_some]
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
  refine VerifiedImg.call hmeets (IExpr.upd ι θ, Ft) ⟨by simp, by simp [hI.live], ?_, ?_, ?_⟩
    hpre' hDg hle ?_
  · rw [hra]; exact hret _ hk1
  · rw [hra]; exact f.pcOf_aligned hst _
  · unfold aligned
    rw [hregs1 2 (by decide), hspn.1]
    have := hI.spAl; have := hspn.2.2; have := hspn.2.1; have := hI.stackLe
    omega
  · intro s2 hdone hfr
    rcases hdone with ⟨hlive, hpc2, hpres, hpost⟩ | ⟨hex, -⟩
    · obtain ⟨ι', F1, g1, hI'⟩ := f.afterCall_inv hst hI hok hθ hstk hls htx huniq hids hregs1 hmem1 hpres
        hlive hpost hfr
      refine cont F1 _ _ ι' ?_ hI' g1 hedge
      rw [hpc2]; exact hra
    · exact hexit s2 hex

theorem Fn.call_step (hst : f.StructSpec) {c : Code} {D : Dom} {Q : State → Prop}
    {S : STy} {s : State} {ι : Val} {Ft : TokFp} {k : Nat} {off : BitVec 21}
    (hI : Inv f T P s0 ι0 S s ι Ft) (hd : D.mem s.pc) (hpc : s.pc = f.pcOf k)
    (hi : c.instr s.pc = some (.jal 1 off)) (hk : f.callOk k S off = true)
    (hcall : ∀ p ∈ f.callees, aligned p.1 4 ∧ ∃ Dg, Meets c Dg p.1 T p.2 ∧ Dg.sub D ∧
      ∀ j < f.size, ¬ Dg.mem (f.pcOf j))
    (hexit : ∀ s', s'.exit ≠ none → Reach c P D Q s')
    (cont : ∀ (F1 : TokFp) S1 s' ι1, s'.pc = f.pcOf (k + 1) → Inv f T P s0 ι0 S1 s' ι1 F1 →
      (∀ y : Nat, y < f.fresh → ι1 y = ι y) → f.edge (some k) S1 (k + 1) = true →
      Reach c P D Q s') :
    Reach c P D Q s :=
  f.callAt_step hst hI hd hpc hi trivial
    (fun hal => by simp only [exec, jumpTo, hpc, hal, if_true]) hk hcall hexit cont

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

/-- I21: `jalr ra, off(rs)` with `rs` a known constant. -/
theorem Fn.callReg_step (hst : f.StructSpec) {c : Code} {D : Dom} {Q : State → Prop}
    {S : STy} {s : State} {ι : Val} {Ft : TokFp} {k : Nat} {rs : Reg} {off : BitVec 12}
    (hI : Inv f T P s0 ι0 S s ι Ft) (hd : D.mem s.pc) (hpc : s.pc = f.pcOf k)
    (hi : c.instr s.pc = some (.jalr 1 rs off)) (hk : f.callRegOk k S rs off = true)
    (hcall : ∀ p ∈ f.callees, aligned p.1 4 ∧ ∃ Dg, Meets c Dg p.1 T p.2 ∧ Dg.sub D ∧
      ∀ j < f.size, ¬ Dg.mem (f.pcOf j))
    (hexit : ∀ s', s'.exit ≠ none → Reach c P D Q s')
    (cont : ∀ (F1 : TokFp) S1 s' ι1, s'.pc = f.pcOf (k + 1) → Inv f T P s0 ι0 S1 s' ι1 F1 →
      (∀ y : Nat, y < f.fresh → ι1 y = ι y) → f.edge (some k) S1 (k + 1) = true →
      Reach c P D Q s') :
    Reach c P D Q s := by
  unfold Fn.callRegOk at hk
  cases hr : S.reg rs with
  | none => rw [hr] at hk; cases hk
  | some e =>
  rw [hr] at hk
  simp only [Bool.and_eq_true] at hk
  obtain ⟨hnil, hk⟩ := hk
  have hv : BitVec.ofInt 64 e.const = s.reg rs :=
    ofInt_const_eq (STy.reg_hasInt hI.regs hr) hnil
  rw [hv] at hk
  exact f.callAt_step hst hI hd hpc hi trivial
    (fun hal => by simp only [exec, jumpTo, hal, if_true]) hk hcall hexit cont

end NoCompiler.Typed
