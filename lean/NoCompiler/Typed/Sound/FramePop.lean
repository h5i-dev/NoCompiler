import NoCompiler.Typed.Sound.FrameGeom

/-
Frames (Lemma 7): the epilogue `addi sp, sp, F`.
-/
namespace NoCompiler.Typed

variable {f : Fn} {T : TokEnv} {P : Perm} {s0 : State} {ι0 : Val}

set_option maxHeartbeats 2000000 in
/-- Lemma 7 (b): the epilogue. -/
theorem Fn.framePop_sound (hst : f.StructSpec) {S : STy} {s : State} {ι : Val} {Ft : TokFp}
    (hI : Inv f T P s0 ι0 S s ι Ft) {Fr : Frame} (hfr : f.frame = some Fr) (hd : S.depth = Fr.size)
    (hF0 : Fr.size ≠ 0) {e : IExpr} (he : S.reg 2 = some e) {imm : BitVec 12}
    (himm : imm.toInt = (Fr.size : Int)) {cs : List HCap} (hcs : Fn.framePopCaps S Fr e = some cs) :
    ∃ s', exec (.iop .addi 2 2 imm) s = some s' ∧
      Inv f T P s0 ι0 (Fn.framePop S Fr e cs) s' ι Ft ∧ s'.pc = s.pc + 4 := by
  have hg := f.frame_geom hst.frameDecl hfr
  have hsp := hI.sp
  rw [hd] at hsp
  have hK := hI.stackLe
  have hle := hg.sizeLe
  have hspl := (s0.reg Reg.sp).isLt
  have hre := STy.reg_hasInt hI.regs he
  rw [show (2 : Reg) = Reg.sp from rfl, hsp] at hre
  have hB := below_sp_toNat (s0.reg Reg.sp) Fr.size 0 (by omega) (by omega)
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.add_zero] at hB
  -- the new sp: back at the entry value
  have hse := hasInt_signExtend (by omega) ι imm
  rw [himm] at hse
  have hnew : s0.reg Reg.sp - BitVec.ofNat 64 Fr.size + imm.signExtend 64 = s0.reg Reg.sp := by
    apply BitVec.eq_of_toNat_eq
    unfold HasInt at hse; simp only [IExpr.eval_lit] at hse
    rw [BitVec.toNat_add, hB]
    have := (imm.signExtend 64).isLt
    omega
  simp only [exec, evalI, Option.some.injEq, exists_eq_left']
  refine ⟨?_, by simp⟩
  rw [show (2 : Reg) = Reg.sp from rfl, hsp, hnew]
  -- the popped capabilities cover the frame's ranges exactly
  obtain ⟨hlen, hget⟩ := mapM_some hcs
  have hpop : ∀ x, f.inFrame s0 Fr.size x → ∃ c ∈ cs, c ∈ S.caps ∧ c.cap.exclusive = true ∧
      c.cap.fp ι Ft x := by
    intro x hx
    obtain ⟨hx0, r, hr, h1, h2⟩ := (inFrame_iff hfr hF0 s0 (by omega) hg.addr x).1 hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hr
    have hjc : j < cs.length := by omega
    have hf := hget j hj hjc
    have hm := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨⟨_, hgd⟩, hk⟩ := hp
    split at hk
    · rename_i b hb
      simp only [Bool.and_eq_true, beq_iff_eq] at hk
      obtain ⟨⟨hrw, hbase⟩, hlenl⟩ := hk
      have hbase := hI.ent hbase
      have hlenl := hI.ent hlenl
      simp only [Constr.holds, Constr.eval, decide_eq_true_eq, IExpr.eval_add, IExpr.eval_lit] at hbase hlenl
      have hv := hI.valid _ hm (by simp [Constr.holds, hgd, Constr.eval])
      rw [hb] at hv
      obtain ⟨v0, v1, v2, -⟩ := hv
      unfold HasInt at hre; rw [hB] at hre
      have ho := hg.addr _ hr
      have hl := Fr.addr[j].2
      refine ⟨cs[j], List.getElem_mem hjc, hm, by simp [Cap.exclusive, hb, hrw], ?_⟩
      unfold Cap.fp Cap.regions
      rw [if_pos (by simp [hgd, Constr.eval]), hb]
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      rw [region_mem_iff v0 v1 v2]
      simp only [List.get_eq_getElem] at *
      omega
    · simp at hk
  have hsub : ∀ c ∈ (Fn.framePop S Fr e cs).caps, c ∈ S.caps ∧ ∀ d ∈ cs, c.id ≠ d.id := by
    intro c hc
    simp only [Fn.framePop, List.mem_filter, Bool.not_eq_true', List.any_eq_false, beq_iff_eq] at hc
    exact ⟨hc.1, fun d hd e' => hc.2 d hd e'.symm⟩
  refine ⟨by simpa [Fn.framePop] using hI.facts, ?_, hI.prot, ?_, ?_, ?_, ?_, ?_, ?_,
    by simpa using hI.live, .inl (by simp [Fn.framePop]), by simp [Fn.framePop],
    hI.stackW, hI.spAl, hI.stackLe⟩
  · intro p hp
    simp only [Fn.framePop, List.mem_cons, List.mem_filter, bne_iff_ne, ne_eq] at hp
    simp only [State.setPc_reg]
    rcases hp with rfl | ⟨hp, hp2⟩
    · rw [show (2 : Reg) = Reg.sp from rfl, State.reg_setReg_same _ _ _ (by decide)]
      unfold HasInt at hre ⊢
      rw [hB] at hre
      simp only [IExpr.eval_add, IExpr.eval_lit]
      omega
    · rw [State.reg_setReg_other _ _ _ _ hp2]; exact hI.regs p hp
  · intro c hc; simpa using hI.valid c (hsub c hc).1
  · intro c hc d hd hne hex x hx hy
    exact hI.sep c (hsub c hc).1 d (hsub d hd).1 hne hex x hx hy
  · intro c hc x hx hm
    exfalso
    have := hI.stack c (hsub c hc).1 x hx hm
    rw [hd] at this
    obtain ⟨d, hdc, hdS, hdex, hdfp⟩ := hpop x this
    exact hI.sep d hdS c (hsub c hc).1 ((hsub c hc).2 d hdc).symm hdex x hdfp hx
  · intro c hc x hx; exact hI.perm c (hsub c hc).1 x hx
  · simp only [Fn.framePop]
    exact (List.Sublist.map _ List.filter_sublist).nodup hI.ids
  · simp only [State.setPc_reg, Fn.framePop]
    rw [State.reg_setReg_same _ _ _ (by decide)]; simp

end NoCompiler.Typed
