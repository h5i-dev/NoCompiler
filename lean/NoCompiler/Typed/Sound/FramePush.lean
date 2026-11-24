import NoCompiler.Typed.Sound.FrameGeom

/-
Frames (Lemma 7): the prologue `addi sp, sp, -F` and the address-taken ranges' capabilities.
-/
namespace NoCompiler.Typed

variable {f : Fn} {T : TokEnv} {P : Perm} {s0 : State} {ι0 : Val}

theorem Fn.framePushNew_length {k : Nat} {S : STy} {Fr : Frame} {e : IExpr} :
    (f.framePushNew k S Fr e).length = Fr.addr.length := by simp [Fn.framePushNew]

/-- The new capabilities of the prologue, by index. -/
theorem Fn.framePushNew_mem {k : Nat} {S : STy} {Fr : Frame} {e : IExpr} {c : HCap}
    (h : c ∈ f.framePushNew k S Fr e) :
    ∃ j, ∃ hj : j < Fr.addr.length,
      c = (f.framePushNew k S Fr e)[j]'(by rw [Fn.framePushNew_length]; exact hj) := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem h
  exact ⟨j, by rw [Fn.framePushNew_length] at hj; exact hj, rfl⟩

theorem Fn.framePushNew_get {k : Nat} {S : STy} {Fr : Frame} {e : IExpr} {j : Nat}
    (hj : j < Fr.addr.length) :
    ((f.framePushNew k S Fr e)[j]'(by rw [Fn.framePushNew_length]; exact hj)).origin = none ∧
    ((f.framePushNew k S Fr e)[j]'(by rw [Fn.framePushNew_length]; exact hj)).cap =
      ⟨.tt, .bytes ⟨e.add (.lit (((Fr.addr[j]).1 : Int) - Fr.size)), .lit (Fr.addr[j]).2, .rw, false, []⟩⟩ := by
  simp [Fn.framePushNew]

set_option maxHeartbeats 2000000 in
/-- Lemma 7 (a): the prologue. -/
theorem Fn.framePush_sound (hst : f.StructSpec) {S : STy} {s : State} {ι : Val} {Ft : TokFp}
    (hI : Inv f T P s0 ι0 S s ι Ft) {Fr : Frame} (hfr : f.frame = some Fr) (hd0 : S.depth = 0)
    (hF0 : Fr.size ≠ 0) {e : IExpr} (he : S.reg 2 = some e) {imm : BitVec 12}
    (himm : imm.toInt = -(Fr.size : Int)) (h1 : S.ent (.le (.lit Fr.size) e) = true)
    (h2 : S.ent (.lt e (.lit (2 ^ 64))) = true) {k : Nat}
    (hids : ((f.framePush k S Fr e).caps.map (·.id)).Nodup) :
    ∃ s', exec (.iop .addi 2 2 imm) s = some s' ∧
      Inv f T P s0 ι0 (f.framePush k S Fr e) s' ι Ft ∧ s'.pc = s.pc + 4 := by
  have hg := f.frame_geom hst.frameDecl hfr
  have hsp := hI.sp
  rw [hd0] at hsp; simp only [BitVec.ofNat_eq_ofNat, BitVec.sub_zero] at hsp
  have hK := hI.stackLe
  have hle := hg.sizeLe
  have hspl := (s0.reg Reg.sp).isLt
  -- the value of `e`: the entry sp
  have hre := STy.reg_hasInt hI.regs he
  have h1 := hI.ent h1
  have h2 := hI.ent h2
  simp only [Constr.holds, Constr.lt, Constr.eval, decide_eq_true_eq, IExpr.eval_lit,
    IExpr.eval_add] at h1 h2
  have hev := hre.toNat_eq (by omega) (by omega)
  rw [show (2 : Reg) = Reg.sp from rfl, hsp] at hev
  -- the new sp
  have hse := hasInt_signExtend (by omega) ι imm
  rw [himm] at hse
  have hnew : s0.reg Reg.sp + imm.signExtend 64 = s0.reg Reg.sp - BitVec.ofNat 64 Fr.size := by
    apply BitVec.eq_of_toNat_eq
    unfold HasInt at hse; simp only [IExpr.eval_lit] at hse
    rw [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := Fr.size) (by omega)]
    have := (imm.signExtend 64).isLt
    omega
  simp only [exec, evalI, Option.some.injEq, exists_eq_left']
  refine ⟨?_, by simp⟩
  rw [show (2 : Reg) = Reg.sp from rfl, hsp, hnew]
  -- the frame capabilities' footprints: inside the frame, inside the stack region
  have hfc : ∀ r ∈ Fr.addr, ∀ x,
      (Cap.fp ι Ft { kind := .bytes { base := e.add (.lit ((r.1 : Int) - Fr.size)), len := .lit r.2,
                                      mode := .rw } } x) ↔
        (s0.reg Reg.sp).toNat - Fr.size + r.1 ≤ x.toNat ∧
          x.toNat < (s0.reg Reg.sp).toNat - Fr.size + r.1 + r.2 := by
    intro r hr x
    have := hg.addr r hr
    unfold Cap.fp Cap.regions
    simp only [Constr.eval, ite_true, List.mem_singleton, exists_eq_left]
    rw [region_mem_iff (by simp; omega) (by simp) (by simp; omega)]
    simp only [IExpr.eval_add, IExpr.eval_lit]
    omega
  have hold : ∀ c ∈ S.caps, ∀ x, c.cap.fp ι Ft x → ¬ (Spec.stackRegion s0 f.sig.stack).mem x := by
    intro c hc x hx hm
    obtain ⟨-, -, -, hne, -⟩ := hI.stack c hc x hx hm
    exact hne hd0
  -- a new capability: its footprint is its range, in the stack region and in the frame
  have hnew_fp : ∀ c ∈ f.framePushNew k S Fr e, ∃ r ∈ Fr.addr, c.origin = none ∧
      c.cap.exclusive = true ∧ (∀ x, c.cap.fp ι Ft x ↔
        (s0.reg Reg.sp).toNat - Fr.size + r.1 ≤ x.toNat ∧
          x.toNat < (s0.reg Reg.sp).toNat - Fr.size + r.1 + r.2) := by
    intro c hc
    obtain ⟨j, hj, rfl⟩ := f.framePushNew_mem hc
    obtain ⟨ho, hcap⟩ := f.framePushNew_get (k := k) (S := S) (e := e) hj
    refine ⟨_, List.getElem_mem hj, ho, by rw [hcap]; rfl, fun x => ?_⟩
    rw [hcap]; exact hfc _ (List.getElem_mem hj) x
  have hnew_stack : ∀ c ∈ f.framePushNew k S Fr e, ∀ x, c.cap.fp ι Ft x →
      (Spec.stackRegion s0 f.sig.stack).mem x ∧ f.inFrame s0 Fr.size x := by
    intro c hc x hx
    obtain ⟨r, hr, -, -, hfp⟩ := hnew_fp c hc
    have hx := (hfp x).1 hx
    have := hg.addr r hr
    refine ⟨(stack_mem_iff s0 _ hK x).2 ⟨by omega, by omega⟩, ?_⟩
    exact (inFrame_iff hfr hF0 s0 (by omega) hg.addr x).2 ⟨by omega, r, hr, by omega, by omega⟩
  have hcaps : ∀ c ∈ (f.framePush k S Fr e).caps, c ∈ S.caps ∨ c ∈ f.framePushNew k S Fr e := by
    intro c hc; simpa [Fn.framePush] using hc
  refine ⟨by simpa [Fn.framePush] using hI.facts, ?_, hI.prot, ?_, ?_, ?_, ?_, hids, ?_,
    by simpa using hI.live, .inr ⟨Fr, hfr, by simp [Fn.framePush], hF0⟩, by simp [Fn.framePush],
    hI.stackW, hI.spAl, hI.stackLe⟩
  · -- registers
    intro p hp
    simp only [Fn.framePush, List.mem_cons, List.mem_filter, bne_iff_ne, ne_eq] at hp
    simp only [State.setPc_reg]
    rcases hp with rfl | ⟨hp, hp2⟩
    · rw [show (2 : Reg) = Reg.sp from rfl, State.reg_setReg_same _ _ _ (by decide)]
      refine hasInt_toNat' ?_
      have := below_sp_toNat (s0.reg Reg.sp) Fr.size 0 (by omega) (by omega)
      simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.add_zero] at this
      simp only [IExpr.eval_add, IExpr.eval_lit, show (2 : Reg) = Reg.sp from rfl, hev, this]
      omega
    · rw [State.reg_setReg_other _ _ _ _ hp2]; exact hI.regs p hp
  · intro c hc
    rcases hcaps c hc with h | h
    · simpa using hI.valid c h
    · obtain ⟨j, hj, rfl⟩ := f.framePushNew_mem h
      obtain ⟨-, hcap⟩ := f.framePushNew_get (k := k) (S := S) (e := e) hj
      rw [hcap]
      have := hg.addr _ (List.getElem_mem hj)
      intro _
      simp only [IExpr.eval_add, IExpr.eval_lit]
      refine ⟨by omega, by omega, by omega, by simp⟩
  · intro c hc d hd hne hex x hx hy
    rcases hcaps c hc with h1 | h1 <;> rcases hcaps d hd with h2 | h2
    · exact hI.sep c h1 d h2 hne hex x hx hy
    · exact hold c h1 x hx (hnew_stack d h2 x hy).1
    · exact hold d h2 x hy (hnew_stack c h1 x hx).1
    · obtain ⟨i, hi, rfl⟩ := f.framePushNew_mem h1
      obtain ⟨j, hj, rfl⟩ := f.framePushNew_mem h2
      have hij : i ≠ j := fun e => hne (by subst e; rfl)
      obtain ⟨-, hci⟩ := f.framePushNew_get (k := k) (S := S) (e := e) hi
      obtain ⟨-, hcj⟩ := f.framePushNew_get (k := k) (S := S) (e := e) hj
      rw [hci] at hx; rw [hcj] at hy
      have hx := (hfc _ (List.getElem_mem hi) x).1 hx
      have hy := (hfc _ (List.getElem_mem hj) x).1 hy
      rcases hg.addrApart i j hi hj hij with h | h <;> omega
  · intro c hc x hx hm
    rcases hcaps c hc with h | h
    · exact absurd hm (hold c h x hx)
    · simpa [Fn.framePush] using (hnew_stack c h x hx).2
  · intro c hc x hx
    rcases hcaps c hc with h | h
    · exact hI.perm c h x hx
    · have hw := hI.stackW x (hnew_stack c h x hx).1
      exact ⟨Perm.readable_of_writable hw, fun _ => hw⟩
  · simp only [State.setPc_reg, Fn.framePush]
    rw [State.reg_setReg_same _ _ _ (by decide)]

end NoCompiler.Typed

namespace NoCompiler.Typed

variable {f : Fn} {T : TokEnv} {P : Perm} {s0 : State} {ι0 : Val}

end NoCompiler.Typed
