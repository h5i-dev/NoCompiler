import NoCompiler.Typed.Sound.Frame
import NoCompiler.Typed.Sound.Runner

/-
Soundness of the `ecall` rule (Lemma 9). Owned by agent U (STATUS.md).

Every outcome `Sys` (NoCompiler/Env.lean) allows is covered: `exit` ends the run; a `write`
changes `a0` and the trace; a `read` also writes bytes, all inside the exclusive capability
the rule found, whose fields it then drops. The capability's footprint gives the
permissions `SysOk` asks for.
-/
namespace NoCompiler.Typed

variable {f : Fn} {T : TokEnv} {P : Perm} {s0 : State} {ι0 : Val}

theorem HCap.dropFields_same (id : Nat) (d : HCap) :
    (d.dropFields id).id = d.id ∧ (d.dropFields id).cap.guard = d.cap.guard ∧
      (d.dropFields id).cap.exclusive = d.cap.exclusive ∧
      (∀ ι F x, (d.dropFields id).cap.fp ι F x ↔ d.cap.fp ι F x) := by
  unfold HCap.dropFields
  split
  · split
    · rename_i bc hk
      refine ⟨rfl, rfl, by simp [Cap.exclusive, hk], fun ι F x => ?_⟩
      simp [Cap.fp, Cap.regions, hk, BytesCap.region]
    · exact ⟨rfl, rfl, rfl, fun _ _ _ => Iff.rfl⟩
  · exact ⟨rfl, rfl, rfl, fun _ _ _ => Iff.rfl⟩

/-- Memory changed only inside the exclusive byte capability `c`, whose fields are dropped:
    the invariant holds again. -/
theorem Inv.writeInside {S : STy} {s : State} {ι : Val} {F : TokFp} (hI : Inv f T P s0 ι0 S s ι F)
    {c : HCap} (hc : c ∈ S.caps) {bc0 : BytesCap} (hk0 : c.cap.kind = .bytes bc0)
    (hex : c.cap.exclusive = true) {m' : Word → Byte}
    (hm : ∀ x, ¬ c.cap.fp ι F x → m' x = s.mem x) :
    Inv f T P s0 ι0 (S.dropFields c.id) (s.setMem m') ι F := by
  have hout : ∀ d ∈ S.caps, d.id ≠ c.id → ∀ x, d.cap.fp ι F x → m' x = s.mem x :=
    fun d hd hne x hx => hm x (fun hcx => hI.sep c hc d hd (Ne.symm hne) hex x hcx hx)
  refine ⟨hI.facts, hI.regs, hI.prot, ?_, ?_, ?_, ?_, ?_, hI.sp,
    hI.live, hI.depth, ?_, hI.stackW, hI.spAl, hI.stackLe⟩
  · intro d' hd'
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hd'
    simp only [State.setMem_mem]
    by_cases hdc : d.id = c.id
    · have : d = c := eq_of_id_eq hI.ids hd hc hdc
      subst this
      have hv := hI.valid d hd
      unfold HCap.dropFields
      simp only [beq_self_eq_true, ite_true]
      split
      · rename_i bc hk
        unfold Cap.valid at hv ⊢
        intro hg
        have hv := hv hg
        rw [hk] at hv
        obtain ⟨h0, h1, h2, -, hh⟩ := hv
        exact ⟨h0, h1, h2, fun fd hfd => by simp at hfd, hh⟩
      · rename_i t ht; rw [hk0] at ht; cases ht
    · unfold HCap.dropFields
      simp only [beq_iff_eq, hdc, ite_false]
      exact Cap.valid_congr (hI.valid d hd) (fun x hx => (hout d hd hdc x hx).symm)
  · intro c1 hc1 d1 hd1 hne hex1 x hx hy
    obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hc1
    obtain ⟨d0, hd0, rfl⟩ := List.mem_map.1 hd1
    obtain ⟨i1, -, e1, f1⟩ := HCap.dropFields_same c.id c0
    obtain ⟨i2, -, -, f2⟩ := HCap.dropFields_same c.id d0
    exact hI.sep c0 hc0 d0 hd0 (by rw [← i1, ← i2]; exact hne) (e1 ▸ hex1) x ((f1 ι F x).1 hx)
      ((f2 ι F x).1 hy)
  · intro c1 hc1 x hx
    obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hc1
    exact hI.stack c0 hc0 x (((HCap.dropFields_same c.id c0).2.2.2 ι F x).1 hx)
  · intro c1 hc1 x hx
    obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hc1
    obtain ⟨-, -, e1, f1⟩ := HCap.dropFields_same c.id c0
    obtain ⟨r1, r2⟩ := hI.perm c0 hc0 x ((f1 ι F x).1 hx)
    exact ⟨r1, fun h => r2 (e1 ▸ h)⟩
  · have : (S.caps.map (HCap.dropFields c.id)).map (·.id) = S.caps.map (·.id) := by
      rw [List.map_map]; exact List.map_congr_left (fun d _ => (HCap.dropFields_same c.id d).1)
    simp only [STy.dropFields]; rw [this]; exact hI.ids
  · intro p hp
    obtain ⟨h1, hb, h2⟩ := hI.slots p hp
    refine ⟨h1, hb, ?_⟩
    simp only [State.setMem_mem, STy.dropFields]
    have : read64 m' (s0.reg Reg.sp - BitVec.ofNat 64 S.depth + BitVec.ofNat 64 p.1) =
        read64 s.mem (s0.reg Reg.sp - BitVec.ofNat 64 S.depth + BitVec.ofNat 64 p.1) := by
      exact read64_congr fun i hi => hm _ (fun hcx => (hb i hi).2 (hI.stack c hc _ hcx (hb i hi).1))
    rw [this]; exact h2

/-- The invariant does not look at the trace. -/
theorem Inv.emit {S : STy} {s : State} {ι : Val} {F : TokFp} (hI : Inv f T P s0 ι0 S s ι F)
    (e : Event) : Inv f T P s0 ι0 S (s.emit e) ι F :=
  ⟨hI.facts, hI.regs, hI.prot, hI.valid, hI.sep, hI.stack, hI.perm, hI.ids, hI.sp, hI.live,
    hI.depth, hI.slots, hI.stackW, hI.spAl, hI.stackLe⟩

theorem State.setMem_self (s : State) : s.setMem s.mem = s := by cases s; rfl

theorem State.sysRet_setMem (s : State) (r : Word) (m : Word → Byte) :
    (s.sysRet r).setMem m = ((s.setMem m).setReg 10 r).setPc (s.pc + 4) := by cases s; rfl

/-- The result facts hold for a value `r` the environment allows. -/
theorem sysResult_holds {ι : Val} {write : Bool} {x : Var} {n : IExpr} {r : Int}
    (hx : ι x = r) (h : (-4095 ≤ r ∧ r ≤ -1) ∨
      (0 ≤ r ∧ r ≤ n.eval ι ∧ r ≤ 0x7ffff000 ∧ (write = true → 1 ≤ n.eval ι → 1 ≤ r))) :
    (Fn.sysResult write x n).holds ι := by
  cases write <;>
  simp [Fn.sysResult, Constr.holds, Constr.eval, Constr.imp, IExpr.eval_var, IExpr.eval_lit, hx] at h ⊢
    <;> omega

theorem hasInt_err (ι : Val) (x : Var) (e : Nat) (he : e ≤ 4095) (hx : ι x = -(e : Int)) :
    HasInt ι (-(BitVec.ofNat 64 e)) (.var x) := by
  unfold HasInt
  rw [IExpr.eval_var, hx, BitVec.toNat_neg, BitVec.toNat_ofNat]
  omega

theorem hasInt_ok (ι : Val) (x : Var) (r : Nat) (hr : r ≤ maxRW) (hx : ι x = (r : Int)) :
    HasInt ι (BitVec.ofNat 64 r) (.var x) := by
  unfold HasInt
  rw [IExpr.eval_var, hx, BitVec.toNat_ofNat]
  unfold maxRW at hr
  omega

theorem sysWrite_ne_read : sysWrite ≠ sysRead := by decide
theorem sysExit_ne : sysExit ≠ sysWrite ∧ sysExit ≠ sysRead := by decide
theorem sysExitGroup_ne : sysExitGroup ≠ sysWrite ∧ sysExitGroup ≠ sysRead := by decide

theorem Fn.ecall_step (hst : f.StructSpec) {c : Code} {D : Dom} {Q : State → Prop} (rn : Runner c P D Q)
    {S : STy} {s : State} {ι : Val} {Ft : TokFp} {k : Nat}
    (hI : Inv f T P s0 ι0 S s ι Ft) (hd : D.mem s.pc) (hpc : s.pc = f.pcOf k)
    (hi : c.instr s.pc = some .ecall) (hk : f.ecallOk k S = true)
    (hexit : ∀ s', s'.exit ≠ none → rn.later s')
    (cont : ∀ S1 s' ι1, s'.pc = f.pcOf (k + 1) → Inv f T P s0 ι0 S1 s' ι1 Ft →
      (∀ y : Nat, y < f.fresh → ι1 y = ι y) → f.edge (some k) S1 (k + 1) = true →
      rn.later s') :
    rn.R s := by
  have hpc4 : s.pc + 4 = f.pcOf (k + 1) := by
    rw [hpc]; unfold Fn.pcOf; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (4 : Word).toNat = 4 from rfl]; omega
  unfold Fn.ecallOk at hk
  split at hk
  case h_2 => cases hk
  rename_i e he
  by_cases ht : e.terms = []
  case neg => rw [if_neg ht] at hk; cases hk
  rw [if_pos ht] at hk
  dsimp only at hk
  -- a7 holds the constant
  have h7 : s.reg Reg.a7 = BitVec.ofInt 64 e.const := by
    have hh := STy.reg_hasInt hI.regs he
    have : e = ⟨e.const, []⟩ := by cases e; simp_all
    rw [this] at hh; exact eq_ofInt_of_hasInt hh
  generalize hw : BitVec.ofInt 64 e.const = w at hk h7
  by_cases hx : w = sysExit ∨ w = sysExitGroup
  · -- exit: every outcome ends the run
    have hnw : w ≠ sysWrite ∧ w ≠ sysRead := by
      rcases hx with h | h <;> rw [h]
      · exact sysExit_ne
      · exact sysExitGroup_ne
    refine rn.sys hd hI.live hi ⟨fun h => absurd (h7 ▸ h) hnw.1,
      fun h => absurd (h7 ▸ h) hnw.2⟩ ⟨_, Sys.exit (h7 ▸ hx)⟩ (fun s' hs => ?_)
    cases hs with
    | writeOk _ h => exact absurd (h7 ▸ h) hnw.1
    | writeErr _ h => exact absurd (h7 ▸ h) hnw.1
    | readOk _ h => exact absurd (h7 ▸ h) hnw.2
    | readErr _ h => exact absurd (h7 ▸ h) hnw.2
    | exit _ => exact rn.later_next _ (hexit _ (by simp [State.emit, State.halt]))
  rw [if_neg hx] at hk
  by_cases hrw : w = sysWrite ∨ w = sysRead
  case neg => rw [if_neg hrw] at hk; cases hk
  rw [if_pos hrw] at hk
  split at hk
  case h_2 => cases hk
  rename_i b n hb hn
  simp only [Bool.and_eq_true] at hk
  obtain ⟨hbd, hk⟩ := hk
  split at hk
  case h_2 => cases hk
  rename_i cap hcap
  -- the length and the capability
  have hbd := hI.ent hbd
  simp only [Constr.holds, Constr.eval, Constr.lt, IExpr.eval_add, IExpr.eval_lit,
    Bool.and_eq_true, decide_eq_true_eq] at hbd
  have hB := STy.reg_hasInt hI.regs hb
  have hN := STy.reg_hasInt hI.regs hn
  have hNn : ((s.reg Reg.a2).toNat : Int) = n.eval ι := hN.toNat_eq hbd.1 (by omega)
  have hcm : cap ∈ S.caps := List.mem_of_find?_eq_some hcap
  have hok := List.find?_some hcap
  unfold Fn.sysCapOk at hok
  split at hok
  case h_2 => cases hok
  rename_i bc hkind
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    beq_iff_eq] at hok
  obtain ⟨⟨hmode, hg⟩, hin⟩ := hok
  have hg := hI.ent hg
  have hin := hI.ent hin
  simp only [Constr.holds, Constr.eval, IExpr.eval_add, Bool.and_eq_true, decide_eq_true_eq] at hin
  have hv := hI.valid cap hcm hg
  unfold Cap.valid at hv
  rw [hkind] at hv
  obtain ⟨h0, h1, h2, -, -⟩ := hv
  have hfp : ∀ i < (s.reg Reg.a2).toNat, cap.cap.fp ι Ft (s.reg Reg.a1 + BitVec.ofNat 64 i) := by
    intro i hi
    have hA : ((s.reg Reg.a1).toNat : Int) = b.eval ι := hB.toNat_eq (by omega) (by omega)
    exact access_fp hkind hg h0 h1 h2 (by omega) (by omega) i hi
  have hrwOf : w = sysRead → cap.cap.exclusive = true := by
    intro hR
    have : bc.mode = .rw := by
      rcases hmode with h | h
      · exact absurd hR h
      · exact h
    simp [Cap.exclusive, hkind, this]
  have hok : SysOk P s :=
    ⟨fun _ i hi => (hI.perm cap hcm _ (hfp i hi)).1,
     fun h i hi => (hI.perm cap hcm _ (hfp i hi)).2 (hrwOf (h7 ▸ h))⟩
  have hex : ∃ s', Sys s s' := by
    rcases hrw with h | h
    · exact ⟨_, Sys.writeErr 1 (h7 ▸ h) (Nat.le_refl _) (by decide)⟩
    · exact ⟨_, Sys.readErr 1 (h7 ▸ h) (Nat.le_refl _) (by decide)⟩
  have hn' : ∀ S1 : STy, S1.reg 12 = some n → ∀ vs,
      n.eval (setFrom ι (f.freshAt S1) vs) = n.eval ι :=
    fun S1 h vs => Fn.eval_setFrom_old (STy.reg_maxVar' h) ι vs
  refine rn.sys hd hI.live hi hok hex (fun s' hs => ?_)
  cases hs with
  | writeOk r h hr1 hr2 hr3 =>
    have hW : w = sysWrite := h7 ▸ h
    simp only [hW, decide_true, sysWrite_ne_read.symm, decide_false, Fn.sysAfter, ite_true] at hk
    obtain ⟨ι', g, hI'⟩ := hI.fresh hst.protFresh (rd := 10) (by decide) [(r : Int)]
      (.var (f.freshAt S)) [Fn.sysResult true (f.freshAt S) n] (BitVec.ofNat 64 r)
      (hasInt_ok _ _ r hr2 setFrom_x) (by
        intro p hp; simp only [List.mem_singleton] at hp; subst hp
        refine sysResult_holds setFrom_x (Or.inr ⟨by omega, ?_, by unfold maxRW at hr2; omega, ?_⟩)
        · rw [hn' S hn]; omega
        · intro _ h1; rw [hn' S hn] at h1; have := hr3 (by omega); omega) (s.pc + 4)
    exact rn.later_next _ (cont _ _ ι' hpc4 (hI'.emit _) g hk)
  | writeErr e h he1 he2 =>
    have hW : w = sysWrite := h7 ▸ h
    simp only [hW, decide_true, sysWrite_ne_read.symm, decide_false, Fn.sysAfter, ite_true] at hk
    obtain ⟨ι', g, hI'⟩ := hI.fresh hst.protFresh (rd := 10) (by decide) [-(e : Int)]
      (.var (f.freshAt S)) [Fn.sysResult true (f.freshAt S) n] (-(BitVec.ofNat 64 e))
      (hasInt_err _ _ e he2 setFrom_x) (by
        intro p hp; simp only [List.mem_singleton] at hp; subst hp
        exact sysResult_holds setFrom_x (Or.inl ⟨by omega, by omega⟩)) (s.pc + 4)
    exact rn.later_next _ (cont _ _ ι' hpc4 hI' g hk)
  | readOk ds h hl1 hl2 =>
    have hR : w = sysRead := h7 ▸ h
    simp only [hR, decide_true, sysWrite_ne_read.symm, decide_false, Fn.sysAfter,
      Bool.false_eq_true, ite_false] at hk
    have hI1 := hI.writeInside hcm hkind (hrwOf hR)
      (m' := writeBytes s.mem (s.reg Reg.a1) ds) (fun x hx =>
        writeBytes_other _ _ _ _ (Nat.le_of_not_lt fun hlt => hx (by
          have := hfp _ (by omega : (x - s.reg Reg.a1).toNat < (s.reg Reg.a2).toNat)
          rwa [add_ofNat_sub] at this)))
    have hn1 : (S.dropFields cap.id).reg 12 = some n := hn
    obtain ⟨ι', g, hI'⟩ := hI1.fresh hst.protFresh (rd := 10) (by decide) [(ds.length : Int)]
      (.var (f.freshAt (S.dropFields cap.id))) [Fn.sysResult false (f.freshAt (S.dropFields cap.id)) n]
      (BitVec.ofNat 64 ds.length) (hasInt_ok _ _ _ hl2 setFrom_x) (by
        intro p hp; simp only [List.mem_singleton] at hp; subst hp
        refine sysResult_holds setFrom_x (Or.inr ⟨by omega, ?_, by unfold maxRW at hl2; omega,
          fun h => by cases h⟩)
        rw [hn' _ hn1]; omega) (s.pc + 4)
    rw [State.sysRet_setMem]
    exact rn.later_next _ (cont _ _ ι' hpc4 (hI'.emit _) g hk)
  | readErr e h he1 he2 =>
    have hR : w = sysRead := h7 ▸ h
    simp only [hR, decide_true, sysWrite_ne_read.symm, decide_false, Fn.sysAfter,
      Bool.false_eq_true, ite_false] at hk
    have hI1 := hI.writeInside hcm hkind (hrwOf hR) (m' := s.mem) (fun _ _ => rfl)
    rw [State.setMem_self] at hI1
    obtain ⟨ι', g, hI'⟩ := hI1.fresh hst.protFresh (rd := 10) (by decide) [-(e : Int)]
      (.var (f.freshAt (S.dropFields cap.id))) [Fn.sysResult false (f.freshAt (S.dropFields cap.id)) n]
      (-(BitVec.ofNat 64 e)) (hasInt_err _ _ e he2 setFrom_x) (by
        intro p hp; simp only [List.mem_singleton] at hp; subst hp
        exact sysResult_holds setFrom_x (Or.inl ⟨by omega, by omega⟩)) (s.pc + 4)
    exact rn.later_next _ (cont _ _ ι' hpc4 hI' g hk)
  | exit h => exact absurd (h7 ▸ h) hx

end NoCompiler.Typed
