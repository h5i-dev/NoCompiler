import NoCompiler.Typed.Sound.Call
import NoCompiler.Typed.Sound.Ecall

/-
The soundness theorem of the Lean checker (Theorems A–C of docs/健全性の証明.md for the
functions milestone 1 accepts): a function the checker accepts meets its signature,
⟦σ⟧ in the total sense (`Typed.Meets`).
-/
namespace NoCompiler.Typed

variable {f : Fn} {T : TokEnv}

/-! ## The entry valuation -/

/-- The signature's valuation with the entry values of the kept registers. -/
def Fn.entryVal (f : Fn) (ι : Val) (s0 : State) : Val := fun x =>
  match f.regVar.find? (·.2 == x) with
  | some p => (s0.reg p.1).toNat
  | none =>
    match (List.finRange 32).find? (fun r => f.fresh + r.val == x) with
    | some r => (s0.reg r).toNat
    | none => ι x

theorem Fn.regVar_nodup (hst : f.StructSpec) : (f.regVar.map (·.2)).Nodup := by
  have := hst.protNodup; unfold Fn.protectedVars at this
  exact (List.nodup_append.1 this).2.1

theorem eq_of_map_eq {α β : Type} {g : α → β} : ∀ {l : List α}, (l.map g).Nodup → ∀ {a b : α},
    a ∈ l → b ∈ l → g a = g b → a = b
  | [], _, _, _, ha, _, _ => by simp at ha
  | c :: l, hn, a, b, ha, hb, he => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exact absurd ⟨b, hb, he.symm⟩ hn.1
    · exact absurd ⟨a, ha, he⟩ hn.1
    · exact eq_of_map_eq hn.2 ha hb he

theorem Fn.entryVal_reg (hst : f.StructSpec) (ι : Val) (s0 : State) {r : Reg} {x : Var}
    (h : (r, x) ∈ f.regVar) : f.entryVal ι s0 x = (s0.reg r).toNat := by
  unfold Fn.entryVal
  cases hf : f.regVar.find? (·.2 == x) with
  | none =>
    have := List.find?_eq_none.1 hf (r, x) h
    simp at this
  | some p =>
    have hp := List.mem_of_find?_eq_some hf
    have hpx : p.2 = x := by simpa using List.find?_some hf
    have : p = (r, x) := eq_of_map_eq (f.regVar_nodup hst) hp h (by simpa using hpx)
    rw [this]

theorem Fn.entryVal_entry (hst : f.StructSpec) (ι : Val) (s0 : State) (r : Reg) :
    f.entryVal ι s0 (f.fresh + r.val) = (s0.reg r).toNat := by
  unfold Fn.entryVal
  cases hf : f.regVar.find? (·.2 == f.fresh + r.val) with
  | some p =>
    exfalso
    have hp := List.mem_of_find?_eq_some hf
    have hpx : p.2 = f.fresh + r.val := by simpa using List.find?_some hf
    have h1 : p.2 < f.fresh := hst.protFresh p.2 (f.regVar_prot (r := p.1) (by simpa using hp))
    rw [hpx] at h1
    exact absurd h1 (Nat.not_lt.2 (Nat.le_add_right _ _))
  | none =>
    simp only
    cases hg : (List.finRange 32).find? (fun q => f.fresh + q.val == f.fresh + r.val) with
    | none =>
      have := List.find?_eq_none.1 hg r (List.mem_finRange r)
      simp at this
    | some q =>
      have := List.find?_some hg
      simp only [beq_iff_eq, Nat.add_left_cancel_iff] at this
      have : q = r := Fin.ext this
      subst this; rfl

theorem Fn.entryVal_param (hst : f.StructSpec) (ι : Val) (s0 : State) {x : Var}
    (h : x ∈ f.sig.params) : f.entryVal ι s0 x = ι x := by
  unfold Fn.entryVal
  cases hf : f.regVar.find? (·.2 == x) with
  | none =>
    simp only
    cases hg : (List.finRange 32).find? (fun q => f.fresh + q.val == x) with
    | none => rfl
    | some q =>
      exfalso
      have e : f.fresh + q.val = x := by simpa using List.find?_some hg
      have h1 : x < f.fresh := hst.protFresh x (f.param_prot h)
      rw [← e] at h1
      exact absurd h1 (Nat.not_lt.2 (Nat.le_add_right _ _))
  | some p =>
    exfalso
    have hp := List.mem_of_find?_eq_some hf
    have hpx : p.2 = x := by simpa using List.find?_some hf
    have := hst.protNodup; unfold Fn.protectedVars at this
    exact (List.nodup_append.1 this).2.2 x h x (List.mem_map.2 ⟨p, hp, hpx⟩) rfl

/-! ## Instruction addresses -/

theorem Fn.pcOf_mem (hst : f.StructSpec) {k : Nat} (hk : k < f.size) :
    Dom.mem [(f.entry, 4 * f.size)] (f.pcOf k) := by
  have := hst.size
  unfold Dom.mem Fn.pcOf
  simp only [List.any_cons, List.any_nil, Bool.or_false, decide_eq_true_eq]
  have : f.entry + BitVec.ofNat 64 (4 * k) - f.entry = BitVec.ofNat 64 (4 * k) := by bv_omega
  rw [this, BitVec.toNat_ofNat]; omega

theorem zipIdx_map_snd {α : Type} : ∀ (l : List α) (k : Nat),
    (l.zipIdx k).map (·.2) = List.range' k l.length
  | [], _ => rfl
  | a :: l, k => by simp [List.zipIdx_cons, List.range'_succ, zipIdx_map_snd l (k + 1)]

theorem zipIdx_snd_nodup {α : Type} : ∀ (l : List α) (k : Nat), ((l.zipIdx k).map (·.2)).Nodup
  | [], _ => by simp
  | a :: l, k => by
    simp only [List.zipIdx_cons, List.map_cons, List.nodup_cons, List.mem_map]
    refine ⟨fun ⟨p, hp, he⟩ => ?_, zipIdx_snd_nodup l (k + 1)⟩
    have := (List.mem_zipIdx (x := p.1) (i := p.2) (by simpa using hp)).1
    omega

theorem Fn.initTy_caps_mem {c : HCap} (h : c ∈ f.initTy.caps) :
    ∃ i, ∃ hi : i < f.sig.entryCaps.length, c = ⟨f.entryId i, f.sig.entryCaps[i], some i⟩ := by
  simp only [Fn.initTy, List.mem_map] at h
  obtain ⟨⟨b, i⟩, hm, rfl⟩ := h
  obtain ⟨-, hi, hb⟩ := List.mem_zipIdx hm
  refine ⟨i, by omega, ?_⟩
  simp only [hb, Nat.sub_zero]

/-- Theorem A at the entry (T0): the signature's entry conditions give the invariant of the
    entry type. -/
theorem Fn.entry_inv (hst : f.StructSpec) {D : Dom} {a : Val × TokFp} {s0 : State}
    (he : Entry D f.entry s0) (hpre : (f.sig.spec T).pre a s0) :
    Inv f T ((f.sig.spec T).perm a s0) s0 (f.entryVal a.1 s0) f.initTy s0 (f.entryVal a.1 s0) a.2 := by
  obtain ⟨hregs, hp, hvalid, hsep, hstk, hsk⟩ := hpre
  have hpar : ∀ x ∈ f.sig.params, f.entryVal a.1 s0 x = a.1 x := fun x hx => f.entryVal_param hst _ _ hx
  -- capabilities of the entry type are the borrowed and taken ones, under the same valuation
  have hcv : ∀ i (hi : i < f.sig.entryCaps.length), ∀ x ∈ f.sig.entryCaps[i].vars,
      a.1 x = f.entryVal a.1 s0 x := fun i hi x hx =>
    (hpar x (f.entryCap_vars hst _ (List.getElem_mem hi) x hx)).symm
  have hcg := fun i hi => Cap.congr_vars (T := T) (F := a.2) (hcv i hi)
  have hmemE : ∀ i (hi : i < f.sig.entryCaps.length), f.sig.entryCaps[i] ∈ f.sig.entryCaps :=
    fun i hi => List.getElem_mem hi
  refine ⟨?_, ?_, fun _ _ => rfl, ?_, ?_, ?_, ?_, ?_, by simp [Fn.initTy], he.live,
    .inl (by simp [Fn.initTy]), by simp [Fn.initTy], ?_, he.sp, hsk⟩
  · intro p hp'
    simp only [Fn.initTy, List.mem_cons] at hp'
    rcases hp' with rfl | hp'
    · unfold Constr.holds at *
      rwa [Constr.eval_congr _ (fun x hx => (hpar x (hst.pre x hx)))]
    · split at hp'
      · rename_i x hx
        have hx' := lookup_mem hx
        have e := f.entryVal_reg hst a.1 s0 hx'
        have := (s0.reg 2).isLt
        have h16 : (s0.reg 2).toNat % 16 = 0 := he.sp
        have hsk' : f.sig.stack ≤ (s0.reg 2).toNat := hsk
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
        rcases hp' with rfl | rfl | rfl | rfl <;>
          simp only [Constr.holds, Constr.eval, Constr.lt, decide_eq_true_eq, IExpr.eval_var,
            IExpr.eval_lit, IExpr.eval_add, e] <;> omega
      · simp at hp'
  · intro p hp'
    simp only [Fn.initTy, List.mem_append, List.mem_map] at hp'
    rcases hp' with (hp' | ⟨⟨r, x⟩, hrx, rfl⟩) | ⟨r, -, rfl⟩
    · exact (hregs p hp').of_eq (IExpr.eval_congr _ (fun x hx => (hpar x (hst.inRegs p hp' x hx)).symm))
    · exact hasInt_toNat _ _ _ (f.entryVal_reg hst a.1 s0 hrx)
    · exact hasInt_toNat _ _ _ (f.entryVal_entry hst a.1 s0 r)
  · intro c hc
    obtain ⟨i, hi, rfl⟩ := f.initTy_caps_mem hc
    exact ((hcg i hi).2 _).1 (hvalid _ (hmemE i hi))
  · intro c hc d hd hne hex x hx hy
    obtain ⟨i, hi, rfl⟩ := f.initTy_caps_mem hc
    obtain ⟨j, hj, rfl⟩ := f.initTy_caps_mem hd
    have hij : i ≠ j := fun e => hne (by subst e; rfl)
    exact hsep i j hi hj hij hex x (((hcg i hi).1 x).2 hx) (((hcg j hj).1 x).2 hy)
  · intro c hc x hx
    obtain ⟨i, hi, rfl⟩ := f.initTy_caps_mem hc
    exact fun hm => absurd hm (hstk _ (hmemE i hi) x (((hcg i hi).1 x).2 hx))
  · intro c hc x hx
    obtain ⟨i, hi, rfl⟩ := f.initTy_caps_mem hc
    have hx := ((hcg i hi).1 x).2 hx
    obtain ⟨r, hr, hm⟩ := hx
    simp only
    by_cases hex : f.sig.entryCaps[i].exclusive = true
    · have hw : (f.sig.spec T |>.perm a s0).writable x := by
        refine ⟨r, ?_, hm⟩
        simp only [Spec.perm, Sig.spec, Sig.writeRegions, List.mem_append, List.mem_flatMap,
          List.mem_filter]
        exact .inl ⟨_, ⟨hmemE i hi, hex⟩, hr⟩
      exact ⟨Perm.readable_of_writable hw, fun _ => hw⟩
    · refine ⟨⟨r, ?_, hm⟩, fun h => absurd h hex⟩
      simp only [Spec.perm, Sig.spec, Sig.readRegions, List.mem_append, List.mem_flatMap,
        List.mem_filter]
      exact .inl ⟨_, ⟨hmemE i hi, by simpa using hex⟩, hr⟩
  · have : f.initTy.caps.map (·.id) = (f.sig.entryCaps.zipIdx.map (·.2)).map f.entryId := by
      simp only [Fn.initTy, List.map_map]; rfl
    rw [this, zipIdx_map_snd, ← List.range_eq_range']; exact hst.entryIds
  · intro x hx
    exact ⟨_, List.mem_append.2 (.inr (List.mem_singleton_self _)), hx⟩

/-! ## Theorems A–C -/

theorem Fn.instr_spec {c : Code} {k : Nat} {S0 : STy} (hS0 : f.tyAt k = some S0)
    (h : f.instr c k = true) :
    ∃ S i, f.tyAt k = some S ∧ c.instr (f.pcOf k) = some i ∧ f.instrAt k S i = true := by
  unfold Fn.instr at h
  rw [hS0] at h
  generalize hI : c.instr (f.pcOf k) = oi at h
  cases oi with
  | none => cases h
  | some i => exact ⟨S0, i, hS0, rfl, h⟩

theorem Sig.Post_setPc {σ : Sig} {ι : Val} {F : TokFp} {s0 s : State} (pc : Word)
    (h : σ.Post T ι F s0 s) : σ.Post T ι F s0 (s.setPc pc) := by
  obtain ⟨ι', F', h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨ι', F', h1, by simpa [Sig.RegsHave] using h2, h3, by simpa using h4, h5, h6⟩

theorem writesReg_step {P : Perm} {i : Instr} {rd : Reg} (hw : writesReg i = some rd) (s : State) :
    InstrOk P i s ∧ ∃ s', exec i s = some s' := by
  cases i <;> simp_all [writesReg, InstrOk, exec]

/-- A register-writing instruction, then the edge to the next one. -/
theorem Fn.arith_step (hst : f.StructSpec) {c : Code} {P : Perm} {D : Dom} {Q : State → Prop} (rn : Runner c P D Q)
    {s0 : State} {ι0 : Val} {F : TokFp} {k : Nat} {S : STy} {s : State} {ι : Val} {i : Instr}
    (cont : ∀ (S1 : STy) (s' : State) (ι1 : Val) (k' : Nat), s'.pc = f.pcOf k' →
      Inv f T P s0 ι0 S1 s' ι1 F → (∀ y : Nat, y < f.fresh → ι1 y = ι y) →
      f.edge (some k) S1 k' = true → rn.later s')
    (hd : D.mem s.pc) (hI : Inv f T P s0 ι0 S s ι F) (hi : c.instr s.pc = some i)
    (hpc : s.pc = f.pcOf k) (hk : f.arithOk k S i = true) : rn.R s := by
  unfold Fn.arithOk at hk
  cases hw : writesReg i with
  | none => rw [hw] at hk; cases hk
  | some rd =>
    rw [hw] at hk
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hk
    obtain ⟨hrd, hk⟩ := hk
    split at hk
    · rename_i S' ha
      obtain ⟨hok, s', hx⟩ := writesReg_step (P := P) hw s
      obtain ⟨ι', g1, hI', hpc'⟩ := f.arith_sound hst.protFresh hI hw hrd ha hx
      exact rn.exec hd hI.live hi hok hx (rn.later_next _ (cont _ _ ι' (k + 1)
        (by rw [hpc', hpc, f.pcOf_succ]) hI' g1 hk))
    · cases hk

/-- `auipc rd, imm` with its exact address. -/
theorem Fn.auipc_step (hst : f.StructSpec) {c : Code} {P : Perm} {D : Dom} {Q : State → Prop} (rn : Runner c P D Q)
    {s0 : State} {ι0 : Val} {F : TokFp} {k : Nat} {S : STy} {s : State} {ι : Val}
    {rd : Reg} {imm : BitVec 20}
    (cont : ∀ (S1 : STy) (s' : State) (ι1 : Val) (k' : Nat), s'.pc = f.pcOf k' →
      Inv f T P s0 ι0 S1 s' ι1 F → (∀ y : Nat, y < f.fresh → ι1 y = ι y) →
      f.edge (some k) S1 k' = true → rn.later s')
    (hd : D.mem s.pc) (hI : Inv f T P s0 ι0 S s ι F) (hi : c.instr s.pc = some (.auipc rd imm))
    (hpc : s.pc = f.pcOf k) (hk : f.auipcOk k S rd imm = true) : rn.R s := by
  unfold Fn.auipcOk at hk
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hk
  obtain ⟨hrd, hk⟩ := hk
  refine rn.exec' hd hI.live hi trivial ?_
  simp only [exec, Runner.optR_some]
  refine rn.later_next _ <| cont _ _ ι (k + 1) (by simp only [State.setPc_pc]; rw [hpc, f.pcOf_succ])
    (hI.exact hrd ?_ _) (fun _ _ => rfl) hk
  rw [hpc]; unfold HasInt; simp [IExpr.eval_lit]

/-- A tail call (I21 `tail`): the callee returns to this function's caller. -/
theorem Fn.tail_step (hst : f.StructSpec) {c : Code} {D : Dom}
    {a : Val × TokFp} {s0 : State} (he : Entry D f.entry s0)
    (rn : Runner c ((f.sig.spec T).perm a s0) D (fun s => Final D s ∧ (f.sig.spec T).Done a s0 s))
    (hcall : ∀ p ∈ f.callees, aligned p.1 4 ∧ ∃ Dg, rn.callee Dg p.1 (p.2.spec T) ∧ Dg.sub D ∧
      ∀ j < f.size, ¬ Dg.mem (f.pcOf j))
    (hι0r : ∀ r x, (r, x) ∈ f.regVar → f.entryVal a.1 s0 x = (s0.reg r).toNat)
    (hι0p : ∀ x ∈ f.sig.params, f.entryVal a.1 s0 x = a.1 x)
    {S : STy} {s : State} {ι : Val} {rs : Reg} {off : BitVec 12}
    {F : TokFp} (hI : Inv f T ((f.sig.spec T).perm a s0) s0 (f.entryVal a.1 s0) S s ι F)
    (hUF : f.UnitFrame T a s0 F)
    (hd : D.mem s.pc) (hi : c.instr s.pc = some (.jalr 0 rs off)) (hk : f.tailRegOk S rs off = true) :
    rn.R s := by
  unfold Fn.tailRegOk at hk
  cases hr : S.reg rs with
  | none => rw [hr] at hk; cases hk
  | some e =>
  rw [hr] at hk
  simp only [Bool.and_eq_true] at hk
  obtain ⟨hnil, hk⟩ := hk
  have hv : BitVec.ofInt 64 e.const = s.reg rs :=
    ofInt_const_eq (STy.reg_hasInt hI.regs hr) hnil
  rw [hv] at hk
  generalize ht : (s.reg rs + off.signExtend 64) &&& ~~~1 = t at hk
  unfold Fn.tailAt at hk
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
  obtain ⟨⟨⟨⟨⟨hin, hpre⟩, hd0⟩, hgs⟩, hra⟩, hk⟩ := hk
  cases hls : Fn.lends S g θ with
  | none => rw [hls] at hk; cases hk
  | some ls =>
  rw [hls] at hk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
  obtain ⟨⟨⟨⟨hap, htx⟩, huq⟩, hids⟩, hret⟩ := hk
  have hgm := lookup_mem hg
  obtain ⟨hal, Dg, hmeets, hDg, -⟩ := hcall _ hgm
  have hok := Fn.calleeOk_spec (hst.callees _ hgm)
  have hra0 : s.reg 1 = s0.reg 1 := f.kept_reg_sound hI hι0r hra
  have hstk : S.depth + g.stack ≤ f.sig.stack := by omega
  have hs0 : s.setReg 0 (s.pc + 4) = s := by simp [State.setReg]
  have hx : exec (.jalr 0 rs off) s = some (s.setPc t) := by
    simp only [exec, hs0, ht, jumpTo, hal, if_true]
  have hregs1 : ∀ r : Reg, r ≠ 1 → (s.setPc t).reg r = s.reg r := fun r _ => by simp
  have hmem1 : (s.setPc t).mem = s.mem := by simp
  obtain ⟨hpre', hle⟩ := f.callee_pre hst hI hok
    (fun p hp => by have := hin p hp; revert this; cases S.reg p.1 <;> simp) hpre hstk hls hap _
    hregs1 hmem1
  have hspn := hI.sp_toNat hst
  have hra1 : (s.setPc t).reg 1 = s0.reg 1 := by simp [hra0]
  refine rn.call hd hI.live hi trivial hx hmeets (IExpr.upd ι θ, F) ⟨by simp, by simp [hI.live], ?_, ?_, ?_⟩
    hpre' hDg hle ?_
  · rw [hra1]; exact fun hm => he.ret (hDg _ hm)
  · rw [hra1]; exact he.retAligned
  · unfold aligned
    rw [hregs1 2 (by decide), hspn.1]
    have := hI.spAl; have := hspn.2.2; have := hspn.2.1; have := hI.stackLe
    omega
  · intro s2 hdone hfr
    rcases hdone with ⟨hlive, hpc2, hpres, hpost⟩ | ⟨hex, -⟩
    · obtain ⟨ι', F1, -, hI', hUF1⟩ := f.afterCall_inv hst hI hok hθ hstk hls htx huq rfl hι0p hUF hids hregs1 hmem1 hpres
        hlive hpost hfr
      obtain ⟨hkept, hpost'⟩ := f.retOkOn_sound (Fα := a.2) hst hI' hret hι0r hι0p rfl hUF1
      have hpc2' : s2.pc = s0.reg 1 := by rw [hpc2]; exact hra1
      refine rn.done_later _ ⟨.inl (by rw [hpc2']; exact he.ret), .inl ⟨hlive, hpc2', hkept, hpost'⟩⟩
    · exact rn.done_later _ ⟨.inr hex, .inr ⟨hex, trivial⟩⟩

/-- One point of a run, for any kind of run (`Runner`: total or partial): from a point of the
    record whose invariant holds, the instruction there, given that every accepted edge
    continues (`contF`). -/
theorem Fn.runStep (hst : f.StructSpec) {c : Code} (hinstr : ∀ k < f.size, f.instr c k = true)
    {D : Dom} (hDf : ∀ k < f.size, D.mem (f.pcOf k))
    {a : Val × TokFp} {s0 : State} (he : Entry D f.entry s0)
    (rn : Runner c ((f.sig.spec T).perm a s0) D (fun s => Final D s ∧ (f.sig.spec T).Done a s0 s))
    (hcall : ∀ p ∈ f.callees, aligned p.1 4 ∧ ∃ Dg, rn.callee Dg p.1 (p.2.spec T) ∧ Dg.sub D ∧
      ∀ j < f.size, ¬ Dg.mem (f.pcOf j))
    (hι0r : ∀ r x, (r, x) ∈ f.regVar → f.entryVal a.1 s0 x = (s0.reg r).toNat)
    (hι0p : ∀ x ∈ f.sig.params, f.entryVal a.1 s0 x = a.1 x)
    {k : Nat} {ι : Val} {F : TokFp} {S : STy} {s : State}
    (hS : f.tyAt k = some S) (hk : k < f.size) (hpc : s.pc = f.pcOf k)
    (hI : Inv f T ((f.sig.spec T).perm a s0) s0 (f.entryVal a.1 s0) S s ι F)
    (hUF : f.UnitFrame T a s0 F)
    (contF : ∀ (F1 : TokFp) (S1 : STy) (s' : State) (ι1 : Val) (k' : Nat), s'.pc = f.pcOf k' →
      Inv f T ((f.sig.spec T).perm a s0) s0 (f.entryVal a.1 s0) S1 s' ι1 F1 →
      f.UnitFrame T a s0 F1 →
      (∀ y : Nat, y < f.fresh → ι1 y = ι y) → f.edge (some k) S1 k' = true → rn.later s') :
    rn.R s := by
  have cont := fun S1 s' ι1 k' hpc' hI1 hag he' => contF F S1 s' ι1 k' hpc' hI1 hUF hag he'
  have hd : Dom.mem D s.pc := hpc ▸ hDf k hk
  have hprot := hst.protFresh
  obtain ⟨S', i, hS', hci, hk1⟩ := Fn.instr_spec hS (hinstr k hk)
  rw [hS] at hS'; cases hS'
  have hi : c.instr s.pc = some i := hpc ▸ hci
  cases i with
  | branch op rs1 rs2 off =>
    simp only [Fn.instrAt] at hk1
    unfold Fn.branchOk at hk1
    cases ht : Fn.target k off.toInt with
    | none => rw [ht] at hk1; cases hk1
    | some k' =>
    rw [ht] at hk1
    simp only at hk1
    have htgt := f.pcOf_target (by omega) ht
    refine rn.exec' hd hI.live hi trivial ?_
    simp only [exec]
    cases h1 : S.reg rs1 with
    | none =>
      rw [h1] at hk1; simp only [Bool.and_eq_true] at hk1
      split
      · simp only [jumpTo, hpc, htgt, if_pos (f.pcOf_aligned hst k'), Runner.optR_some]
        exact rn.later_next _ <| cont _ _ ι k' (by simp) (hI.setPc _) (fun _ _ => rfl) hk1.1
      · simp only [Runner.optR_some]
        exact rn.later_next _ <| cont _ _ ι (k + 1) (by simp only [State.setPc_pc]; rw [hpc, f.pcOf_succ]) (hI.setPc _) (fun _ _ => rfl) hk1.2
    | some e1 =>
    cases h2 : S.reg rs2 with
    | none =>
      rw [h1, h2] at hk1; simp only [Bool.and_eq_true] at hk1
      split
      · simp only [jumpTo, hpc, htgt, if_pos (f.pcOf_aligned hst k'), Runner.optR_some]
        exact rn.later_next _ <| cont _ _ ι k' (by simp) (hI.setPc _) (fun _ _ => rfl) hk1.1
      · simp only [Runner.optR_some]
        exact rn.later_next _ <| cont _ _ ι (k + 1) (by simp only [State.setPc_pc]; rw [hpc, f.pcOf_succ]) (hI.setPc _) (fun _ _ => rfl) hk1.2
    | some e2 =>
      rw [h1, h2] at hk1; simp only [Bool.and_eq_true] at hk1
      obtain ⟨ι', g1, g2, gt, gf⟩ := f.branch_sound hprot hI h1 h2 op
      split
      · rename_i hb
        simp only [jumpTo, hpc, htgt, if_pos (f.pcOf_aligned hst k'), Runner.optR_some]
        exact rn.later_next _ <| cont _ _ ι' k' (by simp) (((hI.congr g2 (fun y hy => g1 y (hprot y hy))).addFacts
          (gt hb)).setPc _) g1 hk1.1
      · rename_i hb
        simp only [Runner.optR_some]
        exact rn.later_next _ <| cont _ _ ι' (k + 1) (by simp only [State.setPc_pc]; rw [hpc, f.pcOf_succ]) (((hI.congr g2
          (fun y hy => g1 y (hprot y hy))).addFacts (gf (by simpa using hb))).setPc _) g1 hk1.2
  | jal rd off =>
    simp only [Fn.instrAt] at hk1
    by_cases hr1 : rd = 1
    · subst hr1
      simp only [beq_self_eq_true, if_true] at hk1
      exact f.call_step hst rn hI hd hpc hi hk1 hcall rfl hι0p hUF
        (fun s' hx => rn.done_later _ ⟨Or.inr hx, Or.inr ⟨hx, trivial⟩⟩)
        (fun F1 S1 s' ι1 hpc' hI1 hUF1 hag he' => contF F1 S1 s' ι1 (k + 1) hpc' hI1 hUF1 hag he')
    rw [if_neg (by simpa using hr1)] at hk1
    simp only [Bool.and_eq_true, beq_iff_eq] at hk1
    obtain ⟨rfl, hk1⟩ := hk1
    unfold Fn.jalOk at hk1
    cases ht : Fn.target k off.toInt with
    | none => rw [ht] at hk1; cases hk1
    | some k' =>
    rw [ht] at hk1
    simp only at hk1
    have htgt := f.pcOf_target (by omega) ht
    refine rn.exec' hd hI.live hi trivial ?_
    have hs0 : s.setReg 0 (s.pc + 4) = s := by simp [State.setReg]
    simp only [exec, hs0, jumpTo, hpc, htgt, if_pos (f.pcOf_aligned hst k'), Runner.optR_some]
    exact rn.later_next _ <| cont _ _ ι k' (by simp) (hI.setPc _) (fun _ _ => rfl) hk1
  | jalr rd rs1 off =>
    simp only [Fn.instrAt] at hk1
    by_cases hr1 : rd = 1
    · subst hr1
      simp only [beq_self_eq_true, if_true] at hk1
      exact f.callReg_step hst rn hI hd hpc hi hk1 hcall rfl hι0p hUF
        (fun s' hx => rn.done_later _ ⟨Or.inr hx, Or.inr ⟨hx, trivial⟩⟩)
        (fun F1 S1 s' ι1 hpc' hI1 hUF1 hag he' => contF F1 S1 s' ι1 (k + 1) hpc' hI1 hUF1 hag he')
    rw [if_neg (by simpa using hr1)] at hk1
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hk1
    obtain ⟨rfl, hk1⟩ := hk1
    by_cases htl : f.tailRegOk S rs1 off = true
    · exact f.tail_step hst he rn hcall hι0r hι0p hI hUF hd hi htl
    have hk2 := hk1.resolve_right htl
    clear hk1
    obtain ⟨⟨rfl, rfl⟩, hk1⟩ := hk2
    unfold Fn.ret at hk1
    obtain ⟨hkept, hpost⟩ := f.retOk_sound (Fα := a.2) hst hI hk1 hι0r hι0p rfl hUF
    refine rn.exec' hd hI.live hi trivial ?_
    have hs0 : s.setReg 0 (s.pc + 4) = s := by simp [State.setReg]
    have hra : s.reg 1 = s0.reg 1 := hkept 1 (by simp [keptRegs])
    have hal := he.retAligned
    unfold aligned at hal
    have ht : (s0.reg 1 + BitVec.signExtend 64 (0 : BitVec 12)) &&& ~~~1 = s0.reg 1 := by
      have hz : s0.reg 1 + BitVec.signExtend 64 (0 : BitVec 12) = s0.reg 1 := by
        apply BitVec.eq_of_toNat_eq; simp
      rw [hz]; exact and_not_one_of_aligned _ hal
    simp only [exec, hs0, hra, ht, jumpTo, if_pos he.retAligned, Runner.optR_some]
    refine rn.later_next _ (rn.done_later _ ⟨.inl (by simpa using he.ret), .inl ⟨by simpa using hI.live, by simp, ?_, ?_⟩⟩)
    · intro r hr; simpa using hkept r (List.mem_cons_of_mem _ hr)
    · exact Sig.Post_setPc _ hpost
  | load op rd rs off =>
    simp only [Fn.instrAt, Fn.loadOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at hk1
    obtain ⟨hrd, hk1⟩ := hk1
    split at hk1
    · -- a frame slot
      rename_i j hj
      obtain ⟨hok, s', hx, hI', hpc'⟩ := f.slotLoad_sound hst hI hrd hj
      refine rn.exec' hd hI.live hi hok ?_
      rw [hx, Runner.optR_some]
      exact rn.later_next _ <| cont _ _ ι (k + 1) (by rw [hpc', hpc, f.pcOf_succ]) hI' (fun _ _ => rfl) hk1
    · split at hk1
      · rename_i S' hl
        obtain ⟨hok, s', hx, ι', g1, hI', hpc'⟩ := f.load_sound hprot hI hl hrd
        refine rn.exec' hd hI.live hi hok ?_
        rw [hx, Runner.optR_some]
        exact rn.later_next _ <| cont _ _ ι' (k + 1) (by rw [hpc', hpc, f.pcOf_succ]) hI' g1 hk1
      · cases hk1
  | store op rs1 rs2 off =>
    simp only [Fn.instrAt, Fn.storeOk] at hk1
    split at hk1
    · -- a frame slot
      rename_i j hj
      obtain ⟨hok, s', hx, hI', hpc'⟩ := f.slotStore_sound (rs2 := rs2) hst hI hj
      refine rn.exec' hd hI.live hi hok ?_
      rw [hx, Runner.optR_some]
      exact rn.later_next _ <| cont _ _ ι (k + 1) (by rw [hpc', hpc, f.pcOf_succ]) hI' (fun _ _ => rfl) hk1
    · split at hk1
      · rename_i S' hl
        obtain ⟨hok, s', hx, ι', g1, hI', hpc'⟩ := f.store_sound hprot hI hl
        refine rn.exec' hd hI.live hi hok ?_
        rw [hx, Runner.optR_some]
        exact rn.later_next _ <| cont _ _ ι' (k + 1) (by rw [hpc', hpc, f.pcOf_succ]) hI' g1 hk1
      · cases hk1
  | iop op rd rs imm =>
    simp only [Fn.instrAt] at hk1
    split at hk1
    · -- `sp` moves: the prologue or the epilogue
      rename_i hrd2
      simp only [beq_iff_eq] at hrd2; subst hrd2
      unfold Fn.frameOk at hk1
      simp only [Bool.and_eq_true, beq_iff_eq] at hk1
      obtain ⟨⟨hop, hrs⟩, hk1⟩ := hk1
      subst hop; subst hrs
      split at hk1
      · rename_i Fr e hfr he
        split at hk1
        · rename_i hc
          simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc hk1
          obtain ⟨⟨hd0, hF0⟩, himm⟩ := hc
          obtain ⟨⟨⟨hids, h1⟩, h2⟩, hedge⟩ := hk1
          obtain ⟨s', hx, hI', hpc'⟩ := f.framePush_sound (k := k) hst hI hfr hd0 hF0 he himm h1 h2
            (of_decide_eq_true hids)
          refine rn.exec' hd hI.live hi trivial ?_
          rw [hx, Runner.optR_some]
          exact rn.later_next _ <| cont _ _ ι (k + 1) (by rw [hpc', hpc, f.pcOf_succ]) hI' (fun _ _ => rfl) hedge
        · split at hk1
          · rename_i _ hc
            simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc
            obtain ⟨⟨hd1, hF0⟩, himm⟩ := hc
            split at hk1
            · rename_i cs hcs
              simp only [Bool.and_eq_true] at hk1
              obtain ⟨-, hedge⟩ := hk1
              obtain ⟨s', hx, hI', hpc'⟩ := f.framePop_sound hst hI hfr hd1 hF0 he himm hcs
              refine rn.exec' hd hI.live hi trivial ?_
              rw [hx, Runner.optR_some]
              exact rn.later_next _ <| cont _ _ ι (k + 1) (by rw [hpc', hpc, f.pcOf_succ]) hI' (fun _ _ => rfl) hedge
            · cases hk1
          · cases hk1
      · cases hk1
    · exact f.arith_step hst rn cont hd hI hi hpc hk1
  | auipc rd imm =>
    simp only [Fn.instrAt] at hk1
    exact f.auipc_step hst rn cont hd hI hi hpc hk1
  | ecall =>
    simp only [Fn.instrAt] at hk1
    exact f.ecall_step hst rn hI hd hpc hi hk1
      (fun s' hx => rn.done_later _ ⟨Or.inr hx, Or.inr ⟨hx, trivial⟩⟩)
      (fun S1 s' ι1 hpc' hI1 hag he' => cont S1 s' ι1 (k + 1) hpc' hI1 hag he')
  | unimp => simp [Fn.instrAt] at hk1
  | _ =>
    simp only [Fn.instrAt] at hk1
    exact f.arith_step hst rn cont hd hI hi hpc hk1

/-- Theorems A, B and C together, for the instructions of `f`: from any point of the record
    whose invariant holds, every run stays in the function, is allowed by the permission,
    ends, and ends returning with the exit conditions. By well-founded induction on the rank. -/
theorem Fn.run (hst : f.StructSpec) {c : Code} (hinstr : ∀ k < f.size, f.instr c k = true)
    (hp : f.sig.isPartial = false)
    {D : Dom} (hDf : ∀ k < f.size, D.mem (f.pcOf k))
    (hcall : ∀ p ∈ f.callees, aligned p.1 4 ∧ ∃ Dg, Meets c Dg p.1 T p.2 ∧ Dg.sub D ∧
      ∀ j < f.size, ¬ Dg.mem (f.pcOf j))
    {a : Val × TokFp} {s0 : State} (he : Entry D f.entry s0)
    (hι0r : ∀ r x, (r, x) ∈ f.regVar → f.entryVal a.1 s0 x = (s0.reg r).toNat)
    (hι0p : ∀ x ∈ f.sig.params, f.entryVal a.1 s0 x = a.1 x) :
    ∀ p : Nat × Val, ∀ (F : TokFp) S s, f.tyAt p.1 = some S → p.1 < f.size → s.pc = f.pcOf p.1 →
      Inv f T ((f.sig.spec T).perm a s0) s0 (f.entryVal a.1 s0) S s p.2 F →
      f.UnitFrame T a s0 F → Exec c ((f.sig.spec T).perm a s0) D ((f.sig.spec T).Done a s0) s := by
  intro p
  refine WellFounded.induction (C := fun p : Nat × Val => ∀ (F : TokFp) S s, f.tyAt p.1 = some S →
      p.1 < f.size → s.pc = f.pcOf p.1 →
      Inv f T ((f.sig.spec T).perm a s0) s0 (f.entryVal a.1 s0) S s p.2 F →
      f.UnitFrame T a s0 F → Exec c ((f.sig.spec T).perm a s0) D ((f.sig.spec T).Done a s0) s)
    (InvImage.wf (fun p : Nat × Val => f.rank p.1 p.2) LexN.wf) p ?_
  intro p ih
  obtain ⟨k, ι⟩ := p
  intro F S s hS hk hpc hI hUF
  simp only at hS hk hpc hI
  exact f.runStep hst hinstr hDf he (Runner.total _ _ _ _) hcall hι0r hι0p hS hk hpc hI hUF
    (fun F1 S1 s' ι1 k' hpc' hI1 hUF1 hag he' => by
      unfold Fn.edge at he'
      split at he'
      · cases he'
      · rename_i S2 hS2
        obtain ⟨hk', hI2, hrk⟩ := f.edgeOk_sound hst he' hI1 hag
        exact ih (k', _) (hrk hp k rfl) F1 S2 s' hS2 hk' hpc' hI2 hUF1)

/-- A partial run (`partial` signatures, I19): the same dispatch with `n` steps of fuel in
    place of the rank; no measure is needed. -/
theorem Fn.runP (hst : f.StructSpec) {c : Code} (hinstr : ∀ k < f.size, f.instr c k = true)
    {D : Dom} (hDf : ∀ k < f.size, D.mem (f.pcOf k))
    (hcall : ∀ p ∈ f.callees, aligned p.1 4 ∧ ∃ Dg, VerifiedImgP c Dg p.1 (p.2.spec T) ∧ Dg.sub D ∧
      ∀ j < f.size, ¬ Dg.mem (f.pcOf j))
    {a : Val × TokFp} {s0 : State} (he : Entry D f.entry s0)
    (hι0r : ∀ r x, (r, x) ∈ f.regVar → f.entryVal a.1 s0 x = (s0.reg r).toNat)
    (hι0p : ∀ x ∈ f.sig.params, f.entryVal a.1 s0 x = a.1 x) :
    ∀ n (k : Nat) (ι : Val) (F : TokFp) S s, f.tyAt k = some S → k < f.size → s.pc = f.pcOf k →
      Inv f T ((f.sig.spec T).perm a s0) s0 (f.entryVal a.1 s0) S s ι F →
      f.UnitFrame T a s0 F → ReachP c ((f.sig.spec T).perm a s0) D (fun s => Final D s ∧ (f.sig.spec T).Done a s0 s) n s := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro k ι F S s hS hk hpc hI hUF
  cases n with
  | zero => exact .zero
  | succ n =>
  exact f.runStep hst hinstr hDf he (Runner.fuel _ _ _ _ n) hcall hι0r hι0p hS hk hpc hI hUF
    (fun F1 S1 s' ι1 k' hpc' hI1 hUF1 hag he' m hm => by
      unfold Fn.edge at he'
      split at he'
      · cases he'
      · rename_i S2 hS2
        obtain ⟨hk', hI2, -⟩ := f.edgeOk_sound hst he' hI1 hag
        exact ih m (by omega) k' _ F1 S2 s' hS2 hk' hpc' hI2 hUF1)

/-- **Soundness of the Lean checker** (theorems A–C for one function): a function it accepts
    meets its signature (⟦σ⟧, total) on the code image it was checked against, for every
    meaning of tokens, on any domain `D` that holds its code and its callees' (each callee
    verified on its own domain, away from this function's code). -/
theorem Fn.check_sound (f : Fn) (c : Code) (T : TokEnv) (h : f.check c = true)
    (hp : f.sig.isPartial = false) {D : Dom}
    (hDf : ∀ k < f.size, D.mem (f.pcOf k))
    (hcall : ∀ p ∈ f.callees, aligned p.1 4 ∧ ∃ Dg, Meets c Dg p.1 T p.2 ∧ Dg.sub D ∧
      ∀ j < f.size, ¬ Dg.mem (f.pcOf j)) :
    Meets c D f.entry T f.sig := by
  unfold Fn.check at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨hso, hentry⟩, hinstr⟩ := h
  have hst := Fn.structOk_spec hso
  intro a s0 he hpre
  have hI0 := f.entry_inv (T := T) hst he hpre
  unfold Fn.edge at hentry
  split at hentry
  · cases hentry
  · rename_i S0 hS0
    obtain ⟨hk0, hI1, -⟩ := f.edgeOk_sound hst hentry hI0 (ιpre := f.entryVal a.1 s0) (fun _ _ => rfl)
    exact f.run hst hinstr hp hDf hcall he (fun r x h => f.entryVal_reg hst a.1 s0 h)
      (fun x h => f.entryVal_param hst a.1 s0 h) (0, _) a.2 S0 s0 hS0 hk0
      (by simp [Fn.pcOf, he.pc]) hI1 (Fn.unitFrame_entry a s0)

/-- A function with no calls, on its own code. -/
theorem Fn.check_sound_leaf (f : Fn) (c : Code) (T : TokEnv) (h : f.check c = true)
    (hnc : f.callees = []) (hp : f.sig.isPartial = false := by decide) : Meets c [(f.entry, 4 * f.size)] f.entry T f.sig := by
  have hso : f.structOk = true := by
    unfold Fn.check at h; simp only [Bool.and_eq_true] at h; exact h.1.1
  exact f.check_sound c T h hp (fun k hk => f.pcOf_mem (Fn.structOk_spec hso) hk) (by simp [hnc])

/-- **Partial soundness** (I19): a function the checker accepts meets its signature's partial
    meaning (⟦σ⟧ without termination); callees may be partial. -/
theorem Fn.check_soundP (f : Fn) (c : Code) (T : TokEnv) (h : f.check c = true) {D : Dom}
    (hDf : ∀ k < f.size, D.mem (f.pcOf k))
    (hcall : ∀ p ∈ f.callees, aligned p.1 4 ∧ ∃ Dg, MeetsP c Dg p.1 T p.2 ∧ Dg.sub D ∧
      ∀ j < f.size, ¬ Dg.mem (f.pcOf j)) :
    MeetsP c D f.entry T f.sig := by
  unfold Fn.check at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨hso, hentry⟩, hinstr⟩ := h
  have hst := Fn.structOk_spec hso
  intro a s0 he hpre
  have hI0 := f.entry_inv (T := T) hst he hpre
  unfold Fn.edge at hentry
  split at hentry
  · cases hentry
  · rename_i S0 hS0
    obtain ⟨hk0, hI1, -⟩ := f.edgeOk_sound hst hentry hI0 (ιpre := f.entryVal a.1 s0) (fun _ _ => rfl)
    intro n
    exact f.runP hst hinstr hDf hcall he (fun r x h => f.entryVal_reg hst a.1 s0 h)
      (fun x h => f.entryVal_param hst a.1 s0 h) n 0 _ a.2 S0 s0 hS0 hk0
      (by simp [Fn.pcOf, he.pc]) hI1 (Fn.unitFrame_entry a s0)

end NoCompiler.Typed
