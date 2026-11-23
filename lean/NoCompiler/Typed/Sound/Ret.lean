import NoCompiler.Typed.Sound.Edge

/-
Lemma 10 (return): the return check gives the exit conditions Q1–Q4 of ⟦σ⟧.
-/
namespace NoCompiler.Typed

variable {f : Fn} {T : TokEnv} {P : Perm} {s0 : State} {ι0 : Val}

theorem and_not_one_of_aligned (x : Word) (h : x.toNat % 4 = 0) : x &&& ~~~1#64 = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
  by_cases h0 : i = 0
  · subst h0
    simp [BitVec.getLsbD, Nat.testBit, Nat.shiftRight_zero]
    omega
  · simp [BitVec.getLsbD_one, h0]

/-- The variables a capability mentions. -/
def Cap.vars (c : Cap) : List Var :=
  c.guard.vars ++ match c.kind with
    | .bytes b => b.base.vars ++ b.len.vars ++ b.fields.flatMap (·.ty.vars)
    | .token _ => []

/-- A capability's meaning depends only on the variables it mentions. -/
theorem Cap.congr_vars {ι ι' : Val} {F : TokFp} {c : Cap} (h : ∀ x ∈ c.vars, ι x = ι' x) :
    (∀ x, c.fp ι F x ↔ c.fp ι' F x) ∧ (∀ m, c.valid T ι F m ↔ c.valid T ι' F m) := by
  have hg : c.guard.eval ι = c.guard.eval ι' :=
    Constr.eval_congr _ (fun x hx => h x (by simp [Cap.vars, hx]))
  cases hk : c.kind with
  | token t =>
    refine ⟨fun x => ?_, fun m => ?_⟩
    · simp [Cap.fp, Cap.regions, hk, hg]
    · simp [Cap.valid, hk, Constr.holds, hg]
  | bytes b =>
    have hv : ∀ x, x ∈ b.base.vars ++ b.len.vars ++ b.fields.flatMap (·.ty.vars) → ι x = ι' x := by
      intro x hx; apply h; simp only [Cap.vars, hk, List.mem_append]; exact .inr (by simpa only [List.mem_append] using hx)
    have hb := IExpr.eval_congr b.base (fun x hx => hv x (by simp [hx]))
    have hl := IExpr.eval_congr b.len (fun x hx => hv x (by simp [hx]))
    have hf : ∀ fd ∈ b.fields, ∀ x ∈ fd.ty.vars, ι x = ι' x := by
      intro fd hfd x hx; apply hv
      simp only [List.mem_append, List.mem_flatMap]; exact .inr ⟨fd, hfd, hx⟩
    refine ⟨fun x => ?_, fun m => ?_⟩
    · simp [Cap.fp, Cap.regions, hk, hg, BytesCap.region, hb, hl]
    · simp only [Cap.valid, hk, Constr.holds, hg, hb, hl]
      constructor
      · intro hv' hg'
        obtain ⟨a, b', c', d⟩ := hv' hg'
        refine ⟨a, b', c', fun fd hfd => ?_⟩
        obtain ⟨e1, e2, e3⟩ := d fd hfd
        refine ⟨by simpa [Cap.Field.holds, hl] using e1, by simpa [hb] using e2, ?_⟩
        rw [← hb]; exact e3.of_eq (IExpr.eval_congr _ (hf fd hfd))
      · intro hv' hg'
        obtain ⟨a, b', c', d⟩ := hv' hg'
        refine ⟨a, b', c', fun fd hfd => ?_⟩
        obtain ⟨e1, e2, e3⟩ := d fd hfd
        refine ⟨by simpa [Cap.Field.holds, hl] using e1, by simpa [hb] using e2, ?_⟩
        rw [hb]; exact e3.of_eq (IExpr.eval_congr _ (hf fd hfd)).symm

theorem mem_zipIdx_of {α : Type} {l : List α} {i : Nat} (h : i < l.length) : (l[i], i) ∈ l.zipIdx :=
  List.mem_zipIdx_iff_getElem?.2 (by simp [h])

theorem Fn.regVar_prot {r : Reg} {x : Var} (h : (r, x) ∈ f.regVar) : x ∈ f.protectedVars := by
  unfold Fn.protectedVars; exact List.mem_append.2 (.inr (List.mem_map.2 ⟨_, h, rfl⟩))

theorem Fn.param_prot {x : Var} (h : x ∈ f.sig.params) : x ∈ f.protectedVars := by
  unfold Fn.protectedVars; exact List.mem_append.2 (.inl h)

/-- A register whose type is its entry variable holds its entry value. -/
theorem Fn.kept_reg_sound {S : STy} {s : State} {ι : Val} {F : TokFp}
    (hI : Inv f T P s0 ι0 S s ι F) (hι0r : ∀ r x, (r, x) ∈ f.regVar → ι0 x = (s0.reg r).toNat)
    {r : Reg} (h : (match S.reg r, f.regVar.lookup r with
      | some e, some x => S.entEqMod e (.var x)
      | _, _ => false) = true) : s.reg r = s0.reg r := by
  split at h
  · rename_i e x he hx
    have h1 := STy.reg_hasInt hI.regs he
    have h2 := STy.entEqMod_sound h hI.hyps
    have h3 : HasInt ι (s.reg r) (.var x) := h1.congr h2
    have hxm := lookup_mem hx
    have h4 : HasInt ι (s0.reg r) (.var x) := by
      refine hasInt_toNat _ _ _ ?_
      rw [hI.prot x (f.regVar_prot hxm), hι0r r x hxm]
    exact h3.word_eq h4
  · cases h

/-- Lemma 10 (Q1–Q4), for the registers `rs`. -/
theorem Fn.retOkOn_sound (hst : f.StructSpec) {rs : List Reg} {S : STy} {s : State} {ι : Val}
    {F : TokFp} {θ : Subst}
    (hI : Inv f T P s0 ι0 S s ι F) (hr : f.retOkOn rs S θ = true)
    (hι0r : ∀ r x, (r, x) ∈ f.regVar → ι0 x = (s0.reg r).toNat)
    {ια : Val} {Fα : TokFp} (hι0p : ∀ x ∈ f.sig.params, ι0 x = ια x) :
    (∀ r ∈ rs, s.reg r = s0.reg r) ∧ f.sig.Post T ια Fα s0 s := by
  unfold Fn.retOkOn at hr
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.contains_iff_mem] at hr
  obtain ⟨⟨⟨hkept, hθ⟩, hsub⟩, hb⟩ := hr
  have hh := hI.hyps
  refine ⟨fun r hr => f.kept_reg_sound hI hι0r (hkept r hr), ?_⟩
  -- the exit valuation
  have hprot' : ∀ p ∈ θ, p.1 ∉ f.protectedVars := fun p hp => hst.outProt _ (hθ p hp)
  have hS' := hI.sub (S' := { regs := f.sig.outRegs, facts := [f.sig.post] }) hsub hprot'
  let ι' : Val := fun y => if y ∈ f.sig.outVars then IExpr.upd ι θ y else ια y
  have hag : ∀ y, y ∈ f.sig.params ∨ y ∈ f.sig.outVars → IExpr.upd ι θ y = ι' y := by
    intro y hy
    by_cases ho : y ∈ f.sig.outVars
    · simp [ι', ho]
    · simp only [ι', ho, if_false]
      have hp : y ∈ f.sig.params := hy.resolve_right ho
      rw [upd_of_not_mem (fun p hp' e => ho (by rw [← e]; exact hθ p hp')), hI.prot y (f.param_prot hp), hι0p y hp]
  -- the borrowed capabilities come back
  have hcap : ∀ i (h : i < f.sig.borrow.length), ∃ c ∈ S.caps, c.origin = some i ∧
      (∀ x, f.sig.borrow[i].exitCap.fp ι' F x → c.cap.fp ι F x) ∧
      f.sig.borrow[i].exitCap.exclusive = c.cap.exclusive ∧
      f.sig.borrow[i].exitCap.valid T ι' F s.mem := by
    intro i hi
    obtain ⟨c, hc, ho⟩ := hb _ (mem_zipIdx_of hi)
    simp only [Bool.and_eq_true, beq_iff_eq] at ho
    obtain ⟨ho, hcs⟩ := ho
    obtain ⟨-, hex, hfp, hv⟩ := STy.capSub_sound (T := T) (F := F) hcs hh
    have hvars : ∀ x ∈ f.sig.borrow[i].exitCap.vars, IExpr.upd ι θ x = ι' x := by
      intro x hx; apply hag
      obtain ⟨hg, hk⟩ := hst.borrowVars _ (List.getElem_mem hi)
      unfold Borrow.exitCap Cap.vars at hx
      split at hx
      · rename_i xb hxb
        obtain ⟨h1, h2⟩ := hk xb hxb
        simp only [List.mem_append] at hx
        rcases hx with hx | (hx | hx) | hx
        · exact .inl (hg x hx)
        · exact .inl (h1 x (by simp [hx]))
        · exact .inl (h1 x (by simp [hx]))
        · exact h2 x hx
      · rename_i t ht
        simp only [ht, List.append_nil] at hx
        exact .inl (hg x hx)
    have hcg := Cap.congr_vars (T := T) (F := F) hvars
    refine ⟨c, hc, ho, fun x hx => hfp x ((hcg.1 x).2 hx), hex, (hcg.2 _).1 (hv _ (hI.valid c hc))⟩
  have hexit : f.sig.exitCaps = f.sig.borrow.map Borrow.exitCap := by
    simp [Sig.exitCaps, hst.give]
  refine ⟨ι', F, fun x hx => by simp [ι', hx], ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    exact (hS'.regs p hp).of_eq (IExpr.eval_congr _ (fun x hx => hag x (hst.outRegs p hp x hx)))
  · have := hS'.facts f.sig.post (by simp)
    unfold Constr.holds at *
    rwa [Constr.eval_congr _ (fun x hx => hag x (hst.post x hx))] at this
  · rw [hexit]; intro c hc
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
    simp only [List.getElem_map]
    obtain ⟨_, _, _, _, _, hv⟩ := hcap i (by simpa using hi)
    exact hv
  · rw [hexit]
    intro i j hi hj hne hex x hx hy
    simp only [List.length_map] at hi hj
    simp only [List.getElem_map] at hex hx hy
    obtain ⟨ci, hci, hoi, hfi, hei, -⟩ := hcap i hi
    obtain ⟨cj, hcj, hoj, hfj, -, -⟩ := hcap j hj
    have hid : ci.id ≠ cj.id := fun e => hne (by
      have := eq_of_id_eq hI.ids hci hcj e; rw [this] at hoi; rw [hoi] at hoj; simpa using hoj)
    exact hI.sep ci hci cj hcj hid (hei ▸ hex) x (hfi x hx) (hfj x hy)
  · intro c hc
    simp only [Sig.fresh, hst.give, List.append_nil, List.mem_filter, List.mem_map] at hc
    obtain ⟨⟨b, hb', rfl⟩, ht⟩ := hc
    obtain ⟨x, hx⟩ := hst.borrowBytes b hb'
    simp [hx] at ht

theorem Fn.retOk_sound (hst : f.StructSpec) {S : STy} {s : State} {ι : Val} {F : TokFp} {θ : Subst}
    (hI : Inv f T P s0 ι0 S s ι F) (hr : f.retOk S θ = true)
    (hι0r : ∀ r x, (r, x) ∈ f.regVar → ι0 x = (s0.reg r).toNat)
    {ια : Val} {Fα : TokFp} (hι0p : ∀ x ∈ f.sig.params, ι0 x = ια x) :
    (∀ r ∈ keptRegs, s.reg r = s0.reg r) ∧ f.sig.Post T ια Fα s0 s :=
  f.retOkOn_sound hst hI hr hι0r hι0p

end NoCompiler.Typed
