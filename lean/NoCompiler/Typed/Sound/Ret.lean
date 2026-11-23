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

theorem Cap.fp_bytes_F {c : Cap} {b : BytesCap} (hk : c.kind = .bytes b) (ι : Val) (F F' : TokFp) :
    c.fp ι F = c.fp ι F' := by
  unfold Cap.fp Cap.regions; rw [hk]

theorem nodup_getElem_inj {α : Type} {l : List α} (h : l.Nodup) {i j : Nat} (hi : i < l.length)
    (hj : j < l.length) (e : l[i] = l[j]) : i = j := by
  induction l generalizing i j with
  | nil => simp at hi
  | cons a r ih =>
    rw [List.nodup_cons] at h
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j => simp at e; exact absurd (e ▸ List.getElem_mem _) h.1
    | succ i =>
      cases j with
      | zero => simp at e; exact absurd (e ▸ List.getElem_mem _) h.1
      | succ j => simp at e; exact congrArg (· + 1) (ih h.2 (by simpa using hi) (by simpa using hj) e)

theorem Borrow.exitCap_fp (b : Borrow) (ι : Val) (F : TokFp) : b.exitCap.fp ι F = b.cap.fp ι F := by
  unfold Borrow.exitCap
  split
  · rename_i x hx
    funext y
    unfold Cap.fp Cap.regions
    simp only [hx]
    rfl
  · rfl

theorem Fn.giveFrom_spec {S : STy} {θ : Subst} : ∀ {gcs : List Cap} {used : List Nat} {hs : List HCap},
    f.giveFrom S θ gcs used = some hs → hs.length = gcs.length ∧
    (∀ j (hj : j < hs.length), hs[j] ∈ S.caps ∧ hs[j].id ∉ used ∧
      (hs[j].origin.any (· < f.sig.borrow.length)) = false ∧ hs[j].cap.exclusive = true ∧
      ∃ hj' : j < gcs.length, S.capSub θ hs[j] { id := hs[j].id, origin := hs[j].origin, cap := gcs[j] } = true) ∧
    (hs.map (·.id)).Nodup
  | [], used, hs, h => by
    simp only [Fn.giveFrom, Option.some.injEq] at h; subst h; simp
  | gc :: gs, used, hs, h => by
    simp only [Fn.giveFrom] at h
    split at h
    · cases h
    · rename_i c hc
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨hs', h', rfl⟩ := h
      obtain ⟨l1, l2, l3⟩ := Fn.giveFrom_spec h'
      have hcm := List.mem_of_find?_eq_some hc
      have hcp := List.find?_some hc
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_iff_mem, decide_eq_true_eq,
        Bool.not_eq_eq_eq_not, Bool.not_true] at hcp
      obtain ⟨⟨⟨hu, ho⟩, hx⟩, hcs⟩ := hcp
      refine ⟨by simp [l1], fun j hj => ?_, ?_⟩
      · cases j with
        | zero => exact ⟨hcm, by simpa using hu, by simpa using ho, hx, by simp, hcs⟩
        | succ j =>
          obtain ⟨a1, a2, a3, a4, hj', a5⟩ := l2 j (by simpa using hj)
          refine ⟨a1, fun hm => a2 (List.mem_cons_of_mem _ hm), a3, a4, by simpa using hj', ?_⟩
          simpa using a5
      · simp only [List.map_cons, List.nodup_cons]
        refine ⟨fun hm => ?_, l3⟩
        obtain ⟨d, hd, e⟩ := List.mem_map.1 hm
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hd
        exact (l2 j hj).2.1 (by rw [e]; exact List.mem_cons_self ..)

theorem Fn.entryCap_vars (hst : f.StructSpec) : ∀ c ∈ f.sig.entryCaps, ∀ x ∈ c.vars,
    x ∈ f.sig.params := by
  intro c hc x hx
  simp only [Sig.entryCaps, List.mem_append, List.mem_map] at hc
  rcases hc with ⟨b, hb, rfl⟩ | hc
  · obtain ⟨hg, hk⟩ := hst.borrowVars b hb
    unfold Cap.vars at hx
    simp only [List.mem_append] at hx
    rcases hx with hx | hx
    · exact hg x hx
    · split at hx
      · rename_i xb hxb; exact (hk xb hxb).1 x (by simpa only [List.mem_append] using hx)
      · simp at hx
  · exact hst.take c hc x hx

/-- Lemma 10 (Q1–Q4), for the registers `rs`. -/
theorem Fn.retOkOn_sound (hst : f.StructSpec) {rs : List Reg} {S : STy} {s : State} {ι : Val}
    {F : TokFp} {θ : Subst}
    (hI : Inv f T P s0 ι0 S s ι F) (hr : f.retOkOn rs S θ = true)
    (hι0r : ∀ r x, (r, x) ∈ f.regVar → ι0 x = (s0.reg r).toNat)
    {ια : Val} {Fα : TokFp} (hι0p : ∀ x ∈ f.sig.params, ι0 x = ια x)
    (hP : P = (f.sig.spec T).perm (ια, Fα) s0) :
    (∀ r ∈ rs, s.reg r = s0.reg r) ∧ f.sig.Post T ια Fα s0 s := by
  unfold Fn.retOkOn at hr
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.contains_iff_mem] at hr
  obtain ⟨⟨⟨⟨hkept, hθ⟩, hsub⟩, hgv⟩, hb⟩ := hr
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
  -- the given capabilities: held ones, distinct, not returned for a borrow
  obtain ⟨hs, hgs, hd0⟩ : ∃ hs : List HCap, f.giveFrom S θ f.sig.give [] = some hs ∧
      (f.sig.give ≠ [] ∨ (∃ b ∈ f.sig.borrow, ∃ t, b.cap.kind = .token t) → S.depth = 0) := by
    simp only [Bool.or_eq_true, List.isEmpty_iff, Bool.and_eq_true, decide_eq_true_eq,
      Option.isSome_iff_exists, List.all_eq_true] at hgv
    rcases hgv with ⟨h, hb⟩ | ⟨h0, hs, h⟩
    · refine ⟨[], by rw [h]; rfl, fun h' => ?_⟩
      rcases h' with h' | ⟨b, hb', t, ht⟩
      · exact absurd h h'
      · have := hb b hb'; rw [ht] at this; simp at this
    · exact ⟨hs, h, fun _ => h0⟩
  obtain ⟨hlen, hgsp, hgnd⟩ := f.giveFrom_spec hgs
  have hvarsP : ∀ y ∈ f.sig.params, ι' y = ια y := by
    intro y hy
    have : y ∉ f.sig.outVars := fun ho => hst.outProt y ho (f.param_prot hy)
    simp [ι', this]
  have hcapG : ∀ j (hj : j < f.sig.give.length), ∃ hj' : j < hs.length,
      (∀ x, f.sig.give[j].fp ι' F x → hs[j].cap.fp ι F x) ∧
      f.sig.give[j].exclusive = hs[j].cap.exclusive ∧
      f.sig.give[j].valid T ι' F s.mem := by
    intro j hj
    have hj' : j < hs.length := hlen ▸ hj
    obtain ⟨hm, -, -, -, _hj, hcs⟩ := hgsp j hj'
    obtain ⟨-, hex, hfp, hv⟩ := STy.capSub_sound (T := T) (F := F) hcs hh
    have hvars : ∀ x ∈ (f.sig.give[j]'hj).vars, IExpr.upd ι θ x = ι' x := fun x hx =>
      hag x ((hst.give _ (List.getElem_mem hj)).2 x hx)
    have hcg := Cap.congr_vars (T := T) (F := F) hvars
    exact ⟨hj', fun x hx => hfp x ((hcg.1 x).2 hx), hex, (hcg.2 _).1 (hv _ (hI.valid _ hm))⟩
  -- which held capability each exit capability comes from
  let Chosen : Nat → HCap → Prop := fun k c =>
    (k < f.sig.borrow.length ∧ c ∈ S.caps ∧ c.origin = some k) ∨
    (f.sig.borrow.length ≤ k ∧ ∃ hj : k - f.sig.borrow.length < hs.length, c = hs[k - f.sig.borrow.length])
  have hchMem : ∀ k c, Chosen k c → c ∈ S.caps := by
    rintro k c (⟨-, hc, -⟩ | ⟨-, hj, rfl⟩)
    · exact hc
    · exact (hgsp _ hj).1
  have hdist : ∀ k l c d, Chosen k c → Chosen l d → k ≠ l → c.id ≠ d.id := by
    rintro k l c d (⟨hk, hc, hoc⟩ | ⟨hk, hj, rfl⟩) (⟨hl, hd, hod⟩ | ⟨hl, hj', rfl⟩) hne e
    · have := eq_of_id_eq hI.ids hc hd e; rw [this, hod] at hoc; cases hoc; exact hne rfl
    · have := eq_of_id_eq hI.ids hc (hgsp _ hj').1 e
      have ho := (hgsp _ hj').2.2.1
      rw [← this, hoc] at ho; simp at ho; omega
    · have := eq_of_id_eq hI.ids (hgsp _ hj).1 hd e
      have ho := (hgsp _ hj).2.2.1
      rw [this, hod] at ho; simp at ho; omega
    · have := nodup_getElem_inj hgnd (by simpa using hj) (by simpa using hj') (by simpa using e)
      omega
  have hexitLen : f.sig.exitCaps.length = f.sig.borrow.length + f.sig.give.length := by
    simp [Sig.exitCaps]
  have hcapE : ∀ k (hk : k < f.sig.exitCaps.length), ∃ c, Chosen k c ∧
      (∀ x, f.sig.exitCaps[k].fp ι' F x → c.cap.fp ι F x) ∧
      f.sig.exitCaps[k].exclusive = c.cap.exclusive ∧
      f.sig.exitCaps[k].valid T ι' F s.mem := by
    intro k hk
    by_cases hkb : k < f.sig.borrow.length
    · obtain ⟨c, hc, ho, hfp, hex, hv⟩ := hcap k hkb
      have e : f.sig.exitCaps[k] = f.sig.borrow[k].exitCap := by
        simp only [Sig.exitCaps]; rw [List.getElem_append_left (by simpa using hkb)]; simp
      rw [e]; exact ⟨c, .inl ⟨hkb, hc, ho⟩, hfp, hex, hv⟩
    · have hj : k - f.sig.borrow.length < f.sig.give.length := by omega
      obtain ⟨hj', hfp, hex, hv⟩ := hcapG _ hj
      have e : f.sig.exitCaps[k] = f.sig.give[k - f.sig.borrow.length] := by
        simp only [Sig.exitCaps]; rw [List.getElem_append_right (by simpa using hkb)]; simp
      rw [e]; exact ⟨_, .inr ⟨by omega, hj', rfl⟩, hfp, hex, hv⟩
  refine ⟨ι', F, fun x hx => by simp [ι', hx], ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    exact (hS'.regs p hp).of_eq (IExpr.eval_congr _ (fun x hx => hag x (hst.outRegs p hp x hx)))
  · have := hS'.facts f.sig.post (by simp)
    unfold Constr.holds at *
    rwa [Constr.eval_congr _ (fun x hx => hag x (hst.post x hx))] at this
  · intro c hc
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hc
    obtain ⟨_, _, _, _, hv⟩ := hcapE k hk
    exact hv
  · intro i j hi hj hne hex x hx hy
    obtain ⟨ci, hci, hfi, hei, -⟩ := hcapE i hi
    obtain ⟨cj, hcj, hfj, -, -⟩ := hcapE j hj
    exact hI.sep ci (hchMem _ _ hci) cj (hchMem _ _ hcj) (hdist _ _ _ _ hci hcj hne) (hei ▸ hex) x
      (hfi x hx) (hfj x hy)
  · -- the Pool: a returned token or given capability lies in the taken ones or borrowed tokens
    have hpoolOf : ∀ k d, Chosen k d → d.cap.exclusive = true →
        (∀ i (hi : i < f.sig.borrow.length), (∃ y, f.sig.borrow[i].cap.kind = .bytes y) → i ≠ k) →
        S.depth = 0 → ∀ x, d.cap.fp ι F x → Sig.pool f.sig ια Fα x := by
      intro k d hdc hdx hbk hz x hxd
      have hdm := hchMem _ _ hdc
      obtain ⟨r, hr, hm⟩ := (hI.perm d hdm x hxd).1
      rw [hP] at hr
      simp only [Spec.perm, Sig.spec, Sig.readRegions, Sig.writeRegions, List.mem_append,
        List.mem_flatMap, List.mem_filter, List.mem_singleton] at hr
      -- the region is an entry capability's, or the stack
      have hent : ∀ e ∈ f.sig.entryCaps, r ∈ e.regions ια Fα → Sig.pool f.sig ια Fα x := by
        intro e he hre
        simp only [Sig.entryCaps, List.mem_append, List.mem_map] at he
        rcases he with ⟨b, hb, rfl⟩ | he
        · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
          cases hkb : f.sig.borrow[i].cap.kind with
          | token t =>
            exact .inr ⟨_, hb, by simp [hkb], r, hre, hm⟩
          | bytes y =>
            exfalso
            obtain ⟨ci, hci, hoi, hfi, -, -⟩ := hcap i hi
            have hci' : Chosen i ci := .inl ⟨hi, hci, hoi⟩
            have hne : i ≠ k := hbk i hi ⟨y, hkb⟩
            have hbx : f.sig.borrow[i].exitCap.fp ι' F x := by
              rw [Borrow.exitCap_fp, Cap.fp_bytes_F hkb ι' F Fα]
              have hv : ∀ y ∈ f.sig.borrow[i].cap.vars, ια y = ι' y := fun y hy =>
                (hvarsP y (f.entryCap_vars hst _ (by unfold Sig.entryCaps; exact List.mem_append.2 (.inl (List.mem_map.2 ⟨_, List.getElem_mem hi, rfl⟩))) y hy)).symm
              rw [← ((Cap.congr_vars (T := T) (F := Fα) hv).1 x)]
              exact ⟨r, hre, hm⟩
            exact hI.sep d hdm ci hci (hdist _ _ _ _ hdc hci' (Ne.symm hne)) hdx x hxd (hfi x hbx)
        · exact .inl ⟨e, he, r, hre, hm⟩
      rcases hr with ⟨e, ⟨he, -⟩, hre⟩ | ⟨e, ⟨he, -⟩, hre⟩ | rfl
      · exact hent e he hre
      · exact hent e he hre
      · exfalso
        have hin := hI.stack d hdm x hxd hm
        obtain ⟨-, -, -, hd0', -⟩ := hin
        exact hd0' hz
    intro c hc x hx
    simp only [Sig.fresh, List.mem_append, List.mem_filter, List.mem_map] at hc
    rcases hc with ⟨⟨b, hb', rfl⟩, ht⟩ | hc
    · -- a borrowed token, returned by the held capability with its origin
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb'
      cases hkb : f.sig.borrow[i].cap.kind with
      | bytes y => simp [hkb] at ht
      | token t =>
        obtain ⟨ci, hci, hoi, hfi, hei, -⟩ := hcap i hi
        have hex : ci.cap.exclusive = true := by
          rw [← hei]; simp [Borrow.exitCap, Cap.exclusive, hkb]
        refine hpoolOf i ci (.inl ⟨hi, hci, hoi⟩) hex (fun i' hi' ⟨y, hy⟩ e => ?_)
          (hd0 (.inr ⟨_, hb', t, hkb⟩)) x (hfi x (by rw [Borrow.exitCap_fp]; exact hx))
        subst e; rw [hkb] at hy; cases hy
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
    have hk : f.sig.borrow.length + j < f.sig.exitCaps.length := by omega
    obtain ⟨d, hdc, hfd, hed, -⟩ := hcapE _ hk
    have e : f.sig.exitCaps[f.sig.borrow.length + j] = f.sig.give[j] := by
      simp only [Sig.exitCaps]; rw [List.getElem_append_right (by simp)]; simp
    rw [e] at hfd hed
    have hdx : d.cap.exclusive = true := by rw [← hed]; exact (hst.give _ hc).1
    exact hpoolOf _ d hdc hdx (fun i hi _ => by omega) (hd0 (.inl (List.ne_nil_of_mem hc))) x (hfd x hx)

theorem Fn.retOk_sound (hst : f.StructSpec) {S : STy} {s : State} {ι : Val} {F : TokFp} {θ : Subst}
    (hI : Inv f T P s0 ι0 S s ι F) (hr : f.retOk S θ = true)
    (hι0r : ∀ r x, (r, x) ∈ f.regVar → ι0 x = (s0.reg r).toNat)
    {ια : Val} {Fα : TokFp} (hι0p : ∀ x ∈ f.sig.params, ι0 x = ια x)
    (hP : P = (f.sig.spec T).perm (ια, Fα) s0) :
    (∀ r ∈ keptRegs, s.reg r = s0.reg r) ∧ f.sig.Post T ια Fα s0 s :=
  f.retOkOn_sound hst hI hr hι0r hι0p hP

end NoCompiler.Typed
