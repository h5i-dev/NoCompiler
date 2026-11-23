import NoCompiler.Typed.Sound.Rename
import NoCompiler.Typed.Sound.CallTok
import NoCompiler.Typed.Sound.CallCaps

/-
Lemma 8.3: when the callee returns, the type after the call holds.
-/
namespace NoCompiler.Typed

variable {f : Fn} {T : TokEnv} {P : Perm} {s0 : State} {ι0 : Val}

/-- Lemma 8.3: when the callee returns, the type after the call holds, with the callee's
    footprints for the tokens lent to it. -/
theorem Fn.afterCall_inv (hst : f.StructSpec) {S : STy} {s : State} {ι : Val} {Ft : TokFp}
    (hI : Inv f T P s0 ι0 S s ι Ft) {g : Sig} (hok : CalleeSpec g) {θ : Subst}
    (hθ : Fn.callInst S g = some θ) (hstk : S.depth + g.stack ≤ f.sig.stack)
    {ls : List (BytesCap × HCap)} (hls : Fn.lends S g θ = some ls)
    (htx : (ls.drop g.borrow.length).all (·.2.cap.exclusive) = true)
    (huniq : ∀ t ∈ g.tokNames, (S.caps.filter fun c => c.cap.kind == .token t).length = 1)
    {ids : List Nat} (hids : ((f.afterCall S g θ ls ids).caps.map (·.id)).Nodup)
    {s1 s2 : State} (hregs : ∀ r : Reg, r ≠ 1 → s1.reg r = s.reg r) (hmem : s1.mem = s.mem)
    (hpres : Preserved s1 s2) (hlive : s2.exit = none)
    (hpost : g.Post T (IExpr.upd ι θ) Ft s1 s2)
    (hframe : ∀ x, ¬ ((g.spec T).perm (IExpr.upd ι θ, Ft) s1).writable x → s2.mem x = s1.mem x) :
    ∃ ι' F1, (∀ y : Nat, y < f.fresh → ι' y = ι y) ∧
      Inv f T P s0 ι0 (f.afterCall S g θ ls ids) s2 ι' F1 := by
  obtain ⟨ιg', Fg', hag, hregs', hpost', hgval, hgsep, hgpool⟩ := hpost
  obtain ⟨hθ1, hθ2⟩ := Fn.callInst_spec hθ
  have hh := hI.hyps
  obtain ⟨hlen, hget⟩ := Fn.lends_spec hls
  let x := f.freshAt S
  have hx : S.maxVar < x := f.freshAt_gt S
  let extra : List Int := (List.finRange 32).map fun r => ((s2.reg r).toNat : Int)
  let ι' := setFrom ι x (g.outVars.map ιg' ++ extra)
  obtain ⟨g1, g2, g3⟩ := setFrom_fresh hst.protFresh S ι (g.outVars.map ιg' ++ extra)
  have hupd := upd_rename (ι := ι) (ιg' := ιg') (extra := extra) hθ1 hθ2 hok hx (fun y hy => hag y hy)
  let F1 := callF g Ft Fg'
  let ρ : Subst := θ ++ g.outVars.zipIdx.map fun (p : Var × Nat) => (p.1, IExpr.var (x + p.2))
  let base := S.caps.foldr (fun (c : HCap) m => max (c.id + 1) m) 0
  have hkept := fun {c0 : HCap} (hc0 : c0 ∈ S.caps) hnt =>
    f.kept_cap hst hI hok hstk hls hregs hmem hframe (ι' := ι') g1 hc0 hnt
  have hexitLen : g.exitCaps.length = g.borrow.length + g.give.length := by simp [Sig.exitCaps]
  -- the exit capabilities: a borrow's (a token's is its clause), a given one
  have hEb : ∀ i (hi : i < g.borrow.length), g.exitCaps[i]'(by omega) = g.borrow[i].exitCap := by
    intro i hi; simp only [Sig.exitCaps]; rw [List.getElem_append_left (by simpa using hi)]; simp
  have hEg : ∀ j (hj : j < g.give.length), g.exitCaps[g.borrow.length + j]'(by omega) = g.give[j] := by
    intro j hj; simp only [Sig.exitCaps]; rw [List.getElem_append_right (by simp)]; simp
  have hEnt : ∀ i (hi : i < g.borrow.length), g.entryCaps[i]'(by simp only [Sig.entryCaps, List.length_append, List.length_map]; omega) = g.borrow[i].cap := by
    intro i hi; simp only [Sig.entryCaps]; rw [List.getElem_append_left (by simpa using hi)]; simp
  -- what the callee returns fresh lies in a held capability that went to it
  let Gone : HCap → Prop := fun h => h.id ∈ Fn.takenIds g ls ∨ ∃ t, h.cap.kind = .token t ∧ t ∈ g.tokNames
  have hfreshGone : ∀ e ∈ g.fresh, ∀ z, e.fp ιg' Fg' z →
      ∃ h ∈ S.caps, Gone h ∧ h.cap.exclusive = true ∧ h.cap.fp ι Ft z := by
    intro e he z hz
    obtain ⟨i, hl, hm, hex, hfz, hor⟩ := f.fresh_in hI hok hls htx hgpool he hz
    refine ⟨_, hm, ?_, hex, hfz⟩
    rcases hor with hb | ht
    · left
      have hd : ls[i] ∈ ls.drop g.borrow.length := by
        rw [List.mem_iff_getElem]
        refine ⟨i - g.borrow.length, by simp; omega, ?_⟩
        rw [List.getElem_drop]; simp only [Nat.add_sub_cancel' hb]
      exact List.mem_map.2 ⟨_, hd, rfl⟩
    · exact .inr ht
  -- a kept token lent to the callee: the clause it went to is a borrow
  have hlentTok : ∀ c0 ∈ S.caps, c0.id ∉ Fn.takenIds g ls → ∀ t, c0.cap.kind = .token t →
      t ∈ g.tokNames → ∃ i, ∃ hi : i < g.borrow.length, g.borrow[i].cap.kind = .token t ∧ c0.cap.guard = .tt := by
    intro c0 hc0 hnt t hk ht
    obtain ⟨i, hi, hki⟩ := Sig.mem_tokNames ht
    have hl : i < ls.length := by omega
    obtain ⟨e, hg0⟩ := Fn.lent_holder hls huniq hi hl hki hc0 hk
    by_cases hib : i < g.borrow.length
    · exact ⟨i, hib, by rw [← hEnt i hib]; exact hki, hg0⟩
    · exfalso
      apply hnt
      have hd : ls[i] ∈ ls.drop g.borrow.length := by
        rw [List.mem_iff_getElem]
        refine ⟨i - g.borrow.length, by simp; omega, ?_⟩
        rw [List.getElem_drop]; simp only [Nat.add_sub_cancel' (by omega : g.borrow.length ≤ i)]
      exact List.mem_map.2 ⟨_, hd, by rw [e]⟩
  -- the given capabilities
  have hgFp : ∀ j (hj : j < g.give.length) z,
      ((g.give[j]).subst ρ).fp ι' F1 z ↔ g.give[j].fp ιg' Fg' z := by
    intro j hj z
    obtain ⟨xb, hk, -⟩ := hok.giveBytes _ (List.getElem_mem hj)
    rw [Cap.subst_fp hk _ _ _ Fg']
    exact (Cap.congr_vars (T := T) (F := Fg')
      (fun y hy => hupd y (hok.giveScoped _ (List.getElem_mem hj) y hy))).1 z
  have hgValid : ∀ j (hj : j < g.give.length), ((g.give[j]).subst ρ).valid T ι' F1 s2.mem := by
    intro j hj
    obtain ⟨xb, hk, hf0⟩ := hok.giveBytes _ (List.getElem_mem hj)
    rw [Cap.subst_valid hk hf0 _ _ _ Fg']
    refine (((Cap.congr_vars (T := T) (F := Fg')
      (fun y hy => hupd y (hok.giveScoped _ (List.getElem_mem hj) y hy))).2 _).2 ?_)
    exact hgval _ (by simp [Sig.exitCaps, List.getElem_mem hj])
  -- a lent token's footprint and validity after the call: the callee's
  have htokFp : ∀ c0 ∈ S.caps, ∀ t, c0.cap.kind = .token t → c0.cap.guard = .tt → t ∈ g.tokNames →
      ∀ i (hi : i < g.borrow.length), g.borrow[i].cap.kind = .token t → ∀ z,
        c0.cap.fp ι' F1 z ↔ (g.exitCaps[i]'(by omega)).fp ιg' Fg' z := by
    intro c0 hc0 t hk hg0 ht i hi hbk z
    have hgi : g.borrow[i].cap.guard = .tt :=
      hok.clauses _ (by unfold Sig.entryCaps; exact List.mem_append.2 (.inl (List.mem_map.2 ⟨_, List.getElem_mem hi, rfl⟩)))
    rw [hEb i hi, Borrow.exitCap_fp, Cap.fp_token hk hg0, Cap.fp_token hbk hgi]
    simp [F1, callF, ht]
  have htokValid : ∀ c0 ∈ S.caps, ∀ t, c0.cap.kind = .token t → t ∈ g.tokNames →
      ∀ i (hi : i < g.borrow.length), g.borrow[i].cap.kind = .token t → c0.cap.valid T ι' F1 s2.mem := by
    intro c0 hc0 t hk ht i hi hbk
    have hv := hgval _ (List.getElem_mem (by omega : i < g.exitCaps.length))
    rw [hEb i hi] at hv
    unfold Cap.valid at hv ⊢
    simp only [Borrow.exitCap, hbk] at hv
    rw [hk]; intro _
    have hgi : g.borrow[i].cap.guard = .tt :=
      hok.clauses _ (by unfold Sig.entryCaps; exact List.mem_append.2 (.inl (List.mem_map.2 ⟨_, List.getElem_mem hi, rfl⟩)))
    have := hv (by rw [hgi]; rfl)
    simpa [F1, callF, ht] using this
  have hcaps' : ∀ c ∈ (f.afterCall S g θ ls ids).caps,
      (∃ c0 ∈ S.caps, c0.id ∉ Fn.takenIds g ls ∧ c = Fn.clearLent ls c0) ∨
      (∃ j, ∃ hj : j < g.give.length, c.id = ids.getD j (base + j) ∧ c.cap = (g.give[j]).subst ρ) := by
    intro c hc
    simp only [Fn.afterCall, List.mem_append, List.mem_map, List.mem_filter, Bool.not_eq_true',
      List.contains_iff_mem] at hc
    rcases hc with ⟨c0, ⟨hc0, hn⟩, rfl⟩ | ⟨⟨gc, j⟩, hm, rfl⟩
    · left
      refine ⟨c0, hc0, fun h => ?_, rfl⟩
      simp [List.elem_iff, h] at hn
    · right
      obtain ⟨-, hj, hgj⟩ := List.mem_zipIdx hm
      refine ⟨j, by simpa using hj, rfl, ?_⟩
      simp only [hgj, Nat.sub_zero]
      rfl
  -- the classification for `caps_after`
  let R : Nat → HCap → Prop := fun k c =>
    (∃ hk : k < g.borrow.length, c ∈ S.caps ∧ c.id ∉ Fn.takenIds g ls ∧ ∃ t, c.cap.kind = .token t ∧
      g.borrow[k].cap.kind = .token t) ∨
    (∃ j, k = g.borrow.length + j ∧ ∃ hj : j < g.give.length, c.id = ids.getD j (base + j) ∧
      c.cap = (g.give[j]).subst ρ)
  have hcls : ∀ c ∈ (f.afterCall S g θ ls ids).caps,
      (∃ c0 ∈ S.caps, ¬ Gone c0 ∧ OldCap ι ι' Ft F1 c0 c) ∨
        ∃ k, R k c ∧ NewCap ι' F1 g.exitCaps ιg' Fg' k c := by
    intro c hc
    rcases hcaps' c hc with ⟨c0, hc0, hnt, rfl⟩ | ⟨j, hj, hid, hcj⟩
    · by_cases hlt : ∃ t, c0.cap.kind = .token t ∧ t ∈ g.tokNames
      · obtain ⟨t, hk, ht⟩ := hlt
        obtain ⟨i, hi, hbk, hg0⟩ := hlentTok c0 hc0 hnt t hk ht
        right
        rw [Fn.clearLent_token hk]
        refine ⟨i, .inl ⟨hi, hc0, hnt, t, hk, hbk⟩, by rw [hexitLen]; omega, ?_,
          htokFp c0 hc0 t hk hg0 ht i hi hbk⟩
        rw [hEb i hi]; simp [Cap.exclusive, Borrow.exitCap, hk, hbk]
      · left
        obtain ⟨i1, e1, f1, -⟩ := hkept hc0 hlt
        refine ⟨c0, hc0, fun hg => ?_, i1, e1, fun z => ?_⟩
        · rcases hg with hg | hg
          · exact hnt hg
          · exact hlt hg
        · rw [← f1 z]
          refine Cap.fp_F_congr (fun t hk => ?_) ι' z
          have : t ∉ g.tokNames := fun ht => hlt ⟨t, Fn.clearLent_kind hk, ht⟩
          simp [F1, callF, this]
    · right
      refine ⟨g.borrow.length + j, .inr ⟨j, rfl, hj, hid, hcj⟩, by rw [hexitLen]; omega, ?_, fun z => ?_⟩
      · rw [hcj, hEg j hj, Cap.subst_exclusive]
      · rw [hcj, hEg j hj]; exact hgFp j hj z
  have hin : ∀ c ∈ (f.afterCall S g θ ls ids).caps, ∀ k, R k c → ∀ z, c.cap.fp ι' F1 z →
      ∃ h ∈ S.caps, Gone h ∧ h.cap.exclusive = true ∧ h.cap.fp ι Ft z := by
    intro c hc k hk z hz
    rcases hk with ⟨hkb, hc0, hnt, t, hk0, hbk⟩ | ⟨j, rfl, hj, -, hcj⟩
    · have ht : t ∈ g.tokNames := Sig.tokNames_of (i := k) (by simp only [Sig.entryCaps, List.length_append, List.length_map]; omega)
        (by rw [hEnt k hkb]; exact hbk)
      obtain ⟨i, hi, -, hg0⟩ := hlentTok c hc0 hnt t hk0 ht
      have hz' := (htokFp c hc0 t hk0 hg0 ht k hkb hbk z).1 hz
      refine hfreshGone _ ?_ z hz'
      rw [hEb k hkb]
      simp only [Sig.fresh, Borrow.exitCap, hbk, List.mem_append, List.mem_filter, List.mem_map]
      exact .inl ⟨⟨_, List.getElem_mem hkb, rfl⟩, by simp [hbk]⟩
    · rw [hcj] at hz
      refine hfreshGone _ (by simp [Sig.fresh, List.getElem_mem hj]) z ((hgFp j hj z).1 hz)
  have hdist : ∀ c ∈ (f.afterCall S g θ ls ids).caps, ∀ d ∈ (f.afterCall S g θ ls ids).caps,
      c.id ≠ d.id → ∀ k l, R k c → R l d → k ≠ l := by
    intro c hc d hd hne k l hk hl e
    subst e
    rcases hk with ⟨hkb, hc0, -, t, hk0, hbk⟩ | ⟨j, hkj, hj, hidc, -⟩ <;>
      rcases hl with ⟨_hl, hd0, -, t', hk1, hbk'⟩ | ⟨j', hkj', hj', hidd, -⟩
    · rw [hbk] at hbk'; cases hbk'
      have ht : t ∈ g.tokNames := Sig.tokNames_of (i := k) (by simp only [Sig.entryCaps, List.length_append, List.length_map]; omega)
        (by rw [hEnt k hkb]; exact hbk)
      exact hne (by rw [holder_unique (huniq t ht) hc0 hd0 hk0 hk1])
    · omega
    · omega
    · have : j = j' := by omega
      subst this
      exact hne (by rw [hidc, hidd])
  obtain ⟨hsep', hstk', hperm'⟩ := caps_after hI Gone R hcls hin hgsep hdist
  refine ⟨ι', F1, g3, ?_, ?_, fun z hz => (g2 z hz).trans (hI.prot z hz), ?_, hsep', hstk', hperm',
    hids, ?_, hlive, hI.depth, ?_, hI.stackW, hI.spAl, hI.stackLe⟩
  · -- facts: the callee's exit constraint, and the old facts
    intro p hp
    simp only [Fn.afterCall, List.mem_cons] at hp
    rcases hp with rfl | hp
    · unfold Constr.holds
      rw [Constr.eval_subst, Constr.eval_congr _ (fun y hy => hupd y (hok.postScoped y hy))]
      exact hpost'
    · exact (Constr.holds_congr (fun z hz => (g1 z (Nat.le_trans hz (STy.le_maxVar_fact hp))).symm)).1
        (hI.facts p hp)
  · -- registers: the preserved ones, and the `out` ones
    intro p hp
    simp only [Fn.afterCall, List.mem_append, List.mem_filter, List.mem_map,
      List.contains_iff_mem] at hp
    rcases hp with (⟨hp, hpr⟩ | ⟨q, hq, rfl⟩) | ⟨r, -, rfl⟩
    · have hr1 : p.1 ≠ 1 := by intro e; rw [e] at hpr; simp [preservedRegs] at hpr
      rw [hpres p.1 (by simpa using hpr), hregs _ hr1]
      exact (hI.regs p hp).of_eq (IExpr.eval_congr_max
        (fun z hz => (g1 z (Nat.le_trans hz (STy.le_maxVar_reg hp))).symm))
    · refine (hregs' q hq).of_eq ?_
      rw [IExpr.eval_subst, IExpr.eval_congr _ (fun y hy => hupd y (hok.outScoped q hq y hy))]
    · -- a clobbered register: its own fresh variable
      refine hasInt_toNat _ _ _ ?_
      show setFrom ι x (g.outVars.map ιg' ++ extra) (x + g.outVars.length + r.val) = _
      have := r.isLt
      rw [Nat.add_assoc, setFrom_at _ (by simp [extra] <;> omega)]
      rw [List.getElem?_append_right (by simp)]
      simp [extra]
  · intro c hc
    rcases hcaps' c hc with ⟨c0, hc0, hnt, rfl⟩ | ⟨j, hj, -, hcj⟩
    · by_cases hlt : ∃ t, c0.cap.kind = .token t ∧ t ∈ g.tokNames
      · obtain ⟨t, hk, ht⟩ := hlt
        obtain ⟨i, hi, hbk, -⟩ := hlentTok c0 hc0 hnt t hk ht
        rw [Fn.clearLent_token hk]
        exact htokValid c0 hc0 t hk ht i hi hbk
      · refine (Cap.valid_F_congr (fun t hk => ?_) ι' s2.mem).1 (hkept hc0 hlt).2.2.2
        have : t ∉ g.tokNames := fun ht => hlt ⟨t, Fn.clearLent_kind hk, ht⟩
        simp [F1, callF, this]
    · rw [hcj]; exact hgValid j hj
  · simp only [Fn.afterCall]
    rw [hpres 2 (by simp [preservedRegs]), hregs _ (by decide)]; exact hI.sp
  · -- slots: not written
    intro p hp
    obtain ⟨h1, hb, h2⟩ := hI.slots p hp
    refine ⟨h1, hb, ?_⟩
    have hrd : read64 s2.mem (s0.reg Reg.sp - BitVec.ofNat 64 S.depth + BitVec.ofNat 64 p.1) =
        read64 s.mem (s0.reg Reg.sp - BitVec.ofNat 64 S.depth + BitVec.ofNat 64 p.1) := by
      refine congrArg (BitVec.ofNat 64) (readLE_congr fun i hi => ?_)
      rw [← hmem]
      refine hframe _ fun hzw => ?_
      rcases f.callee_writes hst hI hok hstk hls hregs _ hzw with ⟨j, hj, -, hfp, hm, -⟩ | ⟨hlt, -⟩
      · exact (hb i hi).2 (hI.stack _ hm _ hfp (hb i hi).1)
      · obtain ⟨Fr, hfr, hd, hj'⟩ := h1
        have hg := f.frame_geom hst.frameDecl hfr
        have hsl := hg.slot _ hj'
        have hle := hg.sizeLe
        have e : s0.reg Reg.sp - BitVec.ofNat 64 S.depth + BitVec.ofNat 64 p.1 + BitVec.ofNat 64 i =
            s0.reg Reg.sp - BitVec.ofNat 64 S.depth + BitVec.ofNat 64 (p.1 + i) := by
          rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp
        rw [e, below_sp_toNat (s0.reg Reg.sp) S.depth (p.1 + i) (by omega)
          (by have := (s0.reg Reg.sp).isLt; omega)] at hlt
        omega
    show HasInt ι' (read64 s2.mem (s0.reg Reg.sp - BitVec.ofNat 64 S.depth + BitVec.ofNat 64 p.1)) p.2
    rw [hrd]
    exact h2.of_eq (IExpr.eval_congr_max
      (fun z hz => (g1 z (Nat.le_trans hz (STy.le_maxVar_slot hp))).symm))

end NoCompiler.Typed
