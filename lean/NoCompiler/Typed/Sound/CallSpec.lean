import NoCompiler.Typed.Sound.Frame

/-
Calls (Lemma 8): what the call rule's checks say: callee signatures, lent clauses, their ranges.
-/
namespace NoCompiler.Typed

variable {f : Fn} {T : TokEnv} {P : Perm} {s0 : State} {ι0 : Val}

theorem Fn.lendFrom_spec {S : STy} {b : BytesCap} {c : HCap} (h : Fn.lendFrom S b = some c) :
    c ∈ S.caps ∧ S.ent c.cap.guard = true ∧ ∃ hb, c.cap.kind = .bytes hb ∧
      (b.mode = .ro ∨ hb.mode = .rw) ∧
      S.ent (.and (.le hb.base b.base) (.and (.le (b.base.add b.len) (hb.base.add hb.len))
        (.le (.lit 0) b.len))) = true := by
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [Bool.and_eq_true] at hp
  obtain ⟨hg, hk⟩ := hp
  split at hk
  · rename_i hb hkb
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hk
    exact ⟨hm, hg, hb, hkb, hk.1.1, hk.1.2⟩
  · cases hk

/-- A `heap` clause is lent from a held `heap` capability with the same range. -/
theorem Fn.lendFrom_heap {S : STy} {b : BytesCap} {c : HCap} (h : Fn.lendFrom S b = some c)
    (hh : b.heap = true) : ∃ hb, c.cap.kind = .bytes hb ∧ hb.heap = true ∧
      S.ent (.and (.eq hb.base b.base) (.eq hb.len b.len)) = true := by
  have hp := List.find?_some h
  simp only [Bool.and_eq_true] at hp
  obtain ⟨-, hk⟩ := hp
  split at hk
  · rename_i hb hkb
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', hh] at hk
    obtain ⟨-, hk⟩ := hk
    rcases hk with h | ⟨h1, h2⟩
    · cases h
    · exact ⟨hb, hkb, h1, h2⟩
  · cases hk

/-- What `calleeOk` says about a callee's signature. -/
structure CalleeSpec (g : Sig) : Prop where
  params : g.params.Nodup
  clauses : ∀ c ∈ g.entryCaps, c.guard = .tt
  tokNodup : g.tokNames.Nodup
  inRegs : ∀ p ∈ g.inRegs, p.1 ≠ 1
  outRegs : ∀ p ∈ g.outRegs, p.1 ∉ preservedRegs
  inScoped : ∀ p ∈ g.inRegs, ∀ x ∈ p.2.vars, x ∈ g.params
  preScoped : ∀ x ∈ g.pre.vars, x ∈ g.params
  outScoped : ∀ p ∈ g.outRegs, ∀ x ∈ p.2.vars, x ∈ g.params ∨ x ∈ g.outVars
  postScoped : ∀ x ∈ g.post.vars, x ∈ g.params ∨ x ∈ g.outVars
  outNodup : g.outVars.Nodup
  outApart : ∀ y ∈ g.outVars, y ∉ g.params
  takeScoped : ∀ c ∈ g.take, ∀ y ∈ c.vars, y ∈ g.params
  giveKind : ∀ c ∈ g.give, (∃ x, c.kind = .bytes x ∧ x.fields = [] ∧ (x.heap = true → heapTok ∈ g.tokNames)) ∨
    ∃ t, c.kind = .token t
  giveScoped : ∀ c ∈ g.give, ∀ y ∈ c.vars, y ∈ g.params ∨ y ∈ g.outVars

theorem Fn.calleeOk_spec {g : Sig} (h : Fn.calleeOk g = true) : CalleeSpec g := by
  unfold Fn.calleeOk Fn.Sig.scoped at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.isEmpty_iff, beq_iff_eq, decide_eq_true_eq,
    Bool.or_eq_true, List.contains_iff_mem, Bool.not_eq_true', bne_iff_ne, ne_eq] at h
  simp only [and_assoc] at h
  obtain ⟨hin, hpre, -, hout, hpost, hond, hoap, hpnd, hcl, htn, hir, hor, htk, hgv⟩ := h
  refine ⟨hpnd, hcl, htn, hir, fun p hp => by simpa using hor p hp, hin, hpre, hout, hpost,
    hond, fun y hy => by simpa using hoap y hy, fun c hc y hy => by simpa using htk c hc y hy, ?_,
    fun c hc y hy => by simpa using (hgv c hc).2 y hy⟩
  · intro c hc
    obtain ⟨hk, -⟩ := hgv c hc
    split at hk
    · rename_i x hx
      simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.isEmpty_iff,
        List.contains_iff_mem] at hk
      refine .inl ⟨x, hx, hk.1, fun hh => ?_⟩
      rcases hk.2 with h | h
      · rw [hh] at h; cases h
      · exact h
    · rename_i t ht; exact .inr ⟨t, ht⟩

theorem Fn.lends_spec {S : STy} {g : Sig} {θ : Subst} {ls : List (BytesCap × HCap)}
    (h : Fn.lends S g θ = some ls) : ls.length = g.entryCaps.length ∧
      ∀ i (hi : i < g.entryCaps.length) (hl : i < ls.length),
        (∃ x, g.entryCaps[i].kind = .bytes x ∧
          ls[i].1 = { x with base := x.base.subst θ, len := x.len.subst θ } ∧
          Fn.lendFrom S ls[i].1 = some ls[i].2) ∨
        (∃ t, g.entryCaps[i].kind = .token t ∧ ls[i].1 = Fn.tokSlot ∧ Fn.lendTok S t = some ls[i].2) := by
  obtain ⟨hlen, hget⟩ := mapM_some h
  refine ⟨hlen, fun i hi hl => ?_⟩
  have := hget i hi hl
  split at this
  · rename_i x hx
    left
    dsimp only at this
    cases hc : Fn.lendFrom S { x with base := x.base.subst θ, len := x.len.subst θ } with
    | none => rw [hc] at this; cases this
    | some c =>
      rw [hc] at this
      dsimp only [Option.bind] at this
      split at this
      · simp only [Option.some.injEq] at this
        rw [← this]
        exact ⟨x, hx, rfl, hc⟩
      · cases this
  · rename_i t ht
    right
    simp only [Option.map_eq_some_iff] at this
    obtain ⟨c, hc, he⟩ := this
    rw [← he]
    exact ⟨t, ht, rfl, hc⟩

theorem Fn.lends_fields {S : STy} {g : Sig} {θ : Subst} {ls : List (BytesCap × HCap)}
    (h : Fn.lends S g θ = some ls) (i : Nat) (hi : i < g.entryCaps.length) (hl : i < ls.length) :
    Fn.fieldsLent S θ ls[i].1 ls[i].2 = true := by
  obtain ⟨-, hget⟩ := mapM_some h
  have := hget i hi hl
  split at this
  · rename_i x hx
    dsimp only at this
    cases hc : Fn.lendFrom S { x with base := x.base.subst θ, len := x.len.subst θ } with
    | none => rw [hc] at this; cases this
    | some c =>
      rw [hc] at this
      dsimp only [Option.bind] at this
      split at this
      · rename_i hf
        simp only [Option.some.injEq] at this
        rw [← this]; exact hf
      · cases this
  · simp only [Option.map_eq_some_iff] at this
    obtain ⟨c, -, he⟩ := this
    rw [← he]; rfl

/-- A lent clause's range lies in the held capability's, and is a valid range. -/
theorem lend_region {T : TokEnv} {ι : Val} {F : TokFp} {S : STy} {b : BytesCap} {c : HCap} {m : Word → Byte}
    (hh : ∀ p ∈ S.hyps, p.holds ι) (hv : c.cap.valid T ι F m) (hl : Fn.lendFrom S b = some c) :
    ∃ hb, c.cap.kind = .bytes hb ∧ (b.mode = .ro ∨ hb.mode = .rw) ∧ c.cap.guard.eval ι = true ∧
      0 ≤ b.base.eval ι ∧ 0 ≤ b.len.eval ι ∧ b.base.eval ι + b.len.eval ι ≤ 2 ^ 64 ∧
      ∀ x, (b.region ι).mem x → c.cap.fp ι F x := by
  obtain ⟨-, hg, hb, hk, hmode, hin⟩ := Fn.lendFrom_spec hl
  have hg := STy.ent_sound hg hh
  have hin := STy.ent_sound hin hh
  simp only [Constr.holds, Constr.eval, Bool.and_eq_true, decide_eq_true_eq, IExpr.eval_add,
    IExpr.eval_lit] at hin
  have hv := hv hg
  rw [hk] at hv
  obtain ⟨v0, v1, v2, -⟩ := hv
  have hg' : c.cap.guard.eval ι = true := hg
  refine ⟨hb, hk, hmode, hg', by omega, by omega, by omega, fun x hx => ?_⟩
  unfold Cap.fp Cap.regions
  rw [if_pos hg', hk]
  refine ⟨_, List.mem_singleton_self _, ?_⟩
  rw [region_mem_iff (by omega) (by omega) (by omega)] at hx
  rw [region_mem_iff v0 v1 v2]
  omega

/-- `sp` inside the function: its value and alignment. -/
theorem Inv.sp_toNat (hst : f.StructSpec) {S : STy} {s : State} {ι : Val} {Ft : TokFp}
    (hI : Inv f T P s0 ι0 S s ι Ft) :
    (s.reg Reg.sp).toNat = (s0.reg Reg.sp).toNat - S.depth ∧ S.depth ≤ f.sig.stack ∧
      S.depth % 16 = 0 := by
  have hK := hI.stackLe
  have hdep : S.depth ≤ f.sig.stack ∧ S.depth % 16 = 0 := by
    rcases hI.depth with h | ⟨Fr, hfr, hd, -⟩
    · rw [h]; omega
    · have hg := f.frame_geom hst.frameDecl hfr
      rw [hd]; exact ⟨hg.sizeLe, hg.size16⟩
  refine ⟨?_, hdep⟩
  rw [hI.sp]
  have := below_sp_toNat (s0.reg Reg.sp) S.depth 0 (by omega) (by have := (s0.reg Reg.sp).isLt; omega)
  simpa using this

/-- No held capability meets a callee's stack region (it lies below the caller's `sp`). -/
theorem Fn.caps_miss_stack (hst : f.StructSpec) {S : STy} {s : State} {ι : Val} {Ft : TokFp}
    (hI : Inv f T P s0 ι0 S s ι Ft) {s1 : State} (hregs : ∀ r : Reg, r ≠ 1 → s1.reg r = s.reg r)
    {n : Nat} (hstk : S.depth + n ≤ f.sig.stack) :
    ∀ c ∈ S.caps, ∀ x, c.cap.fp ι Ft x → ¬ (Spec.stackRegion s1 n).mem x := by
  have hspn := hI.sp_toNat hst
  have hK := hI.stackLe
  have hsp1 : (s1.reg Reg.sp).toNat = (s0.reg Reg.sp).toNat - S.depth := by
    rw [hregs _ (by decide)]; exact hspn.1
  intro c hc x hx hm
  rw [stack_mem_iff s1 n (by omega) x, hsp1] at hm
  have h0 : (Spec.stackRegion s0 f.sig.stack).mem x := (stack_mem_iff s0 _ hK x).2 ⟨by omega, by omega⟩
  obtain ⟨Fr, hfr, hd, hF0, -⟩ := hI.stack c hc x hx h0
  have hg := f.frame_geom hst.frameDecl hfr
  have hF0' : Fr.size ≠ 0 := hd ▸ hF0
  have h2 := (inFrame_iff hfr hF0' s0 (by have := hg.sizeLe; omega) hg.addr x).1
    (by rw [← hd]; exact hI.stack c hc x hx h0)
  rw [← hd] at h2
  omega

/-- The clause `i` of a callee, as a capability under the callee's valuation, has the footprint
    of its instantiated range, which lies in the held capability it is lent from. -/
theorem clause_fp {ι : Val} {F : TokFp} {S : STy} {g : Sig} {θ : Subst}
    {ls : List (BytesCap × HCap)} (hok : CalleeSpec g) (hls : Fn.lends S g θ = some ls)
    {i : Nat} (hi : i < g.entryCaps.length) (hl : i < ls.length) {xb0 : BytesCap}
    (hk0 : g.entryCaps[i].kind = .bytes xb0) (x : Word) :
    g.entryCaps[i].fp (IExpr.upd ι θ) F x ↔ (ls[i].1.region ι).mem x := by
  obtain ⟨-, hget⟩ := Fn.lends_spec hls
  obtain ⟨xb, hk, he, -⟩ := (hget i hi hl).resolve_right (fun ⟨t, ht, _⟩ => by rw [hk0] at ht; cases ht)
  have hg := hok.clauses _ (List.getElem_mem hi)
  unfold Cap.fp Cap.regions
  rw [hg, he, hk]
  simp [Constr.eval, BytesCap.region]

theorem Fn.lendTok_spec {S : STy} {t : String} {c : HCap} (h : Fn.lendTok S t = some c) :
    c ∈ S.caps ∧ c.cap.kind = .token t ∧ c.cap.guard = .tt := by
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  exact ⟨hm, hp.1, hp.2⟩

/-- A token clause is lent from the held token of the same name. -/
theorem Fn.lends_tok {S : STy} {g : Sig} {θ : Subst} {ls : List (BytesCap × HCap)}
    (h : Fn.lends S g θ = some ls) (i : Nat) (hi : i < g.entryCaps.length) (hl : i < ls.length)
    {t : String} (ht : g.entryCaps[i].kind = .token t) :
    ls[i].1 = Fn.tokSlot ∧ Fn.lendTok S t = some ls[i].2 := by
  obtain ⟨-, hget⟩ := mapM_some h
  have := hget i hi hl
  rw [ht] at this
  simp only [Option.map_eq_some_iff] at this
  obtain ⟨c, hc, he⟩ := this
  rw [← he]; exact ⟨rfl, hc⟩

/-- A token's footprint is its name's regions under `F`, when unguarded. -/
theorem Cap.fp_token {c : Cap} {t : String} (hk : c.kind = .token t) (hg : c.guard = .tt)
    (ι : Val) (F : TokFp) (x : Word) : c.fp ι F x ↔ ∃ r ∈ F t, r.mem x := by
  unfold Cap.fp Cap.regions
  rw [hg, hk]; simp [Constr.eval]

/-- A clause's footprint at the callee lies in the held capability's it is lent from. -/
theorem clause_sub {T : TokEnv} {ι : Val} {F : TokFp} {S : STy} {g : Sig} {θ : Subst}
    {ls : List (BytesCap × HCap)} (hok : CalleeSpec g) (hls : Fn.lends S g θ = some ls)
    {m : Word → Byte} (hh : ∀ p ∈ S.hyps, p.holds ι) (hv : ∀ c ∈ S.caps, c.cap.valid T ι F m)
    {i : Nat} (hi : i < g.entryCaps.length) (hl : i < ls.length) (x : Word) :
    g.entryCaps[i].fp (IExpr.upd ι θ) F x → ls[i].2.cap.fp ι F x := by
  intro hx
  have hgt := hok.clauses _ (List.getElem_mem hi)
  cases hk : g.entryCaps[i].kind with
  | token t =>
    obtain ⟨-, hc⟩ := Fn.lends_tok hls i hi hl hk
    obtain ⟨-, hkc, hgc⟩ := Fn.lendTok_spec hc
    exact (Cap.fp_token hkc hgc ι F x).2 ((Cap.fp_token hk hgt _ F x).1 hx)
  | bytes xb =>
    obtain ⟨-, hget⟩ := Fn.lends_spec hls
    rcases hget i hi hl with ⟨xb', hk', -, hlf⟩ | ⟨t, hkt, -⟩
    · obtain ⟨hm, -⟩ := Fn.lendFrom_spec hlf
      obtain ⟨-, -, -, -, -, -, -, hfp⟩ := lend_region hh (hv _ hm) hlf
      exact hfp x ((clause_fp hok hls hi hl hk x).1 hx)
    · rw [hk] at hkt; cases hkt

end NoCompiler.Typed
