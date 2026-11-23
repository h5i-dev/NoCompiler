import NoCompiler.Typed.Sound.Frame

/-
Lemma 8 (calls): a call the checker accepts enters the callee in a state its signature
admits, with a smaller permission; when the callee returns, the type after the call holds.
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
    exact ⟨hm, hg, hb, hkb, hk.1, hk.2⟩
  · cases hk

/-- What `calleeOk` says about a callee's signature. -/
structure CalleeSpec (g : Sig) : Prop where
  take : g.take = []
  give : g.give = []
  params : g.params.Nodup
  borrow : ∀ b ∈ g.borrow, b.cap.guard = .tt ∧ ∃ x, b.cap.kind = .bytes x ∧ x.fields = []
  inRegs : ∀ p ∈ g.inRegs, p.1 ≠ 1
  outRegs : ∀ p ∈ g.outRegs, p.1 ∉ preservedRegs
  inScoped : ∀ p ∈ g.inRegs, ∀ x ∈ p.2.vars, x ∈ g.params
  preScoped : ∀ x ∈ g.pre.vars, x ∈ g.params
  borrowScoped : ∀ b ∈ g.borrow, ∀ x, b.cap.kind = .bytes x →
    ∀ y ∈ x.base.vars ++ x.len.vars, y ∈ g.params
  outScoped : ∀ p ∈ g.outRegs, ∀ x ∈ p.2.vars, x ∈ g.params ∨ x ∈ g.outVars
  postScoped : ∀ x ∈ g.post.vars, x ∈ g.params ∨ x ∈ g.outVars
  outNodup : g.outVars.Nodup
  outApart : ∀ y ∈ g.outVars, y ∉ g.params

theorem Fn.calleeOk_spec {g : Sig} (h : Fn.calleeOk g = true) : CalleeSpec g := by
  unfold Fn.calleeOk Fn.Sig.scoped at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.isEmpty_iff, beq_iff_eq, decide_eq_true_eq,
    Bool.or_eq_true, List.contains_iff_mem, Bool.not_eq_true', bne_iff_ne, ne_eq] at h
  simp only [and_assoc] at h
  obtain ⟨hin, hpre, hbor, hout, hpost, hond, hoap, htake, hgive, hpnd, hbb, hir, hor⟩ := h
  refine ⟨htake, hgive, hpnd, ?_, hir, fun p hp => by simpa using hor p hp, hin, hpre, ?_, hout, hpost,
    hond, fun y hy => by simpa using hoap y hy⟩
  · intro b hb
    obtain ⟨hg, hk⟩ := hbb b hb
    refine ⟨hg, ?_⟩
    split at hk
    · rename_i x hx; exact ⟨x, hx, by simpa using hk⟩
    · cases hk
  · intro b hb x hx y hy
    have := (hbor b hb).2
    rw [hx] at this
    simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at this
    exact this.1 y (by simp only [List.mem_append] at hy ⊢; rcases hy with h | h <;> simp [h])

theorem Fn.lends_spec {S : STy} {g : Sig} {θ : Subst} {ls : List (BytesCap × HCap)}
    (h : Fn.lends S g θ = some ls) : ls.length = g.borrow.length ∧
      ∀ i (hi : i < g.borrow.length) (hl : i < ls.length), ∃ x, g.borrow[i].cap.kind = .bytes x ∧
        ls[i].1 = { x with base := x.base.subst θ, len := x.len.subst θ } ∧
        Fn.lendFrom S ls[i].1 = some ls[i].2 := by
  obtain ⟨hlen, hget⟩ := mapM_some h
  refine ⟨hlen, fun i hi hl => ?_⟩
  have := hget i hi hl
  split at this
  · rename_i x hx
    simp only [Option.map_eq_some_iff] at this
    obtain ⟨c, hc, he⟩ := this
    rw [← he]
    exact ⟨x, hx, rfl, hc⟩
  · cases this

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

/-- The clause `i` of a callee, as a capability under the callee's valuation, has the footprint
    of its instantiated range, which lies in the held capability it is lent from. -/
theorem clause_fp {ι : Val} {F : TokFp} {S : STy} {g : Sig} {θ : Subst}
    {ls : List (BytesCap × HCap)} (hok : CalleeSpec g) (hls : Fn.lends S g θ = some ls)
    {i : Nat} (hi : i < g.borrow.length) (hl : i < ls.length) (x : Word) :
    g.borrow[i].cap.fp (IExpr.upd ι θ) F x ↔ (ls[i].1.region ι).mem x := by
  obtain ⟨-, hget⟩ := Fn.lends_spec hls
  obtain ⟨xb, hk, he, -⟩ := hget i hi hl
  have hg := (hok.borrow _ (List.getElem_mem hi)).1
  unfold Cap.fp Cap.regions
  rw [hg, he, hk]
  simp [Constr.eval, BytesCap.region]

/-- The callee's entry conditions (Lemma 8.1) and its permission (8.2), at the state after
    `jal ra`. -/
theorem Fn.callee_pre (hst : f.StructSpec) {S : STy} {s : State} {ι : Val} {Ft : TokFp}
    (hI : Inv f T P s0 ι0 S s ι Ft) {g : Sig} (hok : CalleeSpec g) {θ : Subst}
    (hin : ∀ p ∈ g.inRegs, match S.reg p.1 with
      | some e => S.entEqMod e (p.2.subst θ) = true
      | none => False)
    (hpre : S.ent (g.pre.subst θ) = true) (hstk : S.depth + g.stack ≤ f.sig.stack)
    {ls : List (BytesCap × HCap)} (hls : Fn.lends S g θ = some ls) (hap : Fn.lendsApart S ls = true)
    (s1 : State) (hregs : ∀ r : Reg, r ≠ 1 → s1.reg r = s.reg r) (hmem : s1.mem = s.mem) :
    (g.spec T).pre (IExpr.upd ι θ, Ft) s1 ∧ ((g.spec T).perm (IExpr.upd ι θ, Ft) s1).le P := by
  have hh := hI.hyps
  obtain ⟨hlen, hget⟩ := Fn.lends_spec hls
  have hentry : g.entryCaps = g.borrow.map (·.cap) := by simp [Sig.entryCaps, hok.take]
  have hspn := hI.sp_toNat hst
  have hsp1 : (s1.reg Reg.sp).toNat = (s0.reg Reg.sp).toNat - S.depth := by
    rw [hregs _ (by decide)]; exact hspn.1
  have hK := hI.stackLe
  -- clause i: its footprint is its instantiated range, inside the held capability
  have hcl : ∀ i (hi : i < g.borrow.length), ∃ hl : i < ls.length,
      (∀ x, g.borrow[i].cap.fp (IExpr.upd ι θ) Ft x → ls[i].2.cap.fp ι Ft x) ∧
      ls[i].2 ∈ S.caps ∧
      (g.borrow[i].cap.exclusive = true → ls[i].2.cap.exclusive = true) ∧
      (∃ x, g.borrow[i].cap.kind = .bytes x ∧ x.fields = [] ∧
        0 ≤ (x.base.subst θ).eval ι ∧ 0 ≤ (x.len.subst θ).eval ι ∧
        (x.base.subst θ).eval ι + (x.len.subst θ).eval ι ≤ 2 ^ 64) := by
    intro i hi
    have hl : i < ls.length := by omega
    obtain ⟨xb, hk, he, hlf⟩ := hget i hi hl
    obtain ⟨hm, -⟩ := Fn.lendFrom_spec hlf
    obtain ⟨hb, hkb, hmode, -, r0, r1, r2, hfp⟩ := lend_region hh (hI.valid _ hm) hlf
    obtain ⟨hgt, xb', hk', hf0⟩ := hok.borrow _ (List.getElem_mem hi)
    rw [hk] at hk'; cases hk'
    refine ⟨hl, fun x hx => hfp x ((clause_fp hok hls hi hl x).1 hx), hm, ?_, ⟨xb, hk, hf0, ?_⟩⟩
    · intro hex
      simp only [Cap.exclusive, hk, beq_iff_eq] at hex
      rw [he] at hmode; simp only at hmode
      rcases hmode with h | h
      · rw [hex] at h; cases h
      · simp [Cap.exclusive, hkb, h]
    · rw [he] at r0 r1 r2; simp only at r0 r1 r2
      exact ⟨r0, r1, r2⟩
  -- the callee's stack region lies in ours, below every capability's footprint there
  have hsg : ∀ x, (Spec.stackRegion s1 g.stack).mem x → (Spec.stackRegion s0 f.sig.stack).mem x ∧
      x.toNat < (s0.reg Reg.sp).toNat - S.depth := by
    intro x hx
    rw [stack_mem_iff s1 g.stack (by omega) x, hsp1] at hx
    exact ⟨(stack_mem_iff s0 _ hK x).2 ⟨by omega, by omega⟩, hx.2⟩
  have hnotcap : ∀ c ∈ S.caps, ∀ x, c.cap.fp ι Ft x → ¬ (Spec.stackRegion s1 g.stack).mem x := by
    intro c hc x hx hm
    obtain ⟨h0, h1⟩ := hsg x hm
    have hin := hI.stack c hc x hx h0
    obtain ⟨Fr, hfr, hd, hF0, -⟩ := hin
    have hg := f.frame_geom hst.frameDecl hfr
    have hF0' : Fr.size ≠ 0 := hd ▸ hF0
    have h2 := (inFrame_iff hfr hF0' s0 (by have := hg.sizeLe; omega) hg.addr x).1
      (by rw [← hd]; exact hI.stack c hc x hx h0)
    rw [← hd] at h2
    omega
  have hentryGet : ∀ i (hi : i < g.entryCaps.length), ∃ hb : i < g.borrow.length,
      g.entryCaps[i] = g.borrow[i].cap := by
    intro i hi
    have hb : i < g.borrow.length := by simpa [hentry] using hi
    exact ⟨hb, by simp [hentry]⟩
  have hentryMem : ∀ c ∈ g.entryCaps, ∃ i, ∃ hi : i < g.borrow.length, c = g.borrow[i].cap := by
    intro c hc
    rw [hentry] at hc
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hc
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    exact ⟨i, hi, rfl⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- registers
    intro p hp
    have := hin p hp
    cases he : S.reg p.1 with
    | none => rw [he] at this; exact this.elim
    | some e =>
      rw [he] at this
      have h1 := STy.reg_hasInt hI.regs he
      have h2 := STy.entEqMod_sound this hh
      rw [hregs _ (hok.inRegs p hp)]
      exact h1.congr' (by simpa using h2)
  · have := hI.ent hpre
    simpa [Constr.holds] using this
  · intro c hc
    obtain ⟨i, hi, rfl⟩ := hentryMem c hc
    obtain ⟨-, -, -, -, xb, hk, hf0, r0, r1, r2⟩ := hcl i hi
    intro _
    rw [hk]
    simp only [IExpr.eval_subst] at r0 r1 r2
    exact ⟨r0, r1, r2, by simp [hf0]⟩
  · intro i j hi hj hne hex x hx hy
    obtain ⟨hbi, ei⟩ := hentryGet i hi
    obtain ⟨hbj, ej⟩ := hentryGet j hj
    rw [ei] at hex hx; rw [ej] at hy
    obtain ⟨hli, fi, mi, exi, -⟩ := hcl i hbi
    obtain ⟨hlj, fj, mj, -, -⟩ := hcl j hbj
    by_cases hid : ls[i].2.id = ls[j].2.id
    · -- lent from the same capability: the check says the ranges are apart
      have h1 := List.all_eq_true.1 hap (ls[i], i) (mem_zipIdx_of hli)
      have h2 := List.all_eq_true.1 h1 (ls[j], j) (mem_zipIdx_of hlj)
      obtain ⟨xi, hki, hei, -⟩ := (Fn.lends_spec hls).2 i hbi hli
      obtain ⟨xj, hkj, hej, -⟩ := (Fn.lends_spec hls).2 j hbj hlj
      have hrw : xi.mode = .rw := by simpa [Cap.exclusive, hki] using hex
      obtain ⟨-, -, -, -, xi', hki', -, a0, a1, a2⟩ := hcl i hbi
      obtain ⟨-, -, -, -, xj', hkj', -, b0, b1, b2⟩ := hcl j hbj
      rw [hki] at hki'; cases hki'
      rw [hkj] at hkj'; cases hkj'
      have hxi := (clause_fp hok hls hbi hli x).1 hx
      have hyj := (clause_fp hok hls hbj hlj x).1 hy
      have ebi : ls[i].1.base = xi.base.subst θ := by rw [hei]
      have eli : ls[i].1.len = xi.len.subst θ := by rw [hei]
      have ebj : ls[j].1.base = xj.base.subst θ := by rw [hej]
      have elj : ls[j].1.len = xj.len.subst θ := by rw [hej]
      rw [← ebi] at a0 a2; rw [← eli] at a1 a2
      rw [← ebj] at b0 b2; rw [← elj] at b1 b2
      rw [region_mem_iff a0 a1 a2] at hxi
      rw [region_mem_iff b0 b1 b2] at hyj
      simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, Bool.and_eq_true] at h2
      rcases h2 with ((h | h) | h) | h
      · exact hne h
      · exact h hid
      · rw [hei] at h; simp only at h; rw [hrw] at h; cases h.1
      · have hd := STy.ent_sound h hh
        simp only [Constr.holds, Constr.eval, Bool.or_eq_true, decide_eq_true_eq, IExpr.eval_add] at hd
        omega
    · exact hI.sep _ mi _ mj hid (exi hex) x (fi x hx) (fj x hy)
  · intro c hc x hx hm
    obtain ⟨i, hi, rfl⟩ := hentryMem c hc
    obtain ⟨_hl, fi, mi, -, -⟩ := hcl i hi
    exact hnotcap _ mi x (fi x hx) hm
  · rw [hsp1]; omega
  · constructor
    · rintro x ⟨r, hr, hm⟩
      simp only [Sig.spec, Spec.perm, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | hr | hr
      · simp only [Sig.readRegions, List.mem_flatMap, List.mem_filter] at hr
        obtain ⟨c, ⟨hc, -⟩, hrc⟩ := hr
        obtain ⟨i, hi, rfl⟩ := hentryMem c hc
        obtain ⟨_hl, fi, mi, -, -⟩ := hcl i hi
        exact (hI.perm _ mi x (fi x ⟨r, hrc, hm⟩)).1
      · simp only [Sig.writeRegions, List.mem_flatMap, List.mem_filter] at hr
        obtain ⟨c, ⟨hc, -⟩, hrc⟩ := hr
        obtain ⟨i, hi, rfl⟩ := hentryMem c hc
        obtain ⟨_hl, fi, mi, -, -⟩ := hcl i hi
        exact (hI.perm _ mi x (fi x ⟨r, hrc, hm⟩)).1
      · subst hr
        exact Perm.readable_of_writable (hI.stackW x (hsg x hm).1)
    · rintro x ⟨r, hr, hm⟩
      simp only [Sig.spec, Spec.perm, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | hr
      · simp only [Sig.writeRegions, List.mem_flatMap, List.mem_filter] at hr
        obtain ⟨c, ⟨hc, hex⟩, hrc⟩ := hr
        obtain ⟨i, hi, rfl⟩ := hentryMem c hc
        obtain ⟨_hl, fi, mi, exi, -⟩ := hcl i hi
        exact (hI.perm _ mi x (fi x ⟨r, hrc, hm⟩)).2 (exi hex)
      · subst hr
        exact hI.stackW x (hsg x hm).1

theorem lookup_append_of_some {α β : Type} [BEq α] [LawfulBEq α] {l₁ l₂ : List (α × β)} {a : α} {b : β}
    (h : l₁.lookup a = some b) : (l₁ ++ l₂).lookup a = some b := by
  induction l₁ with
  | nil => simp at h
  | cons p r ih =>
    obtain ⟨x, y⟩ := p
    simp only [List.cons_append, List.lookup] at h ⊢
    split at h <;> simp_all

theorem lookup_append_of_none {α β : Type} [BEq α] [LawfulBEq α] {l₁ l₂ : List (α × β)} {a : α}
    (h : l₁.lookup a = none) : (l₁ ++ l₂).lookup a = l₂.lookup a := by
  induction l₁ with
  | nil => rfl
  | cons p r ih =>
    obtain ⟨x, y⟩ := p
    simp only [List.cons_append, List.lookup] at h ⊢
    split at h <;> simp_all

/-- The renaming of the `out` variables: the `i`-th to `x + i`. -/
theorem lookup_rename {ys : List Var} (hnd : ys.Nodup) (x : Nat) : ∀ (n : Nat) {i : Nat}
    (hi : i < ys.length),
    ((ys.zipIdx n).map fun (p : Var × Nat) => (p.1, IExpr.var (x + p.2))).lookup ys[i] =
      some (IExpr.var (x + (n + i))) := by
  induction ys with
  | nil => intro n i hi; simp at hi
  | cons y r ih =>
    intro n i hi
    simp only [List.zipIdx_cons, List.map_cons, List.lookup]
    cases i with
    | zero => simp
    | succ i =>
      simp only [List.nodup_cons] at hnd
      have hne : (r[i]'(by simp at hi; omega) == y) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        intro e; exact hnd.1 (e ▸ List.getElem_mem _)
      simp only [List.getElem_cons_succ, hne]
      rw [ih hnd.2 (n + 1) (by simp at hi; omega), show n + 1 + i = n + (i + 1) by omega]

theorem lookup_rename_none {ys : List Var} (x n : Nat) {y : Var} (hy : y ∉ ys) :
    ((ys.zipIdx n).map fun (p : Var × Nat) => (p.1, IExpr.var (x + p.2))).lookup y = none := by
  apply lookup_none
  intro p hp e
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
  exact hy (e ▸ (List.mem_zipIdx hq).2.2 ▸ List.getElem_mem _)

theorem lookup_some_of_mem {α β : Type} [BEq α] [LawfulBEq α] {l : List (α × β)} {a : α} {b : β}
    (h : (a, b) ∈ l) : ∃ b', l.lookup a = some b' := by
  induction l with
  | nil => simp at h
  | cons p r ih =>
    obtain ⟨x, y⟩ := p
    simp only [List.lookup]
    split
    · exact ⟨_, rfl⟩
    · rename_i hne
      rcases List.mem_cons.1 h with e | h
      · cases e; simp at hne
      · exact ih h

theorem Fn.callInst_spec {S : STy} {g : Sig} {θ : Subst} (h : Fn.callInst S g = some θ) :
    (∀ p ∈ θ, p.1 ∈ g.params ∧ p.2.maxVar ≤ S.maxVar) ∧ (∀ y ∈ g.params, ∃ e, θ.lookup y = some e) := by
  unfold Fn.callInst at h
  obtain ⟨hlen, hget⟩ := mapM_some h
  constructor
  · intro p hp
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
    have := hget i (by omega) hi
    split at this
    · simp only [Option.map_eq_some_iff] at this
      obtain ⟨e, he, hpe⟩ := this
      rw [← hpe]; exact ⟨List.getElem_mem _, STy.reg_maxVar he⟩
    · cases this
  · intro y hy
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
    have := hget i hi (by omega)
    split at this
    · simp only [Option.map_eq_some_iff] at this
      obtain ⟨e, -, hpe⟩ := this
      exact lookup_some_of_mem (b := e) (by rw [hpe]; exact List.getElem_mem _)
    · cases this

/-- After the call, the callee's `out` variables are the renamed fresh ones. -/
theorem eval_rename {θ : Subst} {S : STy} {g : Sig}
    (hθ1 : ∀ p ∈ θ, p.1 ∈ g.params ∧ p.2.maxVar ≤ S.maxVar)
    (hθ2 : ∀ y ∈ g.params, ∃ e, θ.lookup y = some e) (hok : CalleeSpec g)
    {ι ιg' : Val} {x : Nat} (hx : S.maxVar < x)
    (hag : ∀ y, y ∉ g.outVars → ιg' y = IExpr.upd ι θ y) {e : IExpr}
    (he : ∀ y ∈ e.vars, y ∈ g.params ∨ y ∈ g.outVars) :
    (e.subst (θ ++ g.outVars.zipIdx.map fun p => (p.1, IExpr.var (x + p.2)))).eval
      (setFrom ι x (g.outVars.map ιg')) = e.eval ιg' := by
  rw [IExpr.eval_subst]
  apply IExpr.eval_congr
  intro y hy
  rcases he y hy with hp | ho
  · obtain ⟨ey, hey⟩ := hθ2 y hp
    have hm : ey.maxVar ≤ S.maxVar := (hθ1 _ (lookup_mem hey)).2
    simp only [IExpr.upd, lookup_append_of_some hey]
    rw [IExpr.eval_congr_max (fun z hz => setFrom_below (by omega))]
    rw [hag y (fun h => hok.outApart y h hp)]
    simp [IExpr.upd, hey]
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ho
    have hnone : θ.lookup g.outVars[i] = none :=
      lookup_none (fun p hp e => hok.outApart _ (List.getElem_mem hi) (e ▸ (hθ1 p hp).1))
    simp only [IExpr.upd, lookup_append_of_none hnone, lookup_rename hok.outNodup x 0 hi,
      Nat.zero_add, IExpr.eval_var]
    rw [setFrom_at i (by simpa using hi)]
    simp [List.getElem?_eq_getElem hi]

theorem upd_rename {θ : Subst} {S : STy} {g : Sig}
    (hθ1 : ∀ p ∈ θ, p.1 ∈ g.params ∧ p.2.maxVar ≤ S.maxVar)
    (hθ2 : ∀ y ∈ g.params, ∃ e, θ.lookup y = some e) (hok : CalleeSpec g)
    {ι ιg' : Val} {x : Nat} (hx : S.maxVar < x)
    (hag : ∀ y, y ∉ g.outVars → ιg' y = IExpr.upd ι θ y) (y : Var)
    (hy : y ∈ g.params ∨ y ∈ g.outVars) :
    IExpr.upd (setFrom ι x (g.outVars.map ιg'))
      (θ ++ g.outVars.zipIdx.map fun (p : Var × Nat) => (p.1, IExpr.var (x + p.2))) y = ιg' y := by
  rcases hy with hp | ho
  · obtain ⟨ey, hey⟩ := hθ2 y hp
    have hm : ey.maxVar ≤ S.maxVar := (hθ1 _ (lookup_mem hey)).2
    simp only [IExpr.upd, lookup_append_of_some hey]
    rw [IExpr.eval_congr_max (fun z hz => setFrom_below (by omega))]
    rw [hag y (fun h => hok.outApart y h hp)]
    simp [IExpr.upd, hey]
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ho
    have hnone : θ.lookup g.outVars[i] = none :=
      lookup_none (fun p hp e => hok.outApart _ (List.getElem_mem hi) (e ▸ (hθ1 p hp).1))
    simp only [IExpr.upd, lookup_append_of_none hnone, lookup_rename hok.outNodup x 0 hi,
      Nat.zero_add, IExpr.eval_var]
    rw [setFrom_at i (by simpa using hi)]
    simp [List.getElem?_eq_getElem hi]

/-- Lemma 8.3: when the callee returns, the type after the call holds. -/
theorem Fn.afterCall_inv (hst : f.StructSpec) {S : STy} {s : State} {ι : Val} {Ft : TokFp}
    (hI : Inv f T P s0 ι0 S s ι Ft) {g : Sig} (hok : CalleeSpec g) {θ : Subst}
    (hθ : Fn.callInst S g = some θ) (hstk : S.depth + g.stack ≤ f.sig.stack)
    {ls : List (BytesCap × HCap)} (hls : Fn.lends S g θ = some ls)
    {s1 s2 : State} (hregs : ∀ r : Reg, r ≠ 1 → s1.reg r = s.reg r) (hmem : s1.mem = s.mem)
    (hpres : Preserved s1 s2) (hlive : s2.exit = none)
    (hpost : g.Post T (IExpr.upd ι θ) Ft s1 s2)
    (hframe : ∀ x, ¬ ((g.spec T).perm (IExpr.upd ι θ, Ft) s1).writable x → s2.mem x = s1.mem x) :
    ∃ ι', (∀ y : Nat, y < f.fresh → ι' y = ι y) ∧ Inv f T P s0 ι0 (f.afterCall S g θ ls) s2 ι' Ft := by
  obtain ⟨ιg', Fg', hag, hregs', hpost', -, -, -⟩ := hpost
  obtain ⟨hθ1, hθ2⟩ := Fn.callInst_spec hθ
  have hh := hI.hyps
  obtain ⟨hlen, hget⟩ := Fn.lends_spec hls
  have hspn := hI.sp_toNat hst
  have hK := hI.stackLe
  let x := f.freshAt S
  have hx : S.maxVar < x := f.freshAt_gt S
  let ι' := setFrom ι x (g.outVars.map ιg')
  obtain ⟨g1, g2, g3⟩ := setFrom_fresh hst.protFresh S ι (g.outVars.map ιg')
  have hev := fun (e : IExpr) (he : ∀ y ∈ e.vars, y ∈ g.params ∨ y ∈ g.outVars) =>
    eval_rename (x := x) (ι := ι) (ιg' := ιg') hθ1 hθ2 hok hx (fun y hy => hag y hy) he
  -- what the callee may write: a range lent `rw`, or its own stack
  have hw : ∀ z, ((g.spec T).perm (IExpr.upd ι θ, Ft) s1).writable z →
      (∃ i, ∃ hi : i < ls.length, ls[i].1.mode = .rw ∧ ls[i].2.cap.fp ι Ft z ∧ ls[i].2 ∈ S.caps ∧
        ls[i].2.cap.exclusive = true) ∨
      (z.toNat < (s0.reg Reg.sp).toNat - S.depth ∧ (Spec.stackRegion s0 f.sig.stack).mem z) := by
    intro z ⟨r, hr, hm⟩
    simp only [Sig.spec, Spec.perm, List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | hr
    · left
      simp only [Sig.writeRegions, List.mem_flatMap, List.mem_filter] at hr
      obtain ⟨c, ⟨hc, hex⟩, hrc⟩ := hr
      have hentry : g.entryCaps = g.borrow.map (·.cap) := by simp [Sig.entryCaps, hok.take]
      rw [hentry] at hc
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hc
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
      have hl : i < ls.length := by omega
      obtain ⟨xb, hk, he, hlf⟩ := hget i hi hl
      obtain ⟨hmc, -⟩ := Fn.lendFrom_spec hlf
      obtain ⟨hb', hkb, hmode, -, -, -, -, hfp⟩ := lend_region hh (hI.valid _ hmc) hlf
      have hrw : xb.mode = .rw := by simpa [Cap.exclusive, hk] using hex
      have hrw' : ls[i].1.mode = .rw := by rw [he]; exact hrw
      have hz := (clause_fp hok hls hi hl z).1 ⟨r, hrc, hm⟩
      refine ⟨i, hl, hrw', hfp z hz, hmc, ?_⟩
      rcases hmode with h | h
      · rw [hrw'] at h; cases h
      · simp [Cap.exclusive, hkb, h]
    · right
      subst hr
      have hsp1 : (s1.reg Reg.sp).toNat = (s0.reg Reg.sp).toNat - S.depth := by
        rw [hregs _ (by decide)]; exact hspn.1
      rw [stack_mem_iff s1 g.stack (by omega) z, hsp1] at hm
      exact ⟨hm.2, (stack_mem_iff s0 _ hK z).2 ⟨by omega, by omega⟩⟩
  -- a capability not lent `rw`, and a slot, are not written
  have hcapw : ∀ c ∈ S.caps, (∀ p ∈ ls, p.1.mode = .rw → p.2.id ≠ c.id) →
      ∀ z, c.cap.fp ι Ft z → s2.mem z = s.mem z := by
    intro c hc hnl z hz
    rw [← hmem]
    refine hframe z fun hzw => ?_
    rcases hw z hzw with ⟨i, hi, hrw, hfp, hm, hex⟩ | ⟨hlt, hS0⟩
    · exact hI.sep _ hm c hc (hnl _ (List.getElem_mem hi) hrw) hex z hfp hz
    · obtain ⟨Fr, hfr, hd, hF0, r, hr, h1, h2⟩ := hI.stack c hc z hz hS0
      have hg := f.frame_geom hst.frameDecl hfr
      have := (inFrame_iff hfr (hd ▸ hF0) s0 (by have := hg.sizeLe; omega) hg.addr z).1
        (hd ▸ hI.stack c hc z hz hS0)
      rw [← hd] at this; omega
  have hupd := upd_rename (ι := ι) (ιg' := ιg') hθ1 hθ2 hok hx (fun y hy => hag y hy)
  -- capabilities after the call: the same footprints, valid in the new memory
  have hclr : ∀ c0 ∈ S.caps, (Fn.clearLent ls c0).id = c0.id ∧
      (Fn.clearLent ls c0).cap.exclusive = c0.cap.exclusive ∧
      (∀ z, (Fn.clearLent ls c0).cap.fp ι' Ft z ↔ c0.cap.fp ι Ft z) ∧
      (Fn.clearLent ls c0).cap.valid T ι' Ft s2.mem := by
    intro c0 hc0
    have hcg := Cap.congr (T := T) (F := Ft) (c := c0) (ι := ι) (ι' := ι')
      (fun z hz => (g1 z (Nat.le_trans hz (STy.le_maxVar_cap hc0))).symm)
    unfold Fn.clearLent
    split
    · rename_i hl
      cases hk : c0.cap.kind with
      | bytes h =>
        simp only
        refine ⟨by simp, by simp [Cap.exclusive, hk], fun z => ?_, ?_⟩
        · rw [hcg.1 z]; simp [Cap.fp, Cap.regions, hk, BytesCap.region]
        · have hv := (hcg.2 s.mem).1 (hI.valid c0 hc0)
          unfold Cap.valid at hv ⊢; rw [hk] at hv
          intro hg; obtain ⟨a0, a1, a2, -⟩ := hv hg
          exact ⟨a0, a1, a2, by simp⟩
      | token t =>
        simp only
        refine ⟨by simp, by simp, fun z => (hcg.1 z).symm, ?_⟩
        refine (hcg.2 _).1 (Cap.valid_congr (hI.valid c0 hc0) (fun z hz => ?_))
        -- a token is never lent: its bytes are not the callee's to write
        rw [hcapw c0 hc0 (fun p hp hrw e => ?_) z hz]
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
        obtain ⟨xb, -, -, hlf⟩ := hget i (by omega) hi
        obtain ⟨hmc, -, hb, hkb, -⟩ := Fn.lendFrom_spec hlf
        have := eq_of_id_eq hI.ids hmc hc0 e
        rw [this, hk] at hkb; cases hkb
    · rename_i hl
      simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq, not_exists, not_and] at hl
      refine ⟨by simp, by simp, fun z => (hcg.1 z).symm, (hcg.2 _).1
        (Cap.valid_congr (hI.valid c0 hc0) (fun z hz => (hcapw c0 hc0 ?_ z hz).symm))⟩
      intro p hp hrw e
      exact hl p hp e hrw
  refine ⟨ι', g3, ?_, ?_, fun z hz => (g2 z hz).trans (hI.prot z hz), ?_, ?_, ?_, ?_, ?_, ?_, hlive,
    hI.depth, ?_, hI.stackW, hI.spAl, hI.stackLe⟩
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
    rcases hp with ⟨hp, hpr⟩ | ⟨q, hq, rfl⟩
    · have hr1 : p.1 ≠ 1 := by intro e; rw [e] at hpr; simp [preservedRegs] at hpr
      rw [hpres p.1 (by simpa using hpr), hregs _ hr1]
      exact (hI.regs p hp).of_eq (IExpr.eval_congr_max
        (fun z hz => (g1 z (Nat.le_trans hz (STy.le_maxVar_reg hp))).symm))
    · refine (hregs' q hq).of_eq ?_
      rw [IExpr.eval_subst, IExpr.eval_congr _ (fun y hy => hupd y (hok.outScoped q hq y hy))]
  · intro c hc
    simp only [Fn.afterCall, List.mem_map] at hc
    obtain ⟨c0, hc0, rfl⟩ := hc
    exact (hclr c0 hc0).2.2.2
  · intro c hc d hd hne hex z hz hy
    simp only [Fn.afterCall, List.mem_map] at hc hd
    obtain ⟨c0, hc0, rfl⟩ := hc
    obtain ⟨d0, hd0, rfl⟩ := hd
    obtain ⟨i1, e1, f1, -⟩ := hclr c0 hc0
    obtain ⟨i2, -, f2, -⟩ := hclr d0 hd0
    exact hI.sep c0 hc0 d0 hd0 (by rw [← i1, ← i2]; exact hne) (e1 ▸ hex) z ((f1 z).1 hz) ((f2 z).1 hy)
  · intro c hc z hz hm
    simp only [Fn.afterCall, List.mem_map] at hc
    obtain ⟨c0, hc0, rfl⟩ := hc
    exact hI.stack c0 hc0 z (((hclr c0 hc0).2.2.1 z).1 hz) hm
  · intro c hc z hz
    simp only [Fn.afterCall, List.mem_map] at hc
    obtain ⟨c0, hc0, rfl⟩ := hc
    obtain ⟨-, e1, f1, -⟩ := hclr c0 hc0
    obtain ⟨r1, r2⟩ := hI.perm c0 hc0 z ((f1 z).1 hz)
    exact ⟨r1, fun h => r2 (e1 ▸ h)⟩
  · have : (f.afterCall S g θ ls).caps.map (·.id) = S.caps.map (·.id) := by
      simp only [Fn.afterCall, List.map_map]
      exact List.map_congr_left (fun c0 hc0 => (hclr c0 hc0).1)
    rw [this]; exact hI.ids
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
      rcases hw _ hzw with ⟨j, hj, -, hfp, hm, -⟩ | ⟨hlt, -⟩
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

/-- Lemma 8: a call, its callee's whole run as one step (`VerifiedImg.call`), and the
    continuation after it returns. -/
theorem Fn.call_step (hst : f.StructSpec) {c : Code} {D : Dom} {Q : State → Prop}
    {S : STy} {s : State} {ι : Val} {Ft : TokFp} {k : Nat} {off : BitVec 21}
    (hI : Inv f T P s0 ι0 S s ι Ft) (hd : D.mem s.pc) (hpc : s.pc = f.pcOf k)
    (hi : c.instr s.pc = some (.jal 1 off)) (hk : f.callOk k S off = true)
    (hcall : ∀ p ∈ f.callees, aligned p.1 4 ∧ ∃ Dg, Meets c Dg p.1 T p.2 ∧ Dg.sub D ∧
      ∀ j < f.size, ¬ Dg.mem (f.pcOf j))
    (hexit : ∀ s', s'.exit ≠ none → Reach c P D Q s')
    (cont : ∀ S1 s' ι1, s'.pc = f.pcOf (k + 1) → Inv f T P s0 ι0 S1 s' ι1 Ft →
      (∀ y : Nat, y < f.fresh → ι1 y = ι y) → f.edge (some k) S1 (k + 1) = true →
      Reach c P D Q s') :
    Reach c P D Q s := by
  unfold Fn.callOk at hk
  generalize ht : f.pcOf k + off.signExtend 64 = t at hk
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
  simp only [Bool.and_eq_true] at hk
  obtain ⟨hap, hedge⟩ := hk
  have hgm := lookup_mem hg
  obtain ⟨hal, Dg, hmeets, hDg, hret⟩ := hcall _ hgm
  have hok := Fn.calleeOk_spec (hst.callees _ hgm)
  have hk1 := Fn.edge_lt hedge
  refine Reach.exec_step hd hI.live hi trivial ?_
  have hx : exec (.jal 1 off) s = some ((s.setReg 1 (s.pc + 4)).setPc t) := by
    simp only [exec, jumpTo, hpc, ht, hal, if_true]
  rw [hx, Reach.opt_some]
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
    · obtain ⟨ι', g1, hI'⟩ := f.afterCall_inv hst hI hok hθ hstk hls hregs1 hmem1 hpres hlive hpost hfr
      refine cont _ _ ι' ?_ hI' g1 hedge
      rw [hpc2]; exact hra
    · exact hexit s2 hex

end NoCompiler.Typed
