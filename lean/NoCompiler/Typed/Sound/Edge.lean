import NoCompiler.Typed.Sound.Mem

/-
The structural conditions and the edge rule: an accepted edge carries the invariant to
the target and decreases the rank (Lemma 4 and Theorem C's step).
-/
namespace NoCompiler.Typed

variable {f : Fn} {T : TokEnv} {P : Perm} {s0 : State} {ι0 : Val}

/-- What `structOk` gives the proof. -/
structure Fn.StructSpec (f : Fn) : Prop where
  take : f.sig.take = []
  give : f.sig.give = []
  callees : ∀ p ∈ f.callees, Fn.calleeOk p.2 = true
  frameDecl : f.frameDeclOk = true
  borrowBytes : ∀ b ∈ f.sig.borrow, ∃ x, b.cap.kind = .bytes x
  kept : ∀ r ∈ keptRegs, (f.regVar.lookup r).isSome
  protNodup : f.protectedVars.Nodup
  entryIds : ((List.range f.sig.borrow.length).map f.entryId).Nodup
  protFresh : ∀ x ∈ f.protectedVars, x < f.fresh
  tau : f.tau = [] ∨ (f.tau.length = f.size ∧ ∀ k < f.size, k ∈ f.tau)
  loopsIn : ∀ L ∈ f.loops, f.pos L.head ≤ f.pos L.last ∧ L.last < f.size
  measFresh : ∀ L ∈ f.loops, ∀ x ∈ L.meas.vars, x < f.fresh
  sorted : (f.loops.map (f.pos ·.head)).Pairwise (· < ·)
  entryAligned : f.entry.toNat % 4 = 0
  size : 4 * f.size < 2 ^ 64
  nested : f.Nested
  inRegs : ∀ p ∈ f.sig.inRegs, ∀ x ∈ p.2.vars, x ∈ f.sig.params
  pre : ∀ x ∈ f.sig.pre.vars, x ∈ f.sig.params
  borrowVars : ∀ b ∈ f.sig.borrow, (∀ x ∈ b.cap.guard.vars, x ∈ f.sig.params) ∧
    ∀ x, b.cap.kind = .bytes x → (∀ y ∈ x.base.vars ++ x.len.vars ++ x.fields.flatMap (·.ty.vars),
      y ∈ f.sig.params) ∧ ∀ y ∈ b.outFields.flatMap (·.ty.vars), y ∈ f.sig.params ∨ y ∈ f.sig.outVars
  outRegs : ∀ p ∈ f.sig.outRegs, ∀ x ∈ p.2.vars, x ∈ f.sig.params ∨ x ∈ f.sig.outVars
  post : ∀ x ∈ f.sig.post.vars, x ∈ f.sig.params ∨ x ∈ f.sig.outVars
  outProt : ∀ x ∈ f.sig.outVars, x ∉ f.protectedVars

theorem Fn.structOk_spec (h : f.structOk = true) : f.StructSpec := by
  unfold Fn.structOk at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.isEmpty_iff, beq_iff_eq, decide_eq_true_eq,
    Bool.or_eq_true, List.contains_iff_mem, Bool.not_eq_true', Option.isSome_iff_exists] at h
  simp only [and_assoc] at h
  obtain ⟨htake, hgive, hcal, hstack, hbb, hkept, hnd, hei, hpf, htau, hloops, hsorted, hal, hsz, hnest, hin, hpre,
    hbv, hout, hpost, hop, -⟩ := h
  refine ⟨htake, hgive, hcal, hstack, ?_, fun r hr => by simpa [Option.isSome_iff_exists] using hkept r hr,
    hnd, hei, hpf, ?_, fun L hL => ⟨(hloops L hL).1, (hloops L hL).2.1⟩, fun L hL => (hloops L hL).2.2.2,
    hsorted, hal, hsz, ?_, hin, hpre, ?_, hout, hpost, fun x hx => by simpa using hop x hx⟩
  · intro b hb
    have := hbb b hb
    split at this
    · rename_i x hx; exact ⟨x, hx⟩
    · cases this
  · rcases htau with h | ⟨hl, hall⟩
    · exact .inl h
    · exact .inr ⟨hl, fun k hk => hall k (List.mem_range.2 hk)⟩
  · intro K hK L hL
    rcases hnest K hK L hL with (((h | h) | h) | h) | h
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr (.inl h)))
    · exact .inr (.inr (.inr (.inr h)))
  · intro b hb
    obtain ⟨hg, hk⟩ := hbv b hb
    refine ⟨hg, fun x hx => ?_⟩
    rw [hx] at hk
    simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem, Bool.or_eq_true] at hk
    exact ⟨hk.1, hk.2⟩

/-- Points of the function have positions inside it. -/
theorem Fn.pos_lt (hst : f.StructSpec) {k : Nat} (hk : k < f.size) : f.pos k < f.size := by
  unfold Fn.pos
  split
  · exact hk
  · rcases hst.tau with h | ⟨hl, hall⟩
    · contradiction
    · rw [← hl]; exact List.idxOf_lt_length_of_mem (hall k hk)

theorem Fn.loopAt_spec {L : Loop} {k : Nat} (h : f.loopAt k = some L) : L ∈ f.loops ∧ L.head = k := by
  unfold Fn.loopAt at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

/-- An accepted edge: the invariant at the target, under `upd ι θ`, and a smaller rank
    than at the source (whose valuation `ιpre` agrees with `ι` below the fresh point). -/
theorem Fn.edgeOk_sound (hst : f.StructSpec) {k : Option Nat} {S S' : STy} {k' : Nat} {θ : Subst}
    (he : f.edgeOk k S S' k' θ = true) {s : State} {ι ιpre : Val} {F : TokFp}
    (hI : Inv f T P s0 ι0 S s ι F) (hag : ∀ y : Nat, y < f.fresh → ι y = ιpre y) :
    k' < f.size ∧ Inv f T P s0 ι0 S' s (IExpr.upd ι θ) F ∧
      ∀ kk, k = some kk → LexN (f.rank k' (IExpr.upd ι θ)) (f.rank kk ιpre) := by
  unfold Fn.edgeOk at he
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true',
    List.contains_iff_mem] at he
  obtain ⟨⟨⟨hk', hθ⟩, hsub⟩, hback⟩ := he
  have hprot : ∀ p ∈ θ, p.1 ∉ f.protectedVars := by
    intro p hp h; have := (hθ p hp).1; simp_all
  refine ⟨hk', hI.sub hsub hprot, ?_⟩
  intro kk hkk
  subst hkk
  -- measure variables untouched by θ keep their values
  have hmeas : ∀ K ∈ f.loops, (∀ p ∈ θ, p.1 ∉ K.meas.vars) →
      ∀ x ∈ K.meas.vars, IExpr.upd ι θ x = ιpre x := by
    intro K hK hK' x hx
    rw [upd_of_not_mem (fun p hp e => hK' p hp (e ▸ hx))]
    exact hag x (hst.measFresh K hK x hx)
  have hfree : ∀ K ∈ f.loops, f.inside K kk = true → f.inside K k' = true →
      ¬ (f.pos k' ≤ f.pos kk ∧ K.head = k') → ∀ p ∈ θ, p.1 ∉ K.meas.vars := by
    intro K hK h1 h2 hn p hp hm
    have := (hθ p hp).2 K hK
    simp only [h1, h2, Bool.true_and, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_imp,
      Bool.not_eq_false, beq_iff_eq, decide_eq_true_eq] at this
    rcases this with h | h
    · simp only [Bool.not_eq_false', Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
      exact hn h
    · simp_all
  by_cases hb : f.pos k' ≤ f.pos kk
  · simp only [hb, decide_true, ite_true] at hback
    split at hback
    · rename_i L kk' hL hkk
      cases hkk
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hback
      obtain ⟨⟨hlast, h0⟩, hlt⟩ := hback
      obtain ⟨hLm, hLh⟩ := Fn.loopAt_spec hL
      have h0 := hI.ent h0
      have hlt := hI.ent hlt
      simp only [Constr.holds, Constr.lt, Constr.eval, decide_eq_true_eq, IExpr.eval_lit,
        IExpr.eval_add, IExpr.eval_subst] at h0 hlt
      have e1 : L.meas.eval ι = L.meas.eval ιpre :=
        IExpr.eval_congr L.meas (fun x hx => hag x (hst.measFresh L hLm x hx))
      refine f.rank_back hLm hLh hb hlast hst.sorted hst.nested (fun K hK hne h1 h2 x hx =>
        hmeas K hK (hfree K hK h1 h2 (fun ⟨_, h⟩ => hne h)) x hx) (by omega) (by omega)
    · simp at hback
  · refine f.rank_fwd (by omega) (f.pos_lt hst hk') (fun K hK h1 h2 x hx =>
      hmeas K hK (hfree K hK h1 h2 (fun ⟨h, _⟩ => hb h)) x hx)

end NoCompiler.Typed
