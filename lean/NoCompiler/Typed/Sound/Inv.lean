import NoCompiler.Typed.Sound.Word

/-
The invariant of a checked function (the proof's D6, I1–I8, for frameless functions
without calls), and Lemma 4: subtyping carries it along an edge.
-/
namespace NoCompiler.Typed

theorem lookup_mem {α β : Type} [BEq α] [LawfulBEq α] {l : List (α × β)} {a : α} {b : β}
    (h : l.lookup a = some b) : (a, b) ∈ l := by
  induction l with
  | nil => simp at h
  | cons p r ih =>
    obtain ⟨x, y⟩ := p
    simp only [List.lookup] at h
    split at h
    · rename_i hx; simp at hx h; subst hx; subst h; simp
    · exact List.mem_cons_of_mem _ (ih h)

theorem lookup_none {α β : Type} [BEq α] [LawfulBEq α] {l : List (α × β)} {a : α}
    (h : ∀ p ∈ l, p.1 ≠ a) : l.lookup a = none := by
  induction l with
  | nil => rfl
  | cons p r ih =>
    obtain ⟨x, y⟩ := p
    simp only [List.lookup]
    have hx : x ≠ a := h (x, y) (List.mem_cons_self ..)
    have : (a == x) = false := by simp; exact fun e => hx e.symm
    rw [this]; exact ih (fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem upd_of_not_mem {ι : Val} {θ : Subst} {x : Var} (h : ∀ p ∈ θ, p.1 ≠ x) :
    IExpr.upd ι θ x = ι x := by
  simp [IExpr.upd, lookup_none h]

namespace STy

theorem hyps_holds {T : TokEnv} {ι : Val} {F : TokFp} {m : Word → Byte} {S : STy}
    (hf : ∀ p ∈ S.facts, p.holds ι) (hv : ∀ c ∈ S.caps, c.cap.valid T ι F m) :
    ∀ p ∈ S.hyps, p.holds ι := by
  intro p hp
  rcases List.mem_append.1 hp with hp | hp
  · exact hf p hp
  · obtain ⟨c, hc, e⟩ := List.mem_filterMap.1 hp
    split at e
    · rename_i b hk
      cases e
      have hvc := hv c hc
      simp only [Cap.valid, hk] at hvc
      unfold Constr.holds Constr.imp
      simp only [Constr.eval, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true,
        decide_eq_true_eq, IExpr.eval_lit, IExpr.eval_add]
      by_cases hg : c.cap.guard.eval ι = true
      · obtain ⟨h0, h1, h2, -⟩ := hvc hg
        exact .inr ⟨h0, h1, h2⟩
      · exact .inl (by simpa using hg)
    · cases e

theorem entQ_sound {ι : Val} {S : STy} {ψ : Constr} (h : S.entQ ψ = true)
    (hh' : ∀ p ∈ S.hyps, p.holds ι) : ψ.holds ι := by
  have hh : ∀ p ∈ relevant S.hyps ψ, p.holds ι := fun p hp => hh' p (List.mem_filter.1 hp).1
  unfold entQ at h
  split at h
  · rfl
  · rename_i a b
    rcases Bool.or_eq_true _ _ ▸ h with h | h
    · simp [Constr.holds, Constr.eval, IExpr.eval_of_same h ι]
    · exact Query.decide_sound h ι hh
  · rename_i c e
    rcases Bool.or_eq_true _ _ ▸ h with h | h
    · simp [Constr.holds, Constr.eval, IExpr.eval_of_same h ι]
    · exact Query.decide_sound h ι hh
  · exact Query.decide_sound h ι hh


theorem constLin_eval {l : Lin} {ok : Int → Bool} (h : constLin l ok = true) (ι : Val) :
    l.eval ι = l.c ∧ ok l.c = true := by
  unfold constLin at h
  simp only [Bool.and_eq_true, List.isEmpty_iff] at h
  obtain ⟨ht, hc⟩ := h
  refine ⟨?_, hc⟩
  simp only [Lin.eval, ht, Lin.evalT]; omega

theorem covers_sound {ι : Val} {p ψ : Constr} (h : covers p ψ = true) (hp : p.holds ι) :
    ψ.holds ι := by
  unfold covers at h
  split at h
  · rename_i a b c d
    obtain ⟨he, hc⟩ := constLin_eval h ι
    simp only [IExpr.eval_toLin, IExpr.eval_sub] at he
    simp only [decide_eq_true_eq] at hc
    simp only [Constr.holds, Constr.eval, decide_eq_true_eq] at hp ⊢; omega
  · rename_i a b c d
    simp only [Constr.holds, Constr.eval, decide_eq_true_eq] at hp ⊢
    rcases Bool.or_eq_true _ _ ▸ h with h | h
    · obtain ⟨he, hc⟩ := constLin_eval h ι
      simp only [IExpr.eval_toLin, IExpr.eval_sub] at he
      simp only [beq_iff_eq] at hc; omega
    · obtain ⟨he, hc⟩ := constLin_eval h ι
      simp only [IExpr.eval_toLin, IExpr.eval_sub, IExpr.eval_add] at he
      simp only [beq_iff_eq] at hc; omega
  · rename_i a b c d
    simp only [Constr.holds, Constr.eval, decide_eq_true_eq] at hp ⊢
    rcases Bool.or_eq_true _ _ ▸ h with h | h
    · obtain ⟨he, hc⟩ := constLin_eval h ι
      simp only [IExpr.eval_toLin, IExpr.eval_sub] at he
      simp only [decide_eq_true_eq] at hc; omega
    · obtain ⟨he, hc⟩ := constLin_eval h ι
      simp only [IExpr.eval_toLin, IExpr.eval_sub, IExpr.eval_add] at he
      simp only [decide_eq_true_eq] at hc; omega
  · rename_i k e k' e'
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨he, hc⟩ := constLin_eval h ι
    simp only [IExpr.eval_toLin, IExpr.eval_sub] at he
    simp only [beq_iff_eq] at hc
    simp only [Constr.holds, Constr.eval, decide_eq_true_eq] at hp ⊢
    have h1 := Int.dvd_of_emod_eq_zero hp
    have h2 := Int.dvd_of_emod_eq_zero hc
    apply Int.emod_eq_zero_of_dvd
    have h3 : e'.eval ι = e.eval ι + ((e'.sub e).toLin).c := by omega
    rw [h3]; exact Int.dvd_add h1 h2
  · rename_i hne1 hne2 hne3 hne4
    simp only [beq_iff_eq] at h; subst h; exact hp

theorem ent_sound {ι : Val} {S : STy} {ψ : Constr} (h : S.ent ψ = true)
    (hh' : ∀ p ∈ S.hyps, p.holds ι) : ψ.holds ι := by
  unfold ent at h
  rcases Bool.or_eq_true _ _ ▸ h with h | h
  · rcases Bool.or_eq_true _ _ ▸ h with h | h
    · exact hh' ψ (List.mem_append_left _ (List.contains_iff_mem.1 h))
    · obtain ⟨p, hp, hc⟩ := List.any_eq_true.1 h
      exact covers_sound hc (hh' p (List.mem_append_left _ hp))
  · exact entQ_sound h hh'
theorem entEqMod_sound {ι : Val} {S : STy} {a b : IExpr} (h : S.entEqMod a b = true)
    (hh : ∀ p ∈ S.hyps, p.holds ι) : (a.eval ι - b.eval ι) % 2 ^ 64 = 0 := by
  unfold entEqMod at h
  rcases Bool.or_eq_true _ _ ▸ h with h | h
  · simp [IExpr.eval_of_same h ι]
  · have := ent_sound h hh
    simp only [Constr.holds, Constr.eqMod, Constr.eval, decide_eq_true_eq, IExpr.eval_sub] at this
    exact_mod_cast this

/-- A register's recorded type holds of it. -/
theorem reg_hasInt {ι : Val} {S : STy} {s : State} (hr : ∀ p ∈ S.regs, HasInt ι (s.reg p.1) p.2)
    {r : Reg} {e : IExpr} (h : S.reg r = some e) : HasInt ι (s.reg r) e := by
  unfold reg at h
  split at h
  · rename_i h0; cases h; subst h0; simp [State.reg, HasInt]
  · exact hr _ (lookup_mem h)

end STy

/-- `x` is in one of the frame's address-taken ranges, the frame being allocated at depth
    `d` (the proof's `A`; empty at depth 0). -/
def Fn.inFrame (f : Fn) (s0 : State) (d : Nat) (x : Word) : Prop :=
  ∃ F, f.frame = some F ∧ d = F.size ∧ d ≠ 0 ∧
    ∃ r ∈ F.addr, r.1 ≤ (x - (s0.reg Reg.sp - BitVec.ofNat 64 d)).toNat ∧
      (x - (s0.reg Reg.sp - BitVec.ofNat 64 d)).toNat < r.1 + r.2

/-- The frame is allocated at depth `d`, or not at all (S3). -/
def Fn.depthOk (f : Fn) (d : Nat) : Prop := d = 0 ∨ ∃ F, f.frame = some F ∧ d = F.size ∧ F.size ≠ 0

/-- The invariant at a point of type `S` (D6), relative to the entry state `s0`, the
    entry valuation `ι0` and the function's permission `P`. -/
structure Inv (f : Fn) (T : TokEnv) (P : Perm) (s0 : State) (ι0 : Val)
    (S : STy) (s : State) (ι : Val) (F : TokFp) : Prop where
  facts : ∀ p ∈ S.facts, p.holds ι
  regs : ∀ p ∈ S.regs, HasInt ι (s.reg p.1) p.2
  prot : ∀ x ∈ f.protectedVars, ι x = ι0 x
  valid : ∀ c ∈ S.caps, c.cap.valid T ι F s.mem
  sep : ∀ c ∈ S.caps, ∀ d ∈ S.caps, c.id ≠ d.id → c.cap.exclusive = true →
    ∀ x, c.cap.fp ι F x → ¬ d.cap.fp ι F x
  stack : ∀ c ∈ S.caps, ∀ x, c.cap.fp ι F x → (Spec.stackRegion s0 f.sig.stack).mem x →
    f.inFrame s0 S.depth x
  perm : ∀ c ∈ S.caps, ∀ x, c.cap.fp ι F x →
    P.readable x ∧ (c.cap.exclusive = true → P.writable x)
  ids : (S.caps.map (·.id)).Nodup
  sp : s.reg Reg.sp = s0.reg Reg.sp - BitVec.ofNat 64 S.depth
  live : s.exit = none
  depth : f.depthOk S.depth
  slots : ∀ p ∈ S.slots, (∃ Fr, f.frame = some Fr ∧ S.depth = Fr.size ∧ p.1 ∈ Fr.slots) ∧
    (∀ i, i < 8 → (Spec.stackRegion s0 f.sig.stack).mem
        (s0.reg Reg.sp - BitVec.ofNat 64 S.depth + BitVec.ofNat 64 p.1 + BitVec.ofNat 64 i) ∧
      ¬ f.inFrame s0 S.depth
        (s0.reg Reg.sp - BitVec.ofNat 64 S.depth + BitVec.ofNat 64 p.1 + BitVec.ofNat 64 i)) ∧
    HasInt ι (read64 s.mem (s0.reg Reg.sp - BitVec.ofNat 64 S.depth + BitVec.ofNat 64 p.1)) p.2
  stackW : ∀ x, (Spec.stackRegion s0 f.sig.stack).mem x → P.writable x
  spAl : (s0.reg Reg.sp).toNat % 16 = 0
  stackLe : f.sig.stack ≤ (s0.reg Reg.sp).toNat

namespace Inv
variable {f : Fn} {T : TokEnv} {P : Perm} {s0 : State} {ι0 : Val} {S : STy} {s : State} {ι : Val}
  {F : TokFp}

theorem hyps (h : Inv f T P s0 ι0 S s ι F) : ∀ p ∈ S.hyps, p.holds ι := STy.hyps_holds h.facts h.valid

theorem ent (h : Inv f T P s0 ι0 S s ι F) {ψ : Constr} (he : S.ent ψ = true) : ψ.holds ι :=
  STy.ent_sound he h.hyps

end Inv

/-! ## Lemma 4 -/

namespace STy

theorem guard_imp {ι : Val} {S : STy} {θ : Subst} {g g' : Constr}
    (h : S.ent (Constr.imp (g'.subst θ) g) = true) (hh : ∀ p ∈ S.hyps, p.holds ι) :
    g'.eval (IExpr.upd ι θ) = true → g.eval ι = true := by
  have := ent_sound h hh
  simp only [Constr.holds, Constr.imp, Constr.eval, Bool.or_eq_true, Bool.not_eq_true',
    Constr.eval_subst] at this
  intro hg; rcases this with h | h
  · rw [hg] at h; cases h
  · exact h

/-- What `capSub` gives: the footprint shrinks, validity carries over, and the kind of
    capability (exclusive or not) is the same. -/
theorem capSub_sound {T : TokEnv} {ι : Val} {F : TokFp} {S : STy} {θ : Subst} {c c' : HCap}
    (h : S.capSub θ c c' = true) (hh : ∀ p ∈ S.hyps, p.holds ι) :
    c.id = c'.id ∧ c'.cap.exclusive = c.cap.exclusive ∧
    (∀ x, c'.cap.fp (IExpr.upd ι θ) F x → c.cap.fp ι F x) ∧
    (∀ m, c.cap.valid T ι F m → c'.cap.valid T (IExpr.upd ι θ) F m) := by
  unfold capSub at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hid, -⟩, hg⟩, hk⟩ := h
  have hgi : c'.cap.guard.eval (IExpr.upd ι θ) = true → c.cap.guard.eval ι = true := by
    rcases Bool.or_eq_true _ _ ▸ hg with h1 | h1
    · simp only [Bool.and_eq_true, beq_iff_eq] at h1
      rw [h1.2]; intro _; rfl
    · exact guard_imp h1 hh
  refine ⟨hid, ?_, ?_, ?_⟩
  · split at hk
    · rename_i b b' hb hb'
      simp only [Bool.and_eq_true, beq_iff_eq] at hk
      simp [Cap.exclusive, hb, hb', hk.1.1.1.1]
    · rename_i t t' hb hb'
      simp at hk; simp [Cap.exclusive, hb, hb']
    · cases hk
  · intro x hx
    obtain ⟨r, hr, hm⟩ := hx
    unfold Cap.regions at hr
    split at hr
    · rename_i hg'
      refine ⟨r, ?_, hm⟩
      unfold Cap.regions; rw [if_pos (hgi hg')]
      split at hk
      · rename_i b b' hb hb'
        simp only [Bool.and_eq_true, beq_iff_eq] at hk
        obtain ⟨⟨⟨⟨-, -⟩, he1⟩, he2⟩, -⟩ := hk
        have e1 := ent_sound he1 hh
        have e2 := ent_sound he2 hh
        simp only [Constr.holds, Constr.eval, decide_eq_true_eq, IExpr.eval_subst] at e1 e2
        simp only [hb] ; simp only [hb'] at hr
        simp only [List.mem_singleton] at hr ⊢; subst hr
        simp [BytesCap.region, e1, e2]
      · rename_i t t' hb hb'
        simp at hk; subst hk; simp only [hb] ; simp only [hb'] at hr; exact hr
      · cases hk
    · simp at hr
  · intro m hv
    unfold Cap.valid at hv ⊢
    intro hg'
    have hv := hv (hgi hg')
    split at hk
    · rename_i b b' hb hb'
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.any_eq_true] at hk
      obtain ⟨⟨⟨⟨-, hheap⟩, he1⟩, he2⟩, hfs⟩ := hk
      have e1 := ent_sound he1 hh
      have e2 := ent_sound he2 hh
      simp only [Constr.holds, Constr.eval, decide_eq_true_eq, IExpr.eval_subst] at e1 e2
      simp only [hb] at hv; simp only [hb']
      obtain ⟨h0, h1, h2, hf, hu⟩ := hv
      have hU : b'.heap = true → (T heapTok).unit (F heapTok) (b'.region (IExpr.upd ι θ)) := by
        intro hh'
        have hr : b'.region (IExpr.upd ι θ) = b.region ι := by
          simp only [BytesCap.region, IExpr.eval_subst] at *; rw [← e1, ← e2]
        rw [hr]; exact hu (by rw [hheap]; exact hh')
      refine ⟨by omega, by omega, by omega, ?_, hU⟩
      intro fd hfd
      obtain ⟨g, hg, hgo⟩ := hfs fd hfd
      obtain ⟨ho, heq⟩ := hgo
      have := entEqMod_sound heq hh
      obtain ⟨k1, k2, k3⟩ := hf g hg
      refine ⟨by rw [← ho]; omega, by rw [← ho, ← e1]; exact k2, ?_⟩
      rw [← ho, ← e1]
      exact (k3.congr' (by simpa using this))
    · rename_i t t' hb hb'
      simp at hk; subst hk; simp only [hb] at hv; simp only [hb']; exact hv
    · cases hk

end STy

/-- Lemma 4 (weakening): an edge check carries the invariant to the target's type. -/
theorem Inv.sub {f : Fn} {T : TokEnv} {P : Perm} {s0 : State} {ι0 : Val} {S S' : STy} {s : State}
    {ι : Val} {F : TokFp} {θ : Subst} (hI : Inv f T P s0 ι0 S s ι F) (hs : S.sub θ S' = true)
    (hθ : ∀ p ∈ θ, p.1 ∉ f.protectedVars) : Inv f T P s0 ι0 S' s (IExpr.upd ι θ) F := by
  unfold STy.sub at hs
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true] at hs
  obtain ⟨⟨⟨⟨⟨⟨hfacts, hregs⟩, hid'⟩, hid⟩, hcaps⟩, hdep⟩, hslots⟩ := hs
  simp only [beq_iff_eq] at hdep
  have hh := hI.hyps
  -- every capability of S' comes from one of S
  have hcap : ∀ c' ∈ S'.caps, ∃ c ∈ S.caps, c.id = c'.id ∧ c'.cap.exclusive = c.cap.exclusive ∧
      (∀ x, c'.cap.fp (IExpr.upd ι θ) F x → c.cap.fp ι F x) ∧
      (∀ m, c.cap.valid T ι F m → c'.cap.valid T (IExpr.upd ι θ) F m) := by
    intro c' hc'
    obtain ⟨c, hc, h⟩ := hcaps c' hc'
    exact ⟨c, hc, STy.capSub_sound h hh⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hdep ▸ hI.sp, hI.live, hdep ▸ hI.depth, ?_, hI.stackW,
    hI.spAl, hI.stackLe⟩
  · intro p hp
    have := hI.ent (hfacts p hp)
    simpa [Constr.holds] using this
  · intro p hp
    have := hregs p hp
    split at this
    · rename_i e he
      have h1 := STy.reg_hasInt hI.regs he
      have h2 := STy.entEqMod_sound this hh
      exact h1.congr' (by simpa using h2)
    · cases this
  · intro x hx
    rw [upd_of_not_mem (fun p hp e => hθ p hp (e ▸ hx))]
    exact hI.prot x hx
  · intro c' hc'
    obtain ⟨c, hc, -, -, -, hv⟩ := hcap c' hc'
    exact hv _ (hI.valid c hc)
  · intro c' hc' d' hd' hne hex x hx hy
    obtain ⟨c, hc, hic, hec, hfc, -⟩ := hcap c' hc'
    obtain ⟨d, hd, hid, -, hfd, -⟩ := hcap d' hd'
    exact hI.sep c hc d hd (by rw [hic, hid]; exact hne) (hec ▸ hex) x (hfc x hx) (hfd x hy)
  · intro c' hc' x hx
    obtain ⟨c, hc, -, -, hfc, -⟩ := hcap c' hc'
    rw [hdep]; exact hI.stack c hc x (hfc x hx)
  · intro c' hc' x hx
    obtain ⟨c, hc, -, hec, hfc, -⟩ := hcap c' hc'
    obtain ⟨h1, h2⟩ := hI.perm c hc x (hfc x hx)
    exact ⟨h1, fun he => h2 (hec ▸ he)⟩
  · simpa using hid'
  · intro p hp
    have := hslots p hp
    split at this
    · rename_i e he
      obtain ⟨h1, h3, h2⟩ := hI.slots _ (lookup_mem he)
      rw [hdep]
      refine ⟨h1, h3, h2.congr' (by simpa using STy.entEqMod_sound this hh)⟩
    · cases this

end NoCompiler.Typed
