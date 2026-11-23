import NoCompiler.Typed.Sound.Rank

/-
Changing the valuation where a type does not look: fresh variables (above `maxVar`)
can be set freely without disturbing the invariant.
-/
namespace NoCompiler.Typed

theorem foldr_max_le {α : Type} (g : α → Nat) : ∀ (l : List α) (a : α), a ∈ l →
    g a ≤ l.foldr (fun t m => max (g t) m) 0
  | [], _, h => by simp at h
  | b :: r, a, h => by
    simp only [List.mem_cons] at h; simp only [List.foldr_cons]
    rcases h with h | h
    · subst h; omega
    · have := foldr_max_le g r a h; omega

theorem IExpr.le_maxVar {e : IExpr} {x : Nat} (h : x ∈ e.vars) : x ≤ e.maxVar := by
  unfold vars at h; unfold maxVar
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 h
  exact foldr_max_le (·.2) _ t ht

theorem Constr.eval_congr {ι ι' : Val} : ∀ (p : Constr), (∀ x ∈ p.vars, ι x = ι' x) →
    p.eval ι = p.eval ι'
  | .tt, _ | .ff, _ => rfl
  | .le a b, h | .eq a b, h => by
    simp only [vars, List.mem_append] at h
    simp only [eval, IExpr.eval_congr a (fun x hx => h x (.inl hx)),
      IExpr.eval_congr b (fun x hx => h x (.inr hx))]
  | .dvd c e, h => by simp only [vars] at h; simp only [eval, IExpr.eval_congr e h]
  | .and p q, h | .or p q, h => by
    simp only [vars, List.mem_append] at h
    simp only [eval, Constr.eval_congr p (fun x hx => h x (.inl hx)),
      Constr.eval_congr q (fun x hx => h x (.inr hx))]
  | .not p, h => by simp only [vars] at h; simp only [eval, Constr.eval_congr p h]

theorem Constr.le_maxVar : ∀ {p : Constr} {x : Nat}, x ∈ p.vars → x ≤ p.maxVar
  | .tt, _, h | .ff, _, h => by simp [vars] at h
  | .le a b, _, h | .eq a b, _, h => by
    simp only [vars, List.mem_append] at h; simp only [maxVar]
    rcases h with h | h
    · have := IExpr.le_maxVar h; omega
    · have := IExpr.le_maxVar h; omega
  | .dvd _ e, _, h => IExpr.le_maxVar h
  | .and p q, _, h | .or p q, _, h => by
    simp only [vars, List.mem_append] at h; simp only [maxVar]
    rcases h with h | h
    · have := Constr.le_maxVar h; omega
    · have := Constr.le_maxVar h; omega
  | .not p, _, h => Constr.le_maxVar (p := p) h

theorem Constr.holds_congr {ι ι' : Val} {p : Constr} (h : ∀ x ≤ p.maxVar, ι x = ι' x) :
    p.holds ι ↔ p.holds ι' := by
  unfold holds; rw [Constr.eval_congr p (fun x hx => h x (Constr.le_maxVar hx))]

theorem IExpr.eval_congr_max {ι ι' : Val} {e : IExpr} (h : ∀ x ≤ e.maxVar, ι x = ι' x) :
    e.eval ι = e.eval ι' := IExpr.eval_congr e (fun x hx => h x (IExpr.le_maxVar hx))

namespace STy

theorem capMaxVar_bytes {c : HCap} {b : BytesCap} (hk : c.cap.kind = .bytes b) :
    capMaxVar c = max c.cap.guard.maxVar
      (max b.base.maxVar (max b.len.maxVar (b.fields.foldr (fun f m => max f.ty.maxVar m) 0))) := by
  simp [capMaxVar, hk]

theorem le_maxVar_reg {S : STy} {p : Reg × IExpr} (hp : p ∈ S.regs) : p.2.maxVar ≤ S.maxVar := by
  unfold maxVar; have := foldr_max_le (fun p : Reg × IExpr => p.2.maxVar) _ p hp; omega

theorem le_maxVar_fact {S : STy} {p : Constr} (hp : p ∈ S.facts) : p.maxVar ≤ S.maxVar := by
  unfold maxVar; have := foldr_max_le Constr.maxVar _ p hp; omega

theorem le_maxVar_cap {S : STy} {c : HCap} (hc : c ∈ S.caps) : capMaxVar c ≤ S.maxVar := by
  unfold maxVar; have := foldr_max_le capMaxVar _ c hc; omega

end STy

/-- A capability's meaning depends only on the variables it mentions. -/
theorem Cap.congr {T : TokEnv} {ι ι' : Val} {F : TokFp} {c : HCap}
    (h : ∀ x ≤ STy.capMaxVar c, ι x = ι' x) :
    (∀ x, c.cap.fp ι F x ↔ c.cap.fp ι' F x) ∧ (∀ m, c.cap.valid T ι F m ↔ c.cap.valid T ι' F m) := by
  have hg : c.cap.guard.eval ι = c.cap.guard.eval ι' :=
    Constr.eval_congr _ (fun x hx => h x (by
      unfold STy.capMaxVar; exact Nat.le_trans (Constr.le_maxVar (x := x) hx) (Nat.le_max_left _ _)))
  cases hk : c.cap.kind with
  | token t =>
    refine ⟨fun x => ?_, fun m => ?_⟩
    · simp [Cap.fp, Cap.regions, hk, hg]
    · simp [Cap.valid, hk, Constr.holds, hg]
  | bytes b =>
    have hcm := STy.capMaxVar_bytes hk
    have hm : ∀ x : Nat, (x ∈ b.base.vars ∨ x ∈ b.len.vars) → ι x = ι' x := by
      intro x hx; apply h
      rcases hx with hx | hx
      · have := IExpr.le_maxVar hx; omega
      · have := IExpr.le_maxVar hx; omega
    have hb := IExpr.eval_congr b.base (fun x hx => hm x (.inl hx))
    have hl := IExpr.eval_congr b.len (fun x hx => hm x (.inr hx))
    have hf : ∀ fd ∈ b.fields, ∀ x : Nat, x ∈ fd.ty.vars → ι x = ι' x := by
      intro fd hfd x hx; apply h
      have h1 := IExpr.le_maxVar hx
      have h2 := foldr_max_le (fun f : Field => f.ty.maxVar) _ fd hfd
      omega
    refine ⟨fun x => ?_, fun m => ?_⟩
    · simp [Cap.fp, Cap.regions, hk, hg, BytesCap.region, hb, hl]
    · simp only [Cap.valid, hk, Constr.holds, hg, hb, hl]
      constructor
      · intro hv hg'
        obtain ⟨a, b', c', d⟩ := hv hg'
        refine ⟨a, b', c', fun fd hfd => ?_⟩
        obtain ⟨e1, e2, e3⟩ := d fd hfd
        refine ⟨by simpa [Cap.Field.holds, hl] using e1, by simpa [hb] using e2, ?_⟩
        rw [← hb]; exact e3.of_eq (IExpr.eval_congr _ (hf fd hfd))
      · intro hv hg'
        obtain ⟨a, b', c', d⟩ := hv hg'
        refine ⟨a, b', c', fun fd hfd => ?_⟩
        obtain ⟨e1, e2, e3⟩ := d fd hfd
        refine ⟨by simpa [Cap.Field.holds, hl] using e1, by simpa [hb] using e2, ?_⟩
        rw [hb]; exact e3.of_eq (IExpr.eval_congr _ (hf fd hfd)).symm

/-- The invariant depends on the valuation only at the type's variables and the
    protected ones. -/
theorem Inv.congr {f : Fn} {T : TokEnv} {P : Perm} {s0 : State} {ι0 : Val} {S : STy}
    {s : State} {ι ι' : Val} {F : TokFp} (hI : Inv f T P s0 ι0 S s ι F)
    (h : ∀ x ≤ S.maxVar, ι' x = ι x) (hp : ∀ x ∈ f.protectedVars, ι' x = ι x) :
    Inv f T P s0 ι0 S s ι' F := by
  have hcap : ∀ c ∈ S.caps, (∀ x, c.cap.fp ι F x ↔ c.cap.fp ι' F x) ∧
      (∀ m, c.cap.valid T ι F m ↔ c.cap.valid T ι' F m) := fun c hc =>
    Cap.congr (fun x hx => (h x (Nat.le_trans hx (STy.le_maxVar_cap hc))).symm)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hI.ids, hI.sp, hI.live⟩
  · intro p hp'
    exact (Constr.holds_congr (fun x hx => (h x (Nat.le_trans hx (STy.le_maxVar_fact hp'))).symm)).1
      (hI.facts p hp')
  · intro p hp'
    exact (hI.regs p hp').of_eq (IExpr.eval_congr_max
      (fun x hx => (h x (Nat.le_trans hx (STy.le_maxVar_reg hp'))).symm))
  · intro x hx; rw [hp x hx]; exact hI.prot x hx
  · intro c hc; exact ((hcap c hc).2 _).1 (hI.valid c hc)
  · intro c hc d hd hne hex x hx hy
    exact hI.sep c hc d hd hne hex x (((hcap c hc).1 x).2 hx) (((hcap d hd).1 x).2 hy)
  · intro c hc x hx; exact hI.stack c hc x (((hcap c hc).1 x).2 hx)
  · intro c hc x hx; exact hI.perm c hc x (((hcap c hc).1 x).2 hx)

end NoCompiler.Typed
