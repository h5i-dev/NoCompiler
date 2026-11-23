import NoCompiler.Typed.Sound.CallSpec

/-
Calls: the callee's parameters and `out` variables at the caller (instantiation and renaming).
-/
namespace NoCompiler.Typed

variable {f : Fn} {T : TokEnv} {P : Perm} {s0 : State} {ι0 : Val}

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
    · simp only [Option.map_eq_some_iff] at this
      obtain ⟨c, -, hpe⟩ := this
      rw [← hpe]; exact ⟨List.getElem_mem _, by simp [IExpr.lit, IExpr.maxVar]⟩
  · intro y hy
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
    have := hget i hi (by omega)
    split at this
    · simp only [Option.map_eq_some_iff] at this
      obtain ⟨e, -, hpe⟩ := this
      exact lookup_some_of_mem (b := e) (by rw [hpe]; exact List.getElem_mem _)
    · simp only [Option.map_eq_some_iff] at this
      obtain ⟨c, -, hpe⟩ := this
      exact lookup_some_of_mem (b := IExpr.lit c) (by rw [hpe]; exact List.getElem_mem _)

/-- After the call, the callee's `out` variables are the renamed fresh ones. -/
theorem eval_rename {θ : Subst} {S : STy} {g : Sig}
    (hθ1 : ∀ p ∈ θ, p.1 ∈ g.params ∧ p.2.maxVar ≤ S.maxVar)
    (hθ2 : ∀ y ∈ g.params, ∃ e, θ.lookup y = some e) (hok : CalleeSpec g)
    {ι ιg' : Val} {x : Nat} {extra : List Int} (hx : S.maxVar < x)
    (hag : ∀ y, y ∉ g.outVars → ιg' y = IExpr.upd ι θ y) {e : IExpr}
    (he : ∀ y ∈ e.vars, y ∈ g.params ∨ y ∈ g.outVars) :
    (e.subst (θ ++ g.outVars.zipIdx.map fun p => (p.1, IExpr.var (x + p.2)))).eval
      (setFrom ι x (g.outVars.map ιg' ++ extra)) = e.eval ιg' := by
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
    rw [setFrom_at i (by simp; omega)]
    simp [List.getElem?_append_left (show i < (g.outVars.map ιg').length by simpa using hi),
      List.getElem?_eq_getElem hi]

theorem upd_rename {θ : Subst} {S : STy} {g : Sig}
    (hθ1 : ∀ p ∈ θ, p.1 ∈ g.params ∧ p.2.maxVar ≤ S.maxVar)
    (hθ2 : ∀ y ∈ g.params, ∃ e, θ.lookup y = some e) (hok : CalleeSpec g)
    {ι ιg' : Val} {x : Nat} {extra : List Int} (hx : S.maxVar < x)
    (hag : ∀ y, y ∉ g.outVars → ιg' y = IExpr.upd ι θ y) (y : Var)
    (hy : y ∈ g.params ∨ y ∈ g.outVars) :
    IExpr.upd (setFrom ι x (g.outVars.map ιg' ++ extra))
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
    rw [setFrom_at i (by simp; omega)]
    simp [List.getElem?_append_left (show i < (g.outVars.map ιg').length by simpa using hi),
      List.getElem?_eq_getElem hi]

theorem Cap.subst_fp {c : Cap} {b : BytesCap} (hk : c.kind = .bytes b) (ρ : Subst) (ι : Val)
    (F F' : TokFp) (z : Word) : (c.subst ρ).fp ι F z ↔ c.fp (IExpr.upd ι ρ) F' z := by
  unfold Cap.subst Cap.fp Cap.regions
  rw [hk]
  simp only [Constr.eval_subst]
  simp [BytesCap.region, IExpr.eval_subst]

theorem Cap.subst_valid {T : TokEnv} {c : Cap} {b : BytesCap} (hk : c.kind = .bytes b) (hf : b.fields = [])
    (ρ : Subst) (ι : Val) (F F' : TokFp) (m : Word → Byte) :
    (c.subst ρ).valid T ι F m ↔ c.valid T (IExpr.upd ι ρ) F' m := by
  unfold Cap.subst Cap.valid
  rw [hk]
  simp [Constr.holds, Constr.eval_subst, IExpr.eval_subst, hf]

theorem Cap.subst_exclusive (c : Cap) (ρ : Subst) : (c.subst ρ).exclusive = c.exclusive := by
  unfold Cap.subst Cap.exclusive
  cases c.kind <;> rfl

end NoCompiler.Typed
