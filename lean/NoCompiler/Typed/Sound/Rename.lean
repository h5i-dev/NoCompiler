import NoCompiler.Typed.Sound.CallTok

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

theorem Cap.subst_valid {T : TokEnv} {c : Cap} {b : BytesCap} (hk : c.kind = .bytes b)
    (ρ : Subst) (ι : Val) (F F' : TokFp) (hF : b.heap = true → F heapTok = F' heapTok)
    (m : Word → Byte) :
    (c.subst ρ).valid T ι F m ↔ c.valid T (IExpr.upd ι ρ) F' m := by
  unfold Cap.subst Cap.valid
  rw [hk]
  by_cases hh : b.heap = true
  · simp [Constr.holds, Constr.eval_subst, IExpr.eval_subst, Cap.Field.holds, HasInt, hF hh, BytesCap.region]
  · simp [Constr.holds, Constr.eval_subst, IExpr.eval_subst, Cap.Field.holds, HasInt, hh]

/-- Translating fields to the caller's offsets preserves their memory meaning. -/
theorem Cap.restoreFields_valid {T : TokEnv} {ι : Val} {F F' : TokFp} {m : Word → Byte}
    {held returned : Cap} {h r : BytesCap} {offset : Nat}
    (hh : held.kind = .bytes h) (hr : returned.kind = .bytes r)
    (hb : r.base.eval ι = h.base.eval ι + offset)
    (hl : r.len.eval ι + offset ≤ h.len.eval ι)
    (hg : returned.guard.holds ι)
    (hv : held.valid T ι F m) (hp : returned.valid T ι F' m) :
    ({ held with kind := .bytes { h with fields := (r.fields.map fun f => { f with off := offset + f.off }) ++
      (h.fields.filter fun f => !(r.fields.map (fun x => { x with off := offset + x.off })).any (fun g => f.off == g.off)) } } : Cap).valid T ι F m := by
  unfold Cap.valid at hv hp ⊢
  rw [hh] at hv
  rw [hr] at hp
  intro guard
  obtain ⟨base, len, bounds, old, heap⟩ := hv guard
  refine ⟨base, len, bounds, ?_, heap⟩
  intro field member
  rcases List.mem_append.1 member with hm | hm
  · have hm' : ∃ orig ∈ r.fields, { orig with off := offset + orig.off } = field :=
      List.mem_map.1 hm
    obtain ⟨orig, hmOrig, rfl⟩ := hm'
    obtain ⟨hsize, halign, hvalue⟩ := (hp hg).2.2.2.1 orig hmOrig
    simp only [Cap.Field.holds, Int.natCast_add] at hsize halign hvalue ⊢
    rw [hb] at halign hvalue
    rw [Int.add_assoc] at halign hvalue
    exact ⟨by omega, halign, hvalue⟩
  · exact old field (List.mem_filter.1 hm).1

theorem Fn.borrowFieldOffset_facts {held returned : BytesCap} {c : Cap} {offset : Nat}
    (hk : c.kind = .bytes returned) (hm : Fn.borrowFieldOffset held c = some offset) (ι : Val) :
    c.guard = .tt ∧ returned.base.eval ι = held.base.eval ι + offset ∧
      returned.len.eval ι + offset ≤ held.len.eval ι := by
  by_cases hg : c.guard = .tt
  · cases he : returned.fields.isEmpty with
    | true => simp [Fn.borrowFieldOffset, hk, hg, he] at hm
    | false =>
      cases hoff : Fn.constOff returned.base held.base with
      | none => simp [Fn.borrowFieldOffset, hk, hg, he, hoff] at hm
      | some k =>
        cases hl : Fn.constOff held.len (returned.len.add (.lit (k : Int))) with
        | none => simp [Fn.borrowFieldOffset, hk, hg, he, hoff, hl] at hm
        | some extra =>
          simp [Fn.borrowFieldOffset, hk, hg, he, hoff, hl] at hm
          subst offset
          have hlen := constOff_sound hl ι
          simp only [IExpr.eval_add, IExpr.eval_lit] at hlen
          exact ⟨hg, constOff_sound hoff ι, by omega⟩
  · simp [Fn.borrowFieldOffset, hk, hg] at hm

theorem Fn.restoreBorrowOne_valid {T : TokEnv} {ι : Val} {F F' : TokFp} {m : Word → Byte}
    {out : Cap} {c : HCap} (hv : c.cap.valid T ι F m) (hp : out.valid T ι F' m) :
    (Fn.restoreBorrowOne out c).cap.valid T ι F m := by
  cases hk : c.cap.kind with
  | token t => simpa [Fn.restoreBorrowOne, hk] using hv
  | bytes h =>
    cases hr : out.kind with
    | token t => simpa [Fn.restoreBorrowOne, hk, hr] using hv
    | bytes r =>
      cases hOff : Fn.borrowFieldOffset h out with
      | none => simpa [Fn.restoreBorrowOne, hk, hr, hOff] using hv
      | some offset =>
        obtain ⟨hg, hb, hl⟩ := Fn.borrowFieldOffset_facts hr hOff ι
        simpa only [Fn.restoreBorrowOne, hk, hr, hOff] using
          (Cap.restoreFields_valid hk hr hb hl (by simp [Constr.holds, hg, Constr.eval]) hv hp)

theorem Fn.restoreBorrow_valid {T : TokEnv} {ι : Val} {F F' : TokFp} {m : Word → Byte}
    {returned : List Cap} {c : HCap} (hv : c.cap.valid T ι F m)
    (hp : ∀ out ∈ returned, out.valid T ι F' m) :
    (Fn.restoreBorrow returned c).cap.valid T ι F m := by
  induction returned with
  | nil => exact hv
  | cons out tail ih =>
    exact Fn.restoreBorrowOne_valid (ih (fun d hd => hp d (.tail out hd))) (hp out (.head tail))

theorem Fn.restoreBorrowOne_shape (out : Cap) (c : HCap) (ι : Val) (F : TokFp) :
    (Fn.restoreBorrowOne out c).id = c.id ∧
    (Fn.restoreBorrowOne out c).cap.guard = c.cap.guard ∧
    (Fn.restoreBorrowOne out c).cap.exclusive = c.cap.exclusive ∧
    (∀ z, (Fn.restoreBorrowOne out c).cap.fp ι F z ↔ c.cap.fp ι F z) := by
  cases hk : c.cap.kind with
  | token t => simp [Fn.restoreBorrowOne, hk]
  | bytes h =>
    cases hr : out.kind with
    | token t => simp [Fn.restoreBorrowOne, hk, hr]
    | bytes r =>
      cases hOff : Fn.borrowFieldOffset h out <;>
        simp [Fn.restoreBorrowOne, hk, hr, hOff, Cap.exclusive, Cap.fp, Cap.regions, BytesCap.region]

theorem Fn.restoreBorrow_shape (returned : List Cap) (c : HCap) (ι : Val) (F : TokFp) :
    (Fn.restoreBorrow returned c).id = c.id ∧
    (Fn.restoreBorrow returned c).cap.guard = c.cap.guard ∧
    (Fn.restoreBorrow returned c).cap.exclusive = c.cap.exclusive ∧
    (∀ z, (Fn.restoreBorrow returned c).cap.fp ι F z ↔ c.cap.fp ι F z) := by
  induction returned with
  | nil => exact ⟨rfl, rfl, rfl, fun _ => Iff.rfl⟩
  | cons out tail ih =>
    obtain ⟨hi, hg, he, hf⟩ := Fn.restoreBorrowOne_shape out (Fn.restoreBorrow tail c) ι F
    exact ⟨hi.trans ih.1, hg.trans ih.2.1, he.trans ih.2.2.1, fun z => (hf z).trans (ih.2.2.2 z)⟩

theorem Fn.restoreBorrow_token {returned : List Cap} {c : HCap} {t : String}
    (hk : c.cap.kind = .token t) : Fn.restoreBorrow returned c = c := by
  induction returned with
  | nil => rfl
  | cons out tail ih =>
    show Fn.restoreBorrowOne out (Fn.restoreBorrow tail c) = c
    simp [ih, Fn.restoreBorrowOne, hk]

theorem Fn.afterBorrow_token {S : STy} {g : Sig} {ρ : Subst} {ls : List (BytesCap × HCap)}
    {c : HCap} {t : String} (hk : c.cap.kind = .token t) :
    Fn.afterBorrow S g ρ ls c = c := by
  simp [Fn.afterBorrow, Fn.clearLent_token hk, Fn.restoreBorrow_token hk]

theorem Fn.restoreBorrow_kind {returned : List Cap} {c : HCap} {t : String}
    (hk : (Fn.restoreBorrow returned c).cap.kind = .token t) : c.cap.kind = .token t := by
  induction returned with
  | nil => exact hk
  | cons out tail ih =>
    apply ih
    change (Fn.restoreBorrowOne out (Fn.restoreBorrow tail c)).cap.kind = .token t at hk
    cases h : (Fn.restoreBorrow tail c).cap.kind with
    | token t' => simpa [Fn.restoreBorrowOne, h] using hk
    | bytes b =>
      cases ho : out.kind with
      | token t' => simp [Fn.restoreBorrowOne, h, ho] at hk
      | bytes r =>
        cases hm : Fn.borrowFieldOffset b out <;> simp [Fn.restoreBorrowOne, h, ho, hm] at hk

theorem Fn.afterBorrow_kind {S : STy} {g : Sig} {ρ : Subst} {ls : List (BytesCap × HCap)}
    {c : HCap} {t : String} (hk : (Fn.afterBorrow S g ρ ls c).cap.kind = .token t) :
    c.cap.kind = .token t :=
  Fn.clearLent_kind (Fn.restoreBorrow_kind hk)

theorem Cap.subst_fp_tok {c : Cap} {t : String} (hk : c.kind = .token t) (ρ : Subst) (ι : Val)
    (F : TokFp) (z : Word) : (c.subst ρ).fp ι F z ↔ c.fp (IExpr.upd ι ρ) F z := by
  unfold Cap.subst Cap.fp Cap.regions
  rw [hk]
  simp only [Constr.eval_subst]

theorem Cap.subst_valid_tok {T : TokEnv} {c : Cap} {t : String} (hk : c.kind = .token t)
    (ρ : Subst) (ι : Val) (F : TokFp) (m : Word → Byte) :
    (c.subst ρ).valid T ι F m ↔ c.valid T (IExpr.upd ι ρ) F m := by
  unfold Cap.subst Cap.valid
  rw [hk]
  simp [Constr.holds, Constr.eval_subst]

theorem Cap.subst_exclusive (c : Cap) (ρ : Subst) : (c.subst ρ).exclusive = c.exclusive := by
  unfold Cap.subst Cap.exclusive
  cases c.kind <;> rfl

end NoCompiler.Typed
