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

namespace Constr
@[simp] theorem eval_mkAnd (ι : Val) (p q : Constr) : (mkAnd p q).eval ι = (p.eval ι && q.eval ι) := by
  unfold mkAnd; split <;> simp_all [eval]

@[simp] theorem eval_mkOr (ι : Val) (p q : Constr) : (mkOr p q).eval ι = (p.eval ι || q.eval ι) := by
  unfold mkOr; split <;> simp_all [eval]

@[simp] theorem eval_mkNot (ι : Val) (p : Constr) : (mkNot p).eval ι = !p.eval ι := by
  unfold mkNot; split <;> simp_all [eval]

theorem eval_fold (ι : Val) (p : Constr) : p.fold.eval ι = p.eval ι := by
  induction p with
  | le a b =>
    simp only [fold]
    split
    · rename_i ht
      have he := IExpr.eval_toLin ι (b.sub a)
      simp only [Lin.eval, List.isEmpty_iff.1 ht, Lin.evalT, IExpr.eval_sub] at he
      split <;> simp [eval] <;> omega
    · rfl
  | eq a b =>
    simp only [fold]
    split
    · rename_i ht
      have he := IExpr.eval_toLin ι (a.sub b)
      simp only [Lin.eval, List.isEmpty_iff.1 ht, Lin.evalT, IExpr.eval_sub] at he
      split <;> simp [eval] <;> omega
    · rfl
  | dvd c e =>
    simp only [fold]
    split
    · rename_i ht
      have he := IExpr.eval_toLin ι e
      simp only [Lin.eval, List.isEmpty_iff.1 ht, Lin.evalT] at he
      have he' : e.eval ι = e.toLin.c := by omega
      split <;> simp_all [eval]
    · rfl
  | and p q ihp ihq => simp only [fold, eval_mkAnd, ihp, ihq, eval]
  | or p q ihp ihq => simp only [fold, eval_mkOr, ihp, ihq, eval]
  | not p ih => simp only [fold, eval_mkNot, ih, eval]
  | tt => rfl
  | ff => rfl

theorem disjuncts_holds {ι : Val} {p : Constr} (h : p.eval ι = true) :
    ∃ d ∈ p.disjuncts, d.eval ι = true := by
  induction p with
  | or p q ihp ihq =>
    simp only [eval, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨d, hd, hh⟩ := ihp h; exact ⟨d, by simp [disjuncts, hd], hh⟩
    · obtain ⟨d, hd, hh⟩ := ihq h; exact ⟨d, by simp [disjuncts, hd], hh⟩
  | _ => exact ⟨_, by simp [disjuncts], h⟩

theorem eval_of_disjunct {ι : Val} {p d : Constr} (hd : d ∈ p.disjuncts) (h : d.eval ι = true) :
    p.eval ι = true := by
  induction p with
  | or p q ihp ihq =>
    simp only [disjuncts, List.mem_append] at hd
    simp only [eval, Bool.or_eq_true]
    rcases hd with hd | hd
    · exact .inl (ihp hd)
    · exact .inr (ihq hd)
  | _ => simp only [disjuncts, List.mem_singleton] at hd; subst hd; exact h

theorem eval_of_conjunct {ι : Val} {p c : Constr} (hc : c ∈ p.conjuncts) (h : p.eval ι = true) :
    c.eval ι = true := by
  induction p with
  | and p q ihp ihq =>
    simp only [conjuncts, List.mem_append] at hc
    simp only [eval, Bool.and_eq_true] at h
    rcases hc with hc | hc
    · exact ihp hc h.1
    · exact ihq hc h.2
  | _ => simp only [conjuncts, List.mem_singleton] at hc; subst hc; exact h

theorem conjuncts_holds {ι : Val} {p : Constr} (h : ∀ c ∈ p.conjuncts, c.eval ι = true) :
    p.eval ι = true := by
  induction p with
  | and p q ihp ihq =>
    simp only [conjuncts, List.mem_append] at h
    simp only [eval, Bool.and_eq_true]
    exact ⟨ihp fun c hc => h c (.inl hc), ihq fun c hc => h c (.inr hc)⟩
  | _ => exact h _ (by simp [conjuncts])

theorem pinOf_sound {ι : Val} {p : Constr} {x : Var} {v : Int} (hp : p.pinOf = some (x, v))
    (h : p.eval ι = true) : ι x = v := by
  induction p with
  | eq a b =>
    simp only [pinOf] at hp
    simp only [eval, decide_eq_true_eq] at h
    have he := IExpr.eval_toLin ι (a.sub b)
    simp only [IExpr.eval_sub] at he
    split at hp
    · rename_i y ht
      simp only [Option.some.injEq, Prod.mk.injEq] at hp; obtain ⟨rfl, rfl⟩ := hp
      simp only [Lin.eval, ht, Lin.evalT] at he; omega
    · rename_i y ht
      simp only [Option.some.injEq, Prod.mk.injEq] at hp; obtain ⟨rfl, rfl⟩ := hp
      simp only [Lin.eval, ht, Lin.evalT] at he; omega
    · cases hp
  | and p q ihp ihq =>
    simp only [eval, Bool.and_eq_true] at h
    simp only [pinOf] at hp
    split at hp
    · rename_i r hr
      simp only [Option.some.injEq] at hp; subst hp; exact ihp hr h.1
    · exact ihq hp h.2
  | _ => simp [pinOf] at hp

theorem pins_sound {ι : Val} {p : Constr} (h : p.eval ι = true) :
    ∀ r ∈ p.pins, ι r.1 = r.2 := by
  induction p with
  | and p q ihp ihq =>
    simp only [eval, Bool.and_eq_true] at h
    intro r hr
    simp only [pins, List.mem_append] at hr
    rcases hr with hr | hr
    · exact ihp h.1 r hr
    · exact ihq h.2 r hr
  | _ =>
    intro r hr
    simp only [pins] at hr
    split at hr
    · rename_i r' hpin
      simp only [List.mem_singleton] at hr; subst hr
      exact pinOf_sound hpin h
    · simp at hr
end Constr

theorem lookup_some_mem : ∀ {l : List (Var × IExpr)} {y : Var} {e : IExpr},
    l.lookup y = some e → (y, e) ∈ l
  | [], _, _, h => by simp [List.lookup] at h
  | (a, b) :: r, y, e, h => by
    by_cases hy : y = a
    · subst hy; simp [List.lookup] at h; subst h; simp
    · have hb : (y == a) = false := by simpa using hy
      simp [List.lookup, hb] at h
      exact List.mem_cons_of_mem _ (lookup_some_mem h)

theorem IExpr.upd_pins {ι : Val} (ps : List (Var × Int)) (h : ∀ r ∈ ps, ι r.1 = r.2) :
    IExpr.upd ι (ps.map fun (x, v) => (x, IExpr.lit v)) = ι := by
  funext y
  simp only [IExpr.upd]
  split
  · rename_i e he
    obtain ⟨⟨x, v⟩, hm, hx, rfl⟩ : ∃ r ∈ ps, y = r.1 ∧ e = IExpr.lit r.2 := by
      have := lookup_some_mem he
      simp only [List.mem_map] at this
      obtain ⟨⟨x, v⟩, hm, heq⟩ := this
      simp only [Prod.mk.injEq] at heq
      exact ⟨(x, v), hm, heq.1.symm, heq.2.symm⟩
    simp only at hx; subst hx; simp [h _ hm]
  · rfl

theorem IExpr.upd_pin {ι : Val} {x : Var} {v : Int} (hx : ι x = v) :
    IExpr.upd ι [(x, .lit v)] = ι := by
  funext y
  by_cases h : y = x
  · subst h; simp [IExpr.upd, List.lookup, hx]
  · have hb : (y == x) = false := by simpa using h
    simp [IExpr.upd, List.lookup, hb]

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

theorem decide2_sound {ι : Val} {hs : List Constr} {ψ : Constr} (h : decide2 hs ψ = true)
    (hh : ∀ p ∈ hs, p.holds ι) : ψ.holds ι := by
  unfold decide2 at h
  rcases Bool.or_eq_true _ _ ▸ h with h | h
  · exact Query.decide_sound h ι fun p hp => hh p (List.mem_filter.1 hp).1
  · exact Query.decide_sound h ι hh

theorem entQ'_sound {ι : Val} {S : STy} {ψ : Constr} (h : S.entQ' ψ = true)
    (hh' : ∀ p ∈ S.hyps, p.holds ι) : ψ.holds ι := by
  have hh : ∀ p ∈ relevant S.hyps ψ, p.holds ι := fun p hp => hh' p (List.mem_filter.1 hp).1
  unfold entQ' at h
  split at h
  · rfl
  · rename_i a b
    rcases Bool.or_eq_true _ _ ▸ h with h | h
    · simp [Constr.holds, Constr.eval, IExpr.eval_of_same h ι]
    · exact decide2_sound h hh
  · rename_i c e
    rcases Bool.or_eq_true _ _ ▸ h with h | h
    · simp [Constr.holds, Constr.eval, IExpr.eval_of_same h ι]
    · exact decide2_sound h hh
  · exact decide2_sound h hh


theorem entIn_sound {ι : Val} {S : STy} {d ψ : Constr} (h : S.entIn d ψ = true)
    (hd : d.eval ι = true) (hh' : ∀ p ∈ S.hyps, p.holds ι) : ψ.holds ι := by
  unfold entIn at h
  apply Constr.conjuncts_holds
  intro c hc
  have := entQ'_sound (List.all_eq_true.1 h c hc) hh'
  simpa only [Constr.holds, Constr.eval_mkOr, Constr.eval_mkNot, hd, Bool.not_true,
    Bool.or_false] using this

theorem pinFacts_hyps {ι : Val} {S : STy} {θ : Subst} {d : Constr} (hθ : IExpr.upd ι θ = ι)
    (hd : d.eval ι = true) (hh' : ∀ p ∈ S.hyps, p.holds ι) :
    ∀ p ∈ (S.pinFacts θ d).hyps, p.holds ι := by
  intro p hp
  simp only [pinFacts, hyps, List.mem_append, List.mem_map, List.mem_cons] at hp
  rcases hp with ⟨q, hq, rfl⟩ | hp
  · simp only [Constr.holds, Constr.eval_fold, Constr.eval_subst, hθ]
    rcases hq with rfl | hq
    · exact hd
    · exact hh' q (List.mem_append_left _ hq)
  · exact hh' p (List.mem_append_right _ hp)

theorem entCaseN_sound : ∀ (n : Nat) {ι : Val} {S : STy} {ψ : Constr}, entCaseN n S ψ = true →
    (∀ p ∈ S.hyps, p.holds ι) → ψ.holds ι
  | 0, _, _, _, h, _ => by simp [entCaseN] at h
  | n + 1, ι, S, ψ, h, hh' => by
    simp only [entCaseN] at h
    obtain ⟨h0, hm, hc⟩ := List.any_eq_true.1 h
    have h0h : h0.eval ι = true := hh' h0 (List.mem_append_left _ (List.mem_filter.1 hm).1)
    split at hc
    · obtain ⟨d, hd, hdh⟩ := Constr.disjuncts_holds h0h
      have hcd := List.all_eq_true.1 hc d hd
      simp only [Bool.or_eq_true] at hcd
      have hθ := IExpr.upd_pins _ (Constr.pins_sound hdh)
      have hh2 := pinFacts_hyps hθ hdh hh'
      have hd' : ((d.subst (d.pins.map fun (x, v) => (x, IExpr.lit v))).fold).eval ι = true := by
        simp only [Constr.eval_fold, Constr.eval_subst, hθ, hdh]
      have hψ : ((ψ.subst (d.pins.map fun (x, v) => (x, IExpr.lit v))).fold).holds ι := by
        rcases hcd with hc2 | hc2
        · exact entIn_sound hc2 hd' hh2
        · exact entCaseN_sound n hc2 hh2
      simpa only [Constr.holds, Constr.eval_fold, Constr.eval_subst, hθ] using hψ
    · cases hc

theorem entCase_sound {ι : Val} {S : STy} {ψ : Constr} (h : S.entCase ψ = true)
    (hh' : ∀ p ∈ S.hyps, p.holds ι) : ψ.holds ι := entCaseN_sound 2 h hh'

theorem entQ_sound {ι : Val} {S : STy} {ψ : Constr} (h : S.entQ ψ = true)
    (hh' : ∀ p ∈ S.hyps, p.holds ι) : ψ.holds ι := by
  unfold entQ at h
  rcases Bool.or_eq_true _ _ ▸ h with h | h
  · have := Constr.conjuncts_holds (ι := ι) (p := ψ.fold) fun c hc =>
      entQ'_sound (List.all_eq_true.1 h c hc) hh'
    simpa only [Constr.holds, Constr.eval_fold] using this
  · exact entCase_sound h hh'

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

theorem coversS_sound {ι : Val} : ∀ (n : Nat) {p ψ : Constr}, coversS n p ψ = true →
    p.holds ι → ψ.holds ι
  | 0, _, _, h, hp => covers_sound (by simpa only [coversS] using h) hp
  | n + 1, p, ψ, h, hp => by
    simp only [coversS, Bool.or_eq_true] at h
    rcases h with h | h
    · exact covers_sound h hp
    · split at h
      · simp only [Bool.and_eq_true] at h
        simp only [Constr.holds, Constr.eval, Bool.and_eq_true] at hp ⊢
        exact ⟨coversS_sound n h.1 hp.1, coversS_sound n h.2 hp.2⟩
      · simp only [Bool.and_eq_true] at h
        simp only [Constr.holds, Constr.eval, Bool.or_eq_true] at hp ⊢
        rcases hp with hp | hp
        · exact Or.inl (coversS_sound n h.1 hp)
        · exact Or.inr (coversS_sound n h.2 hp)
      · rename_i a b
        simp only [Constr.holds, Constr.eval, Bool.not_eq_true'] at hp ⊢
        cases hb : b.eval ι
        · rfl
        · have := coversS_sound (ι := ι) n h hb
          simp only [Constr.holds] at this
          rw [this] at hp; exact absurd hp (by decide)
      · exact absurd h (by decide)

theorem ent0_sound {ι : Val} {S : STy} {ψ : Constr} (h : S.ent0 ψ = true)
    (hh' : ∀ p ∈ S.hyps, p.holds ι) : ψ.holds ι := by
  unfold ent0 at h
  rcases Bool.or_eq_true _ _ ▸ h with h | h
  · rcases Bool.or_eq_true _ _ ▸ h with h | h
    · exact hh' ψ (List.mem_append_left _ (List.contains_iff_mem.1 h))
    · obtain ⟨p, hp, hc⟩ := List.any_eq_true.1 h
      obtain ⟨c, hcm, hc⟩ := List.any_eq_true.1 hc
      exact coversS_sound _ hc (Constr.eval_of_conjunct hcm (hh' p (List.mem_append_left _ hp)))
  · exact entQ_sound h hh'

theorem ent_sound {ι : Val} {S : STy} {ψ : Constr} (h : S.ent ψ = true)
    (hh' : ∀ p ∈ S.hyps, p.holds ι) : ψ.holds ι := by
  unfold ent at h
  rcases Bool.or_eq_true _ _ ▸ h with h | h
  · exact ent0_sound h hh'
  · split at h
    · obtain ⟨d, hd, hh⟩ := List.any_eq_true.1 h
      exact Constr.eval_of_disjunct hd (ent0_sound hh hh')
    · simp at h
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
