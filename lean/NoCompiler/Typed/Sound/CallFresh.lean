import NoCompiler.Typed.Sound.CallSpec

/-
Calls: what the callee returns fresh (its borrowed tokens, its given capabilities) lies, by
its Pool condition, in a held capability that was lent to it as a token or taken by it.
-/
namespace NoCompiler.Typed

variable {f : Fn} {T : TokEnv} {P : Perm} {s0 : State} {ι0 : Val}

theorem drop_all_getElem {α : Type} {ls : List α} {p : α → Bool} {n : Nat}
    (h : (ls.drop n).all p = true) {i : Nat} (hi : n ≤ i) (hl : i < ls.length) : p ls[i] = true := by
  have hm : ls[i] ∈ ls.drop n := by
    rw [List.mem_iff_getElem]
    refine ⟨i - n, by simp; omega, ?_⟩
    rw [List.getElem_drop]; simp only [Nat.add_sub_cancel' hi]
  exact List.all_eq_true.1 h _ hm

/-- A byte of the callee's Pool lies in a held capability that went to it: one a `take` clause
    was lent from, or a lent token. -/
theorem Fn.pool_in {S : STy} {s : State} {ι : Val} {Ft : TokFp} (hI : Inv f T P s0 ι0 S s ι Ft)
    {g : Sig} (hok : CalleeSpec g) {θ : Subst} {ls : List (BytesCap × HCap)}
    (hls : Fn.lends S g θ = some ls) (htx : (ls.drop g.borrow.length).all (·.2.cap.exclusive) = true)
    {z : Word} (hz : g.pool (IExpr.upd ι θ) Ft z) :
    ∃ i, ∃ hl : i < ls.length, ls[i].2 ∈ S.caps ∧ ls[i].2.cap.exclusive = true ∧ ls[i].2.cap.fp ι Ft z ∧
      (g.borrow.length ≤ i ∨ ∃ t, ls[i].2.cap.kind = .token t ∧ t ∈ g.tokNames) := by
  obtain ⟨hlen, -⟩ := Fn.lends_spec hls
  rcases hz with ⟨t, ht, htz⟩ | ⟨b, hb, htok, hbz⟩
  · obtain ⟨i', hi', rfl⟩ := List.getElem_of_mem ht
    have hi : g.borrow.length + i' < g.entryCaps.length := by simp [Sig.entryCaps]; omega
    have hl : g.borrow.length + i' < ls.length := by omega
    have e : g.entryCaps[g.borrow.length + i'] = g.take[i'] := by
      simp only [Sig.entryCaps]; rw [List.getElem_append_right (by simp)]; simp
    have hfz := clause_sub hok hls hI.hyps hI.valid hi hl z (by rw [e]; exact htz)
    have hmc : ls[g.borrow.length + i'].2 ∈ S.caps := by
      rcases (Fn.lends_spec hls).2 _ hi hl with ⟨-, -, -, hlf⟩ | ⟨_, -, -, hlt⟩
      · exact (Fn.lendFrom_spec hlf).1
      · exact (Fn.lendTok_spec hlt).1
    exact ⟨_, hl, hmc, by simpa using drop_all_getElem htx (by omega) hl, hfz, .inl (by omega)⟩
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    cases hkb : g.borrow[i].cap.kind with
    | bytes y => simp [hkb] at htok
    | token t =>
      have hie : i < g.entryCaps.length := by simp [Sig.entryCaps]; omega
      have hl : i < ls.length := by omega
      have e : g.entryCaps[i] = g.borrow[i].cap := by
        simp only [Sig.entryCaps]; rw [List.getElem_append_left (by simpa using hi)]; simp
      have hk : g.entryCaps[i].kind = .token t := by rw [e]; exact hkb
      obtain ⟨-, hlt⟩ := Fn.lends_tok hls i hie hl hk
      obtain ⟨hmc, hkc, -⟩ := Fn.lendTok_spec hlt
      have hfz := clause_sub hok hls hI.hyps hI.valid hie hl z (by rw [e]; exact hbz)
      refine ⟨i, hl, hmc, by simp [Cap.exclusive, hkc], hfz, .inr ⟨t, hkc, ?_⟩⟩
      exact List.mem_filterMap.2 ⟨_, List.getElem_mem hie, by simp [hk]⟩

theorem Fn.fresh_in {S : STy} {s : State} {ι : Val} {Ft : TokFp} (hI : Inv f T P s0 ι0 S s ι Ft)
    {g : Sig} (hok : CalleeSpec g) {θ : Subst} {ls : List (BytesCap × HCap)}
    (hls : Fn.lends S g θ = some ls) (htx : (ls.drop g.borrow.length).all (·.2.cap.exclusive) = true)
    {ιg : Val} {Fg : TokFp}
    (hpool : ∀ c ∈ g.fresh, ∀ x, c.fp ιg Fg x → g.pool (IExpr.upd ι θ) Ft x)
    {c : Cap} (hc : c ∈ g.fresh) {z : Word} (hz : c.fp ιg Fg z) :
    ∃ i, ∃ hl : i < ls.length, ls[i].2 ∈ S.caps ∧ ls[i].2.cap.exclusive = true ∧ ls[i].2.cap.fp ι Ft z ∧
      (g.borrow.length ≤ i ∨ ∃ t, ls[i].2.cap.kind = .token t ∧ t ∈ g.tokNames) :=
  f.pool_in hI hok hls htx (hpool c hc z hz)

end NoCompiler.Typed
