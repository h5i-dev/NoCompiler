import NoCompiler.Typed.Sound.CallSpec

/-
Lemma 8.1–8.2: the callee is entered in a state its signature admits, with a smaller permission.
-/
namespace NoCompiler.Typed

variable {f : Fn} {T : TokEnv} {P : Perm} {s0 : State} {ι0 : Val}

theorem filterMap_nodup_inj {α β : Type} (g : α → Option β) : ∀ (l : List α),
    (l.filterMap g).Nodup → ∀ i j (hi : i < l.length) (hj : j < l.length) (b : β),
      g l[i] = some b → g l[j] = some b → i = j
  | [], _, i, _, hi, _, _, _, _ => by simp at hi
  | a :: r, hn, i, j, hi, hj, b, h1, h2 => by
    have hn' : (r.filterMap g).Nodup := by
      cases ha : g a with
      | none => simpa [List.filterMap_cons, ha] using hn
      | some b' => simp only [List.filterMap_cons, ha, List.nodup_cons] at hn; exact hn.2
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j =>
        exfalso
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h1 h2
        simp only [List.filterMap_cons, h1, List.nodup_cons] at hn
        exact hn.1 (List.mem_filterMap.2 ⟨_, List.getElem_mem _, h2⟩)
    | succ i =>
      cases j with
      | zero =>
        exfalso
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h1 h2
        simp only [List.filterMap_cons, h2, List.nodup_cons] at hn
        exact hn.1 (List.mem_filterMap.2 ⟨_, List.getElem_mem _, h1⟩)
      | succ j =>
        simp only [List.getElem_cons_succ] at h1 h2
        exact congrArg (· + 1) (filterMap_nodup_inj g r hn' i j (by simpa using hi) (by simpa using hj) b h1 h2)

theorem Sig.tokNames_inj {g : Sig} (h : g.tokNames.Nodup) {i j : Nat} (hi : i < g.entryCaps.length)
    (hj : j < g.entryCaps.length) {t : String} (hti : g.entryCaps[i].kind = .token t)
    (htj : g.entryCaps[j].kind = .token t) : i = j :=
  filterMap_nodup_inj _ _ h i j hi hj t (by simp [hti]) (by simp [htj])

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
  have hspn := hI.sp_toNat hst
  have hsp1 : (s1.reg Reg.sp).toNat = (s0.reg Reg.sp).toNat - S.depth := by
    rw [hregs _ (by decide)]; exact hspn.1
  have hK := hI.stackLe
  -- clause i: its footprint is its instantiated range, inside the held capability
  have hcl : ∀ i (hi : i < g.entryCaps.length), ∃ hl : i < ls.length,
      (∀ x, g.entryCaps[i].fp (IExpr.upd ι θ) Ft x → ls[i].2.cap.fp ι Ft x) ∧
      ls[i].2 ∈ S.caps ∧
      (g.entryCaps[i].exclusive = true → ls[i].2.cap.exclusive = true) ∧
      g.entryCaps[i].valid T (IExpr.upd ι θ) Ft s.mem := by
    intro i hi
    have hl : i < ls.length := by omega
    have hgt := hok.clauses _ (List.getElem_mem hi)
    rcases hget i hi hl with ⟨xb, hk, he, hlf⟩ | ⟨t, hk, -, hlt⟩
    case inr =>
      -- a token clause: the held token of the same name
      obtain ⟨hm, hkc, hgc⟩ := Fn.lendTok_spec hlt
      refine ⟨hl, fun x hx => (Cap.fp_token hkc hgc ι Ft x).2 ((Cap.fp_token hk hgt _ Ft x).1 hx), hm,
        fun _ => by simp [Cap.exclusive, hkc], ?_⟩
      intro _
      have hv := hI.valid _ hm
      unfold Cap.valid at hv
      rw [hk]; rw [hkc] at hv
      exact hv (by rw [hgc]; rfl)
    obtain ⟨hm, -⟩ := Fn.lendFrom_spec hlf
    obtain ⟨hb, hkb, hmode, -, r0, r1, r2, hfp⟩ := lend_region hh (hI.valid _ hm) hlf
    -- the clause's fields: fields of the held capability at the same address
    have hf0 : ∀ fl ∈ xb.fields, Cap.Field.holds (IExpr.upd ι θ) s.mem xb fl := by
      intro fl hfl
      have hfl' := List.all_eq_true.1 (Fn.lends_fields hls i hi hl) fl (by rw [he]; exact hfl)
      unfold Fn.fieldsLent at hfl'
      rw [hkb] at hfl'
      simp only [Bool.and_eq_true] at hfl'
      obtain ⟨hlen8, hany⟩ := hfl'
      obtain ⟨fh, hfh, hadr⟩ := List.any_eq_true.1 hany
      simp only [Bool.and_eq_true] at hadr
      obtain ⟨hadr, hty⟩ := hadr
      have hv := hI.valid _ hm
      have hg := STy.ent_sound (Fn.lendFrom_spec hlf).2.1 hh
      unfold Cap.valid at hv
      rw [hkb] at hv
      obtain ⟨-, -, -, hfs⟩ := hv hg
      obtain ⟨-, hal, hread⟩ := hfs fh hfh
      have e1 := STy.ent_sound hadr hh
      have e2 := STy.ent_sound hlen8 hh
      rw [he] at e1 e2
      simp only [Constr.holds, Constr.eval, decide_eq_true_eq, IExpr.eval_add, IExpr.eval_lit,
        IExpr.eval_subst] at e1 e2
      have haddr : xb.base.eval (IExpr.upd ι θ) + fl.off = hb.base.eval ι + fh.off := by omega
      refine ⟨by omega, by rw [haddr]; exact hal, ?_⟩
      rw [haddr]
      have h3 := hread.congr (STy.entEqMod_sound hty hh)
      unfold HasInt at h3 ⊢
      rwa [IExpr.eval_subst] at h3
    refine ⟨hl, fun x hx => hfp x ((clause_fp hok hls hi hl hk x).1 hx), hm, ?_, ?_⟩
    · intro hex
      simp only [Cap.exclusive, hk, beq_iff_eq] at hex
      rw [he] at hmode; simp only at hmode
      rcases hmode with h | h
      · rw [hex] at h; cases h
      · simp [Cap.exclusive, hkb, h]
    · intro _
      rw [hk]
      rw [he] at r0 r1 r2; simp only [IExpr.eval_subst] at r0 r1 r2
      exact ⟨r0, r1, r2, hf0⟩
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
  have hentryGet : ∀ i (hi : i < g.entryCaps.length), ∃ hb : i < g.entryCaps.length,
      g.entryCaps[i] = g.entryCaps[i] := fun i hi => ⟨hi, rfl⟩
  have hentryMem : ∀ c ∈ g.entryCaps, ∃ i, ∃ hi : i < g.entryCaps.length, c = g.entryCaps[i] := by
    intro c hc
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
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
    obtain ⟨-, -, -, -, hv⟩ := hcl i hi
    rw [hmem]; exact hv
  · intro i j hi hj hne hex x hx hy
    obtain ⟨hbi, ei⟩ := hentryGet i hi
    obtain ⟨hbj, ej⟩ := hentryGet j hj
    rw [ei] at hex hx; rw [ej] at hy
    obtain ⟨hli, fi, mi, exi, -⟩ := hcl i hbi
    obtain ⟨hlj, fj, mj, -, -⟩ := hcl j hbj
    by_cases hid : ls[i].2.id = ls[j].2.id
    · -- lent from the same capability
      have hsame := eq_of_id_eq hI.ids mi mj hid
      rcases (Fn.lends_spec hls).2 i hbi hli with ⟨xi, hki, hei, hlfi⟩ | ⟨ti, hki, -, hlti⟩ <;>
        rcases (Fn.lends_spec hls).2 j hbj hlj with ⟨xj, hkj, hej, hlfj⟩ | ⟨tj, hkj, -, hltj⟩
      · -- two byte clauses: the check says the ranges are apart
        have h1 := List.all_eq_true.1 hap (ls[i], i) (mem_zipIdx_of hli)
        have h2 := List.all_eq_true.1 h1 (ls[j], j) (mem_zipIdx_of hlj)
        have hrw : xi.mode = .rw := by simpa [Cap.exclusive, hki] using hex
        obtain ⟨-, -, -, -, a0, a1, a2, -⟩ := lend_region hh (hI.valid _ mi) hlfi
        obtain ⟨-, -, -, -, b0, b1, b2, -⟩ := lend_region hh (hI.valid _ mj) hlfj
        have hxi := (clause_fp hok hls hbi hli hki x).1 hx
        have hyj := (clause_fp hok hls hbj hlj hkj x).1 hy
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
      · obtain ⟨-, -, hb, hkb, -⟩ := Fn.lendFrom_spec hlfi
        obtain ⟨-, hkt, -⟩ := Fn.lendTok_spec hltj
        rw [hsame, hkt] at hkb; cases hkb
      · obtain ⟨-, -, hb, hkb, -⟩ := Fn.lendFrom_spec hlfj
        obtain ⟨-, hkt, -⟩ := Fn.lendTok_spec hlti
        rw [← hsame, hkt] at hkb; cases hkb
      · -- two token clauses of the same held token: the same name, so the same clause
        obtain ⟨-, hkti, -⟩ := Fn.lendTok_spec hlti
        obtain ⟨-, hktj, -⟩ := Fn.lendTok_spec hltj
        rw [hsame, hktj] at hkti
        cases hkti
        exact hne (Sig.tokNames_inj hok.tokNodup hbi hbj hki hkj)
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

end NoCompiler.Typed
