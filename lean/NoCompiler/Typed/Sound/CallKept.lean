import NoCompiler.Typed.Sound.CallFresh

/-
Lemma 8.3, the caller's side: what a callee may write (the ranges and tokens lent to it,
and its own stack), so what stays unchanged in the caller's capabilities and slots.
-/
namespace NoCompiler.Typed

variable {f : Fn} {T : TokEnv} {P : Perm} {s0 : State} {ι0 : Val}

/-- What the callee may write: a clause lent `rw` (a byte range or a token), or its stack. -/
theorem Fn.callee_writes (hst : f.StructSpec) {S : STy} {s : State} {ι : Val} {Ft : TokFp}
    (hI : Inv f T P s0 ι0 S s ι Ft) {g : Sig} (hok : CalleeSpec g) {θ : Subst}
    (hstk : S.depth + g.stack ≤ f.sig.stack)
    {ls : List (BytesCap × HCap)} (hls : Fn.lends S g θ = some ls)
    {s1 : State} (hregs : ∀ r : Reg, r ≠ 1 → s1.reg r = s.reg r) (z : Word)
    (hz : ((g.spec T).perm (IExpr.upd ι θ, Ft) s1).writable z) :
    (∃ i, ∃ hi : i < ls.length, ls[i].1.mode = .rw ∧ ls[i].2.cap.fp ι Ft z ∧ ls[i].2 ∈ S.caps ∧
        ls[i].2.cap.exclusive = true) ∨
      (z.toNat < (s0.reg Reg.sp).toNat - S.depth ∧ (Spec.stackRegion s0 f.sig.stack).mem z) := by
  have hspn := hI.sp_toNat hst
  have hK := hI.stackLe
  obtain ⟨hlen, -⟩ := Fn.lends_spec hls
  obtain ⟨r, hr, hm⟩ := hz
  simp only [Sig.spec, Spec.perm, List.mem_append, List.mem_singleton] at hr
  rcases hr with hr | hr
  · left
    simp only [Sig.writeRegions, List.mem_flatMap, List.mem_filter] at hr
    obtain ⟨c, ⟨hc, hex⟩, hrc⟩ := hr
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
    have hl : i < ls.length := by omega
    have hfz := clause_sub hok hls hI.hyps hI.valid hi hl z ⟨r, hrc, hm⟩
    rcases (Fn.lends_spec hls).2 i hi hl with ⟨xb, hk, he, hlf⟩ | ⟨t, hk, he, hlt⟩
    · obtain ⟨hmc, -⟩ := Fn.lendFrom_spec hlf
      obtain ⟨hb', hkb, hmode, -⟩ := lend_region hI.hyps (hI.valid _ hmc) hlf
      have hrw : xb.mode = .rw := by simpa [Cap.exclusive, hk] using hex
      have hrw' : ls[i].1.mode = .rw := by rw [he]; exact hrw
      refine ⟨i, hl, hrw', hfz, hmc, ?_⟩
      rcases hmode with h | h
      · rw [hrw'] at h; cases h
      · simp [Cap.exclusive, hkb, h]
    · obtain ⟨hmc, hkc, -⟩ := Fn.lendTok_spec hlt
      exact ⟨i, hl, by rw [he]; rfl, hfz, hmc, by simp [Cap.exclusive, hkc]⟩
  · right
    subst hr
    have hsp1 : (s1.reg Reg.sp).toNat = (s0.reg Reg.sp).toNat - S.depth := by
      rw [hregs _ (by decide)]; exact hspn.1
    rw [stack_mem_iff s1 g.stack (by omega) z, hsp1] at hm
    exact ⟨hm.2, (stack_mem_iff s0 _ hK z).2 ⟨by omega, by omega⟩⟩

end NoCompiler.Typed

namespace NoCompiler.Typed

variable {f : Fn} {T : TokEnv} {P : Perm} {s0 : State} {ι0 : Val}

/-- A capability no clause was lent `rw` from keeps its bytes across the call. -/
theorem Fn.unlent_unchanged (hst : f.StructSpec) {S : STy} {s : State} {ι : Val} {Ft : TokFp}
    (hI : Inv f T P s0 ι0 S s ι Ft) {g : Sig} (hok : CalleeSpec g) {θ : Subst}
    (hstk : S.depth + g.stack ≤ f.sig.stack)
    {ls : List (BytesCap × HCap)} (hls : Fn.lends S g θ = some ls)
    {s1 s2 : State} (hregs : ∀ r : Reg, r ≠ 1 → s1.reg r = s.reg r) (hmem : s1.mem = s.mem)
    (hframe : ∀ x, ¬ ((g.spec T).perm (IExpr.upd ι θ, Ft) s1).writable x → s2.mem x = s1.mem x)
    {c : HCap} (hc : c ∈ S.caps) (hnl : ∀ p ∈ ls, p.1.mode = .rw → p.2.id ≠ c.id)
    (z : Word) (hz : c.cap.fp ι Ft z) : s2.mem z = s.mem z := by
  have hK := hI.stackLe
  rw [← hmem]
  refine hframe z fun hzw => ?_
  rcases f.callee_writes hst hI hok hstk hls hregs z hzw with ⟨i, hi, hrw, hfp, hm, hex⟩ | ⟨hlt, hS0⟩
  · exact hI.sep _ hm c hc (hnl _ (List.getElem_mem hi) hrw) hex z hfp hz
  · obtain ⟨Fr, hfr, hd, hF0, r, hr, h1, h2⟩ := hI.stack c hc z hz hS0
    have hg := f.frame_geom hst.frameDecl hfr
    have := (inFrame_iff hfr (hd ▸ hF0) s0 (by have := hg.sizeLe; omega) hg.addr z).1
      (hd ▸ hI.stack c hc z hz hS0)
    rw [← hd] at this; omega

/-- A held capability that is not one of the callee's tokens, after the call: the same
    identity, footprint and exclusivity; valid (its fields forgotten if lent `rw`). -/
theorem Fn.kept_cap (hst : f.StructSpec) {S : STy} {s : State} {ι : Val} {Ft : TokFp}
    (hI : Inv f T P s0 ι0 S s ι Ft) {g : Sig} (hok : CalleeSpec g) {θ : Subst}
    (hstk : S.depth + g.stack ≤ f.sig.stack)
    {ls : List (BytesCap × HCap)} (hls : Fn.lends S g θ = some ls)
    {s1 s2 : State} (hregs : ∀ r : Reg, r ≠ 1 → s1.reg r = s.reg r) (hmem : s1.mem = s.mem)
    (hframe : ∀ x, ¬ ((g.spec T).perm (IExpr.upd ι θ, Ft) s1).writable x → s2.mem x = s1.mem x)
    {ι' : Val} (g1 : ∀ y : Nat, y ≤ S.maxVar → ι' y = ι y)
    {c0 : HCap} (hc0 : c0 ∈ S.caps) (hnt : ¬ ∃ t, c0.cap.kind = .token t ∧ t ∈ g.tokNames) :
    (Fn.clearLent ls c0).id = c0.id ∧
      (Fn.clearLent ls c0).cap.exclusive = c0.cap.exclusive ∧
      (∀ z, (Fn.clearLent ls c0).cap.fp ι' Ft z ↔ c0.cap.fp ι Ft z) ∧
      (Fn.clearLent ls c0).cap.valid T ι' Ft s2.mem := by
  have hcapw := fun c hc hnl z hz => f.unlent_unchanged hst hI hok hstk hls hregs hmem hframe
    (c := c) hc hnl z hz
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
        intro hg; obtain ⟨a0, a1, a2, -, hu⟩ := hv hg
        exact ⟨a0, a1, a2, by simp, hu⟩
    | token t =>
      simp only
      refine ⟨by simp, by simp, fun z => (hcg.1 z).symm, ?_⟩
      refine (hcg.2 _).1 (Cap.valid_congr (hI.valid c0 hc0) (fun z hz => ?_))
      -- not one of the callee's tokens: no clause is lent from it
      rw [hcapw c0 hc0 (fun p hp hrw e => ?_) z hz]
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
      obtain ⟨hlen, hget⟩ := Fn.lends_spec hls
      have hie : i < g.entryCaps.length := by omega
      rcases hget i hie hi with ⟨xb, -, -, hlf⟩ | ⟨t', hkt, -, hlt⟩
      · obtain ⟨hmc, -, hb, hkb, -⟩ := Fn.lendFrom_spec hlf
        have := eq_of_id_eq hI.ids hmc hc0 e
        rw [this, hk] at hkb; cases hkb
      · obtain ⟨hmc, hkc, -⟩ := Fn.lendTok_spec hlt
        have := eq_of_id_eq hI.ids hmc hc0 e
        rw [this, hk] at hkc
        cases hkc
        exact hnt ⟨_, hk, List.mem_filterMap.2 ⟨_, List.getElem_mem hie, by simp [hkt]⟩⟩
  · rename_i hl
    simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq, not_exists, not_and] at hl
    refine ⟨by simp, by simp, fun z => (hcg.1 z).symm, (hcg.2 _).1
      (Cap.valid_congr (hI.valid c0 hc0) (fun z hz => (hcapw c0 hc0 ?_ z hz).symm))⟩
    intro p hp hrw e
    exact hl p hp e hrw

end NoCompiler.Typed
