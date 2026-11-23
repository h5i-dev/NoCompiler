import LPS.Bridge.RefineMmapFixed2

/-!
# Refinement for `mmap` with `MAP_FIXED`, part 3: `mmap_fixed_covers`

See `RefineMmapFixed2` for the statement's meaning and its hypotheses.
-/

namespace LPS.Bridge
open LPS.RiscvSemantics NoCompiler.Linux

theorem m_vmmaps_backing50 (a n : word) (m : Model) : m_vmmaps (with_mmap_backing 50 a n m) = m_vmmaps m := by
  simp only [with_mmap_backing, mmap_noreserve_b]; rfl

theorem m_vmmaps_replacement50 (a n : word) (m : Model) :
    m_vmmaps (with_mmap_replacement 50 a n m) = m_vmmaps m := by
  simp only [with_mmap_replacement, m_vmmaps_backing50]; rfl

/-- NoCompiler's MAP_FIXED outcomes for an aligned, non-wrapping, nonzero range below `taskSize`. -/
theorem procSpec7_mmap_fixed {k k' : Kern} {i : NoCompiler.Linux.SyscallInput} {o : Outcome}
    (h222 : i.sysno = NoCompiler.Linux.sysMmap) (hfl : i.arg 3 = mapPrivateAnonFixed)
    (hfd : i.fd 4 = 0xffffffff#64) (hoff : i.arg 5 = 0) (hlen : 0 < (i.arg 1).toNat)
    (hprot : i.arg 2 = 0 ∨ i.arg 2 = 3) (hal : (i.arg 0).toNat % 4096 = 0)
    (hw : (i.arg 0).toNat + pageUp (i.arg 1) < 2 ^ 64) (h0 : (i.arg 0).toNat ≠ 0)
    (ht : (i.arg 0).toNat + pageUp (i.arg 1) ≤ taskSize) :
    procSpec7 k i o k' ↔
      ((o = .ret { ret := i.arg 0, zeros := [(i.arg 0, pageUp (i.arg 1))] } none ∧
        k' = withProt (i.arg 2) (i.arg 0) (pageUp (i.arg 1))
          { k.unmap (i.arg 0) (pageUp (i.arg 1)) with
            maps := (i.arg 0, pageUp (i.arg 1)) :: (k.unmap (i.arg 0) (pageUp (i.arg 1))).maps }) ∨
      (o = .ret { ret := enomem } none ∧ k' = k) ∨
      (o = .ret { ret := enomem } none ∧ k' = k.unmap (i.arg 0) (pageUp (i.arg 1)))) := by
  have hn1 : ¬ (i.arg 0 = 0 ∧ i.arg 3 = mapPrivateAnon ∧ i.fd 4 = 0xffffffff#64 ∧ i.arg 5 = 0 ∧
      0 < (i.arg 1).toNat ∧ (i.arg 2).toNat < 8) := fun ⟨_, h, _⟩ => absurd (hfl.symm.trans h) (by decide)
  have hc : i.arg 3 = mapPrivateAnonFixed ∧ i.fd 4 = 0xffffffff#64 ∧ i.arg 5 = 0 ∧ 0 < (i.arg 1).toNat ∧
      (i.arg 2 = 0 ∨ i.arg 2 = 3) := ⟨hfl, hfd, hoff, hlen, hprot⟩
  rw [procSpec7_mmap h222]; unfold mmapSpec
  rw [if_neg hn1, if_pos hc]
  simp only [hal, ne_eq, not_true_eq_false, ↓reduceIte, show ¬ (2 ^ 64 ≤ (i.arg 0).toNat + pageUp (i.arg 1)) by omega,
    show ¬ ((i.arg 0).toNat = 0 ∨ taskSize < (i.arg 0).toNat + pageUp (i.arg 1)) by omega]

/-- Every outcome LPS admits for `mmap(a, len, prot, MAP_PRIVATE|MAP_ANONYMOUS|MAP_FIXED, -1, 0)`, `prot`
    PROT_NONE or PROT_READ|PROT_WRITE, `len > 0`, `a` page-aligned, is one of NoCompiler's, `KernMaps` kept. -/
theorem mmap_fixed_covers {k : Kern} {i : NoCompiler.Linux.SyscallInput} {j : SyscallInput} {m m' : Model}
    {eff : SyscallEffect} {evs : List event} (hr : InRel i j) (h222 : i.sysno = NoCompiler.Linux.sysMmap)
    (hfl : i.arg 3 = mapPrivateAnonFixed) (hfd : i.fd 4 = 0xffffffff#64) (hoff : i.arg 5 = 0)
    (hlen : 0 < (i.arg 1).toNat) (hprot : i.arg 2 = 0 ∨ i.arg 2 = 3) (hal : (i.arg 0).toNat % 4096 = 0)
    (hk : KernMaps k m) (htop : alloc_top (m_vmmaps m) ≤ (taskSize : Int))
    (hs : syscall_spec j m (Ok eff m' evs)) :
    ∃ zs k', procSpec7 k i (.ret { ret := eff.eff_ret, zeros := zs } none) k' ∧ KernMaps k' m' ∧ evs = [] := by
  have hn : bv_unsigned j.in_sysno = 222 := by rw [hr.sysno, h222]; rfl
  rw [lookup_arm_of (a := mkSpecArm 222 (fun i => mmap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3)
    (in_arg i 4) (in_arg i 5) i)) (by simp [spec_table, lookup_arm, mkSpecArm]) j hn] at hs
  change mmap_spec (in_arg j 0) (in_arg j 1) (in_arg j 2) (in_arg j 3) (in_arg j 4) (in_arg j 5) j m
    (Ok eff m' evs) at hs
  rw [hr.args 0, hr.args 1, hr.args 2, hr.args 3, hr.args 5, hfl, hoff] at hs
  have e1 : w_is0 (i.arg 1) = false := by
    apply bv_eqb_neq; intro h; rw [h] at hlen; exact absurd hlen (by decide)
  have hpe : page_round_up_Z (bv_unsigned (i.arg 1)) = (pageUp (i.arg 1) : Int) := (pageUp_eq (i.arg 1)).symm
  have hA := (i.arg 0).isLt
  -- NoCompiler's outcome in the wraparound case
  have hwrapNC : 2 ^ 64 ≤ (i.arg 0).toNat + pageUp (i.arg 1) → procSpec7 k i (.ret { ret := enomem } none) k := by
    intro hw'
    have hn1 : ¬ (i.arg 0 = 0 ∧ i.arg 3 = mapPrivateAnon ∧ i.fd 4 = 0xffffffff#64 ∧ i.arg 5 = 0 ∧
        0 < (i.arg 1).toNat ∧ (i.arg 2).toNat < 8) := fun ⟨_, h, _⟩ => absurd (hfl.symm.trans h) (by decide)
    have hc : i.arg 3 = mapPrivateAnonFixed ∧ i.fd 4 = 0xffffffff#64 ∧ i.arg 5 = 0 ∧ 0 < (i.arg 1).toNat ∧
        (i.arg 2 = 0 ∨ i.arg 2 = 3) := ⟨hfl, hfd, hoff, hlen, hprot⟩
    rw [procSpec7_mmap h222]; unfold mmapSpec
    rw [if_neg hn1, if_pos hc]
    simp only [hal, ne_eq, not_true_eq_false, ↓reduceIte, hw']
    simp
  have hN : (Z_to_bv 64 (page_round_up_Z (bv_unsigned (i.arg 1)))).toNat = pageUp (i.arg 1) ∨
      2 ^ 64 ≤ (i.arg 0).toNat + pageUp (i.arg 1) := by
    by_cases h : (pageUp (i.arg 1) : Int) < 2 ^ 64
    · left; unfold Z_to_bv; rw [hpe, BitVec.toNat_ofInt]; omega
    · right; omega
  -- the leaves
  have Lkeep : m' = m → eff.eff_ret = errno_ret ENOMEM → evs = [] →
      2 ^ 64 ≤ (i.arg 0).toNat + pageUp (i.arg 1) ∨ procSpec7 k i (.ret { ret := enomem } none) k →
      ∃ zs k', procSpec7 k i (.ret { ret := eff.eff_ret, zeros := zs } none) k' ∧ KernMaps k' m' ∧ evs = [] := by
    intro hm hret hev hp
    refine ⟨[], k, ?_, hm ▸ hk, hev⟩
    rw [hret]
    rcases hp with hp | hp
    · exact hwrapNC hp
    · exact hp
  rcases hprot with hp | hp <;> rw [hp] at hs <;>
    simp only [mmap_spec, e1] at hs <;>
    simp (config := { decide := true }) only [mapPrivateAnonFixed, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte] at hs <;>
    unfold mmap_fixed_prelude at hs
  all_goals
    by_cases hw : two_pow_64 ≤ bv_unsigned (i.arg 0) + page_round_up_Z (bv_unsigned (i.arg 1))
    · rw [if_pos hw] at hs
      obtain ⟨hret, rfl, hev⟩ := err_ret_ok hs
      have hw' : 2 ^ 64 ≤ (i.arg 0).toNat + pageUp (i.arg 1) := by
        rw [hpe] at hw; unfold two_pow_64 bv_unsigned at hw; omega
      exact Lkeep rfl hret hev (.inl hw')
    rw [if_neg hw, bind_get_model] at hs
    dsimp only at hs
    have hw' : (i.arg 0).toNat + pageUp (i.arg 1) < 2 ^ 64 := by
      rw [hpe] at hw; unfold two_pow_64 bv_unsigned at hw; omega
    have hnat : (Z_to_bv 64 (page_round_up_Z (bv_unsigned (i.arg 1)))).toNat = pageUp (i.arg 1) := by
      rcases hN with h | h
      · exact h
      · omega
    refine (Classical.em (bv_unsigned (i.arg 0) + page_round_up_Z (bv_unsigned (i.arg 1)) ≤
      alloc_top (m_vmmaps m))).elim (fun ht => ?_) (fun ht => by simp [ht, unmodeled] at hs)
    have hz : (Z.modulo (bv_unsigned (i.arg 0)) page_size == 0) = true := by
      unfold Z.modulo page_size bv_unsigned
      rw [Int.fmod_eq_emod_of_nonneg _ (by decide)]
      simp only [beq_iff_eq]; omega
    simp only [ht, hz, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hs
    refine (Classical.em (0 < bv_unsigned (i.arg 0))).elim (fun h0 => ?_) (fun h0 => by simp [h0, unmodeled] at hs)
    simp only [h0, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hs
    have htask : (i.arg 0).toNat + pageUp (i.arg 1) ≤ taskSize := by
      rw [hpe] at ht; unfold bv_unsigned at ht; unfold taskSize at htop ⊢; omega
    have hsp := fun o k' => procSpec7_mmap_fixed (k := k) (k' := k') (o := o) h222 hfl hfd hoff hlen
      (by rw [hp]; simp) hal hw' (by unfold bv_unsigned at h0; omega) htask
    have hcast : bv_unsigned (i.arg 0) + bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned (i.arg 1)))) =
        (((i.arg 0).toNat + pageUp (i.arg 1) : Nat) : Int) := by
      show ((i.arg 0).toNat : Int) + ((Z_to_bv 64 (page_round_up_Z (bv_unsigned (i.arg 1)))).toNat : Int) = _
      rw [hnat]; omega
    have Lsucc : eff.eff_ret = i.arg 0 → KernMaps (k.unmap (i.arg 0) (pageUp (i.arg 1))) m' →
        (∃ q ∈ (m_vmmaps m').vm_reserved ++ (m_vmmaps m').vm_maps,
          q.1.toNat ≤ (i.arg 0).toNat ∧ (i.arg 0).toNat + pageUp (i.arg 1) ≤ q.1.toNat + q.2.toNat) → evs = [] →
        ∃ zs k', procSpec7 k i (.ret { ret := eff.eff_ret, zeros := zs } none) k' ∧ KernMaps k' m' ∧ evs = [] := by
      intro hret hk1 hin hev
      refine ⟨[(i.arg 0, pageUp (i.arg 1))], _, (hsp _ _).2 (.inl ⟨by rw [hret], rfl⟩), ?_, hev⟩
      exact KernMaps.withProt (KernMaps.add hk1 _ hin) _ _ _
    have Ldes : m_vmmaps m' = mmap_fixed_destroyed_next (m_vmmaps m) (i.arg 0)
          (Z_to_bv 64 (page_round_up_Z (bv_unsigned (i.arg 1)))) → eff.eff_ret = errno_ret ENOMEM → evs = [] →
        ∃ zs k', procSpec7 k i (.ret { ret := eff.eff_ret, zeros := zs } none) k' ∧ KernMaps k' m' ∧ evs = [] := by
      intro hmv hret hev
      refine ⟨[], k.unmap (i.arg 0) (pageUp (i.arg 1)), (hsp _ _).2 (.inr (.inr ⟨by rw [hret]; rfl, rfl⟩)), ?_, hev⟩
      refine KernMaps.unmap_sub hk _ _ hw' (by rw [hmv]; rfl) (fun x hx => ?_)
      rw [hmv]; show x ∈ maps_subtract _ _ _; rw [hcast]; exact hx
    have hself : ∀ (ms : List (word × word)), (i.arg 0, Z_to_bv 64 (page_round_up_Z (bv_unsigned (i.arg 1)))) ∈ ms →
        ∃ q ∈ (m_vmmaps m).vm_reserved ++ ms,
          q.1.toNat ≤ (i.arg 0).toNat ∧ (i.arg 0).toNat + pageUp (i.arg 1) ≤ q.1.toNat + q.2.toNat :=
      fun ms h => ⟨_, List.mem_append_right _ h, Nat.le_refl _, by simp only [hnat]; omega⟩
  -- PROT_NONE
  · split at hs
    · rename_i hc
      rcases hs with hinj | hs | hdes
      · obtain ⟨hret, hm, hev⟩ := injected_ok hinj
        exact Lkeep hm hret hev (.inr ((hsp _ _).2 (.inr (.inl ⟨rfl, rfl⟩))))
      · obtain ⟨u, m1, e1, e2, h1, h2, rfl⟩ := hs
        cases h1; cases h2
        simp only [Bool.and_eq_true] at hc
        obtain ⟨q, hq, hq1, hq2⟩ := map_contains_some hc.2
        refine Lsucc rfl (KernMaps.unmap_keep hk _ _ hw' (fun x hx => by rw [m_vmmaps_replacement50]; exact hx))
          ⟨q, by rw [m_vmmaps_replacement50]; exact List.mem_append_right _ hq, hq1, by rw [hnat] at hq2; exact hq2⟩ rfl
      · obtain ⟨hret, hmv, hev⟩ := destroy_ok hdes
        exact Ldes hmv hret hev
    · split at hs
      · rcases hs with hinj | hs
        · obtain ⟨hret, hm, hev⟩ := injected_ok hinj
          exact Lkeep hm hret hev (.inr ((hsp _ _).2 (.inr (.inl ⟨rfl, rfl⟩))))
        · obtain ⟨a, m1, e1, e2, ⟨a', ha, h1⟩, h2, rfl⟩ := hs
          cases h1; subst ha
          obtain ⟨u, m2, e3, e4, h3, h4, rfl⟩ := h2
          cases h3; cases h4
          refine Lsucc rfl (KernMaps.unmap_keep hk _ _ hw' (fun x hx => ?_))
            (by rw [m_vmmaps_backing50]; exact hself _ List.mem_cons_self) rfl
          rw [m_vmmaps_backing50]
          rcases List.mem_append.1 hx with h | h
          · exact List.mem_append_left _ h
          · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
      · split at hs
        · rcases hs with hinj | hs | hdes
          · obtain ⟨hret, hm, hev⟩ := injected_ok hinj
            exact Lkeep hm hret hev (.inr ((hsp _ _).2 (.inr (.inl ⟨rfl, rfl⟩))))
          · obtain ⟨u, m1, e1, e2, h1, h2, rfl⟩ := hs
            cases h1; cases h2
            refine Lsucc rfl (KernMaps.unmap_sub hk _ _ hw' (by rw [m_vmmaps_replacement50]; rfl) (fun x hx => ?_))
              (by rw [m_vmmaps_replacement50]; exact hself _ List.mem_cons_self) rfl
            rw [m_vmmaps_replacement50]
            show x ∈ (_ :: maps_subtract _ _ _)
            rw [hcast]; exact List.mem_cons_of_mem _ hx
          · obtain ⟨hret, hmv, hev⟩ := destroy_ok hdes
            exact Ldes hmv hret hev
        · simp [unmodeled] at hs
  -- PROT_READ|PROT_WRITE
  · split at hs
    · rename_i hc
      rcases hs with hinj | hs | hdes
      · obtain ⟨hret, hm, hev⟩ := injected_ok hinj
        exact Lkeep hm hret hev (.inr ((hsp _ _).2 (.inr (.inl ⟨rfl, rfl⟩))))
      · obtain ⟨u0, m0, e0, e1', ⟨u0', -, h0⟩, hs2, rfl⟩ := hs
        cases h0
        obtain ⟨u, m1, e1, e2, h1, h2, rfl⟩ := hs2
        cases h1; cases h2
        simp only [Bool.and_eq_true] at hc
        obtain ⟨q, hq, hq1, hq2⟩ := map_contains_some hc.2
        refine Lsucc rfl (KernMaps.unmap_keep hk _ _ hw' (fun x hx => by rw [m_vmmaps_replacement50]; exact hx))
          ⟨q, by rw [m_vmmaps_replacement50]; exact List.mem_append_right _ hq, hq1, by rw [hnat] at hq2; exact hq2⟩ rfl
      · obtain ⟨hret, hmv, hev⟩ := destroy_ok hdes
        exact Ldes hmv hret hev
    · split at hs
      · rcases hs with hinj | hs
        · obtain ⟨hret, hm, hev⟩ := injected_ok hinj
          exact Lkeep hm hret hev (.inr ((hsp _ _).2 (.inr (.inl ⟨rfl, rfl⟩))))
        · obtain ⟨a, m1, e1, e2, ⟨a', ha, h1⟩, h2, rfl⟩ := hs
          cases h1; obtain ⟨rfl, -⟩ := ha
          obtain ⟨u, m2, e3, e4, h3, h4, rfl⟩ := h2
          cases h3; cases h4
          refine Lsucc rfl (KernMaps.unmap_keep hk _ _ hw' (fun x hx => ?_))
            (by rw [m_vmmaps_backing50]; exact hself _ List.mem_cons_self) rfl
          rw [m_vmmaps_backing50]
          rcases List.mem_append.1 hx with h | h
          · exact List.mem_append_left _ h
          · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
      · split at hs
        · rcases hs with hinj | hs | hdes
          · obtain ⟨hret, hm, hev⟩ := injected_ok hinj
            exact Lkeep hm hret hev (.inr ((hsp _ _).2 (.inr (.inl ⟨rfl, rfl⟩))))
          · obtain ⟨u0, m0, e0, e1', ⟨u0', -, h0⟩, hs2, rfl⟩ := hs
            cases h0
            obtain ⟨u, m1, e1, e2, h1, h2, rfl⟩ := hs2
            cases h1; cases h2
            refine Lsucc rfl (KernMaps.unmap_sub hk _ _ hw' (by rw [m_vmmaps_replacement50]; rfl) (fun x hx => ?_))
              (by rw [m_vmmaps_replacement50]; exact hself _ List.mem_cons_self) rfl
            rw [m_vmmaps_replacement50]
            show x ∈ (_ :: maps_subtract _ _ _)
            rw [hcast]; exact List.mem_cons_of_mem _ hx
          · obtain ⟨hret, hmv, hev⟩ := destroy_ok hdes
            exact Ldes hmv hret hev
        · simp [unmodeled] at hs

end LPS.Bridge
