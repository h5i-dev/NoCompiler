import LPS.Bridge.RefineBrk
import LPS.Common.MmapSim1

/-!
# Refinement for anonymous `mmap`, the relation for the converse direction

`KernMaps k m`: every byte of a range NoCompiler has mapped (`Kern.maps`) lies in one range of LPS's
(`vm_reserved` or `vm_maps`). Then an address LPS finds free of its own ranges is free of NoCompiler's
(`free_of_region_free`), and LPS's anonymous `mmap` outcome (a page-aligned free address below `alloc_top`,
zero-filled) is one NoCompiler's `mmapSpec` allows, the relation kept (`KernMaps.cons`).

`mmap_anon_covers`: the converse for `mmap(0, len, PROT_READ|PROT_WRITE, MAP_PRIVATE|MAP_ANONYMOUS, -1, 0)`,
`len > 0`, the shape musl's malloc uses, given LPS's `alloc_top` within NoCompiler's `taskSize`. Its proof uses
`mmap_spec_modeled_ok` (Common/MmapSim1): LPS's outcomes are ENOMEM or a granted page-aligned free address.
NoCompiler's hint must be 0 (its `mmapSpec` has no outcome for a nonzero hint without MAP_FIXED; LPS ignores the
hint). Not yet here: other prot values, `MAP_FIXED` (NoCompiler's branch from user decision (7)), `munmap`.
-/

namespace LPS.Bridge
open LPS.RiscvSemantics NoCompiler.Linux

/-- Every NoCompiler range inside some LPS range, endpoints included: also NoCompiler's zero-length entries
    (`brk` adds `(pageUp brk, 0)` when the break grows within a page), whose point must not lie strictly
    inside a new mapping (`mmapSpec`'s disjointness). -/
def KernMaps (k : Kern) (m : Model) : Prop :=
  ∀ p ∈ k.maps, ∃ q ∈ (m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps,
    q.1.toNat ≤ p.1.toNat ∧ p.1.toNat + p.2 ≤ q.1.toNat + q.2.toNat

theorem region_free_disj {l : List (word × word)} {a n : word} (h : region_free l a n = true) :
    ∀ q ∈ l, a.toNat + n.toNat ≤ q.1.toNat ∨ q.1.toNat + q.2.toNat ≤ a.toNat := by
  induction l with
  | nil => simp
  | cons q r ih =>
    simp only [region_free, Bool.and_eq_true, Bool.not_eq_true'] at h
    intro q' hq'
    rcases List.mem_cons.1 hq' with rfl | hq'
    · have hov : iv_overlap a n q'.1 q'.2 = false := by simpa using h.1
      unfold iv_overlap at hov
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not] at hov
      unfold bv_unsigned at hov
      omega
    · exact ih h.2 q' hq'

/-- An address range LPS finds free is disjoint from every range NoCompiler has mapped. -/
theorem free_of_region_free {k : Kern} {m : Model} (hk : KernMaps k m) {a n : word}
    (h : region_free ((m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps) a n = true) :
    ∀ p ∈ k.maps, disjointNat a.toNat n.toNat p.1.toNat p.2 := by
  intro p hp
  obtain ⟨q, hq, h1, h2⟩ := hk p hp
  have := region_free_disj h q hq
  unfold disjointNat; omega

/-- Adding the same range on both sides keeps the relation. -/
theorem KernMaps.cons {k : Kern} {m m' : Model} (hk : KernMaps k m) (a : word) (n : word)
    (hres : (m_vmmaps m').vm_reserved = (m_vmmaps m).vm_reserved)
    (hmaps : (m_vmmaps m').vm_maps = (a, n) :: (m_vmmaps m).vm_maps) :
    KernMaps { k with maps := (a, n.toNat) :: k.maps } m' := by
  intro p hp
  rcases List.mem_cons.1 hp with rfl | hp
  · exact ⟨(a, n), by rw [hres, hmaps]; simp, by simp, by simp⟩
  · obtain ⟨q, hq, h1, h2⟩ := hk p hp
    refine ⟨q, ?_, h1, h2⟩
    rw [hres, hmaps]
    rcases List.mem_append.1 hq with hq | hq
    · exact List.mem_append_left _ hq
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ hq)

/-- `mmap` in NoCompiler's model, unfolded. -/
theorem procSpec7_mmap {k k' : Kern} {i : NoCompiler.Linux.SyscallInput} {o : Outcome}
    (h : i.sysno = NoCompiler.Linux.sysMmap) : procSpec7 k i o k' ↔ mmapSpec k i o k' := by
  simp only [procSpec7, procSpec6, procSpec5, procSpec4, procSpec3, procSpec2, procSpec, h]
  simp (config := { decide := true })

theorem withProt_maps (prot a : NoCompiler.Word) (n : Nat) (k : Kern) : (withProt prot a n k).maps = k.maps := by
  unfold withProt; split
  · rfl
  · split <;> rfl

/-- Every anonymous read-write `mmap` outcome LPS admits is one of NoCompiler's, the maps relation kept. -/
theorem mmap_anon_covers {k : Kern} {i : NoCompiler.Linux.SyscallInput} {j : SyscallInput} {m m' : Model}
    {eff : SyscallEffect} {evs : List event} (hr : InRel i j) (h222 : i.sysno = NoCompiler.Linux.sysMmap)
    (h0 : i.arg 0 = 0) (hlen : 0 < (i.arg 1).toNat) (hprot : i.arg 2 = 3) (hfl : i.arg 3 = mapPrivateAnon)
    (hfd : i.fd 4 = 0xffffffff#64) (hoff : i.arg 5 = 0) (hk : KernMaps k m)
    (htop : alloc_top (m_vmmaps m) ≤ (taskSize : Int)) (hs : syscall_spec j m (Ok eff m' evs)) :
    ∃ zs k', procSpec7 k i (.ret { ret := eff.eff_ret, zeros := zs } none) k' ∧ KernMaps k' m' ∧ evs = [] := by
  have hn : bv_unsigned j.in_sysno = 222 := by rw [hr.sysno, h222]; rfl
  rw [lookup_arm_of (a := mkSpecArm 222 (fun i => mmap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3)
    (in_arg i 4) (in_arg i 5) i)) (by simp [spec_table, lookup_arm, mkSpecArm]) j hn] at hs
  change mmap_spec (in_arg j 0) (in_arg j 1) (in_arg j 2) (in_arg j 3) (in_arg j 4) (in_arg j 5) j m
    (Ok eff m' evs) at hs
  have e2 : in_arg j 2 = Z_to_bv 64 3 := by rw [hr.args, hprot]; decide
  have e3 : in_arg j 3 = Z_to_bv 64 34 := by rw [hr.args, hfl]; decide
  have e5 : in_arg j 5 = Z_to_bv 64 0 := by rw [hr.args, hoff]; decide
  have e1 : in_arg j 1 ≠ Z_to_bv 64 0 := by
    rw [hr.args]; intro h; rw [h] at hlen; exact absurd hlen (by decide)
  rw [e2, e3, e5] at hs
  obtain ⟨hev, hc⟩ := (mmap_spec_modeled_ok _ _ _ j m eff m' evs e1).1 hs
  have hsp : ∀ o k', procSpec7 k i o k' ↔ ((∃ a : NoCompiler.Word, a.toNat % 4096 = 0 ∧ a.toNat + pageUp (i.arg 1) ≤ taskSize ∧
        (∀ p ∈ k.maps, disjointNat a.toNat (pageUp (i.arg 1)) p.1.toNat p.2) ∧
        o = .ret { ret := a, zeros := [(a, pageUp (i.arg 1))] } none ∧
        k' = withProt (i.arg 2) a (pageUp (i.arg 1)) { k with maps := (a, pageUp (i.arg 1)) :: k.maps }) ∨
      (o = .ret { ret := enomem } none ∧ k' = k)) := by
    intro o k'
    have hc : i.arg 0 = 0 ∧ i.arg 3 = mapPrivateAnon ∧ i.fd 4 = 0xffffffff#64 ∧ i.arg 5 = 0 ∧
        0 < (i.arg 1).toNat ∧ (i.arg 2).toNat < 8 := ⟨h0, hfl, hfd, hoff, hlen, by rw [hprot]; decide⟩
    rw [procSpec7_mmap h222]; unfold mmapSpec; rw [if_pos hc]
  rcases hc with ⟨e, he, rfl, rfl⟩ | ⟨a, hg, rfl, rfl⟩
  · simp only [mmap_errnos, List.mem_singleton] at he
    subst he
    refine ⟨[], k, (hsp _ _).2 (.inr ⟨?_, rfl⟩), hk, hev⟩
    show Outcome.ret { ret := errno_ret ENOMEM, zeros := [] } none = _
    rfl
  · have ha1 : in_arg j 1 = i.arg 1 := hr.args 1
    rw [ha1] at hg
    simp only [grant_ok, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hg
    obtain ⟨⟨⟨⟨hmod, hpos⟩, htopa⟩, hfree⟩, -⟩ := hg
    have hpe : page_round_up_Z (bv_unsigned (i.arg 1)) = (pageUp (i.arg 1) : Int) := (pageUp_eq (i.arg 1)).symm
    rw [hpe] at htopa
    have hnat : (page_round_up (i.arg 1)).toNat = pageUp (i.arg 1) := by
      unfold page_round_up Z_to_bv
      rw [hpe, BitVec.toNat_ofInt]
      unfold bv_unsigned at htopa
      have : (pageUp (i.arg 1) : Int) < 2 ^ 64 := by unfold taskSize at htop; omega
      omega
    have hfr := free_of_region_free hk hfree
    rw [show Z_to_bv 64 (page_round_up_Z (bv_unsigned (i.arg 1))) = page_round_up (i.arg 1) from rfl, hnat] at hfr
    unfold bv_unsigned at htopa
    unfold Z.modulo page_size bv_unsigned at hmod
    refine ⟨[(a, pageUp (i.arg 1))], withProt (i.arg 2) a (pageUp (i.arg 1))
      { k with maps := (a, pageUp (i.arg 1)) :: k.maps }, (hsp _ _).2 (.inl ⟨a, ?_, ?_, hfr, rfl, rfl⟩), ?_, hev⟩
    · rw [Int.fmod_eq_emod_of_nonneg _ (by decide)] at hmod; omega
    · unfold taskSize at htop ⊢; omega
    · intro p hp
      rw [withProt_maps] at hp
      rw [ha1]
      have hp' : p ∈ (({ k with maps := (a, (page_round_up (i.arg 1)).toNat) :: k.maps } : Kern)).maps := by
        rw [hnat]; exact hp
      exact KernMaps.cons hk a (page_round_up (i.arg 1)) (m' := mmap_model a (page_round_up (i.arg 1)) m) rfl rfl p hp'

end LPS.Bridge
