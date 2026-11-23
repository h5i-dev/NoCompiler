import LPS.Bridge.RefineMmap

/-!
# Refinement for `munmap`, the converse direction

LPS models `munmap(a, len)` only of a whole mapping: `map_has vm_maps a (page_round_up len)`, and then it removes
every `vm_maps` entry whose base is `a` (`map_remove`). NoCompiler cuts `[a, a + pageUp len)` out of every range
(`Kern.unmap`, Linux's `do_vmi_munmap`). The maps relation `KernMaps` is kept when every LPS entry at base `a` is
that mapping (`MapSole`): a NoCompiler piece left of `a` or right of the cut then lies in an LPS range that stays
(`KernMaps.unmap`). LPS's own mappings are disjoint, so `MapSole` holds for them; it is a hypothesis here.

`munmap_covers`: under LPS's modeled-input conditions (page-aligned `a`, `len > 0`, the range below `TASK_SIZE`,
the mapping present), LPS's only outcome (0, `munmap_model`) is NoCompiler's (0, `Kern.unmap`), `KernMaps` kept.
-/

namespace LPS.Bridge
open LPS.RiscvSemantics NoCompiler.Linux

/-- Every LPS mapping at base `a` has length `n`. -/
def MapSole (m : Model) (a n : word) : Prop := ∀ q ∈ (m_vmmaps m).vm_maps, q.1 = a → q.2 = n

/-- A piece `cutRange` leaves of `p`: inside `p`, and either `p`'s left part (below `a`) or its right part (from
    `a + n`, when `p` reaches past it). -/
theorem cutRange_sub {a n : Nat} {p p' : NoCompiler.Word × Nat} (hb : a + n < 2 ^ 64) (h : p' ∈ cutRange a n p) :
    p.1.toNat ≤ p'.1.toNat ∧ p'.1.toNat + p'.2 ≤ p.1.toNat + p.2 ∧
      ((p'.1.toNat = p.1.toNat ∧ p.1.toNat < a) ∨ (a + n < p.1.toNat + p.2 ∧ a + n ≤ p'.1.toNat)) := by
  unfold cutRange at h
  simp only [List.mem_append] at h
  have hp := p.1.isLt
  rcases h with h | h
  · split at h
    · rw [List.mem_singleton] at h; subst h; dsimp only at *; rw [Nat.min_def]; split <;> omega
    · simp at h
  · split at h
    · rw [List.mem_singleton] at h; subst h
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    · simp at h

/-- Unmapping the same mapping on both sides keeps the relation. -/
theorem KernMaps.unmap {k : Kern} {m m' : Model} (hk : KernMaps k m) (a n : word) (hsole : MapSole m a n)
    (hb : a.toNat + n.toNat < 2 ^ 64)
    (hres : (m_vmmaps m').vm_reserved = (m_vmmaps m).vm_reserved)
    (hmaps : (m_vmmaps m').vm_maps = map_remove (m_vmmaps m).vm_maps a) :
    KernMaps (k.unmap a n.toNat) m' := by
  intro p' hp'
  simp only [Kern.unmap_maps, unmapRanges, List.mem_flatMap] at hp'
  obtain ⟨p, hp, hc⟩ := hp'
  obtain ⟨q, hq, h1, h2⟩ := hk p hp
  have hs := cutRange_sub hb hc
  rw [hres, hmaps]
  rcases List.mem_append.1 hq with hq | hq
  · exact ⟨q, List.mem_append_left _ hq, by omega, by omega⟩
  · by_cases hqa : q.1 = a
    · have hn := hsole q hq hqa
      rw [hqa] at h1 h2; rw [hn] at h2
      omega
    · refine ⟨q, List.mem_append_right _ ?_, by omega, by omega⟩
      simp only [map_remove, List.mem_filter, Bool.not_eq_true']
      exact ⟨hq, bv_eqb_neq _ _ hqa⟩

/-- `munmap` in NoCompiler's model, unfolded. -/
theorem procSpec7_munmap {k k' : Kern} {i : NoCompiler.Linux.SyscallInput} {o : Outcome}
    (h : i.sysno = NoCompiler.Linux.sysMunmap) : procSpec7 k i o k' ↔ munmapSpec k i o k' := by
  simp only [procSpec7, procSpec6, procSpec5, procSpec4, procSpec3, procSpec2, procSpec, h]
  simp (config := { decide := true })

/-- Every `munmap` outcome LPS admits on its modeled inputs is NoCompiler's, the maps relation kept. -/
theorem munmap_covers {k : Kern} {i : NoCompiler.Linux.SyscallInput} {j : SyscallInput} {m m' : Model}
    {eff : SyscallEffect} {evs : List event} (hr : InRel i j) (h215 : i.sysno = NoCompiler.Linux.sysMunmap)
    (hal : (i.arg 0).toNat % 4096 = 0) (hlen : 0 < (i.arg 1).toNat)
    (hnw : (i.arg 0).toNat + pageUp (i.arg 1) ≤ taskSize)
    (hhas : map_has (m_vmmaps m).vm_maps (i.arg 0) (page_round_up (i.arg 1)) = true)
    (hsole : MapSole m (i.arg 0) (page_round_up (i.arg 1))) (hk : KernMaps k m)
    (hs : syscall_spec j m (Ok eff m' evs)) :
    ∃ k', procSpec7 k i (.ret { ret := eff.eff_ret } none) k' ∧ KernMaps k' m' ∧ evs = [] := by
  have hn : bv_unsigned j.in_sysno = 215 := by rw [hr.sysno, h215]; rfl
  rw [lookup_arm_of (a := mkSpecArm 215 (fun i => munmap_spec (in_arg i 0) (in_arg i 1) i))
    (by simp [spec_table, lookup_arm, mkSpecArm]) j hn] at hs
  change munmap_spec (in_arg j 0) (in_arg j 1) j m (Ok eff m' evs) at hs
  rw [hr.args 0, hr.args 1] at hs
  have hpe := pageUp_eq (i.arg 1)
  have Hal : Z.modulo (bv_unsigned (i.arg 0)) page_size = 0 := by
    unfold Z.modulo page_size bv_unsigned
    rw [Int.fmod_eq_emod_of_nonneg _ (by decide)]; omega
  have Hlen : i.arg 1 ≠ Z_to_bv 64 0 := by
    intro h; rw [h] at hlen; exact absurd hlen (by decide)
  have Hnw : bv_unsigned (i.arg 0) + page_round_up_Z (bv_unsigned (i.arg 1)) ≤ TASK_SIZE := by
    rw [← hpe]; unfold bv_unsigned TASK_SIZE; unfold taskSize at hnw; omega
  obtain ⟨rfl, rfl, hev⟩ := (munmap_spec_modeled_ok _ _ j m eff m' evs Hal Hlen Hnw hhas).1 hs
  have hnat : (page_round_up (i.arg 1)).toNat = pageUp (i.arg 1) := by
    unfold page_round_up Z_to_bv
    rw [← hpe, BitVec.toNat_ofInt]
    unfold taskSize at hnw
    omega
  refine ⟨k.unmap (i.arg 0) (pageUp (i.arg 1)), ?_, ?_, hev⟩
  · rw [procSpec7_munmap h215]; unfold munmapSpec
    rw [if_pos ⟨hal, hlen⟩]
    exact ⟨rfl, rfl⟩
  · rw [← hnat]
    exact KernMaps.unmap hk _ _ hsole (by unfold taskSize at hnw; omega) rfl rfl

end LPS.Bridge
