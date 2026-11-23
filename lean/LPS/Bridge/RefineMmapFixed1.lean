import LPS.Bridge.RefineMunmap

/-!
# Refinement for `mmap` with `MAP_FIXED`, part 1: the maps relation after a fixed mapping

NoCompiler's `MAP_FIXED` branch of `mmapSpec` (user decision (7)) cuts `[a, a + len)` out of every range
(`Kern.unmap`) and, on success, adds `(a, len)`. LPS's arms (`mmap_fixed_noaccess_*`, `mmap_fixed_rw_*`) keep its
maps when the range lies inside one mapping, add `(a, n)` when the range is free, and otherwise replace them by
`maps_subtract` (span, and the destroy arm's ENOMEM). Here: `KernMaps` is kept in each case
(`KernMaps.unmap_keep`, `KernMaps.unmap_sub`, `KernMaps.add`).
-/

namespace LPS.Bridge
open LPS.RiscvSemantics NoCompiler.Linux

theorem toNat_Z_to_bv {z : Int} (h0 : 0 ≤ z) (h1 : z < 2 ^ 64) : ((Z_to_bv 64 z).toNat : Int) = z := by
  unfold Z_to_bv
  rw [BitVec.toNat_ofInt]
  omega

/-- The pieces `cutRange` leaves: inside the range cut, and left of the hole or right of it. -/
theorem cutRange_side {a n : Nat} {p p' : NoCompiler.Word × Nat} (hb : a + n < 2 ^ 64) (h : p' ∈ cutRange a n p) :
    p.1.toNat ≤ p'.1.toNat ∧ p'.1.toNat + p'.2 ≤ p.1.toNat + p.2 ∧
      ((p'.1.toNat + p'.2 ≤ a ∧ p'.1.toNat < a) ∨ (a + n < p.1.toNat + p.2 ∧ a + n ≤ p'.1.toNat)) := by
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

theorem mem_maps_subtract {l : List (word × word)} {lo hi : Int} {q x : word × word} (hq : q ∈ l)
    (hx : x ∈ iv_subtract q.1 q.2 lo hi) : x ∈ maps_subtract l lo hi := by
  induction l with
  | nil => simp at hq
  | cons r t ih =>
    obtain ⟨ra, rs⟩ := r
    simp only [maps_subtract, List.mem_append]
    rcases List.mem_cons.1 hq with rfl | hq
    · exact .inl hx
    · exact .inr (ih hq)

/-- A range inside `q` and outside `[lo, hi)` lies in one of `q`'s pieces after subtracting `[lo, hi)`. -/
theorem iv_subtract_covers {q : word × word} {lo hi : Int} {s e : Int} (hlo : 0 ≤ lo) (hhi : hi < 2 ^ 64)
    (hq1 : (q.1.toNat : Int) ≤ s) (hq2 : e ≤ q.1.toNat + q.2.toNat) (hse : s ≤ e)
    (hside : (e ≤ lo ∧ s < lo) ∨ (hi < q.1.toNat + q.2.toNat ∧ hi ≤ s)) :
    ∃ x ∈ iv_subtract q.1 q.2 lo hi, (x.1.toNat : Int) ≤ s ∧ e ≤ x.1.toNat + x.2.toNat := by
  have hqa := q.1.isLt
  have hqs := q.2.isLt
  unfold iv_subtract
  simp only [bv_unsigned, List.mem_append]
  rcases hside with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hc : (q.1.toNat : Int) < lo := by omega
    refine ⟨(q.1, Z_to_bv 64 (min (q.2.toNat : Int) (lo - q.1.toNat))), .inl (by simp [hc]), by simp; omega, ?_⟩
    rw [toNat_Z_to_bv (by omega) (by omega)]
    simp only
    omega
  · have hc : hi < (q.1.toNat : Int) + q.2.toNat := h1
    refine ⟨(Z_to_bv 64 (max (q.1.toNat : Int) hi), Z_to_bv 64 ((q.1.toNat : Int) + q.2.toNat - max (q.1.toNat : Int) hi)),
      .inr (by simp [hc]), ?_, ?_⟩
    · simp only; rw [toNat_Z_to_bv (by omega) (by omega)]; omega
    · simp only; rw [toNat_Z_to_bv (by omega) (by omega), toNat_Z_to_bv (by omega) (by omega)]; omega

/-- Cutting `[a, a + n)` out of NoCompiler's ranges while LPS's maps become `maps_subtract` (or a superset of it):
    the relation is kept. -/
theorem KernMaps.unmap_sub {k : Kern} {m m' : Model} (hk : KernMaps k m) (a : word) (n : Nat)
    (hb : a.toNat + n < 2 ^ 64)
    (hres : (m_vmmaps m').vm_reserved = (m_vmmaps m).vm_reserved)
    (hmaps : ∀ x ∈ maps_subtract (m_vmmaps m).vm_maps a.toNat (a.toNat + n), x ∈ (m_vmmaps m').vm_maps) :
    KernMaps (k.unmap a n) m' := by
  intro p' hp'
  simp only [Kern.unmap_maps, unmapRanges, List.mem_flatMap] at hp'
  obtain ⟨p, hp, hc⟩ := hp'
  obtain ⟨q, hq, h1, h2⟩ := hk p hp
  have hs := cutRange_side hb hc
  rw [hres]
  rcases List.mem_append.1 hq with hq | hq
  · exact ⟨q, List.mem_append_left _ hq, by omega, by omega⟩
  · obtain ⟨x, hx, hx1, hx2⟩ := iv_subtract_covers (q := q) (lo := a.toNat) (hi := a.toNat + n)
      (s := p'.1.toNat) (e := p'.1.toNat + p'.2) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by rcases hs.2.2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
          · left; omega
          · right; omega)
    exact ⟨x, List.mem_append_right _ (hmaps x (mem_maps_subtract hq hx)), by omega, by omega⟩

/-- Cutting `[a, a + n)` out of NoCompiler's ranges while LPS's ranges stay: the relation is kept (pieces lie in
    the ranges they were cut from). -/
theorem KernMaps.unmap_keep {k : Kern} {m m' : Model} (hk : KernMaps k m) (a : word) (n : Nat)
    (hb : a.toNat + n < 2 ^ 64)
    (hsub : ∀ x ∈ (m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps,
      x ∈ (m_vmmaps m').vm_reserved ++ (m_vmmaps m').vm_maps) :
    KernMaps (k.unmap a n) m' := by
  intro p' hp'
  simp only [Kern.unmap_maps, unmapRanges, List.mem_flatMap] at hp'
  obtain ⟨p, hp, hc⟩ := hp'
  obtain ⟨q, hq, h1, h2⟩ := hk p hp
  have hs := cutRange_side hb hc
  exact ⟨q, hsub q hq, by omega, by omega⟩

/-- Adding a NoCompiler range that lies in an LPS range keeps the relation. -/
theorem KernMaps.add {k : Kern} {m : Model} (hk : KernMaps k m) (p : NoCompiler.Word × Nat)
    (hp : ∃ q ∈ (m_vmmaps m).vm_reserved ++ (m_vmmaps m).vm_maps,
      q.1.toNat ≤ p.1.toNat ∧ p.1.toNat + p.2 ≤ q.1.toNat + q.2.toNat) :
    KernMaps { k with maps := p :: k.maps } m := by
  intro p' hp'
  rcases List.mem_cons.1 hp' with rfl | hp'
  · exact hp
  · exact hk p' hp'

theorem KernMaps.withProt {k : Kern} {m : Model} (hk : KernMaps k m) (prot a : NoCompiler.Word) (n : Nat) :
    KernMaps (withProt prot a n k) m := by
  intro p hp; rw [withProt_maps] at hp; exact hk p hp

/-- `map_contains`: some LPS mapping contains `[lo, lo + n)`. -/
theorem map_contains_some {l : List (word × word)} {lo n : word} (h : map_contains l lo n = true) :
    ∃ q ∈ l, q.1.toNat ≤ lo.toNat ∧ lo.toNat + n.toNat ≤ q.1.toNat + q.2.toNat := by
  unfold map_contains at h
  obtain ⟨q, hq, hc⟩ := List.any_eq_true.1 h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  unfold bv_unsigned at hc
  exact ⟨q, hq, by omega, by omega⟩

end LPS.Bridge
