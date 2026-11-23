import LPS.Bridge.RefineMmapFixed1

/-!
# Refinement for `mmap` with `MAP_FIXED`, part 2: the converse

`mmap_fixed_covers`: every outcome LPS admits for `mmap(a, len, prot, MAP_PRIVATE|MAP_ANONYMOUS|MAP_FIXED, -1, 0)`,
`prot` PROT_NONE or PROT_READ|PROT_WRITE, `len > 0`, `a` page-aligned, is one of NoCompiler's (`mmapSpec`'s
MAP_FIXED branch, user decision (7)), `KernMaps` kept, given LPS's `alloc_top` within `taskSize`. LPS's outcomes:
ENOMEM when `a + len` wraps; an injected ENOMEM (model kept); success, the range inside one mapping (maps kept),
free (one entry added) or spanning several (`maps_subtract`, then the entry); ENOMEM after destroying the range.
NoCompiler's: success (the range cut, then added), ENOMEM with the kernel kept, ENOMEM with the range cut.

Hypothesis `hal` (page-aligned): LPS checks wraparound before alignment, NoCompiler alignment first, so an
unaligned address that also wraps gets ENOMEM from LPS and EINVAL from NoCompiler.
-/

namespace LPS.Bridge
open LPS.RiscvSemantics NoCompiler.Linux

theorem err_ret_ok {e : Int} {j : SyscallInput} {m m' : Model} {eff : SyscallEffect} {evs : List event}
    (h : err_ret e j m (Ok eff m' evs)) : eff.eff_ret = errno_ret e ∧ m' = m ∧ evs = [] := by
  simp only [err_ret, ret_only, Sys.pure] at h
  cases h; exact ⟨rfl, rfl, rfl⟩

theorem injected_ok {j : SyscallInput} {m m' : Model} {eff : SyscallEffect} {evs : List event}
    (h : mmap_injected j m (Ok eff m' evs)) : eff.eff_ret = errno_ret ENOMEM ∧ m' = m ∧ evs = [] := by
  obtain ⟨e, m1, e1, e2, ⟨e', he, h1⟩, h2, rfl⟩ := h
  cases h1
  simp only [mmap_errnos, List.mem_singleton] at he
  subst he
  obtain ⟨hr, rfl, rfl⟩ := err_ret_ok h2
  exact ⟨hr, rfl, rfl⟩

theorem destroy_ok {a n : word} {hv : VmMaps} {m0 : Model} {j : SyscallInput} {m m' : Model}
    {eff : SyscallEffect} {evs : List event} (h : mmap_destroy_arm a n hv m0 j m (Ok eff m' evs)) :
    eff.eff_ret = errno_ret ENOMEM ∧ m_vmmaps m' = mmap_fixed_destroyed_next hv a n ∧ evs = [] := by
  obtain ⟨e, m1, e1, e2, ⟨e', he, h1⟩, h2, rfl⟩ := h
  cases h1
  simp only [mmap_errnos, List.mem_singleton] at he
  subst he
  obtain ⟨u, m2, e3, e4, h3, h4, rfl⟩ := h2
  cases h3
  cases h4
  exact ⟨rfl, rfl, rfl⟩

theorem m_vmmaps_replacement (a n : word) (m : Model) :
    m_vmmaps (with_mmap_replacement (Z_to_bv 64 50) a n m) = m_vmmaps m := by
  simp only [with_mmap_replacement, with_mmap_backing, mmap_noreserve_b]
  rfl

end LPS.Bridge
