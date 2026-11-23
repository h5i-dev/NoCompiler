import Examples.Libc.InitLibc
namespace Examples.Libc.Slen
open NoCompiler NoCompiler.Linux Examples.Libc.SlenImage Examples.Libc.SlenSpec

section
variable (la : LaunchAuxv) (hc : la.cache.length = 8) (entry uid gid hwcap ar ef : Word)
include hc

theorem cache8 : ∃ c0 c1 c2 c3 c4 c5 c6 c7, la.cache = [c0, c1, c2, c3, c4, c5, c6, c7] := by
  match h : la.cache, hc with
  | [c0, c1, c2, c3, c4, c5, c6, c7], _ => exact ⟨c0, c1, c2, c3, c4, c5, c6, c7, rfl⟩

/-- The launch auxv's entry `i` (below 26: the same with and without rseq). -/
theorem aux_at (i : Nat) (hi : i < 26) :
    ∃ h : i < (auxvEntries la slenPhdr entry uid gid hwcap ar ef).length,
      (auxvEntries la slenPhdr entry uid gid hwcap ar ef)[i] =
        ([(AT_SYSINFO_EHDR, la.sysinfoEhdr)] ++ cacheTypes.zip la.cache ++ [(AT_MINSIGSTKSZ, la.minsigstksz),
          (AT_HWCAP, hwcap), (AT_PAGESZ, 4096), (AT_CLKTCK, 100),
          (AT_PHDR, slenPhdr.addr), (AT_PHENT, slenPhdr.ent), (AT_PHNUM, slenPhdr.num),
          (AT_BASE, 0), (AT_FLAGS, 0), (AT_ENTRY, entry),
          (AT_UID, uid), (AT_EUID, uid), (AT_GID, gid), (AT_EGID, gid),
          (AT_SECURE, 0), (AT_RANDOM, ar), (AT_EXECFN, ef)])[i]'(by
            obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, hcl⟩ := cache8 la hc; simp [hcl, cacheTypes]; omega) := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, hcl⟩ := cache8 la hc
  refine ⟨by unfold auxvEntries; simp [hcl, cacheTypes]; omega, ?_⟩
  unfold auxvEntries; rw [List.getElem_append_left]

theorem aux_has (i : Nat) (hi : i < 26) (t v : Word)
    (h : ([(AT_SYSINFO_EHDR, la.sysinfoEhdr)] ++ cacheTypes.zip la.cache ++ [(AT_MINSIGSTKSZ, la.minsigstksz),
          (AT_HWCAP, hwcap), (AT_PAGESZ, 4096), (AT_CLKTCK, 100),
          (AT_PHDR, slenPhdr.addr), (AT_PHENT, slenPhdr.ent), (AT_PHNUM, slenPhdr.num),
          (AT_BASE, 0), (AT_FLAGS, 0), (AT_ENTRY, entry),
          (AT_UID, uid), (AT_EUID, uid), (AT_GID, gid), (AT_EGID, gid),
          (AT_SECURE, 0), (AT_RANDOM, ar), (AT_EXECFN, ef)])[i]? = some (t, v)) :
    AuxHas (auxvEntries la slenPhdr entry uid gid hwcap ar ef) t v := by
  obtain ⟨hl, he⟩ := aux_at la hc entry uid gid hwcap ar ef i hi
  refine ⟨i, hl, ?_⟩
  obtain ⟨_, h'⟩ := List.getElem?_eq_some_iff.1 h
  rw [he, h']; exact ⟨rfl, rfl⟩

theorem aux_types : ((auxvEntries la slenPhdr entry uid gid hwcap ar ef).map Prod.fst).Nodup ∧
    ∀ p ∈ auxvEntries la slenPhdr entry uid gid hwcap ar ef, p.1 ≠ 0 := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, hcl⟩ := cache8 la hc
  unfold auxvEntries
  cases la.rseq <;> simp only [hcl, cacheTypes, List.zip_cons_cons, List.zip_nil_right, List.cons_append,
    List.nil_append, List.append_nil, List.map_cons, List.map_nil, Bool.false_eq_true, ↓reduceIte] <;>
    refine ⟨by decide, ?_⟩ <;> intro p hp <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hp <;>
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (dsimp only; decide)

end

end Examples.Libc.Slen
