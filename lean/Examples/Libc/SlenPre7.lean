import Examples.Libc.SlenPre5

/-!
UNFINISHED (round 9): part of discharging `slen_correct_of_pre`'s hypothesis `hpre` (the start-up chain's
precondition at `__libc_start_main`'s entry) from `SlenLaunch`. The parts (SlenPre3..12) are proved; they are not yet
composed into `hpre`, so `SlenCorrect` is not proved (Examples/Libc/README.md).
-/
namespace Examples.Libc.Slen
open NoCompiler NoCompiler.Linux Examples.Libc.SlenImage Examples.Libc.SlenSpec

theorem code_range : (code.base, 4 * code.words.size) = (0x111d0#64, 4 * Chunk.total chunks) := by
  simp only [code, Code.ofChunks, List.size_toArray, Chunk.length_flatten]

/-- The read-only overlays, as numbers. -/
theorem roIn_num (r : Word × Nat) (h : RoIn r) :
    r = (0x111d0#64, 4 * Chunk.total chunks) ∨ r = (seg_rodata.base, 64) ∨ r = (seg_phdr.base, 336) := by
  unfold RoIn at h; rw [code_range] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl
  · exact .inl rfl
  · right; left; rfl
  · right; right; simp [seg_phdr, Segment.size_bytesOfNat]

/-- A mapped range of the image apart (as numbers) from `.text`, `.rodata` and the program headers is read-write. -/
theorem img_rw (k : Kern) (hna : k.noacc = []) (hro : ∀ r ∈ k.ro, RoIn r) (p : Word × Nat) (hm : p ∈ k.maps) (hp : 0 < p.2)
    (h1 : NumApart p (0x111d0#64, 4 * Chunk.total chunks)) (h2 : NumApart p (seg_rodata.base, 64))
    (h3 : NumApart p (seg_phdr.base, 336)) (a : Word) (n : Nat) (hc : (Region.mk p.1 p.2).covers a n) :
    k.perm.canWrite a n ∧ k.perm.canRead a n := by
  have hr : ∀ c ∈ k.ro, NumApart p c := by
    intro c hc; rcases roIn_num c (hro c hc) with rfl | rfl | rfl <;> assumption
  exact ⟨Kern.canWrite_of_apart k p hm hp hr (by simp [hna]) a n hc, Kern.canRead_of_apart k p hm hp hr (by simp [hna]) a n hc⟩

/-- A mapped range that is a read-only overlay is readable. -/
theorem Kern.canRead_of_ro (k : Kern) (hna : k.noacc = []) (p : Word × Nat) (hm : p ∈ k.maps) (hr : p ∈ k.ro) (hp : 0 < p.2)
    (a : Word) (n : Nat) (hc : (Region.mk p.1 p.2).covers a n) : k.perm.canRead a n := by
  refine .inr ⟨⟨p.1, p.2⟩, List.mem_append_left _ ?_, hc⟩
  simp only [Kern.perm, hna, cutAll_nil, List.mem_map]
  refine ⟨p, ?_, rfl⟩
  simp only [interAll, List.mem_flatMap]
  refine ⟨p, hr, p, hm, ?_⟩
  have hlt : p.1.toNat < p.1.toNat + p.2 := by omega
  simp only [interRange, Nat.max_self, Nat.min_self, hlt, ↓reduceIte, List.mem_singleton]
  simp

section
variable {s : State} {k : Kern} {la : LaunchAuxv} {top : Word} {argv envp : List (List Byte)} {execfn : List Byte}
  {uid gid hwcap : Word} {rnd : BitVec 128} (h : SL s k la top argv envp execfn uid gid hwcap rnd)
include h

theorem SL.segmap (g : Segment) (hg : g ∈ seg_phdr :: segments) : (g.base, g.bytes.size) ∈ k.maps :=
  h.hmaps _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨g, hg, rfl⟩)))

theorem SL.sbss_rw (a : Word) (n : Nat) (hc : (Region.mk seg_sbss.base seg_sbss.bytes.size).covers a n) :
    k.perm.canWrite a n ∧ k.perm.canRead a n :=
  img_rw k h.hna h.hro _ (h.segmap seg_sbss (by simp [segments])) (by decide)
    (by simp [NumApart, seg_sbss]; decide) (by simp [NumApart, seg_sbss, seg_rodata]) (by simp [NumApart, seg_sbss, seg_phdr]) a n hc

theorem SL.sdata_rw (a : Word) (n : Nat) (hc : (Region.mk seg_sdata.base seg_sdata.bytes.size).covers a n) :
    k.perm.canWrite a n ∧ k.perm.canRead a n :=
  img_rw k h.hna h.hro _ (h.segmap seg_sdata (by simp [segments])) (by simp [seg_sdata, Segment.size_bytesOfNat])
    (by simp [NumApart, seg_sdata, Segment.size_bytesOfNat]; decide) (by simp [NumApart, seg_sdata, seg_rodata, Segment.size_bytesOfNat])
    (by simp [NumApart, seg_sdata, seg_phdr, Segment.size_bytesOfNat]) a n hc

theorem SL.bss_rw (a : Word) (n : Nat) (hc : (Region.mk seg_bss.base seg_bss.bytes.size).covers a n) :
    k.perm.canWrite a n ∧ k.perm.canRead a n :=
  img_rw k h.hna h.hro _ (h.segmap seg_bss (by simp [segments])) (by simp [seg_bss])
    (by simp [NumApart, seg_bss]; decide) (by simp [NumApart, seg_bss, seg_rodata]) (by simp [NumApart, seg_bss, seg_phdr]) a n hc

theorem SL.phdr_rd (a : Word) (n : Nat) (hc : (Region.mk 0x10040#64 336).covers a n) : k.perm.canRead a n := by
  have hm := h.segmap seg_phdr (List.mem_cons_self ..)
  have e : (seg_phdr.base, seg_phdr.bytes.size) = (0x10040#64, 336) := by simp [seg_phdr, Segment.size_bytesOfNat]
  rw [e] at hm
  by_cases hr : (0x10040#64, 336) ∈ k.ro
  · exact Kern.canRead_of_ro k h.hna _ hm hr (by decide) a n hc
  · have hap : ∀ c ∈ k.ro, NumApart (0x10040#64, 336) c := by
      intro c hc'
      rcases roIn_num c (h.hro c hc') with rfl | rfl | rfl
      · simp [NumApart]
      · simp [NumApart, seg_rodata]
      · exact absurd hc' (by simpa [seg_phdr] using hr)
    exact Kern.canRead_of_apart k _ hm (by decide) hap (by simp [h.hna]) a n hc

/-- `__init_libc`'s frame (448 bytes below its sp = sp - 32) is writable. -/
theorem SL.frame_rw (a : Word) (n : Nat) (hc : (Region.mk (s.reg 2 - 480#64) 448).covers a n) : k.perm.canWrite a n := by
  have hlo := h.hA.1; have ht := top.isLt; have hfit := h.headfit
  simp only [Reg.sp] at hlo
  simp only [Region.covers] at hc
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact .inl rfl
  exact (stk_rw s top k h.hA h.hna h.hro h.sm a n (by bv_omega) (by bv_omega)).1

end

end Examples.Libc.Slen
