import Examples.Libc.SlenPre9

/-!
UNFINISHED (round 9): part of discharging `slen_correct_of_pre`'s hypothesis `hpre` (the start-up chain's
precondition at `__libc_start_main`'s entry) from `SlenLaunch`. The parts (SlenPre3..12) are proved; they are not yet
composed into `hpre`, so `SlenCorrect` is not proved (Examples/Libc/README.md).
-/
namespace Examples.Libc.Slen
open NoCompiler NoCompiler.Linux Examples.Libc.SlenImage Examples.Libc.SlenSpec

section
variable {s : State} {k : Kern} {la : LaunchAuxv} {top : Word} {argv envp : List (List Byte)} {execfn : List Byte}
  {uid gid hwcap : Word} {rnd : BitVec 128} (h : SL s k la top argv envp execfn uid gid hwcap rnd)
include h

theorem SL.auxHas (i : Nat) (hi : i < 26) (t v : Word)
    (hv : ∀ c0 c1 c2 c3 c4 c5 c6 c7 : Word, la.cache = [c0, c1, c2, c3, c4, c5, c6, c7] →
      ([(AT_SYSINFO_EHDR, la.sysinfoEhdr)] ++ cacheTypes.zip [c0, c1, c2, c3, c4, c5, c6, c7] ++ [(AT_MINSIGSTKSZ, la.minsigstksz),
          (AT_HWCAP, hwcap), (AT_PAGESZ, 4096), (AT_CLKTCK, 100),
          (AT_PHDR, slenPhdr.addr), (AT_PHENT, slenPhdr.ent), (AT_PHNUM, slenPhdr.num),
          (AT_BASE, 0), (AT_FLAGS, 0), (AT_ENTRY, startEntry),
          (AT_UID, uid), (AT_EUID, uid), (AT_GID, gid), (AT_EGID, gid),
          (AT_SECURE, 0), (AT_RANDOM, atRandomPtr (s.reg 2) la.rseq argv envp), (AT_EXECFN, atExecfnPtr top execfn)])[i]? = some (t, v)) :
    AuxHas (lA la (s.reg 2) top argv envp execfn uid gid hwcap) t v := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, hcl⟩ := cache8 la h.hc
  exact aux_has la h.hc startEntry uid gid hwcap _ _ i hi t v (by rw [hcl]; exact hv _ _ _ _ _ _ _ _ hcl)

/-- `__init_libc`'s precondition at its entry, from the launch. -/
theorem SL.initLibcPre (z z1 : State) (hSC : StartCall s z) (hIC : InitCall z z1) :
    ∃ n A P S, InitLibcPre z1 k ((z.reg 11 <<< 3) + z.reg 12 + 8#64) n A P S := by
  have hlo := h.hA.1; simp only [Reg.sp] at hlo
  have hbl := bss_below s top h.hA
  have hal := h.hal; unfold aligned at hal; simp only [Reg.sp] at hal
  have hz2 := h.z1_sp z z1 hSC hIC
  have hS := ilS_of z1 (s.reg 2) hz2
  have he : (z.reg 11 <<< 3) + z.reg 12 + 8#64 = s.reg 2 + BitVec.ofNat 64 (8 * (argv.length + 2)) := by
    rw [← hIC.2.2.2.2.1]; exact h.z1_a0 z z1 hSC hIC
  obtain ⟨P, S, hStr, hpn⟩ := h.pn z z1 hSC hIC
  refine ⟨envp.length, lA la (s.reg 2) top argv envp execfn uid gid hwcap, P, S,
    { a0 := hIC.2.2.2.2.1
      sp := by unfold aligned; rw [hz2]; bv_omega
      lo := by rw [hz2]; bv_omega
      env := by rw [he]; exact h.envAt z z1 hSC hIC
      aux := by rw [he]; exact h.auxAt z z1 hSC hIC
      str := hStr
      pn := hpn
      phdr := h.auxHas 13 (by omega) _ _ (fun _ _ _ _ _ _ _ _ _ => rfl)
      phent := h.auxHas 14 (by omega) _ _ (fun _ _ _ _ _ _ _ _ _ => rfl)
      phnum := h.auxHas 15 (by omega) _ _ (fun _ _ _ _ _ _ _ _ _ => rfl)
      uid := ⟨uid, h.auxHas 19 (by omega) _ _ (fun _ _ _ _ _ _ _ _ _ => rfl), h.auxHas 20 (by omega) _ _ (fun _ _ _ _ _ _ _ _ _ => rfl)⟩
      gid := ⟨gid, h.auxHas 21 (by omega) _ _ (fun _ _ _ _ _ _ _ _ _ => rfl), h.auxHas 22 (by omega) _ _ (fun _ _ _ _ _ _ _ _ _ => rfl)⟩
      secure := h.auxHas 23 (by omega) _ _ (fun _ _ _ _ _ _ _ _ _ => rfl)
      ph := PhdrLit_congr (fun p hp => h.z1_out z z1 hSC hIC p (h.img_out p (by simp only [Region.mem] at hp; bv_omega)))
        (phdrLit_of s.mem h.hph)
      bss := by
        have hb := h.hseg seg_bss (by simp [segments])
        refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
          rw [h.z1_read64_img z z1 hSC hIC _ (by decide)]
        · exact bss_zero s.mem hb 8 (by omega)
        · exact bss_zero s.mem hb 24 (by omega)
        · exact bss_zero s.mem hb 32 (by omega)
        · exact bss_zero s.mem hb 424 (by omega)
        · exact bss_zero s.mem hb 400 (by omega)
      wS := by intro p n hc; rw [hS] at hc; exact h.frame_rw p n hc
      wG := by intro p n hc; exact (h.sbss_rw p n (by simpa [ilG, seg_sbss, Region.covers] using hc)).1
      wW := by
        intro p n hc; refine (h.bss_rw p n ?_).1
        simp only [tlW, Region.covers] at hc; simp only [seg_bss, Region.covers, Array.size_replicate]; omega
      rP := fun p n hc => h.phdr_rd p n hc
      rS4 := (h.sdata_rw _ _ (by simp [seg_sdata, Region.covers, Segment.size_bytesOfNat])).2
      rSy := (h.sbss_rw _ _ (by simp [seg_sbss, Region.covers])).2
      dG := by rw [hS]; unfold Region.Disjoint ilG; dsimp only; constructor <;> bv_omega
      dW := by rw [hS]; unfold Region.Disjoint tlW; dsimp only; constructor <;> bv_omega
      dPh := by rw [hS]; unfold Region.Disjoint; dsimp only; constructor <;> bv_omega }⟩

end

end Examples.Libc.Slen
