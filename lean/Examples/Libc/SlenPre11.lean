import Examples.Libc.SlenPre9

/-!
UNFINISHED (round 9): part of discharging `slen_correct_of_pre`'s hypothesis `hpre` (the start-up chain's
precondition at `__libc_start_main`'s entry) from `SlenLaunch`. The parts (SlenPre3..12) are proved; they are not yet
composed into `hpre`, so `SlenCorrect` is not proved (Examples/Libc/README.md).
-/
namespace Examples.Libc.Slen
open NoCompiler NoCompiler.Linux Examples.Libc.SlenImage Examples.Libc.SlenSpec

/-- `m` is the launch memory on the image outside `.sbss` (ilG) and `tlW`: what `__init_libc` and the stack frames
    leave of it. -/
def ImgEq (m : Word → Byte) (s : State) : Prop := ∀ p : Word, p.toNat < 0x15000 → ¬ ilG.mem p → ¬ tlW.mem p → m p = s.mem p

/-- A read of a loaded section through `ImgEq`, away from ilG and tlW. -/
theorem img_rd (s : State) (m : Word → Byte) (hm : ImgEq m s) (g : Segment) (hg : g.Loaded s.mem) (o n : Nat)
    (ho : o + n ≤ g.bytes.size) (hb : g.base.toNat + g.bytes.size ≤ 0x15000)
    (hG : (Region.mk (g.base + BitVec.ofNat 64 o) n).Disjoint ilG) (hW : (Region.mk (g.base + BitVec.ofNat 64 o) n).Disjoint tlW) :
    readLE m (g.base + BitVec.ofNat 64 o) n = segLE g o n := by
  rw [← seg_readLE g s.mem hg n o ho]
  apply readLE_congr; intro j hj
  have hbl := g.base.isLt
  apply hm
  · bv_omega
  · simp only [Region.Disjoint, ilG, Region.mem] at hG ⊢; bv_omega
  · simp only [Region.Disjoint, tlW, Region.mem] at hW ⊢; bv_omega

/-- The image values `main` reads, through `ImgEq`. -/
theorem img_main (s : State) (hseg : ∀ g ∈ segments, g.Loaded s.mem) (m : Word → Byte) (hm : ImgEq m s) :
    read64 m 0x101c0#64 = 0x13de0#64 ∧ read64 m 0x101c8#64 = 0x13ec8#64 ∧ read64 m 0x13fb0#64 = 0xcccccccccccccccd#64 := by
  have hr := hseg seg_rodata (by simp [segments])
  have hs := hseg seg_sdata (by simp [segments])
  refine ⟨?_, ?_, ?_⟩ <;> unfold read64
  · rw [show (0x101c0#64) = seg_rodata.base + BitVec.ofNat 64 48 from rfl,
      img_rd s m hm seg_rodata hr 48 8 (by simp [seg_rodata, Segment.size_bytesOfNat]) (by simp [seg_rodata, Segment.size_bytesOfNat])
        (by unfold Region.Disjoint ilG; decide) (by unfold Region.Disjoint tlW; decide)]
    decide +kernel
  · rw [show (0x101c8#64) = seg_rodata.base + BitVec.ofNat 64 56 from rfl,
      img_rd s m hm seg_rodata hr 56 8 (by simp [seg_rodata, Segment.size_bytesOfNat]) (by simp [seg_rodata, Segment.size_bytesOfNat])
        (by unfold Region.Disjoint ilG; decide) (by unfold Region.Disjoint tlW; decide)]
    decide +kernel
  · rw [show (0x13fb0#64) = seg_sdata.base + BitVec.ofNat 64 0 from rfl,
      img_rd s m hm seg_sdata hs 0 8 (by simp [seg_sdata, Segment.size_bytesOfNat]) (by simp [seg_sdata, Segment.size_bytesOfNat])
        (by unfold Region.Disjoint ilG; decide) (by unfold Region.Disjoint tlW; decide)]
    decide +kernel

section
variable {s : State} {k : Kern} {la : LaunchAuxv} {top : Word} {argv envp : List (List Byte)} {execfn : List Byte}
  {uid gid hwcap : Word} {rnd : BitVec 128} (h : SL s k la top argv envp execfn uid gid hwcap rnd)
include h

/-- `main`'s entry memory is the launch's on the image outside `.sbss` and `tlW`. -/
theorem SL.imgEq_main (z z1 : State) (w : State × Kern) (z2 zM : State) (hSC : StartCall s z) (hIC : InitCall z z1)
    (hpost : initLibcP.post ((z.reg 11 <<< 3) + z.reg 12 + 8#64, read64 z.mem (z.reg 12)) (z1.setReg 4 0x14110#64, k) w)
    (hS2 : Stage2Call z w.1 z2) (hMC : MainCall z2 zM) : ImgEq zM.mem s := by
  intro p hp hG hW
  have hbl := bss_below s top h.hA
  have hz2 : z.reg 2 = s.reg 2 := by rw [hSC.2.2.1, h.mask]
  have h22 : z2.reg 2 = s.reg 2 := by rw [hS2.2.2.1, hz2]
  have hS1 := ilS_of z1 (s.reg 2) (h.z1_sp z z1 hSC hIC)
  have hnS : ¬ (ilS (z1.setReg 4 0x14110#64)).mem p := by
    have e : ilS (z1.setReg 4 0x14110#64) = ilS z1 := by
      simp only [ilS, State.reg_setReg_other _ _ _ _ (show (2 : Reg) ≠ 4 by decide)]
    rw [e, hS1]; simp only [Region.mem]; bv_omega
  have hnF : ¬ (Region.mk (z2.reg 2 - 80#64) 80).mem p := by rw [h22]; simp only [Region.mem]; bv_omega
  rw [hMC.2.2.2.2.2.2.2.2.2.2.2.2.1 p hnF, hS2.2.2.2.2.2.2.2.2.2.2.2.1, hpost.2.2 p hnS hG hW]
  simp only [nocompiler_state]
  exact h.z1_out z z1 hSC hIC p (h.img_out p hp)

theorem SL.data_rw (a : Word) (n : Nat) (hc : (Region.mk seg_data.base seg_data.bytes.size).covers a n) :
    k.perm.canWrite a n ∧ k.perm.canRead a n :=
  img_rw k h.hna h.hro _ (h.segmap seg_data (by simp [segments])) (by simp [seg_data, Segment.size_bytesOfNat])
    (by simp [NumApart, seg_data, Segment.size_bytesOfNat]; decide) (by simp [NumApart, seg_data, seg_rodata, Segment.size_bytesOfNat])
    (by simp [NumApart, seg_data, seg_phdr, Segment.size_bytesOfNat]) a n hc

theorem SL.rodata_rd (a : Word) (n : Nat) (hc : (Region.mk 0x10190#64 64).covers a n) : k.perm.canRead a n := by
  have hm := h.segmap seg_rodata (by simp [segments])
  have e : (seg_rodata.base, seg_rodata.bytes.size) = (0x10190#64, 64) := by simp [seg_rodata, Segment.size_bytesOfNat]
  rw [e] at hm
  by_cases hr : (0x10190#64, 64) ∈ k.ro
  · exact Kern.canRead_of_ro k h.hna _ hm hr (by decide) a n hc
  · have hap : ∀ c ∈ k.ro, NumApart (0x10190#64, 64) c := by
      intro c hc'
      rcases roIn_num c (h.hro c hc') with rfl | rfl | rfl
      · simp [NumApart]
      · exact absurd hc' (by simpa [seg_rodata] using hr)
      · simp [NumApart, seg_phdr]
    exact Kern.canRead_of_apart k _ hm (by decide) hap (by simp [h.hna]) a n hc

end

/-- `.data` read through `ImgEq`. -/
theorem dat (s : State) (hseg : ∀ g ∈ segments, g.Loaded s.mem) (m : Word → Byte) (hm : ImgEq m s) (o n : Nat)
    (ho : o + n ≤ 464) : readLE m (0x13de0#64 + BitVec.ofNat 64 o) n = segLE seg_data o n := by
  have := img_rd s m hm seg_data (hseg seg_data (by simp [segments])) o n (by simp [seg_data, Segment.size_bytesOfNat]; omega)
    (by simp [seg_data, Segment.size_bytesOfNat])
    (by simp only [Region.Disjoint, ilG, seg_data]; constructor <;> bv_omega)
    (by simp only [Region.Disjoint, tlW, seg_data]; constructor <;> bv_omega)
  simpa [seg_data] using this

end Examples.Libc.Slen
