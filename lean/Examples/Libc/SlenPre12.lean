import Examples.Libc.SlenPre11

/-!
UNFINISHED (round 9): part of discharging `slen_correct_of_pre`'s hypothesis `hpre` (the start-up chain's
precondition at `__libc_start_main`'s entry) from `SlenLaunch`. The parts (SlenPre3..12) are proved; they are not yet
composed into `hpre`, so `SlenCorrect` is not proved (Examples/Libc/README.md).
-/
namespace Examples.Libc.Slen
open NoCompiler NoCompiler.Linux Examples.Libc.SlenImage Examples.Libc.SlenSpec

theorem datv (s : State) (hseg : ∀ g ∈ segments, g.Loaded s.mem) (m : Word → Byte) (hm : ImgEq m s) (o n v : Nat)
    (ho : o + n ≤ 464) (hv : segLE seg_data o n = v) (a : Word) (ha : a = 0x13de0#64 + BitVec.ofNat 64 o) :
    readLE m a n = v := by
  rw [ha, dat s hseg m hm o n ho, hv]

/-- The FILE fields `main` reads, through `ImgEq`. -/
theorem main_reads (s : State) (hseg : ∀ g ∈ segments, g.Loaded s.mem) (m : Word → Byte) (hm : ImgEq m s) :
    readLE m 0x13de0#64 4 = 9 ∧
    readLE m (0x13de0#64 + 8#64) 8 = 0 ∧
    readLE m (0x13de0#64 + 16#64) 8 = 0 ∧
    readLE m (0x13de0#64 + 40#64) 8 = 0 ∧
    readLE m (0x13de0#64 + 56#64) 8 = 0 ∧
    readLE m (0x13de0#64 + 64#64) 8 = 0x12308 ∧
    readLE m (0x13de0#64 + 88#64) 8 = 0x14208 ∧
    readLE m (0x13de0#64 + 96#64) 8 = 1024 ∧
    readLE m (0x13de0#64 + 120#64) 4 = 0 ∧
    readLE m (0x13de0#64 + 140#64) 4 = 0xffffffff ∧
    readLE m 0x13ec8#64 4 = 5 ∧
    readLE m (0x13ec8#64 + 32#64) 8 = 0 ∧
    readLE m (0x13ec8#64 + 72#64) 8 = 0x1240c ∧
    readLE m (0x13ec8#64 + 88#64) 8 = 0x14610 ∧
    readLE m (0x13ec8#64 + 96#64) 8 = 1024 ∧
    readLE m (0x13ec8#64 + 140#64) 4 = 0xffffffff ∧
    readLE m (0x13ec8#64 + 144#64) 4 = 0xa := by
  have D := datv s hseg m hm
  exact ⟨D 0 4 9 (by omega) (by decide +kernel) _ rfl, D 8 8 0 (by omega) (by decide +kernel) _ rfl, D 16 8 0 (by omega) (by decide +kernel) _ rfl, D 40 8 0 (by omega) (by decide +kernel) _ rfl, D 56 8 0 (by omega) (by decide +kernel) _ rfl, D 64 8 _ (by omega) (by decide +kernel) _ rfl, D 88 8 _ (by omega) (by decide +kernel) _ rfl, D 96 8 _ (by omega) (by decide +kernel) _ rfl, D 120 4 _ (by omega) (by decide +kernel) _ rfl, D 140 4 _ (by omega) (by decide +kernel) _ rfl, D 232 4 5 (by omega) (by decide +kernel) _ rfl, D 264 8 0 (by omega) (by decide +kernel) _ rfl, D 304 8 _ (by omega) (by decide +kernel) _ rfl, D 320 8 _ (by omega) (by decide +kernel) _ rfl, D 328 8 _ (by omega) (by decide +kernel) _ rfl, D 372 4 _ (by omega) (by decide +kernel) _ rfl, D 376 4 _ (by omega) (by decide +kernel) _ rfl⟩

theorem reg_apart (r r' : Region) (h0 : 0 < r.size) (h1 : r.base.toNat + r.size ≤ r'.base.toNat) (h2 : r'.base.toNat + r'.size ≤ 2 ^ 64) :
    r.Disjoint r' := by
  unfold Region.Disjoint
  have hb := r.base.isLt; have hb' := r'.base.isLt
  constructor <;> (rw [BitVec.toNat_sub]; omega)

theorem mST_eq (zM : State) (sp : Word) (hsp : zM.reg 2 = sp - 48#64) : mST zM = ⟨sp - 416#64, 368⟩ := by
  unfold mST; rw [hsp]; congr 1; bv_omega

section
variable {s : State} {k : Kern} {la : LaunchAuxv} {top : Word} {argv envp : List (List Byte)} {execfn : List Byte}
  {uid gid hwcap : Word} {rnd : BitVec 128} (h : SL s k la top argv envp execfn uid gid hwcap rnd)
include h

/-- `main`'s precondition at a state with the launch's image memory (outside `.sbss`/`tlW`), tp = 0x14110 (as
    `__init_tls` set it) and sp 48 bytes below the launch's. -/
theorem SL.mainPre_of (zM : State) (hm : ImgEq zM.mem s) (htp : zM.reg 4 = 0x14110#64)
    (hsp : zM.reg 2 = s.reg 2 - 48#64) (hfile : (k.files.lookup 0).isSome) : MainPre zM k := by
  have hseg := h.hseg
  have hlo := h.hA.1; simp only [Reg.sp] at hlo
  have hbl := bss_below s top h.hA
  have hfit := h.headfit; have ht := top.isLt
  obtain ⟨hgi, hgo, hmg⟩ := img_main s hseg zM.mem hm
  have hfi : fiOf zM = 0x13de0#64 := hgi
  have hfo : foOf zM = 0x13ec8#64 := hgo
  obtain ⟨i0, i8, i16, i40, i56, i64, i88, i96, i120, i140, o0, o32, o72, o88, o96, o140, o144⟩ := main_reads s hseg zM.mem hm
  have r64 : ∀ a v, readLE zM.mem a 8 = v → read64 zM.mem a = BitVec.ofNat 64 v := fun a v e => by unfold read64; rw [e]
  have hFi : mFi zM = ⟨0x13de0#64, 144⟩ := by simp only [mFi, hfi]
  have hFo : mFo zM = ⟨0x13ec8#64, 152⟩ := by simp only [mFo, hfo]
  have hE : mE zM = ⟨0x1406c#64, 4⟩ := by simp only [mE, htp]; rfl
  have hUi : mUi zM = ⟨0x14208#64, 1024⟩ := by simp only [mUi, hfi, r64 _ _ i88, r64 _ _ i96]; rfl
  have hUo : mUo zM = ⟨0x14610#64, 1024⟩ := by simp only [mUo, hfo, r64 _ _ o88, r64 _ _ o96]; rfl
  have hST := mST_eq zM (s.reg 2) hsp
  have stk : ∀ a n, (Region.mk (s.reg 2 - 416#64) 368).covers a n → k.perm.canWrite a n ∧ k.perm.canRead a n := by
    intro a n hc
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨.inl rfl, .inl rfl⟩
    simp only [Region.covers] at hc
    exact stk_rw s top k h.hA h.hna h.hro h.sm a n (by bv_omega) (by bv_omega)
  have dat' : ∀ a n, (Region.mk 0x13de0#64 144).covers a n ∨ (Region.mk 0x13ec8#64 152).covers a n →
      k.perm.canWrite a n ∧ k.perm.canRead a n := by
    intro a n hc; apply h.data_rw
    simp only [seg_data, Region.covers, Segment.size_bytesOfNat] at hc ⊢; rcases hc with hc | hc <;> bv_omega
  have bss' : ∀ a n, (Region.mk 0x1406c#64 4).covers a n ∨ (Region.mk 0x14208#64 1024).covers a n →
      k.perm.canWrite a n ∧ k.perm.canRead a n := by
    intro a n hc; apply h.bss_rw
    simp only [seg_bss, Region.covers, Array.size_replicate] at hc ⊢; rcases hc with hc | hc <;> bv_omega
  have hD := reg_apart
  have hst1 : 0x14a10 ≤ (s.reg 2 - 416#64).toNat := by bv_omega
  have hst2 : (s.reg 2 - 416#64).toNat + 368 ≤ 2 ^ 64 := by bv_omega
  refine
    { perm := ⟨?_, ?_⟩
      magic := hmg
      alE := by rw [htp]; decide
      alFi := by rw [hfi]; decide
      stdin := by
        rw [hfi]
        refine ⟨by rw [r64 _ _ i64], by rw [r64 _ _ i40, r64 _ _ i56], by unfold read32; rw [i0]; decide,
          by rw [r64 _ _ i96]; decide, by rw [i140]; decide, .inl ?_⟩
        unfold frAvail; rw [r64 _ _ i8, r64 _ _ i16]; rfl
      bufIn := by rw [hfi, r64 _ _ i96]; decide
      eof := by intro he; unfold EofSet read32 at he; rw [hfi, i0] at he; exact absurd he (by decide)
      file := by
        have : fdIn zM = 0 := by unfold fdIn fdOf; rw [hfi, i120]; decide
        rw [this]; exact hfile
      fdNonneg := by
        have : fdIn zM = 0 := by unfold fdIn fdOf; rw [hfi, i120]; decide
        rw [this]; decide
      fdOutNonneg := by
        have o120 : readLE zM.mem (0x13ec8#64 + 120#64) 4 = 1 := datv s hseg zM.mem hm 352 4 1 (by omega) (by decide +kernel) _ rfl
        unfold fdOf; rw [hfo, o120]; decide
      alFo := by rw [hfo]; decide
      lockO := by rw [hfo, o140]; decide
      wendO := by rw [hfo, r64 _ _ o32]; rfl
      flagsO := by unfold read32; rw [hfo, o0]; decide
      writeO := by rw [hfo, r64 _ _ o72]
      bufO := by rw [hfo, r64 _ _ o96]; decide
      lbfO := by rw [hfo, o144]; decide
      dSFi := by rw [hST, hFi]; exact (hD _ _ (by simp) (by simp; omega) hst2).symm
      dSE := by rw [hST, hE]; exact (hD _ _ (by simp) (by simp; omega) hst2).symm
      dSUi := by rw [hST, hUi]; exact (hD _ _ (by simp) (by simp; omega) hst2).symm
      dSFo := by rw [hST, hFo]; exact (hD _ _ (by simp) (by simp; omega) hst2).symm
      dSUo := by rw [hST, hUo]; exact (hD _ _ (by simp) (by simp; omega) hst2).symm
      dFiE := by rw [hFi, hE]; unfold Region.Disjoint; decide
      dFiUi := by rw [hFi, hUi]; unfold Region.Disjoint; decide
      dFiFo := by rw [hFi, hFo]; unfold Region.Disjoint; decide
      dFiUo := by rw [hFi, hUo]; unfold Region.Disjoint; decide
      dEUi := by rw [hE, hUi]; unfold Region.Disjoint; decide
      dEFo := by rw [hE, hFo]; unfold Region.Disjoint; decide
      dEUo := by rw [hE, hUo]; unfold Region.Disjoint; decide
      dUiFo := by rw [hUi, hFo]; unfold Region.Disjoint; decide
      dUiUo := by rw [hUi, hUo]; unfold Region.Disjoint; decide
      dFoUo := by rw [hFo, hUo]; unfold Region.Disjoint; decide
      dGS := by rw [hST]; exact hD _ _ (by simp [mG]) (by simp [mG]; omega) hst2
      dGFi := by rw [hFi]; unfold Region.Disjoint mG; decide
      dGE := by rw [hE]; unfold Region.Disjoint mG; decide
      dGUi := by rw [hUi]; unfold Region.Disjoint mG; decide
      dCS := by rw [hST]; exact hD _ _ (by simp [mC]) (by simp [mC]; omega) hst2
      dCFi := by rw [hFi]; unfold Region.Disjoint mC; decide
      dCE := by rw [hE]; unfold Region.Disjoint mC; decide
      dCUi := by rw [hUi]; unfold Region.Disjoint mC; decide
      d0S := by rw [hST]; exact hD _ _ (by simp) (by simp; omega) hst2
      d0Fo := by rw [hFo]; unfold Region.Disjoint; decide }
  · rintro a n (h0 | ⟨r, hr, hc⟩)
    · exact .inl h0
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h.rodata_rd a n (by simp only [mG, Region.covers] at hc ⊢; bv_omega)
    · exact (h.sdata_rw a n (by simp only [mC, seg_sdata, Region.covers, Segment.size_bytesOfNat] at hc ⊢; bv_omega)).2
    · rw [hST] at hc; exact (stk a n hc).2
    · rw [hFi] at hc; exact (dat' a n (.inl hc)).2
    · rw [hE] at hc; exact (bss' a n (.inl hc)).2
    · rw [hUi] at hc; exact (bss' a n (.inr hc)).2
    · rw [hFo] at hc; exact (dat' a n (.inr hc)).2
  · rintro a n (h0 | ⟨r, hr, hc⟩)
    · exact .inl h0
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [hST] at hc; exact (stk a n hc).1
    · rw [hFi] at hc; exact (dat' a n (.inl hc)).1
    · rw [hE] at hc; exact (bss' a n (.inl hc)).1
    · rw [hUi] at hc; exact (bss' a n (.inr hc)).1
    · rw [hFo] at hc; exact (dat' a n (.inr hc)).1

/-- (C): `main`'s precondition at every `MainCall` after `__init_libc` and stage 2. -/
theorem SL.mainPre (hfile : (k.files.lookup 0).isSome) (z z1 : State) (w : State × Kern) (z2 zM : State)
    (hSC : StartCall s z) (hIC : InitCall z z1)
    (hpost : initLibcP.post ((z.reg 11 <<< 3) + z.reg 12 + 8#64, read64 z.mem (z.reg 12)) (z1.setReg 4 0x14110#64, k) w)
    (hpres : Preserved (z1.setReg 4 0x14110#64) w.1) (hS2 : Stage2Call z w.1 z2) (hMC : MainCall z2 zM) :
    MainPre zM w.2 := by
  have hk : w.2 = k := hpost.1
  rw [hk]
  have hz2 : z.reg 2 = s.reg 2 := by rw [hSC.2.2.1, h.mask]
  have htp : zM.reg 4 = 0x14110#64 := by
    rw [hMC.2.2.2.2.2.2.2.2.2.2.2.1 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hS2.2.2.2.2.2.2.2.2.2.2.1 4 (by decide) (by decide) (by decide) (by decide) (by decide),
      hpres 4 (by decide)]
    exact State.reg_setReg_same _ _ _ (by decide)
  have hsp : zM.reg 2 = s.reg 2 - 48#64 := by rw [hMC.2.2.2.1, hS2.2.2.1, hz2]
  exact h.mainPre_of zM (h.imgEq_main z z1 w z2 zM hSC hIC hpost hS2 hMC) htp hsp hfile

end

end Examples.Libc.Slen
