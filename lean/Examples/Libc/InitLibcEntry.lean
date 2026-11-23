import Examples.Libc.InitTls
import NoCompiler.Linux.RunN
namespace Examples.Libc.Slen
open NoCompiler NoCompiler.Linux Examples.Libc.SlenImage

/-- `.sbss`: __environ, __sysinfo, __progname(_full), __hwcap (0x13fd0..0x14018). -/
def ilG : Region := ⟨0x13fd0#64, 72⟩

/-- `__init_libc`'s stack: its 384-byte frame and `__init_tls`'s 64 below. -/
def ilS (s : State) : Region := ⟨s.reg 2 - 448#64, 448⟩

/-- The two words of `libc` `__init_libc` itself writes: `libc.auxv` (0x141a0), `libc.page_size` (0x141c8). -/
def ilL : Region := ⟨0x141a0#64, 8⟩
def ilP : Region := ⟨0x141c8#64, 8⟩

theorem not_ilL_of_tlW {p : Word} (h : ¬ tlW.mem p) : ¬ ilL.mem p := fun h' =>
  h (by simp only [tlW, ilL, Region.mem] at h' ⊢; bv_omega)
theorem not_ilP_of_tlW {p : Word} (h : ¬ tlW.mem p) : ¬ ilP.mem p := fun h' =>
  h (by simp only [tlW, ilP, Region.mem] at h' ⊢; bv_omega)

/-- Memory `m` as at `s` outside `__init_libc`'s stack, `.sbss` and the two libc words it writes. -/
def IlFrame (s : State) (m : Word → Byte) : Prop :=
  ∀ p, ¬ (ilS s).mem p → ¬ ilG.mem p → ¬ ilL.mem p → ¬ ilP.mem p → m p = s.mem p

/-- What holds at the cuts of `__init_libc` from `s`: frame at sp - 384, s0 = pn, the four saved registers in
    their slots, the callee-saved registers it does not use as at entry, memory per `IlFrame`. -/
def IlCommon (s : State) (u : State) : Prop :=
  u.exit = none ∧ u.reg 2 = s.reg 2 - 384#64 ∧ u.reg 8 = s.reg 11 ∧
  (∀ q ∈ preservedRegs, q ≠ 2 → q ≠ 8 → q ≠ 9 → q ≠ 18 → u.reg q = s.reg q) ∧
  read64 u.mem (s.reg 2 - 8#64) = s.reg 1 ∧ read64 u.mem (s.reg 2 - 16#64) = s.reg 8 ∧
  read64 u.mem (s.reg 2 - 24#64) = s.reg 9 ∧ read64 u.mem (s.reg 2 - 32#64) = s.reg 18 ∧
  IlFrame s u.mem ∧ u.trace = s.trace

/-- A permission whose regions all lie within `R` is below `Q` if `Q` lets one write all of `R`. -/
theorem perm_le_of_within {P Q : Perm} {R : Region} (hw : ∀ p n, R.covers p n → Q.canWrite p n)
    (h : ∀ r ∈ P.rd ++ P.wr, r.within R) : P.le Q := by
  constructor
  · rintro a n (h0 | ⟨r, hr, hc⟩)
    · exact .inl h0
    · exact Perm.canRead_of_canWrite (hw a n (Region.covers_of_within hc (h r hr)))
  · rintro a n (h0 | ⟨r, hr, hc⟩)
    · exact .inl h0
    · exact hw a n (Region.covers_of_within hc (h r (List.mem_append.2 (.inr hr))))

/-- Memory after `__init_libc`'s four saves. -/
def ilM0 (s : State) : Word → Byte :=
  writeLE (writeLE (writeLE (writeLE s.mem (s.reg 2 - 8#64) (s.reg 1).toNat 8) (s.reg 2 - 16#64) (s.reg 8).toNat 8)
    (s.reg 2 - 24#64) (s.reg 9).toNat 8) (s.reg 2 - 32#64) (s.reg 18).toNat 8

theorem ilM0_off (s : State) (p : Word) (hp : ¬ (ilS s).mem p) : ilM0 s p = s.mem p := by
  have hc : ∀ o, o = 8 ∨ o = 16 ∨ o = 24 ∨ o = 32 → (ilS s).covers (s.reg 2 - BitVec.ofNat 64 o) 8 := by
    intro o ho; simp only [ilS, Region.covers]; rcases ho with rfl | rfl | rfl | rfl <;> bv_omega
  unfold ilM0
  rw [writeLE_of_not_mem (hc 32 (by omega)) hp, writeLE_of_not_mem (hc 24 (by omega)) hp,
    writeLE_of_not_mem (hc 16 (by omega)) hp, writeLE_of_not_mem (hc 8 (by omega)) hp]

theorem il_e384 (sp : Word) : sp + 18446744073709551232#64 = sp - 384#64 := by bv_omega
theorem il_eS (sp : Word) (o : Nat) (h : o ≤ 384) : sp - 384#64 + BitVec.ofNat 64 o = sp - BitVec.ofNat 64 (384 - o) := by
  bv_omega

theorem memset_proc : VerifiedProc code memset_dom memset_entry memsetSpec.toPns :=
  VerifiedImg.toProcNoSys memset_verified (noEcall_of (by decide +kernel))

/-- `__init_libc`'s prologue (0x112f0..0x1131c) and the call `memset(aux, 0, 304)`; then at 0x11320. -/
theorem il_entry (s : State) (k : Kern) (R : State × Kern → Prop) (hpc : s.pc = 0x112f0#64) (hx : s.exit = none)
    (hsp : aligned (s.reg 2) 16) (hlo : 448 ≤ (s.reg 2).toNat)
    (hw : ∀ p n, (ilS s).covers p n → k.perm.canWrite p n)
    (K : ∀ v, v.pc = 0x11320#64 → IlCommon s v → v.reg 9 = s.reg 10 → PReachK code initLibcD R (v, k)) :
    PReachK code initLibcD R (s, k) := by
  have wS : ∀ o, 8 ≤ o → o ≤ 448 → k.perm.canWrite (s.reg 2 - BitVec.ofNat 64 o) 8 := fun o h1 h3 =>
    hw _ _ (by simp only [ilS, Region.covers]; bv_omega)
  nocompiler_run_n 5 [hx, hpc, il_e384, il_eS _ 376 (by omega), sw_alS hsp 8 rfl, il_eS _ 368 (by omega), sw_alS hsp 16 rfl, il_eS _ 360 (by omega), sw_alS hsp 24 rfl, il_eS _ 352 (by omega), sw_alS hsp 32 rfl] using [wS]
  iterate 7 nocompiler_wstep [hx]
  have hd : (s.reg 2 - 384#64 + 48#64) = s.reg 2 - 336#64 := by bv_omega
  refine VerifiedProc.call memset_proc (s.reg 2 - 336#64, 304) ⟨by simp only [nocompiler_state]; rfl,
    by simp only [nocompiler_state]; exact hx, ?_, ?_, ?_⟩ ⟨⟨?_, ?_, by decide, by decide, ?_⟩, ?_⟩
    (Dom.sub_of_ranges (by decide)) ?_
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.ra] <;> decide
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.ra] <;> decide
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.sp]; unfold aligned at *; bv_omega
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.a0, hd]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.a2]
  · bv_omega
  · refine perm_le_of_within hw ?_
    intro r hr
    simp only [Spec.perm, memsetSpec, List.mem_append, List.mem_singleton, List.nil_append, List.not_mem_nil, false_or] at hr
    rcases hr with rfl | rfl
    · simp only [ilS, Region.within]; bv_omega
    · simp (disch := nocompiler_decide_closed) only [Spec.stackRegion, nocompiler_state, Reg.sp, ilS, Region.within]; bv_omega
  rintro ⟨y, ky⟩ (⟨hxy, hpcy, hpresy, ha0, hk, htry, hfr⟩ | ⟨_, hex⟩)
  rotate_left
  · exact hex.1.elim
  simp only at hxy hpcy hpresy ha0 hk htry hfr
  subst hk
  have hoff : ∀ p, ¬ (Region.mk (s.reg 2 - 336#64) 304).mem p → y.mem p = ilM0 s p := by
    intro p h1
    refine hfr p ?_
    rintro ⟨r, hr, hm⟩
    simp only [Spec.perm, memsetSpec, List.mem_append, List.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact h1 hm
    · simp (disch := nocompiler_decide_closed) only [Spec.stackRegion, nocompiler_state, Reg.sp, Region.mem] at hm; omega
  have hsl : ∀ o, o = 8 ∨ o = 16 ∨ o = 24 ∨ o = 32 → read64 y.mem (s.reg 2 - BitVec.ofNat 64 o) =
      read64 (ilM0 s) (s.reg 2 - BitVec.ofNat 64 o) := by
    intro o ho; apply read64_congr_on; intro j hj
    exact hoff _ (by simp only [Region.mem]; rcases ho with rfl | rfl | rfl | rfl <;> bv_omega)
  have hpy : ∀ q ∈ preservedRegs, y.reg q = _ := hpresy
  refine K y (by rw [hpcy]; simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.ra])
    ⟨hxy, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_
  · rw [hpy 2 (by decide)]; simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · rw [hpy 8 (by decide)]; simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · intro q hq a2 a8 a9 a18
    rw [hpy q hq]
    have hne : q ≠ 1 ∧ q ≠ 10 ∧ q ≠ 11 ∧ q ≠ 12 := by revert hq; revert q; decide
    simp only [State.setPc_reg, State.setMem_reg, State.reg_setReg_other _ _ _ _ hne.1, State.reg_setReg_other _ _ _ _ hne.2.1,
      State.reg_setReg_other _ _ _ _ hne.2.2.1, State.reg_setReg_other _ _ _ _ hne.2.2.2, State.reg_setReg_other _ _ _ _ a2,
      State.reg_setReg_other _ _ _ _ a8, State.reg_setReg_other _ _ _ _ a9]
  · rw [hsl 8 (by simp)]; unfold ilM0; simp (disch := nocompiler_decide_closed) only [slot_ne, fw_slot_same]
  · rw [hsl 16 (by simp)]; unfold ilM0; simp (disch := nocompiler_decide_closed) only [slot_ne, fw_slot_same]
  · rw [hsl 24 (by simp)]; unfold ilM0; simp (disch := nocompiler_decide_closed) only [slot_ne, fw_slot_same]
  · rw [hsl 32 (by simp)]; unfold ilM0; simp (disch := nocompiler_decide_closed) only [slot_ne, fw_slot_same]
  · intro p a _ _ _
    rw [hoff p (fun h => a (by simp only [ilS, Region.mem] at h ⊢; bv_omega))]; exact ilM0_off s p a
  · rw [htry]; simp only [nocompiler_state]
  · rw [hpy 9 (by decide)]; simp (disch := nocompiler_decide_closed) only [nocompiler_state]

end Examples.Libc.Slen
