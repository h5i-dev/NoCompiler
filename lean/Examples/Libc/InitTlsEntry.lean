import Examples.Libc.InitTlsLoop
import NoCompiler.Linux.RunN
namespace Examples.Libc.Slen
open NoCompiler NoCompiler.Linux Examples.Libc.SlenImage

/-- `__init_tls`'s memory after its prologue: the seven saved registers below sp. -/
def tlM (s : State) : Word → Byte :=
  writeLE (writeLE (writeLE (writeLE (writeLE (writeLE (writeLE s.mem
    (s.reg 2 - 8#64) (s.reg 1).toNat 8) (s.reg 2 - 16#64) (s.reg 8).toNat 8) (s.reg 2 - 24#64) (s.reg 9).toNat 8)
    (s.reg 2 - 32#64) (s.reg 18).toNat 8) (s.reg 2 - 40#64) (s.reg 19).toNat 8) (s.reg 2 - 48#64) (s.reg 20).toNat 8)
    (s.reg 2 - 56#64) (s.reg 21).toNat 8

/-- The phdr facts in memory `m`, at the literal addresses the loop computes. -/
def PhdrLit (m : Word → Byte) : Prop :=
  readLE m 65600#64 4 = 6 ∧ readLE m 65656#64 4 = 1 ∧ readLE m 65712#64 4 = 1 ∧ readLE m 65768#64 4 = 1 ∧
  readLE m 65824#64 4 = 0x6474e551 ∧ readLE m 65880#64 4 = 0x70000003 ∧
  read64 m 65616#64 = 0x10040#64 ∧ read64 m 65864#64 = 0

theorem tlM_off (s : State) (p : Word) (hp : ¬ (Region.mk (s.reg 2 - 64#64) 64).mem p) : tlM s p = s.mem p := by
  have hc : ∀ o, o = 8 ∨ o = 16 ∨ o = 24 ∨ o = 32 ∨ o = 40 ∨ o = 48 ∨ o = 56 →
      (Region.mk (s.reg 2 - 64#64) 64).covers (s.reg 2 - BitVec.ofNat 64 o) 8 := by
    intro o ho; simp only [Region.covers]; rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> bv_omega
  unfold tlM
  rw [writeLE_of_not_mem (hc 56 (by omega)) hp, writeLE_of_not_mem (hc 48 (by omega)) hp,
    writeLE_of_not_mem (hc 40 (by omega)) hp, writeLE_of_not_mem (hc 32 (by omega)) hp,
    writeLE_of_not_mem (hc 24 (by omega)) hp, writeLE_of_not_mem (hc 16 (by omega)) hp,
    writeLE_of_not_mem (hc 8 (by omega)) hp]

theorem tlM_read64 (s : State) (a : Word) (o : Nat) (ho : o + 8 ≤ 24)
    (hd : (Region.mk (a + 24#64) 24).Disjoint ⟨s.reg 2 - 64#64, 64⟩) :
    read64 (tlM s) (a + 24#64 + BitVec.ofNat 64 o) = read64 s.mem (a + 24#64 + BitVec.ofNat 64 o) := by
  apply read64_congr_on; intro j hj
  exact tlM_off s _ (not_mem_of_mem_disj hd.symm (by simp only [Region.mem]; bv_omega))

theorem tl_e64 (sp : Word) : sp + 18446744073709551552#64 = sp - 64#64 := by bv_omega
theorem tl_eS (sp : Word) (o : Nat) (h : o ≤ 64) : sp - 64#64 + BitVec.ofNat 64 o = sp - BitVec.ofNat 64 (64 - o) := by
  bv_omega

/-- `__init_tls`'s prologue to the phdr loop (0x117a4..0x11818), for slen's aux (AT_PHDR 0x10040, AT_PHENT 56,
    AT_PHNUM 6). -/
theorem tl_entry (s : State) (k : Kern) (R : State × Kern → Prop) (hpc : s.pc = 0x117a4#64) (hx : s.exit = none)
    (hsp : aligned (s.reg 2) 16) (a : Word) (h10 : s.reg 10 = a) (hal : aligned a 8)
    (hph : read64 s.mem (a + 24#64) = 0x10040#64) (hpe : read64 s.mem (a + 32#64) = 56#64)
    (hpn : read64 s.mem (a + 40#64) = 6#64)
    (hw : ∀ o, 8 ≤ o → o ≤ 64 → k.perm.canWrite (s.reg 2 - BitVec.ofNat 64 o) 8)
    (hra : ∀ o, o = 24 ∨ o = 32 ∨ o = 40 → k.perm.canRead (a + BitVec.ofNat 64 o) 8)
    (hdA : (Region.mk (a + 24#64) 24).Disjoint ⟨s.reg 2 - 64#64, 64⟩)
    (K : ∀ v, v.pc = 0x11830#64 → TlLoop s (tlM s) 0 v → PReachK code initTlsD R (v, k)) :
    PReachK code initTlsD R (s, k) := by
  have e40 : a + 40#64 = a + 24#64 + BitVec.ofNat 64 16 := by bv_omega
  have e24 : a + 24#64 = a + 24#64 + BitVec.ofNat 64 0 := by bv_omega
  have e32 : a + 32#64 = a + 24#64 + BitVec.ofNat 64 8 := by bv_omega
  have r40 : read64 (tlM s) (a + 40#64) = 6#64 := by rw [e40, tlM_read64 s a 16 (by omega) hdA, ← e40]; exact hpn
  have r24 : read64 (tlM s) (a + 24#64) = 0x10040#64 := by rw [e24, tlM_read64 s a 0 (by omega) hdA, ← e24]; exact hph
  have r32 : read64 (tlM s) (a + 32#64) = 56#64 := by rw [e32, tlM_read64 s a 8 (by omega) hdA, ← e32]; exact hpe
  have al : ∀ o, o = 24 ∨ o = 32 ∨ o = 40 → aligned (a + BitVec.ofNat 64 o) 8 := by
    intro o ho; unfold aligned at *; rcases ho with rfl | rfl | rfl <;> bv_omega
  have hm : (writeLE (writeLE (writeLE (writeLE (writeLE (writeLE (writeLE s.mem
    (s.reg 2 - 8#64) (s.reg 1).toNat 8) (s.reg 2 - 16#64) (s.reg 8).toNat 8) (s.reg 2 - 24#64) (s.reg 9).toNat 8)
    (s.reg 2 - 32#64) (s.reg 18).toNat 8) (s.reg 2 - 40#64) (s.reg 19).toNat 8) (s.reg 2 - 48#64) (s.reg 20).toNat 8)
    (s.reg 2 - 56#64) (s.reg 21).toNat 8) = tlM s := rfl
  nocompiler_run_n 18 [hx, hpc, tl_e64, tl_eS _ 56 (by omega), sw_alS hsp 8 rfl, tl_eS _ 48 (by omega), sw_alS hsp 16 rfl, tl_eS _ 40 (by omega), sw_alS hsp 24 rfl, tl_eS _ 32 (by omega), sw_alS hsp 32 rfl, tl_eS _ 24 (by omega), sw_alS hsp 40 rfl, tl_eS _ 16 (by omega), sw_alS hsp 48 rfl, tl_eS _ 8 (by omega), sw_alS hsp 56 rfl, h10, hm, r40, al 40 (by omega), r24, al 24 (by omega), r32, al 32 (by omega)] using [hw, hra]
  iterate 12 nocompiler_wstep [hx]
  refine K _ (by simp only [nocompiler_state]) ⟨?_, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (simp (disch := nocompiler_decide_closed) only [nocompiler_state, hx]; done)
    | (simp (disch := nocompiler_decide_closed) only [nocompiler_state]; decide)
    | (intro q hq a2 a8 a9
       have hne : q ≠ 5 ∧ q ≠ 6 ∧ q ≠ 7 ∧ q ≠ 10 ∧ q ≠ 11 ∧ q ≠ 12 ∧ q ≠ 13 ∧ q ≠ 14 ∧ q ≠ 15 ∧ q ≠ 16 ∧ q ≠ 17 ∧
           q ≠ 28 ∧ q ≠ 29 ∧ q ≠ 30 := by revert hq; revert q; decide
       obtain ⟨n5, n6, n7, n10, n11, n12, n13, n14, n15, n16, n17, n28, n29, n30⟩ := hne
       simp only [State.setPc_reg, State.setMem_reg, State.reg_setReg_other _ _ _ _ n5, State.reg_setReg_other _ _ _ _ n6,
         State.reg_setReg_other _ _ _ _ n7, State.reg_setReg_other _ _ _ _ n10, State.reg_setReg_other _ _ _ _ n11,
         State.reg_setReg_other _ _ _ _ n12, State.reg_setReg_other _ _ _ _ n13, State.reg_setReg_other _ _ _ _ n14,
         State.reg_setReg_other _ _ _ _ n15, State.reg_setReg_other _ _ _ _ n16, State.reg_setReg_other _ _ _ _ n17,
         State.reg_setReg_other _ _ _ _ n28, State.reg_setReg_other _ _ _ _ n29, State.reg_setReg_other _ _ _ _ n30,
         State.reg_setReg_other _ _ _ _ a2, State.reg_setReg_other _ _ _ _ a9])


/-- The six iterations of the phdr loop, from header 0 to its exit (0x11880). -/
theorem tl_chain (s : State) (k : Kern) (m : Word → Byte) (R : State × Kern → Prop) (hP : PhdrLit m)
    (hr : ∀ i, i < 6 → k.perm.canRead (BitVec.ofNat 64 (65600 + 56 * i)) 4)
    (hrv : k.perm.canRead 65616#64 8) (hrm : k.perm.canRead 65864#64 8) (hrs : k.perm.canRead 0x13fc8#64 4)
    (u : State) (hpc : u.pc = 0x11830#64) (hL : TlLoop s m 0 u)
    (K : ∀ v : State, v.pc = 0x11880#64 → TlOut s m v → PReachK code initTlsD R (v, k)) :
    PReachK code initTlsD R (u, k) := by
  obtain ⟨t0, t1, t2, t3, t4, t5, va, ms⟩ := hP
  refine tl_iter0 s k m R u hpc hL t0 (hr 0 (by omega)) va hrv (fun v1 h1 hL1 => ?_)
  refine tl_iter1 s k m R v1 h1 hL1 t1 (hr 1 (by omega)) (fun v2 h2 hL2 => ?_)
  refine tl_iter2 s k m R v2 h2 hL2 t2 (hr 2 (by omega)) (fun v3 h3 hL3 => ?_)
  refine tl_iter3 s k m R v3 h3 hL3 t3 (hr 3 (by omega)) (fun v4 h4 hL4 => ?_)
  refine tl_iter4 s k m R v4 h4 hL4 t4 (hr 4 (by omega)) ms hrm hrs (fun v5 h5 hL5 => ?_)
  exact tl_iter5 s k m R v5 h5 hL5 t5 (hr 5 (by omega)) K

end Examples.Libc.Slen
