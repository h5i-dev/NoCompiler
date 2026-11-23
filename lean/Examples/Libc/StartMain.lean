import Examples.Libc.Stage2
import NoCompiler.Linux.RunN
namespace Examples.Libc.Slen
open NoCompiler NoCompiler.Linux Examples.Libc.SlenImage

/-- `VerifiedProc` for a function that sets tp to `tpv` (through `__init_tp`'s `__set_thread_area`): its
    `Done` is taken against the entry state with tp already `tpv`, so `Preserved` is the right frame. -/
def VerifiedProcT {α : Type} (c : Code) (D : Dom) (entry : Word) (sp : SpecP α) (tpv : Word) : Prop :=
  ∀ a s k, Entry D entry s → sp.pre a s k →
    PReachK c D (fun y => Final D y.1 ∧ sp.Done a (s.setReg 4 tpv, k) y) (s, k)

/-- `__init_libc` with the assembly `__set_thread_area` `__init_tls` calls (no symbol size, so not in the
    image's domains). -/
def initLibcD : Dom := __init_libc_dom ++ __set_thread_area_dom

/-- `__libc_start_main` with stage 2 and what it reaches. -/
def lsmD : Dom := __libc_start_main_dom ++ __set_thread_area_dom ++ stage2D

/-- `__init_libc(envp, argv[0])`'s call from `__libc_start_main` entered at `s` (0x115b8). -/
def InitCall (s z : State) : Prop :=
  z.pc = 0x112f0#64 ∧ z.exit = none ∧ z.reg 1 = 0x115bc#64 ∧ z.reg 2 = s.reg 2 - 32#64 ∧
  z.reg 10 = (s.reg 11 <<< 3) + s.reg 12 + 8#64 ∧ z.reg 11 = read64 s.mem (s.reg 12) ∧
  z.reg 8 = s.reg 12 ∧ z.reg 9 = s.reg 11 ∧ z.reg 18 = s.reg 10 ∧
  (∀ q ∈ preservedRegs, q ≠ 2 → q ≠ 8 → q ≠ 9 → q ≠ 18 → z.reg q = s.reg q) ∧
  (∀ p, ¬ (Region.mk (s.reg 2 - 32#64) 32).mem p → z.mem p = s.mem p) ∧
  read64 z.mem (s.reg 2 - 8#64) = s.reg 1 ∧ read64 z.mem (s.reg 2 - 16#64) = s.reg 8 ∧
  read64 z.mem (s.reg 2 - 24#64) = s.reg 9 ∧ read64 z.mem (s.reg 2 - 32#64) = s.reg 18 ∧ z.trace = s.trace

/-- The tail call of stage 2 (0x115e4, `jr t1`) after `__init_libc` returned `w`: main, argc, argv in a0..a2, the
    frame popped (ra, s0, s1, s2 reloaded from it), the rest as at `w`. -/
def Stage2Call (s w z : State) : Prop :=
  z.pc = 0x115e8#64 ∧ z.exit = none ∧ z.reg 2 = s.reg 2 ∧ z.reg 10 = w.reg 18 ∧ z.reg 11 = w.reg 9 ∧
  z.reg 12 = w.reg 8 ∧ z.reg 1 = read64 w.mem (s.reg 2 - 8#64) ∧ z.reg 8 = read64 w.mem (s.reg 2 - 16#64) ∧
  z.reg 9 = read64 w.mem (s.reg 2 - 24#64) ∧ z.reg 18 = read64 w.mem (s.reg 2 - 32#64) ∧
  (∀ q ∈ preservedRegs, q ≠ 2 → q ≠ 8 → q ≠ 9 → q ≠ 18 → z.reg q = w.reg q) ∧ z.mem = w.mem ∧ z.trace = w.trace

/-- `__libc_start_main(main, argc, argv)` (musl src/env/__libc_start_main.c), given `__init_libc`'s
    specification `I` (arguments envp, argv[0]) and stage 2's `S` (which does not return): it calls
    `__init_libc(envp, argv[0])`, then tail-calls stage 2. It ends where they end it. -/
def lsmP (I : SpecP (Word × Word)) (S : SpecP Unit) (tpv : Word) : SpecP Unit where
  pre := fun _ s k => (Perm.mk [⟨s.reg 12, 8⟩] [⟨s.reg 2 - 32#64, 32⟩]).le k.perm ∧ aligned (s.reg 12) 8 ∧
    (Region.mk (s.reg 12) 8).Disjoint ⟨s.reg 2 - 32#64, 32⟩ ∧
    (∀ z, InitCall s z → I.pre ((s.reg 11 <<< 3) + s.reg 12 + 8#64, read64 s.mem (s.reg 12)) z k) ∧
    (∀ z w, InitCall s z → I.post ((s.reg 11 <<< 3) + s.reg 12 + 8#64, read64 s.mem (s.reg 12)) (z.setReg 4 tpv, k) w →
      w.2.perm = k.perm ∧ read64 w.1.mem (s.reg 2 - 8#64) = s.reg 1 ∧ read64 w.1.mem (s.reg 2 - 16#64) = s.reg 8 ∧
      read64 w.1.mem (s.reg 2 - 24#64) = s.reg 9 ∧ read64 w.1.mem (s.reg 2 - 32#64) = s.reg 18) ∧
    (∀ z w z2, InitCall s z → I.post ((s.reg 11 <<< 3) + s.reg 12 + 8#64, read64 s.mem (s.reg 12)) (z.setReg 4 tpv, k) w →
      Preserved (z.setReg 4 tpv) w.1 → Stage2Call s w.1 z2 → S.pre () z2 w.2)
  post := fun _ _ _ => False
  onExit := fun _ x y => ∃ z, InitCall x.1 z ∧
    (I.onExit ((x.1.reg 11 <<< 3) + x.1.reg 12 + 8#64, read64 x.1.mem (x.1.reg 12)) (z.setReg 4 tpv, x.2) y ∨
     ∃ w z2, w.1.exit = none ∧ w.1.pc = 0x115bc#64 ∧ Preserved (z.setReg 4 tpv) w.1 ∧
       I.post ((x.1.reg 11 <<< 3) + x.1.reg 12 + 8#64, read64 x.1.mem (x.1.reg 12)) (z.setReg 4 tpv, x.2) w ∧
       Stage2Call x.1 w.1 z2 ∧ S.onExit () (z2, w.2) y)

theorem lsm_e32 (sp : Word) : sp + 18446744073709551584#64 = sp - 32#64 := by bv_omega
theorem lsm_eS (sp : Word) (o : Nat) (h : o ≤ 32) : sp - 32#64 + BitVec.ofNat 64 o = sp - BitVec.ofNat 64 (32 - o) := by
  bv_omega
theorem lsm_e0 (sp : Word) : sp - 32#64 + 0#64 = sp - 32#64 := by bv_omega
theorem lsm_eT (sp : Word) : sp - 32#64 + 32#64 = sp := by bv_omega

/-- The tail call of stage 2 from `z2`. -/
theorem lsm_s2 (I : SpecP (Word × Word)) (S : SpecP Unit) (tpv : Word) (hS : VerifiedProcNR code stage2D libc_start_main_stage2_entry S)
    (hSp : ∀ x y, ¬ S.post () x y) (s : State) (k : Kern)
    (hsp : aligned (s.reg 2) 16) (z : State) (hIC : InitCall s z) (w : State × Kern) (hxw : w.1.exit = none)
    (hpcw : w.1.pc = 0x115bc#64) (hpw : Preserved (z.setReg 4 tpv) w.1)
    (hpost : I.post ((s.reg 11 <<< 3) + s.reg 12 + 8#64, read64 s.mem (s.reg 12)) (z.setReg 4 tpv, k) w)
    (hs1 : read64 w.1.mem (s.reg 2 - 8#64) = s.reg 1) (z2 : State) (hSC : Stage2Call s w.1 z2) (hSpre : S.pre () z2 w.2) :
    PReachK code lsmD (fun y => Final lsmD y.1 ∧ (lsmP I S tpv).Done () (s, k) y) (z2, w.2) := by
  have hSC' := hSC
  obtain ⟨c1, c2, c3, -, -, -, c7, -⟩ := hSC'
  refine PReachK.bind (Dom.sub_of_ranges (by decide)) (fun y hy => ?_)
    (hS () z2 w.2 ⟨by rw [c1]; rfl, c2, by simp only [Reg.sp, c3]; exact hsp⟩ hSpre)
  obtain ⟨-, hy⟩ := hy
  rcases hy with ⟨-, -, -, hp⟩ | ⟨hex, hon⟩
  · exact (hSp _ _ hp).elim
  · exact .done ⟨.inr hex, .inr ⟨hex, z, hIC, .inr ⟨w, z2, hxw, hpcw, hpw, hpost, hSC, hon⟩⟩⟩

/-- After `__init_libc` returned (0x115bc): the frame popped, the tail call of stage 2. -/
theorem lsm_tail (I : SpecP (Word × Word)) (S : SpecP Unit) (tpv : Word) (hS : VerifiedProcNR code stage2D libc_start_main_stage2_entry S)
    (hSp : ∀ x y, ¬ S.post () x y) (s : State) (k : Kern)
    (hsp : aligned (s.reg 2) 16) (z : State) (hIC : InitCall s z) (w : State × Kern) (hxw : w.1.exit = none)
    (hpcw : w.1.pc = 0x115bc#64) (hpw : Preserved (z.setReg 4 tpv) w.1)
    (hpost : I.post ((s.reg 11 <<< 3) + s.reg 12 + 8#64, read64 s.mem (s.reg 12)) (z.setReg 4 tpv, k) w)
    (hkp : w.2.perm = k.perm) (hle : (Perm.mk [⟨s.reg 12, 8⟩] [⟨s.reg 2 - 32#64, 32⟩]).le k.perm)
    (hs1 : read64 w.1.mem (s.reg 2 - 8#64) = s.reg 1)
    (hSpre : ∀ z2, Stage2Call s w.1 z2 → S.pre () z2 w.2) :
    PReachK code lsmD (fun y => Final lsmD y.1 ∧ (lsmP I S tpv).Done () (s, k) y) w := by
  obtain ⟨y, ky⟩ := w
  simp only at hxw hpcw hpw hpost hkp hSpre hs1 ⊢
  have h2 : y.reg 2 = s.reg 2 - 32#64 := by
    rw [hpw 2 (by decide), State.reg_setReg_other _ _ _ _ (by decide)]; exact hIC.2.2.2.1
  have rS : ∀ o, 8 ≤ o → o ≤ 32 → ky.perm.canRead (s.reg 2 - BitVec.ofNat 64 o) 8 := fun o h1 h3 =>
    hkp ▸ Perm.canRead_of_canWrite (hle.write _ _ (.inr ⟨⟨s.reg 2 - 32#64, 32⟩, by simp, by simp only [Region.covers]; bv_omega⟩))
  have hal : aligned (0x115e8#64 : Word) 4 := by decide
  nocompiler_run_n 11 [hxw, hpcw, h2, lsm_eS _ 24 (by omega), sw_alS hsp 8 rfl, lsm_eS _ 16 (by omega), sw_alS hsp 16 rfl, lsm_eS _ 8 (by omega), sw_alS hsp 24 rfl, lsm_e0, sw_alS hsp 32 rfl, lsm_eT, ret_mask hal] using [rS]
  have hSC : Stage2Call s y ((((((((((((((((((((y.setReg 6 71100#64).setPc 71104#64).setReg 6 71144#64).setPc 71108#64).setReg 10
      (y.reg 18)).setPc 71112#64).setReg 11 (y.reg 9)).setPc 71116#64).setReg 12 (y.reg 8)).setPc 71120#64).setReg 1
      (read64 y.mem (s.reg 2 - 8#64))).setPc 71124#64).setReg 8 (read64 y.mem (s.reg 2 - 16#64))).setPc 71128#64).setReg 9
      (read64 y.mem (s.reg 2 - 24#64))).setPc 71132#64).setReg 18 (read64 y.mem (s.reg 2 - 32#64))).setPc 71136#64).setReg 2
      (s.reg 2)).setPc 0x115e8#64) := by
    refine ⟨rfl, hxw, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq a2 a8 a9 a18 => ?_, rfl, rfl⟩
    all_goals (try simp (disch := nocompiler_decide_closed) only [nocompiler_state])
    have hne : q ≠ 1 ∧ q ≠ 6 ∧ q ≠ 10 ∧ q ≠ 11 ∧ q ≠ 12 := by revert hq; revert q; decide
    simp only [State.setPc_reg, State.reg_setReg_other _ _ _ _ hne.1, State.reg_setReg_other _ _ _ _ hne.2.1,
      State.reg_setReg_other _ _ _ _ hne.2.2.1, State.reg_setReg_other _ _ _ _ hne.2.2.2.1,
      State.reg_setReg_other _ _ _ _ hne.2.2.2.2, State.reg_setReg_other _ _ _ _ a2, State.reg_setReg_other _ _ _ _ a8,
      State.reg_setReg_other _ _ _ _ a9, State.reg_setReg_other _ _ _ _ a18]
  exact lsm_s2 I S tpv hS hSp s k hsp z hIC (y, ky) hxw hpcw hpw hpost hs1 _ hSC (hSpre _ hSC)

/-- `__init_libc(envp, argv[0])` from its call state `z`, then the rest. -/
theorem lsm_call (I : SpecP (Word × Word)) (S : SpecP Unit) (tpv : Word)
    (hI : VerifiedProcT code initLibcD __init_libc_entry I tpv)
    (hS : VerifiedProcNR code stage2D libc_start_main_stage2_entry S) (hSp : ∀ x y, ¬ S.post () x y) (s : State) (k : Kern)
    (hsp : aligned (s.reg 2) 16)
    (hle : (Perm.mk [⟨s.reg 12, 8⟩] [⟨s.reg 2 - 32#64, 32⟩]).le k.perm)
    (hIpre : ∀ z, InitCall s z → I.pre ((s.reg 11 <<< 3) + s.reg 12 + 8#64, read64 s.mem (s.reg 12)) z k)
    (hIpost : ∀ z w, InitCall s z → I.post ((s.reg 11 <<< 3) + s.reg 12 + 8#64, read64 s.mem (s.reg 12)) (z.setReg 4 tpv, k) w →
      w.2.perm = k.perm ∧ read64 w.1.mem (s.reg 2 - 8#64) = s.reg 1 ∧ read64 w.1.mem (s.reg 2 - 16#64) = s.reg 8 ∧
      read64 w.1.mem (s.reg 2 - 24#64) = s.reg 9 ∧ read64 w.1.mem (s.reg 2 - 32#64) = s.reg 18)
    (hSpre : ∀ z w z2, InitCall s z → I.post ((s.reg 11 <<< 3) + s.reg 12 + 8#64, read64 s.mem (s.reg 12)) (z.setReg 4 tpv, k) w →
      Preserved (z.setReg 4 tpv) w.1 → Stage2Call s w.1 z2 → S.pre () z2 w.2) (z : State) (hIC : InitCall s z) :
    PReachK code lsmD (fun y => Final lsmD y.1 ∧ (lsmP I S tpv).Done () (s, k) y) (z, k) := by
  have hIC' := hIC
  obtain ⟨c1, c2, c3, c4, -⟩ := hIC'
  refine PReachK.bind (Dom.sub_of_ranges (by decide)) (fun w hw => ?_)
    (hI _ z k ⟨by rw [c1]; rfl, c2, by simp only [Reg.ra, c3]; decide, by simp only [Reg.ra, c3]; decide,
      by simp only [Reg.sp, c4]; unfold aligned at *; bv_omega⟩ (hIpre z hIC))
  obtain ⟨-, hw⟩ := hw
  rcases hw with ⟨hxw, hpcw, hpw, hpost⟩ | ⟨hex, hon⟩
  · simp only [Reg.ra, State.reg_setReg_other _ _ _ _ (show (1 : Reg) ≠ 4 by decide), c3] at hpcw
    obtain ⟨hkp, hs1, -⟩ := hIpost z w hIC hpost
    exact lsm_tail I S tpv hS hSp s k hsp z hIC w hxw hpcw hpw hpost hkp hle hs1 (fun z2 h => hSpre z w z2 hIC hpost hpw h)
  · exact .done ⟨.inr hex, .inr ⟨hex, z, hIC, .inl hon⟩⟩

/-- `__libc_start_main` (0x11584) at the process level, given `__init_libc`'s and stage 2's specifications. -/
theorem lsm_verified (I : SpecP (Word × Word)) (S : SpecP Unit) (tpv : Word)
    (hI : VerifiedProcT code initLibcD __init_libc_entry I tpv)
    (hS : VerifiedProcNR code stage2D libc_start_main_stage2_entry S) (hSp : ∀ x y, ¬ S.post () x y) :
    VerifiedProcNR code lsmD __libc_start_main_entry (lsmP I S tpv) := by
  rintro ⟨⟩ s k he ⟨hle, hal, hdA, hIpre, hIpost, hSpre⟩
  have hpc := he.pc
  have hx := he.live
  have hsp := he.sp
  simp only [__libc_start_main_entry] at hpc
  simp only [Reg.sp] at hsp
  have wS : ∀ o, 8 ≤ o → o ≤ 32 → k.perm.canWrite (s.reg 2 - BitVec.ofNat 64 o) 8 := fun o h1 h3 =>
    hle.write _ _ (.inr ⟨⟨s.reg 2 - 32#64, 32⟩, by simp, by simp only [Region.covers]; bv_omega⟩)
  have rA : k.perm.canRead (s.reg 12) 8 := hle.read _ _ (.inr ⟨⟨s.reg 12, 8⟩, by simp, by simp [Region.covers]⟩)
  nocompiler_run_n 14 [hx, hpc, lsm_e32, lsm_eS _ 24 (by omega), sw_alS hsp 8 rfl, lsm_eS _ 16 (by omega), sw_alS hsp 16 rfl, lsm_eS _ 8 (by omega), sw_alS hsp 24 rfl, lsm_e0, sw_alS hsp 32 rfl, hal] using [wS, rA]
  have hcv : ∀ o, o = 8 ∨ o = 16 ∨ o = 24 ∨ o = 32 →
      (Region.mk (s.reg 2 - 32#64) 32).covers (s.reg 2 - BitVec.ofNat 64 o) 8 := by
    intro o ho; simp only [Region.covers]; rcases ho with rfl | rfl | rfl | rfl <;> bv_omega
  have hoff : ∀ p, ¬ (Region.mk (s.reg 2 - 32#64) 32).mem p → writeLE (writeLE (writeLE (writeLE s.mem (s.reg 2 - 8#64)
      (BitVec.toNat (s.reg 1)) 8) (s.reg 2 - 16#64) (BitVec.toNat (s.reg 8)) 8) (s.reg 2 - 24#64) (BitVec.toNat (s.reg 9)) 8)
      (s.reg 2 - 32#64) (BitVec.toNat (s.reg 18)) 8 p = s.mem p := by
    intro p hp
    rw [writeLE_of_not_mem (hcv 32 (by omega)) hp, writeLE_of_not_mem (hcv 24 (by omega)) hp,
      writeLE_of_not_mem (hcv 16 (by omega)) hp, writeLE_of_not_mem (hcv 8 (by omega)) hp]
  have hA : read64 (writeLE (writeLE (writeLE (writeLE s.mem (s.reg 2 - 8#64)
      (BitVec.toNat (s.reg 1)) 8) (s.reg 2 - 16#64) (BitVec.toNat (s.reg 8)) 8) (s.reg 2 - 24#64) (BitVec.toNat (s.reg 9)) 8)
      (s.reg 2 - 32#64) (BitVec.toNat (s.reg 18)) 8) (s.reg 12) = read64 s.mem (s.reg 12) := by
    apply read64_congr_on; intro j hj
    exact hoff _ (not_mem_of_mem_disj hdA.symm (by simp only [Region.mem]; bv_omega))
  refine lsm_call I S tpv hI hS hSp s k hsp hle hIpre hIpost hSpre _
    ⟨by simp only [nocompiler_state], by simp only [nocompiler_state]; exact hx, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, by simp only [nocompiler_state]⟩
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact hA
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · intro q hq a2 a8 a9 a18
    have hne : q ≠ 1 ∧ q ≠ 10 ∧ q ≠ 11 ∧ q ≠ 12 := by revert hq; revert q; decide
    simp only [State.setPc_reg, State.setMem_reg, State.reg_setReg_other _ _ _ _ hne.1, State.reg_setReg_other _ _ _ _ hne.2.1,
      State.reg_setReg_other _ _ _ _ hne.2.2.1, State.reg_setReg_other _ _ _ _ hne.2.2.2, State.reg_setReg_other _ _ _ _ a2,
      State.reg_setReg_other _ _ _ _ a8, State.reg_setReg_other _ _ _ _ a9, State.reg_setReg_other _ _ _ _ a18]
  · intro p hp; simp only [nocompiler_state]; exact hoff p hp
  · simp only [nocompiler_state]; simp (disch := nocompiler_decide_closed) only [slot_ne, fw_slot_same]
  · simp only [nocompiler_state]; simp (disch := nocompiler_decide_closed) only [slot_ne, fw_slot_same]
  · simp only [nocompiler_state]; simp (disch := nocompiler_decide_closed) only [slot_ne, fw_slot_same]
  · simp only [nocompiler_state]; simp (disch := nocompiler_decide_closed) only [slot_ne, fw_slot_same]

end Examples.Libc.Slen
