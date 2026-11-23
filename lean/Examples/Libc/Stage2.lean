import Examples.Libc.Main
import Examples.Libc.SlenProc
import Examples.Libc.InitFini
import NoCompiler.Linux.RunN
namespace Examples.Libc.Slen
open NoCompiler NoCompiler.Linux Examples.Libc.SlenImage

/-- An entry state of a function that does not return: as `Entry`, without the two facts about the return
    address (`_start` never sets ra, so the functions it reaches without a call see the launch's ra). -/
structure EntryNR (entry : Word) (s : State) : Prop where
  pc : s.pc = entry
  live : s.exit = none
  sp : aligned (s.reg Reg.sp) 16

/-- `VerifiedProc` from an `EntryNR` state: the same conclusion under fewer assumptions. -/
def VerifiedProcNR {α : Type} (c : Code) (D : Dom) (entry : Word) (sp : SpecP α) : Prop :=
  ∀ a s k, EntryNR entry s → sp.pre a s k → PReachK c D (fun y => Final D y.1 ∧ sp.Done a (s, k) y) (s, k)

/-- `libc_start_main_stage2` with `main` and what `main` reaches. -/
def stage2D : Dom := libc_start_main_stage2_dom ++ mainD

/-- `main`'s call from `libc_start_main_stage2` entered at `s` (0x11628, `jalr s2`): main(argc, argv, envp), the
    five saved registers in their slots, memory as at `s` outside the 80 bytes below sp. -/
def MainCall (s z : State) : Prop :=
  z.pc = 0x1121c#64 ∧ z.exit = none ∧ z.reg 1 = 0x1162c#64 ∧ z.reg 2 = s.reg 2 - 48#64 ∧
  z.reg 10 = s.reg 11 ∧ z.reg 11 = s.reg 12 ∧ z.reg 12 = (s.reg 11 <<< 3) + s.reg 12 + 8#64 ∧
  z.reg 8 = s.reg 12 ∧ z.reg 9 = s.reg 11 ∧ z.reg 18 = s.reg 10 ∧ z.reg 19 = (s.reg 11 <<< 3) + s.reg 12 + 8#64 ∧
  (∀ q ∈ preservedRegs, q ≠ 2 → q ≠ 8 → q ≠ 9 → q ≠ 18 → q ≠ 19 → z.reg q = s.reg q) ∧
  (∀ p, ¬ (Region.mk (s.reg 2 - 80#64) 80).mem p → z.mem p = s.mem p) ∧
  read64 z.mem (s.reg 2 - 8#64) = s.reg 1 ∧ read64 z.mem (s.reg 2 - 16#64) = s.reg 8 ∧
  read64 z.mem (s.reg 2 - 24#64) = s.reg 9 ∧ read64 z.mem (s.reg 2 - 32#64) = s.reg 18 ∧
  read64 z.mem (s.reg 2 - 40#64) = s.reg 19 ∧ z.trace = s.trace

/-- `libc_start_main_stage2(main, argc, argv)` (musl src/env/__libc_start_main.c) for slen's `main`, given main's
    specification `M` and exit's `E` (which does not return): `__libc_start_init()`, then `exit(main(argc, argv,
    envp))`. It does not return; it ends where `main` or `exit` end it. -/
def stage2P (M : SpecP Unit) (E : SpecP Word) : SpecP Unit where
  pre := fun _ s k => s.reg 10 = 0x1121c#64 ∧ (Perm.mk [] [⟨s.reg 2 - 80#64, 80⟩]).le k.perm ∧
    (∀ z, MainCall s z → M.pre () z k) ∧
    (∀ z w z3, MainCall s z → M.post () (z, k) w → Preserved z w.1 → callFrom w.1 z3 0x11aa4#64 0x11634#64 → E.pre (w.1.reg 10) z3 w.2)
  post := fun _ _ _ => False
  onExit := fun _ x y => ∃ z, MainCall x.1 z ∧ (M.onExit () (z, x.2) y ∨
    ∃ w z3, w.1.exit = none ∧ w.1.pc = 0x1162c#64 ∧ Preserved z w.1 ∧ M.post () (z, x.2) w ∧
      callFrom w.1 z3 0x11aa4#64 0x11634#64 ∧ E.onExit (w.1.reg 10) (z3, w.2) y)

theorem st2_e48 (sp : Word) : sp + 18446744073709551568#64 = sp - 48#64 := by bv_omega
theorem st2_eS (sp : Word) (o : Nat) (h : o ≤ 48) : sp - 48#64 + BitVec.ofNat 64 o = sp - BitVec.ofNat 64 (48 - o) := by
  bv_omega

/-- exit(main's result) (0x11aa4), from main's return `w`. -/
theorem st2_exit (M : SpecP Unit) (E : SpecP Word) (hE : VerifiedProc code exit_dom exit_entry E)
    (hEp : ∀ c x y, ¬ E.post c x y) (s : State) (k : Kern) (z : State) (hMC : MainCall s z) (w : State × Kern)
    (hxw : w.1.exit = none) (hpcw : w.1.pc = 0x1162c#64) (hpw : Preserved z w.1) (hpost : M.post () (z, k) w)
    (hEpre : E.pre (w.1.reg 10) z3 w.2) (hsp : aligned (s.reg 2) 16) (hcall : callFrom w.1 z3 0x11aa4#64 0x11634#64) :
    PReachK code stage2D (fun y => Final stage2D y.1 ∧ (stage2P M E).Done () (s, k) y) (z3, w.2) := by
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hcall
  have h2 : z3.reg 2 = s.reg 2 - 48#64 := by
    rw [c3 2 (by decide), hpw 2 (by decide)]; exact hMC.2.2.2.1
  refine VerifiedProc.call hE (w.1.reg 10) ⟨by rw [c1]; rfl, by rw [c6]; exact hxw, ?_, ?_, ?_⟩ hEpre
    (Dom.sub_of_ranges (by decide)) ?_
  · simp only [Reg.ra, c2]; decide
  · simp only [Reg.ra, c2]; decide
  · simp only [Reg.sp, h2]; unfold aligned at *; bv_omega
  rintro y (⟨-, -, -, hp⟩ | ⟨hex, hon⟩)
  · exact (hEp _ _ _ hp).elim
  · exact .done ⟨.inr hex, .inr ⟨hex, z, hMC, .inr ⟨w, z3, hxw, hpcw, hpw, hpost, ⟨c1, c2, c3, c4, c5, c6⟩, hon⟩⟩⟩

/-- main(argc, argv, envp) (0x1121c) from its call state `z`, then exit. -/
theorem st2_call (M : SpecP Unit) (E : SpecP Word) (hM : VerifiedProc code mainD main_entry M)
    (hE : VerifiedProc code exit_dom exit_entry E) (hEp : ∀ c x y, ¬ E.post c x y) (s : State) (k : Kern)
    (hMpre : ∀ z, MainCall s z → M.pre () z k)
    (hEpre : ∀ z w z3, MainCall s z → M.post () (z, k) w → Preserved z w.1 → callFrom w.1 z3 0x11aa4#64 0x11634#64 → E.pre (w.1.reg 10) z3 w.2)
    (hsp : aligned (s.reg 2) 16) (z : State) (hMC : MainCall s z) :
    PReachK code stage2D (fun y => Final stage2D y.1 ∧ (stage2P M E).Done () (s, k) y) (z, k) := by
  have hMC' := hMC
  obtain ⟨m1, m2, m3, m4, -⟩ := hMC'
  refine VerifiedProc.call hM () ⟨by rw [m1]; rfl, m2, ?_, ?_, ?_⟩ (hMpre z hMC) (Dom.sub_of_ranges (by decide)) ?_
  · simp only [Reg.ra, m3]; decide
  · simp only [Reg.ra, m3]; decide
  · simp only [Reg.sp, m4]; unfold aligned at *; bv_omega
  rintro ⟨y, ky⟩ (⟨hxy, hpcy, hpresy, hpost⟩ | ⟨hex, hon⟩)
  rotate_left
  · exact .done ⟨.inr hex, .inr ⟨hex, z, hMC, .inl hon⟩⟩
  simp only [Reg.ra, m3] at hxy hpcy hpresy hpost
  nocompiler_run_n 2 [hxy, hpcy] using []
  refine st2_exit M E hE hEp s k z hMC (y, ky) hxy hpcy hpresy hpost (hEpre z (y, ky) _ hMC hpost hpresy ?_) hsp ?_ <;>
  · refine ⟨by simp only [nocompiler_state], by simp (disch := nocompiler_decide_closed) only [nocompiler_state], fun r hr => ?_, by simp only [nocompiler_state],
      by simp only [nocompiler_state], by simp only [nocompiler_state]⟩
    have h1 : r ≠ 1 := fun h => hr (by rw [h]; decide)
    simp only [State.setPc_reg, State.reg_setReg_other _ _ _ _ h1]

/-- After `__libc_start_init` returned (0x1161c): main(argc, argv, envp) through s2, then exit(its result). -/
theorem st2_main (M : SpecP Unit) (E : SpecP Word) (hM : VerifiedProc code mainD main_entry M)
    (hE : VerifiedProc code exit_dom exit_entry E) (hEp : ∀ c x y, ¬ E.post c x y) (s : State) (k : Kern)
    (h10s : s.reg 10 = 0x1121c#64) (hMpre : ∀ z, MainCall s z → M.pre () z k)
    (hEpre : ∀ z w z3, MainCall s z → M.post () (z, k) w → Preserved z w.1 → callFrom w.1 z3 0x11aa4#64 0x11634#64 → E.pre (w.1.reg 10) z3 w.2)
    (hsp : aligned (s.reg 2) 16) (w : State) (hpc : w.pc = 0x1161c#64) (hx : w.exit = none)
    (h2 : w.reg 2 = s.reg 2 - 48#64) (h8 : w.reg 8 = s.reg 12) (h9 : w.reg 9 = s.reg 11) (h18 : w.reg 18 = s.reg 10)
    (h19 : w.reg 19 = (s.reg 11 <<< 3) + s.reg 12 + 8#64)
    (hpr : ∀ q ∈ preservedRegs, q ≠ 2 → q ≠ 8 → q ≠ 9 → q ≠ 18 → q ≠ 19 → w.reg q = s.reg q)
    (hm : ∀ p, ¬ (Region.mk (s.reg 2 - 80#64) 80).mem p → w.mem p = s.mem p)
    (s1 : read64 w.mem (s.reg 2 - 8#64) = s.reg 1) (s2 : read64 w.mem (s.reg 2 - 16#64) = s.reg 8)
    (s3 : read64 w.mem (s.reg 2 - 24#64) = s.reg 9) (s4 : read64 w.mem (s.reg 2 - 32#64) = s.reg 18)
    (s5 : read64 w.mem (s.reg 2 - 40#64) = s.reg 19) (htr : w.trace = s.trace) :
    PReachK code stage2D (fun y => Final stage2D y.1 ∧ (stage2P M E).Done () (s, k) y) (w, k) := by
  have hal : aligned (0x1121c#64 : Word) 4 := by decide
  nocompiler_run_n 4 [hx, hpc, h9, h8, h19, h18, h10s, ret_mask hal] using []
  refine st2_call M E hM hE hEp s k hMpre hEpre hsp _
    ⟨by simp only [nocompiler_state], by simp only [nocompiler_state]; exact hx, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, by simp only [nocompiler_state]; exact htr⟩
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h2
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h8
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h9
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h18
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h19
  · intro q hq a2 a8 a9 a18 a19
    have hne : q ≠ 1 ∧ q ≠ 10 ∧ q ≠ 11 ∧ q ≠ 12 := by revert hq; revert q; decide
    simp only [State.setPc_reg, State.reg_setReg_other _ _ _ _ hne.1, State.reg_setReg_other _ _ _ _ hne.2.1,
      State.reg_setReg_other _ _ _ _ hne.2.2.1, State.reg_setReg_other _ _ _ _ hne.2.2.2]
    exact hpr q hq a2 a8 a9 a18 a19
  · intro p hp; simp only [nocompiler_state]; exact hm p hp
  · simp only [nocompiler_state]; exact s1
  · simp only [nocompiler_state]; exact s2
  · simp only [nocompiler_state]; exact s3
  · simp only [nocompiler_state]; exact s4
  · simp only [nocompiler_state]; exact s5

theorem stage2_verified (M : SpecP Unit) (E : SpecP Word) (hM : VerifiedProc code mainD main_entry M)
    (hE : VerifiedProc code exit_dom exit_entry E) (hEp : ∀ c x y, ¬ E.post c x y) :
    VerifiedProcNR code stage2D libc_start_main_stage2_entry (stage2P M E) := by
  rintro ⟨⟩ s k he ⟨h10, hle, hMpre, hEpre⟩
  have hpc := he.pc
  have hx := he.live
  have hsp := he.sp
  simp only [libc_start_main_stage2_entry] at hpc
  simp only [Reg.sp] at hsp
  have wS : ∀ o, 8 ≤ o → o ≤ 80 → k.perm.canWrite (s.reg 2 - BitVec.ofNat 64 o) 8 := fun o h1 h3 =>
    hle.write _ _ (.inr ⟨⟨s.reg 2 - 80#64, 80⟩, by simp, by simp only [Region.covers]; bv_omega⟩)
  nocompiler_run_n 13 [hx, hpc, st2_e48, st2_eS _ 40 (by omega), sw_alS hsp 8 rfl, st2_eS _ 32 (by omega), sw_alS hsp 16 rfl, st2_eS _ 24 (by omega), sw_alS hsp 24 rfl, st2_eS _ 16 (by omega), sw_alS hsp 32 rfl, st2_eS _ 8 (by omega), sw_alS hsp 40 rfl] using [wS]
  refine VerifiedProc.call __libc_start_init_verified () ⟨by simp only [nocompiler_state]; rfl,
    by simp only [nocompiler_state]; exact hx, ?_, ?_, ?_⟩ ?_ (Dom.sub_of_ranges (by decide)) ?_
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.ra] <;> decide
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.ra] <;> decide
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.sp]; unfold aligned at *; bv_omega
  · simp (disch := nocompiler_decide_closed) only [retP32, nocompiler_state]
    refine Perm.le_trans (Perm.le_of (by simp) ?_) hle
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨s.reg 2 - 80#64, 80⟩, by simp, by simp only [Region.within]; bv_omega⟩
  rintro ⟨w, kw⟩ (⟨hxw, hpcw, hpresw, hkw, htrw, hmw⟩ | ⟨_, hex⟩)
  rotate_left
  · exact hex.elim
  simp only at hxw hpcw hpresw hkw htrw hmw
  simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.ra] at hpcw htrw hmw
  subst hkw
  have hin32 : ∀ p, ¬ (Region.mk (s.reg 2 - 80#64) 80).mem p → ¬ (Region.mk (s.reg 2 - 48#64 - 32#64) 32).mem p := by
    intro p hp h; exact hp (by simp only [Region.mem] at h ⊢; bv_omega)
  have hslw : ∀ o, o = 8 ∨ o = 16 ∨ o = 24 ∨ o = 32 ∨ o = 40 →
      read64 w.mem (s.reg 2 - BitVec.ofNat 64 o) = read64 (writeLE (writeLE (writeLE (writeLE (writeLE s.mem
        (s.reg 2 - 8#64) (BitVec.toNat (s.reg 1)) 8) (s.reg 2 - 16#64) (BitVec.toNat (s.reg 8)) 8)
        (s.reg 2 - 24#64) (BitVec.toNat (s.reg 9)) 8) (s.reg 2 - 32#64) (BitVec.toNat (s.reg 18)) 8)
        (s.reg 2 - 40#64) (BitVec.toNat (s.reg 19)) 8) (s.reg 2 - BitVec.ofNat 64 o) := by
    intro o ho; apply read64_congr_on; intro j hj
    exact hmw _ (by simp only [Region.mem]; rcases ho with rfl | rfl | rfl | rfl | rfl <;> bv_omega)
  have hcv : ∀ o, o = 8 ∨ o = 16 ∨ o = 24 ∨ o = 32 ∨ o = 40 →
      (Region.mk (s.reg 2 - 80#64) 80).covers (s.reg 2 - BitVec.ofNat 64 o) 8 := by
    intro o ho; simp only [Region.covers]; rcases ho with rfl | rfl | rfl | rfl | rfl <;> bv_omega
  refine st2_main M E hM hE hEp s kw h10 hMpre hEpre hsp w hpcw hxw ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hpresw 2 (by decide)]; simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · rw [hpresw 8 (by decide)]; simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · rw [hpresw 9 (by decide)]; simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · rw [hpresw 18 (by decide)]; simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · rw [hpresw 19 (by decide)]; simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · intro q hq a2 a8 a9 a18 a19
    rw [hpresw q hq]
    have hne : q ≠ 1 ∧ q ≠ 10 := by revert hq; revert q; decide
    simp only [State.setPc_reg, State.setMem_reg, State.reg_setReg_other _ _ _ _ hne.1, State.reg_setReg_other _ _ _ _ hne.2,
      State.reg_setReg_other _ _ _ _ a2, State.reg_setReg_other _ _ _ _ a8, State.reg_setReg_other _ _ _ _ a9,
      State.reg_setReg_other _ _ _ _ a18, State.reg_setReg_other _ _ _ _ a19]
  · intro p hp
    rw [hmw p (hin32 p hp), writeLE_of_not_mem (hcv 40 (by omega)) hp, writeLE_of_not_mem (hcv 32 (by omega)) hp,
      writeLE_of_not_mem (hcv 24 (by omega)) hp, writeLE_of_not_mem (hcv 16 (by omega)) hp,
      writeLE_of_not_mem (hcv 8 (by omega)) hp]
  · rw [hslw 8 (by omega)]; simp (disch := nocompiler_decide_closed) only [slot_ne, fw_slot_same]
  · rw [hslw 16 (by omega)]; simp (disch := nocompiler_decide_closed) only [slot_ne, fw_slot_same]
  · rw [hslw 24 (by omega)]; simp (disch := nocompiler_decide_closed) only [slot_ne, fw_slot_same]
  · rw [hslw 32 (by omega)]; simp (disch := nocompiler_decide_closed) only [slot_ne, fw_slot_same]
  · rw [hslw 40 (by omega)]; simp (disch := nocompiler_decide_closed) only [slot_ne, fw_slot_same]
  · rw [htrw]

end Examples.Libc.Slen
