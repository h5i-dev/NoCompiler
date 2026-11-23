import Examples.Libc.Fwritex

/-!
# `__libc_start_init` and `__libc_exit_fini` (musl src/env/__libc_start_main.c, src/exit/exit.c)

At the process level, by hand: `nocompiler_auto` leaves the reloaded return address on their return path
without the facts it needs (the explore path drops the final state's memory; STATUS-A, for C). In this image
both arrays are empty: `__init_array_start = __init_array_end = __fini_array_start = __fini_array_end =
0x10000` (llvm-nm), so the loops are not entered.
-/
set_option maxRecDepth 20000
namespace Examples.Libc.Slen
open NoCompiler NoCompiler.Linux Examples.Libc.SlenImage

/-- A function that only returns, at the process level: the kernel and the trace unchanged, memory outside its
    32-byte frame unchanged. -/
def retP32 : SpecP Unit where
  pre := fun _ s k => (Perm.mk [] [⟨s.reg 2 - 32#64, 32⟩]).le k.perm
  post := fun _ x y => y.2 = x.2 ∧ y.1.trace = x.1.trace ∧
    ∀ p, ¬ (Region.mk (x.1.reg 2 - 32#64) 32).mem p → y.1.mem p = x.1.mem p

theorem _init_proc : VerifiedProc code _init_dom _init_entry retSpec.toPns :=
  VerifiedImg.toProcNoSys _init_verified (noEcall_of (by decide +kernel))

/-- `__libc_start_init` after `_init` returned to 0x1154c: the init array is empty (its bounds are the same
    link-time constant 0x10000), so the loop is not entered; the epilogue. -/
theorem lsi_after (s : State) (k : Kern) (he : Entry __libc_start_init_dom __libc_start_init_entry s)
    (hle : (Perm.mk [] [⟨s.reg 2 - 32#64, 32⟩]).le k.perm)
    (w : State) (hpc : w.pc = 0x1154c#64) (hx : w.exit = none) (h2 : w.reg 2 = s.reg 2 - 32#64)
    (hpr : ∀ q ∈ preservedRegs, q ≠ 2 → q ≠ 8 → q ≠ 9 → w.reg q = s.reg q)
    (s1 : read64 w.mem (s.reg 2 - 8#64) = s.reg 1) (s2 : read64 w.mem (s.reg 2 - 16#64) = s.reg 8)
    (s3 : read64 w.mem (s.reg 2 - 24#64) = s.reg 9) (htr : w.trace = s.trace)
    (hfr : ∀ p, ¬ (Region.mk (s.reg 2 - 32#64) 32).mem p → w.mem p = s.mem p) :
    PReachK code __libc_start_init_dom (fun y => Final __libc_start_init_dom y.1 ∧ retP32.Done () (s, k) y) (w, k) := by
  have hsp := he.sp
  have hra4 := he.retAligned
  have hret := he.ret
  simp only [Reg.sp, Reg.ra] at hsp hra4 hret
  have rS : ∀ o, 8 ≤ o → o ≤ 32 → k.perm.canRead (s.reg 2 - BitVec.ofNat 64 o) 8 := fun o h1 h3 =>
    Perm.canRead_of_canWrite (hle.write _ _ (.inr ⟨⟨s.reg 2 - 32#64, 32⟩, by simp, by simp only [Region.covers]; bv_omega⟩))
  have eS : ∀ o, o ≤ 32 → s.reg 2 - 32#64 + BitVec.ofNat 64 o = s.reg 2 - BitVec.ofNat 64 (32 - o) := by
    intro o ho; bv_omega
  have e32 : s.reg 2 - 32#64 + 32#64 = s.reg 2 := by bv_omega
  nocompiler_wstep [hx, hpc]
  nocompiler_wstep [hx]
  nocompiler_wstep [hx]
  nocompiler_wstep [hx]
  nocompiler_wstep [hx]
  nocompiler_wstep [hx, h2, eS 24 (by omega), sw_alS hsp 8 rfl, s1]
  refine ⟨rS 8 (by omega) (by omega), ?_⟩
  nocompiler_wstep [hx, h2, eS 16 (by omega), sw_alS hsp 16 rfl, s2]
  refine ⟨rS 16 (by omega) (by omega), ?_⟩
  nocompiler_wstep [hx, h2, eS 8 (by omega), sw_alS hsp 24 rfl, s3]
  refine ⟨rS 24 (by omega) (by omega), ?_⟩
  nocompiler_wstep [hx, h2, e32]
  nocompiler_wstep [hx, ret_mask hra4, hra4]
  refine .done ⟨.inl ?_, .inl ⟨?_, ?_, ?_, rfl, ?_, ?_⟩⟩
  · simp only [nocompiler_state]; exact hret
  · simp only [nocompiler_state]; exact hx
  · simp only [nocompiler_state, Reg.ra]
  · intro q hq
    have hq' := hq
    simp only [preservedRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals (simp (disch := nocompiler_decide_closed) only [nocompiler_state])
    all_goals (exact hpr _ hq' (by decide) (by decide) (by decide))
  · simp only [nocompiler_state]; exact htr
  · intro p hp; simp only [nocompiler_state]; exact hfr p hp


/-- The call of `_init` from 0x11548 (state `z`), then lsi_after. -/
theorem lsi_call (s : State) (k : Kern) (he : Entry __libc_start_init_dom __libc_start_init_entry s)
    (hle : (Perm.mk [] [⟨s.reg 2 - 32#64, 32⟩]).le k.perm)
    (z : State) (hpc : z.pc = 0x112e8#64) (hx : z.exit = none) (hra : z.reg 1 = 0x1154c#64)
    (h2 : z.reg 2 = s.reg 2 - 32#64) (hpr : ∀ q ∈ preservedRegs, q ≠ 2 → q ≠ 8 → q ≠ 9 → z.reg q = s.reg q)
    (s1 : read64 z.mem (s.reg 2 - 8#64) = s.reg 1) (s2 : read64 z.mem (s.reg 2 - 16#64) = s.reg 8)
    (s3 : read64 z.mem (s.reg 2 - 24#64) = s.reg 9) (htr : z.trace = s.trace)
    (hfr : ∀ p, ¬ (Region.mk (s.reg 2 - 32#64) 32).mem p → z.mem p = s.mem p) :
    PReachK code __libc_start_init_dom (fun y => Final __libc_start_init_dom y.1 ∧ retP32.Done () (s, k) y) (z, k) := by
  have hsp := he.sp
  simp only [Reg.sp] at hsp
  refine VerifiedProc.call _init_proc () ⟨hpc, hx, by rw [Reg.ra, hra]; decide, by rw [Reg.ra, hra]; decide,
    by rw [Reg.sp, h2]; unfold aligned at *; bv_omega⟩ ⟨trivial, retSpec_le _ _⟩ (Dom.sub_of_ranges (by decide)) ?_
  rintro ⟨w, kw⟩ (⟨hxw, hpcw, hpresw, -, hk, htrw, hfrw⟩ | ⟨_, hex, _⟩)
  rotate_left
  · exact hex.elim
  simp only at hxw hpcw hpresw hk htrw hfrw
  rw [hk]
  have hwm : w.mem = z.mem := funext fun x => hfrw x (retSpec_nowrite _ x)
  refine lsi_after s k he hle w (by rw [hpcw, Reg.ra, hra]) hxw (by rw [hpresw 2 (by decide), h2])
    (fun q hq h2' h8 h9 => by rw [hpresw q hq, hpr q hq h2' h8 h9]) (by rw [hwm]; exact s1) (by rw [hwm]; exact s2)
    (by rw [hwm]; exact s3) (by rw [htrw, htr]) (fun p hp => by rw [hwm]; exact hfr p hp)

/-- `__libc_start_init` as compiled (`_init`, then the empty init array), at the process level. -/
theorem __libc_start_init_verified : VerifiedProc code __libc_start_init_dom __libc_start_init_entry retP32 := by
  intro _ s k he hle
  have hpc := he.pc
  have hx := he.live
  have hsp := he.sp
  simp only [__libc_start_init_entry] at hpc
  simp only [Reg.sp] at hsp
  have wS : ∀ o, 8 ≤ o → o ≤ 32 → k.perm.canWrite (s.reg 2 - BitVec.ofNat 64 o) 8 := fun o h1 h3 =>
    hle.write _ _ (.inr ⟨⟨s.reg 2 - 32#64, 32⟩, by simp, by simp only [Region.covers]; bv_omega⟩)
  have e32 : s.reg 2 + 18446744073709551584#64 = s.reg 2 - 32#64 := by bv_omega
  have eS : ∀ o, o ≤ 32 → s.reg 2 - 32#64 + BitVec.ofNat 64 o = s.reg 2 - BitVec.ofNat 64 (32 - o) := by
    intro o ho; bv_omega
  nocompiler_wstep [hx, hpc, e32]
  nocompiler_wstep [hx, eS 24 (by omega), sw_alS hsp 8 rfl]
  refine ⟨wS 8 (by omega) (by omega), ?_⟩
  nocompiler_wstep [hx, eS 16 (by omega), sw_alS hsp 16 rfl]
  refine ⟨wS 16 (by omega) (by omega), ?_⟩
  nocompiler_wstep [hx, eS 8 (by omega), sw_alS hsp 24 rfl]
  refine ⟨wS 24 (by omega) (by omega), ?_⟩
  nocompiler_wstep [hx]
  nocompiler_wstep [hx]
  refine lsi_call s k he hle _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [nocompiler_state]
  · simp only [nocompiler_state]; exact hx
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · intro q hq h2 h8 h9
    have h1 : q ≠ 1 := not_one_of_preserved q hq
    repeat (first | rw [State.setPc_reg] | rw [State.setMem_reg] | rw [State.reg_setReg_other _ _ _ _ h1] | rw [State.reg_setReg_other _ _ _ _ h2])
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state, slot_ne, fw_slot_same]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state, slot_ne, fw_slot_same]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state, slot_ne, fw_slot_same]
  · simp only [nocompiler_state]
  · intro p hp
    simp (disch := nocompiler_decide_closed) only [nocompiler_state]
    rw [writeLE_of_not_mem (r := ⟨s.reg 2 - 32#64, 32⟩) (by simp only [Region.covers]; bv_omega) hp,
      writeLE_of_not_mem (r := ⟨s.reg 2 - 32#64, 32⟩) (by simp only [Region.covers]; bv_omega) hp,
      writeLE_of_not_mem (r := ⟨s.reg 2 - 32#64, 32⟩) (by simp only [Region.covers]; bv_omega) hp]

theorem __funcs_on_exit_proc : VerifiedProc code __funcs_on_exit_dom __funcs_on_exit_entry retSpec.toPns :=
  VerifiedImg.toProcNoSys __funcs_on_exit_verified (noEcall_of (by decide +kernel))

/-- `__libc_exit_fini`'s tail call of `_fini` (0x11a50, the empty function `__funcs_on_exit` shares) from a state
    `z` with the caller's ra and sp and every saved register back. -/
theorem lef_tail (s : State) (k : Kern) (he : Entry __libc_exit_fini_dom __libc_exit_fini_entry s)
    (z : State) (hpc : z.pc = 0x11a50#64) (hx : z.exit = none) (hra : z.reg 1 = s.reg 1)
    (hpr : ∀ q ∈ preservedRegs, z.reg q = s.reg q) (htr : z.trace = s.trace)
    (hfr : ∀ p, ¬ (Region.mk (s.reg 2 - 32#64) 32).mem p → z.mem p = s.mem p) :
    PReachK code __libc_exit_fini_dom (fun y => Final __libc_exit_fini_dom y.1 ∧ retP32.Done () (s, k) y) (z, k) := by
  have hra4 := he.retAligned
  have hret := he.ret
  have hsp := he.sp
  simp only [Reg.ra, Reg.sp] at hra4 hret hsp
  refine VerifiedProc.call __funcs_on_exit_proc () ⟨hpc, hx, ?_, by rw [Reg.ra, hra]; exact hra4,
    by rw [Reg.sp, hpr 2 (by decide)]; exact hsp⟩ ⟨trivial, retSpec_le _ _⟩ (Dom.sub_of_ranges (by decide)) ?_
  · rw [Reg.ra, hra]; intro hm; exact hret (Dom.sub_of_ranges (by decide) _ hm)
  rintro ⟨w, kw⟩ (⟨hxw, hpcw, hpresw, -, hk, htrw, hfrw⟩ | ⟨_, hex, _⟩)
  rotate_left
  · exact hex.elim
  simp only at hxw hpcw hpresw hk htrw hfrw
  have hwm : w.mem = z.mem := funext fun x => hfrw x (retSpec_nowrite _ x)
  have hpc' : w.pc = s.reg 1 := by rw [hpcw, Reg.ra, hra]
  refine .done ⟨.inl (by rw [hpc']; exact hret), .inl ⟨hxw, by rw [hpc'], fun q hq => by rw [hpresw q hq, hpr q hq], hk, by rw [htrw, htr],
    fun p hp => by rw [hwm]; exact hfr p hp⟩⟩


/-- `__libc_exit_fini` as compiled (the empty fini array, then `_fini`), at the process level. -/
theorem __libc_exit_fini_verified : VerifiedProc code __libc_exit_fini_dom __libc_exit_fini_entry retP32 := by
  intro _ s k he hle
  have hpc := he.pc
  have hx := he.live
  have hsp := he.sp
  simp only [__libc_exit_fini_entry] at hpc
  simp only [Reg.sp] at hsp
  have wS : ∀ o, 8 ≤ o → o ≤ 32 → k.perm.canWrite (s.reg 2 - BitVec.ofNat 64 o) 8 := fun o h1 h3 =>
    hle.write _ _ (.inr ⟨⟨s.reg 2 - 32#64, 32⟩, by simp, by simp only [Region.covers]; bv_omega⟩)
  have rS : ∀ o, 8 ≤ o → o ≤ 32 → k.perm.canRead (s.reg 2 - BitVec.ofNat 64 o) 8 := fun o h1 h3 =>
    Perm.canRead_of_canWrite (wS o h1 h3)
  have e32 : s.reg 2 + 18446744073709551584#64 = s.reg 2 - 32#64 := by bv_omega
  have eS : ∀ o, o ≤ 32 → s.reg 2 - 32#64 + BitVec.ofNat 64 o = s.reg 2 - BitVec.ofNat 64 (32 - o) := by
    intro o ho; bv_omega
  have e32' : s.reg 2 - 32#64 + 32#64 = s.reg 2 := by bv_omega
  nocompiler_wstep [hx, hpc, e32]
  nocompiler_wstep [hx, eS 24 (by omega), sw_alS hsp 8 rfl]
  refine ⟨wS 8 (by omega) (by omega), ?_⟩
  nocompiler_wstep [hx, eS 16 (by omega), sw_alS hsp 16 rfl]
  refine ⟨wS 16 (by omega) (by omega), ?_⟩
  nocompiler_wstep [hx, eS 8 (by omega), sw_alS hsp 24 rfl]
  refine ⟨wS 24 (by omega) (by omega), ?_⟩
  nocompiler_wstep [hx]
  nocompiler_wstep [hx]
  nocompiler_wstep [hx]
  nocompiler_wstep [hx]
  nocompiler_wstep [hx]
  nocompiler_wstep [hx, eS 24 (by omega), sw_alS hsp 8 rfl, slot_ne, fw_slot_same]
  refine ⟨rS 8 (by omega) (by omega), ?_⟩
  nocompiler_wstep [hx, eS 16 (by omega), sw_alS hsp 16 rfl, slot_ne, fw_slot_same]
  refine ⟨rS 16 (by omega) (by omega), ?_⟩
  nocompiler_wstep [hx, eS 8 (by omega), sw_alS hsp 24 rfl, slot_ne, fw_slot_same]
  refine ⟨rS 24 (by omega) (by omega), ?_⟩
  nocompiler_wstep [hx, e32']
  nocompiler_wstep [hx]
  nocompiler_wstep [hx]
  refine lef_tail s k he _ ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [nocompiler_state]
  · simp only [nocompiler_state]; exact hx
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · intro q hq
    have hq' := hq
    simp only [preservedRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals (simp (disch := nocompiler_decide_closed) only [nocompiler_state])
  · simp only [nocompiler_state]
  · intro p hp
    simp (disch := nocompiler_decide_closed) only [nocompiler_state]
    rw [writeLE_of_not_mem (r := ⟨s.reg 2 - 32#64, 32⟩) (by simp only [Region.covers]; bv_omega) hp,
      writeLE_of_not_mem (r := ⟨s.reg 2 - 32#64, 32⟩) (by simp only [Region.covers]; bv_omega) hp,
      writeLE_of_not_mem (r := ⟨s.reg 2 - 32#64, 32⟩) (by simp only [Region.covers]; bv_omega) hp]

/-- `__set_thread_area` (src/thread/riscv64/__set_thread_area.s, 0x12dc4, 3 instructions; assembly, so not one of
    the image's functions): its words. -/
def __set_thread_area_dom : Dom := [(0x12dc4#64, 12)]

/-- `__set_thread_area(p)` as compiled: `mv tp, a0; li a0, 0; ret`. A run rule, not a `VerifiedProc`: it changes
    tp, a register `Spec.Done`/`SpecP.Done` require to be preserved. From its entry inside a region `D`, the run
    goes on at the return address with tp = p, a0 = 0, everything else as it was. -/
theorem __set_thread_area_verified (D : Dom) (hD : __set_thread_area_dom.sub D) (R : State × Kern → Prop)
    (s : State) (k : Kern) (hpc : s.pc = 0x12dc4#64) (hx : s.exit = none) (hra4 : aligned (s.reg 1) 4)
    (K : ∀ y : State, y.pc = s.reg 1 → y.exit = none → y.reg 4 = s.reg 10 → y.reg 10 = 0 →
      Same s y [4, 10] → y.mem = s.mem → y.trace = s.trace → PReachK code D R (y, k)) :
    PReachK code D R (s, k) := by
  nocompiler_wstepD hD [hx, hpc]
  nocompiler_wstepD hD [hx]
  nocompiler_wstepD hD [hx, ret_mask hra4, hra4]
  refine K _ (by simp (disch := nocompiler_decide_closed) only [nocompiler_state])
    (by simp only [nocompiler_state]; exact hx) (by simp (disch := nocompiler_decide_closed) only [nocompiler_state])
    (by simp (disch := nocompiler_decide_closed) only [nocompiler_state]) ?_ (by simp only [nocompiler_state])
    (by simp only [nocompiler_state])
  nocompiler_same

end Examples.Libc.Slen
