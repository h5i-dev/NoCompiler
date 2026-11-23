import Examples.Libc.Musl.StdioWrite3

set_option maxRecDepth 20000
namespace NoCompiler.Libc.Musl.StdioWrite
open NoCompiler NoCompiler.Linux NoCompiler.Libc NoCompiler.Libc.Musl.StdioWriteImg NoCompiler.Libc.Musl.SyscallRet

/-- A stack slot read after a store to another 8-byte slot below sp (offsets as decidable side conditions). -/
theorem slot_ne (sp : Word) (a b : Nat)
    (h : (decide (8 ≤ a) && decide (a ≤ 112) && decide (8 ≤ b) && decide (b ≤ 112) &&
      (decide (a + 8 ≤ b) || decide (b + 8 ≤ a))) = true) (m : Word → Byte) (v : Nat) :
    read64 (writeLE m (sp - BitVec.ofNat 64 a) v 8) (sp - BitVec.ofNat 64 b) = read64 m (sp - BitVec.ofNat 64 b) := by
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  exact Auto.read64_writeLE_of_disjoint (R := ⟨sp - BitVec.ofNat 64 a, 8⟩) (by simp only [Region.Disjoint]; bv_omega) _ _ _ _
    (by simp [Region.covers])

theorem file_after_slot {f sp : Word} (dFS : (Region.mk f 128).Disjoint ⟨sp - 112#64, 112⟩) (a o : Nat)
    (h : (decide (8 ≤ a) && decide (a ≤ 112) && decide (o + 8 ≤ 128)) = true) (m : Word → Byte) (v : Nat) :
    read64 (writeLE m (sp - BitVec.ofNat 64 a) v 8) (f + BitVec.ofNat 64 o) = read64 m (f + BitVec.ofNat 64 o) := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact Auto.read64_writeLE_of_disjoint (R := ⟨sp - BitVec.ofNat 64 a, 8⟩)
    (sw_dFS dFS o 8 a (by omega) (by omega) (by omega) (by omega)).symm _ _ _ _ (by simp [Region.covers])

theorem file4_after_slot {f sp : Word} (dFS : (Region.mk f 128).Disjoint ⟨sp - 112#64, 112⟩) (a o : Nat)
    (h : (decide (8 ≤ a) && decide (a ≤ 112) && decide (o + 4 ≤ 128)) = true) (m : Word → Byte) (v : Nat) :
    readLE (writeLE m (sp - BitVec.ofNat 64 a) v 8) (f + BitVec.ofNat 64 o) 4 = readLE m (f + BitVec.ofNat 64 o) 4 := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact readLE_writeLE_disj (R := ⟨sp - BitVec.ofNat 64 a, 8⟩)
    (sw_dFS dFS o 4 a (by omega) (by omega) (by omega) (by omega)).symm _ _ _ _ (by simp [Region.covers])

theorem writeLE_slot_out {sp p : Word} (hp : ¬ (Region.mk (sp - 112#64) 112).mem p) (a : Nat)
    (h : (decide (8 ≤ a) && decide (a ≤ 112)) = true) (m : Word → Byte) (v : Nat) :
    writeLE m (sp - BitVec.ofNat 64 a) v 8 p = m p := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact writeLE_of_not_mem (r := ⟨sp - 112#64, 112⟩) (sw_cS _ a 8 (by omega) (by omega)) hp

theorem sw_e96' (sp : Word) : sp + 18446744073709551520#64 = sp - 96#64 := by bv_omega

/-- `__stdio_write` as compiled, at the process level (stdioWriteSpec). -/
theorem __stdio_write_verified : VerifiedProc img dom __stdio_write_entry stdioWriteSpec := by
  rintro ⟨f, buf, len⟩ s k he hpre
  have hpre' := hpre
  obtain ⟨ha0, ha1, ha2, hal, hale, hle, dFS, dES, dEF, dP1, dB1, dP2, dB2, hB, -⟩ := hpre'
  have hpc := he.pc
  have hx := he.live
  have hsp := he.sp
  simp only [__stdio_write_entry] at hpc
  simp only [Reg.sp] at hsp
  have hW := fun {a n} h => sw_canWrite (a := a) (n := n) hle h
  have rF : ∀ o, o + 8 ≤ 128 → k.perm.canRead (f + BitVec.ofNat 64 o) 8 := fun o ho =>
    Perm.canRead_of_canWrite (hW (.inl (sw_cF f o 8 ho)))
  have wS : ∀ o, 8 ≤ o → o ≤ 112 → k.perm.canWrite (s.reg 2 - BitVec.ofNat 64 o) 8 := fun o h1 h2 =>
    hW (.inr (.inl (sw_cS _ o 8 h1 h2)))
  have r120 : k.perm.canRead (f + 120#64) 4 := Perm.canRead_of_canWrite (hW (.inl (sw_cF f 120 4 (by omega))))
  have al120 : aligned (f + 120#64) 4 := by have := sw_alF hal 120 rfl; unfold aligned at *; omega
  have fs := file_after_slot dFS
  have fs4 := file4_after_slot dFS
  nocompiler_run_n 24 [hx, hpc, sw_e96', sw_eS (s.reg 2) 88 (by omega), sw_alS hsp 8 rfl, sw_eS (s.reg 2) 80 (by omega), sw_alS hsp 16 rfl, sw_eS (s.reg 2) 72 (by omega), sw_alS hsp 24 rfl, sw_eS (s.reg 2) 64 (by omega), sw_alS hsp 32 rfl, sw_eS (s.reg 2) 56 (by omega), sw_alS hsp 40 rfl, sw_eS (s.reg 2) 48 (by omega), sw_alS hsp 48 rfl, sw_eS (s.reg 2) 40 (by omega), sw_alS hsp 56 rfl, ha0, sw_alF hal 56 rfl, fs, sw_eS (s.reg 2) 8 (by omega), sw_alS hsp 88 rfl, sw_alF hal 40 rfl, ha2, sw_eS (s.reg 2) 16 (by omega), sw_alS hsp 80 rfl, ha1, sw_eS (s.reg 2) 24 (by omega), sw_alS hsp 72 rfl, sw_eS (s.reg 2) 32 (by omega), sw_alS hsp 64 rfl, al120, fs4] using [wS, rF, r120]
  have hBl := stdioBytes_length s.mem f buf len
  have hpB : (BitVec.ofNat 64 (stdioPend s.mem f) : Word) = read64 s.mem (f + 40#64) - read64 s.mem (f + 56#64) := by
    simp only [stdioPend, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine sw_ecall f buf len s k he hpre _ 0x124dc#64 (.inl rfl) _ ?_ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_
    (s.reg 2 - 88#64) 2#64 ?_ ?_ 0 ?_ ?_ ?_
  · simp only [nocompiler_state]
  · simp only [nocompiler_state]; exact hx
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  all_goals (try simp (disch := nocompiler_decide_closed) only [nocompiler_state, slot_ne, Auto.read64_writeLE_same',
    BitVec.ofNat_toNat, BitVec.setWidth_eq])
  · intro p hp1 hp2
    simp (disch := nocompiler_decide_closed) only [nocompiler_state, writeLE_slot_out hp1]
  · refine .inl ⟨Nat.zero_le _, rfl, rfl, ?_, ?_, ?_, ?_⟩
    all_goals (simp (disch := nocompiler_decide_closed) only [nocompiler_state, slot_ne, Auto.read64_writeLE_same',
      BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_zero, Nat.sub_zero, hpB])
  · intro w hpcw hcw hsw hiw hres
    have hw20 := hsw 20 (by simp)
    have hw21 := hsw 21 (by simp)
    have hw18 := hsw 18 (by simp)
    simp (disch := nocompiler_decide_closed) only [nocompiler_state] at hw20 hw21 hw18
    refine sw_first f buf len s k he hpre w (by rw [hpcw]; rfl) hcw ?_ (by rw [hw21, hw18]; exact hiw) ?_
    · rw [hw20, hBl, BitVec.ofNat_add, hpB]
      simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rcases hres with ⟨r, hr1, hr2, hr3, hr4, hr5⟩ | ⟨h1, h2⟩
      · refine .inl ⟨r, by simpa using hr1, fun h => hr2 (by simpa using h), hr4, ?_⟩
        rw [hr5]; simp only [nocompiler_state, List.drop_zero]; rfl
      · exact .inr ⟨h1, by rw [h2]⟩
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hfd⟩ := hpre
    unfold fdOf at hfd; omega

/-- `stdioWriteSpec` for a caller that keeps its own frame above the stack pointer: FILE's fields and errno
    outside the 16 bytes above sp (precondition), and those 16 bytes unchanged (postcondition). -/
def stdioWriteSpecF : SpecP (Word × Word × Word) where
  pre := fun a s k => stdioWriteSpec.pre a s k ∧ (Region.mk a.1 128).Disjoint ⟨s.reg 2, 16⟩ ∧
    (Region.mk (s.reg 4 + 18446744073709551452#64) 4).Disjoint ⟨s.reg 2, 16⟩
  post := fun a x y => stdioWriteSpec.post a x y ∧
    ∀ p, (Region.mk (x.1.reg 2) 16).mem p → y.1.mem p = x.1.mem p

theorem not_mem_sub128 {f p : Word} (o n : Nat) (h : o + n ≤ 128) (hp : ¬ (Region.mk f 128).mem p) :
    ¬ (Region.mk (f + BitVec.ofNat 64 o) n).mem p := by
  intro hm; apply hp; simp only [Region.mem] at *; bv_omega

theorem above_not_stack {sp p : Word} (hp : (Region.mk sp 16).mem p) : ¬ (Region.mk (sp - 112#64) 112).mem p := by
  simp only [Region.mem] at *; bv_omega

theorem __stdio_write_verifiedF : VerifiedProc img dom __stdio_write_entry stdioWriteSpecF := by
  refine VerifiedProc.consequence __stdio_write_verified (fun a s k h => h.1) ?_
  rintro ⟨f, buf, len⟩ s k y ⟨hp, dF, dE⟩ (⟨h1, h2, h3, hpost⟩ | ⟨h1, h2⟩)
  · refine .inl ⟨h1, h2, h3, hpost, ?_⟩
    intro p hp16
    obtain ⟨-, evs, -, hfr, -⟩ := hpost
    have hF := not_mem_of_disj_mem dF hp16
    exact hfr p (above_not_stack hp16) (not_mem_of_disj_mem dE hp16)
      (by have := not_mem_sub128 (f := f) 0 4 (by omega) hF; simpa using this)
      (not_mem_sub128 32 16 (by omega) hF) (not_mem_sub128 56 8 (by omega) hF)
  · exact .inr ⟨h1, h2⟩


theorem stdioWriteF_frame : StdioWriteFrame stdioWriteSpecF := by
  rintro ⟨f, buf, len⟩ z w ⟨⟨hk, -⟩, hfr⟩
  exact ⟨fun p hp => hfr p (by simpa [Reg.sp] using hp), by rw [hk]⟩

end NoCompiler.Libc.Musl.StdioWrite
