import Examples.Libc.InitFini
import Examples.Libc.Musl.Fread3

/-!
# The input side: `__toread` (musl src/stdio/__toread.c), at the process level, by hand

`nocompiler_auto` loses `s0 = f` at the join after `__toread`'s first branch (the explore-path gap, STATUS-A).
`__toread` calls `f->write(f, 0, 0)` only when bytes are buffered for writing; the specification asks for none
(wpos = wbase), which holds for slen's stdin.
-/
set_option maxRecDepth 20000
namespace Examples.Libc.Slen
open NoCompiler NoCompiler.Linux Examples.Libc.SlenImage

/-- An 8-byte FILE field read after a store to another (offsets as decidable side conditions). -/
theorem field_after_field (f : Word) (a n b : Nat)
    (h : (decide (a + n ≤ b) || decide (b + 8 ≤ a)) && decide (b + 8 ≤ 144) && decide (a + n ≤ 144) && decide (0 < n) = true)
    (m : Word → Byte) (v : Nat) :
    read64 (writeLE m (f + BitVec.ofNat 64 a) v n) (f + BitVec.ofNat 64 b) = read64 m (f + BitVec.ofNat 64 b) := by
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  exact Auto.read64_writeLE_of_disjoint (R := ⟨f + BitVec.ofNat 64 a, n⟩) (by simp only [Region.Disjoint]; bv_omega)
    _ _ _ _ (by simp [Region.covers])

/-- A 4-byte FILE field (as readLE) after a store to another. -/
theorem field4_after_field (f : Word) (a n b : Nat)
    (h : (decide (a + n ≤ b) || decide (b + 4 ≤ a)) && decide (b + 4 ≤ 144) && decide (a + n ≤ 144) && decide (0 < n) = true)
    (m : Word → Byte) (v : Nat) :
    readLE (writeLE m (f + BitVec.ofNat 64 a) v n) (f + BitVec.ofNat 64 b) 4 = readLE m (f + BitVec.ofNat 64 b) 4 := by
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  exact readLE_writeLE_disj (R := ⟨f + BitVec.ofNat 64 a, n⟩) (by simp only [Region.Disjoint]; bv_omega)
    _ _ _ _ (by simp [Region.covers])

/-- A FILE field after a store to a stack slot, and a stack slot after a store to a FILE field. -/
theorem field_after_slot16 {f sp : Word} (hFS : (Region.mk f 144).Disjoint ⟨sp - 16#64, 16⟩) (a b n : Nat)
    (h : decide (8 ≤ a) && decide (a ≤ 16) && decide (b + n ≤ 144) && decide (0 < n) && decide (n ≤ 8) = true)
    (m : Word → Byte) (v : Nat) :
    readLE (writeLE m (sp - BitVec.ofNat 64 a) v 8) (f + BitVec.ofNat 64 b) n = readLE m (f + BitVec.ofNat 64 b) n := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact readLE_writeLE_disj (R := ⟨sp - BitVec.ofNat 64 a, 8⟩) (by simp only [Region.Disjoint] at *; bv_omega)
    _ _ _ _ (by simp [Region.covers])

theorem slot16_after_field {f sp : Word} (hFS : (Region.mk f 144).Disjoint ⟨sp - 16#64, 16⟩) (a b n : Nat)
    (h : decide (8 ≤ b) && decide (b ≤ 16) && decide (a + n ≤ 144) && decide (0 < n) = true)
    (m : Word → Byte) (v : Nat) :
    read64 (writeLE m (f + BitVec.ofNat 64 a) v n) (sp - BitVec.ofNat 64 b) = read64 m (sp - BitVec.ofNat 64 b) := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact Auto.read64_writeLE_of_disjoint (R := ⟨f + BitVec.ofNat 64 a, n⟩) (by simp only [Region.Disjoint] at *; bv_omega)
    _ _ _ _ (by simp [Region.covers])

/-- A FILE field after a store at the FILE's base (flags), and the flags after a store to another field. -/
theorem field_after_base (f : Word) (n b : Nat)
    (h : decide (n ≤ b) && decide (b + 8 ≤ 144) && decide (0 < n) = true) (m : Word → Byte) (v : Nat) :
    read64 (writeLE m f v n) (f + BitVec.ofNat 64 b) = read64 m (f + BitVec.ofNat 64 b) := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact Auto.read64_writeLE_of_disjoint (R := ⟨f, n⟩) (by simp only [Region.Disjoint]; bv_omega) _ _ _ _ (by simp [Region.covers])

theorem base_after_field (f : Word) (a n : Nat)
    (h : decide (4 ≤ a) && decide (a + n ≤ 144) && decide (0 < n) = true) (m : Word → Byte) (v : Nat) :
    read32 (writeLE m (f + BitVec.ofNat 64 a) v n) f = read32 m f := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  unfold read32
  rw [readLE_writeLE_disj (R := ⟨f + BitVec.ofNat 64 a, n⟩) (by simp only [Region.Disjoint]; bv_omega) _ _ _ _
    (by simp [Region.covers])]

theorem base_after_slot16 {f sp : Word} (hFS : (Region.mk f 144).Disjoint ⟨sp - 16#64, 16⟩) (a : Nat)
    (h : decide (8 ≤ a) && decide (a ≤ 16) = true) (m : Word → Byte) (v : Nat) :
    read32 (writeLE m (sp - BitVec.ofNat 64 a) v 8) f = read32 m f := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  unfold read32
  rw [readLE_writeLE_disj (R := ⟨sp - BitVec.ofNat 64 a, 8⟩) (by simp only [Region.Disjoint] at *; bv_omega) _ _ _ _
    (by simp [Region.covers])]

theorem slot16_after_base {f sp : Word} (hFS : (Region.mk f 144).Disjoint ⟨sp - 16#64, 16⟩) (b n : Nat)
    (h : decide (8 ≤ b) && decide (b ≤ 16) && decide (n ≤ 144) && decide (0 < n) = true) (m : Word → Byte) (v : Nat) :
    read64 (writeLE m f v n) (sp - BitVec.ofNat 64 b) = read64 m (sp - BitVec.ofNat 64 b) := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact Auto.read64_writeLE_of_disjoint (R := ⟨f, n⟩) (by simp only [Region.Disjoint] at *; bv_omega) _ _ _ _
    (by simp [Region.covers])

/-- The EOF bit as musl's `-(f->flags & F_EOF) >> ...`: slli 59, srai 63 is -1 if bit 4 is set, else 0. -/
theorem eof_bit (x : Word) : (x <<< 59).sshiftRight 63 = (if x &&& 16#64 = 0 then 0 else -1) := by
  exact NoCompiler.Libc.sshiftRight_shl59 x


/-- A store to one of the FILE fields `__toread` writes (rpos, rend, wend, wpos, wbase, mode) leaves a byte
    outside them. -/
theorem tr_field_out' {f p : Word} (h2 : ¬ (Region.mk (f + 8#64) 16).mem p)
    (h3 : ¬ (Region.mk (f + 32#64) 32).mem p) (h4 : ¬ (Region.mk (f + 136#64) 4).mem p) (a n : Nat)
    (h : decide ((a = 8 ∨ a = 16 ∨ a = 32 ∨ a = 40 ∨ a = 56) ∧ n = 8 ∨ a = 136 ∧ n = 4) = true)
    (m : Word → Byte) (v : Nat) : writeLE m (f + BitVec.ofNat 64 a) v n p = m p := by
  simp only [decide_eq_true_eq] at h
  apply writeLE_other
  simp only [Region.mem] at h2 h3 h4
  rcases h with ⟨ha | ha | ha | ha | ha, rfl⟩ | ⟨rfl, rfl⟩ <;> (try subst ha) <;> bv_omega

theorem tr_field_out {f p : Word} (h1 : ¬ (Region.mk f 4).mem p) (h2 : ¬ (Region.mk (f + 8#64) 16).mem p)
    (h3 : ¬ (Region.mk (f + 32#64) 32).mem p) (h4 : ¬ (Region.mk (f + 136#64) 4).mem p) (a n : Nat)
    (h : decide ((a = 8 ∨ a = 16 ∨ a = 32 ∨ a = 40 ∨ a = 56) ∧ n = 8 ∨ a = 136 ∧ n = 4) = true)
    (m : Word → Byte) (v : Nat) : writeLE m (f + BitVec.ofNat 64 a) v n p = m p := by
  simp only [decide_eq_true_eq] at h
  apply writeLE_other
  simp only [Region.mem] at h1 h2 h3 h4
  rcases h with ⟨ha | ha | ha | ha | ha, rfl⟩ | ⟨rfl, rfl⟩ <;> (try subst ha) <;> bv_omega

/-- `__toread(f)` at the process level, when nothing is buffered for writing (wpos = wbase, so f->write is not
    called; slen's stdin): wpos, wbase, wend cleared; F_NORD (4) set: -1; else rpos = rend = buf + buf_size and -1
    if F_EOF (16) is set, else 0, flags unchanged. The kernel and the trace unchanged; nothing written outside FILE's flags,
    rpos/rend, wend/wpos/wbase, mode and the 16-byte frame. -/
def toreadP : SpecP Word where
  pre := fun f s k => s.reg 10 = f ∧ aligned f 8 ∧ read64 s.mem (f + 40#64) = read64 s.mem (f + 56#64) ∧
    (Perm.mk [] [⟨f, 144⟩, ⟨s.reg 2 - 16#64, 16⟩]).le k.perm ∧ (Region.mk f 144).Disjoint ⟨s.reg 2 - 16#64, 16⟩
  post := fun f x y => y.2 = x.2 ∧ y.1.trace = x.1.trace ∧
    (∀ p, ¬ (Region.mk f 4).mem p → ¬ (Region.mk (f + 8#64) 16).mem p → ¬ (Region.mk (f + 32#64) 32).mem p →
      ¬ (Region.mk (f + 136#64) 4).mem p → ¬ (Region.mk (x.1.reg 2 - 16#64) 16).mem p → y.1.mem p = x.1.mem p) ∧
    read64 y.1.mem (f + 32#64) = 0 ∧ read64 y.1.mem (f + 40#64) = 0 ∧ read64 y.1.mem (f + 56#64) = 0 ∧
    (read32 x.1.mem f &&& 4#64 ≠ 0 → y.1.reg 10 = -1) ∧
    (read32 x.1.mem f &&& 4#64 = 0 →
      read64 y.1.mem (f + 8#64) = read64 x.1.mem (f + 88#64) + read64 x.1.mem (f + 96#64) ∧
      read64 y.1.mem (f + 16#64) = read64 x.1.mem (f + 88#64) + read64 x.1.mem (f + 96#64) ∧
      y.1.reg 10 = (if read32 x.1.mem f &&& 16#64 = 0 then 0 else -1) ∧ readLE y.1.mem f 4 = readLE x.1.mem f 4)

theorem __toread_verified : VerifiedProc code __toread_dom __toread_entry toreadP := by
  intro f s k he ⟨ha0, hal, hw, hle, hFS⟩
  have hpc := he.pc
  have hx := he.live
  have hsp := he.sp
  have hra4 := he.retAligned
  have hret := he.ret
  simp only [__toread_entry] at hpc
  simp only [Reg.sp, Reg.ra] at hsp hra4 hret
  have wF : ∀ o n, o + n ≤ 144 → k.perm.canWrite (f + BitVec.ofNat 64 o) n := fun o n h =>
    hle.write _ _ (.inr ⟨⟨f, 144⟩, by simp, by simp only [Region.covers]; bv_omega⟩)
  have wS : ∀ o, 8 ≤ o → o ≤ 16 → k.perm.canWrite (s.reg 2 - BitVec.ofNat 64 o) 8 := fun o h1 h3 =>
    hle.write _ _ (.inr ⟨⟨s.reg 2 - 16#64, 16⟩, by simp, by simp only [Region.covers]; bv_omega⟩)
  have alF : ∀ o, o % 8 = 0 → aligned (f + BitVec.ofNat 64 o) 8 := fun o h => sw_alF hal o h
  have alF4 : ∀ o, o % 4 = 0 → aligned (f + BitVec.ofNat 64 o) 4 := by intro o h; unfold aligned at *; bv_omega
  have e16 : s.reg 2 + 18446744073709551600#64 = s.reg 2 - 16#64 := by bv_omega
  have e8 : s.reg 2 - 16#64 + 8#64 = s.reg 2 - 8#64 := by bv_omega
  have e16' : s.reg 2 - 16#64 + 16#64 = s.reg 2 := by bv_omega
  have fa := field_after_field f
  have fa4 := field4_after_field f
  have fs := field_after_slot16 hFS
  have sf := slot16_after_field hFS
  nocompiler_wstep [hx, hpc, e16]
  nocompiler_wstep [hx, e8, sw_alS hsp 8 rfl]
  refine ⟨wS 8 (by omega) (by omega), ?_⟩
  nocompiler_wstep [hx, sw_alS hsp 16 rfl, BitVec.add_zero]
  refine ⟨wS 16 (by omega) (by omega), ?_⟩
  have fs64 : ∀ a b, (decide (8 ≤ a) && decide (a ≤ 16) && decide (b + 8 ≤ 144) && decide (0 < 8) && decide (8 ≤ 8)) = true →
      ∀ (m : Word → Byte) (v : Nat), read64 (writeLE m (s.reg 2 - BitVec.ofNat 64 a) v 8) (f + BitVec.ofNat 64 b) =
        read64 m (f + BitVec.ofNat 64 b) := by
    intro a b h m v; unfold read64; rw [fs a b 8 h]
  have fs32 : ∀ a b, (decide (8 ≤ a) && decide (a ≤ 16) && decide (b + 4 ≤ 144) && decide (0 < 4) && decide (4 ≤ 8)) = true →
      ∀ (m : Word → Byte) (v : Nat), read32 (writeLE m (s.reg 2 - BitVec.ofNat 64 a) v 8) (f + BitVec.ofNat 64 b) =
        read32 m (f + BitVec.ofNat 64 b) := by
    intro a b h m v; unfold read32; rw [fs a b 4 h]
  nocompiler_wstep [hx, ha0]
  nocompiler_wstep [hx, ha0, alF4 136 rfl]
  refine ⟨Perm.canRead_of_canWrite (wF 136 4 (by omega)), ?_⟩
  nocompiler_wstep [hx, alF 40 rfl, fs64]
  refine ⟨Perm.canRead_of_canWrite (wF 40 8 (by omega)), ?_⟩
  nocompiler_wstep [hx, alF 56 rfl, fs64]
  refine ⟨Perm.canRead_of_canWrite (wF 56 8 (by omega)), ?_⟩
  nocompiler_wstep [hx]
  nocompiler_wstep [hx]
  nocompiler_wstep [hx, alF4 136 rfl]
  refine ⟨wF 136 4 (by omega), ?_⟩
  nocompiler_wstep [hx, hw, beq_self_eq_true]
  have ba := base_after_field f
  have bs := base_after_slot16 hFS
  have sb := slot16_after_base hFS
  have fb := field_after_base f
  have al0 : aligned f 4 := by have := alF4 0 rfl; simpa using this
  have w0 : k.perm.canWrite f 4 := by have := wF 0 4 (by omega); simpa using this
  nocompiler_wstep [hx, al0, ba, bs]
  refine ⟨Perm.canRead_of_canWrite w0, ?_⟩
  nocompiler_wstep [hx, alF 32 rfl]
  refine ⟨wF 32 8 (by omega), ?_⟩
  nocompiler_wstep [hx, alF 56 rfl]
  refine ⟨wF 56 8 (by omega), ?_⟩
  nocompiler_wstep [hx]
  nocompiler_wstep [hx, alF 40 rfl]
  refine ⟨wF 40 8 (by omega), ?_⟩
  by_cases hN : read32 s.mem f &&& 4#64 = 0
  · have hb : (read32 s.mem f &&& 4#64 != 0) = false := by rw [hN]; rfl
    nocompiler_wstep [hx, hb]
    nocompiler_wstep [hx, alF 88 rfl, fa, fs64]
    refine ⟨Perm.canRead_of_canWrite (wF 88 8 (by omega)), ?_⟩
    nocompiler_wstep [hx, alF 96 rfl, fa, fs64]
    refine ⟨Perm.canRead_of_canWrite (wF 96 8 (by omega)), ?_⟩
    nocompiler_wstep [hx]
    nocompiler_wstep [hx, alF 16 rfl]
    refine ⟨wF 16 8 (by omega), ?_⟩
    nocompiler_wstep [hx, alF 8 rfl]
    refine ⟨wF 8 8 (by omega), ?_⟩
    nocompiler_wstep [hx]
    nocompiler_wstep [hx, eof_bit]
    nocompiler_wstep [hx]
    nocompiler_wstep [hx, e8, sw_alS hsp 8 rfl, sf, slot_ne, fw_slot_same]
    refine ⟨Perm.canRead_of_canWrite (wS 8 (by omega) (by omega)), ?_⟩
    nocompiler_wstep [hx, BitVec.add_zero, sw_alS hsp 16 rfl, sf, slot_ne, fw_slot_same]
    refine ⟨Perm.canRead_of_canWrite (wS 16 (by omega) (by omega)), ?_⟩
    nocompiler_wstep [hx, e16']
    nocompiler_wstep [hx, ret_mask hra4, hra4]
    refine .done ⟨.inl ?_, .inl ⟨?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, fun h => absurd hN h, fun _ => ⟨?_, ?_, ?_, ?_⟩⟩⟩
    · simp only [nocompiler_state]; exact hret
    · simp only [nocompiler_state]; exact hx
    · simp only [nocompiler_state, Reg.ra]
    · intro q hq
      simp only [preservedRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals (simp (disch := nocompiler_decide_closed) only [nocompiler_state])
    · simp only [nocompiler_state]
    · intro p hp1 hq2 hq3 hq4 hp2
      have wF' := tr_field_out hp1 hq2 hq3 hq4
      have wS' : ∀ (a : Nat), (decide (8 ≤ a) && decide (a ≤ 16)) = true → ∀ (m : Word → Byte) (v : Nat),
          writeLE m (s.reg 2 - BitVec.ofNat 64 a) v 8 p = m p := fun a h m v =>
        writeLE_of_not_mem (r := ⟨s.reg 2 - 16#64, 16⟩)
          (by simp only [Bool.and_eq_true, decide_eq_true_eq] at h; simp only [Region.covers]; bv_omega) hp2
      simp (disch := nocompiler_decide_closed) only [nocompiler_state, wF', wS']
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state, fa, Auto.read64_writeLE_same']; rfl
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state, fa, Auto.read64_writeLE_same']; rfl
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state, fa, Auto.read64_writeLE_same']; rfl
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state, fa, Auto.read64_writeLE_same',
        BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state, fa, Auto.read64_writeLE_same',
        BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; rfl
    · apply readLE_congr; intro j hj
      have hq2 : ¬ (Region.mk (f + 8#64) 16).mem (f + BitVec.ofNat 64 j) := by simp only [Region.mem]; bv_omega
      have hq3 : ¬ (Region.mk (f + 32#64) 32).mem (f + BitVec.ofNat 64 j) := by simp only [Region.mem]; bv_omega
      have hq4 : ¬ (Region.mk (f + 136#64) 4).mem (f + BitVec.ofNat 64 j) := by simp only [Region.mem]; bv_omega
      have hq5 : ¬ (Region.mk (s.reg 2 - 16#64) 16).mem (f + BitVec.ofNat 64 j) :=
        Auto.not_mem_of_disjoint hFS.symm (by omega)
      have wF' := tr_field_out' hq2 hq3 hq4
      have wS' : ∀ (a : Nat), (decide (8 ≤ a) && decide (a ≤ 16)) = true → ∀ (m : Word → Byte) (v : Nat),
          writeLE m (s.reg 2 - BitVec.ofNat 64 a) v 8 (f + BitVec.ofNat 64 j) = m (f + BitVec.ofNat 64 j) := fun a h m v =>
        writeLE_of_not_mem (r := ⟨s.reg 2 - 16#64, 16⟩)
          (by simp only [Bool.and_eq_true, decide_eq_true_eq] at h; simp only [Region.covers]; bv_omega) hq5
      simp (disch := nocompiler_decide_closed) only [nocompiler_state, wF', wS']
  · have hb : (read32 s.mem f &&& 4#64 != 0) = true := by simpa using hN
    nocompiler_wstep [hx, hb]
    nocompiler_wstep [hx]
    nocompiler_wstep [hx, al0]
    refine ⟨w0, ?_⟩
    nocompiler_wstep [hx]
    nocompiler_wstep [hx, e8, sw_alS hsp 8 rfl, sf, sb, slot_ne, fw_slot_same]
    refine ⟨Perm.canRead_of_canWrite (wS 8 (by omega) (by omega)), ?_⟩
    nocompiler_wstep [hx, BitVec.add_zero, sw_alS hsp 16 rfl, sf, sb, slot_ne, fw_slot_same]
    refine ⟨Perm.canRead_of_canWrite (wS 16 (by omega) (by omega)), ?_⟩
    nocompiler_wstep [hx, e16']
    nocompiler_wstep [hx, ret_mask hra4, hra4]
    refine .done ⟨.inl ?_, .inl ⟨?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, fun _ => ?_, fun h => absurd h hN⟩⟩
    · simp only [nocompiler_state]; exact hret
    · simp only [nocompiler_state]; exact hx
    · simp only [nocompiler_state, Reg.ra]
    · intro q hq
      simp only [preservedRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals (simp (disch := nocompiler_decide_closed) only [nocompiler_state])
    · simp only [nocompiler_state]
    · intro p hp1 hq2 hq3 hq4 hp2
      have wF' := tr_field_out hp1 hq2 hq3 hq4
      have wF0 : ∀ (m : Word → Byte) (v : Nat), writeLE m f v 4 p = m p := fun m v =>
        writeLE_of_not_mem (r := ⟨f, 4⟩) (by simp only [Region.covers]; bv_omega) hp1
      have wS' : ∀ (a : Nat), (decide (8 ≤ a) && decide (a ≤ 16)) = true → ∀ (m : Word → Byte) (v : Nat),
          writeLE m (s.reg 2 - BitVec.ofNat 64 a) v 8 p = m p := fun a h m v =>
        writeLE_of_not_mem (r := ⟨s.reg 2 - 16#64, 16⟩)
          (by simp only [Bool.and_eq_true, decide_eq_true_eq] at h; simp only [Region.covers]; bv_omega) hp2
      simp (disch := nocompiler_decide_closed) only [nocompiler_state, wF', wS', wF0]
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state, fa, fb, Auto.read64_writeLE_same']; rfl
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state, fa, fb, Auto.read64_writeLE_same']; rfl
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state, fa, fb, Auto.read64_writeLE_same']; rfl
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; rfl

/-! ## `__stdio_read` and `fread`: from the library (Examples/Libc/Musl/StdioRead*, Fread*), under their old names -/

export NoCompiler.Libc.Musl.StdioRead (writeBytes_at writeBytes_out readBytes_eq_of applyWrites_scatter2 scatter2_out scatter2_first scatter2_second sr_field_after_slot sr_field_after_slot64 sr_slot_after_field stdioReadPerm StdioReadDisj ReadK FileEnd ReadsK lookup_map_advance take_chunk_append maxRW_pos stdioReadP SrCommon sext_or_16 sr_slot_after_base sr_fileLE sr_np srK sr_epi disj_byte_of disj_sub_r field_disj rend_eq writeLE_one_self readLE_one file_sub_disj' srK_out srK_fileLE sr_pos sr_ecall_dom sr_slot_out sr_not16 sr_al64 sr_errDisj16 sr_retcall slt_zero_ofNat srK_nil writeBytes_congr_pt applyWrites_congr_pt not_mem_of_mem_disj sr_slot_in SrCommon_setPc SrCommon_mod sr_iovs stdioReadP_pre_perm chunk_len_le sr_readv srK_one sr_read)
export NoCompiler.Libc.Musl.Fread (freadD frAvail frBuffered StdinFile freadPerm FreadDisj FrFrame EofSet FrK FrK_init FrK_congr FrK_step FrK_end freadP fr_epi FrSlots FrCommon frStream FrOut fr_done fr_exit_full fr_exit_part FrLoop FrOut_of_loop not_field_of_disj not_sub_of_disj mem_sub_of file_mem field_byte_out fr_file_byte FrQ FrLoop_setPc frAvail_of_eq not_frame16 not_in_F_sub fr_slot_ok liftQ fr_toread covers_field fr_frame_field disj_mono within_sub_c within_s80 within_f128 fr_sread_pre FrCommon_setPc FrCommon_setReg ofNat_ne_zero' availC withinC FrCommon_mod avail_sub mem_of_within within_shift FrCommon_mod' readLE_lt' nord_or not_s80 not_sub_dest dest_low_out slot_out80 slot_in144 dest_in readBytes_succ_drop fr_sread fr_loop lock_neg fr_agree0 fr_field_after_slot fr_field_after_slot64 fr_flags fr_agreeF fr_mid fr_slot_after_field fr_entry)

theorem Kern.lookup_advance (k : Kern) (fd : Word) (m : Nat) :
    (k.advance fd m).files.lookup fd = (k.files.lookup fd).map fun fl => { fl with off := fl.off + m } :=
  lookup_map_advance _ _ _

theorem Kern.advance_zero (k : Kern) (fd : Word) : k.advance fd 0 = k := by
  cases k; simp [Kern.advance]

theorem Kern.advance_advance (k : Kern) (fd : Word) (a b : Nat) :
    (k.advance fd a).advance fd b = k.advance fd (a + b) := by
  simp only [Kern.advance, List.map_map]
  congr 1; apply List.map_congr_left; intro p _
  by_cases h : p.1 = fd <;> simp [h, Nat.add_assoc]

theorem ReadsK.nil (fd : Word) (k : Kern) : ReadsK fd [] k k := by
  cases h : k.files.lookup fd with
  | none => exact .inl ⟨h, rfl⟩
  | some fl => exact .inr ⟨fl, h, by simp, by simp [Kern.advance_zero]⟩

theorem ReadsK.perm {fd : Word} {dss : List (List Byte)} {k k' : Kern} (h : ReadsK fd dss k k') : k'.perm = k.perm := by
  rcases h with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩
  · rfl
  · rfl

theorem ReadsK.snoc {fd : Word} {dss : List (List Byte)} {ds : List Byte} {N : Nat} {k k1 k2 : Kern}
    (h : ReadsK fd dss k k1) (h' : ReadK fd N ds k1 k2) : ReadsK fd (dss ++ [ds]) k k2 := by
  rcases h with ⟨hn, rfl⟩ | ⟨fl, hl, hf, rfl⟩
  · rcases h' with ⟨-, rfl⟩ | ⟨fl', hl', -, -⟩
    · exact .inl ⟨hn, rfl⟩
    · rw [hn] at hl'; cases hl'
  · rcases h' with ⟨hn, -⟩ | ⟨fl', hl', hd, rfl⟩
    · rw [Kern.lookup_advance, hl] at hn; cases hn
    · rw [Kern.lookup_advance, hl] at hl'
      cases hl'
      have hL : dss.flatten.length ≤ (fl.data.drop fl.off).length := by
        have := congrArg List.length hf; rw [List.length_take] at this; omega
      have hd' : ds = ((fl.data.drop fl.off).drop dss.flatten.length).take (min N maxRW) := by
        rw [hd]; simp only [OpenFile.chunk, List.drop_drop]
      refine .inr ⟨fl, hl, ?_, ?_⟩
      · simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil, List.length_append]
        generalize hLd : dss.flatten.length = L at hf hd' hL ⊢
        generalize hF : dss.flatten = F at hf ⊢
        rw [hd', hf]; exact take_chunk_append _ _ _ hL
      · simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil, List.length_append]
        rw [Kern.advance_advance]

/-- A read that returned nothing (of at least one byte asked) leaves the file, if any, at its end. -/
theorem FileEnd.of_nil {fd : Word} {N : Nat} {k1 k2 : Kern} (h : ReadK fd N [] k1 k2) (hN : 0 < N) : FileEnd fd k2 := by
  rcases h with ⟨hn, rfl⟩ | ⟨fl, hl, hd, rfl⟩
  · intro fl h; rw [hn] at h; cases h
  · intro fl' h _
    rw [List.length_nil, Kern.advance_zero, hl] at h
    cases h
    have h0 := congrArg List.length hd
    simp only [OpenFile.chunk, List.length_take, List.length_nil, List.length_drop] at h0
    have := maxRW_pos
    omega

theorem FileEnd.mono {fd : Word} {N : Nat} {ds : List Byte} {k1 k2 : Kern} (hE : FileEnd fd k1)
    (h : ReadK fd N ds k1 k2) : FileEnd fd k2 := by
  rcases h with ⟨-, rfl⟩ | ⟨fl, hl, -, rfl⟩
  · exact hE
  · intro fl' h hin
    rw [Kern.lookup_advance, hl] at h
    cases h
    have := hE fl hl hin
    simp only; omega

/-- `__stdio_read` (with `__syscall_ret`, `___errno_location`) in slen's image, from the library. -/
theorem __stdio_read_verified : VerifiedProc code __stdio_read_dom __stdio_read_entry stdioReadP := by
  have hv := NoCompiler.Libc.Musl.StdioRead.__stdio_read_verified
  have e : NoCompiler.Libc.Musl.StdioReadImg.img = Code.ofChunks 0x122c0#64 NoCompiler.Libc.Musl.StdioReadImg.chunks := rfl
  rw [e] at hv
  refine VerifiedProc.of_code_eq hv fun x hx => ?_
  simp only [__stdio_read_dom, Dom.mem_cons_iff] at hx
  rcases hx with h | h | h | h
  · exact Code.instr_eq_of_chunk (k := 0) NoCompiler.Libc.Musl.StdioReadImg.chunks_contig rfl NoCompiler.Libc.Musl.StdioReadImg.chunks_bound __syscall_ret_chunk
      rfl rfl (by decide) x
      (by rw [show [chunk_30.range 0x111d0#64] = [(0x122c0#64, 60)] by decide, Dom.mem_single_iff]; exact h)
  · exact Code.instr_eq_of_chunk (k := 1) NoCompiler.Libc.Musl.StdioReadImg.chunks_contig rfl NoCompiler.Libc.Musl.StdioReadImg.chunks_bound ___errno_location_chunk
      rfl rfl (by decide) x
      (by rw [show [chunk_31.range 0x111d0#64] = [(0x122fc#64, 12)] by decide, Dom.mem_single_iff]; exact h)
  · exact Code.instr_eq_of_chunk (k := 2) NoCompiler.Libc.Musl.StdioReadImg.chunks_contig rfl NoCompiler.Libc.Musl.StdioReadImg.chunks_bound __stdio_read_chunk
      rfl rfl (by decide) x
      (by rw [show [chunk_32.range 0x111d0#64] = [(0x12308#64, 248)] by decide, Dom.mem_single_iff]; exact h)
  · simp [Dom.mem] at h

/-- `fread` in slen's image, from the library (memcpy's theorem as a hypothesis, as there). -/
theorem fread_verified (hM : VerifiedProc code memcpy_dom 0x125dc#64 memcpySpec) :
    VerifiedProc code freadD fread_entry freadP := by
  have e : NoCompiler.Libc.Musl.FreadImg.img = Code.ofChunks 0x11af4#64 NoCompiler.Libc.Musl.FreadImg.chunks := rfl
  have hM' : VerifiedProc NoCompiler.Libc.Musl.FreadImg.img NoCompiler.Libc.Musl.Fread.memcpy_dom 0x125dc#64 memcpySpec := by
    rw [e]
    refine VerifiedProc.of_code_eq hM fun x hx => Eq.symm ?_
    simp only [NoCompiler.Libc.Musl.Fread.memcpy_dom] at hx
    simp only [Dom.mem_cons_iff] at hx
    rcases hx with h | h
    · exact Code.instr_eq_of_chunk (k := 9) NoCompiler.Libc.Musl.FreadImg.chunks_contig rfl NoCompiler.Libc.Musl.FreadImg.chunks_bound memcpy_chunk
        rfl rfl (by decide) x
        (by rw [show [chunk_36.range 0x111d0#64] = [(0x125dc#64, 1044)] by decide, Dom.mem_single_iff]; exact h)
    · simp [Dom.mem] at h
  have hv := NoCompiler.Libc.Musl.Fread.fread_verified hM'
  rw [e] at hv
  refine VerifiedProc.of_code_eq hv fun x hx => ?_
  simp only [NoCompiler.Libc.Musl.Fread.freadD, NoCompiler.Libc.Musl.Fread.fread_dom, NoCompiler.Libc.Musl.Fread.__stdio_read_dom,
    List.cons_append, List.nil_append] at hx
  simp only [Dom.mem_cons_iff] at hx
  rcases hx with h | h | h | h | h | h | h | h | h
  · exact Code.instr_eq_of_chunk (k := 0) NoCompiler.Libc.Musl.FreadImg.chunks_contig rfl NoCompiler.Libc.Musl.FreadImg.chunks_bound fread_chunk
      rfl rfl (by decide) x
      (by rw [show [chunk_16.range 0x111d0#64] = [(0x11af4#64, 328)] by decide, Dom.mem_single_iff]; exact h)
  · exact Code.instr_eq_of_chunk (k := 1) NoCompiler.Libc.Musl.FreadImg.chunks_contig rfl NoCompiler.Libc.Musl.FreadImg.chunks_bound __lockfile_chunk
      rfl rfl (by decide) x
      (by rw [show [chunk_17.range 0x111d0#64] = [(0x11c3c#64, 240)] by decide, Dom.mem_single_iff]; exact h)
  · exact Code.instr_eq_of_chunk (k := 2) NoCompiler.Libc.Musl.FreadImg.chunks_contig rfl NoCompiler.Libc.Musl.FreadImg.chunks_bound __unlockfile_chunk
      rfl rfl (by decide) x
      (by rw [show [chunk_18.range 0x111d0#64] = [(0x11d2c#64, 92)] by decide, Dom.mem_single_iff]; exact h)
  · exact Code.instr_eq_of_chunk (k := 3) NoCompiler.Libc.Musl.FreadImg.chunks_contig rfl NoCompiler.Libc.Musl.FreadImg.chunks_bound __toread_chunk
      rfl rfl (by decide) x
      (by rw [show [chunk_19.range 0x111d0#64] = [(0x11d88#64, 148)] by decide, Dom.mem_single_iff]; exact h)
  · exact Code.instr_eq_of_chunk (k := 9) NoCompiler.Libc.Musl.FreadImg.chunks_contig rfl NoCompiler.Libc.Musl.FreadImg.chunks_bound memcpy_chunk
      rfl rfl (by decide) x
      (by rw [show [chunk_36.range 0x111d0#64] = [(0x125dc#64, 1044)] by decide, Dom.mem_single_iff]; exact h)
  · exact Code.instr_eq_of_chunk (k := 5) NoCompiler.Libc.Musl.FreadImg.chunks_contig rfl NoCompiler.Libc.Musl.FreadImg.chunks_bound __syscall_ret_chunk
      rfl rfl (by decide) x
      (by rw [show [chunk_30.range 0x111d0#64] = [(0x122c0#64, 60)] by decide, Dom.mem_single_iff]; exact h)
  · exact Code.instr_eq_of_chunk (k := 6) NoCompiler.Libc.Musl.FreadImg.chunks_contig rfl NoCompiler.Libc.Musl.FreadImg.chunks_bound ___errno_location_chunk
      rfl rfl (by decide) x
      (by rw [show [chunk_31.range 0x111d0#64] = [(0x122fc#64, 12)] by decide, Dom.mem_single_iff]; exact h)
  · exact Code.instr_eq_of_chunk (k := 7) NoCompiler.Libc.Musl.FreadImg.chunks_contig rfl NoCompiler.Libc.Musl.FreadImg.chunks_bound __stdio_read_chunk
      rfl rfl (by decide) x
      (by rw [show [chunk_32.range 0x111d0#64] = [(0x12308#64, 248)] by decide, Dom.mem_single_iff]; exact h)
  · simp [Dom.mem] at h

end Examples.Libc.Slen
