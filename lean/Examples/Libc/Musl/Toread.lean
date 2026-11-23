import Examples.Libc.Musl.ToreadImg
import Examples.Libc.Musl.StdioWrite4
import NoCompiler.Linux.Run
import NoCompiler.Lib.Rw

/-!
# `__toread` (musl src/stdio/__toread.c) at the process level

The proof is C's (c-logs/runt/T5.lean, by `nocompiler_run`); the FILE-field lemmas are from Examples/Libc/Fread.lean.
-/
set_option maxRecDepth 20000
namespace NoCompiler.Libc.Musl.Toread
open NoCompiler NoCompiler.Linux NoCompiler.Libc NoCompiler.Libc.Musl.StdioWrite NoCompiler.Libc.Musl.ToreadImg

theorem fw_slot_same {sp : Word} (o : Nat) (m : Word → Byte) (v : Word) :
    read64 (writeLE m (sp - BitVec.ofNat 64 o) v.toNat 8) (sp - BitVec.ofNat 64 o) = v := by
  rw [Auto.read64_writeLE_same', BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The EOF bit as musl's `-(f->flags & F_EOF) >> ...`: slli 59, srai 63 is -1 if bit 4 is set, else 0. -/
theorem eof_bit (x : Word) : (x <<< 59).sshiftRight 63 = (if x &&& 16#64 = 0 then 0 else -1) := by
  exact NoCompiler.Libc.sshiftRight_shl59 x

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

/-- An 8-byte FILE field read after a store to another (offsets as decidable side conditions). -/
theorem field_after_field (f : Word) (a n b : Nat)
    (h : (decide (a + n ≤ b) || decide (b + 8 ≤ a)) && decide (b + 8 ≤ 144) && decide (a + n ≤ 144) && decide (0 < n) = true)
    (m : Word → Byte) (v : Nat) :
    read64 (writeLE m (f + BitVec.ofNat 64 a) v n) (f + BitVec.ofNat 64 b) = read64 m (f + BitVec.ofNat 64 b) := by
  exact Lib.read64_field_after_field f a n b (by simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h ⊢; omega) m v

/-- A 4-byte FILE field (as readLE) after a store to another. -/
theorem field4_after_field (f : Word) (a n b : Nat)
    (h : (decide (a + n ≤ b) || decide (b + 4 ≤ a)) && decide (b + 4 ≤ 144) && decide (a + n ≤ 144) && decide (0 < n) = true)
    (m : Word → Byte) (v : Nat) :
    readLE (writeLE m (f + BitVec.ofNat 64 a) v n) (f + BitVec.ofNat 64 b) 4 = readLE m (f + BitVec.ofNat 64 b) 4 := by
  exact Lib.readLE_field_after_field f a n b 4 (by simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h ⊢; omega) m v

/-- A FILE field after a store to a stack slot, and a stack slot after a store to a FILE field. -/
theorem field_after_slot16 {f sp : Word} (hFS : (Region.mk f 144).Disjoint ⟨sp - 16#64, 16⟩) (a b n : Nat)
    (h : decide (8 ≤ a) && decide (a ≤ 16) && decide (b + n ≤ 144) && decide (0 < n) && decide (n ≤ 8) = true)
    (m : Word → Byte) (v : Nat) :
    readLE (writeLE m (sp - BitVec.ofNat 64 a) v 8) (f + BitVec.ofNat 64 b) n = readLE m (f + BitVec.ofNat 64 b) n := by
  exact Lib.readLE_field_after_slot hFS a 8 b n (by simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h ⊢; omega) m v

theorem slot16_after_field {f sp : Word} (hFS : (Region.mk f 144).Disjoint ⟨sp - 16#64, 16⟩) (a b n : Nat)
    (h : decide (8 ≤ b) && decide (b ≤ 16) && decide (a + n ≤ 144) && decide (0 < n) = true)
    (m : Word → Byte) (v : Nat) :
    read64 (writeLE m (f + BitVec.ofNat 64 a) v n) (sp - BitVec.ofNat 64 b) = read64 m (sp - BitVec.ofNat 64 b) := by
  exact Lib.read64_slot_after_field hFS a n b (by simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h ⊢; omega) m v

theorem base_after_field (f : Word) (a n : Nat)
    (h : decide (4 ≤ a) && decide (a + n ≤ 144) && decide (0 < n) = true) (m : Word → Byte) (v : Nat) :
    read32 (writeLE m (f + BitVec.ofNat 64 a) v n) f = read32 m f := by
  simpa using Lib.read32_field_after_field f a n 0 (by simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h ⊢; omega) m v

theorem base_after_slot16 {f sp : Word} (hFS : (Region.mk f 144).Disjoint ⟨sp - 16#64, 16⟩) (a : Nat)
    (h : decide (8 ≤ a) && decide (a ≤ 16) = true) (m : Word → Byte) (v : Nat) :
    read32 (writeLE m (sp - BitVec.ofNat 64 a) v 8) f = read32 m f := by
  simpa using Lib.read32_field_after_slot hFS a 8 0 (by simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h ⊢; omega) m v

theorem slot16_after_base {f sp : Word} (hFS : (Region.mk f 144).Disjoint ⟨sp - 16#64, 16⟩) (b n : Nat)
    (h : decide (8 ≤ b) && decide (b ≤ 16) && decide (n ≤ 144) && decide (0 < n) = true) (m : Word → Byte) (v : Nat) :
    read64 (writeLE m f v n) (sp - BitVec.ofNat 64 b) = read64 m (sp - BitVec.ofNat 64 b) := by
  simpa using Lib.read64_slot_after_field hFS 0 n b (by simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h ⊢; omega) m v

/-- A FILE field after a store at the FILE's base (flags), and the flags after a store to another field. -/
theorem field_after_base (f : Word) (n b : Nat)
    (h : decide (n ≤ b) && decide (b + 8 ≤ 144) && decide (0 < n) = true) (m : Word → Byte) (v : Nat) :
    read64 (writeLE m f v n) (f + BitVec.ofNat 64 b) = read64 m (f + BitVec.ofNat 64 b) := by
  simpa using Lib.read64_field_after_field f 0 n b (by simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h ⊢; omega) m v

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

set_option maxHeartbeats 4000000 in
theorem __toread_verified : VerifiedProc img dom base toreadP := by
  intro f s k he ⟨ha0, hal, hw, hle, hFS⟩
  have hpc := he.pc
  have hx := he.live
  have hsp := he.sp
  have hra4 := he.retAligned
  have hret := he.ret
  simp only [base] at hpc
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
  have fs64 : ∀ a b, (decide (8 ≤ a) && decide (a ≤ 16) && decide (b + 8 ≤ 144) && decide (0 < 8) && decide (8 ≤ 8)) = true →
      ∀ (m : Word → Byte) (v : Nat), read64 (writeLE m (s.reg 2 - BitVec.ofNat 64 a) v 8) (f + BitVec.ofNat 64 b) =
        read64 m (f + BitVec.ofNat 64 b) := by
    intro a b h m v; unfold read64; rw [fs a b 8 h]
  have fs32 : ∀ a b, (decide (8 ≤ a) && decide (a ≤ 16) && decide (b + 4 ≤ 144) && decide (0 < 4) && decide (4 ≤ 8)) = true →
      ∀ (m : Word → Byte) (v : Nat), read32 (writeLE m (s.reg 2 - BitVec.ofNat 64 a) v 8) (f + BitVec.ofNat 64 b) =
        read32 m (f + BitVec.ofNat 64 b) := by
    intro a b h m v; unfold read32; rw [fs a b 4 h]
  have ba := base_after_field f
  have bs := base_after_slot16 hFS
  have sb := slot16_after_base hFS
  have fb := field_after_base f
  have al0 : aligned f 4 := by have := alF4 0 rfl; simpa using this
  have w0 : k.perm.canWrite f 4 := by have := wF 0 4 (by omega); simpa using this
  nocompiler_run [hx, hpc, e16, e8, sw_alS hsp, BitVec.add_zero, ha0, alF4, alF, fs64, hw, beq_self_eq_true, al0, ba, bs] using [wF, wS]
  by_cases hN : read32 s.mem f &&& 4#64 = 0
  · have hb : (read32 s.mem f &&& 4#64 != 0) = false := by rw [hN]; rfl
    nocompiler_run [hx, hb, alF, fa, fs64, eof_bit, e8, sw_alS hsp, sf, slot_ne, fw_slot_same, BitVec.add_zero, e16', ret_mask hra4, hra4] using [wF, wS]
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
    nocompiler_run [hx, hb, al0, e8, sw_alS hsp, sf, sb, slot_ne, fw_slot_same, BitVec.add_zero, e16', ret_mask hra4, hra4] using [wF, wS]
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


end NoCompiler.Libc.Musl.Toread
