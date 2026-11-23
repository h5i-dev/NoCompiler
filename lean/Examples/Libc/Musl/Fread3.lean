import Examples.Libc.Musl.Fread2

set_option maxRecDepth 20000
namespace NoCompiler.Libc.Musl.Fread
open NoCompiler NoCompiler.Linux NoCompiler.Libc NoCompiler.Libc.Musl NoCompiler.Libc.Musl.StdioWrite NoCompiler.Libc.Musl.Toread NoCompiler.Libc.Musl.StdioRead NoCompiler.Libc.Musl.SyscallRet NoCompiler.Libc.Musl.Memcpy NoCompiler.Libc.Musl.Fread NoCompiler.Libc.Musl.FreadImg

/-- Memory that agrees with `s`'s outside the stack and FILE's mode field: `StdinFile`, the frame, the
    buffered bytes as at `s`. -/
theorem fr_agree0 {s : State} {dest n f : Word} {m : Word → Byte} (hD : FreadDisj dest n f s) (hS : StdinFile f s.mem)
    (hm : ∀ p, ¬ (Region.mk (s.reg 2 - 144#64) 144).mem p → ¬ (Region.mk (f + 136#64) 4).mem p → m p = s.mem p) :
    StdinFile f m ∧ FrFrame s dest n f m ∧ frAvail m f = frAvail s.mem f ∧ frBuffered m f = frBuffered s.mem f := by
  obtain ⟨dFS, dES, dEF, dBS, dBE, dBF, dUS, dUE, dUF, dBU⟩ := hD
  have hF : ∀ o len, o + len ≤ 136 ∨ (140 ≤ o ∧ o + len ≤ 144) → readLE m (f + BitVec.ofNat 64 o) len = readLE s.mem (f + BitVec.ofNat 64 o) len := by
    intro o len ho
    apply readLE_congr; intro j hj
    have hin := file_mem f o j (by omega)
    exact hm _ (not_mem_of_mem_disj dFS.symm hin) (field_byte_out f o j 136 4 (by omega))
  have r64 : ∀ o, o + 8 ≤ 136 → read64 m (f + BitVec.ofNat 64 o) = read64 s.mem (f + BitVec.ofNat 64 o) := by
    intro o ho; unfold read64; rw [hF o 8 (by omega)]
  have hav : frAvail m f = frAvail s.mem f := by unfold frAvail; rw [r64 8 (by omega), r64 16 (by omega)]
  have hbuf : frBuffered m f = frBuffered s.mem f := by
    unfold frBuffered; rw [hav, r64 8 (by omega)]
    rcases hS.2.2.2.2.2 with h0 | hw
    · rw [h0]; rfl
    · apply readBytes_congr; intro j hj
      have hin : (Region.mk (read64 s.mem (f + 88#64)) (read64 s.mem (f + 96#64)).toNat).mem
          (read64 s.mem (f + 8#64) + BitVec.ofNat 64 j) := by
        simp only [Region.within, Region.mem] at hw ⊢; bv_omega
      exact hm _ (not_mem_of_mem_disj dUS.symm hin)
        (not_in_F_sub (not_mem_of_mem_disj dUF.symm hin) 136 4 (by omega))
  obtain ⟨h64, hw, hn, hb, hl, ha⟩ := hS
  refine ⟨⟨by rw [r64 64 (by omega)]; exact h64, by rw [r64 40 (by omega), r64 56 (by omega)]; exact hw,
    by have := hF 0 4 (by omega); simp only [BitVec.add_zero] at this; unfold read32; rw [this]; exact hn,
    by rw [r64 96 (by omega)]; exact hb, by rw [hF 140 4 (by omega)]; exact hl, ?_⟩, ?_, hav, hbuf⟩
  · rw [hav, r64 8 (by omega), r64 88 (by omega), r64 96 (by omega)]; exact ha
  · intro p a1 a2 a3 a4 a5 a6 a7 a8; exact hm p a1 a6

theorem fr_field_after_slot {f sp : Word} (hFS : (Region.mk f 144).Disjoint ⟨sp - 144#64, 144⟩) (a b n : Nat)
    (h : decide (8 ≤ a) && decide (a ≤ 144) && decide (b + n ≤ 144) && decide (0 < n) = true)
    (m : Word → Byte) (v : Nat) :
    readLE (writeLE m (sp - BitVec.ofNat 64 a) v 8) (f + BitVec.ofNat 64 b) n = readLE m (f + BitVec.ofNat 64 b) n := by
  exact Lib.readLE_field_after_slot hFS a 8 b n (by simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h ⊢; omega) m v

theorem fr_field_after_slot64 {f sp : Word} (hFS : (Region.mk f 144).Disjoint ⟨sp - 144#64, 144⟩) (a b : Nat)
    (h : decide (8 ≤ a) && decide (a ≤ 144) && decide (b + 8 ≤ 144) && decide (0 < 8) = true)
    (m : Word → Byte) (v : Nat) :
    read64 (writeLE m (sp - BitVec.ofNat 64 a) v 8) (f + BitVec.ofNat 64 b) = read64 m (f + BitVec.ofNat 64 b) := by
  unfold read64; rw [fr_field_after_slot hFS a b 8 h]

/-- FILE's flags in a memory that agrees with `s`'s outside fread's frame, mode, rpos/rend and the destination. -/
theorem fr_flags {s : State} {dest n f : Word} {m : Word → Byte} (hD : FreadDisj dest n f s)
    (hm : ∀ p, ¬ (Region.mk (s.reg 2 - 144#64) 144).mem p → ¬ (Region.mk (f + 136#64) 4).mem p →
      ¬ (Region.mk (f + 8#64) 16).mem p → ¬ (Region.mk dest n.toNat).mem p → m p = s.mem p) :
    read32 m f = read32 s.mem f := by
  obtain ⟨dFS, -, -, -, -, dBF, -⟩ := hD
  have h : readLE m (f + BitVec.ofNat 64 0) 4 = readLE s.mem (f + BitVec.ofNat 64 0) 4 := by
    apply readLE_congr; intro j hj
    have hin := file_mem f 0 j (by omega)
    exact hm _ (not_mem_of_mem_disj dFS.symm hin) (field_byte_out f 0 j 136 4 (by omega))
      (field_byte_out f 0 j 8 16 (by omega)) (not_mem_of_mem_disj dBF hin)
  simp only [BitVec.add_zero] at h
  unfold read32; rw [h]

/-- Memory agreeing with `s`'s outside the stack, the mode field, rpos/rend and the destination: the
    `StdinFile` fields other than rpos/rend as at `s`, and the frame. -/
theorem fr_agreeF {s : State} {dest n f : Word} {m : Word → Byte} (hD : FreadDisj dest n f s) (hS : StdinFile f s.mem)
    (hm : ∀ p, ¬ (Region.mk (s.reg 2 - 144#64) 144).mem p → ¬ (Region.mk (f + 136#64) 4).mem p →
      ¬ (Region.mk (f + 8#64) 16).mem p → ¬ (Region.mk dest n.toNat).mem p → m p = s.mem p)
    (ha : frAvail m f = 0 ∨ (Region.mk (read64 m (f + 8#64)) (frAvail m f)).within
      ⟨read64 s.mem (f + 88#64), (read64 s.mem (f + 96#64)).toNat⟩) :
    StdinFile f m ∧ FrFrame s dest n f m := by
  have hD' := hD
  obtain ⟨dFS, dES, dEF, dBS, dBE, dBF, dUS, dUE, dUF, dBU⟩ := hD'
  have hF : ∀ o len, (24 ≤ o ∧ o + len ≤ 136) ∨ (140 ≤ o ∧ o + len ≤ 144) ∨ o + len ≤ 8 →
      readLE m (f + BitVec.ofNat 64 o) len = readLE s.mem (f + BitVec.ofNat 64 o) len := by
    intro o len ho
    apply readLE_congr; intro j hj
    have hin := file_mem f o j (by omega)
    exact hm _ (not_mem_of_mem_disj dFS.symm hin) (field_byte_out f o j 136 4 (by omega))
      (field_byte_out f o j 8 16 (by omega)) (not_mem_of_mem_disj dBF hin)
  have r64 : ∀ o, 24 ≤ o → o + 8 ≤ 136 → read64 m (f + BitVec.ofNat 64 o) = read64 s.mem (f + BitVec.ofNat 64 o) := by
    intro o h1 ho; unfold read64; rw [hF o 8 (by omega)]
  obtain ⟨h64, hw, hn, hb, hl, -⟩ := hS
  refine ⟨⟨by rw [r64 64 (by omega) (by omega)]; exact h64,
    by rw [r64 40 (by omega) (by omega), r64 56 (by omega) (by omega)]; exact hw,
    by have := hF 0 4 (by omega); simp only [BitVec.add_zero] at this; unfold read32; rw [this]; exact hn,
    by rw [r64 96 (by omega) (by omega)]; exact hb, by rw [hF 140 4 (by omega)]; exact hl,
    by rw [r64 88 (by omega) (by omega), r64 96 (by omega) (by omega)]; exact ha⟩, ?_⟩
  intro p a1 a2 a3 a4 a5 a6 a7 a8; exact hm p a1 a6 a4 a7

/-- `fread` at 0x11b70 (rpos == rend?), the prologue done: s0 = f, s1 = n, s2 = 1, s3 = dest, s4 = 0,
    s5 = s6 = n, a1 = rpos, a0 = rend, memory as at entry outside the stack and the mode field. -/
theorem fr_mid (dest n f : Word) (s : State) (k : Kern) (he : Entry freadD fread_entry s)
    (hpre : freadP.pre (dest, n, f) s k) (P : State) (hpc : P.pc = 0x11b70#64) (hx : P.exit = none)
    (h2 : P.reg 2 = s.reg 2 - 64#64) (h8 : P.reg 8 = f) (h9 : P.reg 9 = n) (h18 : P.reg 18 = 1) (h20 : P.reg 20 = 0)
    (h22 : P.reg 22 = n) (h19 : P.reg 19 = dest) (h21 : P.reg 21 = n) (hsl : FrSlots s P)
    (h11 : P.reg 11 = read64 s.mem (f + 8#64)) (h10 : P.reg 10 = read64 s.mem (f + 16#64))
    (hm : ∀ p, ¬ (Region.mk (s.reg 2 - 144#64) 144).mem p → ¬ (Region.mk (f + 136#64) 4).mem p → P.mem p = s.mem p)
    (htr : P.trace = s.trace) (hM : VerifiedProc img memcpy_dom 0x125dc#64 memcpySpec) :
    PReachK img freadD (FrQ dest n f s k) (P, k) := by
  have hpre' := hpre
  obtain ⟨-, -, -, -, hal, hale, hS, hB, -, hle, hD⟩ := hpre'
  obtain ⟨hS0, hF0, hav0, hbuf0⟩ := fr_agree0 hD hS hm
  have hfl0 : read32 P.mem f = read32 s.mem f := fr_flags hD (fun p a1 a2 _ _ => hm p a1 a2)
  have hC : FrCommon s n f P := ⟨hx, h2, h8, h9, h18, h20, h22, hsl⟩
  by_cases hR : read64 s.mem (f + 8#64) = read64 s.mem (f + 16#64)
  · have hb : (P.reg 11 == P.reg 10) = true := by rw [h11, h10, hR]; simp
    have hA0 : frAvail s.mem f = 0 := frAvail_of_eq hR
    have hst : frStream s f [] = [] := by simp [frStream, frBuffered, hA0, readBytes]
    nocompiler_wstep [hx, hpc, hb]
    nocompiler_wstep [hx, h22]
    by_cases hn0 : n = 0
    · have hb2 : (n != 0) = false := by rw [hn0]; rfl
      nocompiler_wstep [hx, hb2]
      nocompiler_wstep [hx]
      have hz : n.toNat = 0 := by rw [hn0]; rfl
      refine fr_exit_full dest n f s k he hpre _ (by simp only [nocompiler_state]) ?_ []
        (by simp only [nocompiler_state]; rw [htr]; simp) ?_ k (by simp only [nocompiler_state]; exact FrK_init hfl0)
      · refine FrCommon_mod hC _ (by simp only [nocompiler_state]) (by simp only [nocompiler_state]) ?_
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals simp (disch := nocompiler_decide_closed) only [nocompiler_state]
      simp only [nocompiler_state]
      refine ⟨hS0, hF0, Nat.le_refl _, ?_, ?_, fun h => absurd h (Nat.lt_irrefl _)⟩
      · rw [hz]; rfl
      · rw [hz, hbuf0]; simp [frStream]
    · have hb2 : (n != 0) = true := by simpa using hn0
      have hn0' : 0 < n.toNat := by
        rcases Nat.eq_zero_or_pos n.toNat with h | h
        · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hn0
        · exact h
      nocompiler_wstep [hx, hb2]
      refine fr_loop dest n f s k he hpre _ ⟨0, n.toNat, [], by simp only [nocompiler_state]; exact FrK_init hfl0,
        by simp only [nocompiler_state],
        ⟨?_, ?_, ?_, by omega, hn0', ?_, ?_, ?_, ?_, ?_⟩⟩
      · refine FrCommon_mod hC _ (by simp only [nocompiler_state]) (by simp only [nocompiler_state]) ?_
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals simp (disch := nocompiler_decide_closed) only [nocompiler_state]
      · simp (disch := nocompiler_decide_closed) only [nocompiler_state, h19]; simp
      · simp (disch := nocompiler_decide_closed) only [nocompiler_state, h22]; simp
      · simp only [nocompiler_state]; rw [htr]; simp
      · simp only [nocompiler_state]; exact hS0
      · simp only [nocompiler_state]; exact hF0
      · simp only [nocompiler_state]; rw [hav0, hA0]
      · simp only [nocompiler_state]; rw [hst]; rfl
  · have hsp := he.sp
    simp only [Reg.sp] at hsp
    have hD' := hD
    obtain ⟨dFS, dES, dEF, dBS, dBE, dBF, dUS, dUE, dUF, dBU⟩ := hD'
    have hb : (P.reg 11 == P.reg 10) = false := by rw [h11, h10]; simpa using hR
    have hav : 0 < frAvail s.mem f := by
      unfold frAvail
      rcases Nat.eq_zero_or_pos (read64 s.mem (f + 16#64) - read64 s.mem (f + 8#64)).toNat with h | h
      · exfalso; apply hR; have := BitVec.eq_of_toNat_eq (by simpa using h : (read64 s.mem (f + 16#64) - read64 s.mem (f + 8#64)).toNat = (0#64).toNat); bv_omega
      · exact h
    have hW : (Region.mk (read64 s.mem (f + 8#64)) (frAvail s.mem f)).within
        ⟨read64 s.mem (f + 88#64), (read64 s.mem (f + 96#64)).toNat⟩ := by
      rcases hS.2.2.2.2.2 with h | h
      · omega
      · exact h
    have hn := n.isLt
    have hKl : min (frAvail s.mem f) n.toNat < 2 ^ 64 := by omega
    have hk : (if BitVec.ult (read64 s.mem (f + 16#64) - read64 s.mem (f + 8#64)) n then
        read64 s.mem (f + 16#64) - read64 s.mem (f + 8#64) else n) = BitVec.ofNat 64 (min (frAvail s.mem f) n.toNat) := by
      unfold frAvail
      split
      · rename_i h; simp only [BitVec.ult, decide_eq_true_eq] at h
        rw [Nat.min_eq_left (by omega), BitVec.ofNat_toNat, BitVec.setWidth_eq]
      · rename_i h; simp only [BitVec.ult, decide_eq_true_eq] at h
        rw [Nat.min_eq_right (by omega), BitVec.ofNat_toNat, BitVec.setWidth_eq]
    nocompiler_wstep [hx, hpc, hb]
    nocompiler_wstep [hx, h10, h11]
    nocompiler_wstep [hx, h22, hk]
    nocompiler_wstep [hx, h19]
    nocompiler_wstep [hx]
    nocompiler_wstep [hx]
    nocompiler_wstep [hx]
    have hKn : min (frAvail s.mem f) n.toNat ≤ n.toNat := Nat.min_le_right _ _
    have hKa : min (frAvail s.mem f) n.toNat ≤ frAvail s.mem f := Nat.min_le_left _ _
    have hKt : (BitVec.ofNat 64 (min (frAvail s.mem f) n.toNat)).toNat = min (frAvail s.mem f) n.toNat := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hKl]
    have hUw : (Region.mk (read64 s.mem (f + 8#64)) (min (frAvail s.mem f) n.toNat)).within
        ⟨read64 s.mem (f + 88#64), (read64 s.mem (f + 96#64)).toNat⟩ := by
      simp only [Region.within] at hW ⊢; omega
    have hBw : (Region.mk dest (min (frAvail s.mem f) n.toNat)).within ⟨dest, n.toNat⟩ := by
      simp only [Region.within]; simp; omega
    refine VerifiedProc.call hM (dest, read64 s.mem (f + 8#64), BitVec.ofNat 64 (min (frAvail s.mem f) n.toNat))
      ⟨?_, ?_, ?_, ?_, ?_⟩ ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ (Dom.sub_of_ranges (by decide)) ?_
    · simp only [nocompiler_state]
    · simp only [nocompiler_state]; exact hx
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.ra] <;> decide
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.ra] <;> decide
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.sp, h2]; exact sr_al64 hsp
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state, h11]
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
    · rw [hKt]
      exact Perm.canRead_of_canWrite (hle.write _ _ (.inr ⟨_, by simp [freadPerm],
        Region.covers_of_within (by simp [Region.covers]) hUw⟩))
    · rw [hKt]
      exact hle.write _ _ (.inr ⟨_, by simp [freadPerm], Region.covers_of_within (by simp [Region.covers]) hBw⟩)
    · rw [hKt]
      rcases Nat.eq_zero_or_pos (min (frAvail s.mem f) n.toNat) with h0 | h0
      · rw [h0]; simp [Region.Disjoint]
      · exact disj_mono dBU hBw hUw h0 h0
    rintro ⟨y, ky⟩ (⟨hxy, hpcy, hpresy, hky, htry, ha0y, hrby, hfry⟩ | ⟨_, hex⟩)
    rotate_left
    · exact hex.elim
    simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.ra, hKt] at hxy hpcy hpresy hky htry ha0y hrby hfry
    rw [hky]
    have hyr : ∀ q ∈ preservedRegs, q ≠ 21 → y.reg q = P.reg q := by
      intro q hq h21'; rw [hpresy q hq]
      obtain ⟨a1, a10, a12⟩ := (show ∀ q ∈ preservedRegs, q ≠ 1 ∧ q ≠ 10 ∧ q ≠ 12 by decide) q hq
      repeat (first | rw [State.setPc_reg] | rw [State.reg_setReg_other _ _ _ _ a1] | rw [State.reg_setReg_other _ _ _ _ a10] | rw [State.reg_setReg_other _ _ _ _ a12] | rw [State.reg_setReg_other _ _ _ _ h21'])
    have hy21 : y.reg 21 = BitVec.ofNat 64 (min (frAvail s.mem f) n.toNat) := by
      rw [hpresy 21 (by decide)]; simp (disch := nocompiler_decide_closed) only [nocompiler_state]
    have hy8 : y.reg 8 = f := by rw [hyr 8 (by decide) (by decide), h8]
    have hy19 : y.reg 19 = dest := by rw [hyr 19 (by decide) (by decide), h19]
    have hy22 : y.reg 22 = n := by rw [hyr 22 (by decide) (by decide), h22]
    have hyxx : y.exit = none := hxy
    have hpcy' : y.pc = 0x11b8c#64 := hpcy
    have hm8 : read64 y.mem (f + 8#64) = read64 s.mem (f + 8#64) := by
      apply read64_congr_on; intro j hj
      have hin := file_mem f 8 j (by omega)
      rw [hfry _ (fun h => not_mem_of_mem_disj dBF hin (mem_sub_of _ hKn h)),
        hm _ (not_mem_of_mem_disj dFS.symm hin) (field_byte_out f 8 j 136 4 (by omega))]
    have wF : ∀ o len, o + len ≤ 144 → k.perm.canWrite (f + BitVec.ofNat 64 o) len := fun o len h =>
      hle.write _ _ (.inr ⟨⟨f, 144⟩, by simp [freadPerm], covers_field f o len h⟩)
    nocompiler_wstep [hyxx, hpcy', hy8, sw_alF hal 8 rfl, hm8]
    refine ⟨Perm.canRead_of_canWrite (wF 8 8 (by omega)), ?_⟩
    nocompiler_wstep [hyxx, hy21]
    nocompiler_wstep [hyxx, hy8, sw_alF hal 8 rfl]
    refine ⟨wF 8 8 (by omega), ?_⟩
    nocompiler_wstep [hyxx, hy19, hy21]
    nocompiler_wstep [hyxx, hy22, hy21]
    generalize hKdef : min (frAvail s.mem f) n.toNat = K at *
    have hMs : ∀ p, ¬ (Region.mk (s.reg 2 - 144#64) 144).mem p → ¬ (Region.mk (f + 136#64) 4).mem p →
        ¬ (Region.mk (f + 8#64) 16).mem p → ¬ (Region.mk dest n.toNat).mem p →
        writeLE y.mem (f + 8#64) (BitVec.toNat (read64 s.mem (f + 8#64) + BitVec.ofNat 64 (K))) 8 p
          = s.mem p := by
      intro p a1 a2 a3 a4
      rw [writeLE_of_not_mem (r := ⟨f + 8#64, 16⟩) (by simp [Region.covers]) a3,
        hfry p (fun h => a4 (mem_sub_of _ hKn h)), hm p a1 a2]
    have hr8 : read64 (writeLE y.mem (f + 8#64) (BitVec.toNat (read64 s.mem (f + 8#64) + BitVec.ofNat 64 (K))) 8)
        (f + 8#64) = read64 s.mem (f + 8#64) + BitVec.ofNat 64 (K) := by
      rw [Auto.read64_writeLE_same']; simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have hr16 : read64 (writeLE y.mem (f + 8#64) (BitVec.toNat (read64 s.mem (f + 8#64) + BitVec.ofNat 64 (K))) 8)
        (f + 16#64) = read64 s.mem (f + 16#64) := by
      rw [Auto.read64_writeLE_of_disjoint (R := ⟨f + 8#64, 8⟩) (field_disj f 8 16) _ _ _ _ (by simp [Region.covers])]
      apply read64_congr_on; intro j hj
      have hin := file_mem f 16 j (by omega)
      rw [hfry _ (fun h => not_mem_of_mem_disj dBF hin (mem_sub_of _ hKn h)),
        hm _ (not_mem_of_mem_disj dFS.symm hin) (field_byte_out f 16 j 136 4 (by omega))]
    have hav' : frAvail (writeLE y.mem (f + 8#64) (BitVec.toNat (read64 s.mem (f + 8#64) + BitVec.ofNat 64 (K))) 8) f
        = frAvail s.mem f - K := by
      unfold frAvail; rw [hr8, hr16]; exact avail_sub _ _ _ hKa
    have hbufM : ∀ j, j < frAvail s.mem f →
        writeLE y.mem (f + 8#64) (BitVec.toNat (read64 s.mem (f + 8#64) + BitVec.ofNat 64 (K))) 8
          (read64 s.mem (f + 8#64) + BitVec.ofNat 64 j) = s.mem (read64 s.mem (f + 8#64) + BitVec.ofNat 64 j) := by
      intro j hj
      have hin : (Region.mk (read64 s.mem (f + 88#64)) (read64 s.mem (f + 96#64)).toNat).mem
          (read64 s.mem (f + 8#64) + BitVec.ofNat 64 j) := mem_of_within hW j hj
      have hnF := not_mem_of_mem_disj dUF.symm hin
      exact hMs _ (not_mem_of_mem_disj dUS.symm hin) (not_in_F_sub hnF 136 4 (by omega)) (not_in_F_sub hnF 8 16 (by omega))
        (not_mem_of_mem_disj dBU hin)
    have hdestM : readBytes (writeLE y.mem (f + 8#64) (BitVec.toNat (read64 s.mem (f + 8#64) + BitVec.ofNat 64 (K))) 8)
        dest (K) = (frBuffered s.mem f).take (K) := by
      rw [readBytes_congr (m' := y.mem) (fun j hj => writeLE_of_not_mem (r := ⟨f + 8#64, 16⟩) (by simp [Region.covers])
        (not_in_F_sub (not_mem_of_mem_disj dBF.symm (dest_in j (by omega))) 8 16 (by omega))), hrby]
      unfold frBuffered
      rw [readBytes_take' _ _ _ _ hKa]
      apply readBytes_congr; intro j hj
      have hin := mem_of_within hW j (by omega)
      have hnF := not_mem_of_mem_disj dUF.symm hin
      exact hm _ (not_mem_of_mem_disj dUS.symm hin) (not_in_F_sub hnF 136 4 (by omega))
    have hbufR : frBuffered (writeLE y.mem (f + 8#64) (BitVec.toNat (read64 s.mem (f + 8#64) + BitVec.ofNat 64 (K))) 8) f
        = (frBuffered s.mem f).drop (K) := by
      unfold frBuffered
      rw [drop_readBytes _ _ _ _ hKa, ← hav', hr8]
      rw [hav']
      apply readBytes_congr; intro j hj
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact hbufM _ (by omega)
    have hflM := fr_flags hD hMs
    have hSM := fr_agreeF hD hS hMs (by
      rw [hav']
      rcases Nat.eq_zero_or_pos (frAvail s.mem f - K) with h0 | h0
      · exact .inl h0
      · right; rw [hr8]; exact within_shift hW _ hKa)
    by_cases hKe : K = n.toNat
    · have hb3 : (n - BitVec.ofNat 64 (K) == 0) = true := by
        rw [hKe, BitVec.ofNat_toNat, BitVec.setWidth_eq]; simp
      nocompiler_wstep [hyxx, hb3]
      refine fr_exit_full dest n f s k he hpre _ (by simp only [nocompiler_state]) ?_ [] ?_ ?_ k
        (by simp only [nocompiler_state]; exact FrK_init hflM)
      · refine FrCommon_mod' hC _ (by simp only [nocompiler_state]; rw [hxy, hx]) (fun o h1 h3 => ?_) (fun r hr => ?_)
        · simp only [nocompiler_state]; apply read64_congr_on; intro j hj
          have hin := slot_in144 (s.reg 2) o j hj h1 h3
          rw [writeLE_of_not_mem (r := ⟨f + 8#64, 16⟩) (by simp [Region.covers])
            (not_in_F_sub (not_mem_of_mem_disj dFS hin) 8 16 (by omega)),
            hfry _ (fun h => not_mem_of_mem_disj dBS hin (mem_sub_of _ hKn h))]
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          all_goals (simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact hyr _ (by decide) (by decide))
      · simp only [nocompiler_state]; rw [htry, htr]; simp
      · simp only [nocompiler_state]
        refine ⟨hSM.1, hSM.2, Nat.le_refl _, ?_, ?_, fun h => absurd h (Nat.lt_irrefl _)⟩
        · rw [← hKe, hdestM]; simp [frStream]
        · rw [hbufR, hKe]; simp [frStream]
    · have hKa' : K = frAvail s.mem f := by omega
      have hKlt : K < n.toNat := by omega
      have hsubK : n - BitVec.ofNat 64 K = BitVec.ofNat 64 (n.toNat - K) := by
        apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hKl]; omega
      have hb3 : (n - BitVec.ofNat 64 K == 0) = false := by
        rw [hsubK]; simpa using ofNat_ne_zero' (n.toNat - K) (by omega) (by omega)
      nocompiler_wstep [hyxx, hb3]
      refine fr_loop dest n f s k he hpre _ ⟨K, n.toNat - K, [], by simp only [nocompiler_state]; exact FrK_init hflM,
        by simp only [nocompiler_state],
        ⟨?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_, ?_⟩⟩
      · refine FrCommon_mod' hC _ (by simp only [nocompiler_state]; rw [hxy, hx]) (fun o h1 h3 => ?_) (fun r hr => ?_)
        · simp only [nocompiler_state]; apply read64_congr_on; intro j hj
          have hin := slot_in144 (s.reg 2) o j hj h1 h3
          rw [writeLE_of_not_mem (r := ⟨f + 8#64, 16⟩) (by simp [Region.covers])
            (not_in_F_sub (not_mem_of_mem_disj dFS hin) 8 16 (by omega)),
            hfry _ (fun h => not_mem_of_mem_disj dBS hin (mem_sub_of _ hKn h))]
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          all_goals (simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact hyr _ (by decide) (by decide))
      · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
      · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact hsubK
      · simp only [nocompiler_state]; rw [htry, htr]; simp
      · simp only [nocompiler_state]; exact hSM.1
      · simp only [nocompiler_state]; exact hSM.2
      · simp only [nocompiler_state]; rw [hav']; omega
      · simp only [nocompiler_state]; rw [hdestM, List.take_of_length_le (by simp [frBuffered, Auto.readBytes_length]; omega)]
        simp [frStream]

theorem fr_slot_after_field {f sp : Word} (hFS : (Region.mk f 144).Disjoint ⟨sp - 144#64, 144⟩) (a n o : Nat)
    (h : decide (a + n ≤ 144) && decide (8 ≤ o) && decide (o ≤ 144) && decide (0 < n) = true)
    (m : Word → Byte) (v : Nat) :
    read64 (writeLE m (f + BitVec.ofNat 64 a) v n) (sp - BitVec.ofNat 64 o) = read64 m (sp - BitVec.ofNat 64 o) := by
  exact Lib.read64_slot_after_field hFS a n o (by simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h ⊢; omega) m v

theorem fr_entry (dest n f : Word) (s : State) (k : Kern) (he : Entry freadD fread_entry s)
    (hpre : freadP.pre (dest, n, f) s k) (hM : VerifiedProc img memcpy_dom 0x125dc#64 memcpySpec) : PReachK img freadD (FrQ dest n f s k) (s, k) := by
  have hpc := he.pc
  have hx := he.live
  have hsp := he.sp
  simp only [fread_entry] at hpc
  simp only [Reg.sp] at hsp
  have hpre' := hpre
  obtain ⟨ha0, ha1, ha2, ha3, hal, hale, hS, hB, hfdn, hle, hD⟩ := hpre'
  have hD' := hD
  obtain ⟨dFS, dES, dEF, dBS, dBE, dBF, dUS, dUE, dUF, dBU⟩ := hD'
  have dFS' : (Region.mk f 144).Disjoint ⟨s.reg 2 - 144#64, 144⟩ := dFS
  have wF : ∀ o len, o + len ≤ 144 → k.perm.canWrite (f + BitVec.ofNat 64 o) len := fun o len h =>
    hle.write _ _ (.inr ⟨⟨f, 144⟩, by simp [freadPerm], covers_field f o len h⟩)
  have wS : ∀ o, 8 ≤ o → o ≤ 144 → k.perm.canWrite (s.reg 2 - BitVec.ofNat 64 o) 8 := fun o h1 h3 =>
    hle.write _ _ (.inr ⟨⟨s.reg 2 - 144#64, 144⟩, by simp [freadPerm], by simp only [Region.covers]; bv_omega⟩)
  have alF : ∀ o, o % 8 = 0 → aligned (f + BitVec.ofNat 64 o) 8 := fun o h => sw_alF hal o h
  have alF4 : ∀ o, o % 4 = 0 → aligned (f + BitVec.ofNat 64 o) 4 := by intro o h; unfold aligned at *; bv_omega
  have eS : ∀ o, o ≤ 64 → s.reg 2 - 64#64 + BitVec.ofNat 64 o = s.reg 2 - BitVec.ofNat 64 (64 - o) := by
    intro o ho; bv_omega
  have e64 : s.reg 2 + 18446744073709551552#64 = s.reg 2 - 64#64 := by bv_omega
  have fs := fr_field_after_slot dFS'
  have fs64 := fr_field_after_slot64 dFS'
  nocompiler_wstep [hx, hpc, e64]
  nocompiler_wstep [hx, eS 56 (by omega), sw_alS hsp 8 rfl]
  refine ⟨wS 8 (by omega) (by omega), ?_⟩
  nocompiler_wstep [hx, eS 48 (by omega), sw_alS hsp 16 rfl]
  refine ⟨wS 16 (by omega) (by omega), ?_⟩
  nocompiler_wstep [hx, eS 40 (by omega), sw_alS hsp 24 rfl]
  refine ⟨wS 24 (by omega) (by omega), ?_⟩
  nocompiler_wstep [hx, eS 32 (by omega), sw_alS hsp 32 rfl]
  refine ⟨wS 32 (by omega) (by omega), ?_⟩
  nocompiler_wstep [hx, eS 24 (by omega), sw_alS hsp 40 rfl]
  refine ⟨wS 40 (by omega) (by omega), ?_⟩
  nocompiler_wstep [hx, eS 16 (by omega), sw_alS hsp 48 rfl]
  refine ⟨wS 48 (by omega) (by omega), ?_⟩
  nocompiler_wstep [hx, eS 8 (by omega), sw_alS hsp 56 rfl]
  refine ⟨wS 56 (by omega) (by omega), ?_⟩
  nocompiler_wstep [hx, BitVec.add_zero, sw_alS hsp 64 rfl]
  refine ⟨wS 64 (by omega) (by omega), ?_⟩
  nocompiler_wstep [hx]
  nocompiler_wstep [hx]
  nocompiler_wstep [hx]
  nocompiler_wstep [hx]
  nocompiler_wstep [hx]
  have hb1 : (s.reg 11 == 0) = false := by rw [ha1]; rfl
  nocompiler_wstep [hx, hb1]
  nocompiler_wstep [hx]
  nocompiler_wstep [hx, ha3, alF4 140 rfl, fs]
  refine ⟨Perm.canRead_of_canWrite (wF 140 4 (by omega)), ?_⟩
  have hlk' : BitVec.slt (BitVec.signExtend 64 (BitVec.ofNat 32 (readLE s.mem (f + 140#64) 4))) 0 = true :=
    lock_neg _ hS.2.2.2.2.1 (readLE_lt' _ _ 4)
  nocompiler_wstep [hx, hlk']
  nocompiler_wstep [hx]
  nocompiler_wstep [hx, alF4 136 rfl, fs]
  refine ⟨Perm.canRead_of_canWrite (wF 136 4 (by omega)), ?_⟩
  nocompiler_wstep [hx, alF 8 rfl, fs64]
  refine ⟨Perm.canRead_of_canWrite (wF 8 8 (by omega)), ?_⟩
  nocompiler_wstep [hx, alF 16 rfl, fs64]
  refine ⟨Perm.canRead_of_canWrite (wF 16 8 (by omega)), ?_⟩
  nocompiler_wstep [hx]
  nocompiler_wstep [hx]
  nocompiler_wstep [hx, alF4 136 rfl]
  refine ⟨wF 136 4 (by omega), ?_⟩
  nocompiler_wstep [hx, ha1, ha2, BitVec.mul_one]
  have hm1 : n * 1 = n := BitVec.mul_one n
  have hmw : ∀ p, ¬ (Region.mk (s.reg 2 - 144#64) 144).mem p → ∀ (m : Word → Byte) (o : Nat), 8 ≤ o → o ≤ 144 → ∀ v : Nat,
      writeLE m (s.reg 2 - BitVec.ofNat 64 o) v 8 p = m p := by
    intro p hp m o h1 h3 v
    exact writeLE_of_not_mem (r := ⟨s.reg 2 - 144#64, 144⟩) (by simp only [Region.covers]; bv_omega) hp
  have sfa := fr_slot_after_field dFS'
  refine fr_mid dest n f s k he hpre _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ⟨fun q hq => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ hM
  all_goals try (simp (disch := nocompiler_decide_closed) only [nocompiler_state, slot_ne, fw_slot_same, ha0, ha1, ha2, ha3, hm1, sr_slot_after_base]; done)
  all_goals first
    | (simp only [nocompiler_state]; exact hx)
    | (have hq' : q ≠ 2 ∧ q ≠ 8 ∧ q ≠ 9 ∧ q ≠ 10 ∧ q ≠ 11 ∧ q ≠ 12 ∧ q ≠ 13 ∧ q ≠ 18 ∧ q ≠ 19 ∧ q ≠ 20 ∧ q ≠ 21 ∧ q ≠ 22 := by
          revert hq; revert q; decide
       obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _⟩ := hq'
       repeat (first | rw [State.setPc_reg] | rw [State.setMem_reg] | rw [State.reg_setReg_other _ _ _ _ (by assumption)]))
    | (simp (disch := nocompiler_decide_closed) only [nocompiler_state, sfa, slot_ne, fw_slot_same]; done)
    | (intro p h1 h2; simp only [nocompiler_state]
       rw [writeLE_of_not_mem (r := ⟨f + 136#64, 4⟩) (by simp [Region.covers]) h2]
       repeat rw [hmw p h1 _ _ (by omega) (by omega)])

/-- `fread(dest, 1, n, f)` (musl src/stdio/fread.c) on slen's stdin, at the process level, by hand, over
    memcpy's specification (memcpy's proof is a separate item). Its region includes `__stdio_read`, the
    function slen's `f->read` points to (`StdinFile`). -/
theorem fread_verified (hM : VerifiedProc img memcpy_dom 0x125dc#64 memcpySpec) :
    VerifiedProc img freadD fread_entry freadP := by
  rintro ⟨dest, n, f⟩ s k he hpre
  exact fr_entry dest n f s k he hpre hM

end NoCompiler.Libc.Musl.Fread
