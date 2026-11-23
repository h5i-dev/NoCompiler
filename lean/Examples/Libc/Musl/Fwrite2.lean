import Examples.Libc.Musl.Fwrite1

set_option maxRecDepth 20000
namespace NoCompiler.Libc.Musl.Fwrite
open NoCompiler NoCompiler.Linux NoCompiler.Libc NoCompiler.Libc.Musl NoCompiler.Libc.Musl.StdioWrite NoCompiler.Libc.Musl.Memcpy NoCompiler.Libc.Musl.Towrite NoCompiler.Libc.Musl.StdoutWrite NoCompiler.Libc.Musl.Fwritex NoCompiler.Libc.Musl.Fwrite NoCompiler.Libc.Musl.FwriteImg

theorem fr_field_after_slot {f sp : Word} (hFS : (Region.mk f 144).Disjoint ⟨sp - 144#64, 144⟩) (a b n : Nat)
    (h : decide (8 ≤ a) && decide (a ≤ 144) && decide (b + n ≤ 144) && decide (0 < n) = true)
    (m : Word → Byte) (v : Nat) :
    readLE (writeLE m (sp - BitVec.ofNat 64 a) v 8) (f + BitVec.ofNat 64 b) n = readLE m (f + BitVec.ofNat 64 b) n := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact readLE_writeLE_disj (R := ⟨sp - BitVec.ofNat 64 a, 8⟩) (by simp only [Region.Disjoint] at *; bv_omega)
    _ _ _ _ (by simp [Region.covers])



def fwriteD : Dom := fwrite_dom ++ __stdout_write_dom

/-- `fwrite(src, 1, n, f)` for slen's output line: `f` unlocked (lock < 0) and as `fwxStdoutP` asks;
    the result and effects are `__fwritex`'s, with the stack 64 bytes deeper. -/
def fwriteStdoutP : SpecP (Word × Word × Word) where
  pre := fun ⟨src, n, f⟩ s k =>
    s.reg 10 = src ∧ s.reg 11 = 1 ∧ s.reg 12 = n ∧ s.reg 13 = f ∧ aligned f 8 ∧
    aligned (s.reg 4 + 18446744073709551452#64) 4 ∧ 2 ^ 31 ≤ readLE s.mem (f + 140#64) 4 ∧
    read64 s.mem (f + 32#64) = 0 ∧ read32 s.mem f &&& 8#64 = 0 ∧ read64 s.mem (f + 72#64) = 0x1240c#64 ∧
    n.toNat ≤ (read64 s.mem (f + 96#64)).toNat ∧ readLE s.mem (f + 144#64) 4 < 2 ^ 31 ∧
    0 < n.toNat ∧ n.toNat < 2 ^ 62 ∧ s.mem (src + BitVec.ofNat 64 (n.toNat - 1)) = 10#8 ∧
    (Perm.mk [⟨src, n.toNat⟩] [⟨f, 152⟩, ⟨s.reg 2 - 256#64, 256⟩, ⟨s.reg 4 + 18446744073709551452#64, 4⟩]).le k.perm ∧
    (Region.mk f 152).Disjoint ⟨s.reg 2 - 256#64, 256⟩ ∧
    (Region.mk (s.reg 4 + 18446744073709551452#64) 4).Disjoint ⟨s.reg 2 - 256#64, 256⟩ ∧
    (Region.mk (s.reg 4 + 18446744073709551452#64) 4).Disjoint ⟨f, 152⟩ ∧
    (Region.mk src n.toNat).Disjoint ⟨s.reg 2 - 256#64, 256⟩ ∧
    (Region.mk src n.toNat).Disjoint ⟨s.reg 4 + 18446744073709551452#64, 4⟩ ∧
    (Region.mk src n.toNat).Disjoint ⟨f, 152⟩ ∧
    (Region.mk (read64 s.mem (f + 88#64)) (read64 s.mem (f + 96#64)).toNat).Disjoint ⟨s.reg 2 - 256#64, 256⟩ ∧
    (Region.mk (read64 s.mem (f + 88#64)) (read64 s.mem (f + 96#64)).toNat).Disjoint ⟨s.reg 4 + 18446744073709551452#64, 4⟩ ∧
    (Region.mk (read64 s.mem (f + 88#64)) (read64 s.mem (f + 96#64)).toNat).Disjoint ⟨f, 152⟩ ∧
    (Region.mk 0#64 1).Disjoint ⟨s.reg 2 - 256#64, 256⟩ ∧ (Region.mk 0#64 1).Disjoint ⟨f, 152⟩ ∧
    (fdOf s.mem f).toNat < 2 ^ 31
  post := fun ⟨src, n, f⟩ x y =>
    y.2 = x.2 ∧
    (∀ p, ¬ (Region.mk f 152).mem p → ¬ (Region.mk (x.1.reg 2 - 256#64) 256).mem p →
      ¬ (Region.mk (x.1.reg 4 + 18446744073709551452#64) 4).mem p → y.1.mem p = x.1.mem p) ∧
    read64 y.1.mem (f + 40#64) = read64 y.1.mem (f + 56#64) ∧ read64 y.1.mem (f + 8#64) = read64 y.1.mem (f + 16#64) ∧
    readLE y.1.mem (f + 140#64) 4 = readLE x.1.mem (f + 140#64) 4 ∧
    ∃ evs, y.1.trace = x.1.trace ++ evs ∧
      ((WritesOf (fdOf x.1.mem f) evs (readBytes x.1.mem src n.toNat) ∧ y.1.reg 10 = n) ∨
       (∃ m, m < n.toNat ∧ WritesOf (fdOf x.1.mem f) evs ((readBytes x.1.mem src n.toNat).take m) ∧
         y.1.reg 10 = BitVec.ofNat 64 m))

theorem fwr_field {f sp : Word} (h : (Region.mk f 152).Disjoint ⟨sp - 256#64, 256⟩) (o j : Nat) (hj : o + j < 152) :
    ¬ (Region.mk (sp - 64#64) 64).mem (f + BitVec.ofNat 64 o + BitVec.ofNat 64 j) := by
  simp only [Region.Disjoint, Region.mem] at *; bv_omega

theorem fwr_disj256 {a sp : Word} {n : Nat} (h : (Region.mk a n).Disjoint ⟨sp - 256#64, 256⟩) :
    (Region.mk a n).Disjoint ⟨sp - 64#64 - 192#64, 192⟩ := by
  simp only [Region.Disjoint] at *; bv_omega

theorem fwr_slot_out (sp : Word) (o j : Nat) (hj : j < 8) (h1 : 8 ≤ o) (h3 : o ≤ 56) :
    ¬ (Region.mk (sp - 64#64 - 192#64) 192).mem (sp - BitVec.ofNat 64 o + BitVec.ofNat 64 j) := by
  simp only [Region.mem]; bv_omega

theorem fwr_n192 {sp p : Word} (h : ¬ (Region.mk (sp - 256#64) 256).mem p) : ¬ (Region.mk (sp - 64#64 - 192#64) 192).mem p := by
  simp only [Region.mem] at *; bv_omega
theorem fwr_n64 {sp p : Word} (h : ¬ (Region.mk (sp - 256#64) 256).mem p) : ¬ (Region.mk (sp - 64#64) 64).mem p := by
  simp only [Region.mem] at *; bv_omega

/-- `fwrite`'s postcondition from `__fwritex`'s, at the call state `Z` (memory as at entry outside the frame). -/
theorem fwr_post (src n f : Word) (s : State) (k : Kern) (hpre : fwriteStdoutP.pre (src, n, f) s k) (Z y : State)
    (hfr : ∀ p, ¬ (Region.mk f 152).mem p → ¬ (Region.mk (s.reg 2 - 64#64 - 192#64) 192).mem p →
      ¬ (Region.mk (s.reg 4 + 18446744073709551452#64) 4).mem p → y.mem p = Z.mem p)
    (h40 : read64 y.mem (f + 40#64) = read64 y.mem (f + 56#64)) (h8 : read64 y.mem (f + 8#64) = read64 y.mem (f + 16#64))
    (hL : readLE y.mem (f + 140#64) 4 = readLE Z.mem (f + 140#64) 4) (evs : List Event) (htr : y.trace = s.trace ++ evs)
    (hres : (WritesOf (fdOf Z.mem f) evs (readBytes Z.mem src n.toNat) ∧ y.reg 10 = n) ∨
       (∃ m, m < n.toNat ∧ WritesOf (fdOf Z.mem f) evs ((readBytes Z.mem src n.toNat).take m) ∧ y.reg 10 = BitVec.ofNat 64 m))
    (hZm : ∀ p, ¬ (Region.mk (s.reg 2 - 64#64) 64).mem p → Z.mem p = s.mem p) :
    fwriteStdoutP.post (src, n, f) (s, k) (y, k) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, dFS, -, -, dCS, -⟩ := hpre
  have hfd : fdOf Z.mem f = fdOf s.mem f := by
    unfold fdOf
    rw [readLE_congr (m' := s.mem) (fun j hj => hZm _ (fwr_field dFS 120 j (by omega)))]
  have hrb : readBytes Z.mem src n.toNat = readBytes s.mem src n.toNat := by
    apply readBytes_congr; intro j hj
    exact hZm _ (fun h => Auto.not_mem_of_disjoint (R := ⟨s.reg 2 - 256#64, 256⟩) dCS.symm hj
      (by simp only [Region.mem] at h ⊢; bv_omega))
  rw [hfd, hrb] at hres
  have hL' : readLE y.mem (f + 140#64) 4 = readLE s.mem (f + 140#64) 4 := by
    rw [hL]; exact readLE_congr (fun j hj => hZm _ (fwr_field dFS 140 j (by omega)))
  exact ⟨rfl, fun p a b c => by rw [hfr p a (fwr_n192 b) c, hZm p (fwr_n64 b)], h40, h8, hL', evs, htr, hres⟩

theorem fwr_post_congr {src n f : Word} {s : State} {k : Kern} {y y' : State}
    (h : fwriteStdoutP.post (src, n, f) (s, k) (y, k)) (hm : y'.mem = y.mem) (ht : y'.trace = y.trace)
    (h10 : y'.reg 10 = y.reg 10) : fwriteStdoutP.post (src, n, f) (s, k) (y', k) := by
  obtain ⟨a1, a2, a3, a4, aL, evs, a5, a6⟩ := h
  exact ⟨a1, fun p b c d => by rw [hm]; exact a2 p b c d, by rw [hm]; exact a3, by rw [hm]; exact a4, by rw [hm]; exact aL, evs,
    by rw [ht]; exact a5, by rw [h10]; exact a6⟩

/-- `__fwritex`'s precondition at `fwrite`'s call, from `fwrite`'s and memory as at entry outside its frame. -/
theorem fwr_pre (src n f : Word) (s : State) (k : Kern) (hpre : fwriteStdoutP.pre (src, n, f) s k) (z : State)
    (h10 : z.reg 10 = src) (h11 : z.reg 11 = n) (h12 : z.reg 12 = f) (h2 : z.reg 2 = s.reg 2 - 64#64)
    (h4 : z.reg 4 = s.reg 4) (hm : ∀ p, ¬ (Region.mk (s.reg 2 - 64#64) 64).mem p → z.mem p = s.mem p) :
    fwxStdoutP.pre (src, n, f) z k := by
  obtain ⟨-, -, -, -, hal, hale, -, hwend, hnowr, hw72, hfit, hlbf, hl0, hl62, hnl, hle,
    dFS, dES, dEF, dCS, dCE, dCF, dUS, dUE, dUF, d0S, d0F, hfdW⟩ := hpre
  have hF : ∀ o len, o + len ≤ 152 → readLE z.mem (f + BitVec.ofNat 64 o) len = readLE s.mem (f + BitVec.ofNat 64 o) len := by
    intro o len h; apply readLE_congr; intro j hj; exact hm _ (fwr_field dFS o j (by omega))
  have r64 : ∀ o, o + 8 ≤ 152 → read64 z.mem (f + BitVec.ofNat 64 o) = read64 s.mem (f + BitVec.ofNat 64 o) := by
    intro o h; unfold read64; rw [hF o 8 h]
  have z88 : read64 z.mem (f + 88#64) = read64 s.mem (f + 88#64) := r64 88 (by omega)
  have z96 : read64 z.mem (f + 96#64) = read64 s.mem (f + 96#64) := r64 96 (by omega)
  have hfdZ : (fdOf z.mem f).toNat < 2 ^ 31 := by unfold fdOf at hfdW ⊢; rw [hF 120 4 (by omega)]; exact hfdW
  refine ⟨h10, h11, h12, hal, by rw [h4]; exact hale, ?_, ?_, ?_, ?_, ?_, hl0, hl62, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfdZ⟩
  · have : read64 z.mem (f + 32#64) = read64 s.mem (f + 32#64) := r64 32 (by omega)
    rw [this]; exact hwend
  · have := hF 0 4 (by omega); simp only [BitVec.add_zero] at this; unfold read32; rw [this]; exact hnowr
  · have : read64 z.mem (f + 72#64) = read64 s.mem (f + 72#64) := r64 72 (by omega)
    rw [this]; exact hw72
  · rw [z96]; exact hfit
  · have : readLE z.mem (f + 144#64) 4 = readLE s.mem (f + 144#64) 4 := hF 144 4 (by omega)
    rw [this]; exact hlbf
  · rw [hm _ (fun h => Auto.not_mem_of_disjoint (R := ⟨s.reg 2 - 256#64, 256⟩) dCS.symm (by omega : n.toNat - 1 < n.toNat)
      (by simp only [Region.mem] at h ⊢; bv_omega))]; exact hnl
  · rw [h2, h4, show s.reg 2 - 64#64 - 192#64 = s.reg 2 - 256#64 by bv_omega]
    refine Perm.le_trans (Perm.le_of (fun r hr => ⟨r, by simp at hr ⊢; exact .inl hr, Region.within_refl _⟩) ?_) hle
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, by simp, Region.within_refl _⟩
    · exact ⟨⟨s.reg 2 - 256#64, 256⟩, by simp, by simp only [Region.within]; bv_omega⟩
    · exact ⟨_, by simp, Region.within_refl _⟩
  all_goals (try rw [h2]); (try rw [h4]); (try rw [z88]); (try rw [z96])
  · exact fwr_disj256 dFS
  · exact fwr_disj256 dES
  · exact dEF
  · exact fwr_disj256 dCS
  · exact dCE
  · exact dCF
  · exact fwr_disj256 dUS
  · exact dUE
  · exact dUF
  · exact fwr_disj256 d0S
  · exact d0F

theorem fwrite_stdout_verified (hM : VerifiedProc img memcpy_dom 0x125dc#64 memcpySpec) :
    VerifiedProc img fwriteD fwrite_entry fwriteStdoutP := by
  rintro ⟨src, n, f⟩ s k he hpre
  have hpre' := hpre
  obtain ⟨ha0, ha1, ha2, ha3, hal, hale, hlk, hwend, hnowr, hw72, hfit, hlbf, hl0, hl62, hnl, hle,
    dFS, dES, dEF, dCS, dCE, dCF, dUS, dUE, dUF, d0S, d0F, -⟩ := hpre'
  have hpc := he.pc
  have hx := he.live
  have hsp := he.sp
  simp only [fwrite_entry] at hpc
  simp only [Reg.sp] at hsp
  have wS : ∀ o, 8 ≤ o → o ≤ 256 → k.perm.canWrite (s.reg 2 - BitVec.ofNat 64 o) 8 := fun o h1 h3 =>
    hle.write _ _ (.inr ⟨⟨s.reg 2 - 256#64, 256⟩, by simp, by simp only [Region.covers]; bv_omega⟩)
  have eS : ∀ o, o ≤ 64 → s.reg 2 - 64#64 + BitVec.ofNat 64 o = s.reg 2 - BitVec.ofNat 64 (64 - o) := by
    intro o ho; bv_omega
  have e64 : s.reg 2 + 18446744073709551552#64 = s.reg 2 - 64#64 := by bv_omega
  have dFS' : (Region.mk f 144).Disjoint ⟨s.reg 2 - 144#64, 144⟩ := by simp only [Region.Disjoint] at dFS ⊢; bv_omega
  have fs := fr_field_after_slot dFS'
  have hr140 : k.perm.canRead (f + 140#64) 4 := Perm.canRead_of_canWrite
    (hle.write _ _ (.inr ⟨⟨f, 152⟩, by simp, by simp only [Region.covers]; bv_omega⟩))
  have hb1 : (s.reg 11 == 0) = false := by rw [ha1]; rfl
  have al140 : aligned (f + 140#64) 4 := by unfold aligned at *; bv_omega
  have hlk' := lock_neg _ hlk (readLE_lt' _ _ 4)
  nocompiler_run_n 22 [hx, hpc, e64, eS 56 (by omega), sw_alS hsp 8 rfl, eS 48 (by omega), sw_alS hsp 16 rfl, eS 40 (by omega), sw_alS hsp 24 rfl, eS 32 (by omega), sw_alS hsp 32 rfl, eS 24 (by omega), sw_alS hsp 40 rfl, eS 16 (by omega), sw_alS hsp 48 rfl, eS 8 (by omega), sw_alS hsp 56 rfl, hb1, ha3, al140, fs, ha1, ha2, BitVec.mul_one, hlk'] using [wS, hr140, rS]
  have hn1 : n * 1 = n := BitVec.mul_one n
  have hmw : ∀ p, ¬ (Region.mk (s.reg 2 - 64#64) 64).mem p → ∀ (m : Word → Byte) (o : Nat), 8 ≤ o → o ≤ 64 → ∀ v : Nat,
      writeLE m (s.reg 2 - BitVec.ofNat 64 o) v 8 p = m p := by
    intro p hp m o h1 h3 v
    exact writeLE_of_not_mem (r := ⟨s.reg 2 - 64#64, 64⟩) (by simp only [Region.covers]; bv_omega) hp
  refine VerifiedProc.call (__fwritex_stdout_verified hM) (src, n, f) ⟨?_, ?_, ?_, ?_, ?_⟩ ?_ (Dom.sub_of_ranges (by decide)) ?_
  · simp only [nocompiler_state]
  · simp only [nocompiler_state]; exact hx
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.ra] <;> decide
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.ra] <;> decide
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.sp]; exact sr_al64 hsp
  · refine fwr_pre src n f s k hpre _ ?_ ?_ ?_ ?_ ?_ ?_
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state, ha0]
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state, hn1]
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
    · intro p hp; simp only [nocompiler_state]; repeat rw [hmw p hp _ _ (by omega) (by omega)]
  rintro ⟨y, ky⟩ (⟨hxy, hpcy, hpresy, hk, hfr, h40, h8, hL, evs, htr, hres⟩ | ⟨_, hex⟩)
  rotate_left
  · exact hex.elim
  simp only at hxy hpcy hpresy hk hfr h40 h8 hL htr hres
  simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.ra] at hpcy hfr htr
  rw [hk]
  have hra4 := he.retAligned
  have hret := he.ret
  simp only [Reg.ra] at hra4 hret
  have hyr : ∀ q ∈ preservedRegs, y.reg q = s.reg q ∨ q ∈ [(2 : Reg), 8, 9, 18, 19, 20, 21] := by
    intro q hq
    by_cases h : q ∈ [(2 : Reg), 8, 9, 18, 19, 20, 21]
    · exact .inr h
    · left; rw [hpresy q hq]
      have hne : q ≠ 1 ∧ q ≠ 10 ∧ q ≠ 11 ∧ q ≠ 12 ∧ q ≠ 8 ∧ q ≠ 9 ∧ q ≠ 18 ∧ q ≠ 19 ∧ q ≠ 20 ∧ q ≠ 21 ∧ q ≠ 2 := by
        revert h; revert hq; revert q; decide
      obtain ⟨a1, a10, a11, a12, a8, a9, a18, a19, a20, a21, a2⟩ := hne
      repeat (first | rw [State.setPc_reg] | rw [State.setMem_reg] | rw [State.reg_setReg_other _ _ _ _ a2] | rw [State.reg_setReg_other _ _ _ _ a1] | rw [State.reg_setReg_other _ _ _ _ a10] | rw [State.reg_setReg_other _ _ _ _ a11] | rw [State.reg_setReg_other _ _ _ _ a12] | rw [State.reg_setReg_other _ _ _ _ a8] | rw [State.reg_setReg_other _ _ _ _ a9] | rw [State.reg_setReg_other _ _ _ _ a18] | rw [State.reg_setReg_other _ _ _ _ a19] | rw [State.reg_setReg_other _ _ _ _ a20] | rw [State.reg_setReg_other _ _ _ _ a21])
  have hy2 : y.reg 2 = s.reg 2 - 64#64 := by
    rw [hpresy 2 (by decide)]; simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  have hy8 : y.reg 8 = 1 := by rw [hpresy 8 (by decide)]; simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  have hy9 : y.reg 9 = n := by rw [hpresy 9 (by decide)]; simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  have hy18 : y.reg 18 = n := by rw [hpresy 18 (by decide)]; simp (disch := nocompiler_decide_closed) only [nocompiler_state, hn1]
  have hslot : ∀ o, 8 ≤ o → o ≤ 56 → read64 y.mem (s.reg 2 - BitVec.ofNat 64 o) =
      read64 (writeLE (writeLE (writeLE (writeLE (writeLE (writeLE (writeLE s.mem (s.reg 2 - 8#64) (BitVec.toNat (s.reg 1)) 8)
        (s.reg 2 - 16#64) (BitVec.toNat (s.reg 8)) 8) (s.reg 2 - 24#64) (BitVec.toNat (s.reg 9)) 8) (s.reg 2 - 32#64) (BitVec.toNat (s.reg 18)) 8)
        (s.reg 2 - 40#64) (BitVec.toNat (s.reg 19)) 8) (s.reg 2 - 48#64) (BitVec.toNat (s.reg 20)) 8) (s.reg 2 - 56#64) (BitVec.toNat (s.reg 21)) 8)
        (s.reg 2 - BitVec.ofNat 64 o) := by
    intro o h1 h3; apply read64_congr_on; intro j hj
    have hin : (Region.mk (s.reg 2 - 256#64) 256).mem (s.reg 2 - BitVec.ofNat 64 o + BitVec.ofNat 64 j) := by
      simp only [Region.mem]; bv_omega
    rw [hfr _ (not_mem_of_mem_disj dFS hin) (fwr_slot_out _ o j hj h1 h3) (not_mem_of_mem_disj dES hin)]
  have v : ∀ o, o ∈ [8, 16, 24, 32, 40, 48, 56] → read64 y.mem (s.reg 2 - BitVec.ofNat 64 o) =
      (if o = 8 then s.reg 1 else if o = 16 then s.reg 8 else if o = 24 then s.reg 9 else if o = 32 then s.reg 18
        else if o = 40 then s.reg 19 else if o = 48 then s.reg 20 else s.reg 21) := by
    intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      (rw [hslot _ (by omega) (by omega)]; simp (disch := nocompiler_decide_closed) only [slot_ne, fw_slot_same]; rfl)
  have v8 := v 8 (by simp); have v16 := v 16 (by simp); have v24 := v 24 (by simp); have v32 := v 32 (by simp)
  have v40 := v 40 (by simp); have v48 := v 48 (by simp); have v56 := v 56 (by simp)
  simp only [if_true, if_false, show (16 : Nat) ≠ 8 by omega] at v8 v16 v24 v32 v40 v48 v56
  have rS : ∀ o, 8 ≤ o → o ≤ 256 → k.perm.canRead (s.reg 2 - BitVec.ofNat 64 o) 8 := fun o h1 h3 =>
    Perm.canRead_of_canWrite (wS o h1 h3)
  have e64' : s.reg 2 - 64#64 + 64#64 = s.reg 2 := by bv_omega
  have hdiv : ∀ x : Word, rvDivu x 1 = x := fun x => by simp [rvDivu]
  have fin : ∀ u : State, u.pc = 0x121a8#64 → u.exit = none → u.mem = y.mem → u.trace = y.trace → u.reg 9 = y.reg 10 →
      u.reg 2 = s.reg 2 - 64#64 → (∀ q ∈ preservedRegs, q ∉ [(2 : Reg), 8, 9, 18, 19, 20, 21] → u.reg q = s.reg q) →
      PReachK img fwriteD (fun y => Final fwriteD y.1 ∧ fwriteStdoutP.Done (src, n, f) (s, k) y) (u, k) := by
    intro u hpu hxu hmu htu h9u h2u hpru
    nocompiler_wstep [hxu, hpu]
    nocompiler_wstep [hxu, h2u, eS 56 (by omega), sw_alS hsp 8 rfl, hmu, v8]
    refine ⟨rS 8 (by omega) (by omega), ?_⟩
    nocompiler_wstep [hxu, h2u, eS 48 (by omega), sw_alS hsp 16 rfl, hmu, v16]
    refine ⟨rS 16 (by omega) (by omega), ?_⟩
    nocompiler_wstep [hxu, h2u, eS 40 (by omega), sw_alS hsp 24 rfl, hmu, v24]
    refine ⟨rS 24 (by omega) (by omega), ?_⟩
    nocompiler_wstep [hxu, h2u, eS 32 (by omega), sw_alS hsp 32 rfl, hmu, v32]
    refine ⟨rS 32 (by omega) (by omega), ?_⟩
    nocompiler_wstep [hxu, h2u, eS 24 (by omega), sw_alS hsp 40 rfl, hmu, v40]
    refine ⟨rS 40 (by omega) (by omega), ?_⟩
    nocompiler_wstep [hxu, h2u, eS 16 (by omega), sw_alS hsp 48 rfl, hmu, v48]
    refine ⟨rS 48 (by omega) (by omega), ?_⟩
    nocompiler_wstep [hxu, h2u, eS 8 (by omega), sw_alS hsp 56 rfl, hmu, v56]
    refine ⟨rS 56 (by omega) (by omega), ?_⟩
    nocompiler_wstep [hxu, h2u, e64']
    nocompiler_wstep [hxu, ret_mask hra4, hra4]
    refine .done ⟨.inl ?_, .inl ⟨?_, ?_, ?_, ?_⟩⟩
    · simp only [nocompiler_state]; exact hret
    · simp only [nocompiler_state]; exact hxu
    · simp only [nocompiler_state, Reg.ra]
    · intro q hq
      have hq' := hq
      simp only [preservedRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals (simp (disch := nocompiler_decide_closed) only [nocompiler_state])
      all_goals (first | rfl | exact hpru _ hq' (by decide))
    · refine fwr_post_congr (fwr_post src n f s k hpre _ y hfr h40 h8 hL evs htr hres ?_) ?_ ?_ ?_
      · intro p hp; simp only [nocompiler_state]; repeat rw [hmw p hp _ _ (by omega) (by omega)]
      · simp only [nocompiler_state]; exact hmu
      · simp only [nocompiler_state]; exact htu
      · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h9u
  have hpr2 : ∀ q ∈ preservedRegs, q ∉ [(2 : Reg), 8, 9, 18, 19, 20, 21] → y.reg q = s.reg q := by
    intro q hq hn
    rcases hyr q hq with h | h
    · exact h
    · exact absurd h hn
  by_cases heq : y.reg 10 = n
  · have hb : (y.reg 10 != y.reg 18) = false := by rw [heq, hy18]; simp
    nocompiler_run_n 3 [hxy, hpcy, hb] using [wS, hr140, rS]
    refine fin _ (by simp only [nocompiler_state]) (by simp only [nocompiler_state]; exact hxy) (by simp only [nocompiler_state])
      (by simp only [nocompiler_state]) (by simp (disch := nocompiler_decide_closed) only [nocompiler_state]; rw [hy9, heq]) ?_ ?_
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact hy2
    · intro q hq hn
      have h20 : q ≠ 20 := fun h => hn (by subst h; simp)
      simp only [State.setPc_reg]; rw [State.reg_setReg_other _ _ _ _ h20]; exact hpr2 q hq hn
  · have hb : (y.reg 10 != y.reg 18) = true := by rw [hy18]; simpa using heq
    nocompiler_run_n 3 [hxy, hpcy, hb, hy8, hdiv] using [wS, hr140, rS]
    refine fin _ (by simp only [nocompiler_state]) (by simp only [nocompiler_state]; exact hxy) (by simp only [nocompiler_state])
      (by simp only [nocompiler_state]) (by simp (disch := nocompiler_decide_closed) only [nocompiler_state]) ?_ ?_
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact hy2
    · intro q hq hn
      have h20 : q ≠ 20 := fun h => hn (by subst h; simp)
      have h9 : q ≠ 9 := fun h => hn (by subst h; simp)
      simp only [State.setPc_reg]
      rw [State.reg_setReg_other _ _ _ _ h9, State.setPc_reg, State.reg_setReg_other _ _ _ _ h20]; exact hpr2 q hq hn

end NoCompiler.Libc.Musl.Fwrite
