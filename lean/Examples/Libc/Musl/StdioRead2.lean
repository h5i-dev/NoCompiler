import Examples.Libc.Musl.StdioRead1

set_option maxRecDepth 20000
namespace NoCompiler.Libc.Musl.StdioRead
open NoCompiler NoCompiler.Linux NoCompiler.Libc NoCompiler.Libc.Musl NoCompiler.Libc.Musl.StdioWrite NoCompiler.Libc.Musl.Toread NoCompiler.Libc.Musl.StdioRead NoCompiler.Libc.Musl.StdioReadImg NoCompiler.Libc.Musl.SyscallRet

/-- `__stdio_read`'s epilogue (0x123e4): a0 = s1, the saved registers reloaded, back to ra. -/
theorem sr_epi (s : State) (k : Kern) (he : Entry dom __stdio_read_entry s)
    (hle : (Perm.mk [] [⟨s.reg 2 - 80#64, 80⟩]).le k.perm)
    (u : State) (hpc : u.pc = 0x123e4#64) (hx : u.exit = none) (h2 : u.reg 2 = s.reg 2 - 64#64)
    (hpr : ∀ q ∈ preservedRegs, q ≠ 2 → q ≠ 8 → q ≠ 9 → q ≠ 18 → u.reg q = s.reg q)
    (s1 : read64 u.mem (s.reg 2 - 8#64) = s.reg 1) (s2 : read64 u.mem (s.reg 2 - 16#64) = s.reg 8)
    (s3 : read64 u.mem (s.reg 2 - 24#64) = s.reg 9) (s4 : read64 u.mem (s.reg 2 - 32#64) = s.reg 18) :
    PReachK img dom (fun y => Final dom y.1 ∧ y.1.exit = none ∧ y.1.pc = s.reg 1 ∧
      Preserved s y.1 ∧ y.2 = k ∧ y.1.trace = u.trace ∧ y.1.reg 10 = u.reg 9 ∧ y.1.mem = u.mem) (u, k) := by
  have hsp := he.sp
  have hra4 := he.retAligned
  have hret := he.ret
  simp only [Reg.sp, Reg.ra] at hsp hra4 hret
  have rS : ∀ o, 8 ≤ o → o ≤ 80 → k.perm.canRead (s.reg 2 - BitVec.ofNat 64 o) 8 := fun o h1 h3 =>
    Perm.canRead_of_canWrite (hle.write _ _ (.inr ⟨⟨s.reg 2 - 80#64, 80⟩, by simp, by simp only [Region.covers]; bv_omega⟩))
  have eS : ∀ o, o ≤ 64 → s.reg 2 - 64#64 + BitVec.ofNat 64 o = s.reg 2 - BitVec.ofNat 64 (64 - o) := by
    intro o ho; bv_omega
  have e64 : s.reg 2 - 64#64 + 64#64 = s.reg 2 := by bv_omega
  nocompiler_wstep [hx, hpc]
  nocompiler_wstep [hx, h2, eS 56 (by omega), sw_alS hsp 8 rfl, s1]
  refine ⟨rS 8 (by omega) (by omega), ?_⟩
  nocompiler_wstep [hx, h2, eS 48 (by omega), sw_alS hsp 16 rfl, s2]
  refine ⟨rS 16 (by omega) (by omega), ?_⟩
  nocompiler_wstep [hx, h2, eS 40 (by omega), sw_alS hsp 24 rfl, s3]
  refine ⟨rS 24 (by omega) (by omega), ?_⟩
  nocompiler_wstep [hx, h2, eS 32 (by omega), sw_alS hsp 32 rfl, s4]
  refine ⟨rS 32 (by omega) (by omega), ?_⟩
  nocompiler_wstep [hx, h2, e64]
  nocompiler_wstep [hx, ret_mask hra4, hra4]
  refine .done ⟨.inl ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_⟩
  · simp only [nocompiler_state]; exact hret
  · simp only [nocompiler_state]; exact hx
  · simp only [nocompiler_state]
  · intro q hq
    have hq' := hq
    simp only [preservedRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals (simp (disch := nocompiler_decide_closed) only [nocompiler_state])
    all_goals (first | rfl | exact hpr _ hq' (by decide) (by decide) (by decide) (by decide))
  · simp only [nocompiler_state]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp only [nocompiler_state]

theorem disj_byte_of {b u : Word} {n m L : Nat} (h : (Region.mk b n).Disjoint ⟨u, m⟩) (hL : L < n) :
    (Region.mk (b + BitVec.ofNat 64 L) 1).Disjoint ⟨u, m⟩ := by
  simp only [Region.Disjoint] at *; bv_omega

theorem disj_sub_r {R : Region} {f : Word} (h : R.Disjoint ⟨f, 128⟩) (o n : Nat) (h1 : o + n ≤ 128) (h0 : 0 < n) :
    R.Disjoint ⟨f + BitVec.ofNat 64 o, n⟩ := by
  simp only [Region.Disjoint] at *; bv_omega

theorem field_disj (f : Word) (a b : Nat) (h : decide (a + 8 ≤ b) = true := by decide) (h2 : decide (b + 8 ≤ 128) = true := by decide) :
    (Region.mk (f + BitVec.ofNat 64 a) 8).Disjoint ⟨f + BitVec.ofNat 64 b, 8⟩ := by
  simp only [decide_eq_true_eq] at h h2; simp only [Region.Disjoint]; bv_omega

theorem rend_eq (fb r10 len : Word) (r : Nat) (h10 : r10 = BitVec.ofNat 64 r) (hr : r < 2 ^ 64)
    (hL : len.toNat - 1 < r) (hlen : 0 < len.toNat) :
    fb + (r10 - (len - 1#64)) = fb + BitVec.ofNat 64 (r - (len.toNat - 1)) := by
  subst h10; bv_omega

theorem writeLE_one_self (m : Word → Byte) (a : Word) (v : Nat) : writeLE m a v 1 a = BitVec.ofNat 8 v := by
  simp [writeLE]

theorem readLE_one (m : Word → Byte) (a : Word) : readLE m a 1 = (m a).toNat := by
  simp only [readLE]; omega

theorem file_sub_disj' {f : Word} {R : Region} (h : (Region.mk f 128).Disjoint R) (o n : Nat) (h1 : o + n ≤ 128)
    (h0 : 0 < n) : (Region.mk (f + BitVec.ofNat 64 o) n).Disjoint R := by
  simp only [Region.Disjoint] at *; bv_omega

theorem srK_out {s : State} {f buf len p : Word} (ds : List Byte)
    (hb : ¬ (Region.mk buf len.toNat).mem p)
    (hu : ¬ (Region.mk (read64 s.mem (f + 88#64)) (read64 s.mem (f + 96#64)).toNat).mem p) :
    srK s f buf len ds p = s.mem p :=
  scatter2_out ds (by simp only [Region.mem] at *; omega) hu

theorem srK_fileLE {s : State} {f buf len : Word} (ds : List Byte)
    (dBF : (Region.mk buf len.toNat).Disjoint ⟨f, 128⟩)
    (dUF : (Region.mk (read64 s.mem (f + 88#64)) (read64 s.mem (f + 96#64)).toNat).Disjoint ⟨f, 128⟩)
    (o n : Nat) (h : o + n ≤ 128) :
    readLE (srK s f buf len ds) (f + BitVec.ofNat 64 o) n = readLE s.mem (f + BitVec.ofNat 64 o) n := by
  apply readLE_congr; intro j hj
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact srK_out ds (Auto.not_mem_of_disjoint dBF (by omega)) (Auto.not_mem_of_disjoint dUF (by omega))

/-- `__stdio_read` after a read that got `ds`, `0 < |ds|` (0x1236c). -/
theorem sr_pos (f buf len : Word) (s : State) (k : Kern) (he : Entry dom __stdio_read_entry s)
    (hpre : stdioReadP.pre (f, buf, len) s k) (ds : List Byte)
    (hdl : ds.length ≤ len.toNat - 1 + (read64 s.mem (f + 96#64)).toNat) (hmx : ds.length ≤ maxRW)
    (hpos : 0 < ds.length)
    (w : State) (hpc : w.pc = 0x1236c#64) (hc : SrCommon s f buf len (srK s f buf len ds) w)
    (h10 : w.reg 10 = BitVec.ofNat 64 ds.length) (htr : w.trace = s.trace ++ [.read (fdOf s.mem f) ds]) (k0 : Kern)
    (hK : ReadK (fdOf s.mem f) (len.toNat - 1 + (read64 s.mem (f + 96#64)).toNat) ds k0 k) :
    PReachK img dom (fun y => Final dom y.1 ∧ stdioReadP.Done (f, buf, len) (s, k0) y) (w, k) := by
  have hsp := he.sp
  have hra4 := he.retAligned
  have hret := he.ret
  simp only [Reg.sp, Reg.ra] at hsp hra4 hret
  obtain ⟨ha0, ha1, ha2, hal, hale, hlen, hbs, hB, -, hle, dFS, dES, dEF, dBS, dBE, dBF, dUS, dUE, dUF, dBU⟩ := hpre
  obtain ⟨hx, h2, h8, h9, h18, hpr, s1, s2, s3, s4, s5, hfr⟩ := hc
  have rS : ∀ o, 8 ≤ o → o ≤ 80 → k.perm.canRead (s.reg 2 - BitVec.ofNat 64 o) 8 := fun o h1 h3 =>
    Perm.canRead_of_canWrite (hle.write _ _ (.inr ⟨⟨s.reg 2 - 80#64, 80⟩, by simp [stdioReadPerm], by simp only [Region.covers]; bv_omega⟩))
  have eS : ∀ o, o ≤ 64 → s.reg 2 - 64#64 + BitVec.ofNat 64 o = s.reg 2 - BitVec.ofNat 64 (64 - o) := by
    intro o ho; bv_omega
  nocompiler_wstep [hx, hpc, h2, eS 8 (by omega), sw_alS hsp 56 rfl, s5]
  refine ⟨rS 56 (by omega) (by omega), ?_⟩
  have dFS' : (Region.mk f 128).Disjoint ⟨s.reg 2 - 80#64, 80⟩ := dFS
  have hFw : ∀ o n, o + n ≤ 128 → readLE w.mem (f + BitVec.ofNat 64 o) n = readLE s.mem (f + BitVec.ofNat 64 o) n := by
    intro o n h; rw [sr_fileLE dFS' dEF hfr o n h, srK_fileLE ds dBF dUF o n h]
  have hle80 : (Perm.mk [] [⟨s.reg 2 - 80#64, 80⟩]).le k.perm :=
    Perm.le_trans (Perm.le_of (by simp) (fun r hr => ⟨r, by simp [stdioReadPerm] at hr ⊢; exact .inr (.inl hr), Region.within_refl _⟩)) hle
  have hpr' : ∀ q ∈ preservedRegs, q ≠ 2 → q ≠ 8 → q ≠ 9 → q ≠ 18 → w.reg q = s.reg q := by
    intro q hq a b c d
    have : q ∈ [(3 : Reg), 4, 19, 20, 21, 22, 23, 24, 25, 26, 27] := by revert a b c d; revert hq; revert q; decide
    exact hpr q this
  have hL : len.toNat - 1 < 2 ^ 64 := by omega
  have hlm : (len - 1#64).toNat = len.toNat - 1 := by bv_omega
  have hult : BitVec.ult (len - 1#64) (BitVec.ofNat 64 ds.length) = decide (len.toNat - 1 < ds.length) := by
    simp only [BitVec.ult, hlm, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold maxRW at hmx; omega : ds.length < 2 ^ 64)]
  have hbuf : ∀ j, j < len.toNat - 1 → j < ds.length → w.mem (buf + BitVec.ofNat 64 j) = ds[j]! := by
    intro j hj hjd
    rw [hfr _ (Auto.not_mem_of_disjoint dBS.symm (by omega)) (Auto.not_mem_of_disjoint dBE.symm (by omega))]
    simp only [srK]
    rw [scatter2_first ds (disj_shrink_l dBU (by omega)) hL j hj hjd]
    simp [hjd]
  by_cases hA : ds.length ≤ len.toNat - 1
  · have hb : (!BitVec.ult (len - 1#64) (BitVec.ofNat 64 ds.length)) = true := by
      rw [hult]; simp; omega
    nocompiler_wstep [hx, h10, hb]
    nocompiler_wstep [hx]
    refine PReachK.bind (Dom.sub_of_ranges (by decide)) ?_ (sr_epi s k he hle80 _ (by simp only [nocompiler_state])
      (by simp only [nocompiler_state]; exact hx) (by simp (disch := nocompiler_decide_closed) only [nocompiler_state, h2])
      (fun q hq a b c d => by
        have h12 : q ≠ 12 := by revert hq; revert q; decide
        repeat (first | rw [State.setPc_reg] | rw [State.reg_setReg_other _ _ _ _ c] | rw [State.reg_setReg_other _ _ _ _ h12])
        exact hpr' q hq a b c d)
      (by simp only [nocompiler_state]; exact s1) (by simp only [nocompiler_state]; exact s2)
      (by simp only [nocompiler_state]; exact s3) (by simp only [nocompiler_state]; exact s4))
    rintro ⟨y, ky⟩ ⟨hF', hxy, hpcy, hpy, rfl, htry, h10y, hmy⟩
    simp only [nocompiler_state] at htry h10y hmy
    refine .done ⟨hF', .inl ⟨hxy, by rw [hpcy], hpy, ?_, .inl ⟨ds, hK, hdl, by rw [htry, htr], fun h => absurd h (by
      intro e; subst e; simp at hpos), fun _ _ => ⟨?_, ?_, ?_, ?_, ?_⟩, fun h => absurd h (by omega)⟩⟩⟩
    · intro p a b c d e g
      rw [hmy, hfr p a b, srK_out ds e g]
    · rw [h10y]; simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h10
    · rw [hmy]
      refine readBytes_eq_of rfl fun j hj => ?_
      rw [hbuf j (by omega) hj]; simp [hj]
    · rw [hmy]; have := hFw 0 4 (by omega); simpa using this
    · rw [hmy]; unfold read64; rw [hFw 8 8 (by omega)]
    · rw [hmy]; unfold read64; rw [hFw 16 8 (by omega)]
  · have hb : (!BitVec.ult (len - 1#64) (BitVec.ofNat 64 ds.length)) = false := by
      rw [hult]; simp; omega
    have wF : ∀ o n, o + n ≤ 128 → k.perm.canWrite (f + BitVec.ofNat 64 o) n := fun o n h =>
      hle.write _ _ (.inr ⟨⟨f, 128⟩, by simp [stdioReadPerm], by simp only [Region.covers]; bv_omega⟩)
    have alF : ∀ o, o % 8 = 0 → aligned (f + BitVec.ofNat 64 o) 8 := fun o h => sw_alF hal o h
    have h88 : read64 w.mem (f + 88#64) = read64 s.mem (f + 88#64) := by unfold read64; rw [hFw 88 8 (by omega)]
    have h96 : read64 w.mem (f + 96#64) = read64 s.mem (f + 96#64) := by unfold read64; rw [hFw 96 8 (by omega)]
    have hb2 : (read64 s.mem (f + 96#64) == 0) = false := by simpa using hbs
    nocompiler_wstep [hx, h10, hb]
    nocompiler_wstep [hx, h8, alF 88 rfl, h88]
    refine ⟨Perm.canRead_of_canWrite (wF 88 8 (by omega)), ?_⟩
    nocompiler_wstep [hx, h8, alF 96 rfl, h96]
    refine ⟨Perm.canRead_of_canWrite (wF 96 8 (by omega)), ?_⟩
    nocompiler_wstep [hx]
    nocompiler_wstep [hx]
    nocompiler_wstep [hx, h8, alF 16 rfl]
    refine ⟨wF 16 8 (by omega), ?_⟩
    nocompiler_wstep [hx, h8, alF 8 rfl]
    refine ⟨wF 8 8 (by omega), ?_⟩
    nocompiler_wstep [hx, hb2]
    nocompiler_wstep [hx]
    nocompiler_wstep [hx, h8, alF 8 rfl]
    refine ⟨wF 8 8 (by omega), ?_⟩
    have hbsn : 0 < (read64 s.mem (f + 96#64)).toNat := by
      rcases Nat.eq_zero_or_pos (read64 s.mem (f + 96#64)).toNat with h | h
      · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hbs
      · exact h
    have hUF : ∀ (o n : Nat), decide (o + n ≤ 128) = true → ∀ (m : Word → Byte) (v : Nat),
        readLE (writeLE m (f + BitVec.ofNat 64 o) v n) (read64 s.mem (f + 88#64)) 1 = readLE m (read64 s.mem (f + 88#64)) 1 := by
      intro o n h m v
      simp only [decide_eq_true_eq] at h
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · rfl
      exact readLE_writeLE_disj (R := ⟨f + BitVec.ofNat 64 o, n⟩)
        (disj_shrink_r (file_sub_disj' dUF.symm o n h hn) (by omega)) _ _ _ _ (by simp [Region.covers])
    have hdL : len.toNat - 1 < ds.length := by omega
    have hw0 : readLE w.mem (read64 s.mem (f + 88#64)) 1 = (ds[len.toNat - 1]'hdL).toNat := by
      rw [readLE_one]
      have := hfr (read64 s.mem (f + 88#64) + BitVec.ofNat 64 0) (Auto.not_mem_of_disjoint dUS.symm hbsn)
        (Auto.not_mem_of_disjoint dUE.symm hbsn)
      simp only [BitVec.add_zero] at this
      rw [this]; simp only [srK]
      have h2' := scatter2_second (m := s.mem) (a := buf) (b := read64 s.mem (f + 88#64)) (n := len.toNat - 1) ds (by omega) 0 hbsn (by omega)
      simp only [BitVec.add_zero, Nat.add_zero] at h2'
      rw [h2']
    have rU : k.perm.canRead (read64 s.mem (f + 88#64)) 1 := Perm.canRead_of_canWrite
      (hle.write _ _ (.inr ⟨⟨read64 s.mem (f + 88#64), (read64 s.mem (f + 96#64)).toNat⟩, by simp [stdioReadPerm],
        by simp only [Region.covers]; bv_omega⟩))
    have wB : k.perm.canWrite (buf + BitVec.ofNat 64 (len.toNat - 1)) 1 :=
      hle.write _ _ (.inr ⟨⟨buf, len.toNat⟩, by simp [stdioReadPerm], by simp only [Region.covers]; bv_omega⟩)
    have eB : len + buf + 18446744073709551615#64 = buf + BitVec.ofNat 64 (len.toNat - 1) := by bv_omega
    have eB' : buf + len + 18446744073709551615#64 = buf + BitVec.ofNat 64 (len.toNat - 1) := by bv_omega
    obtain ⟨b, hbd⟩ : ∃ b, ds[len.toNat - 1]'hdL = b := ⟨_, rfl⟩
    rw [hbd] at hw0
    have hsx : BitVec.ofNat 8 (BitVec.toNat ((BitVec.ofNat 8 b.toNat).signExtend 64)) = b := by
      exact NoCompiler.Libc.ofNat8_signExtend_toNat b
    nocompiler_wstep [hx, BitVec.add_zero, hUF, hw0, Auto.aligned_one]
    refine ⟨rU, ?_⟩
    nocompiler_wstep [hx, h9, h18]
    nocompiler_wstep [hx, eB, eB', Auto.aligned_one]
    refine ⟨wB, ?_⟩
    nocompiler_wstep [hx]
    have hBL : (Region.mk (buf + BitVec.ofNat 64 (len.toNat - 1)) 1).Disjoint ⟨s.reg 2 - 80#64, 80⟩ := by
      simp only [Region.Disjoint] at dBS ⊢; bv_omega
    have hM : ∀ (m : Word → Byte) (v1 v2 v3 v4 : Nat) (p : Word), ¬ (Region.mk (f + 8#64) 16).mem p →
        ¬ (Region.mk (buf + BitVec.ofNat 64 (len.toNat - 1)) 1).mem p →
        writeLE (writeLE (writeLE (writeLE m (f + 16#64) v1 8) (f + 8#64) v2 8) (f + 8#64) v3 8)
          (buf + BitVec.ofNat 64 (len.toNat - 1)) v4 1 p = m p := by
      intro m v1 v2 v3 v4 p h1 h2
      rw [writeLE_of_not_mem (r := ⟨buf + BitVec.ofNat 64 (len.toNat - 1), 1⟩) (by simp [Region.covers]) h2,
        writeLE_of_not_mem (r := ⟨f + 8#64, 16⟩) (by simp [Region.covers]) h1,
        writeLE_of_not_mem (r := ⟨f + 8#64, 16⟩) (by simp [Region.covers]) h1,
        writeLE_of_not_mem (r := ⟨f + 8#64, 16⟩) (by simp only [Region.covers]; bv_omega) h1]
    have hslot : ∀ (m : Word → Byte) (v1 v2 v3 v4 : Nat) (o : Nat), 8 ≤ o → o ≤ 80 →
        read64 (writeLE (writeLE (writeLE (writeLE m (f + 16#64) v1 8) (f + 8#64) v2 8) (f + 8#64) v3 8)
          (buf + BitVec.ofNat 64 (len.toNat - 1)) v4 1) (s.reg 2 - BitVec.ofNat 64 o) = read64 m (s.reg 2 - BitVec.ofNat 64 o) := by
      intro m v1 v2 v3 v4 o h1 h3
      apply read64_congr_on; intro j hj
      apply hM
      · simp only [Region.Disjoint, Region.mem] at dFS' ⊢; bv_omega
      · simp only [Region.Disjoint, Region.mem] at hBL ⊢; bv_omega
    refine PReachK.bind (Dom.sub_of_ranges (by decide)) ?_ (sr_epi s k he hle80 _ (by simp only [nocompiler_state])
      (by simp only [nocompiler_state]; exact hx) (by simp (disch := nocompiler_decide_closed) only [nocompiler_state, h2])
      (fun q hq a b c d => by
        obtain ⟨h10', h11', h12', h13'⟩ := (show ∀ q ∈ preservedRegs, q ≠ 10 ∧ q ≠ 11 ∧ q ≠ 12 ∧ q ≠ 13 by decide) q hq
        repeat (first | rw [State.setPc_reg] | rw [State.setMem_reg] | rw [State.reg_setReg_other _ _ _ _ h10'] | rw [State.reg_setReg_other _ _ _ _ h11'] | rw [State.reg_setReg_other _ _ _ _ h12'] | rw [State.reg_setReg_other _ _ _ _ h13'])
        exact hpr' q hq a b c d)
      (by simp only [nocompiler_state]; rw [hslot _ _ _ _ _ 8 (by omega) (by omega)]; exact s1)
      (by simp only [nocompiler_state]; rw [hslot _ _ _ _ _ 16 (by omega) (by omega)]; exact s2)
      (by simp only [nocompiler_state]; rw [hslot _ _ _ _ _ 24 (by omega) (by omega)]; exact s3)
      (by simp only [nocompiler_state]; rw [hslot _ _ _ _ _ 32 (by omega) (by omega)]; exact s4))
    rintro ⟨y, ky⟩ ⟨hF', hxy, hpcy, hpy, rfl, htry, h10y, hmy⟩
    simp only [nocompiler_state] at htry hmy
    simp (disch := nocompiler_decide_closed) only [nocompiler_state] at h10y
    have hr' : ds.length - (len.toNat - 1) ≤ (read64 s.mem (f + 96#64)).toNat := by omega
    refine .done ⟨hF', .inl ⟨hxy, by rw [hpcy], hpy, ?_, .inl ⟨ds, hK, hdl, by rw [htry, htr], fun h => absurd h (by
      intro e; subst e; simp at hpos), fun _ h => absurd h hA, fun _ => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩⟩⟩
    · intro p a b c d e g
      rw [hmy, hM _ _ _ _ _ p d (by simp only [Region.mem] at e ⊢; bv_omega), hfr p a b, srK_out ds e g]
    · rw [h10y, h9]
    · rw [hmy]
      refine readBytes_eq_of (by simp; omega) fun j hj => ?_
      by_cases hjL : j = len.toNat - 1
      · subst hjL
        rw [writeLE_one_self, hsx, ← hbd, List.getElem_take]
      · rw [hM _ _ _ _ _ _ (Auto.not_mem_of_disjoint (file_sub_disj' dBF.symm 8 16 (by omega) (by omega)) hj)
          (by simp only [Region.mem]; bv_omega), hbuf j (by omega) (by omega)]
        simp only [List.getElem_take]
        rw [getElem!_pos ds j (by omega)]
    · rw [hmy]
      have dLU := disj_byte_of (L := len.toNat - 1) dBU (by omega)
      refine readBytes_eq_of (by simp) fun j hj => ?_
      have hj' : j < (read64 s.mem (f + 96#64)).toNat := by omega
      rw [hM _ _ _ _ _ _ (Auto.not_mem_of_disjoint (file_sub_disj' dUF.symm 8 16 (by omega) (by omega)) hj')
        (Auto.not_mem_of_disjoint dLU hj'),
        hfr _ (Auto.not_mem_of_disjoint dUS.symm hj') (Auto.not_mem_of_disjoint dUE.symm hj')]
      simp only [srK]
      rw [scatter2_second ds (by omega) j hj' (by omega)]
      simp only [List.getElem_drop]
    · rw [hmy]
      have hc : readLE (writeLE (writeLE (writeLE (writeLE w.mem (f + 16#64) (BitVec.toNat (read64 s.mem (f + 88#64) + (w.reg 10 - (len - 1#64)))) 8)
          (f + 8#64) (BitVec.toNat (read64 s.mem (f + 88#64))) 8) (f + 8#64) (BitVec.toNat (read64 s.mem (f + 88#64) + 1#64)) 8)
          (buf + BitVec.ofNat 64 (len.toNat - 1)) (BitVec.signExtend 64 (BitVec.ofNat 8 (BitVec.toNat b))).toNat 1)
          (f + BitVec.ofNat 64 0) 4 = readLE w.mem (f + BitVec.ofNat 64 0) 4 := by
        apply readLE_congr; intro j hj
        apply hM
        · simp only [Region.mem]; bv_omega
        · simp only [Region.Disjoint, Region.mem] at dBF ⊢; bv_omega
      simp only [BitVec.add_zero] at hc
      rw [hc]; have := hFw 0 4 (by omega); simpa using this
    · rw [hmy, Auto.read64_writeLE_of_disjoint (R := ⟨buf + BitVec.ofNat 64 (len.toNat - 1), 1⟩)
        (disj_sub_r (disj_byte_of (L := len.toNat - 1) dBF (by omega)) 8 8 (by omega) (by omega)) _ _ _ _ (by simp [Region.covers]),
        Auto.read64_writeLE_same']
      simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [hmy, Auto.read64_writeLE_of_disjoint (R := ⟨buf + BitVec.ofNat 64 (len.toNat - 1), 1⟩)
        (disj_sub_r (disj_byte_of (L := len.toNat - 1) dBF (by omega)) 16 8 (by omega) (by omega)) _ _ _ _ (by simp [Region.covers]),
        Auto.read64_writeLE_of_disjoint (R := ⟨f + 8#64, 8⟩) (field_disj f 8 16) _ _ _ _
          (by simp [Region.covers]),
        Auto.read64_writeLE_of_disjoint (R := ⟨f + 8#64, 8⟩) (field_disj f 8 16) _ _ _ _
          (by simp [Region.covers]), Auto.read64_writeLE_same']
      simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
      exact rend_eq _ _ _ _ h10 (by unfold maxRW at hmx; omega) hdL hlen

theorem sr_ecall_dom (E : Word) (hE : E = 0x1235c#64 ∨ E = 0x123b0#64) :
    dom.mem E ∧ dom.mem (E + 4#64) ∧ dom.mem (E + 8#64) := by
  rcases hE with rfl | rfl <;> decide

theorem sr_slot_out {s : State}
    (dES : (Region.mk (s.reg 4 + 18446744073709551452#64) 4).Disjoint ⟨s.reg 2 - 80#64, 80⟩)
    (o j : Nat) (h1 : j < 8) (h2 : 8 ≤ o) (h3 : o ≤ 64) :
    ¬ (Region.mk (s.reg 2 - 64#64 - 16#64) 16).mem (s.reg 2 - BitVec.ofNat 64 o + BitVec.ofNat 64 j) ∧
    ¬ (Region.mk (s.reg 4 + 18446744073709551452#64) 4).mem (s.reg 2 - BitVec.ofNat 64 o + BitVec.ofNat 64 j) := by
  have e : s.reg 2 - BitVec.ofNat 64 o + BitVec.ofNat 64 j = s.reg 2 - 80#64 + BitVec.ofNat 64 (80 - o + j) := by bv_omega
  refine ⟨?_, ?_⟩
  · rw [e]; simp only [Region.mem]; bv_omega
  · rw [e]; exact Auto.not_mem_of_disjoint dES (by omega)

theorem sr_not16 {sp p : Word} (h : ¬ (Region.mk (sp - 80#64) 80).mem p) : ¬ (Region.mk (sp - 64#64 - 16#64) 16).mem p := by
  simp only [Region.mem] at *; bv_omega

theorem sr_al64 {sp : Word} (h : aligned sp 16) : aligned (sp - 64#64) 16 := by unfold aligned at *; bv_omega

theorem sr_errDisj16 {s : State}
    (dES : (Region.mk (s.reg 4 + 18446744073709551452#64) 4).Disjoint ⟨s.reg 2 - 80#64, 80⟩) :
    (Region.mk (s.reg 4 + 18446744073709551452#64) 4).Disjoint ⟨s.reg 2 - 64#64 - 16#64, 16⟩ := by
  simp only [Region.Disjoint] at *; bv_omega

/-- After a syscall of `__stdio_read` (at 0x1235c or 0x123b0), from the state `y` at its `auipc` (E + 4) with
    a0 = `v`: the call of `__syscall_ret` and the return to E + 12. -/
theorem sr_retcall (f buf len : Word) (s : State) (k : Kern) (he : Entry dom __stdio_read_entry s)
    (hpre : stdioReadP.pre (f, buf, len) s k) (m0 : Word → Byte)
    (Q : State × Kern → Prop) (E : Word) (hE : E = 0x1235c#64 ∨ E = 0x123b0#64)
    (v : Word) (y : State) (hpc : y.pc = E + 4#64) (hc : SrCommon s f buf len m0 y) (hy10 : y.reg 10 = v)
    (K : ∀ w : State, w.pc = E + 12#64 → SrCommon s f buf len m0 w →
      w.reg 10 = (if v.toNat < 2 ^ 64 - 4095 then v else -1) → w.trace = y.trace → PReachK img dom Q (w, k)) :
    PReachK img dom Q (y, k) := by
  have hsp := he.sp
  simp only [Reg.sp] at hsp
  obtain ⟨ha0, ha1, ha2, hal, hale, hlen, hbs, hB, -, hle, dFS, dES, dEF, dBS, dBE, dBF, dUS, dUE, dUF, dBU⟩ := hpre
  obtain ⟨hyx, h2, h8, h9, h18, hpr, s1, s2, s3, s4, s5, hfr⟩ := hc
  have h4 : y.reg 4 = s.reg 4 := hpr 4 (by simp)
  have dES' : (Region.mk (s.reg 4 + 18446744073709551452#64) 4).Disjoint ⟨s.reg 2 - 80#64, 80⟩ := dES
  have hsrle : ∀ (st : State), st.reg 2 = s.reg 2 - 64#64 → st.reg 4 = s.reg 4 → ∀ v,
      (syscallRetSpec.perm v st).le k.perm := by
    intro st hs2 hs4 v
    refine Perm.le_trans (Perm.le_of (by simp [Spec.perm, syscallRetSpec]) ?_) hle
    intro r hr
    simp only [Spec.perm, syscallRetSpec, Spec.stackRegion, Reg.sp, Reg.tp, hs2, hs4, List.mem_cons,
      List.not_mem_nil, or_false, List.cons_append, List.nil_append] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨s.reg 4 + 18446744073709551452#64, 4⟩, by simp [stdioReadPerm], Region.within_refl _⟩
    · exact ⟨⟨s.reg 2 - 80#64, 80⟩, by simp [stdioReadPerm], by simp only [Region.within]; bv_omega⟩
  rcases hE with rfl | rfl
  all_goals (
    simp only [BitVec.reduceAdd] at hpc
    refine NoCompiler.Linux.PReachK.exec_step (by rw [hpc]; decide) hyx ?_
    rw [hpc]
    simp only [nocompiler_image]
    nocompiler_vnorm [hpc, true_and]
    nocompiler_vnorm [hpc, true_and]
    refine NoCompiler.Linux.PReachK.exec_step ?_ ?_ ?_
    · simp only [nocompiler_state]; decide
    · simp only [nocompiler_state]; exact hyx
    simp only [nocompiler_state, nocompiler_image]
    nocompiler_vnorm [true_and]
    nocompiler_vnorm [true_and]
    refine VerifiedProc.call sr_syscall_ret v ⟨?_, ?_, ?_, ?_, ?_⟩ ⟨⟨?_, ?_, ?_⟩, ?_⟩
      (Dom.sub_of_ranges (by decide)) ?_
    · simp only [nocompiler_state]; rfl
    · simp only [nocompiler_state]; exact hyx
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.ra] <;> decide
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.ra] <;> decide
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.sp, h2]; exact sr_al64 hsp
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.a0, hy10]
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.tp, h4]; exact hale
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.tp, Reg.sp, h4, h2, Spec.stackRegion]; exact sr_errDisj16 dES'
    · exact hsrle _ (by simp (disch := nocompiler_decide_closed) only [nocompiler_state, h2]) (by simp (disch := nocompiler_decide_closed) only [nocompiler_state, h4]) _
    rintro ⟨w, kw⟩ (⟨hxw, hpcw, hpresw, ha0w, hkw, htrw, hfrw⟩ | ⟨_, hexw⟩)
    rotate_left
    · exact hexw.elim
    simp only at hxw hpcw hpresw ha0w hkw htrw hfrw
    simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.tp, Reg.sp, h4, h2] at hfrw
    rw [hkw]
    have hwr : ∀ q : Reg, q ∈ preservedRegs → w.reg q = y.reg q := by
      intro q hq; rw [hpresw q hq]
      have h1 : q ≠ 1 := not_one_of_preserved q hq
      repeat (first | rw [State.setPc_reg] | rw [State.reg_setReg_other _ _ _ _ h1])
    have hws : ∀ o, 8 ≤ o → o ≤ 64 → read64 w.mem (s.reg 2 - BitVec.ofNat 64 o) = read64 y.mem (s.reg 2 - BitVec.ofNat 64 o) := by
      intro o h1 h3
      apply read64_congr_on; intro j hj
      have hj' := sr_slot_out dES' o j hj h1 h3
      rw [hfrw _ hj'.2 hj'.1]
    have hpr0 : ∀ q ∈ [(3 : Reg), 4, 19, 20, 21, 22, 23, 24, 25, 26, 27], q ∈ preservedRegs := by decide
    refine K w ?_ ⟨hxw, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_ ?_
    · rw [hpcw]; simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.ra] <;> decide
    · rw [hwr 2 (by decide), h2]
    · rw [hwr 8 (by decide), h8]
    · rw [hwr 9 (by decide), h9]
    · rw [hwr 18 (by decide), h18]
    · intro q hq; rw [hwr q (hpr0 q hq), hpr q hq]
    · rw [hws 8 (by omega) (by omega)]; exact s1
    · rw [hws 16 (by omega) (by omega)]; exact s2
    · rw [hws 24 (by omega) (by omega)]; exact s3
    · rw [hws 32 (by omega) (by omega)]; exact s4
    · rw [hws 56 (by omega) (by omega)]; exact s5
    · intro p hp1 hp2
      rw [hfrw p hp2 (sr_not16 hp1)]; exact hfr p hp1 hp2
    · simpa using ha0w
    · rw [htrw]; simp only [nocompiler_state]
    )

theorem slt_zero_ofNat (r : Nat) (h : r < 2 ^ 63) : BitVec.slt (0 : Word) (BitVec.ofNat 64 r) = decide (0 < r) := by
  have : BitVec.slt (0 : Word) (BitVec.ofNat 64 r) = true ↔ 0 < r := by
    constructor
    · intro h1; rcases Nat.eq_zero_or_pos r with rfl | hr
      · simp at h1
      · exact hr
    · intro hr; rw [BitVec.slt_eq_decide, decide_eq_true_eq, BitVec.toInt_eq_toNat_cond, BitVec.toInt_eq_toNat_cond]
      simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : r < 2 ^ 64)]; omega
  by_cases hr : 0 < r
  · rw [this.2 hr]; simp [hr]
  · have : BitVec.slt (0 : Word) (BitVec.ofNat 64 r) ≠ true := fun h' => hr (this.1 h')
    simp_all

end NoCompiler.Libc.Musl.StdioRead
