import Examples.Libc.Musl.StdioWrite2

set_option maxRecDepth 20000
namespace NoCompiler.Libc.Musl.StdioWrite
open NoCompiler NoCompiler.Linux NoCompiler.Libc NoCompiler.Libc.Musl.StdioWriteImg NoCompiler.Libc.Musl.SyscallRet

/-- One round from the cut with two iovecs and a count `r` within the buffered bytes left: the first
    iovec advanced by `r`, then 0x12558. -/
theorem sw_round_two (f buf len : Word) (s : State) (k : Kern) (he : Entry dom __stdio_write_entry s)
    (hpre : stdioWriteSpec.pre (f, buf, len) s k)
    (u : State) (hpc : u.pc = 0x1256c#64) (hc : SwCommon s f len u) (d : Nat) (evs : List Event)
    (htr : u.trace = s.trace ++ evs)
    (h20 : u.reg 20 = BitVec.ofNat 64 ((stdioBytes s.mem f buf len).length - d))
    (h21 : u.reg 21 = s.reg 2 - 88#64) (h18 : u.reg 18 = 2#64)
    (m88 : read64 u.mem (s.reg 2 - 88#64) = read64 s.mem (f + 56#64) + BitVec.ofNat 64 d)
    (m80 : read64 u.mem (s.reg 2 - 80#64) = BitVec.ofNat 64 (stdioPend s.mem f - d))
    (m72 : read64 u.mem (s.reg 2 - 72#64) = buf) (m64 : read64 u.mem (s.reg 2 - 64#64) = len)
    (hpd : d ≤ stdioPend s.mem f) (r : Nat) (hr : 0 < r) (hrp : r ≤ stdioPend s.mem f - d)
    (hdr : d + r < (stdioBytes s.mem f buf len).length)
    (h10 : u.reg 10 = BitVec.ofNat 64 r)
    (hev : WritesOf (fdOf s.mem f) evs ((stdioBytes s.mem f buf len).take (d + r))) :
    PReachK img dom (SwLoopQ f buf len s k ((stdioBytes s.mem f buf len).length - d)) (u, k) := by
  have hpre' := hpre
  obtain ⟨-, -, -, hal, -, hle, dFS, dES, dEF, -, -, -, -, hB, -⟩ := hpre'
  have hBl := stdioBytes_length s.mem f buf len
  have hsp := he.sp
  simp only [Reg.sp] at hsp
  have hc' := hc
  obtain ⟨hx, h2, h9, h8, hpr, s1, s2, s3, s4, s5, s6, s7, hfr⟩ := hc'
  have hW := fun {a n} h => sw_canWrite (a := a) (n := n) hle h
  have rS : ∀ o, 8 ≤ o → o ≤ 112 → k.perm.canRead (s.reg 2 - BitVec.ofNat 64 o) 8 := fun o h1 h2 =>
    Perm.canRead_of_canWrite (hW (.inr (.inl (sw_cS _ o 8 h1 h2))))
  have wS : ∀ o, 8 ≤ o → o ≤ 112 → k.perm.canWrite (s.reg 2 - BitVec.ofNat 64 o) 8 := fun o h1 h2 =>
    hW (.inr (.inl (sw_cS _ o 8 h1 h2)))
  have hr63 : r < 2 ^ 63 := by omega
  have e80 : s.reg 2 - 88#64 + 8#64 = s.reg 2 - 80#64 := by bv_omega
  have hult : (BitVec.ofNat 64 (stdioPend s.mem f - d)).ult (BitVec.ofNat 64 r) = false :=
    ult_ofNat_false (by omega) (by omega)
  have hsub : BitVec.ofNat 64 (stdioPend s.mem f - d) - BitVec.ofNat 64 r =
      BitVec.ofNat 64 (stdioPend s.mem f - d - r) := ofNat_sub_ofNat (by omega)
  have hsub' : BitVec.ofNat 64 ((stdioBytes s.mem f buf len).length - d) - BitVec.ofNat 64 r =
      BitVec.ofNat 64 ((stdioBytes s.mem f buf len).length - (d + r)) := by
    rw [ofNat_sub_ofNat (by omega), show (stdioBytes s.mem f buf len).length - d - r = (stdioBytes s.mem f buf len).length - (d + r) by omega]
  have hm1 : ∀ v, read64 (writeLE u.mem (s.reg 2 - 88#64) v 8) (s.reg 2 - 80#64) = read64 u.mem (s.reg 2 - 80#64) := by
    intro v
    exact Auto.read64_writeLE_of_disjoint (R := ⟨s.reg 2 - 88#64, 8⟩) (by simp only [Region.Disjoint]; bv_omega) _ _ _ _
      (by simp [Region.covers])
  have hfd : ∀ v1 v2, readLE (writeLE (writeLE u.mem (s.reg 2 - 88#64) v1 8) (s.reg 2 - 80#64) v2 8) (f + 120#64) 4 =
      readLE s.mem (f + 120#64) 4 := by
    intro v1 v2
    rw [readLE_writeLE_disj (R := ⟨s.reg 2 - 80#64, 8⟩) ((sw_dFS dFS 120 4 80 (by omega) (by omega) (by omega) (by omega)).symm) _ _ _ _ (by simp [Region.covers]),
      readLE_writeLE_disj (R := ⟨s.reg 2 - 88#64, 8⟩) ((sw_dFS dFS 120 4 88 (by omega) (by omega) (by omega) (by omega)).symm) _ _ _ _ (by simp [Region.covers])]
    apply readLE_congr; intro j hj
    have hj' := sw_outF dFS dEF (120 + j) (by omega)
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact hfr _ hj'.1 hj'.2
  have r120 : k.perm.canRead (f + 120#64) 4 := Perm.canRead_of_canWrite (hW (.inl (sw_cF f 120 4 (by omega))))
  have al120 : aligned (f + 120#64) 4 := by have := sw_alF hal 120 rfl; unfold aligned at *; omega
  nocompiler_run_n 26 [hx, bool64_false', bool64_true', hpc, h10, slt_ofNat_zero hr63, h21, e80, sw_alS hsp 80 rfl, m80, hult, BitVec.add_zero, sw_alS hsp 88 rfl, m88, hm1, hsub, h9, al120, hfd, h20, hsub', h18] using [rS, wS, r120]
  have hslot : ∀ o, 8 ≤ o → o ≤ 56 → ∀ v1 v2 : Nat,
      read64 (writeLE (writeLE u.mem (s.reg 2 - 88#64) v1 8) (s.reg 2 - 80#64) v2 8) (s.reg 2 - BitVec.ofNat 64 o) =
        read64 u.mem (s.reg 2 - BitVec.ofNat 64 o) := by
    intro o h1 h2 v1 v2
    rw [Auto.read64_writeLE_of_disjoint (R := ⟨s.reg 2 - 80#64, 8⟩) (by simp only [Region.Disjoint]; bv_omega) _ _ _ _ (by simp [Region.covers]),
      Auto.read64_writeLE_of_disjoint (R := ⟨s.reg 2 - 88#64, 8⟩) (by simp only [Region.Disjoint]; bv_omega) _ _ _ _ (by simp [Region.covers])]
  refine sw_at_12558 f buf len s k he hpre _ ?_ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ (d + r) (by omega) ?_ ?_ evs ?_ hev _ (by omega)
  · simp only [nocompiler_state]
  · simp only [nocompiler_state]; exact hx
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h2
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h9
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h8
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      (simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact hpr _ (by simp))
  · simp only [nocompiler_state]; rw [hslot 8 (by omega) (by omega)]; exact s1
  · simp only [nocompiler_state]; rw [hslot 16 (by omega) (by omega)]; exact s2
  · simp only [nocompiler_state]; rw [hslot 24 (by omega) (by omega)]; exact s3
  · simp only [nocompiler_state]; rw [hslot 32 (by omega) (by omega)]; exact s4
  · simp only [nocompiler_state]; rw [hslot 40 (by omega) (by omega)]; exact s5
  · simp only [nocompiler_state]; rw [hslot 48 (by omega) (by omega)]; exact s6
  · simp only [nocompiler_state]; rw [hslot 56 (by omega) (by omega)]; exact s7
  · intro p hp1 hp2
    simp only [nocompiler_state]
    rw [writeLE_of_not_mem (r := ⟨s.reg 2 - 112#64, 112⟩) (sw_cS _ 80 8 (by omega) (by omega)) hp1,
      writeLE_of_not_mem (r := ⟨s.reg 2 - 112#64, 112⟩) (sw_cS _ 88 8 (by omega) (by omega)) hp1]
    exact hfr p hp1 hp2
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; rfl
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
    have d8072 : (Region.mk (s.reg 2 - 80#64) 8).Disjoint ⟨s.reg 2 - 72#64, 8⟩ := by simp only [Region.Disjoint]; bv_omega
    have d8872 : (Region.mk (s.reg 2 - 88#64) 8).Disjoint ⟨s.reg 2 - 72#64, 8⟩ := by simp only [Region.Disjoint]; bv_omega
    have d8064 : (Region.mk (s.reg 2 - 80#64) 8).Disjoint ⟨s.reg 2 - 64#64, 8⟩ := by simp only [Region.Disjoint]; bv_omega
    have d8864 : (Region.mk (s.reg 2 - 88#64) 8).Disjoint ⟨s.reg 2 - 64#64, 8⟩ := by simp only [Region.Disjoint]; bv_omega
    have d8088 : (Region.mk (s.reg 2 - 80#64) 8).Disjoint ⟨s.reg 2 - 88#64, 8⟩ := by simp only [Region.Disjoint]; bv_omega
    refine .inl ⟨by omega, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · rw [Auto.read64_writeLE_of_disjoint d8088 _ _ _ _ (by simp [Region.covers]),
        Auto.read64_writeLE_same', BitVec.ofNat_toNat, BitVec.setWidth_eq, add_ofNat_add]
    · rw [Auto.read64_writeLE_same', BitVec.ofNat_toNat, BitVec.setWidth_eq,
        show stdioPend s.mem f - d - r = stdioPend s.mem f - (d + r) by omega]
    · rw [Auto.read64_writeLE_of_disjoint d8072 _ _ _ _ (by simp [Region.covers]),
        Auto.read64_writeLE_of_disjoint d8872 _ _ _ _ (by simp [Region.covers]), m72]
    · rw [Auto.read64_writeLE_of_disjoint d8064 _ _ _ _ (by simp [Region.covers]),
        Auto.read64_writeLE_of_disjoint d8864 _ _ _ _ (by simp [Region.covers]), m64]
  · simp only [nocompiler_state]; exact htr

/-- One round from the cut with two iovecs and a count `r` past the buffered bytes left: the second
    iovec advanced by what `r` took from it, one iovec left, then 0x12558. -/
theorem sw_round_cross (f buf len : Word) (s : State) (k : Kern) (he : Entry dom __stdio_write_entry s)
    (hpre : stdioWriteSpec.pre (f, buf, len) s k)
    (u : State) (hpc : u.pc = 0x1256c#64) (hc : SwCommon s f len u) (d : Nat) (evs : List Event)
    (htr : u.trace = s.trace ++ evs)
    (h20 : u.reg 20 = BitVec.ofNat 64 ((stdioBytes s.mem f buf len).length - d))
    (h21 : u.reg 21 = s.reg 2 - 88#64) (h18 : u.reg 18 = 2#64)
    (m80 : read64 u.mem (s.reg 2 - 80#64) = BitVec.ofNat 64 (stdioPend s.mem f - d))
    (m72 : read64 u.mem (s.reg 2 - 72#64) = buf) (m64 : read64 u.mem (s.reg 2 - 64#64) = len)
    (hpd : d ≤ stdioPend s.mem f) (r : Nat) (hr : 0 < r) (hrp : stdioPend s.mem f - d < r)
    (hdr : d + r < (stdioBytes s.mem f buf len).length)
    (h10 : u.reg 10 = BitVec.ofNat 64 r)
    (hev : WritesOf (fdOf s.mem f) evs ((stdioBytes s.mem f buf len).take (d + r))) :
    PReachK img dom (SwLoopQ f buf len s k ((stdioBytes s.mem f buf len).length - d)) (u, k) := by
  have hpre' := hpre
  obtain ⟨-, -, -, hal, -, hle, dFS, dES, dEF, -, -, -, -, hB, -⟩ := hpre'
  have hBl := stdioBytes_length s.mem f buf len
  have hsp := he.sp
  simp only [Reg.sp] at hsp
  have hc' := hc
  obtain ⟨hx, h2, h9, h8, hpr, s1, s2, s3, s4, s5, s6, s7, hfr⟩ := hc'
  have hW := fun {a n} h => sw_canWrite (a := a) (n := n) hle h
  have rS : ∀ o, 8 ≤ o → o ≤ 112 → k.perm.canRead (s.reg 2 - BitVec.ofNat 64 o) 8 := fun o h1 h2 =>
    Perm.canRead_of_canWrite (hW (.inr (.inl (sw_cS _ o 8 h1 h2))))
  have wS : ∀ o, 8 ≤ o → o ≤ 112 → k.perm.canWrite (s.reg 2 - BitVec.ofNat 64 o) 8 := fun o h1 h2 =>
    hW (.inr (.inl (sw_cS _ o 8 h1 h2)))
  have hr63 : r < 2 ^ 63 := by omega
  have e80 : s.reg 2 - 88#64 + 8#64 = s.reg 2 - 80#64 := by bv_omega
  have e72 : s.reg 2 - 88#64 + 16#64 = s.reg 2 - 72#64 := by bv_omega
  have e64 : s.reg 2 - 88#64 + 24#64 = s.reg 2 - 64#64 := by bv_omega
  have hult : (BitVec.ofNat 64 (stdioPend s.mem f - d)).ult (BitVec.ofNat 64 r) = true :=
    ult_ofNat_true (by omega) (by omega)
  have hsubr : BitVec.ofNat 64 r - BitVec.ofNat 64 (stdioPend s.mem f - d) =
      BitVec.ofNat 64 (r - (stdioPend s.mem f - d)) := ofNat_sub_ofNat (by omega)
  have hlen : len - BitVec.ofNat 64 (r - (stdioPend s.mem f - d)) =
      BitVec.ofNat 64 (len.toNat - (r - (stdioPend s.mem f - d))) := by
    have hx' : r - (stdioPend s.mem f - d) ≤ len.toNat := by rw [hBl] at hdr; omega
    have e : len = BitVec.ofNat 64 len.toNat := by simp
    conv => lhs; rw [e]
    exact ofNat_sub_ofNat hx'
  have hsub' : BitVec.ofNat 64 ((stdioBytes s.mem f buf len).length - d) - BitVec.ofNat 64 r =
      BitVec.ofNat 64 ((stdioBytes s.mem f buf len).length - (d + r)) := by
    rw [ofNat_sub_ofNat (by omega), show (stdioBytes s.mem f buf len).length - d - r = (stdioBytes s.mem f buf len).length - (d + r) by omega]
  have hm1 : ∀ v, read64 (writeLE u.mem (s.reg 2 - 72#64) v 8) (s.reg 2 - 64#64) = read64 u.mem (s.reg 2 - 64#64) := by
    intro v
    exact Auto.read64_writeLE_of_disjoint (R := ⟨s.reg 2 - 72#64, 8⟩) (by simp only [Region.Disjoint]; bv_omega) _ _ _ _
      (by simp [Region.covers])
  have hfd : ∀ v1 v2, readLE (writeLE (writeLE u.mem (s.reg 2 - 72#64) v1 8) (s.reg 2 - 64#64) v2 8) (f + 120#64) 4 =
      readLE s.mem (f + 120#64) 4 := by
    intro v1 v2
    rw [readLE_writeLE_disj (R := ⟨s.reg 2 - 64#64, 8⟩) ((sw_dFS dFS 120 4 64 (by omega) (by omega) (by omega) (by omega)).symm) _ _ _ _ (by simp [Region.covers]),
      readLE_writeLE_disj (R := ⟨s.reg 2 - 72#64, 8⟩) ((sw_dFS dFS 120 4 72 (by omega) (by omega) (by omega) (by omega)).symm) _ _ _ _ (by simp [Region.covers])]
    apply readLE_congr; intro j hj
    have hj' := sw_outF dFS dEF (120 + j) (by omega)
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact hfr _ hj'.1 hj'.2
  have r120 : k.perm.canRead (f + 120#64) 4 := Perm.canRead_of_canWrite (hW (.inl (sw_cF f 120 4 (by omega))))
  have al120 : aligned (f + 120#64) 4 := by have := sw_alF hal 120 rfl; unfold aligned at *; omega
  nocompiler_run_n 23 [hx, bool64_false', bool64_true', hpc, h10, slt_ofNat_zero hr63, h21, e80, sw_alS hsp 80 rfl, m80, hult, hsubr, e72, BitVec.add_zero, sw_alS hsp 72 rfl, m72, e64, sw_alS hsp 64 rfl, hm1, m64, hlen, h9, al120, hfd, h20, hsub', h18] using [rS, wS, r120]
  have hslot : ∀ o, 8 ≤ o → o ≤ 56 → ∀ v1 v2 : Nat,
      read64 (writeLE (writeLE u.mem (s.reg 2 - 72#64) v1 8) (s.reg 2 - 64#64) v2 8) (s.reg 2 - BitVec.ofNat 64 o) =
        read64 u.mem (s.reg 2 - BitVec.ofNat 64 o) := by
    intro o h1 h2 v1 v2
    rw [Auto.read64_writeLE_of_disjoint (R := ⟨s.reg 2 - 64#64, 8⟩) (by simp only [Region.Disjoint]; bv_omega) _ _ _ _ (by simp [Region.covers]),
      Auto.read64_writeLE_of_disjoint (R := ⟨s.reg 2 - 72#64, 8⟩) (by simp only [Region.Disjoint]; bv_omega) _ _ _ _ (by simp [Region.covers])]
  refine sw_at_12558 f buf len s k he hpre _ ?_ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ (d + r) (by omega) ?_ ?_ evs ?_ hev _ (by omega)
  · simp only [nocompiler_state]
  · simp only [nocompiler_state]; exact hx
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h2
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h9
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h8
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      (simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact hpr _ (by simp))
  · simp only [nocompiler_state]; rw [hslot 8 (by omega) (by omega)]; exact s1
  · simp only [nocompiler_state]; rw [hslot 16 (by omega) (by omega)]; exact s2
  · simp only [nocompiler_state]; rw [hslot 24 (by omega) (by omega)]; exact s3
  · simp only [nocompiler_state]; rw [hslot 32 (by omega) (by omega)]; exact s4
  · simp only [nocompiler_state]; rw [hslot 40 (by omega) (by omega)]; exact s5
  · simp only [nocompiler_state]; rw [hslot 48 (by omega) (by omega)]; exact s6
  · simp only [nocompiler_state]; rw [hslot 56 (by omega) (by omega)]; exact s7
  · intro p hp1 hp2
    simp only [nocompiler_state]
    rw [writeLE_of_not_mem (r := ⟨s.reg 2 - 112#64, 112⟩) (sw_cS _ 64 8 (by omega) (by omega)) hp1,
      writeLE_of_not_mem (r := ⟨s.reg 2 - 112#64, 112⟩) (sw_cS _ 72 8 (by omega) (by omega)) hp1]
    exact hfr p hp1 hp2
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; rfl
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
    refine .inr ⟨by omega, by rw [← hBl]; omega, rfl, rfl, ?_, ?_⟩
    · rw [Auto.read64_writeLE_of_disjoint (R := ⟨s.reg 2 - 64#64, 8⟩) (by simp only [Region.Disjoint]; bv_omega) _ _ _ _ (by simp [Region.covers]),
        Auto.read64_writeLE_same', BitVec.ofNat_toNat, BitVec.setWidth_eq,
        show r - (stdioPend s.mem f - d) = d + r - stdioPend s.mem f by omega]
    · rw [Auto.read64_writeLE_same', BitVec.ofNat_toNat, BitVec.setWidth_eq,
        show len.toNat - (r - (stdioPend s.mem f - d)) = stdioPend s.mem f + len.toNat - (d + r) by rw [hBl] at hdr; omega]
  · simp only [nocompiler_state]; exact htr

/-- The loop: from every state at the cut, the run reaches `__stdio_write`'s end (its specification's
    `Done`, outside its domain). By `PReachK.loop`, measure s4 (the bytes left before the last writev). -/
theorem sw_loop (f buf len : Word) (s : State) (k : Kern) (he : Entry dom __stdio_write_entry s)
    (hpre : stdioWriteSpec.pre (f, buf, len) s k) :
    ∀ x, CutInv f buf len s k x → PReachK img dom (SwQ f buf len s k) x := by
  have hpre' := hpre
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hB, -⟩ := hpre'
  have hBl := stdioBytes_length s.mem f buf len
  refine PReachK.loop (CutInv f buf len s k) (fun x => (x.1.reg 20).toNat) ?_
  rintro ⟨u, ku⟩ ⟨hk, hpc, hc, d, evs, hd, htr, h20, hiov, hres⟩
  simp only at hk hpc hc htr h20 hiov hres ⊢
  rw [hk]
  have hμ : (u.reg 20).toNat = (stdioBytes s.mem f buf len).length - d := by
    rw [h20, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [hμ]
  rcases hres with ⟨r, hr, hdr, h10, hev⟩ | ⟨h10, hev⟩
  · rcases hiov with ⟨hdp, h18, h21, m88, m80, m72, m64⟩ | ⟨hpd, hdB, h18, h21, m72, m64⟩
    · by_cases hcross : r ≤ stdioPend s.mem f - d
      · exact sw_round_two f buf len s k he hpre u hpc hc d evs htr h20 h21 h18 m88 m80 m72 m64 hdp r hr hcross hdr h10 hev
      · exact sw_round_cross f buf len s k he hpre u hpc hc d evs htr h20 h21 h18 m80 m72 m64 hdp r hr (by omega) hdr h10 hev
    · exact sw_round_one f buf len s k he hpre u hpc hc d evs htr h20 h21 h18 m72 m64 hpd r hr hdr h10 hev
  · exact PReachK.bind (fun _ h => h) (fun y hy => .done (.inl hy))
      (sw_cut_err f buf len s k he hpre u hpc hc d evs hd htr hiov h10 hev)

theorem SwCommon.setPc {s : State} {f len : Word} {u : State} (h : SwCommon s f len u) (p : Word) :
    SwCommon s f len (u.setPc p) := by
  unfold SwCommon at *
  simp only [nocompiler_state] at h ⊢
  exact h

/-- From 0x124e8 (after the first writev and its `__syscall_ret`): `bne s4, a0`: all of the bytes written
    (into the success exit), else the cut with nothing written before (into the loop). -/
theorem sw_first (f buf len : Word) (s : State) (k : Kern) (he : Entry dom __stdio_write_entry s)
    (hpre : stdioWriteSpec.pre (f, buf, len) s k)
    (w : State) (hpc : w.pc = 0x124e8#64) (hc : SwCommon s f len w)
    (h20 : w.reg 20 = BitVec.ofNat 64 (stdioBytes s.mem f buf len).length)
    (hiov : IovAt s f buf len w.mem (w.reg 21) (w.reg 18) 0)
    (hres : (∃ r, r ≤ (stdioBytes s.mem f buf len).length ∧ ((0 < (stdioBytes s.mem f buf len).length) → 0 < r) ∧
        w.reg 10 = BitVec.ofNat 64 r ∧
        w.trace = s.trace ++ [.write (fdOf s.mem f) ((stdioBytes s.mem f buf len).take r)]) ∨
      (w.reg 10 = -1 ∧ w.trace = s.trace)) :
    PReachK img dom (SwQ f buf len s k) (w, k) := by
  have hpre' := hpre
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hB, -⟩ := hpre'
  have hBl := stdioBytes_length s.mem f buf len
  have hx := hc.1
  have hcut : ∀ (hr : (∃ r, 0 < r ∧ 0 + r < (stdioBytes s.mem f buf len).length ∧ w.reg 10 = BitVec.ofNat 64 r ∧
        WritesOf (fdOf s.mem f) (w.trace.drop s.trace.length) ((stdioBytes s.mem f buf len).take (0 + r))) ∨
      (w.reg 10 = -1 ∧ WritesOf (fdOf s.mem f) (w.trace.drop s.trace.length) ((stdioBytes s.mem f buf len).take 0))),
      w.trace = s.trace ++ w.trace.drop s.trace.length →
      PReachK img dom (SwQ f buf len s k) (w.setPc 0x1256c#64, k) := by
    intro hr htr
    refine sw_loop f buf len s k he hpre _ ⟨rfl, rfl, ?_, 0, w.trace.drop s.trace.length, by omega,
      by simp only [nocompiler_state]; exact htr, ?_, ?_, ?_⟩
    · exact hc.setPc _
    · simp only [nocompiler_state, h20, Nat.sub_zero]
    · simp only [nocompiler_state]; exact hiov
    · simp only [nocompiler_state]; exact hr
  rcases hres with ⟨r, hr1, hr2, hr3, hr4⟩ | ⟨hr3, hr4⟩
  · have hdrop : w.trace.drop s.trace.length = [.write (fdOf s.mem f) ((stdioBytes s.mem f buf len).take r)] := by
      rw [hr4]; simp
    have hW1 : WritesOf (fdOf s.mem f) [.write (fdOf s.mem f) ((stdioBytes s.mem f buf len).take r)]
        ((stdioBytes s.mem f buf len).take r) :=
      ⟨fun e he => by simp at he; exact ⟨_, he⟩, by simp [evBytes]⟩
    by_cases heq : r = (stdioBytes s.mem f buf len).length
    · have hr3' : w.reg 10 = BitVec.ofNat 64 (stdioBytes s.mem f buf len).length := by rw [hr3, heq]
      nocompiler_vstep [hx, hpc, h20, hr3', bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      have htake : (stdioBytes s.mem f buf len).take r = stdioBytes s.mem f buf len := by
        rw [heq]; exact List.take_of_length_le (Nat.le_refl _)
      refine sw_succ f buf len s k he hpre _ (by simp only [nocompiler_state]) ?_
        [.write (fdOf s.mem f) ((stdioBytes s.mem f buf len).take r)] (by simp only [nocompiler_state]; exact hr4) ?_
      · exact hc.setPc _
      · exact ⟨hW1.1, by rw [hW1.2, htake]⟩
    · have hne : BitVec.ofNat 64 (stdioBytes s.mem f buf len).length ≠ BitVec.ofNat 64 r :=
        ofNat_ne_of_lt (by omega) (by omega) (Ne.symm heq)
      nocompiler_vstep [hx, hpc, h20, hr3, bne_iff_ne, ne_eq, hne, not_false_eq_true, ↓reduceIte]
      refine hcut (.inl ⟨r, hr2 (by omega), by omega, hr3, by rw [hdrop, Nat.zero_add]; exact hW1⟩) ?_
      rw [hdrop]; exact hr4
  · have hne : BitVec.ofNat 64 (stdioBytes s.mem f buf len).length ≠ -1 := ofNat_ne_neg_one (by omega)
    nocompiler_vstep [hx, hpc, h20, hr3, bne_iff_ne, ne_eq, hne, not_false_eq_true, ↓reduceIte]
    refine hcut (.inr ⟨hr3, by rw [hr4]; simp [WritesOf]⟩) (by rw [hr4]; simp)

end NoCompiler.Libc.Musl.StdioWrite
