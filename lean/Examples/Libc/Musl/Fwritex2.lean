import Examples.Libc.Musl.Fwritex1

set_option maxRecDepth 20000
namespace NoCompiler.Libc.Musl.Fwritex
open NoCompiler NoCompiler.Linux NoCompiler.Libc NoCompiler.Libc.Musl NoCompiler.Libc.Musl.StdioWrite NoCompiler.Libc.Musl.Memcpy NoCompiler.Libc.Musl.FwriteImg

/-- After `f->write` returned fewer than `i`: that count is the result. -/
theorem fw_after_lt (s : State) (k : Kern) (D : Dom) (hD : __fwritex_dom.sub D) (he : Entry D 0x11fe8#64 s)
    (hrd : ∀ o, 8 ≤ o → o ≤ 56 → k.perm.canRead (s.reg 2 - BitVec.ofNat 64 o) 8)
    (f src l i : Word) (j : Nat) (w : State) (hb : FwBack s f src l i j w)
    (hlt : (w.reg 10).ult i = true) (R : State × Kern → Prop)
    (hR : ∀ y : State × Kern, y.2 = k → y.1.mem = w.mem → y.1.trace = w.trace → y.1.reg 10 = w.reg 10 →
      y.1.exit = none → y.1.pc = s.reg 1 → Preserved s y.1 → R y) :
    PReachK img D (fun y => Final D y.1 ∧ R y) (w, k) := by
  obtain ⟨hpc, hx, h2, h8, h9, h18, h19, h20, h21, hpr, s1, s2, s3, s4, s5, s6, s7⟩ := hb
  nocompiler_wstepD hD [hx, hpc, h19, hlt]
  exact fw_epi s k D hD he hrd R _ (by simp only [nocompiler_state]) (by simp only [nocompiler_state]; exact hx)
    (by simp only [nocompiler_state]; exact h2) (fun q hq => by simp only [nocompiler_state]; exact hpr q hq)
    s1 s2 s3 s4 s5 s6 s7 (fun y hk hm ht ha hxy hpcy hpy => hR y hk hm ht ha hxy hpcy hpy)

theorem fw_src (src l : Word) (j : Nat) (hj : j < l.toNat) :
    src - BitVec.ofNat 64 (j + 1) + l + 1#64 = src + BitVec.ofNat 64 (l.toNat - j) := by bv_omega

theorem fw_j (j : Nat) (hj : j < 2 ^ 62) : BitVec.ofNat 64 (j + 1) + 18446744073709551615#64 = BitVec.ofNat 64 j := by
  bv_omega

/-- After `f->write` returned `i` or more: the rest (`j` bytes from `src + i`) into the buffer by `fw_tail`. -/
theorem fw_after_ge (s : State) (k : Kern) (D : Dom) (hD : __fwritex_dom.sub D) (he : Entry D 0x11fe8#64 s)
    (hM : VerifiedProc img memcpy_dom 0x125dc#64 memcpySpec)
    (hrd : ∀ o, 8 ≤ o → o ≤ 56 → k.perm.canRead (s.reg 2 - BitVec.ofNat 64 o) 8)
    (f src l : Word) (j : Nat) (hj : j < l.toNat) (hl : l.toNat < 2 ^ 62) (w : State)
    (hb : FwBack s f src l (BitVec.ofNat 64 (l.toNat - j)) j w)
    (hge : (w.reg 10).ult (BitVec.ofNat 64 (l.toNat - j)) = false)
    (hmr : k.perm.canRead (src + BitVec.ofNat 64 (l.toNat - j)) j)
    (hmw : k.perm.canWrite (read64 w.mem (f + 40#64)) j)
    (hmd : (Region.mk (read64 w.mem (f + 40#64)) j).Disjoint ⟨src + BitVec.ofNat 64 (l.toNat - j), j⟩)
    (hdS : (Region.mk (read64 w.mem (f + 40#64)) j).Disjoint ⟨s.reg 2 - 64#64, 64⟩)
    (hdF : (Region.mk (read64 w.mem (f + 40#64)) j).Disjoint ⟨f + 40#64, 8⟩)
    (hFS : (Region.mk (f + 40#64) 8).Disjoint ⟨s.reg 2 - 64#64, 64⟩)
    (hr40 : k.perm.canRead (f + 40#64) 8) (hw40 : k.perm.canWrite (f + 40#64) 8) (al40 : aligned (f + 40#64) 8)
    (R : State × Kern → Prop)
    (hR : ∀ y : State × Kern, y.2 = k → y.1.trace = w.trace →
      y.1.reg 10 = BitVec.ofNat 64 (l.toNat - j) + BitVec.ofNat 64 j →
      (∀ p, ¬ (Region.mk (read64 w.mem (f + 40#64)) j).mem p → ¬ (Region.mk (f + 40#64) 8).mem p → y.1.mem p = w.mem p) →
      readBytes y.1.mem (read64 w.mem (f + 40#64)) j = readBytes w.mem (src + BitVec.ofNat 64 (l.toNat - j)) j →
      read64 y.1.mem (f + 40#64) = read64 w.mem (f + 40#64) + BitVec.ofNat 64 j →
      y.1.exit = none → y.1.pc = s.reg 1 → Preserved s y.1 → R y) :
    PReachK img D (fun y => Final D y.1 ∧ R y) (w, k) := by
  obtain ⟨hpc, hx, h2, h8, h9, h18, h19, h20, h21, hpr, s1, s2, s3, s4, s5, s6, s7⟩ := hb
  have hjn : (BitVec.ofNat 64 j).toNat = j := by rw [BitVec.toNat_ofNat]; omega
  nocompiler_wstepD hD [hx, hpc, h19, hge]
  nocompiler_wstepD hD [hx, h8, al40]
  refine ⟨hr40, ?_⟩
  nocompiler_wstepD hD [hx, h21, h9]
  nocompiler_wstepD hD [hx, h20, fw_j j (by omega)]
  nocompiler_wstepD hD [hx, fw_src src l j hj]
  nocompiler_wstepD hD [hx]
  refine fw_tail s k D hD he hM hrd f (read64 w.mem (f + 40#64)) (src + BitVec.ofNat 64 (l.toNat - j))
    (BitVec.ofNat 64 j) (BitVec.ofNat 64 (l.toNat - j)) (by rw [hjn]; exact hmr) (by rw [hjn]; exact hmw)
    (by rw [hjn]; exact hmd) (by rw [hjn]; exact hdS) (by rw [hjn]; exact hdF) hFS hr40 hw40 al40 R _
    (by simp only [nocompiler_state]) (by simp only [nocompiler_state]; exact hx) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h2
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h8
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h19
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      (simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact hpr _ (by simp))
  · simp only [nocompiler_state]; exact s1
  · simp only [nocompiler_state]; exact s2
  · simp only [nocompiler_state]; exact s3
  · simp only [nocompiler_state]; exact s4
  · simp only [nocompiler_state]; exact s5
  · simp only [nocompiler_state]; exact s6
  · simp only [nocompiler_state]; exact s7
  · intro y hk ht ha hm hbs h40 hxy hpcy hpy
    refine hR y hk (by rw [ht]; simp only [nocompiler_state]) ha ?_ ?_ ?_ hxy hpcy hpy
    · intro p hp1 hp2; rw [hm p (by rw [hjn]; exact hp1) hp2]; simp only [nocompiler_state]
    · rw [hjn] at hbs; rw [hbs]; simp only [nocompiler_state]
    · rw [h40]; simp only [nocompiler_state]

/-- `__towrite` in this image, from the library's (over its own words, Examples/Libc/Musl/Small.lean). -/
theorem __towrite_proc : VerifiedProc img __towrite_dom __towrite_entry Towrite.towriteSpec.toPns := by
  have hv := VerifiedImg.toProcNoSys Towrite.__towrite_verified (noEcall_of (by decide +kernel))
  have e : TowriteImg.img = Code.ofChunks 0x121f0#64 TowriteImg.chunks := rfl
  rw [e] at hv
  refine VerifiedProc.of_code_eq hv fun x hx => ?_
  exact Code.instr_eq_of_chunks (k1 := 5) (k2 := 0) chunks_contig rfl chunks_bound TowriteImg.chunks_contig rfl
    TowriteImg.chunks_bound rfl rfl (by decide) x
      (by have e : [TowriteImg.chunk_0.range 0x121f0#64] = __towrite_dom := by decide
          rw [e]; exact hx)

/-- The state at `__fwritex`'s tail call `f->write(f, src, l)` (jr t1 at 0x12058): the frame popped, the saved
    registers back, ra the caller's; memory and trace as at 0x12028. -/
def FwTailCall (s u : State) (e f src l : Word) (z : State) : Prop :=
  z.pc = e ∧ z.exit = none ∧ z.reg 1 = s.reg 1 ∧ z.reg 10 = f ∧ z.reg 11 = src ∧ z.reg 12 = l ∧
  (∀ q ∈ preservedRegs, z.reg q = s.reg q) ∧ z.mem = u.mem ∧ z.trace = u.trace

theorem fw_tcallz (s : State) (k : Kern) (D : Dom) (u : State) (e f src l : Word)
    (Wr : SpecP (Word × Word × Word)) (De : Dom) (hWr : VerifiedProc img De e Wr) (hDe : De.sub D)
    (hret : ¬ De.mem (s.reg 1)) (hra4 : aligned (s.reg 1) 4) (hsp16 : aligned (s.reg 2) 16)
    (R : State × Kern → Prop)
    (hpre : ∀ z, FwTailCall s u e f src l z → Wr.pre (f, src, l) z k)
    (K : ∀ z, FwTailCall s u e f src l z → ∀ w, Wr.Done (f, src, l) (z, k) w → PReachK img D R w)
    (z : State) (hz : FwTailCall s u e f src l z) : PReachK img D R (z, k) :=
  VerifiedProc.call hWr _ ⟨hz.1, hz.2.1, by rw [Reg.ra, hz.2.2.1]; exact hret, by rw [Reg.ra, hz.2.2.1]; exact hra4,
    by rw [Reg.sp, hz.2.2.2.2.2.2.1 2 (by decide)]; exact hsp16⟩ (hpre _ hz) hDe (K _ hz)

/-- From 0x12028 (l does not fit in the buffer): the tail call of `f->write(f, src, l)`. -/
theorem fw_tailcall (s : State) (k : Kern) (D : Dom) (hD : __fwritex_dom.sub D) (he : Entry D 0x11fe8#64 s)
    (hrd : ∀ o, 8 ≤ o → o ≤ 56 → k.perm.canRead (s.reg 2 - BitVec.ofNat 64 o) 8)
    (f src l : Word) (m : Word → Byte)
    (Wr : SpecP (Word × Word × Word)) (e : Word) (De : Dom) (hWr : VerifiedProc img De e Wr) (hDe : De.sub D)
    (hret : ¬ De.mem (s.reg 1)) (he4 : aligned e 4)
    (hr72 : k.perm.canRead (f + 72#64) 8) (al72 : aligned (f + 72#64) 8) (he72 : read64 m (f + 72#64) = e)
    (R : State × Kern → Prop) (u : State) (hpc : u.pc = 0x12028#64) (hx : u.exit = none)
    (h2 : u.reg 2 = s.reg 2 - 64#64) (h8 : u.reg 8 = f) (h9 : u.reg 9 = l) (h18 : u.reg 18 = src) (hm : u.mem = m)
    (hpr : ∀ q ∈ [(3 : Reg), 4, 22, 23, 24, 25, 26, 27], u.reg q = s.reg q)
    (s1 : read64 m (s.reg 2 - 8#64) = s.reg 1) (s2 : read64 m (s.reg 2 - 16#64) = s.reg 8)
    (s3 : read64 m (s.reg 2 - 24#64) = s.reg 9) (s4 : read64 m (s.reg 2 - 32#64) = s.reg 18)
    (s5 : read64 m (s.reg 2 - 40#64) = s.reg 19) (s6 : read64 m (s.reg 2 - 48#64) = s.reg 20)
    (s7 : read64 m (s.reg 2 - 56#64) = s.reg 21)
    (hpre : ∀ z, FwTailCall s u e f src l z → Wr.pre (f, src, l) z k)
    (K : ∀ z, FwTailCall s u e f src l z → ∀ w, Wr.Done (f, src, l) (z, k) w → PReachK img D R w) :
    PReachK img D R (u, k) := by
  have hsp := he.sp
  have hra4 := he.retAligned
  simp only [Reg.sp, Reg.ra] at hsp hra4
  have eS : ∀ o, o ≤ 64 → s.reg 2 - 64#64 + BitVec.ofNat 64 o = s.reg 2 - BitVec.ofNat 64 (64 - o) := by
    intro o ho; bv_omega
  have e64 : s.reg 2 - 64#64 + 64#64 = s.reg 2 := by bv_omega
  nocompiler_wstepD hD [hx, hpc, h8, al72, hm, he72]
  refine ⟨hr72, ?_⟩
  nocompiler_wstepD hD [hx, h8]
  nocompiler_wstepD hD [hx, h18]
  nocompiler_wstepD hD [hx, h9]
  nocompiler_wstepD hD [hx, h2, eS 56 (by omega), sw_alS hsp 8 rfl, hm, s1]
  refine ⟨hrd 8 (by omega) (by omega), ?_⟩
  nocompiler_wstepD hD [hx, h2, eS 48 (by omega), sw_alS hsp 16 rfl, hm, s2]
  refine ⟨hrd 16 (by omega) (by omega), ?_⟩
  nocompiler_wstepD hD [hx, h2, eS 40 (by omega), sw_alS hsp 24 rfl, hm, s3]
  refine ⟨hrd 24 (by omega) (by omega), ?_⟩
  nocompiler_wstepD hD [hx, h2, eS 32 (by omega), sw_alS hsp 32 rfl, hm, s4]
  refine ⟨hrd 32 (by omega) (by omega), ?_⟩
  nocompiler_wstepD hD [hx, h2, eS 24 (by omega), sw_alS hsp 40 rfl, hm, s5]
  refine ⟨hrd 40 (by omega) (by omega), ?_⟩
  nocompiler_wstepD hD [hx, h2, eS 16 (by omega), sw_alS hsp 48 rfl, hm, s6]
  refine ⟨hrd 48 (by omega) (by omega), ?_⟩
  nocompiler_wstepD hD [hx, h2, eS 8 (by omega), sw_alS hsp 56 rfl, hm, s7]
  refine ⟨hrd 56 (by omega) (by omega), ?_⟩
  nocompiler_wstepD hD [hx, h2, e64]
  nocompiler_wstepD hD [hx, ret_mask he4, he4]
  refine fw_tcallz s k D u e f src l Wr De hWr hDe hret hra4 hsp R hpre K _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [nocompiler_state]
  · simp only [nocompiler_state]; exact hx
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · intro q hq
    simp only [preservedRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals (simp (disch := nocompiler_decide_closed) only [nocompiler_state])
    all_goals (exact hpr _ (by simp))
  · simp only [nocompiler_state]
  · simp only [nocompiler_state]

/-- From 0x1201c (a2 = f->wend): l does not fit (to the tail call at 0x12028), else unbuffered (lbf < 0, to the
    copy at 0x120dc), else the '\n' scan (0x12070, nothing scanned). -/
theorem fw_mid (s : State) (k : Kern) (D : Dom) (hD : __fwritex_dom.sub D) (f src l : Word) (m : Word → Byte)
    (hr40 : k.perm.canRead (f + 40#64) 8) (al40 : aligned (f + 40#64) 8)
    (hr144 : k.perm.canRead (f + 144#64) 4) (al144 : aligned (f + 144#64) 4)
    (R : State × Kern → Prop) (u : State) (hpc : u.pc = 0x1201c#64) (hkeep : FwKeep s f src l m u)
    (h12 : u.reg 12 = read64 m (f + 32#64))
    (K1 : ∀ u', u'.pc = 0x12028#64 → FwKeep s f src l m u' →
      (read64 m (f + 32#64) - read64 m (f + 40#64)).ult l = true → PReachK img D R (u', k))
    (K2 : ∀ u', u'.pc = 0x120dc#64 → FwKeep s f src l m u' → u'.reg 10 = read64 m (f + 40#64) →
      (read64 m (f + 32#64) - read64 m (f + 40#64)).ult l = false →
      BitVec.slt ((BitVec.ofNat 32 (readLE m (f + 144#64) 4)).signExtend 64) 0 = true → PReachK img D R (u', k))
    (K3 : ∀ u', u'.pc = 0x12070#64 → FwKeep s f src l m u' → u'.reg 10 = read64 m (f + 40#64) →
      (read64 m (f + 32#64) - read64 m (f + 40#64)).ult l = false →
      BitVec.slt ((BitVec.ofNat 32 (readLE m (f + 144#64) 4)).signExtend 64) 0 = false →
      u'.reg 20 = 0#64 → u'.reg 21 = src → u'.reg 11 = 10#64 → PReachK img D R (u', k)) :
    PReachK img D R (u, k) := by
  have hk := hkeep
  obtain ⟨hx, h2, h8, h9, h18, hm, hpr, htr⟩ := hk
  have keep : ∀ v : State, v.exit = none → v.reg 2 = u.reg 2 → v.reg 8 = u.reg 8 → v.reg 9 = u.reg 9 →
      v.reg 18 = u.reg 18 → v.mem = u.mem → (∀ q ∈ [(3 : Reg), 4, 22, 23, 24, 25, 26, 27], v.reg q = u.reg q) →
      v.trace = u.trace → FwKeep s f src l m v := by
    intro v a b c d e g h i
    exact ⟨a, b ▸ h2, c ▸ h8, d ▸ h9, e ▸ h18, g ▸ hm, fun q hq => (h q hq).trans (hpr q hq), i ▸ htr⟩
  nocompiler_wstepD hD [hx, hpc, h8, al40, hm]
  refine ⟨hr40, ?_⟩
  nocompiler_wstepD hD [hx, h12]
  by_cases hfit : (read64 m (f + 32#64) - read64 m (f + 40#64)).ult l = true
  · have hb : (!(read64 m (f + 32#64) - read64 m (f + 40#64)).ult l) = false := by simp [hfit]
    nocompiler_wstepD hD [hx, h9, hb]
    refine K1 _ (by simp only [nocompiler_state]) ?_ hfit
    apply keep <;> simp (disch := nocompiler_decide_closed) only [nocompiler_state]
    · exact hx
    · intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · have hfit' : (read64 m (f + 32#64) - read64 m (f + 40#64)).ult l = false := by simpa using hfit
    have hb : (!(read64 m (f + 32#64) - read64 m (f + 40#64)).ult l) = true := by simp [hfit']
    nocompiler_wstepD hD [hx, h9, hb]
    nocompiler_wstepD hD [hx, h8, al144, hm]
    refine ⟨hr144, ?_⟩
    by_cases hlbf : BitVec.slt ((BitVec.ofNat 32 (readLE m (f + 144#64) 4)).signExtend 64) 0 = true
    · nocompiler_wstepD hD [hx, hlbf]
      refine K2 _ (by simp only [nocompiler_state]) ?_ (by simp (disch := nocompiler_decide_closed) only [nocompiler_state]) hfit' hlbf
      apply keep <;> simp (disch := nocompiler_decide_closed) only [nocompiler_state]
      · exact hx
      · intro q hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp (disch := nocompiler_decide_closed) only [nocompiler_state]
    · have hlbf' : BitVec.slt ((BitVec.ofNat 32 (readLE m (f + 144#64) 4)).signExtend 64) 0 = false := by simpa using hlbf
      nocompiler_wstepD hD [hx, hlbf']
      nocompiler_wstepD hD [hx]
      nocompiler_wstepD hD [hx]
      nocompiler_wstepD hD [hx, h18]
      refine K3 _ (by simp only [nocompiler_state]) ?_ (by simp (disch := nocompiler_decide_closed) only [nocompiler_state])
        hfit' hlbf' (by simp (disch := nocompiler_decide_closed) only [nocompiler_state]; rfl)
        (by simp (disch := nocompiler_decide_closed) only [nocompiler_state])
        (by simp (disch := nocompiler_decide_closed) only [nocompiler_state])
      apply keep <;> simp (disch := nocompiler_decide_closed) only [nocompiler_state]
      · exact hx
      · intro q hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp (disch := nocompiler_decide_closed) only [nocompiler_state]

/-- The seven saved registers in `__fwritex`'s frame (below the entry sp `s.reg 2`). -/
def FwSlots (s : State) (m : Word → Byte) : Prop :=
  read64 m (s.reg 2 - 8#64) = s.reg 1 ∧ read64 m (s.reg 2 - 16#64) = s.reg 8 ∧
  read64 m (s.reg 2 - 24#64) = s.reg 9 ∧ read64 m (s.reg 2 - 32#64) = s.reg 18 ∧
  read64 m (s.reg 2 - 40#64) = s.reg 19 ∧ read64 m (s.reg 2 - 48#64) = s.reg 20 ∧
  read64 m (s.reg 2 - 56#64) = s.reg 21

theorem fw_slot_same {sp : Word} (o : Nat) (m : Word → Byte) (v : Word) :
    read64 (writeLE m (sp - BitVec.ofNat 64 o) v.toNat 8) (sp - BitVec.ofNat 64 o) = v := by
  rw [Auto.read64_writeLE_same', BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem file32_after_slot {f sp : Word} (hFS : (Region.mk (f + 32#64) 8).Disjoint ⟨sp - 64#64, 64⟩) (a : Nat)
    (h : (decide (8 ≤ a) && decide (a ≤ 64)) = true) (m : Word → Byte) (v : Nat) :
    read64 (writeLE m (sp - BitVec.ofNat 64 a) v 8) (f + 32#64) = read64 m (f + 32#64) := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact Auto.read64_writeLE_of_disjoint (R := ⟨sp - BitVec.ofNat 64 a, 8⟩)
    (by simp only [Region.Disjoint] at *; bv_omega) _ _ _ _ (by simp [Region.covers])

theorem writeLE_slot64_out {sp p : Word} (hp : ¬ (Region.mk (sp - 64#64) 64).mem p) (a : Nat)
    (h : (decide (8 ≤ a) && decide (a ≤ 64)) = true) (m : Word → Byte) (v : Nat) :
    writeLE m (sp - BitVec.ofNat 64 a) v 8 p = m p := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact writeLE_of_not_mem (r := ⟨sp - 64#64, 64⟩) (by simp only [Region.covers]; bv_omega) hp

theorem fw_entry_k (s : State) (k : Kern) (D : Dom) (f src l : Word) (R : State × Kern → Prop)
    (Kd : ∀ (m : Word → Byte) (u : State), (∀ p, ¬ (Region.mk (s.reg 2 - 64#64) 64).mem p → m p = s.mem p) →
      FwSlots s m → u.pc = 0x1201c#64 → FwKeep s f src l m u → u.reg 12 = read64 m (f + 32#64) →
      u.trace = s.trace → PReachK img D R (u, k))
    (u : State) (hpc : u.pc = 0x1201c#64) (hx : u.exit = none) (h2 : u.reg 2 = s.reg 2 - 64#64) (h8 : u.reg 8 = f)
    (h9 : u.reg 9 = l) (h18 : u.reg 18 = src) (hpr : ∀ q ∈ [(3 : Reg), 4, 22, 23, 24, 25, 26, 27], u.reg q = s.reg q)
    (hfr : ∀ p, ¬ (Region.mk (s.reg 2 - 64#64) 64).mem p → u.mem p = s.mem p) (hsl : FwSlots s u.mem)
    (h12 : u.reg 12 = read64 u.mem (f + 32#64)) (htr : u.trace = s.trace) : PReachK img D R (u, k) :=
  Kd u.mem u hfr hsl hpc ⟨hx, h2, h8, h9, h18, rfl, hpr, htr⟩ h12 htr

/-- `__fwritex`'s entry block: the seven saves, the arguments moved (s0 = f, s1 = l, s2 = s), f->wend loaded;
    on to 0x1201c directly when wend is set. (The `__towrite` path is the next lemma.) -/
theorem fw_entry_direct (s : State) (k : Kern) (D : Dom) (hD : __fwritex_dom.sub D) (he : Entry D 0x11fe8#64 s)
    (src l f : Word) (ha0 : s.reg 10 = src) (ha1 : s.reg 11 = l) (ha2 : s.reg 12 = f)
    (hwS : ∀ o, 8 ≤ o → o ≤ 56 → k.perm.canWrite (s.reg 2 - BitVec.ofNat 64 o) 8)
    (hr32 : k.perm.canRead (f + 32#64) 8) (al32 : aligned (f + 32#64) 8)
    (hFS : (Region.mk (f + 32#64) 8).Disjoint ⟨s.reg 2 - 64#64, 64⟩)
    (hwend : read64 s.mem (f + 32#64) ≠ 0#64)
    (R : State × Kern → Prop)
    (Kd : ∀ (m : Word → Byte) (u : State), (∀ p, ¬ (Region.mk (s.reg 2 - 64#64) 64).mem p → m p = s.mem p) →
      FwSlots s m → u.pc = 0x1201c#64 → FwKeep s f src l m u → u.reg 12 = read64 m (f + 32#64) →
      u.trace = s.trace → PReachK img D R (u, k)) :
    PReachK img D R (s, k) := by
  have hpc := he.pc
  have hx := he.live
  have hsp := he.sp
  simp only [Reg.sp] at hsp
  have e96 : s.reg 2 + 18446744073709551552#64 = s.reg 2 - 64#64 := by bv_omega
  have eS : ∀ o, o ≤ 64 → s.reg 2 - 64#64 + BitVec.ofNat 64 o = s.reg 2 - BitVec.ofNat 64 (64 - o) := by
    intro o ho; bv_omega
  have fs := file32_after_slot hFS
  have hw0 : ¬ read64 s.mem (f + 32#64) = 0 := hwend
  nocompiler_wstepD hD [hx, hpc, e96]
  nocompiler_wstepD hD [hx, eS 56 (by omega), sw_alS hsp 8 rfl]
  refine ⟨hwS 8 (by omega) (by omega), ?_⟩
  nocompiler_wstepD hD [hx, eS 48 (by omega), sw_alS hsp 16 rfl]
  refine ⟨hwS 16 (by omega) (by omega), ?_⟩
  nocompiler_wstepD hD [hx, eS 40 (by omega), sw_alS hsp 24 rfl]
  refine ⟨hwS 24 (by omega) (by omega), ?_⟩
  nocompiler_wstepD hD [hx, eS 32 (by omega), sw_alS hsp 32 rfl]
  refine ⟨hwS 32 (by omega) (by omega), ?_⟩
  nocompiler_wstepD hD [hx, eS 24 (by omega), sw_alS hsp 40 rfl]
  refine ⟨hwS 40 (by omega) (by omega), ?_⟩
  nocompiler_wstepD hD [hx, eS 16 (by omega), sw_alS hsp 48 rfl]
  refine ⟨hwS 48 (by omega) (by omega), ?_⟩
  nocompiler_wstepD hD [hx, eS 8 (by omega), sw_alS hsp 56 rfl]
  refine ⟨hwS 56 (by omega) (by omega), ?_⟩
  nocompiler_wstepD hD [hx, ha2]
  nocompiler_wstepD hD [hx, ha2, al32]
  refine ⟨hr32, ?_⟩
  nocompiler_wstepD hD [hx, ha1]
  nocompiler_wstepD hD [hx, ha0]
  nocompiler_wstepD hD [hx, fs, hw0, beq_iff_eq, Bool.false_eq_true, ↓reduceIte]
  refine fw_entry_k s k D f src l R Kd _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [nocompiler_state]
  · simp only [nocompiler_state]; exact hx
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · intro p hp
    simp (disch := nocompiler_decide_closed) only [nocompiler_state, writeLE_slot64_out hp]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp (disch := nocompiler_decide_closed) only [nocompiler_state, slot_ne, fw_slot_same]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state, fs]
  · simp only [nocompiler_state]

/-- After `__towrite` returned to 0x120c8 with `r`: nonzero returns 0 (fw_epi), else f->wend reloaded and on to
    0x1201c. -/
theorem fw_twret (s : State) (k : Kern) (D : Dom) (hD : __fwritex_dom.sub D) (he : Entry D 0x11fe8#64 s)
    (hrd : ∀ o, 8 ≤ o → o ≤ 56 → k.perm.canRead (s.reg 2 - BitVec.ofNat 64 o) 8)
    (f src l : Word) (hr32 : k.perm.canRead (f + 32#64) 8) (al32 : aligned (f + 32#64) 8)
    (R : State × Kern → Prop) (w : State) (hpc : w.pc = 0x120c8#64) (hx : w.exit = none)
    (h2 : w.reg 2 = s.reg 2 - 64#64) (h8 : w.reg 8 = f) (h9 : w.reg 9 = l) (h18 : w.reg 18 = src)
    (hpr : ∀ q ∈ [(3 : Reg), 4, 22, 23, 24, 25, 26, 27], w.reg q = s.reg q) (hsl : FwSlots s w.mem)
    (htw : w.trace = s.trace)
    (hR0 : w.reg 10 ≠ 0 → ∀ y : State × Kern, y.2 = k → y.1.mem = w.mem → y.1.trace = w.trace →
      y.1.reg 10 = 0 → y.1.exit = none → y.1.pc = s.reg 1 → Preserved s y.1 → R y)
    (Kt : w.reg 10 = 0 → ∀ u : State, u.pc = 0x1201c#64 → FwKeep s f src l w.mem u →
      u.reg 12 = read64 w.mem (f + 32#64) → u.trace = w.trace → PReachK img D (fun y => Final D y.1 ∧ R y) (u, k)) :
    PReachK img D (fun y => Final D y.1 ∧ R y) (w, k) := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := hsl
  nocompiler_wstepD hD [hx, hpc]
  nocompiler_wstepD hD [hx]
  by_cases hr : w.reg 10 = 0
  · have hb : (w.reg 10 != 0) = false := by rw [hr]; rfl
    nocompiler_wstepD hD [hx, hb]
    nocompiler_wstepD hD [hx, h8, al32]
    refine ⟨hr32, ?_⟩
    nocompiler_wstepD hD [hx]
    refine Kt hr _ (by simp only [nocompiler_state]) ⟨by simp only [nocompiler_state]; exact hx, ?_, ?_, ?_, ?_,
      by simp only [nocompiler_state], ?_, ?_⟩ ?_ (by simp only [nocompiler_state])
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h2
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h8
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h9
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h18
    · intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        (simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact hpr _ (by simp))
    · simp only [nocompiler_state]; exact htw
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · have hb : (w.reg 10 != 0) = true := by simpa using hr
    nocompiler_wstepD hD [hx, hb]
    refine fw_epi s k D hD he hrd R _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp only [nocompiler_state]
    · simp only [nocompiler_state]; exact hx
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h2
    · intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        (simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact hpr _ (by simp))
    · simp only [nocompiler_state]; exact s1
    · simp only [nocompiler_state]; exact s2
    · simp only [nocompiler_state]; exact s3
    · simp only [nocompiler_state]; exact s4
    · simp only [nocompiler_state]; exact s5
    · simp only [nocompiler_state]; exact s6
    · simp only [nocompiler_state]; exact s7
    · intro y hk hm ht ha hxy hpcy hpy
      exact hR0 hr y hk (by rw [hm]; simp only [nocompiler_state]) (by rw [ht]; simp only [nocompiler_state])
        (by rw [ha]; simp (disch := nocompiler_decide_closed) only [nocompiler_state]) hxy hpcy hpy

/-- A byte of `__fwritex`'s frame is not one `__towrite` may write (FILE's first 144 bytes, no stack). -/
theorem fw_tw_notw {s z : State} {f p : Word} (hF : (Region.mk f 144).Disjoint ⟨s.reg 2 - 64#64, 64⟩)
    (hp : (Region.mk (s.reg 2 - 64#64) 64).mem p) : ¬ (Towrite.towriteSpec.perm f z).writable p := by
  rintro ⟨r, hr, hm⟩
  simp only [Spec.perm, Towrite.towriteSpec, Spec.stackRegion, List.cons_append, List.nil_append, List.mem_cons,
    List.mem_singleton, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · simp only [Region.Disjoint, Region.mem] at hF hp hm; bv_omega
  · simp only [Region.Disjoint, Region.mem] at hF hp hm; bv_omega
  · simp only [Region.mem] at hm; omega

/-- The call of `__towrite` from 0x120c0 (state `z`), and on from its return by fw_twret. -/
theorem fw_twz (s : State) (k : Kern) (D : Dom) (hD : __fwritex_dom.sub D) (he : Entry D 0x11fe8#64 s)
    (hrd : ∀ o, 8 ≤ o → o ≤ 56 → k.perm.canRead (s.reg 2 - BitVec.ofNat 64 o) 8)
    (f src l : Word) (hal : aligned f 8) (hr32 : k.perm.canRead (f + 32#64) 8) (al32 : aligned (f + 32#64) 8)
    (hF : (Region.mk f 144).Disjoint ⟨s.reg 2 - 64#64, 64⟩) (htwp : ∀ z : State, z.reg 2 = s.reg 2 - 64#64 → (Towrite.towriteSpec.perm f z).le k.perm)
    (R : State × Kern → Prop) (z : State) (hpc : z.pc = 0x121f0#64) (hx : z.exit = none)
    (hra : z.reg 1 = 0x120c8#64) (h10 : z.reg 10 = f)
    (h2 : z.reg 2 = s.reg 2 - 64#64) (h8 : z.reg 8 = f) (h9 : z.reg 9 = l) (h18 : z.reg 18 = src)
    (hpr : ∀ q ∈ [(3 : Reg), 4, 22, 23, 24, 25, 26, 27], z.reg q = s.reg q) (hsl : FwSlots s z.mem)
    (htz : z.trace = s.trace)
    (hR0 : ∀ w : State, Towrite.towriteSpec.post f z w → w.reg 10 ≠ 0 → ∀ y : State × Kern, y.2 = k → y.1.mem = w.mem →
      y.1.trace = z.trace → y.1.reg 10 = 0 → y.1.exit = none → y.1.pc = s.reg 1 → Preserved s y.1 → R y)
    (Kt : ∀ w : State, Towrite.towriteSpec.post f z w → w.reg 10 = 0 →
      (∀ p, ¬ (Region.mk f 140).mem p → w.mem p = z.mem p) → ∀ u : State, u.pc = 0x1201c#64 →
      FwKeep s f src l w.mem u → u.reg 12 = read64 w.mem (f + 32#64) → u.trace = z.trace →
      PReachK img D (fun y => Final D y.1 ∧ R y) (u, k)) :
    PReachK img D (fun y => Final D y.1 ∧ R y) (z, k) := by
  have hsp := he.sp
  simp only [Reg.sp] at hsp
  refine VerifiedProc.call __towrite_proc f ⟨hpc, hx, by rw [Reg.ra, hra]; decide, by rw [Reg.ra, hra]; decide,
    by rw [Reg.sp, h2]; unfold aligned at *; bv_omega⟩ ⟨⟨h10, hal⟩, htwp z h2⟩
    (fun x hx => hD x (Dom.sub_of_ranges (by decide) x hx)) ?_
  rintro ⟨w, kw⟩ (⟨hxw, hpcw, hpresw, hpost, hk, htr, hfr⟩ | ⟨_, hex, _⟩)
  rotate_left
  · exact hex.elim
  simp only at hxw hpcw hpresw hpost hk htr hfr
  rw [hk]
  have hwr : ∀ q ∈ preservedRegs, w.reg q = z.reg q := fun q hq => hpresw q hq
  have hslot : ∀ a, (Region.mk (s.reg 2 - 64#64) 64).covers a 8 → read64 w.mem a = read64 z.mem a := by
    intro a ha
    apply read64_congr_on; intro j hj
    apply hfr
    apply fw_tw_notw hF
    simp only [Region.covers, Region.mem] at *; bv_omega
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := hsl
  have cv : ∀ o, 8 ≤ o → o ≤ 56 → (Region.mk (s.reg 2 - 64#64) 64).covers (s.reg 2 - BitVec.ofNat 64 o) 8 := by
    intro o h1 h3; simp only [Region.covers]; bv_omega
  refine fw_twret s k D hD he hrd f src l hr32 al32 R w (by rw [hpcw, Reg.ra, hra]) hxw
    (by rw [hwr 2 (by decide), h2]) (by rw [hwr 8 (by decide), h8]) (by rw [hwr 9 (by decide), h9])
    (by rw [hwr 18 (by decide), h18]) (fun q hq => by rw [hwr q (by revert hq; revert q; decide), hpr q hq])
    ⟨by rw [hslot _ (cv 8 (by omega) (by omega))]; exact s1, by rw [hslot _ (cv 16 (by omega) (by omega))]; exact s2,
     by rw [hslot _ (cv 24 (by omega) (by omega))]; exact s3, by rw [hslot _ (cv 32 (by omega) (by omega))]; exact s4,
     by rw [hslot _ (cv 40 (by omega) (by omega))]; exact s5, by rw [hslot _ (cv 48 (by omega) (by omega))]; exact s6,
     by rw [hslot _ (cv 56 (by omega) (by omega))]; exact s7⟩ (by rw [htr, htz])
    (fun hr y hk' hm ht ha hxy hpcy hpy => hR0 w hpost hr y hk' hm (by rw [ht, htr]) ha hxy hpcy hpy)
    (fun hr u hpcu hku h12 htu => Kt w hpost hr (fun p hp => hfr p (by
      rintro ⟨r, hr', hm⟩
      simp only [Spec.perm, Towrite.towriteSpec, Spec.stackRegion, List.cons_append, List.nil_append, List.mem_cons,
        List.mem_singleton, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl
      · exact hp (by simp only [Region.mem] at hm ⊢; omega)
      · exact hp (by simp only [Region.mem] at hm ⊢; bv_omega)
      · simp only [Region.mem] at hm; omega)) u hpcu hku h12 (by rw [htu, htr]))

/-- What `__fwritex`'s entry block establishes at the `__towrite` call (0x121f0, returning to 0x120c8). -/
def FwTwCall (s : State) (f src l : Word) (z : State) : Prop :=
  z.pc = 0x121f0#64 ∧ z.exit = none ∧ z.reg 1 = 0x120c8#64 ∧ z.reg 10 = f ∧ z.reg 2 = s.reg 2 - 64#64 ∧
  z.reg 8 = f ∧ z.reg 9 = l ∧ z.reg 18 = src ∧ (∀ q ∈ [(3 : Reg), 4, 22, 23, 24, 25, 26, 27], z.reg q = s.reg q) ∧
  FwSlots s z.mem ∧ (∀ p, ¬ (Region.mk (s.reg 2 - 64#64) 64).mem p → z.mem p = s.mem p) ∧ z.trace = s.trace

theorem fw_entry_twk (s : State) (k : Kern) (D : Dom) (hD : __fwritex_dom.sub D) (he : Entry D 0x11fe8#64 s)
    (hrd : ∀ o, 8 ≤ o → o ≤ 56 → k.perm.canRead (s.reg 2 - BitVec.ofNat 64 o) 8)
    (f src l : Word) (hal : aligned f 8) (hr32 : k.perm.canRead (f + 32#64) 8) (al32 : aligned (f + 32#64) 8)
    (hF : (Region.mk f 144).Disjoint ⟨s.reg 2 - 64#64, 64⟩) (htwp : ∀ z : State, z.reg 2 = s.reg 2 - 64#64 → (Towrite.towriteSpec.perm f z).le k.perm)
    (R : State × Kern → Prop)
    (hR0 : ∀ z, FwTwCall s f src l z → ∀ w : State, Towrite.towriteSpec.post f z w → w.reg 10 ≠ 0 → ∀ y : State × Kern,
      y.2 = k → y.1.mem = w.mem → y.1.trace = z.trace → y.1.reg 10 = 0 → y.1.exit = none → y.1.pc = s.reg 1 →
      Preserved s y.1 → R y)
    (Kt : ∀ z, FwTwCall s f src l z → ∀ w : State, Towrite.towriteSpec.post f z w → w.reg 10 = 0 →
      (∀ p, ¬ (Region.mk f 140).mem p → w.mem p = z.mem p) → ∀ u : State, u.pc = 0x1201c#64 →
      FwKeep s f src l w.mem u → u.reg 12 = read64 w.mem (f + 32#64) → u.trace = z.trace →
      PReachK img D (fun y => Final D y.1 ∧ R y) (u, k))
    (z : State) (hz : FwTwCall s f src l z) : PReachK img D (fun y => Final D y.1 ∧ R y) (z, k) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := hz
  exact fw_twz s k D hD he hrd f src l hal hr32 al32 hF htwp R z a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a12
    (hR0 z ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩) (Kt z ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩)

/-- `__fwritex`'s entry block when f->wend is 0: the saves, then the call of `__towrite`. -/
theorem fw_entry_tw (s : State) (k : Kern) (D : Dom) (hD : __fwritex_dom.sub D) (he : Entry D 0x11fe8#64 s)
    (hrd : ∀ o, 8 ≤ o → o ≤ 56 → k.perm.canRead (s.reg 2 - BitVec.ofNat 64 o) 8)
    (src l f : Word) (ha0 : s.reg 10 = src) (ha1 : s.reg 11 = l) (ha2 : s.reg 12 = f) (hal : aligned f 8)
    (hwS : ∀ o, 8 ≤ o → o ≤ 56 → k.perm.canWrite (s.reg 2 - BitVec.ofNat 64 o) 8)
    (hr32 : k.perm.canRead (f + 32#64) 8) (al32 : aligned (f + 32#64) 8)
    (hFS : (Region.mk (f + 32#64) 8).Disjoint ⟨s.reg 2 - 64#64, 64⟩)
    (hF : (Region.mk f 144).Disjoint ⟨s.reg 2 - 64#64, 64⟩) (htwp : ∀ z : State, z.reg 2 = s.reg 2 - 64#64 → (Towrite.towriteSpec.perm f z).le k.perm)
    (hwend : read64 s.mem (f + 32#64) = 0)
    (R : State × Kern → Prop)
    (hR0 : ∀ z, FwTwCall s f src l z → ∀ w : State, Towrite.towriteSpec.post f z w → w.reg 10 ≠ 0 → ∀ y : State × Kern,
      y.2 = k → y.1.mem = w.mem → y.1.trace = z.trace → y.1.reg 10 = 0 → y.1.exit = none → y.1.pc = s.reg 1 →
      Preserved s y.1 → R y)
    (Kt : ∀ z, FwTwCall s f src l z → ∀ w : State, Towrite.towriteSpec.post f z w → w.reg 10 = 0 →
      (∀ p, ¬ (Region.mk f 140).mem p → w.mem p = z.mem p) → ∀ u : State, u.pc = 0x1201c#64 →
      FwKeep s f src l w.mem u → u.reg 12 = read64 w.mem (f + 32#64) → u.trace = z.trace →
      PReachK img D (fun y => Final D y.1 ∧ R y) (u, k)) :
    PReachK img D (fun y => Final D y.1 ∧ R y) (s, k) := by
  have hpc := he.pc
  have hx := he.live
  have hsp := he.sp
  simp only [Reg.sp] at hsp
  have e96 : s.reg 2 + 18446744073709551552#64 = s.reg 2 - 64#64 := by bv_omega
  have eS : ∀ o, o ≤ 64 → s.reg 2 - 64#64 + BitVec.ofNat 64 o = s.reg 2 - BitVec.ofNat 64 (64 - o) := by
    intro o ho; bv_omega
  have fs := file32_after_slot hFS
  nocompiler_wstepD hD [hx, hpc, e96]
  nocompiler_wstepD hD [hx, eS 56 (by omega), sw_alS hsp 8 rfl]
  refine ⟨hwS 8 (by omega) (by omega), ?_⟩
  nocompiler_wstepD hD [hx, eS 48 (by omega), sw_alS hsp 16 rfl]
  refine ⟨hwS 16 (by omega) (by omega), ?_⟩
  nocompiler_wstepD hD [hx, eS 40 (by omega), sw_alS hsp 24 rfl]
  refine ⟨hwS 24 (by omega) (by omega), ?_⟩
  nocompiler_wstepD hD [hx, eS 32 (by omega), sw_alS hsp 32 rfl]
  refine ⟨hwS 32 (by omega) (by omega), ?_⟩
  nocompiler_wstepD hD [hx, eS 24 (by omega), sw_alS hsp 40 rfl]
  refine ⟨hwS 40 (by omega) (by omega), ?_⟩
  nocompiler_wstepD hD [hx, eS 16 (by omega), sw_alS hsp 48 rfl]
  refine ⟨hwS 48 (by omega) (by omega), ?_⟩
  nocompiler_wstepD hD [hx, eS 8 (by omega), sw_alS hsp 56 rfl]
  refine ⟨hwS 56 (by omega) (by omega), ?_⟩
  nocompiler_wstepD hD [hx, ha2]
  nocompiler_wstepD hD [hx, ha2, al32]
  refine ⟨hr32, ?_⟩
  nocompiler_wstepD hD [hx, ha1]
  nocompiler_wstepD hD [hx, ha0]
  nocompiler_wstepD hD [hx, fs, hwend, beq_self_eq_true, ↓reduceIte]
  nocompiler_wstepD hD [hx]
  nocompiler_wstepD hD [hx]
  nocompiler_wstepD hD [hx]
  refine fw_entry_twk s k D hD he hrd f src l hal hr32 al32 hF htwp R hR0 Kt _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [nocompiler_state]
  · simp only [nocompiler_state]; exact hx
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (disch := nocompiler_decide_closed) only [nocompiler_state]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp (disch := nocompiler_decide_closed) only [nocompiler_state, slot_ne, fw_slot_same]
  · intro p hp
    simp (disch := nocompiler_decide_closed) only [nocompiler_state, writeLE_slot64_out hp]
  · simp only [nocompiler_state]

end NoCompiler.Libc.Musl.Fwritex
