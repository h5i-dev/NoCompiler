import Examples.Libc.Musl.StdioWrite1

set_option maxRecDepth 20000
namespace NoCompiler.Libc.Musl.StdioWrite
open NoCompiler NoCompiler.Linux NoCompiler.Libc NoCompiler.Libc.Musl.StdioWriteImg NoCompiler.Libc.Musl.SyscallRet

/-- After a `writev` of `__stdio_write`, from the state `y` at its `auipc` (E + 4) with a0 = `v`: the call of
    `__syscall_ret` and the return to E + 12. -/
theorem sw_retcall (f buf len : Word) (s : State) (k : Kern) (he : Entry dom __stdio_write_entry s)
    (hpre : stdioWriteSpec.pre (f, buf, len) s k)
    (Q : State × Kern → Prop) (E : Word) (hE : E = 0x124dc#64 ∨ E = 0x12558#64)
    (z : State) (hc : SwCommon s f len z) (iovp cnt : Word) (d : Nat) (hiov : IovAt s f buf len z.mem iovp cnt d)
    (v : Word) (y : State) (hpc : y.pc = E + 4#64) (hyx : y.exit = none) (hym : y.mem = z.mem) (hy10 : y.reg 10 = v)
    (hyr : ∀ q ∈ preservedRegs, y.reg q = z.reg q)
    (K : ∀ w : State, w.pc = E + 12#64 → SwCommon s f len w → (∀ q ∈ [(18 : Reg), 19, 20, 21], w.reg q = z.reg q) →
      IovAt s f buf len w.mem iovp cnt d → w.reg 10 = (if v.toNat < 2 ^ 64 - 4095 then v else -1) →
      w.trace = y.trace → PReachK img dom Q (w, k)) :
    PReachK img dom Q (y, k) := by
  have hsp := he.sp
  simp only [Reg.sp] at hsp
  obtain ⟨ha0, ha1, ha2, hal, hale, hle, dFS, dES, dEF, dP1, dB1, dP2, dB2, hB, -⟩ := hpre
  obtain ⟨hx, h2, h9, h8, hpr, s1, s2, s3, s4, s5, s6, s7, hfr⟩ := hc
  have h4 : z.reg 4 = s.reg 4 := hpr 4 (by simp)
  -- the call of __syscall_ret from the state after the writev and the auipc/jalr, for its result `v`
  have hsrle : ∀ (st : State), st.reg 2 = s.reg 2 - 96#64 → st.reg 4 = s.reg 4 → ∀ v,
      (syscallRetSpec.perm v st).le k.perm := by
    intro st hs2 hs4 v
    refine Perm.le_trans (Perm.le_of (by simp [Spec.perm, syscallRetSpec]) ?_) hle
    intro r hr
    simp only [Spec.perm, syscallRetSpec, Spec.stackRegion, Reg.sp, Reg.tp, hs2, hs4, List.mem_cons,
      List.not_mem_nil, or_false, List.cons_append, List.nil_append] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨s.reg 4 + 18446744073709551452#64, 4⟩, by simp [stdioWritePerm], Region.within_refl _⟩
    · exact ⟨⟨s.reg 2 - 112#64, 112⟩, by simp [stdioWritePerm], by simp only [Region.within]; bv_omega⟩
  have hy2 : y.reg 2 = s.reg 2 - 96#64 := by rw [hyr 2 (by decide), h2]
  have hy4 : y.reg 4 = s.reg 4 := by rw [hyr 4 (by decide), h4]
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
    refine VerifiedProc.call __syscall_ret_verified v ⟨?_, ?_, ?_, ?_, ?_⟩ ⟨⟨?_, ?_, ?_⟩, ?_⟩
      (Dom.sub_of_ranges (by decide)) ?_
    · simp only [nocompiler_state]; rfl
    · simp only [nocompiler_state]; exact hyx
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.ra] <;> decide
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.ra] <;> decide
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.sp, hy2]; exact sw_al96 hsp
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.a0, hy10]
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.tp, hy4]; exact hale
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.tp, Reg.sp, hy4, hy2, Spec.stackRegion, sw_e112]; exact sw_errDisj16 dES
    · exact hsrle _ (by simp (disch := nocompiler_decide_closed) only [nocompiler_state, hy2]) (by simp (disch := nocompiler_decide_closed) only [nocompiler_state, hy4]) _
    rintro ⟨w, kw⟩ (⟨hxw, hpcw, hpresw, ha0w, hkw, htrw, hfrw⟩ | ⟨_, hexw⟩)
    rotate_left
    · exact hexw.elim
    simp only at hxw hpcw hpresw ha0w hkw htrw hfrw
    simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.tp, Reg.sp, hy4, hy2, sw_e112] at hfrw
    rw [hkw]
    have hwr : ∀ q : Reg, q ∈ preservedRegs → w.reg q = z.reg q := by
      intro q hq; rw [hpresw q hq, ← hyr q hq]
      have h1 : q ≠ 1 := not_one_of_preserved q hq
      repeat (first | rw [State.setPc_reg] | rw [State.reg_setReg_other _ _ _ _ h1])
    have hws : ∀ o, 8 ≤ o → o ≤ 88 → read64 w.mem (s.reg 2 - BitVec.ofNat 64 o) = read64 z.mem (s.reg 2 - BitVec.ofNat 64 o) := by
      intro o h1 h3
      apply read64_congr_on; intro j hj
      have hj' := sw_slot_out dES o j hj h1 h3
      rw [hfrw _ hj'.2 hj'.1]; simp only [nocompiler_state, hym]
    have hpr0 : ∀ q ∈ [(3 : Reg), 4, 22, 23, 24, 25, 26, 27], q ∈ preservedRegs := by decide
    refine K w ?_ ⟨hxw, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_
    · rw [hpcw]; simp (disch := nocompiler_decide_closed) only [nocompiler_state, Reg.ra] <;> decide
    · rw [hwr 2 (by decide), h2]
    · rw [hwr 9 (by decide), h9]
    · rw [hwr 8 (by decide), h8]
    · intro q hq; rw [hwr q (hpr0 q hq), hpr q hq]
    · rw [hws 8 (by omega) (by omega)]; exact s1
    · rw [hws 16 (by omega) (by omega)]; exact s2
    · rw [hws 24 (by omega) (by omega)]; exact s3
    · rw [hws 32 (by omega) (by omega)]; exact s4
    · rw [hws 40 (by omega) (by omega)]; exact s5
    · rw [hws 48 (by omega) (by omega)]; exact s6
    · rw [hws 56 (by omega) (by omega)]; exact s7
    · intro p hp1 hp2
      rw [hfrw p hp2 (sw_not16 hp1)]; simp only [nocompiler_state, hym]; exact hfr p hp1 hp2
    · intro q hq; exact hwr q (by revert hq; revert q; decide)
    · apply IovAt_congr _ hiov
      intro o ho
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl <;> exact hws _ (by omega) (by omega)
    · simpa using ha0w
    · rw [htrw]; simp only [nocompiler_state]
    )

/-- A `writev` of `__stdio_write` (at 0x124dc or 0x12558) and the `__syscall_ret` after it: the run goes
    on 12 bytes later from a state where the frame, the s-registers and the iovecs are as before, and a0
    is the count `r` of the bytes the kernel took (one event more: the next `r` of the unwritten ones) or
    -1 (no event). -/
theorem sw_ecall (f buf len : Word) (s : State) (k : Kern) (he : Entry dom __stdio_write_entry s)
    (hpre : stdioWriteSpec.pre (f, buf, len) s k)
    (Q : State × Kern → Prop) (E : Word) (hE : E = 0x124dc#64 ∨ E = 0x12558#64)
    (z : State) (hpc : z.pc = E) (hc : SwCommon s f len z)
    (h17 : z.reg 17 = 66#64) (iovp cnt : Word) (h11 : z.reg 11 = iovp) (h12 : z.reg 12 = cnt) (d : Nat)
    (hiov : IovAt s f buf len z.mem iovp cnt d)
    (K : ∀ w : State, w.pc = E + 12#64 → SwCommon s f len w → (∀ q ∈ [(18 : Reg), 19, 20, 21], w.reg q = z.reg q) →
      IovAt s f buf len w.mem iovp cnt d →
      ((∃ r, r ≤ (stdioBytes s.mem f buf len).length - d ∧ (d < (stdioBytes s.mem f buf len).length → 0 < r) ∧
          r ≤ maxRW ∧ w.reg 10 = BitVec.ofNat 64 r ∧
          w.trace = z.trace ++ [.write (z.reg 10) (((stdioBytes s.mem f buf len).drop d).take r)]) ∨
        (w.reg 10 = -1 ∧ w.trace = z.trace)) →
      PReachK img dom Q (w, k))
    (h10 : (z.reg 10).toNat < 2 ^ 32) :
    PReachK img dom Q (z, k) := by
  have hpre' := hpre
  obtain ⟨-, -, -, -, -, -, -, -, -, dP1, dB1, dP2, dB2, hB, -⟩ := hpre'
  have hc' := hc
  obtain ⟨hx, -, -, -, -, -, -, -, -, -, -, -, hfr⟩ := hc'
  have h7 : z.reg Reg.a7 = sysWritev := h17
  have hg : gather z.mem (z.reg 11) (z.reg 12).toNat = (stdioBytes s.mem f buf len).drop d := by
    rw [h11, h12]; exact sw_gather hfr dP1 dB1 dP2 dB2 hB hiov
  have hdom := sw_ecall_dom E hE
  refine PReachK.ecall (by rw [hpc]; exact hdom.1) hx (by rw [hpc]; exact sw_ecall_instr E hE)
    (by simp only [SysOk, h7]; exact ⟨fun h => absurd h (by decide), fun h => absurd h (by decide)⟩)
    (writev_progress _ _ h7) ?_
  intro y hy0
  obtain ⟨hk, hy⟩ := writev_cases h7 hy0
  clear hy0
  obtain ⟨y, ky⟩ := y
  simp only at hk hy
  rw [hk]
  have hyr10 : ∀ q ∈ preservedRegs, q ≠ 10 := by decide
  rcases hy with ⟨r, hr, hpos, hrm, rfl⟩ | ⟨e, hev, rfl⟩
  · refine sw_retcall f buf len s k he hpre Q E hE z hc iovp cnt d hiov (BitVec.ofNat 64 r) _
      (by simp only [nocompiler_state, hpc]; rfl) (by simp only [nocompiler_state]; exact hx)
      (by simp only [nocompiler_state]) (by simp (disch := nocompiler_decide_closed) only [nocompiler_state])
      (fun q hq => by
        simp only [State.emit_reg, sysRet_reg]
        exact State.reg_setReg_other _ _ _ _ (hyr10 q hq)) ?_
    intro w hpcw hcw hsw hiw ha htr
    have hrb : r < 2 ^ 64 - 4095 := by unfold maxRW at hrm; omega
    have hrn : (BitVec.ofNat 64 r).toNat = r := by rw [BitVec.toNat_ofNat]; omega
    refine K w hpcw hcw hsw hiw (.inl ⟨r, ?_, ?_, hrm, ?_, ?_⟩)
    · rw [hg] at hr; simpa using hr
    · intro hlt; apply hpos; rw [hg]; simp; omega
    · rw [ha, hrn]; simp [hrb]
    · have hfd0 : (SyscallInput.of z).fd 0 = z.reg 10 := SyscallInput.fd_of_lt h10
      rw [htr]; simp only [nocompiler_state, hg, hfd0]
  · refine sw_retcall f buf len s k he hpre Q E hE z hc iovp cnt d hiov e _
      (by simp only [nocompiler_state, hpc]; rfl) (by simp only [nocompiler_state]; exact hx)
      (by simp only [nocompiler_state]) (by simp (disch := nocompiler_decide_closed) only [nocompiler_state])
      (fun q hq => by
        simp only [sysRet_reg]
        exact State.reg_setReg_other _ _ _ _ (hyr10 q hq)) ?_
    intro w hpcw hcw hsw hiw ha htr
    refine K w hpcw hcw hsw hiw (.inr ⟨?_, ?_⟩)
    · rw [ha]; simp [sw_err_big hev]
    · rw [htr]; simp only [nocompiler_state]

/-- `__stdio_write`'s loop at 0x1256c, after a `writev`: `d` bytes had been written before it (`s4` holds
    the count left then), the iovecs at `(s5, s2)` hold the rest; a0 is that `writev`'s count `r` (not
    all of the rest) with its bytes written, or -1 (an error, nothing more written). -/
def CutInv (f buf len : Word) (s : State) (k : Kern) (x : State × Kern) : Prop :=
  x.2 = k ∧ x.1.pc = 0x1256c#64 ∧ SwCommon s f len x.1 ∧
  ∃ d evs, d ≤ (stdioBytes s.mem f buf len).length ∧ x.1.trace = s.trace ++ evs ∧
    x.1.reg 20 = BitVec.ofNat 64 ((stdioBytes s.mem f buf len).length - d) ∧
    IovAt s f buf len x.1.mem (x.1.reg 21) (x.1.reg 18) d ∧
    ((∃ r, 0 < r ∧ d + r < (stdioBytes s.mem f buf len).length ∧ x.1.reg 10 = BitVec.ofNat 64 r ∧
        WritesOf (fdOf s.mem f) evs ((stdioBytes s.mem f buf len).take (d + r))) ∨
     (x.1.reg 10 = -1 ∧ WritesOf (fdOf s.mem f) evs ((stdioBytes s.mem f buf len).take d)))

theorem WritesOf.snoc {fd : Word} {evs : List Event} {bs : List Byte} (d r : Nat)
    (h : WritesOf fd evs (bs.take d)) : WritesOf fd (evs ++ [.write fd ((bs.drop d).take r)]) (bs.take (d + r)) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun e he => ?_, ?_⟩
  · rcases List.mem_append.1 he with he | he
    · exact h1 e he
    · simp at he; exact ⟨_, he⟩
  · rw [List.flatMap_append, h2, List.take_add]; simp [evBytes]

/-- The error exit from the cut: a0 = -1. -/
theorem sw_cut_err (f buf len : Word) (s : State) (k : Kern) (he : Entry dom __stdio_write_entry s)
    (hpre : stdioWriteSpec.pre (f, buf, len) s k) (u : State) (hpc : u.pc = 0x1256c#64) (hc : SwCommon s f len u)
    (d : Nat) (evs : List Event) (hd : d ≤ (stdioBytes s.mem f buf len).length) (htr : u.trace = s.trace ++ evs)
    (hiov : IovAt s f buf len u.mem (u.reg 21) (u.reg 18) d) (h10 : u.reg 10 = -1)
    (hev : WritesOf (fdOf s.mem f) evs ((stdioBytes s.mem f buf len).take d)) :
    PReachK img dom (SwQ f buf len s k) (u, k) := by
  have hx := hc.1
  nocompiler_pstep [hpc, h10]
  refine sw_err f buf len s k he hpre _ (by simp only [nocompiler_state]) hc d evs htr hd hev ?_
  simp only [nocompiler_state]
  rcases hiov with ⟨a, b, c, h0, h1, h2, h3⟩ | ⟨a, a', b, c, h2, h3⟩
  · exact .inl ⟨b, a⟩
  · refine .inr ⟨b, a, c, ?_⟩
    rw [h3]
    rw [stdioBytes_length] at hd
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_sub, BitVec.toNat_ofNat]
    have hl := len.isLt
    rw [Nat.mod_eq_of_lt (by omega : d - stdioPend s.mem f < 2 ^ 64)]
    omega

abbrev SwLoopQ (f buf len : Word) (s : State) (k : Kern) (μ0 : Nat) : State × Kern → Prop :=
  fun y => SwQ f buf len s k y ∨ (CutInv f buf len s k y ∧ (y.1.reg 20).toNat < μ0)

/-- From 0x12564 (after the loop's writev and its `__syscall_ret`): `mv s5, s3`, then `beq s4, a0`: all of
    the rest written (to the success exit), or back at the cut with `d'`. -/
theorem sw_back (f buf len : Word) (s : State) (k : Kern) (he : Entry dom __stdio_write_entry s)
    (hpre : stdioWriteSpec.pre (f, buf, len) s k)
    (w : State) (hpc : w.pc = 0x12564#64) (hc : SwCommon s f len w) (d' : Nat) (evs : List Event)
    (hd' : d' < (stdioBytes s.mem f buf len).length) (htr : w.trace = s.trace ++ evs)
    (h20 : w.reg 20 = BitVec.ofNat 64 ((stdioBytes s.mem f buf len).length - d'))
    (hiov : IovAt s f buf len w.mem (w.reg 19) (w.reg 18) d')
    (hres : (∃ r, r ≤ (stdioBytes s.mem f buf len).length - d' ∧ 0 < r ∧ w.reg 10 = BitVec.ofNat 64 r ∧
        WritesOf (fdOf s.mem f) evs ((stdioBytes s.mem f buf len).take (d' + r))) ∨
      (w.reg 10 = -1 ∧ WritesOf (fdOf s.mem f) evs ((stdioBytes s.mem f buf len).take d')))
    (μ0 : Nat) (hμ : (stdioBytes s.mem f buf len).length - d' < μ0) :
    PReachK img dom (SwLoopQ f buf len s k μ0) (w, k) := by
  have hpre' := hpre
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hB, -⟩ := hpre'
  have hBl := stdioBytes_length s.mem f buf len
  have hx := hc.1
  nocompiler_vstep [hpc]
  have hc' : ∀ p, SwCommon s f len ((w.setReg 21 (w.reg 19)).setPc p) := by
    intro p
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ := hc
    refine ⟨by simp only [nocompiler_state]; exact a1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals (try simp (disch := nocompiler_decide_closed) only [nocompiler_state])
    · exact a2
    · exact a3
    · exact a4
    · intro q hq
      have h21 : q ≠ 21 := by revert hq; revert q; decide
      rw [State.reg_setReg_other _ _ _ _ h21]; exact a5 q hq
    · exact a6
    · exact a7
    · exact a8
    · exact a9
    · exact a10
    · exact a11
    · exact a12
    · exact a13
  have hcut : ((∃ r, 0 < r ∧ d' + r < (stdioBytes s.mem f buf len).length ∧ w.reg 10 = BitVec.ofNat 64 r ∧
        WritesOf (fdOf s.mem f) evs ((stdioBytes s.mem f buf len).take (d' + r))) ∨
      (w.reg 10 = -1 ∧ WritesOf (fdOf s.mem f) evs ((stdioBytes s.mem f buf len).take d'))) →
      PReachK img dom (SwLoopQ f buf len s k μ0) ((w.setReg 21 (w.reg 19)).setPc 0x1256c#64, k) := by
    intro hr
    refine .done (.inr ⟨⟨rfl, rfl, hc' _, d', evs, by omega, by simp only [nocompiler_state]; exact htr, ?_, ?_, ?_⟩, ?_⟩)
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact h20
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact hiov
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state]; exact hr
    · simp (disch := nocompiler_decide_closed) only [nocompiler_state, h20]
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hμ
  rcases hres with ⟨r, hr1, hr2, hr3, hr4⟩ | ⟨hr3, hr4⟩
  · by_cases heq : r = (stdioBytes s.mem f buf len).length - d'
    · subst heq
      nocompiler_vstep [h20, hr3, beq_self_eq_true, ↓reduceIte]
      refine PReachK.bind (fun _ h => h) (fun y hy => .done (.inl hy))
        (sw_succ f buf len s k he hpre _ (by simp only [nocompiler_state]) (hc' _) evs
          (by simp only [nocompiler_state]; exact htr) ?_)
      rw [show d' + ((stdioBytes s.mem f buf len).length - d') = (stdioBytes s.mem f buf len).length by omega,
        List.take_of_length_le (Nat.le_refl _)] at hr4
      exact hr4
    · have hne : BitVec.ofNat 64 ((stdioBytes s.mem f buf len).length - d') ≠ BitVec.ofNat 64 r :=
        ofNat_ne_of_lt (by omega) (by omega) (Ne.symm heq)
      nocompiler_vstep [h20, hr3, beq_iff_eq, hne, ↓reduceIte]
      exact hcut (.inl ⟨r, hr2, by omega, hr3, hr4⟩)
  · have hne : BitVec.ofNat 64 ((stdioBytes s.mem f buf len).length - d') ≠ -1 := ofNat_ne_neg_one (by omega)
    nocompiler_vstep [h20, hr3, beq_iff_eq, hne, ↓reduceIte]
    exact hcut (.inr ⟨hr3, hr4⟩)

/-- At the loop's `writev` (0x12558) with `d'` bytes written: the writev, its `__syscall_ret`, and the
    beq after it (sw_back): the run reaches the success exit or the cut with a smaller measure. -/
theorem sw_at_12558 (f buf len : Word) (s : State) (k : Kern) (he : Entry dom __stdio_write_entry s)
    (hpre : stdioWriteSpec.pre (f, buf, len) s k)
    (z : State) (hpc : z.pc = 0x12558#64) (hc : SwCommon s f len z) (h17 : z.reg 17 = 66#64)
    (h10 : z.reg 10 = fdOf s.mem f) (h11 : z.reg 11 = z.reg 19) (h12 : z.reg 12 = z.reg 18) (d' : Nat)
    (hd' : d' < (stdioBytes s.mem f buf len).length)
    (h20 : z.reg 20 = BitVec.ofNat 64 ((stdioBytes s.mem f buf len).length - d'))
    (hiov : IovAt s f buf len z.mem (z.reg 19) (z.reg 18) d') (evs : List Event) (htr : z.trace = s.trace ++ evs)
    (hev : WritesOf (fdOf s.mem f) evs ((stdioBytes s.mem f buf len).take d'))
    (μ0 : Nat) (hμ : (stdioBytes s.mem f buf len).length - d' < μ0) :
    PReachK img dom (SwLoopQ f buf len s k μ0) (z, k) := by
  refine sw_ecall f buf len s k he hpre _ 0x12558#64 (.inr rfl) z hpc hc h17 (z.reg 19) (z.reg 18) h11 h12 d' hiov ?_
    (by obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hfd⟩ := hpre; rw [h10]; omega)
  intro w hpcw hcw hsw hiw hres
  have hw19 : w.reg 19 = z.reg 19 := hsw 19 (by simp)
  have hw18 : w.reg 18 = z.reg 18 := hsw 18 (by simp)
  have hw20 : w.reg 20 = z.reg 20 := hsw 20 (by simp)
  rcases hres with ⟨r, hr1, hr2, hr3, hr4, hr5⟩ | ⟨hr4, hr5⟩
  · refine sw_back f buf len s k he hpre w (by rw [hpcw]; rfl) hcw d' (evs ++ [.write (fdOf s.mem f) (((stdioBytes s.mem f buf len).drop d').take r)])
      hd' (by rw [hr5, htr, h10, List.append_assoc]) (by rw [hw20, h20]) (by rw [hw19, hw18]; exact hiw)
      (.inl ⟨r, hr1, hr2 hd', hr4, WritesOf.snoc d' r hev⟩) μ0 hμ
  · exact sw_back f buf len s k he hpre w (by rw [hpcw]; rfl) hcw d' evs hd' (by rw [hr5, htr]) (by rw [hw20, h20])
      (by rw [hw19, hw18]; exact hiw) (.inr ⟨hr4, hev⟩) μ0 hμ

/-- One round from the cut with one iovec (all of the buffered bytes written): the iovec advanced by the
    count `r`, then 0x12558. -/
theorem sw_round_one (f buf len : Word) (s : State) (k : Kern) (he : Entry dom __stdio_write_entry s)
    (hpre : stdioWriteSpec.pre (f, buf, len) s k)
    (u : State) (hpc : u.pc = 0x1256c#64) (hc : SwCommon s f len u) (d : Nat) (evs : List Event)
    (htr : u.trace = s.trace ++ evs)
    (h20 : u.reg 20 = BitVec.ofNat 64 ((stdioBytes s.mem f buf len).length - d))
    (h21 : u.reg 21 = s.reg 2 - 72#64) (h18 : u.reg 18 = 1#64)
    (m72 : read64 u.mem (s.reg 2 - 72#64) = buf + BitVec.ofNat 64 (d - stdioPend s.mem f))
    (m64 : read64 u.mem (s.reg 2 - 64#64) = BitVec.ofNat 64 (stdioPend s.mem f + len.toNat - d))
    (hpd : stdioPend s.mem f < d) (r : Nat) (hr : 0 < r) (hdr : d + r < (stdioBytes s.mem f buf len).length)
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
  have e64 : s.reg 2 - 72#64 + 8#64 = s.reg 2 - 64#64 := by bv_omega
  have hult : (BitVec.ofNat 64 (stdioPend s.mem f + len.toNat - d)).ult (BitVec.ofNat 64 r) = false :=
    ult_ofNat_false (by omega) (by omega)
  have hBd : stdioPend s.mem f + len.toNat - d < 2 ^ 64 := by omega
  have hsub : BitVec.ofNat 64 (stdioPend s.mem f + len.toNat - d) - BitVec.ofNat 64 r =
      BitVec.ofNat 64 (stdioPend s.mem f + len.toNat - d - r) := ofNat_sub_ofNat (by omega)
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
  nocompiler_run_n 26 [hx, bool64_false', bool64_true', hpc, h10, slt_ofNat_zero hr63, h21, e64, sw_alS hsp 64 rfl, m64, hult, BitVec.add_zero, sw_alS hsp 72 rfl, m72, hm1, hsub, h9, al120, hfd, h20, hsub', h18] using [rS, wS, r120]
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
        Auto.read64_writeLE_same', BitVec.ofNat_toNat, BitVec.setWidth_eq, add_ofNat_add,
        show d - stdioPend s.mem f + r = d + r - stdioPend s.mem f by omega]
    · rw [Auto.read64_writeLE_same', BitVec.ofNat_toNat, BitVec.setWidth_eq,
        show stdioPend s.mem f + len.toNat - d - r = stdioPend s.mem f + len.toNat - (d + r) by omega]
  · simp only [nocompiler_state]; exact htr

end NoCompiler.Libc.Musl.StdioWrite
