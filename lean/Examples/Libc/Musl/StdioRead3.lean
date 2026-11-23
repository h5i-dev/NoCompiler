import Examples.Libc.Musl.StdioRead2

set_option maxRecDepth 20000
namespace NoCompiler.Libc.Musl.StdioRead
open NoCompiler NoCompiler.Linux NoCompiler.Libc NoCompiler.Libc.Musl NoCompiler.Libc.Musl.StdioWrite NoCompiler.Libc.Musl.Toread NoCompiler.Libc.Musl.StdioRead NoCompiler.Libc.Musl.StdioReadImg NoCompiler.Libc.Musl.SyscallRet

theorem srK_nil (s : State) (f buf len : Word) : srK s f buf len [] = s.mem := by
  simp [srK, scatter, applyWrites, writeBytes]

theorem writeBytes_congr_pt {m m' : Word → Byte} {p : Word} (h : m p = m' p) (a : Word) (bs : List Byte) :
    writeBytes m a bs p = writeBytes m' a bs p := by
  induction bs generalizing a with
  | nil => exact h
  | cons b bs ih => simp only [writeBytes]; split
                    · rfl
                    · exact ih _

theorem applyWrites_congr_pt {p : Word} (ws : List (Word × List Byte)) :
    ∀ {m m' : Word → Byte}, m p = m' p → applyWrites m ws p = applyWrites m' ws p := by
  induction ws with
  | nil => intro m m' h; exact h
  | cons w ws ih => intro m m' h; exact ih (writeBytes_congr_pt h _ _)

theorem not_mem_of_mem_disj {r r' : Region} {x : Word} (hd : r.Disjoint r') (hx : r'.mem x) : ¬ r.mem x := by
  simp only [Region.Disjoint, Region.mem] at *; bv_omega

theorem sr_slot_in (sp : Word) (o j : Nat) (hj : j < 8) (h1 : 8 ≤ o) (h3 : o ≤ 80) :
    (Region.mk (sp - 80#64) 80).mem (sp - BitVec.ofNat 64 o + BitVec.ofNat 64 j) := by
  simp only [Region.mem]; bv_omega

theorem SrCommon_setPc {s : State} {f buf len : Word} {m0 : Word → Byte} {u : State} (a : Word)
    (h : SrCommon s f buf len m0 u) : SrCommon s f buf len m0 (u.setPc a) := by
  simpa [SrCommon] using h

theorem SrCommon_mod {s : State} {f buf len : Word} {m0 m1 : Word → Byte} {z : State}
    (hc : SrCommon s f buf len m0 z) (y : State) (hx : y.exit = none) (hr : ∀ q : Reg, q ≠ 10 → y.reg q = z.reg q)
    (hs : ∀ o, o ∈ [8, 16, 24, 32, 56] → read64 y.mem (s.reg 2 - BitVec.ofNat 64 o) = read64 z.mem (s.reg 2 - BitVec.ofNat 64 o))
    (hm : ∀ p, ¬ (Region.mk (s.reg 2 - 80#64) 80).mem p → ¬ (Region.mk (s.reg 4 + 18446744073709551452#64) 4).mem p →
      y.mem p = m1 p) : SrCommon s f buf len m1 y := by
  obtain ⟨-, h2, h8, h9, h18, hpr, s1, s2, s3, s4, s5, -⟩ := hc
  refine ⟨hx, by rw [hr 2 (by decide), h2], by rw [hr 8 (by decide), h8], by rw [hr 9 (by decide), h9],
    by rw [hr 18 (by decide), h18], fun q hq => by rw [hr q (by revert hq; revert q; decide), hpr q hq], ?_, ?_, ?_, ?_, ?_, hm⟩
  · have := hs 8 (by simp); rw [this]; exact s1
  · have := hs 16 (by simp); rw [this]; exact s2
  · have := hs 24 (by simp); rw [this]; exact s3
  · have := hs 32 (by simp); rw [this]; exact s4
  · have := hs 56 (by simp); rw [this]; exact s5

theorem sr_iovs (m : Word → Byte) (sp : Word) :
    iovs m (sp - 64#64) 2 = [(read64 m (sp - 64#64), (read64 m (sp - 56#64)).toNat),
      (read64 m (sp - 48#64), (read64 m (sp - 40#64)).toNat)] := by
  simp only [iovs, iovAt, show List.range 2 = [0, 1] from rfl, List.map_cons, List.map_nil]
  rw [show sp - 64#64 + BitVec.ofNat 64 (16 * 0) = sp - 64#64 by bv_omega,
    show sp - 64#64 + BitVec.ofNat 64 (16 * 0 + 8) = sp - 56#64 by bv_omega,
    show sp - 64#64 + BitVec.ofNat 64 (16 * 1) = sp - 48#64 by bv_omega,
    show sp - 64#64 + BitVec.ofNat 64 (16 * 1 + 8) = sp - 40#64 by bv_omega]

/-- The `readv` of `__stdio_read` (0x1235c, len ≥ 2) and the run after it. -/
theorem stdioReadP_pre_perm {a : Word × Word × Word} {s : State} {k k' : Kern} (h : stdioReadP.pre a s k)
    (hk : k'.perm = k.perm) : stdioReadP.pre a s k' := by
  obtain ⟨f, buf, len⟩ := a
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a8', a9, a10⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a8', by rw [hk]; exact a9, a10⟩

theorem chunk_len_le (fl : OpenFile) (n : Nat) : (fl.chunk n).length ≤ n ∧ (fl.chunk n).length ≤ maxRW := by
  simp only [OpenFile.chunk, List.length_take]; constructor <;> omega

theorem sr_readv (f buf len : Word) (s : State) (k : Kern) (he : Entry dom __stdio_read_entry s)
    (hpre : stdioReadP.pre (f, buf, len) s k) (hL2 : 1 < len.toNat)
    (z : State) (hpc : z.pc = 0x1235c#64) (hc : SrCommon s f buf len s.mem z) (h17 : z.reg 17 = 65#64)
    (h11 : z.reg 11 = s.reg 2 - 64#64) (h12 : z.reg 12 = 2#64) (h10 : z.reg 10 = fdOf s.mem f)
    (hi0 : read64 z.mem (s.reg 2 - 64#64) = buf) (hi2 : read64 z.mem (s.reg 2 - 48#64) = read64 s.mem (f + 88#64))
    (hi3 : read64 z.mem (s.reg 2 - 40#64) = read64 s.mem (f + 96#64)) (htr : z.trace = s.trace) :
    PReachK img dom (fun y => Final dom y.1 ∧ stdioReadP.Done (f, buf, len) (s, k) y) (z, k) := by
  have hpre' := hpre
  obtain ⟨ha0, ha1, ha2, hal, hale, hlen, hbs, hB, hfdn, hle, dFS, dES, dEF, dBS, dBE, dBF, dUS, dUE, dUF, dBU⟩ := hpre'
  have hc' := hc
  obtain ⟨hx, h2, h8, h9, h18, hpr, s1, s2, s3, s4, s5, hfr⟩ := hc'
  have h7 : z.reg Reg.a7 = sysReadv := h17
  have hlm : (len - 1#64).toNat = len.toNat - 1 := by bv_omega
  have hiov : iovs z.mem (z.reg 11) (z.reg 12).toNat =
      [(buf, len.toNat - 1), (read64 s.mem (f + 88#64), (read64 s.mem (f + 96#64)).toNat)] := by
    rw [h11, h12, show (2#64).toNat = 2 from rfl, sr_iovs, hi0, s5, hi2, hi3, hlm]
  have hdom := sr_ecall_dom 0x1235c#64 (.inl rfl)
  have hslotB : ∀ o, o ∈ [8, 16, 24, 32, 56] → ∀ ds : List Byte,
      read64 (applyWrites z.mem (scatter [(buf, len.toNat - 1), (read64 s.mem (f + 88#64), (read64 s.mem (f + 96#64)).toNat)] ds))
        (s.reg 2 - BitVec.ofNat 64 o) = read64 z.mem (s.reg 2 - BitVec.ofNat 64 o) := by
    intro o ho ds
    have ho' : 8 ≤ o ∧ o ≤ 56 := by simp at ho; omega
    apply read64_congr_on; intro j hj
    have hin := sr_slot_in (s.reg 2) o j hj ho'.1 (by omega)
    exact scatter2_out ds (fun h => not_mem_of_mem_disj dBS hin (by simp only [Region.mem] at h ⊢; omega))
      (not_mem_of_mem_disj dUS hin)
  have post : ∀ (k' : Kern) (ds : List Byte), k'.perm = k.perm → ds.length ≤ len.toNat - 1 + (read64 s.mem (f + 96#64)).toNat → ds.length ≤ maxRW →
      ReadK (fdOf s.mem f) (len.toNat - 1 + (read64 s.mem (f + 96#64)).toNat) ds k k' →
      PReachK img dom (fun y => Final dom y.1 ∧ stdioReadP.Done (f, buf, len) (s, k) y)
        (((z.sysRet (BitVec.ofNat 64 ds.length)).setMem (applyWrites z.mem (scatter [(buf, len.toNat - 1), (read64 s.mem (f + 88#64), (read64 s.mem (f + 96#64)).toNat)] ds))).emit (.read (z.reg 10) ds), k') := by
    intro k' ds hkp hdl' hmx hK
    have hpre2 : stdioReadP.pre (f, buf, len) s k' := stdioReadP_pre_perm hpre hkp
    have hc1 : SrCommon s f buf len (srK s f buf len ds) (((z.sysRet (BitVec.ofNat 64 ds.length)).setMem
        (applyWrites z.mem (scatter [(buf, len.toNat - 1), (read64 s.mem (f + 88#64), (read64 s.mem (f + 96#64)).toNat)] ds))).emit
          (.read (z.reg 10) ds)) := by
      refine SrCommon_mod hc _ (by simp only [State.emit_exit, nocompiler_state]; exact hx) (fun q hq => ?_) (fun o ho => ?_) (fun p h1 h2 => ?_)
      · simp only [State.emit_reg, sysRet_reg]; exact State.reg_setReg_other _ _ _ _ hq
      · simp only [State.emit_mem, nocompiler_state]; exact hslotB o ho ds
      · simp only [State.emit_mem, nocompiler_state, srK]; exact applyWrites_congr_pt _ (hfr p h1 h2)
    have hrs : (BitVec.ofNat 64 ds.length).toNat < 2 ^ 64 - 4095 := by
      rw [BitVec.toNat_ofNat]; unfold maxRW at hmx; omega
    refine sr_retcall f buf len s k' he hpre2 _ _ 0x1235c#64 (.inl rfl) (BitVec.ofNat 64 ds.length) _
      (by simp only [State.emit_pc, nocompiler_state, hpc]; rfl) hc1
      (by simp (disch := nocompiler_decide_closed) only [State.emit_reg, sysRet_reg, nocompiler_state]) ?_
    intro w hpcw hcw ha htrw
    rw [if_pos hrs] at ha
    have hxw := hcw.1
    simp only [BitVec.reduceAdd] at hpcw
    have htr' : w.trace = s.trace ++ [.read (fdOf s.mem f) ds] := by
      rw [htrw]; simp only [State.emit_trace, nocompiler_state, htr, h10]
    by_cases h0 : ds = []
    · subst h0
      have hb : (!BitVec.slt (0 : Word) (w.reg 10)) = true := by rw [ha]; decide
      nocompiler_wstep [hcw.1, hpcw, hb]
      rw [srK_nil] at hcw
      refine sr_np f buf len s k' he hpre2 _ ?_ (SrCommon_setPc _ hcw) k (.inl ⟨?_, ?_, hK⟩)
      · simp only [nocompiler_state]
      · simp only [nocompiler_state]; rw [ha]; rfl
      · simp only [nocompiler_state]; exact htr'
    · have hpos : 0 < ds.length := List.length_pos_iff.mpr h0
      have hb : (!BitVec.slt (0 : Word) (w.reg 10)) = false := by
        rw [ha, slt_zero_ofNat _ (by unfold maxRW at hmx; omega)]; simp [hpos]
      nocompiler_wstep [hcw.1, hpcw, hb]
      refine sr_pos f buf len s k' he hpre2 ds hdl' hmx hpos _ ?_ (SrCommon_setPc _ hcw) ?_ ?_ k hK
      · simp only [nocompiler_state]
      · simp only [nocompiler_state]; exact ha
      · simp only [nocompiler_state]; exact htr'
  have perr : ∀ e : Word, ¬ e.toNat < 2 ^ 64 - 4095 →
      (∀ fl, k.files.lookup (fdOf s.mem f) = some fl → fdOf s.mem f ∉ k.fds) →
      PReachK img dom (fun y => Final dom y.1 ∧ stdioReadP.Done (f, buf, len) (s, k) y)
        (z.sysRet e, k) := by
    intro e hbig hnf
    have hc1 : SrCommon s f buf len s.mem (z.sysRet e) := by
      refine SrCommon_mod hc _ (by simp only [nocompiler_state]; exact hx) (fun q hq => ?_) (fun o ho => ?_) (fun p h1 h2 => ?_)
      · simp only [sysRet_reg]; exact State.reg_setReg_other _ _ _ _ hq
      · simp only [sysRet_mem]
      · simp only [sysRet_mem]; exact hfr p h1 h2
    refine sr_retcall f buf len s k he hpre _ _ 0x1235c#64 (.inl rfl) e _
      (by simp only [nocompiler_state, hpc]; rfl) hc1
      (by simp (disch := nocompiler_decide_closed) only [sysRet_reg, nocompiler_state]) ?_
    intro w hpcw hcw ha htrw
    rw [if_neg hbig] at ha
    simp only [BitVec.reduceAdd] at hpcw
    have hb : (!BitVec.slt (0 : Word) (w.reg 10)) = true := by rw [ha]; decide
    nocompiler_wstep [hcw.1, hpcw, hb]
    refine sr_np f buf len s k he hpre _ ?_ (SrCommon_setPc _ hcw) k (.inr ⟨?_, ?_, rfl, hnf⟩)
    · simp only [nocompiler_state]
    · simp only [nocompiler_state]; exact ha
    · simp only [nocompiler_state]; rw [htrw]; simp only [nocompiler_state, htr]
  have hfd : z.reg Reg.a0 = fdOf s.mem f := by simp only [Reg.a0]; exact h10
  have hfd0 : (SyscallInput.of z).fd 0 = z.reg Reg.a0 :=
    SyscallInput.fd_of_lt (show (z.reg 10).toNat < 2 ^ 32 by rw [h10]; omega)
  have htot : iovTotal [(buf, len.toNat - 1), (read64 s.mem (f + 88#64), (read64 s.mem (f + 96#64)).toNat)] =
      len.toNat - 1 + (read64 s.mem (f + 96#64)).toNat := by simp [iovTotal]
  rcases hlk : k.files.lookup (fdOf s.mem f) with _ | fl
  · have hl : k.files.lookup ((SyscallInput.of z).fd 0) = none := by rw [hfd0, hfd]; exact hlk
    refine PReachK.ecall (by rw [hpc]; exact hdom.1) hx (by rw [hpc]; simp only [nocompiler_image])
      (by simp only [SysOk, h7]; exact ⟨fun h => absurd h (by decide), fun h => absurd h (by decide)⟩)
      (readv_progress _ _ h7 hl) ?_
    intro y hy0
    obtain ⟨hk, hy⟩ := readv_cases h7 hl hy0
    clear hy0
    obtain ⟨y, ky⟩ := y
    simp only at hk hy
    rw [hk]
    rw [hiov, hfd0] at hy
    rcases hy with ⟨ds, hdl, hmx, rfl⟩ | ⟨e, hev, rfl⟩
    · exact post k ds rfl (by rw [← htot]; exact hdl) hmx (.inl ⟨hlk, rfl⟩)
    · exact perr e (sw_err_big hev) (fun fl h => by rw [hlk] at h; cases h)
  · have hl : k.files.lookup ((SyscallInput.of z).fd 0) = some fl := by rw [hfd0, hfd]; exact hlk
    refine PReachK.ecall (by rw [hpc]; exact hdom.1) hx (by rw [hpc]; simp only [nocompiler_image])
      (by simp only [SysOk, h7]; exact ⟨fun h => absurd h (by decide), fun h => absurd h (by decide)⟩)
      (readv_progress_file _ _ fl h7 hl) ?_
    intro y hy0
    rcases readv_cases_file h7 hl hy0 with ⟨hk, hy⟩ | ⟨hk, e, hev, hy⟩
    all_goals (try rw [hfd0] at hk)
    all_goals (try rw [hfd0] at hy)
    · obtain ⟨y, ky⟩ := y
      simp only at hk hy
      rw [hiov, htot] at hk hy
      rw [hk, hy]
      have hcl := chunk_len_le fl (len.toNat - 1 + (read64 s.mem (f + 96#64)).toNat)
      exact post _ _ rfl hcl.1 hcl.2 (.inr ⟨fl, hlk, rfl, by first | rw [hfd] | rw [h10] | rw [hfd0, hfd]⟩)
    · obtain ⟨y, ky⟩ := y
      simp only at hk hy
      rw [hk, hy]
      rcases hev with ⟨rfl, hn⟩ | ⟨rfl, hn⟩
      · rw [h12] at hn; exact absurd hn (by decide)
      · exact perr _ (sw_err_big (by simp)) (fun _ _ => by rw [← h10, ← hfd0]; exact hn)
theorem srK_one {s : State} {f buf len : Word} (hl : len.toNat = 1) (ds : List Byte)
    (hd : ds.length ≤ (read64 s.mem (f + 96#64)).toNat) :
    srK s f buf len ds = writeBytes s.mem (read64 s.mem (f + 88#64)) ds := by
  simp only [srK, applyWrites_scatter2, hl, Nat.sub_self, List.take_zero, List.drop_zero, List.take_of_length_le hd]
  rfl

/-- The `read` of `__stdio_read` (0x123b0, len = 1: the whole request goes to FILE's buffer) and the run after it. -/
theorem sr_read (f buf len : Word) (s : State) (k : Kern) (he : Entry dom __stdio_read_entry s)
    (hpre : stdioReadP.pre (f, buf, len) s k) (hL1 : len.toNat = 1)
    (z : State) (hpc : z.pc = 0x123b0#64) (hc : SrCommon s f buf len s.mem z) (h17 : z.reg 17 = 63#64)
    (h11 : z.reg 11 = read64 s.mem (f + 88#64)) (h12 : z.reg 12 = read64 s.mem (f + 96#64)) (h10 : z.reg 10 = fdOf s.mem f)
    (htr : z.trace = s.trace) :
    PReachK img dom (fun y => Final dom y.1 ∧ stdioReadP.Done (f, buf, len) (s, k) y) (z, k) := by
  have hpre' := hpre
  obtain ⟨ha0, ha1, ha2, hal, hale, hlen, hbs, hB, hfdn, hle, dFS, dES, dEF, dBS, dBE, dBF, dUS, dUE, dUF, dBU⟩ := hpre'
  have hc' := hc
  obtain ⟨hx, h2, h8, h9, h18, hpr, s1, s2, s3, s4, s5, hfr⟩ := hc'
  have h7 : z.reg Reg.a7 = sysRead := h17
  have wU : k.perm.canWrite (read64 s.mem (f + 88#64)) (read64 s.mem (f + 96#64)).toNat :=
    hle.write _ _ (.inr ⟨⟨read64 s.mem (f + 88#64), (read64 s.mem (f + 96#64)).toNat⟩, by simp [stdioReadPerm],
      by simp only [Region.covers]; bv_omega⟩)
  have hdom := sr_ecall_dom 0x123b0#64 (.inr rfl)
  have post : ∀ (k' : Kern) (ds : List Byte), k'.perm = k.perm → ds.length ≤ len.toNat - 1 + (read64 s.mem (f + 96#64)).toNat → ds.length ≤ maxRW →
      ReadK (fdOf s.mem f) (len.toNat - 1 + (read64 s.mem (f + 96#64)).toNat) ds k k' →
      PReachK img dom (fun y => Final dom y.1 ∧ stdioReadP.Done (f, buf, len) (s, k) y)
        (((z.sysRet (BitVec.ofNat 64 ds.length)).setMem (writeBytes z.mem (read64 s.mem (f + 88#64)) ds)).emit (.read (z.reg 10) ds), k') := by
    intro k' ds hkp hdl' hmx hK
    have hdl : ds.length ≤ (read64 s.mem (f + 96#64)).toNat := by omega
    have hpre2 : stdioReadP.pre (f, buf, len) s k' := stdioReadP_pre_perm hpre hkp
    have hc1 : SrCommon s f buf len (srK s f buf len ds) (((z.sysRet (BitVec.ofNat 64 ds.length)).setMem
        (writeBytes z.mem (read64 s.mem (f + 88#64)) ds)).emit (.read (z.reg 10) ds)) := by
      refine SrCommon_mod hc _ (by simp only [State.emit_exit, nocompiler_state]; exact hx) (fun q hq => ?_) (fun o ho => ?_) (fun p h1 h2 => ?_)
      · simp only [State.emit_reg, sysRet_reg]; exact State.reg_setReg_other _ _ _ _ hq
      · simp only [State.emit_mem, nocompiler_state]
        have ho' : 8 ≤ o ∧ o ≤ 56 := by simp at ho; omega
        apply read64_congr_on; intro j hj
        exact writeBytes_out hdl (not_mem_of_mem_disj dUS (sr_slot_in (s.reg 2) o j hj ho'.1 (by omega)))
      · simp only [State.emit_mem, nocompiler_state]; rw [srK_one hL1 ds hdl]; exact writeBytes_congr_pt (hfr p h1 h2) _ _
    have hrs : (BitVec.ofNat 64 ds.length).toNat < 2 ^ 64 - 4095 := by
      rw [BitVec.toNat_ofNat]; unfold maxRW at hmx; omega
    refine sr_retcall f buf len s k' he hpre2 _ _ 0x123b0#64 (.inr rfl) (BitVec.ofNat 64 ds.length) _
      (by simp only [State.emit_pc, nocompiler_state, hpc]; rfl) hc1
      (by simp (disch := nocompiler_decide_closed) only [State.emit_reg, nocompiler_state]) ?_
    intro w hpcw hcw ha htrw
    rw [if_pos hrs] at ha
    simp only [BitVec.reduceAdd] at hpcw
    have htr' : w.trace = s.trace ++ [.read (fdOf s.mem f) ds] := by
      rw [htrw]; simp only [State.emit_trace, nocompiler_state, htr, h10]
    by_cases h0 : ds = []
    · subst h0
      have hb : BitVec.slt (0 : Word) (w.reg 10) = false := by rw [ha]; decide
      nocompiler_wstep [hcw.1, hpcw, hb]
      rw [srK_nil] at hcw
      refine sr_np f buf len s k' he hpre2 _ ?_ (SrCommon_setPc _ hcw) k (.inl ⟨?_, ?_, hK⟩)
      · simp only [nocompiler_state]
      · simp only [nocompiler_state]; rw [ha]; rfl
      · simp only [nocompiler_state]; exact htr'
    · have hpos : 0 < ds.length := List.length_pos_iff.mpr h0
      have hb : BitVec.slt (0 : Word) (w.reg 10) = true := by
        rw [ha, slt_zero_ofNat _ (by unfold maxRW at hmx; omega)]; simp [hpos]
      nocompiler_wstep [hcw.1, hpcw, hb]
      refine sr_pos f buf len s k' he hpre2 ds hdl' hmx hpos _ ?_ (SrCommon_setPc _ hcw) ?_ ?_ k hK
      · simp only [nocompiler_state]
      · simp only [nocompiler_state]; exact ha
      · simp only [nocompiler_state]; exact htr'
  have perr : ∀ e : Word, ¬ e.toNat < 2 ^ 64 - 4095 →
      (∀ fl, k.files.lookup (fdOf s.mem f) = some fl → fdOf s.mem f ∉ k.fds) →
      PReachK img dom (fun y => Final dom y.1 ∧ stdioReadP.Done (f, buf, len) (s, k) y)
        (z.sysRet e, k) := by
    intro e hbig hnf
    have hc1 : SrCommon s f buf len s.mem (z.sysRet e) := by
      refine SrCommon_mod hc _ (by simp only [nocompiler_state]; exact hx) (fun q hq => ?_) (fun o ho => ?_) (fun p h1 h2 => ?_)
      · simp only [sysRet_reg]; exact State.reg_setReg_other _ _ _ _ hq
      · simp only [sysRet_mem]
      · simp only [sysRet_mem]; exact hfr p h1 h2
    refine sr_retcall f buf len s k he hpre _ _ 0x123b0#64 (.inr rfl) e _
      (by simp only [nocompiler_state, hpc]; rfl) hc1
      (by simp (disch := nocompiler_decide_closed) only [sysRet_reg, nocompiler_state]) ?_
    intro w hpcw hcw ha htrw
    rw [if_neg hbig] at ha
    simp only [BitVec.reduceAdd] at hpcw
    have hb : BitVec.slt (0 : Word) (w.reg 10) = false := by rw [ha]; decide
    nocompiler_wstep [hcw.1, hpcw, hb]
    refine sr_np f buf len s k he hpre _ ?_ (SrCommon_setPc _ hcw) k (.inr ⟨?_, ?_, rfl, hnf⟩)
    · simp only [nocompiler_state]
    · simp only [nocompiler_state]; exact ha
    · simp only [nocompiler_state]; rw [htrw]; simp only [nocompiler_state, htr]
  have hfd : z.reg Reg.a0 = fdOf s.mem f := by simp only [Reg.a0]; exact h10
  have hfd0 : (SyscallInput.of z).fd 0 = z.reg Reg.a0 :=
    SyscallInput.fd_of_lt (show (z.reg 10).toNat < 2 ^ 32 by rw [h10]; omega)
  have hN : len.toNat - 1 + (read64 s.mem (f + 96#64)).toNat = (read64 s.mem (f + 96#64)).toNat := by omega
  rcases hlk : k.files.lookup (fdOf s.mem f) with _ | fl
  · have hl : k.files.lookup ((SyscallInput.of z).fd 0) = none := by rw [hfd0, hfd]; exact hlk
    refine PReachK.ecall (by rw [hpc]; exact hdom.1) hx (by rw [hpc]; simp only [nocompiler_image])
      (by simp only [SysOk, h7]; exact ⟨fun h => absurd h (by decide), fun _ => by simp only [Reg.a1, Reg.a2, h11, h12]; exact wU⟩)
      (read_progress _ _ h7 hl) ?_
    intro y hy0
    obtain ⟨hk, hy⟩ := read_cases h7 hl hy0
    clear hy0
    obtain ⟨y, ky⟩ := y
    simp only at hk hy
    rw [hk]
    rw [h11, h12, hfd0] at hy
    rcases hy with ⟨ds, hdl, hmx, rfl⟩ | ⟨e, hev, rfl⟩
    · exact post k ds rfl (by omega) hmx (.inl ⟨hlk, rfl⟩)
    · exact perr e (sw_err_big (by rcases hev with h | h; exact .inr (.inl h); exact .inr (.inr h)))
        (fun fl h => by rw [hlk] at h; cases h)
  · have hl : k.files.lookup ((SyscallInput.of z).fd 0) = some fl := by rw [hfd0, hfd]; exact hlk
    refine PReachK.ecall (by rw [hpc]; exact hdom.1) hx (by rw [hpc]; simp only [nocompiler_image])
      (by simp only [SysOk, h7]; exact ⟨fun h => absurd h (by decide), fun _ => by simp only [Reg.a1, Reg.a2, h11, h12]; exact wU⟩)
      (read_progress_file _ _ fl h7 hl) ?_
    intro y hy0
    obtain ⟨hk, hy⟩ := read_cases_file h7 hl hy0
    rw [hfd0] at hk
    obtain ⟨y, ky⟩ := y
    simp only at hk hy
    rw [h11, h12, hfd0] at hy
    rw [h12] at hk
    rw [hk, hy]
    have hcl := chunk_len_le fl (read64 s.mem (f + 96#64)).toNat
    exact post _ _ rfl (by omega) hcl.2 (.inr ⟨fl, hlk, by rw [hN], by first | rw [hfd] | rw [h10] | rw [hfd0, hfd]⟩)
/-- `__stdio_read` (musl src/stdio/__stdio_read.c) at the process level, by hand. -/
theorem __stdio_read_verified : VerifiedProc img dom __stdio_read_entry stdioReadP := by
  rintro ⟨f, buf, len⟩ s k he hpre
  have hpre0 := hpre
  obtain ⟨ha0, ha1, ha2, hal, hale, hlen, hbs, hB, hfdn, hle, hD⟩ := hpre0
  have hpc := he.pc
  have hx := he.live
  have hsp := he.sp
  simp only [__stdio_read_entry] at hpc
  simp only [Reg.sp] at hsp
  obtain ⟨dFS, dES, dEF, dBS, dBE, dBF, dUS, dUE, dUF, dBU⟩ := hD
  have wF : ∀ o n, o + n ≤ 128 → k.perm.canWrite (f + BitVec.ofNat 64 o) n := fun o n h =>
    hle.write _ _ (.inr ⟨⟨f, 128⟩, by simp [stdioReadPerm], by simp only [Region.covers]; bv_omega⟩)
  have wS : ∀ o, 8 ≤ o → o ≤ 80 → k.perm.canWrite (s.reg 2 - BitVec.ofNat 64 o) 8 := fun o h1 h3 =>
    hle.write _ _ (.inr ⟨⟨s.reg 2 - 80#64, 80⟩, by simp [stdioReadPerm], by simp only [Region.covers]; bv_omega⟩)
  have alF : ∀ o, o % 8 = 0 → aligned (f + BitVec.ofNat 64 o) 8 := fun o h => sw_alF hal o h
  have alF4 : ∀ o, o % 4 = 0 → aligned (f + BitVec.ofNat 64 o) 4 := by intro o h; unfold aligned at *; bv_omega
  have eS : ∀ o, o ≤ 64 → s.reg 2 - 64#64 + BitVec.ofNat 64 o = s.reg 2 - BitVec.ofNat 64 (64 - o) := by
    intro o ho; bv_omega
  have e64 : s.reg 2 + 18446744073709551552#64 = s.reg 2 - 64#64 := by bv_omega
  have fs := sr_field_after_slot64 dFS
  have hsn : bool64 (BitVec.ult 0 (read64 s.mem (f + 96#64))) = 1 := by
    have h0 : 0 < (read64 s.mem (f + 96#64)).toNat := by
      rcases Nat.eq_zero_or_pos (read64 s.mem (f + 96#64)).toNat with h | h
      · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hbs
      · exact h
    simp only [bool64, BitVec.ult]; rw [if_pos (by simpa using h0)]
  nocompiler_run_n 17 [hx, hpc, e64, eS 56 (by omega), sw_alS hsp 8 rfl, eS 48 (by omega), sw_alS hsp 16 rfl, eS 40 (by omega), sw_alS hsp 24 rfl, eS 32 (by omega), sw_alS hsp 32 rfl, BitVec.add_zero, sw_alS hsp 64 rfl, ha0, alF 96 rfl, fs, hsn, eS 8 (by omega), sw_alS hsp 56 rfl, alF 88 rfl, eS 16 (by omega), sw_alS hsp 48 rfl, eS 24 (by omega), sw_alS hsp 40 rfl, alF4 120 rfl, sr_field_after_slot dFS] using [wS, wF]
  have hm : ∀ p, ¬ (Region.mk (s.reg 2 - 80#64) 80).mem p → ∀ (m : Word → Byte) (o : Nat), 8 ≤ o → o ≤ 80 → ∀ v : Nat,
      writeLE m (s.reg 2 - BitVec.ofNat 64 o) v 8 p = m p := by
    intro p hp m o h1 h3 v
    exact writeLE_of_not_mem (r := ⟨s.reg 2 - 80#64, 80⟩) (by simp only [Region.covers]; bv_omega) hp
  have hpr0 : ∀ q ∈ [(3 : Reg), 4, 19, 20, 21, 22, 23, 24, 25, 26, 27],
      q ≠ 2 ∧ q ≠ 8 ∧ q ≠ 9 ∧ q ≠ 10 ∧ q ≠ 11 ∧ q ≠ 12 ∧ q ≠ 13 ∧ q ≠ 17 ∧ q ≠ 18 := by decide
  by_cases hL : s.reg 12 - 1 = 0
  · have hb : (s.reg 12 - 1 == 0) = true := by simpa using hL
    nocompiler_run_n 3 [hx, hb] using [wS, wF]
    refine sr_read f buf len s k he hpre (by rw [← ha2]; bv_omega) _ ?_ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ ?_
    all_goals try (simp (disch := nocompiler_decide_closed) only [nocompiler_state, slot_ne, fw_slot_same, ha0, ha1, ha2]; done)
    all_goals first
      | (simp only [nocompiler_state]; exact hx)
      | (intro (q : Reg) hq; obtain ⟨_, _, _, _, _, _, _, _, _⟩ := hpr0 q hq; repeat (first | rw [State.setPc_reg] | rw [State.setMem_reg] | rw [State.reg_setReg_other _ _ _ _ (by assumption)]))
      | (intro p h1 _; simp only [nocompiler_state]; repeat rw [hm p h1 _ _ (by omega) (by omega)])
      | (simp (disch := nocompiler_decide_closed) only [nocompiler_state, fdOf]; done)
      | (simp (disch := nocompiler_decide_closed) only [nocompiler_state, slot_ne, fw_slot_same, ha2, BitVec.ofNat_toNat, BitVec.setWidth_eq]; done)
      | (simp (disch := nocompiler_decide_closed) only [nocompiler_state, slot_ne, fw_slot_same, ha2, BitVec.ofNat_toNat, BitVec.setWidth_eq]; rfl)
  · have hb : (s.reg 12 - 1 == 0) = false := by simpa using hL
    nocompiler_run_n 4 [hx, hb] using [wS, wF]
    refine sr_readv f buf len s k he hpre (by rw [← ha2] at hlen; rw [← ha2]; bv_omega) _ ?_
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals try (simp (disch := nocompiler_decide_closed) only [nocompiler_state, slot_ne, fw_slot_same, ha0, ha1, ha2]; done)
    all_goals first
      | (simp only [nocompiler_state]; exact hx)
      | (intro (q : Reg) hq; obtain ⟨_, _, _, _, _, _, _, _, _⟩ := hpr0 q hq; repeat (first | rw [State.setPc_reg] | rw [State.setMem_reg] | rw [State.reg_setReg_other _ _ _ _ (by assumption)]))
      | (intro p h1 _; simp only [nocompiler_state]; repeat rw [hm p h1 _ _ (by omega) (by omega)])
      | (simp (disch := nocompiler_decide_closed) only [nocompiler_state, fdOf]; done)
      | (simp (disch := nocompiler_decide_closed) only [nocompiler_state, slot_ne, fw_slot_same, ha2, BitVec.ofNat_toNat, BitVec.setWidth_eq]; done)
      | (simp (disch := nocompiler_decide_closed) only [nocompiler_state, slot_ne, fw_slot_same, ha2, BitVec.ofNat_toNat, BitVec.setWidth_eq]; rfl)

end NoCompiler.Libc.Musl.StdioRead
