import Examples.Libc.Musl.StdioWriteImg
import NoCompiler.Libc.Tactic
import Examples.Libc.Musl.Small
set_option maxRecDepth 20000
namespace NoCompiler.Libc.Musl.StdioWrite
open NoCompiler NoCompiler.Linux NoCompiler.Libc NoCompiler.Libc.Musl.StdioWriteImg NoCompiler.Libc.Musl.SyscallRet

theorem not_one_of_preserved : ∀ r ∈ preservedRegs, r ≠ 1 := by decide

/-- A `write` function's specification that keeps its caller's 16 bytes above sp and the permissions. -/
def StdioWriteFrame (W : SpecP (Word × Word × Word)) : Prop :=
  ∀ a z w, W.post a z w → (∀ p, (Region.mk (z.1.reg Reg.sp) 16).mem p → w.1.mem p = z.1.mem p) ∧
    w.2.perm = z.2.perm

def ___errno_location_dom : Dom := [(0x122fc#64, 12)]

/-- `___errno_location()` at the process level, by hand: a0 = tp - 164; nothing else changes (no syscall,
    no store), the kernel and the trace included. -/
def errnoP : SpecP Unit where
  pre := fun _ _ _ => True
  post := fun _ x y => y.1.reg 10 = x.1.reg 4 + 18446744073709551452#64 ∧ y.2 = x.2 ∧
    y.1.trace = x.1.trace ∧ y.1.mem = x.1.mem

theorem ___errno_location_proc : VerifiedProc img ___errno_location_dom ___errno_location_entry errnoP := by
  intro _ s k he _
  have hpc := he.pc
  have hx := he.live
  have hra4 := he.retAligned
  have hret := he.ret
  simp only [___errno_location_entry] at hpc
  simp only [Reg.ra] at hra4 hret
  nocompiler_pstep [hpc]
  nocompiler_pstep
  nocompiler_pstep [ret_mask hra4, hra4]
  refine .done ⟨.inl ?_, .inl ⟨?_, ?_, ?_, ?_, rfl, ?_, ?_⟩⟩
  · simp only [nocompiler_state]; exact hret
  · simp only [nocompiler_state]; exact hx
  · simp only [nocompiler_state, Reg.ra]
  · intro q hq
    have h10 : q ≠ 10 := by revert hq; revert q; decide
    repeat (first | rw [State.setPc_reg] | rw [State.reg_setReg_other _ _ _ _ h10])
  · simp (config := { decide := true }) only [nocompiler_state]
  · simp only [nocompiler_state]
  · simp only [nocompiler_state]

/-- `__syscall_ret` and `___errno_location`, in the image. -/
def __syscall_ret_dom : Dom := [(0x122c0#64, 60), (0x122fc#64, 12)]

/-- `__syscall_ret(r)` at the process level: its machine-level specification `syscallRetSpec`'s
    precondition (as `Spec.toP`'s), and on return a0 as `syscallRetSpec` says, the kernel and the trace
    unchanged, memory outside errno and its 16-byte frame unchanged. -/
def syscallRetP : SpecP Word where
  pre := syscallRetSpec.toP.pre
  post := fun r x y => y.1.reg 10 = (if r.toNat < 2 ^ 64 - 4095 then r else -1) ∧ y.2 = x.2 ∧
    y.1.trace = x.1.trace ∧
    ∀ p, ¬ (Region.mk (x.1.reg 4 + 18446744073709551452#64) 4).mem p →
      ¬ (Region.mk (x.1.reg 2 - 16#64) 16).mem p → y.1.mem p = x.1.mem p

abbrev SysRetQ (r : Word) (s : State) (k : Kern) : State × Kern → Prop :=
  fun y => Final __syscall_ret_dom y.1 ∧ syscallRetP.Done r (s, k) y

theorem not_one_eight_of_preserved : ∀ q ∈ preservedRegs, q ≠ 2 → q ≠ 8 →
    q ≠ 1 ∧ q ≠ 10 ∧ q ≠ 11 := by decide

/-- `__syscall_ret`'s error path from its call of `__errno_location` (state `p0`) on. -/
theorem sysret_err (r : Word) (s : State) (k : Kern) (he : Entry __syscall_ret_dom __syscall_ret_entry s)
    (hal : aligned (s.reg 4 + 18446744073709551452#64) 4)
    (hdisj : (Region.mk (s.reg 4 + 18446744073709551452#64) 4).Disjoint ⟨s.reg 2 - 16#64, 16⟩)
    (hW : ∀ a n, ((Region.mk (s.reg 4 + 18446744073709551452#64) 4).covers a n ∨
      (Region.mk (s.reg 2 - 16#64) 16).covers a n) → k.perm.canWrite a n)
    (hb : ¬ r.toNat < 2 ^ 64 - 4095)
    (p0 : State) (hpc : p0.pc = 0x122fc#64) (hx : p0.exit = none) (htr0 : p0.trace = s.trace)
    (hra : p0.reg 1 = 0x122e4#64)
    (h2 : p0.reg 2 = s.reg 2 - 16#64) (h4 : p0.reg 4 = s.reg 4)
    (hpr : ∀ q ∈ preservedRegs, q ≠ 2 → q ≠ 8 → p0.reg q = s.reg q)
    (hm : p0.mem = writeLE (writeLE s.mem (s.reg 2 - 8#64) (s.reg 1).toNat 8) (s.reg 2 - 16#64)
      (s.reg 8).toNat 8) :
    PReachK img __syscall_ret_dom (SysRetQ r s k) (p0, k) := by
  have hsp := he.sp
  have hra4 := he.retAligned
  have hret := he.ret
  simp only [Reg.sp, Reg.ra] at hsp hra4 hret
  have hent : Entry ___errno_location_dom ___errno_location_entry p0 :=
    ⟨hpc, hx, by rw [Reg.ra, hra]; decide, by rw [Reg.ra, hra]; decide,
      by rw [Reg.sp, h2]; unfold aligned at *; bv_omega⟩
  refine VerifiedProc.call ___errno_location_proc () hent trivial (Dom.sub_of_ranges (by decide)) ?_
  rintro ⟨w, kw⟩ (⟨hx1, hpc1, hpres1, h10, hk1, htr1, hm1⟩ | ⟨_, hex1⟩)
  · simp only at hx1 hpc1 hpres1 h10 hk1 htr1 hm1
    rw [Reg.ra, hra] at hpc1
    have h10' : w.reg 10 = s.reg 4 + 18446744073709551452#64 := by rw [← h4]; exact h10
    have hwm : w.mem = p0.mem := hm1
    have hw2 : w.reg 2 = s.reg 2 - 16#64 := by rw [hpres1 2 (by decide), h2]
    have e8 : s.reg 2 - 16#64 + 8#64 = s.reg 2 - 8#64 := by bv_omega
    have al8 : aligned (s.reg 2 - 8#64) 8 := by unfold aligned at *; bv_omega
    have al16 : aligned (s.reg 2 - 16#64) 8 := by unfold aligned at *; bv_omega
    have hwe : kw.perm.canWrite (s.reg 4 + 18446744073709551452#64) 4 := by
      rw [hk1]; exact hW _ _ (.inl (by simp [Region.covers]))
    have hr8 : kw.perm.canRead (s.reg 2 - 8#64) 8 := by
      rw [hk1]; exact Perm.canRead_of_canWrite (hW _ _ (.inr (by simp only [Region.covers]; bv_omega)))
    have hr16 : kw.perm.canRead (s.reg 2 - 16#64) 8 := by
      rw [hk1]; exact Perm.canRead_of_canWrite (hW _ _ (.inr (by simp only [Region.covers]; bv_omega)))
    have d8 : (Region.mk (s.reg 4 + 18446744073709551452#64) 4).Disjoint ⟨s.reg 2 - 8#64, 8⟩ := by
      unfold Region.Disjoint at *; simp only at *; bv_omega
    have d16 : (Region.mk (s.reg 4 + 18446744073709551452#64) 4).Disjoint ⟨s.reg 2 - 16#64, 8⟩ := by
      unfold Region.Disjoint at *; simp only at *; bv_omega
    have d816 : (Region.mk (s.reg 2 - 8#64) 8).Disjoint ⟨s.reg 2 - 16#64, 8⟩ := by
      unfold Region.Disjoint at *; simp only at *; bv_omega
    have hrd8 : read64 (writeLE w.mem (s.reg 4 + 18446744073709551452#64) (w.reg 8).toNat 4) (s.reg 2 - 8#64)
        = s.reg 1 := by
      rw [Auto.read64_writeLE_of_disjoint d8 _ _ _ _ (by simp [Region.covers]), hwm, hm,
        Auto.read64_writeLE_of_disjoint d816.symm _ _ _ _ (by simp [Region.covers]), Auto.read64_writeLE_same']
      simp
    have hrd16 : read64 (writeLE w.mem (s.reg 4 + 18446744073709551452#64) (w.reg 8).toNat 4) (s.reg 2 - 16#64)
        = s.reg 8 := by
      rw [Auto.read64_writeLE_of_disjoint d16 _ _ _ _ (by simp [Region.covers]), hwm, hm,
        Auto.read64_writeLE_same']
      simp
    nocompiler_pstep [hpc1, h10', hal, BitVec.add_zero]
    refine ⟨hwe, ?_⟩
    nocompiler_pstep
    nocompiler_pstep [hw2, e8, al8]
    refine ⟨hr8, ?_⟩
    nocompiler_pstep [hw2, al16]
    refine ⟨hr16, ?_⟩
    nocompiler_pstep [hrd8, hrd16, hw2]
    nocompiler_pstep [hrd8, hrd16, ret_mask hra4, hra4]
    refine .done ⟨.inl ?_, .inl ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · simp only [nocompiler_state]; exact hret
    · simp only [nocompiler_state]; exact hx1
    · simp only [nocompiler_state, Reg.ra]
    · intro q hq
      by_cases hq2 : q = 2
      · subst hq2; simp (config := { decide := true }) only [nocompiler_state]; bv_omega
      by_cases hq8 : q = 8
      · subst hq8; simp (config := { decide := true }) only [nocompiler_state]
      obtain ⟨hq1, hq10, -⟩ := not_one_eight_of_preserved q hq hq2 hq8
      simp only [State.setPc_reg, State.setMem_reg, State.reg_setReg_other _ _ _ _ hq1,
        State.reg_setReg_other _ _ _ _ hq2, State.reg_setReg_other _ _ _ _ hq8,
        State.reg_setReg_other _ _ _ _ hq10]
      rw [hpres1 q hq, hpr q hq hq2 hq8]
    · simp (config := { decide := true }) only [nocompiler_state, hb, ↓reduceIte]
    · exact hk1
    · simp only [nocompiler_state]; rw [htr1, htr0]
    · intro p hpe hps
      simp only [nocompiler_state]
      rw [writeLE_of_not_mem (by simp [Region.covers]) hpe, hwm, hm,
        writeLE_of_not_mem (r := ⟨s.reg 2 - 16#64, 16⟩) (by simp only [Region.covers]; bv_omega) hps,
        writeLE_of_not_mem (r := ⟨s.reg 2 - 16#64, 16⟩) (by simp only [Region.covers]; bv_omega) hps]
  · exact hex1.elim


theorem sext32_4095 : (sext32 18446744073709547521#64 : Word) = 18446744073709547521#64 := by decide

/-- `__syscall_ret(r)` as compiled, at the process level: `r` if it is not an error img, else `-1` with
    errno (at `tp - 164`) set to `-r`; its frame and errno are all it writes. By hand (nocompiler_auto
    on it: STATUS-A). -/
theorem __syscall_ret_verified : VerifiedProc img __syscall_ret_dom __syscall_ret_entry syscallRetP := by
  intro r s k he ⟨⟨ha0, hal, hdisj⟩, hle⟩
  have hpc := he.pc
  have hx := he.live
  have hsp := he.sp
  have hra4 := he.retAligned
  have hret := he.ret
  simp only [__syscall_ret_entry] at hpc
  simp only [Reg.sp, Reg.a0, Reg.ra, Reg.tp] at ha0 hal hdisj hsp hra4 hret
  have hdisj' : (Region.mk (s.reg 4 + 18446744073709551452#64) 4).Disjoint ⟨s.reg 2 - 16#64, 16⟩ := by
    simpa [Spec.stackRegion] using hdisj
  have hW : ∀ a n, ((Region.mk (s.reg 4 + 18446744073709551452#64) 4).covers a n ∨
      (Region.mk (s.reg 2 - 16#64) 16).covers a n) → k.perm.canWrite a n := by
    intro a n h; apply hle.write; right
    rcases h with h | h
    · exact ⟨_, by simp [Spec.perm, syscallRetSpec, Reg.tp], h⟩
    · exact ⟨_, by simp [Spec.perm, syscallRetSpec, Spec.stackRegion, Reg.sp], h⟩
  nocompiler_pstep [hpc]
  nocompiler_pstep
  nocompiler_pstep [ha0, sext32_4095]
  by_cases hb : r.toNat < 2 ^ 64 - 4095
  · have hu : BitVec.ult r 18446744073709547521#64 = true := by simpa [BitVec.ult] using hb
    rw [hu]
    simp only [↓reduceIte, PReachK.opt_some]
    nocompiler_pstep [ret_mask hra4, hra4]
    refine .done ⟨.inl ?_, .inl ⟨?_, ?_, ?_, ?_, rfl, by simp only [nocompiler_state], fun _ _ _ => rfl⟩⟩
    · simp only [nocompiler_state]; exact hret
    · simp only [nocompiler_state]; exact hx
    · simp only [nocompiler_state, Reg.ra]
    · intro q hq
      have hq11 : q ≠ 11 := by revert hq; revert q; decide
      simp only [State.setPc_reg, State.reg_setReg_other _ _ _ _ hq11]
    · simp (config := { decide := true }) only [nocompiler_state, hb, ↓reduceIte, ha0]
  · have hu : BitVec.ult r 18446744073709547521#64 = false := by simpa [BitVec.ult] using hb
    rw [hu]
    simp only [Bool.false_eq_true, ↓reduceIte, PReachK.opt_some]
    have e16 : s.reg 2 + 18446744073709551600#64 = s.reg 2 - 16#64 := by bv_omega
    have e8 : s.reg 2 - 16#64 + 8#64 = s.reg 2 - 8#64 := by bv_omega
    have al8 : aligned (s.reg 2 - 8#64) 8 := by unfold aligned at *; bv_omega
    have al16 : aligned (s.reg 2 - 16#64) 8 := by unfold aligned at *; bv_omega
    nocompiler_pstep
    nocompiler_pstep [e8, e16, al8]
    refine ⟨hW _ _ (.inr (by simp only [Region.covers]; bv_omega)), ?_⟩
    nocompiler_pstep [al16]
    refine ⟨hW _ _ (.inr (by simp only [Region.covers]; bv_omega)), ?_⟩
    nocompiler_pstep
    nocompiler_pstep
    nocompiler_pstep
    refine sysret_err r s k he hal hdisj' hW hb _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals (try simp (config := { decide := true }) only [nocompiler_state, hx])
    intro q hq hq2 hq8
    obtain ⟨hq1, -, hq11⟩ := not_one_eight_of_preserved q hq hq2 hq8
    simp only [State.setPc_reg, State.setMem_reg, State.reg_setReg_other _ _ _ _ hq1,
      State.reg_setReg_other _ _ _ _ hq2, State.reg_setReg_other _ _ _ _ hq8]
    iterate 2 (try simp only [State.setPc_reg, State.reg_setReg_other _ _ _ _ hq11])

/-! ## `__stdio_write` (musl src/stdio/__stdio_write.c)

```c
size_t __stdio_write(FILE *f, const unsigned char *buf, size_t len)
{
	struct iovec iovs[2] = {
		{ .iov_base = f->wbase, .iov_len = f->wpos-f->wbase },
		{ .iov_base = (void *)buf, .iov_len = len }
	};
	struct iovec *iov = iovs;
	size_t rem = iov[0].iov_len + iov[1].iov_len;
	int iovcnt = 2;
	ssize_t cnt;
	for (;;) {
		cnt = syscall(SYS_writev, f->fd, iov, iovcnt);
		if (cnt == rem) {
			f->wend = f->buf + f->buf_size;
			f->wpos = f->wbase = f->buf;
			return len;
		}
		if (cnt < 0) {
			f->wpos = f->wbase = f->wend = 0;
			f->flags |= F_ERR;
			return iovcnt == 2 ? 0 : len-iov[0].iov_len;
		}
		rem -= cnt;
		if (cnt > iov[0].iov_len) {
			cnt -= iov[0].iov_len;
			iov++; iovcnt--;
		}
		iov[0].iov_base = (char *)iov[0].iov_base + cnt;
		iov[0].iov_len -= cnt;
	}
}
```
FILE's fields in this build: `flags` 0 (4 bytes), `wend` 32, `wpos` 40, `wbase` 56, `buf` 88, `buf_size` 96,
`fd` 120 (4 bytes, sign-extended); `F_ERR` is 32. -/

/-- The bytes of an event list's writes. -/
def evBytes : Event → List Byte
  | .write _ bs => bs
  | _ => []

/-- `evs` are writes to `fd` whose bytes, in order, are `bs`. -/
def WritesOf (fd : Word) (evs : List Event) (bs : List Byte) : Prop :=
  (∀ e ∈ evs, ∃ b, e = .write fd b) ∧ evs.flatMap evBytes = bs

/-- The descriptor in `f->fd`, as `lw` loads it. -/
def fdOf (m : Word → Byte) (f : Word) : Word := (BitVec.ofNat 32 (readLE m (f + 120#64) 4)).signExtend 64

/-- What `__stdio_write(f, buf, len)` is asked to write: the buffered bytes `[wbase, wpos)`, then `buf`. -/
def stdioBytes (m : Word → Byte) (f buf len : Word) : List Byte :=
  readBytes m (read64 m (f + 56#64)) (read64 m (f + 40#64) - read64 m (f + 56#64)).toNat ++
    readBytes m buf len.toNat

/-- The number of buffered bytes. -/
def stdioPend (m : Word → Byte) (f : Word) : Nat := (read64 m (f + 40#64) - read64 m (f + 56#64)).toNat

/-- The regions `__stdio_write` may write: FILE's first 128 bytes, its 96-byte frame and the 16 bytes of
    `__syscall_ret`'s below it, errno. -/
def stdioWritePerm (f : Word) (s : State) : Perm :=
  { rd := [], wr := [⟨f, 128⟩, ⟨s.reg 2 - 112#64, 112⟩, ⟨s.reg 4 + 18446744073709551452#64, 4⟩] }

/-- `__stdio_write(f, buf, len)` at the process level. Precondition: the arguments; `f` 8-byte aligned;
    errno 4-byte aligned; FILE's first 128 bytes, the 112 bytes below sp and errno pairwise disjoint and
    writable; the bytes to write outside the stack and errno (two facts each); their count below 2^63. Postcondition: the
    kernel unchanged; the new events are writes to `f->fd`: on success all of `stdioBytes` (a0 = len,
    wend = buf + buf_size, wpos = wbase = buf), on error a prefix `n` (a0 = 0 if `n ≤` the buffered
    count, else `n` minus it; wpos = wbase = wend = 0, F_ERR set); memory outside the stack, errno and
    those fields unchanged. -/
def stdioWriteSpec : SpecP (Word × Word × Word) where
  pre := fun ⟨f, buf, len⟩ s k =>
    s.reg 10 = f ∧ s.reg 11 = buf ∧ s.reg 12 = len ∧ aligned f 8 ∧
    aligned (s.reg 4 + 18446744073709551452#64) 4 ∧
    (stdioWritePerm f s).le k.perm ∧
    (Region.mk f 128).Disjoint ⟨s.reg 2 - 112#64, 112⟩ ∧
    (Region.mk (s.reg 4 + 18446744073709551452#64) 4).Disjoint ⟨s.reg 2 - 112#64, 112⟩ ∧
    (Region.mk (s.reg 4 + 18446744073709551452#64) 4).Disjoint ⟨f, 128⟩ ∧
    (Region.mk (read64 s.mem (f + 56#64)) (stdioPend s.mem f)).Disjoint ⟨s.reg 2 - 112#64, 112⟩ ∧
    (Region.mk buf len.toNat).Disjoint ⟨s.reg 2 - 112#64, 112⟩ ∧
    (Region.mk (read64 s.mem (f + 56#64)) (stdioPend s.mem f)).Disjoint ⟨s.reg 4 + 18446744073709551452#64, 4⟩ ∧
    (Region.mk buf len.toNat).Disjoint ⟨s.reg 4 + 18446744073709551452#64, 4⟩ ∧
    stdioPend s.mem f + len.toNat < 2 ^ 63 ∧ (fdOf s.mem f).toNat < 2 ^ 31
  post := fun ⟨f, buf, len⟩ x y =>
    y.2 = x.2 ∧ ∃ evs, y.1.trace = x.1.trace ++ evs ∧
    (∀ p, ¬ (Region.mk (x.1.reg 2 - 112#64) 112).mem p → ¬ (Region.mk (x.1.reg 4 + 18446744073709551452#64) 4).mem p →
      ¬ (Region.mk f 4).mem p → ¬ (Region.mk (f + 32#64) 16).mem p → ¬ (Region.mk (f + 56#64) 8).mem p →
      y.1.mem p = x.1.mem p) ∧
    ((WritesOf (fdOf x.1.mem f) evs (stdioBytes x.1.mem f buf len) ∧ y.1.reg 10 = len ∧
        read64 y.1.mem (f + 32#64) = read64 x.1.mem (f + 88#64) + read64 x.1.mem (f + 96#64) ∧
        read64 y.1.mem (f + 40#64) = read64 x.1.mem (f + 88#64) ∧
        read64 y.1.mem (f + 56#64) = read64 x.1.mem (f + 88#64) ∧
        readLE y.1.mem f 4 = readLE x.1.mem f 4) ∨
     (∃ n, n ≤ (stdioBytes x.1.mem f buf len).length ∧
        WritesOf (fdOf x.1.mem f) evs ((stdioBytes x.1.mem f buf len).take n) ∧
        y.1.reg 10 = (if n ≤ stdioPend x.1.mem f then 0 else BitVec.ofNat 64 (n - stdioPend x.1.mem f)) ∧
        read64 y.1.mem (f + 32#64) = 0 ∧ read64 y.1.mem (f + 40#64) = 0 ∧ read64 y.1.mem (f + 56#64) = 0 ∧
        readLE y.1.mem f 4 = (BitVec.ofNat 32 (readLE x.1.mem f 4) ||| 32#32).toNat))


/-- What holds at every cut of `__stdio_write`'s run from its entry state `s` (frame at `sp - 96`): its
    registers (s1 = f, s0 = len, the callee-saved ones it does not use as at entry), the seven saved
    registers in their slots, memory outside the 112 bytes below sp and errno as at entry. -/
def SwCommon (s : State) (f len : Word) (u : State) : Prop :=
  u.exit = none ∧ u.reg 2 = s.reg 2 - 96#64 ∧ u.reg 9 = f ∧ u.reg 8 = len ∧
  (∀ q ∈ [(3 : Reg), 4, 22, 23, 24, 25, 26, 27], u.reg q = s.reg q) ∧
  read64 u.mem (s.reg 2 - 8#64) = s.reg 1 ∧ read64 u.mem (s.reg 2 - 16#64) = s.reg 8 ∧
  read64 u.mem (s.reg 2 - 24#64) = s.reg 9 ∧ read64 u.mem (s.reg 2 - 32#64) = s.reg 18 ∧
  read64 u.mem (s.reg 2 - 40#64) = s.reg 19 ∧ read64 u.mem (s.reg 2 - 48#64) = s.reg 20 ∧
  read64 u.mem (s.reg 2 - 56#64) = s.reg 21 ∧
  ∀ p, ¬ (Region.mk (s.reg 2 - 112#64) 112).mem p → ¬ (Region.mk (s.reg 4 + 18446744073709551452#64) 4).mem p →
    u.mem p = s.mem p

abbrev SwQ (f buf len : Word) (s : State) (k : Kern) : State × Kern → Prop :=
  fun y => Final dom y.1 ∧ stdioWriteSpec.Done (f, buf, len) (s, k) y



theorem sw_alF {f : Word} (hal : aligned f 8) (o : Nat) (h1 : o % 8 = 0) :
    aligned (f + BitVec.ofNat 64 o) 8 := by
  unfold aligned at *; bv_omega

theorem sw_alS {sp : Word} (hsp : aligned sp 16) (o : Nat) (h1 : o % 8 = 0) :
    aligned (sp - BitVec.ofNat 64 o) 8 := by
  unfold aligned at *; bv_omega

theorem sw_eS (sp : Word) (o : Nat) (h : o ≤ 96) : sp - 96#64 + BitVec.ofNat 64 o = sp - BitVec.ofNat 64 (96 - o) := by
  bv_omega

theorem sw_cF (f : Word) (o n : Nat) (h : o + n ≤ 128) : (Region.mk f 128).covers (f + BitVec.ofNat 64 o) n := by
  simp only [Region.covers]; bv_omega

theorem sw_cS (sp : Word) (o n : Nat) (h1 : n ≤ o) (h2 : o ≤ 112) :
    (Region.mk (sp - 112#64) 112).covers (sp - BitVec.ofNat 64 o) n := by
  simp only [Region.covers]; bv_omega

/-- A FILE field and a stack slot do not overlap. -/
theorem sw_dFS {f sp : Word} (h : (Region.mk f 128).Disjoint ⟨sp - 112#64, 112⟩) (o n q : Nat)
    (h1 : o + n ≤ 128) (h0 : 0 < n) (h2 : 8 ≤ q) (h3 : q ≤ 112) :
    (Region.mk (f + BitVec.ofNat 64 o) n).Disjoint ⟨sp - BitVec.ofNat 64 q, 8⟩ := by
  simp only [Region.Disjoint] at *; bv_omega

/-- A FILE byte is outside the stack and errno. -/
theorem sw_outF {f sp e : Word} (h : (Region.mk f 128).Disjoint ⟨sp - 112#64, 112⟩)
    (h' : (Region.mk e 4).Disjoint ⟨f, 128⟩) (o : Nat) (ho : o < 128) :
    ¬ (Region.mk (sp - 112#64) 112).mem (f + BitVec.ofNat 64 o) ∧ ¬ (Region.mk e 4).mem (f + BitVec.ofNat 64 o) := by
  simp only [Region.Disjoint, Region.mem] at *; constructor <;> bv_omega

/-- Writable by `__stdio_write`'s permission, by region. -/
theorem sw_canWrite {f : Word} {s : State} {k : Kern} (hle : (stdioWritePerm f s).le k.perm) {a : Word} {n : Nat}
    (h : (Region.mk f 128).covers a n ∨ (Region.mk (s.reg 2 - 112#64) 112).covers a n ∨
      (Region.mk (s.reg 4 + 18446744073709551452#64) 4).covers a n) : k.perm.canWrite a n := by
  apply hle.write; right
  rcases h with h | h | h
  · exact ⟨_, by simp [stdioWritePerm], h⟩
  · exact ⟨_, by simp [stdioWritePerm], h⟩
  · exact ⟨_, by simp [stdioWritePerm], h⟩


/-- Two FILE fields that do not overlap. -/
theorem sw_dFF (f : Word) (o1 n1 o2 n2 : Nat) (h : o1 + n1 ≤ o2 ∨ o2 + n2 ≤ o1) (h1 : o1 + n1 ≤ 128)
    (h2 : o2 + n2 ≤ 128) (h0 : 0 < n1) (h0' : 0 < n2) :
    (Region.mk (f + BitVec.ofNat 64 o1) n1).Disjoint ⟨f + BitVec.ofNat 64 o2, n2⟩ := by
  simp only [Region.Disjoint]; bv_omega

theorem sw_notsub {f p : Word} (o n o' n' : Nat) (h : o ≤ o') (h' : o' + n' ≤ o + n) (hn : o + n ≤ 128)
    (hp : ¬ (Region.mk (f + BitVec.ofNat 64 o) n).mem p) : ¬ (Region.mk (f + BitVec.ofNat 64 o') n').mem p := by
  intro hm; apply hp; simp only [Region.mem] at *; bv_omega

theorem sw_e96 (sp : Word) : sp - 96#64 + 96#64 = sp := by bv_omega

/-- The success exit, from 0x124ec. -/
theorem sw_succ (f buf len : Word) (s : State) (k : Kern) (he : Entry dom __stdio_write_entry s)
    (hpre : stdioWriteSpec.pre (f, buf, len) s k)
    (u : State) (hpc : u.pc = 0x124ec#64) (hc : SwCommon s f len u) (evs : List Event)
    (htr : u.trace = s.trace ++ evs) (hw : WritesOf (fdOf s.mem f) evs (stdioBytes s.mem f buf len)) :
    PReachK img dom (SwQ f buf len s k) (u, k) := by
  obtain ⟨ha0, ha1, ha2, hal, hale, hle, dFS, dES, dEF, -, -, -, -, -⟩ := hpre
  obtain ⟨hx, h2, h9, h8, hpr, s1, s2, s3, s4, s5, s6, s7, hfr⟩ := hc
  have hsp := he.sp
  have hra4 := he.retAligned
  have hret := he.ret
  simp only [Reg.sp, Reg.ra] at hsp hra4 hret
  have hF : ∀ o, o + 8 ≤ 128 → read64 u.mem (f + BitVec.ofNat 64 o) = read64 s.mem (f + BitVec.ofNat 64 o) := by
    intro o ho
    apply read64_congr_on; intro j hj
    have hj' := sw_outF dFS dEF (o + j) (by omega)
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact hfr _ hj'.1 hj'.2
  have h88 := hF 88 (by omega)
  have h96 := hF 96 (by omega)
  have hW := fun {a n} h => sw_canWrite (a := a) (n := n) hle h
  have alF := sw_alF hal
  have rF : ∀ o, o + 8 ≤ 128 → k.perm.canRead (f + BitVec.ofNat 64 o) 8 := fun o ho =>
    Perm.canRead_of_canWrite (hW (.inl (sw_cF f o 8 ho)))
  have wF : ∀ o, o + 8 ≤ 128 → k.perm.canWrite (f + BitVec.ofNat 64 o) 8 := fun o ho => hW (.inl (sw_cF f o 8 ho))
  have rS : ∀ o, 8 ≤ o → o ≤ 112 → k.perm.canRead (s.reg 2 - BitVec.ofNat 64 o) 8 := fun o h1 h2 =>
    Perm.canRead_of_canWrite (hW (.inr (.inl (sw_cS _ o 8 h1 h2))))
  have hS : ∀ o, 8 ≤ o → o ≤ 112 → ∀ v1 v0 : Nat,
      read64 (writeLE (writeLE (writeLE u.mem (f + 32#64) v1 8) (f + 56#64) v0 8) (f + 40#64) v0 8)
        (s.reg 2 - BitVec.ofNat 64 o) = read64 u.mem (s.reg 2 - BitVec.ofNat 64 o) := by
    intro o h1 h2 v1 v0
    rw [Auto.read64_writeLE_of_disjoint (sw_dFS dFS 40 8 o (by omega) (by omega) h1 h2) _ _ _ _ (by simp [Region.covers]),
      Auto.read64_writeLE_of_disjoint (sw_dFS dFS 56 8 o (by omega) (by omega) h1 h2) _ _ _ _ (by simp [Region.covers]),
      Auto.read64_writeLE_of_disjoint (sw_dFS dFS 32 8 o (by omega) (by omega) h1 h2) _ _ _ _ (by simp [Region.covers])]
  nocompiler_pstep [hpc, h9, alF 88 rfl]
  refine ⟨rF 88 (by omega), ?_⟩
  nocompiler_pstep [h9, alF 96 rfl]
  refine ⟨rF 96 (by omega), ?_⟩
  nocompiler_pstep
  nocompiler_pstep [h9, alF 32 rfl]
  refine ⟨wF 32 (by omega), ?_⟩
  nocompiler_pstep [h9, alF 56 rfl]
  refine ⟨wF 56 (by omega), ?_⟩
  nocompiler_pstep [h9, alF 40 rfl]
  refine ⟨wF 40 (by omega), ?_⟩
  nocompiler_pstep [h8]
  nocompiler_pstep [h2, sw_eS (s.reg 2) 88 (by omega), sw_alS hsp 8 rfl, hS 8 (by omega) (by omega), s1]
  refine ⟨rS 8 (by omega) (by omega), ?_⟩
  nocompiler_pstep [h2, sw_eS (s.reg 2) 80 (by omega), sw_alS hsp 16 rfl, hS 16 (by omega) (by omega), s2]
  refine ⟨rS 16 (by omega) (by omega), ?_⟩
  nocompiler_pstep [h2, sw_eS (s.reg 2) 72 (by omega), sw_alS hsp 24 rfl, hS 24 (by omega) (by omega), s3]
  refine ⟨rS 24 (by omega) (by omega), ?_⟩
  nocompiler_pstep [h2, sw_eS (s.reg 2) 64 (by omega), sw_alS hsp 32 rfl, hS 32 (by omega) (by omega), s4]
  refine ⟨rS 32 (by omega) (by omega), ?_⟩
  nocompiler_pstep [h2, sw_eS (s.reg 2) 56 (by omega), sw_alS hsp 40 rfl, hS 40 (by omega) (by omega), s5]
  refine ⟨rS 40 (by omega) (by omega), ?_⟩
  nocompiler_pstep [h2, sw_eS (s.reg 2) 48 (by omega), sw_alS hsp 48 rfl, hS 48 (by omega) (by omega), s6]
  refine ⟨rS 48 (by omega) (by omega), ?_⟩
  nocompiler_pstep [h2, sw_eS (s.reg 2) 40 (by omega), sw_alS hsp 56 rfl, hS 56 (by omega) (by omega), s7]
  refine ⟨rS 56 (by omega) (by omega), ?_⟩
  nocompiler_pstep [h2]
  nocompiler_pstep [ret_mask hra4, hra4]
  refine .done ⟨.inl ?_, .inl ⟨?_, ?_, ?_, ?_⟩⟩
  · simp only [nocompiler_state]; exact hret
  · simp only [nocompiler_state]; exact hx
  · simp only [nocompiler_state, Reg.ra]
  · intro q hq
    simp only [preservedRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals (simp (config := { decide := true }) only [nocompiler_state, sw_e96])
    all_goals (exact hpr _ (by simp))
  · refine ⟨rfl, evs, by simp only [nocompiler_state]; exact htr, ?_, .inl ⟨hw, ?_, ?_, ?_, ?_, ?_⟩⟩
    · intro p hp1 hp2 hp3 hp4 hp5
      simp only [nocompiler_state]
      rw [writeLE_of_not_mem (r := ⟨f + 40#64, 8⟩) (by simp [Region.covers]) (sw_notsub 32 16 40 8 (by omega) (by omega) (by omega) hp4),
        writeLE_of_not_mem (r := ⟨f + 56#64, 8⟩) (by simp [Region.covers]) hp5,
        writeLE_of_not_mem (r := ⟨f + 32#64, 8⟩) (by simp [Region.covers]) (sw_notsub 32 16 32 8 (by omega) (by omega) (by omega) hp4)]
      exact hfr p hp1 hp2
    · simp (config := { decide := true }) only [nocompiler_state]
    · simp only [nocompiler_state]
      rw [Auto.read64_writeLE_of_disjoint (sw_dFF f 40 8 32 8 (by omega) (by omega) (by omega) (by omega) (by omega)) _ _ _ _ (by simp [Region.covers]),
        Auto.read64_writeLE_of_disjoint (sw_dFF f 56 8 32 8 (by omega) (by omega) (by omega) (by omega) (by omega)) _ _ _ _ (by simp [Region.covers]),
        Auto.read64_writeLE_same', h88, h96]
      simp only [BitVec.toNat_add]; bv_omega
    · simp only [nocompiler_state]
      rw [Auto.read64_writeLE_same', h88]
      simp
    · simp only [nocompiler_state]
      rw [Auto.read64_writeLE_of_disjoint (sw_dFF f 40 8 56 8 (by omega) (by omega) (by omega) (by omega) (by omega)) _ _ _ _ (by simp [Region.covers]),
        Auto.read64_writeLE_same', h88]
      simp
    · simp only [nocompiler_state]
      have d40 := sw_dFF f 40 8 0 4 (by omega) (by omega) (by omega) (by omega) (by omega)
      have d56 := sw_dFF f 56 8 0 4 (by omega) (by omega) (by omega) (by omega) (by omega)
      have d32 := sw_dFF f 32 8 0 4 (by omega) (by omega) (by omega) (by omega) (by omega)
      simp only [BitVec.add_zero] at d40 d56 d32
      rw [readLE_writeLE_disj d40 _ _ _ _ (by simp [Region.covers]), readLE_writeLE_disj d56 _ _ _ _ (by simp [Region.covers]),
        readLE_writeLE_disj d32 _ _ _ _ (by simp [Region.covers])]
      apply readLE_congr; intro j hj
      have hj' := sw_outF dFS dEF j (by omega)
      exact hfr _ hj'.1 hj'.2


/-- The epilogue, from 0x12508 (a0 already the result): the seven saved registers reloaded, the frame
    popped, the return; the post is the caller's, for the state's memory, trace and a0. -/
theorem sw_epi (f buf len : Word) (s : State) (k : Kern) (he : Entry dom __stdio_write_entry s)
    (hle : (stdioWritePerm f s).le k.perm)
    (u : State) (hpc : u.pc = 0x12508#64) (hx : u.exit = none) (h2 : u.reg 2 = s.reg 2 - 96#64)
    (hpr : ∀ q ∈ [(3 : Reg), 4, 22, 23, 24, 25, 26, 27], u.reg q = s.reg q)
    (s1 : read64 u.mem (s.reg 2 - 8#64) = s.reg 1) (s2 : read64 u.mem (s.reg 2 - 16#64) = s.reg 8)
    (s3 : read64 u.mem (s.reg 2 - 24#64) = s.reg 9) (s4 : read64 u.mem (s.reg 2 - 32#64) = s.reg 18)
    (s5 : read64 u.mem (s.reg 2 - 40#64) = s.reg 19) (s6 : read64 u.mem (s.reg 2 - 48#64) = s.reg 20)
    (s7 : read64 u.mem (s.reg 2 - 56#64) = s.reg 21)
    (hpost : ∀ y : State × Kern, y.2 = k → y.1.mem = u.mem → y.1.trace = u.trace → y.1.reg 10 = u.reg 10 →
      stdioWriteSpec.post (f, buf, len) (s, k) y) :
    PReachK img dom (SwQ f buf len s k) (u, k) := by
  have hsp := he.sp
  have hra4 := he.retAligned
  have hret := he.ret
  simp only [Reg.sp, Reg.ra] at hsp hra4 hret
  have hW := fun {a n} h => sw_canWrite (a := a) (n := n) hle h
  have rS : ∀ o, 8 ≤ o → o ≤ 112 → k.perm.canRead (s.reg 2 - BitVec.ofNat 64 o) 8 := fun o h1 h2 =>
    Perm.canRead_of_canWrite (hW (.inr (.inl (sw_cS _ o 8 h1 h2))))
  nocompiler_pstep [hpc, h2, sw_eS (s.reg 2) 88 (by omega), sw_alS hsp 8 rfl, s1]
  refine ⟨rS 8 (by omega) (by omega), ?_⟩
  nocompiler_pstep [h2, sw_eS (s.reg 2) 80 (by omega), sw_alS hsp 16 rfl, s2]
  refine ⟨rS 16 (by omega) (by omega), ?_⟩
  nocompiler_pstep [h2, sw_eS (s.reg 2) 72 (by omega), sw_alS hsp 24 rfl, s3]
  refine ⟨rS 24 (by omega) (by omega), ?_⟩
  nocompiler_pstep [h2, sw_eS (s.reg 2) 64 (by omega), sw_alS hsp 32 rfl, s4]
  refine ⟨rS 32 (by omega) (by omega), ?_⟩
  nocompiler_pstep [h2, sw_eS (s.reg 2) 56 (by omega), sw_alS hsp 40 rfl, s5]
  refine ⟨rS 40 (by omega) (by omega), ?_⟩
  nocompiler_pstep [h2, sw_eS (s.reg 2) 48 (by omega), sw_alS hsp 48 rfl, s6]
  refine ⟨rS 48 (by omega) (by omega), ?_⟩
  nocompiler_pstep [h2, sw_eS (s.reg 2) 40 (by omega), sw_alS hsp 56 rfl, s7]
  refine ⟨rS 56 (by omega) (by omega), ?_⟩
  nocompiler_pstep [h2]
  nocompiler_pstep [ret_mask hra4, hra4]
  refine .done ⟨.inl ?_, .inl ⟨?_, ?_, ?_, ?_⟩⟩
  · simp only [nocompiler_state]; exact hret
  · simp only [nocompiler_state]; exact hx
  · simp only [nocompiler_state, Reg.ra]
  · intro q hq
    simp only [preservedRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals (simp (config := { decide := true }) only [nocompiler_state, sw_e96])
    all_goals (exact hpr _ (by simp))
  · exact hpost _ rfl (by simp only [nocompiler_state]) (by simp only [nocompiler_state])
      (by simp (config := { decide := true }) only [nocompiler_state])


theorem sw_subsub (a b : Word) : a - (a - b) = b := by bv_omega

theorem sw_al4 {f : Word} (hal : aligned f 8) : aligned f 4 := by unfold aligned at *; omega

/-- The error exit, from 0x125ac: `n` bytes written, then an error. -/
theorem sw_err (f buf len : Word) (s : State) (k : Kern) (he : Entry dom __stdio_write_entry s)
    (hpre : stdioWriteSpec.pre (f, buf, len) s k)
    (u : State) (hpc : u.pc = 0x125ac#64) (hc : SwCommon s f len u) (n : Nat) (evs : List Event)
    (htr : u.trace = s.trace ++ evs) (hn : n ≤ (stdioBytes s.mem f buf len).length)
    (hev : WritesOf (fdOf s.mem f) evs ((stdioBytes s.mem f buf len).take n))
    (hcnt : (u.reg 18 = 2#64 ∧ n ≤ stdioPend s.mem f) ∨
      (u.reg 18 = 1#64 ∧ stdioPend s.mem f < n ∧ u.reg 21 = s.reg 2 - 72#64 ∧
        read64 u.mem (s.reg 2 - 64#64) = len - BitVec.ofNat 64 (n - stdioPend s.mem f))) :
    PReachK img dom (SwQ f buf len s k) (u, k) := by
  have hpre' := hpre
  obtain ⟨ha0, ha1, ha2, hal, hale, hle, dFS, dES, dEF, -, -, -, -, -⟩ := hpre
  obtain ⟨hx, h2, h9, h8, hpr, s1, s2, s3, s4, s5, s6, s7, hfr⟩ := hc
  have hW := fun {a n} h => sw_canWrite (a := a) (n := n) hle h
  have alF := sw_alF hal
  have wF : ∀ o, o + 8 ≤ 128 → k.perm.canWrite (f + BitVec.ofNat 64 o) 8 := fun o ho => hW (.inl (sw_cF f o 8 ho))
  have w0 : k.perm.canWrite f 4 := by have := hW (.inl (sw_cF f 0 4 (by omega))); simpa using this
  have r0 : k.perm.canRead f 4 := Perm.canRead_of_canWrite w0
  nocompiler_pstep [hpc, h9, sw_al4 hal]
  refine ⟨r0, ?_⟩
  nocompiler_pstep
  nocompiler_pstep [h9, alF 32 rfl]
  refine ⟨wF 32 (by omega), ?_⟩
  nocompiler_pstep [h9, alF 56 rfl]
  refine ⟨wF 56 (by omega), ?_⟩
  nocompiler_pstep
  nocompiler_pstep [h9, sw_al4 hal]
  refine ⟨w0, ?_⟩
  nocompiler_pstep
  nocompiler_pstep [h9, alF 40 rfl]
  refine ⟨wF 40 (by omega), ?_⟩
  have d0 : ∀ q, 8 ≤ q → q ≤ 112 → (Region.mk f 4).Disjoint ⟨s.reg 2 - BitVec.ofNat 64 q, 8⟩ := by
    intro q h1 h2; have := sw_dFS dFS 0 4 q (by omega) (by omega) h1 h2; simpa using this
  have hS : ∀ o, 8 ≤ o → o ≤ 112 → ∀ v : Nat,
      read64 (writeLE (writeLE (writeLE (writeLE u.mem (f + 32#64) 0 8) (f + 56#64) 0 8) f v 4) (f + 40#64) 0 8)
        (s.reg 2 - BitVec.ofNat 64 o) = read64 u.mem (s.reg 2 - BitVec.ofNat 64 o) := by
    intro o h1 h2 v
    rw [Auto.read64_writeLE_of_disjoint (sw_dFS dFS 40 8 o (by omega) (by omega) h1 h2) _ _ _ _ (by simp [Region.covers]),
      Auto.read64_writeLE_of_disjoint (d0 o h1 h2) _ _ _ _ (by simp [Region.covers]),
      Auto.read64_writeLE_of_disjoint (sw_dFS dFS 56 8 o (by omega) (by omega) h1 h2) _ _ _ _ (by simp [Region.covers]),
      Auto.read64_writeLE_of_disjoint (sw_dFS dFS 32 8 o (by omega) (by omega) h1 h2) _ _ _ _ (by simp [Region.covers])]
  have dF0 : ∀ o, 4 ≤ o → o + 8 ≤ 128 → (Region.mk (f + BitVec.ofNat 64 o) 8).Disjoint ⟨f, 4⟩ := by
    intro o h1 h2; have := sw_dFF f o 8 0 4 (by omega) h2 (by omega) (by omega) (by omega); simpa using this
  have hflags : readLE u.mem f 4 = readLE s.mem f 4 := by
    apply readLE_congr; intro j hj
    have hj' := sw_outF dFS dEF j (by omega)
    exact hfr _ hj'.1 hj'.2
  have hpost : ∀ (r0 : Word), (r0 = if n ≤ stdioPend s.mem f then 0 else BitVec.ofNat 64 (n - stdioPend s.mem f)) →
      ∀ y : State × Kern, y.2 = k →
      y.1.mem = writeLE (writeLE (writeLE (writeLE u.mem (f + 32#64) 0 8) (f + 56#64) 0 8) f
          (BitVec.toNat (BitVec.signExtend 64 (BitVec.ofNat 32 (readLE u.mem f 4)) ||| 32#64)) 4) (f + 40#64) 0 8 →
      y.1.trace = u.trace → y.1.reg 10 = r0 → stdioWriteSpec.post (f, buf, len) (s, k) y := by
    intro r0 hr0 y hk hm ht ha
    refine ⟨hk, evs, by rw [ht]; exact htr, ?_, .inr ⟨n, hn, hev, by rw [ha, hr0], ?_, ?_, ?_, ?_⟩⟩
    · intro p hp1 hp2 hp3 hp4 hp5
      rw [hm, writeLE_of_not_mem (r := ⟨f + 40#64, 8⟩) (by simp [Region.covers]) (sw_notsub 32 16 40 8 (by omega) (by omega) (by omega) hp4),
        writeLE_of_not_mem (r := ⟨f, 4⟩) (by simp [Region.covers]) hp3,
        writeLE_of_not_mem (r := ⟨f + 56#64, 8⟩) (by simp [Region.covers]) hp5,
        writeLE_of_not_mem (r := ⟨f + 32#64, 8⟩) (by simp [Region.covers]) (sw_notsub 32 16 32 8 (by omega) (by omega) (by omega) hp4)]
      exact hfr p hp1 hp2
    · rw [hm, Auto.read64_writeLE_of_disjoint (sw_dFF f 40 8 32 8 (by omega) (by omega) (by omega) (by omega) (by omega)) _ _ _ _ (by simp [Region.covers]),
        Auto.read64_writeLE_of_disjoint (dF0 32 (by omega) (by omega)).symm _ _ _ _ (by simp [Region.covers]),
        Auto.read64_writeLE_of_disjoint (sw_dFF f 56 8 32 8 (by omega) (by omega) (by omega) (by omega) (by omega)) _ _ _ _ (by simp [Region.covers]),
        Auto.read64_writeLE_same']
      rfl
    · rw [hm, Auto.read64_writeLE_same']; rfl
    · rw [hm, Auto.read64_writeLE_of_disjoint (sw_dFF f 40 8 56 8 (by omega) (by omega) (by omega) (by omega) (by omega)) _ _ _ _ (by simp [Region.covers]),
        Auto.read64_writeLE_of_disjoint (dF0 56 (by omega) (by omega)).symm _ _ _ _ (by simp [Region.covers]),
        Auto.read64_writeLE_same']
      rfl
    · rw [hm, readLE_writeLE_disj (dF0 40 (by omega) (by omega)) _ _ _ _ (by simp [Region.covers]),
        readLE_writeLE_same _ _ _ (by omega), show (256 : Nat) ^ 4 = 2 ^ 32 from rfl, sext_or_32, hflags]
  have hpr' : ∀ q ∈ [(3 : Reg), 4, 22, 23, 24, 25, 26, 27], q ≠ 10 ∧ q ≠ 11 := by decide
  rcases hcnt with ⟨h18, hnp⟩ | ⟨h18, hnp, h21, hiov⟩
  · nocompiler_pstep [h18]
    refine sw_epi f buf len s k he hle _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp only [nocompiler_state]
    · simp only [nocompiler_state]; exact hx
    · simp (config := { decide := true }) only [nocompiler_state, h2]
    · intro q hq
      obtain ⟨q10, q11⟩ := hpr' q hq
      repeat (first | rw [State.setPc_reg] | rw [State.setMem_reg] | rw [State.reg_setReg_other _ _ _ _ q10] | rw [State.reg_setReg_other _ _ _ _ q11])
      exact hpr q hq
    · simp only [nocompiler_state]; rw [hS 8 (by omega) (by omega)]; exact s1
    · simp only [nocompiler_state]; rw [hS 16 (by omega) (by omega)]; exact s2
    · simp only [nocompiler_state]; rw [hS 24 (by omega) (by omega)]; exact s3
    · simp only [nocompiler_state]; rw [hS 32 (by omega) (by omega)]; exact s4
    · simp only [nocompiler_state]; rw [hS 40 (by omega) (by omega)]; exact s5
    · simp only [nocompiler_state]; rw [hS 48 (by omega) (by omega)]; exact s6
    · simp only [nocompiler_state]; rw [hS 56 (by omega) (by omega)]; exact s7
    intro y hk hm ht ha
    simp only [nocompiler_state] at hm ht ha
    exact hpost 0 (by simp [hnp]) y hk hm ht (by rw [ha]; rfl)
  · have hsp := he.sp
    simp only [Reg.sp] at hsp
    have e64 : s.reg 2 - 72#64 + 8#64 = s.reg 2 - 64#64 := by bv_omega
    have r64 : k.perm.canRead (s.reg 2 - 64#64) 8 :=
      Perm.canRead_of_canWrite (hW (.inr (.inl (sw_cS _ 64 8 (by omega) (by omega)))))
    nocompiler_pstep [h18]
    nocompiler_pstep [h21, e64, sw_alS hsp 64 rfl, hS 64 (by omega) (by omega), hiov]
    refine ⟨r64, ?_⟩
    nocompiler_pstep [h8]
    nocompiler_pstep
    refine sw_epi f buf len s k he hle _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp only [nocompiler_state]
    · simp only [nocompiler_state]; exact hx
    · simp (config := { decide := true }) only [nocompiler_state, h2]
    · intro q hq
      obtain ⟨q10, q11⟩ := hpr' q hq
      repeat (first | rw [State.setPc_reg] | rw [State.setMem_reg] | rw [State.reg_setReg_other _ _ _ _ q10] | rw [State.reg_setReg_other _ _ _ _ q11])
      exact hpr q hq
    · simp only [nocompiler_state]; rw [hS 8 (by omega) (by omega)]; exact s1
    · simp only [nocompiler_state]; rw [hS 16 (by omega) (by omega)]; exact s2
    · simp only [nocompiler_state]; rw [hS 24 (by omega) (by omega)]; exact s3
    · simp only [nocompiler_state]; rw [hS 32 (by omega) (by omega)]; exact s4
    · simp only [nocompiler_state]; rw [hS 40 (by omega) (by omega)]; exact s5
    · simp only [nocompiler_state]; rw [hS 48 (by omega) (by omega)]; exact s6
    · simp only [nocompiler_state]; rw [hS 56 (by omega) (by omega)]; exact s7
    intro y hk hm ht ha
    simp only [nocompiler_state] at hm ht ha
    exact hpost (len - (len - BitVec.ofNat 64 (n - stdioPend s.mem f)))
      (by simp only [show ¬ n ≤ stdioPend s.mem f by omega, ↓reduceIte]; exact sw_subsub _ _) y hk hm ht ha

/-- `__stdio_write`'s iovecs (at sp - 88, its frame + 8) after `d` of the bytes are written: two, the
    rest of the buffered bytes and `buf`, while `d` is within the buffered ones; else one, the rest of
    `buf`. `iovp` and `cnt` are the pointer and count the next `writev` gets. -/
def IovAt (s : State) (f buf len : Word) (m : Word → Byte) (iovp cnt : Word) (d : Nat) : Prop :=
  (d ≤ stdioPend s.mem f ∧ cnt = 2#64 ∧ iovp = s.reg 2 - 88#64 ∧
    read64 m (s.reg 2 - 88#64) = read64 s.mem (f + 56#64) + BitVec.ofNat 64 d ∧
    read64 m (s.reg 2 - 80#64) = BitVec.ofNat 64 (stdioPend s.mem f - d) ∧
    read64 m (s.reg 2 - 72#64) = buf ∧ read64 m (s.reg 2 - 64#64) = len) ∨
  (stdioPend s.mem f < d ∧ d ≤ stdioPend s.mem f + len.toNat ∧ cnt = 1#64 ∧ iovp = s.reg 2 - 72#64 ∧
    read64 m (s.reg 2 - 72#64) = buf + BitVec.ofNat 64 (d - stdioPend s.mem f) ∧
    read64 m (s.reg 2 - 64#64) = BitVec.ofNat 64 (stdioPend s.mem f + len.toNat - d))

theorem stdioBytes_length (m : Word → Byte) (f buf len : Word) :
    (stdioBytes m f buf len).length = stdioPend m f + len.toNat := by
  simp [stdioBytes, stdioPend, Auto.readBytes_length]

/-- Bytes in a region outside the stack and errno read the same in `m` as at entry. -/
theorem sw_readBytes_eq {s : State} {m : Word → Byte} {a : Word} {n : Nat}
    (hm : ∀ p, ¬ (Region.mk (s.reg 2 - 112#64) 112).mem p → ¬ (Region.mk (s.reg 4 + 18446744073709551452#64) 4).mem p →
      m p = s.mem p)
    (d1 : (Region.mk a n).Disjoint ⟨s.reg 2 - 112#64, 112⟩)
    (d2 : (Region.mk a n).Disjoint ⟨s.reg 4 + 18446744073709551452#64, 4⟩) (o r : Nat) (hor : o + r ≤ n) :
    readBytes m (a + BitVec.ofNat 64 o) r = readBytes s.mem (a + BitVec.ofNat 64 o) r := by
  apply readBytes_congr; intro j hj
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  apply hm
  · exact Auto.not_mem_of_disjoint d1.symm (by omega)
  · exact Auto.not_mem_of_disjoint d2.symm (by omega)


theorem stdioBytes_eq (m : Word → Byte) (f buf len : Word) :
    stdioBytes m f buf len = readBytes m (read64 m (f + 56#64)) (stdioPend m f) ++ readBytes m buf len.toNat := rfl

theorem drop_readBytes (m : Word → Byte) (a : Word) (d n : Nat) (h : d ≤ n) :
    (readBytes m a n).drop d = readBytes m (a + BitVec.ofNat 64 d) (n - d) := by
  have e := readBytes_add m a d (n - d)
  rw [show d + (n - d) = n by omega] at e
  rw [e, List.drop_left' (Auto.readBytes_length _ _ _)]

/-- What `writev` gathers from the iovecs is the unwritten suffix. -/
theorem sw_gather {s : State} {f buf len : Word} {m : Word → Byte} {iovp cnt : Word} {d : Nat}
    (hm : ∀ p, ¬ (Region.mk (s.reg 2 - 112#64) 112).mem p → ¬ (Region.mk (s.reg 4 + 18446744073709551452#64) 4).mem p →
      m p = s.mem p)
    (dP1 : (Region.mk (read64 s.mem (f + 56#64)) (stdioPend s.mem f)).Disjoint ⟨s.reg 2 - 112#64, 112⟩)
    (dB1 : (Region.mk buf len.toNat).Disjoint ⟨s.reg 2 - 112#64, 112⟩)
    (dP2 : (Region.mk (read64 s.mem (f + 56#64)) (stdioPend s.mem f)).Disjoint ⟨s.reg 4 + 18446744073709551452#64, 4⟩)
    (dB2 : (Region.mk buf len.toNat).Disjoint ⟨s.reg 4 + 18446744073709551452#64, 4⟩)
    (hB : stdioPend s.mem f + len.toNat < 2 ^ 63) (hiov : IovAt s f buf len m iovp cnt d) :
    gather m iovp cnt.toNat = (stdioBytes s.mem f buf len).drop d := by
  have hpl : (readBytes s.mem (read64 s.mem (f + 56#64)) (stdioPend s.mem f)).length = stdioPend s.mem f :=
    Auto.readBytes_length _ _ _
  rcases hiov with ⟨hd, rfl, rfl, h0, h1, h2, h3⟩ | ⟨hd, hd', rfl, rfl, h2, h3⟩
  · rw [show (2#64).toNat = 2 from rfl]
    simp only [gather, show List.range 2 = [0, 1] from rfl, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      iovBuf, Nat.mul_zero, Nat.mul_one, Nat.zero_add]
    rw [show s.reg 2 - 88#64 + BitVec.ofNat 64 0 = s.reg 2 - 88#64 by bv_omega,
      show s.reg 2 - 88#64 + BitVec.ofNat 64 8 = s.reg 2 - 80#64 by bv_omega,
      show s.reg 2 - 88#64 + BitVec.ofNat 64 16 = s.reg 2 - 72#64 by bv_omega,
      show s.reg 2 - 88#64 + BitVec.ofNat 64 (16 + 8) = s.reg 2 - 64#64 by bv_omega, h0, h1, h2, h3,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : stdioPend s.mem f - d < 2 ^ 64)]
    rw [sw_readBytes_eq hm dP1 dP2 d _ (by omega)]
    have hb0 := sw_readBytes_eq hm dB1 dB2 0 len.toNat (by omega)
    simp only [BitVec.add_zero] at hb0
    rw [hb0, stdioBytes_eq, List.drop_append_of_le_length (by rw [hpl]; exact hd),
      drop_readBytes _ _ _ _ hd]
  · rw [show (1#64).toNat = 1 from rfl]
    simp only [gather, show List.range 1 = [0] from rfl, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      iovBuf, Nat.mul_zero, Nat.zero_add]
    rw [show s.reg 2 - 72#64 + BitVec.ofNat 64 0 = s.reg 2 - 72#64 by bv_omega,
      show s.reg 2 - 72#64 + BitVec.ofNat 64 8 = s.reg 2 - 64#64 by bv_omega, h2, h3,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : stdioPend s.mem f + len.toNat - d < 2 ^ 64)]
    rw [sw_readBytes_eq hm dB1 dB2 (d - stdioPend s.mem f) _ (by omega)]
    rw [stdioBytes_eq, List.drop_append, List.drop_eq_nil_of_le (by rw [hpl]; omega), List.nil_append, hpl,
      drop_readBytes _ _ _ _ (by omega),
      show stdioPend s.mem f + len.toNat - d = len.toNat - (d - stdioPend s.mem f) by omega]

theorem sw_ecall_instr (E : Word) (hE : E = 0x124dc#64 ∨ E = 0x12558#64) : img.instr E = some .ecall := by
  rcases hE with rfl | rfl <;> simp only [nocompiler_image]

theorem sw_ecall_dom (E : Word) (hE : E = 0x124dc#64 ∨ E = 0x12558#64) :
    dom.mem E ∧ dom.mem (E + 4#64) ∧ dom.mem (E + 8#64) := by
  rcases hE with rfl | rfl <;> decide

theorem sw_slot_eq (sp : Word) (o j : Nat) (h1 : j < 8) (h2 : 8 ≤ o) (h3 : o ≤ 88) :
    sp - BitVec.ofNat 64 o + BitVec.ofNat 64 j = sp - 112#64 + BitVec.ofNat 64 (112 - o + j) := by
  bv_omega

theorem sw_slot_notret (sp : Word) (o j : Nat) (h1 : j < 8) (h2 : 8 ≤ o) (h3 : o ≤ 88) :
    ¬ (Region.mk (sp - 112#64) 16).mem (sp - BitVec.ofNat 64 o + BitVec.ofNat 64 j) := by
  rw [sw_slot_eq sp o j h1 h2 h3]; simp only [Region.mem]; bv_omega

/-- A byte of the frame at or above sp - 88 is outside `__syscall_ret`'s frame (16 bytes at sp - 112) and errno. -/
theorem sw_slot_out {s : State}
    (dES : (Region.mk (s.reg 4 + 18446744073709551452#64) 4).Disjoint ⟨s.reg 2 - 112#64, 112⟩)
    (o j : Nat) (h1 : j < 8) (h2 : 8 ≤ o) (h3 : o ≤ 88) :
    ¬ (Region.mk (s.reg 2 - 112#64) 16).mem (s.reg 2 - BitVec.ofNat 64 o + BitVec.ofNat 64 j) ∧
    ¬ (Region.mk (s.reg 4 + 18446744073709551452#64) 4).mem (s.reg 2 - BitVec.ofNat 64 o + BitVec.ofNat 64 j) := by
  refine ⟨sw_slot_notret _ o j h1 h2 h3, ?_⟩
  rw [sw_slot_eq _ o j h1 h2 h3]
  exact Auto.not_mem_of_disjoint dES (by omega)

theorem IovAt_congr {s : State} {f buf len : Word} {m m' : Word → Byte} {iovp cnt : Word} {d : Nat}
    (h : ∀ o, o ∈ [88, 80, 72, 64] → read64 m' (s.reg 2 - BitVec.ofNat 64 o) = read64 m (s.reg 2 - BitVec.ofNat 64 o))
    (hi : IovAt s f buf len m iovp cnt d) : IovAt s f buf len m' iovp cnt d := by
  have e88 := h 88 (by simp); have e80 := h 80 (by simp); have e72 := h 72 (by simp); have e64 := h 64 (by simp)
  rcases hi with ⟨a, b, c, h0, h1, h2, h3⟩ | ⟨a, a', b, c, h2, h3⟩
  · exact .inl ⟨a, b, c, by rw [e88]; exact h0, by rw [e80]; exact h1, by rw [e72]; exact h2, by rw [e64]; exact h3⟩
  · exact .inr ⟨a, a', b, c, by rw [e72]; exact h2, by rw [e64]; exact h3⟩

theorem sw_al96 {sp : Word} (h : aligned sp 16) : aligned (sp - 96#64) 16 := by unfold aligned at *; bv_omega

theorem sw_e112 (sp : Word) : sp - 96#64 - 16#64 = sp - 112#64 := by bv_omega

theorem sw_errDisj16 {s : State}
    (dES : (Region.mk (s.reg 4 + 18446744073709551452#64) 4).Disjoint ⟨s.reg 2 - 112#64, 112⟩) :
    (Region.mk (s.reg 4 + 18446744073709551452#64) 4).Disjoint ⟨s.reg 2 - 112#64, 16⟩ := by
  simp only [Region.Disjoint] at *; omega

theorem sw_not16 {sp p : Word} (h : ¬ (Region.mk (sp - 112#64) 112).mem p) : ¬ (Region.mk (sp - 112#64) 16).mem p := by
  simp only [Region.mem] at *; omega

theorem sw_err_big {e : Word} (h : e = einval ∨ e = ebadf ∨ ∃ n : Nat, 1 ≤ n ∧ n ≤ 4095 ∧ e = -(BitVec.ofNat 64 n)) :
    ¬ e.toNat < 2 ^ 64 - 4095 := by
  rcases h with rfl | rfl | ⟨n, h1, h2, rfl⟩
  · decide
  · decide
  · rw [BitVec.toNat_neg, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 2 ^ 64)]; omega

end NoCompiler.Libc.Musl.StdioWrite
