import Examples.Libc.Musl.StdoutWriteImg
import Examples.Libc.Musl.StdioWrite4

set_option maxRecDepth 20000
namespace NoCompiler.Libc.Musl.StdoutWrite
open NoCompiler NoCompiler.Linux NoCompiler.Libc NoCompiler.Libc.Musl NoCompiler.Libc.Musl.StdioWrite NoCompiler.Libc.Musl.StdoutWriteImg

def __stdio_write_dom : Dom := [(0x122c0#64, 60), (0x122fc#64, 12), (0x1247c#64, 352)]
def __stdout_write_dom : Dom := dom

/-! ## `__stdout_write` (musl src/stdio/__stdout_write.c)

```c
size_t __stdout_write(FILE *f, const unsigned char *buf, size_t len)
{
	struct winsize wsz;
	f->write = __stdio_write;
	if (!(f->flags & F_SVB) && __syscall(SYS_ioctl, f->fd, TIOCGWINSZ, &wsz))
		f->lbf = -1;
	return __stdio_write(f, buf, len);
}
```
FILE's fields as this build lays them out: `flags` at 0, `write` at 72, `fd` at 120, `lbf` at 144; `F_SVB` is 64.
The ioctl goes to the process level (`ProcStep7`, `procSpec7_ioctl`); the call of `__stdio_write` is at
0x12468, its return at 0x12470. Its theorem is over any specification `W` of `__stdio_write` whose
postcondition leaves the caller's 16 bytes above its stack pointer and the permission as they were. -/

/-- The memory at the call of `__stdio_write`, from the entry state `s`: the saved `ra` at `sp - 8`,
    `f->write = __stdio_write`, the 8 bytes of `wsz` at `sp - 16` if the ioctl wrote them, `f->lbf = -1`
    if `lbf`. -/
def stdoutMem (s : State) (f : Word) (wsz : Option (List Byte)) (lbf : Bool) : Word → Byte :=
  let m1 := writeLE (writeLE s.mem (s.reg Reg.sp - 8#64) (s.reg Reg.ra).toNat 8) (f + 72#64) 0x1247c 8
  let m2 := match wsz with
    | some ws => writeBytes m1 (s.reg Reg.sp - 16#64) ws
    | none => m1
  if lbf then writeLE m2 (f + 144#64) 18446744073709551615 4 else m2

/-- The state at `__stdout_write`'s call of `__stdio_write`, from its entry state `s`, for `f`, `buf`,
    `len`: the arguments passed on, the return address, a 16-byte frame, the registers outside
    ra, sp, a0..a5, a7 as at entry, the trace and the kernel unchanged, the memory `stdoutMem` with
    `wsz` and `lbf` as the img decides them (no ioctl if `F_SVB` is set; `lbf = -1` if the ioctl
    failed; `wsz` written if it succeeded). -/
def stdoutCall (f buf len : Word) (s z : State) : Prop :=
  z.pc = 0x1247c#64 ∧ z.exit = none ∧ z.trace = s.trace ∧
  z.reg Reg.a0 = f ∧ z.reg Reg.a1 = buf ∧ z.reg Reg.a2 = len ∧ z.reg Reg.ra = 0x12470#64 ∧
  z.reg Reg.sp = s.reg Reg.sp - 16#64 ∧ Same s z [1, 2, 10, 11, 12, 13, 14, 15, 17] ∧
  ∃ wsz lbf, z.mem = stdoutMem s f wsz lbf ∧
    (read8 s.mem f &&& 64#64 ≠ 0#64 → wsz = none ∧ lbf = false) ∧
    (read8 s.mem f &&& 64#64 = 0#64 →
      (wsz = none ∧ lbf = true) ∨ ∃ ws : List Byte, ws.length = 8 ∧ wsz = some ws ∧ lbf = false)

/-- `__stdout_write(f, buf, len)`, given `W`, a specification of `__stdio_write`: what `W` promises
    from the call state. It reads `f->flags`' low byte and `f->fd`, writes `f->write` and `f->lbf`
    (8-byte aligned `f`; FILE's first 152 bytes outside its frame) and its 16-byte frame. -/
def stdoutWriteSpec (W : SpecP (Word × Word × Word)) : SpecP (Word × Word × Word) where
  pre := fun ⟨f, buf, len⟩ s k =>
    s.reg Reg.a0 = f ∧ s.reg Reg.a1 = buf ∧ s.reg Reg.a2 = len ∧ aligned f 8 ∧
    k.perm.canRead f 1 ∧ k.perm.canWrite (f + 72#64) 8 ∧ k.perm.canRead (f + 120#64) 4 ∧
    k.perm.canWrite (f + 144#64) 4 ∧ k.perm.canWrite (s.reg Reg.sp - 8#64) 8 ∧
    k.perm.canRead (s.reg Reg.sp - 8#64) 8 ∧
    (Region.mk f 152).Disjoint (Spec.stackRegion s 16) ∧
    ∀ z, stdoutCall f buf len s z → W.pre (f, buf, len) z k
  post := fun ⟨f, buf, len⟩ x y => ∃ z w, stdoutCall f buf len x.1 z ∧ W.post (f, buf, len) (z, x.2) w ∧
    y.1.mem = w.1.mem ∧ y.1.trace = w.1.trace ∧ y.1.reg Reg.a0 = w.1.reg Reg.a0 ∧ y.2 = w.2
  onExit := fun ⟨f, buf, len⟩ x y => ∃ z, stdoutCall f buf len x.1 z ∧ W.onExit (f, buf, len) (z, x.2) y


theorem stdoutMem_ra {s : State} {f : Word} {wsz : Option (List Byte)} {lbf : Bool}
    (hdisj : (Region.mk f 152).Disjoint ⟨s.reg 2 - 16#64, 16⟩) (hws : ∀ ws, wsz = some ws → ws.length = 8) :
    read64 (stdoutMem s f wsz lbf) (s.reg 2 - 8#64) = s.reg 1 := by
  have d72 : (Region.mk (f + 72#64) 8).Disjoint ⟨s.reg 2 - 8#64, 8⟩ := by
    unfold Region.Disjoint at *; simp only at *; bv_omega
  have d144 : (Region.mk (f + 144#64) 4).Disjoint ⟨s.reg 2 - 8#64, 8⟩ := by
    unfold Region.Disjoint at *; simp only at *; bv_omega
  have hm2 : ∀ m, read64 (match wsz with | some ws => writeBytes m (s.reg 2 - 16#64) ws | none => m)
      (s.reg 2 - 8#64) = read64 m (s.reg 2 - 8#64) := by
    intro m
    cases hw : wsz with
    | none => rfl
    | some ws =>
      have hl := hws ws hw
      unfold read64
      rw [readLE_writeBytes_above (fun j hj => by rw [hl]; bv_omega)]
  unfold stdoutMem
  simp only
  split
  · rw [Auto.read64_writeLE_of_disjoint d144 _ _ _ _ (by simp [Region.covers])]
    rw [hm2, Auto.read64_writeLE_of_disjoint d72 _ _ _ _ (by simp [Region.covers]), Auto.read64_writeLE_same']
    simp
  · rw [hm2, Auto.read64_writeLE_of_disjoint d72 _ _ _ _ (by simp [Region.covers]), Auto.read64_writeLE_same']
    simp

theorem preserved_not_call : ∀ r ∈ preservedRegs, r ≠ 2 →
    r.val ∉ [1, 2, 10, 11, 12, 13, 14, 15, 17] ∧ r ≠ 1 := by decide

/-- From the call of `__stdio_write` on: the call by `W`, then `ld ra; addi sp; ret`. -/
theorem stdout_call (W : SpecP (Word × Word × Word)) (hWv : VerifiedProc img __stdio_write_dom 0x1247c#64 W)
    (hWf : StdioWriteFrame W) (f buf len : Word) (s : State) (k : Kern)
    (he : Entry __stdout_write_dom __stdout_write_entry s)
    (hdisj : (Region.mk f 152).Disjoint ⟨s.reg 2 - 16#64, 16⟩) (hrsp : k.perm.canRead (s.reg 2 - 8#64) 8)
    (hW : ∀ (z : State), stdoutCall f buf len s z → W.pre (f, buf, len) z k)
    (z : State) (hcall : stdoutCall f buf len s z) :
    PReachK img __stdout_write_dom (fun y => Final __stdout_write_dom y.1 ∧
      (stdoutWriteSpec W).Done (f, buf, len) (s, k) y) (z, k) := by
  obtain ⟨hzpc, hzx, hztr, hz10, hz11, hz12, hz1, hz2, hzs, wsz, lbf, hzm, hc1, hc2⟩ := hcall
  have hws : ∀ ws, wsz = some ws → ws.length = 8 := by
    intro ws hw
    by_cases hf : read8 s.mem f &&& 64#64 = 0#64
    · rcases hc2 hf with ⟨h, _⟩ | ⟨ws', hl, h, _⟩
      · rw [h] at hw; cases hw
      · rw [h] at hw; cases hw; exact hl
    · rw [(hc1 hf).1] at hw; cases hw
  have hcall : stdoutCall f buf len s z :=
    ⟨hzpc, hzx, hztr, hz10, hz11, hz12, hz1, hz2, hzs, wsz, lbf, hzm, hc1, hc2⟩
  have hsp := he.sp
  have hra4 := he.retAligned
  have hret := he.ret
  simp only [Reg.sp, Reg.ra] at hsp hra4 hret hz1 hz2
  have hent : Entry __stdio_write_dom 0x1247c#64 z :=
    ⟨hzpc, hzx, by rw [Reg.ra, hz1]; decide, by rw [Reg.ra, hz1]; decide,
      by rw [Reg.sp, hz2]; unfold aligned at *; bv_omega⟩
  refine VerifiedProc.call hWv (f, buf, len) hent (hW z hcall) (Dom.sub_of_ranges (by decide)) ?_
  rintro ⟨w, kw⟩ (⟨hwx, hwpc, hpres, hpost⟩ | ⟨hwx, hex⟩)
  · obtain ⟨hfr, hperm⟩ := hWf _ _ _ hpost
    simp only at hwx hwpc hfr hperm
    rw [Reg.ra, hz1] at hwpc
    have hw2 : w.reg 2 = s.reg 2 - 16#64 := by rw [hpres 2 (by decide), hz2]
    have e8 : s.reg 2 - 16#64 + 8#64 = s.reg 2 - 8#64 := by bv_omega
    have e16 : s.reg 2 - 16#64 + 16#64 = s.reg 2 := by bv_omega
    have al8 : aligned (s.reg 2 - 8#64) 8 := by unfold aligned at *; bv_omega
    have hra : read64 w.mem (s.reg 2 - 8#64) = s.reg 1 := by
      have h := stdoutMem_ra (lbf := lbf) hdisj hws
      rw [← hzm] at h
      rw [← h]
      unfold read64
      rw [readLE_congr (m' := z.mem) (fun j hj => hfr _ (by simp only [Region.mem, Reg.sp, hz2]; bv_omega))]
    have hrd : kw.perm.canRead (s.reg 2 - 8#64) 8 := by rw [hperm]; exact hrsp
    nocompiler_prun_n 3 [hwpc, hw2, e8, al8, hra, e16, ret_mask hra4, hra4] using [hrd]
    refine .done ⟨.inl ?_, .inl ⟨?_, ?_, ?_, ?_⟩⟩
    · simp only [nocompiler_state]; exact hret
    · simp only [nocompiler_state]; exact hwx
    · simp only [nocompiler_state, Reg.ra]
    · intro r hr
      by_cases h2 : r = 2
      · subst h2; simp (config := { decide := true }) only [nocompiler_state]
      · obtain ⟨hn, h1⟩ := preserved_not_call r hr h2
        simp only [State.setPc_reg, State.reg_setReg_other _ _ _ _ h1, State.reg_setReg_other _ _ _ _ h2]
        rw [hpres r hr, hzs r hn]
    · exact ⟨z, (w, kw), hcall, hpost, by simp only [nocompiler_state], by simp only [nocompiler_state],
        by simp (config := { decide := true }) only [nocompiler_state, Reg.a0], rfl⟩
  · exact .done ⟨.inr hwx, .inr ⟨hwx, z, hcall, hex⟩⟩

theorem stdout_tail (W : SpecP (Word × Word × Word)) (hWv : VerifiedProc img __stdio_write_dom 0x1247c#64 W)
    (hWf : StdioWriteFrame W) (f buf len : Word) (s : State) (k : Kern)
    (he : Entry __stdout_write_dom __stdout_write_entry s)
    (hdisj : (Region.mk f 152).Disjoint ⟨s.reg 2 - 16#64, 16⟩) (hrsp : k.perm.canRead (s.reg 2 - 8#64) 8)
    (hW : ∀ (z : State), stdoutCall f buf len s z → W.pre (f, buf, len) z k)
    (u : State) (wsz : Option (List Byte)) (lbf : Bool) (hpc : u.pc = 0x1245c#64) (hx : u.exit = none)
    (htr : u.trace = s.trace) (h13 : u.reg 13 = f) (h15 : u.reg 15 = buf) (h14 : u.reg 14 = len)
    (h2 : u.reg 2 = s.reg 2 - 16#64) (hsame : Same s u [1, 2, 10, 11, 12, 13, 14, 15, 17])
    (hmem : u.mem = stdoutMem s f wsz lbf)
    (hc1 : read8 s.mem f &&& 64#64 ≠ 0#64 → wsz = none ∧ lbf = false)
    (hc2 : read8 s.mem f &&& 64#64 = 0#64 →
      (wsz = none ∧ lbf = true) ∨ ∃ ws : List Byte, ws.length = 8 ∧ wsz = some ws ∧ lbf = false) :
    PReachK img __stdout_write_dom (fun y => Final __stdout_write_dom y.1 ∧
      (stdoutWriteSpec W).Done (f, buf, len) (s, k) y) (u, k) := by
  have hws : ∀ ws, wsz = some ws → ws.length = 8 := by
    intro ws hw
    by_cases hf : read8 s.mem f &&& 64#64 = 0#64
    · rcases hc2 hf with ⟨h, _⟩ | ⟨ws', hl, h, _⟩
      · rw [h] at hw; cases hw
      · rw [h] at hw; cases hw; exact hl
    · rw [(hc1 hf).1] at hw; cases hw
  nocompiler_prun_n 5 [hpc] using []
  refine stdout_call W hWv hWf f buf len s k he hdisj hrsp hW _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, wsz, lbf, ?_, hc1, hc2⟩
  all_goals (try simp (config := { decide := true }) only [nocompiler_state, hx, htr, h13, h15, h14, h2, hmem,
    Reg.a0, Reg.a1, Reg.a2, Reg.ra, Reg.sp])
  nocompiler_same

/-- The memory before the ioctl: the saved `ra`, `f->write`. -/
theorem stdoutMem_none (s : State) (f : Word) :
    stdoutMem s f none false = writeLE (writeLE s.mem (s.reg 2 - 8#64) (s.reg 1).toNat 8) (f + 72#64) 74876 8 :=
  rfl

/-- From the `ecall` (ioctl TIOCGWINSZ, `F_SVB` clear) on. -/
theorem stdout_ioctl (W : SpecP (Word × Word × Word)) (hWv : VerifiedProc img __stdio_write_dom 0x1247c#64 W)
    (hWf : StdioWriteFrame W) (f buf len : Word) (s : State) (k : Kern)
    (he : Entry __stdout_write_dom __stdout_write_entry s)
    (hdisj : (Region.mk f 152).Disjoint ⟨s.reg 2 - 16#64, 16⟩) (hrsp : k.perm.canRead (s.reg 2 - 8#64) 8)
    (hw144 : k.perm.canWrite (f + 144#64) 4) (al144 : aligned (f + 144#64) 4)
    (hW : ∀ (z : State), stdoutCall f buf len s z → W.pre (f, buf, len) z k)
    (hf : read8 s.mem f &&& 64#64 = 0#64)
    (v : State) (hpc : v.pc = 0x1244c#64) (hx : v.exit = none)
    (htr : v.trace = s.trace) (h13 : v.reg 13 = f) (h15 : v.reg 15 = buf) (h14 : v.reg 14 = len)
    (h2 : v.reg 2 = s.reg 2 - 16#64) (h17 : v.reg 17 = 29#64) (h11 : v.reg 11 = 0x5413#64)
    (h12 : v.reg 12 = s.reg 2 - 16#64) (hsame : Same s v [1, 2, 10, 11, 12, 13, 14, 15, 17])
    (hmem : v.mem = stdoutMem s f none false) :
    PReachK img __stdout_write_dom (fun y => Final __stdout_write_dom y.1 ∧
      (stdoutWriteSpec W).Done (f, buf, len) (s, k) y) (v, k) := by
  have h7 : v.reg Reg.a7 = sysIoctl := h17
  have h1 : v.reg Reg.a1 = tiocgwinsz := h11
  refine PReachK.ecall (by rw [hpc]; decide) hx (by rw [hpc]; simp only [nocompiler_image])
    (by simp only [SysOk, h7]; exact ⟨fun h => absurd h (by decide), fun h => absurd h (by decide)⟩)
    (ioctl_progress _ _ h7 h1) ?_
  intro y hy0
  obtain ⟨hk, hy⟩ := ioctl_cases h7 h1 hy0
  clear hy0
  obtain ⟨y, ky⟩ := y
  simp only at hk hy
  rw [hk]
  have hmem' := hmem
  rw [stdoutMem_none] at hmem'
  rcases hy with rfl | rfl | ⟨ws, hws, rfl⟩
  · nocompiler_pstep [hpc, enotty]
    nocompiler_pstep
    nocompiler_pstep [h13, hmem', al144]
    refine ⟨by simpa [nocompiler_state, h13] using hw144, ?_⟩
    refine stdout_tail W hWv hWf f buf len s k he hdisj hrsp hW _ none true ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      (fun h => absurd hf h) (fun _ => .inl ⟨rfl, rfl⟩)
    all_goals (try simp (config := { decide := true }) only [nocompiler_state, hx, htr, h13, h15, h14, h2,
      stdoutMem, Reg.sp, Reg.ra, ↓reduceIte])
    nocompiler_same
  · nocompiler_pstep [hpc, ebadf]
    nocompiler_pstep
    nocompiler_pstep [h13, hmem', al144]
    refine ⟨by simpa [nocompiler_state, h13] using hw144, ?_⟩
    refine stdout_tail W hWv hWf f buf len s k he hdisj hrsp hW _ none true ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      (fun h => absurd hf h) (fun _ => .inl ⟨rfl, rfl⟩)
    all_goals (try simp (config := { decide := true }) only [nocompiler_state, hx, htr, h13, h15, h14, h2,
      stdoutMem, Reg.sp, Reg.ra, ↓reduceIte])
    nocompiler_same
  · nocompiler_pstep [hpc]
    refine stdout_tail W hWv hWf f buf len s k he hdisj hrsp hW _ (some ws) false ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      (fun h => absurd hf h) (fun _ => .inr ⟨ws, hws, rfl, rfl⟩)
    all_goals (try simp (config := { decide := true }) only [nocompiler_state, hx, htr, h13, h15, h14, h2, h12,
      hmem', stdoutMem, Reg.sp, Reg.ra, Reg.a2, ↓reduceIte])
    nocompiler_same

/-- `__stdout_write` as compiled, for any specification `W` of `__stdio_write` that keeps its caller's
    frame: it sets `f->write`, asks the kernel for the window size unless `F_SVB` is set, sets `f->lbf = -1`
    if that failed, and then is what `W` says from there; safe, at the process level. -/
theorem __stdout_write_verified (W : SpecP (Word × Word × Word))
    (hWv : VerifiedProc img __stdio_write_dom 0x1247c#64 W) (hWf : StdioWriteFrame W) :
    VerifiedProc img __stdout_write_dom __stdout_write_entry (stdoutWriteSpec W) := by
  rintro ⟨f, buf, len⟩ s k he hpre
  obtain ⟨ha0, ha1, ha2, hal, hrf, hw72, hr120, hw144, hwsp, hrsp, hdisj, hW⟩ := hpre
  have hpc := he.pc
  have hx := he.live
  have hsp16 := he.sp
  simp only [__stdout_write_entry] at hpc
  simp only [Reg.sp, Reg.a0, Reg.a1, Reg.a2] at ha0 ha1 ha2 hwsp hrsp hsp16
  have hdisj' : (Region.mk f 152).Disjoint ⟨s.reg 2 - 16#64, 16⟩ := by
    simpa [Spec.stackRegion] using hdisj
  have e16 : s.reg 2 + 18446744073709551600#64 = s.reg 2 - 16#64 := by bv_omega
  have e8 : s.reg 2 - 16#64 + 8#64 = s.reg 2 - 8#64 := by bv_omega
  have al8 : aligned (s.reg 2 - 8#64) 8 := by unfold aligned at *; bv_omega
  have al72 : aligned (f + 72#64) 8 := by unfold aligned at *; bv_omega
  have al120 : aligned (f + 120#64) 4 := by unfold aligned at *; bv_omega
  have al144 : aligned (f + 144#64) 4 := by unfold aligned at *; bv_omega
  have d1 : (Region.mk (s.reg 2 - 8#64) 8).Disjoint ⟨f, 1⟩ := by
    unfold Region.Disjoint at *; simp only at *; bv_omega
  have hflag : read8 (writeLE s.mem (s.reg 2 - 8#64) (BitVec.toNat (s.reg 1)) 8) f = read8 s.mem f := by
    unfold read8; rw [readLE_writeLE_disj d1 _ _ _ _ (by simp [Region.covers])]
  nocompiler_prun_n 11 [hpc, e8, e16, al8, ha0, Auto.aligned_one, al72, hflag] using [hwsp, hrf, hw72, hr120]
  by_cases hf : read8 s.mem f &&& 64#64 = 0#64
  · simp only [hf]
    try simp (config := { decide := true }) only [↓reduceIte, PReachK.opt_some]
    nocompiler_prun_n 5 [al120] using [hwsp, hrf, hw72, hr120]
    refine stdout_ioctl W hWv hWf f buf len s k he hdisj' hrsp hw144 al144 hW hf _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals (try simp (config := { decide := true }) only [nocompiler_state, hx, ha1, ha2, stdoutMem_none])
    all_goals nocompiler_same
  · simp only [bne_iff_ne, ne_eq]
    split
    case isFalse h => exact (h hf).elim
    rw [PReachK.opt_some]
    refine stdout_tail W hWv hWf f buf len s k he hdisj' hrsp hW _ none false ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      (fun _ => ⟨rfl, rfl⟩) (fun h => absurd h hf)
    all_goals (try simp (config := { decide := true }) only [nocompiler_state, hx, ha1, ha2, stdoutMem_none])
    all_goals nocompiler_same

end NoCompiler.Libc.Musl.StdoutWrite
