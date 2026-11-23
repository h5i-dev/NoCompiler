import NoCompiler.Linux.ProcSpec
import NoCompiler.Linux.SysSteps
import NoCompiler.Auto
import Examples.Libc.SlenImage
import Examples.Libc.Slen
import NoCompiler.Linux.RunN

/-!
# The functions on slen's path that make a syscall the trusted `Sys` does not have

Over the process step (`VerifiedProc`, Linux/ProcSpec.lean), by hand (`nocompiler_pstep`): they were written
before `nocompiler_auto_p` (the tactic over `PStep`, Linux/AutoP.lean; Examples/Linux/StdoutAuto.lean proves
`__stdout_write` with it). Each is stated over the specification of the function it calls, taken as a parameter
(as `_start_c_verified` in Examples/Libc/Slen.lean).
-/

namespace Examples.Libc.Slen
open NoCompiler NoCompiler.Linux

end Examples.Libc.Slen

set_option maxRecDepth 20000
namespace Examples.Libc.Slen
open NoCompiler NoCompiler.Linux Examples.Libc.SlenImage

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
    `wsz` and `lbf` as the code decides them (no ioctl if `F_SVB` is set; `lbf = -1` if the ioctl
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

/-- What `__stdout_write` needs of `__stdio_write`'s specification: on return, the caller's 16 bytes
    above its stack pointer and the permission are as they were. -/
def StdioWriteFrame (W : SpecP (Word × Word × Word)) : Prop :=
  ∀ a z w, W.post a z w → (∀ p, (Region.mk (z.1.reg Reg.sp) 16).mem p → w.1.mem p = z.1.mem p) ∧
    w.2.perm = z.2.perm

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
theorem stdout_call (W : SpecP (Word × Word × Word)) (hWv : VerifiedProc code __stdio_write_dom 0x1247c#64 W)
    (hWf : StdioWriteFrame W) (f buf len : Word) (s : State) (k : Kern)
    (he : Entry __stdout_write_dom __stdout_write_entry s)
    (hdisj : (Region.mk f 152).Disjoint ⟨s.reg 2 - 16#64, 16⟩) (hrsp : k.perm.canRead (s.reg 2 - 8#64) 8)
    (hW : ∀ (z : State), stdoutCall f buf len s z → W.pre (f, buf, len) z k)
    (z : State) (hcall : stdoutCall f buf len s z) :
    PReachK code __stdout_write_dom (fun y => Final __stdout_write_dom y.1 ∧
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

theorem stdout_tail (W : SpecP (Word × Word × Word)) (hWv : VerifiedProc code __stdio_write_dom 0x1247c#64 W)
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
    PReachK code __stdout_write_dom (fun y => Final __stdout_write_dom y.1 ∧
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
theorem stdout_ioctl (W : SpecP (Word × Word × Word)) (hWv : VerifiedProc code __stdio_write_dom 0x1247c#64 W)
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
    PReachK code __stdout_write_dom (fun y => Final __stdout_write_dom y.1 ∧
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
    (hWv : VerifiedProc code __stdio_write_dom 0x1247c#64 W) (hWf : StdioWriteFrame W) :
    VerifiedProc code __stdout_write_dom __stdout_write_entry (stdoutWriteSpec W) := by
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

/-- `_Exit(c)` from any state at its entry, whatever its return address (it does not return): the
    process ends with status `c`, the event `exit c` last, the kernel unchanged. `exit` calls it with
    `ra = 0x11ad8`, its own entry (the compiler put it right after the call), so `Entry` does not hold
    there and `_Exit_verified` does not apply. -/
theorem _Exit_proc (s : State) (k : Kern) (hpc : s.pc = 0x11ad8#64) (hx : s.exit = none) :
    PReachK code _Exit_dom (fun y => y.1.exit = some (s.reg 10) ∧
      y.1.trace = s.trace ++ [.exit (s.reg 10)] ∧ y.2 = k) (s, k) := by
  nocompiler_prun_n 2 [hpc] using []
  refine PReachK.ecall (by nocompiler_norm <;> decide) (by nocompiler_norm <;> exact hx)
    (by nocompiler_norm <;> simp only [nocompiler_image])
    (by simp only [SysOk]; nocompiler_norm <;>
      exact ⟨fun h => absurd h (by decide), fun h => absurd h (by decide)⟩)
    (exitGroup_progress _ _ (by nocompiler_norm <;> decide)) ?_
  intro y hy
  rw [exitGroup_cases (by nocompiler_norm <;> decide) hy]
  exact .done ⟨by nocompiler_norm, by nocompiler_norm, rfl⟩


/-! ## `exit` (musl src/exit/exit.c)

```c
_Noreturn void exit(int code)
{
	__funcs_on_exit();
	__libc_exit_fini();
	__stdio_exit();
	_Exit(code);
}
```
At the process level: `__stdio_exit` flushes the FILEs through their `write`, which reaches `writev`.
Stated over specifications `F` of `__libc_exit_fini` and `X` of `__stdio_exit`; `__funcs_on_exit`
(`__funcs_on_exit_verified`, an empty function) and `_Exit` (`_Exit_proc`) are proved. -/

/-- The state at `exit`'s call of `__libc_exit_fini` (0x11a54, returning to 0x11ac4), from its entry state
    `s` with status `c`: its frame (ra at sp - 8, s0 at sp - 16), s0 = c, the other callee-saved registers
    as at entry, the memory as its prologue left it (`__funcs_on_exit` writes nothing). -/
def exitCall1 (c : Word) (s z : State) : Prop :=
  z.pc = 0x11a54#64 ∧ z.exit = none ∧ z.reg 1 = 0x11ac4#64 ∧ z.reg 2 = s.reg 2 - 16#64 ∧ z.reg 8 = c ∧
  (∀ r ∈ preservedRegs, r ≠ 2 → r ≠ 8 → z.reg r = s.reg r) ∧
  z.mem = writeLE (writeLE s.mem (s.reg 2 - 8#64) (s.reg 1).toNat 8) (s.reg 2 - 16#64) (s.reg 8).toNat 8 ∧
  z.trace = s.trace

/-- A call from `w` into `e` returning to `r`: `ra` set, nothing else changed. -/
def callFrom (w z : State) (e r : Word) : Prop :=
  z.pc = e ∧ z.reg 1 = r ∧ Same w z [1] ∧ z.mem = w.mem ∧ z.trace = w.trace ∧ z.exit = w.exit

/-- `exit(c)`, given `F` (`__libc_exit_fini`) and `X` (`__stdio_exit`): it does not return; the process
    ends where `F` or `X` end it, or with status `c` and the event `exit c` after what `X` did, the
    kernel as `X` left it. -/
def exitProcSpec (F X : SpecP Unit) : SpecP Word where
  pre := fun c s k => s.reg Reg.a0 = c ∧ k.perm.canWrite (s.reg Reg.sp - 8#64) 8 ∧
    k.perm.canWrite (s.reg Reg.sp - 16#64) 8 ∧
    (∀ z k', exitCall1 c s z → k'.perm = k.perm → F.pre () z k') ∧
    (∀ z1 k1 w1 z2, exitCall1 c s z1 → k1.perm = k.perm → F.post () (z1, k1) w1 →
      Preserved z1 w1.1 → callFrom w1.1 z2 0x11e24#64 0x11acc#64 → X.pre () z2 w1.2)
  post := fun _ _ _ => False
  onExit := fun c x y => ∃ z1 k1, exitCall1 c x.1 z1 ∧ k1.perm = x.2.perm ∧
    (F.onExit () (z1, k1) y ∨ ∃ w1 z2, F.post () (z1, k1) w1 ∧ callFrom w1.1 z2 0x11e24#64 0x11acc#64 ∧
      (X.onExit () (z2, w1.2) y ∨ ∃ w2, X.post () (z2, w1.2) w2 ∧
        y.1.trace = w2.1.trace ++ [.exit c] ∧ y.1.exit = some c ∧ y.2 = w2.2))

/-- A specification with no regions allows nothing: below any permission. -/
theorem perm_le_of_empty {α : Type} {sp : Spec α} {a : α} {s : State} (hr : sp.reads a s = [])
    (hw : sp.writes a s = []) (hs : sp.stack = 0) (P : Perm) : (sp.perm a s).le P := by
  have h0 : ∀ a' n, (∃ r ∈ (sp.perm a s).rd ++ (sp.perm a s).wr, r.covers a' n) → n = 0 := by
    intro a' n ⟨r, hr', hc⟩
    simp only [Spec.perm, hr, hw, hs, List.nil_append, List.mem_singleton] at hr'
    subst hr'
    unfold Region.covers Spec.stackRegion at hc; simp only at hc; omega
  refine ⟨fun a' n h => ?_, fun a' n h => ?_⟩
  · rcases h with h | h
    · exact .inl h
    · exact .inl (h0 a' n h)
  · rcases h with h | ⟨r, hr', hc⟩
    · exact .inl h
    · exact .inl (h0 a' n ⟨r, List.mem_append.2 (.inr hr'), hc⟩)

theorem retSpec_le (s : State) (P : Perm) : (retSpec.perm () s).le P :=
  perm_le_of_empty rfl rfl rfl P

theorem retSpec_nowrite (s : State) (x : Word) : ¬ (retSpec.perm () s).writable x := by
  rintro ⟨r, hr, hm⟩
  simp only [Spec.perm, retSpec, List.nil_append, List.mem_singleton] at hr
  subst hr
  unfold Region.mem Spec.stackRegion at hm; simp at hm

abbrev ExitQ (F X : SpecP Unit) (c : Word) (s : State) (k : Kern) : State × Kern → Prop :=
  fun y => Final exit_dom y.1 ∧ (exitProcSpec F X).Done c (s, k) y

theorem exit_stage3 (F X : SpecP Unit) (c : Word) (s : State) (k : Kern) (z1 : State) (k1 : Kern)
    (w1 : State × Kern) (z2 : State) (h1 : exitCall1 c s z1) (hk1 : k1.perm = k.perm)
    (hF : F.post () (z1, k1) w1) (hc2 : callFrom w1.1 z2 0x11e24#64 0x11acc#64)
    (w2 : State × Kern) (hX : X.post () (z2, w1.2) w2) (hpc : w2.1.pc = 0x11acc#64)
    (hx : w2.1.exit = none) (h8 : w2.1.reg 8 = c) : PReachK code exit_dom (ExitQ F X c s k) w2 := by
  obtain ⟨w, kw⟩ := w2
  simp only at hpc hx h8 hX
  nocompiler_prun_n 3 [hpc] using []
  refine PReachK.bind (Dom.sub_of_ranges (by decide)) ?_
    (_Exit_proc _ kw (by nocompiler_norm) (by nocompiler_norm; exact hx))
  rintro ⟨y, ky⟩ ⟨hye, hyt, hyk⟩
  simp only at hye hyt hyk
  refine .done ⟨.inr (by simp [hye]), .inr ⟨by simp [hye], z1, k1, h1, hk1,
    .inr ⟨w1, z2, hF, hc2, .inr ⟨(w, kw), hX, ?_, ?_, hyk⟩⟩⟩⟩
  · rw [hyt]; nocompiler_norm [h8]
  · rw [hye]; nocompiler_norm [h8]

theorem exit_stage2b (F X : SpecP Unit) (hXv : VerifiedProc code __stdio_exit_dom 0x11e24#64 X)
    (c : Word) (s : State) (k : Kern) (hsp : aligned (s.reg 2) 16)
    (hXpre : ∀ z1 k1 w1 z2, exitCall1 c s z1 → k1.perm = k.perm → F.post () (z1, k1) w1 →
      Preserved z1 w1.1 → callFrom w1.1 z2 0x11e24#64 0x11acc#64 → X.pre () z2 w1.2)
    (z1 : State) (k1 : Kern) (w1 : State × Kern) (h1 : exitCall1 c s z1) (hk1 : k1.perm = k.perm)
    (hF : F.post () (z1, k1) w1) (hx : w1.1.exit = none) (hpres : Preserved z1 w1.1)
    (z2 : State) (hc2 : callFrom w1.1 z2 0x11e24#64 0x11acc#64) :
    PReachK code exit_dom (ExitQ F X c s k) (z2, w1.2) := by
  obtain ⟨hzpc, hzra, hzs, hzm, hztr, hzx⟩ := hc2
  have hc2 : callFrom w1.1 z2 0x11e24#64 0x11acc#64 := ⟨hzpc, hzra, hzs, hzm, hztr, hzx⟩
  have h2 : z2.reg 2 = s.reg 2 - 16#64 := by
    rw [hzs 2 (by decide), hpres 2 (by decide), h1.2.2.2.1]
  have h8 : z2.reg 8 = c := by
    rw [hzs 8 (by decide), hpres 8 (by decide), h1.2.2.2.2.1]
  have hent : Entry __stdio_exit_dom 0x11e24#64 z2 :=
    ⟨hzpc, by rw [hzx]; exact hx, by rw [Reg.ra, hzra]; decide, by rw [Reg.ra, hzra]; decide,
      by rw [Reg.sp, h2]; unfold aligned at *; bv_omega⟩
  refine VerifiedProc.call hXv () hent (hXpre z1 k1 w1 z2 h1 hk1 hF hpres hc2) (Dom.sub_of_ranges (by decide)) ?_
  rintro w2 (⟨hx2, hpc2, hpres2, hpost2⟩ | ⟨hx2, hex2⟩)
  · exact exit_stage3 F X c s k z1 k1 w1 z2 h1 hk1 hF hc2 w2 hpost2 (by rw [hpc2, Reg.ra, hzra]) hx2
      (by rw [hpres2 8 (by decide), h8])
  · exact .done ⟨.inr hx2, .inr ⟨hx2, z1, k1, h1, hk1, .inr ⟨w1, z2, hF, hc2, .inl hex2⟩⟩⟩

theorem exit_stage1b (F X : SpecP Unit) (hFv : VerifiedProc code __libc_exit_fini_dom 0x11a54#64 F)
    (hXv : VerifiedProc code __stdio_exit_dom 0x11e24#64 X)
    (c : Word) (s : State) (k : Kern) (hsp : aligned (s.reg 2) 16)
    (hFpre : ∀ z k', exitCall1 c s z → k'.perm = k.perm → F.pre () z k')
    (hXpre : ∀ z1 k1 w1 z2, exitCall1 c s z1 → k1.perm = k.perm → F.post () (z1, k1) w1 →
      Preserved z1 w1.1 → callFrom w1.1 z2 0x11e24#64 0x11acc#64 → X.pre () z2 w1.2)
    (z1 : State) (k1 : Kern) (h1 : exitCall1 c s z1) (hk1 : k1.perm = k.perm) :
    PReachK code exit_dom (ExitQ F X c s k) (z1, k1) := by
  have hent : Entry __libc_exit_fini_dom 0x11a54#64 z1 :=
    ⟨h1.1, h1.2.1, by rw [Reg.ra, h1.2.2.1]; decide, by rw [Reg.ra, h1.2.2.1]; decide,
      by rw [Reg.sp, h1.2.2.2.1]; unfold aligned at *; bv_omega⟩
  refine VerifiedProc.call hFv () hent (hFpre z1 k1 h1 hk1) (Dom.sub_of_ranges (by decide)) ?_
  rintro ⟨w, kw⟩ (⟨hx1, hpc1, hpres1, hpost1⟩ | ⟨hx1, hex1⟩)
  · simp only at hx1 hpc1 hpres1
    rw [Reg.ra, h1.2.2.1] at hpc1
    nocompiler_prun_n 2 [hpc1] using []
    refine exit_stage2b F X hXv c s k hsp hXpre z1 k1 (w, kw) h1 hk1 hpost1 hx1 hpres1 _ ?_
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals (try simp (config := { decide := true }) only [nocompiler_state])
    nocompiler_same
  · exact .done ⟨.inr hx1, .inr ⟨hx1, z1, k1, h1, hk1, .inl hex1⟩⟩

theorem not_one_of_preserved : ∀ r ∈ preservedRegs, r ≠ 1 := by decide

theorem exit_stage0 (F X : SpecP Unit) (hFv : VerifiedProc code __libc_exit_fini_dom 0x11a54#64 F)
    (hXv : VerifiedProc code __stdio_exit_dom 0x11e24#64 X)
    (c : Word) (s : State) (k : Kern) (hsp : aligned (s.reg 2) 16)
    (hFpre : ∀ z k', exitCall1 c s z → k'.perm = k.perm → F.pre () z k')
    (hXpre : ∀ z1 k1 w1 z2, exitCall1 c s z1 → k1.perm = k.perm → F.post () (z1, k1) w1 →
      Preserved z1 w1.1 → callFrom w1.1 z2 0x11e24#64 0x11acc#64 → X.pre () z2 w1.2)
    (p0 : State) (hpc : p0.pc = 0x11a50#64) (hx : p0.exit = none) (hra : p0.reg 1 = 0x11abc#64)
    (h2 : p0.reg 2 = s.reg 2 - 16#64) (h8 : p0.reg 8 = c)
    (hpr : ∀ r ∈ preservedRegs, r ≠ 2 → r ≠ 8 → p0.reg r = s.reg r)
    (hm : p0.mem = writeLE (writeLE s.mem (s.reg 2 - 8#64) (s.reg 1).toNat 8) (s.reg 2 - 16#64)
      (s.reg 8).toNat 8) (htr : p0.trace = s.trace) :
    PReachK code exit_dom (ExitQ F X c s k) (p0, k) := by
  have hent : Entry __funcs_on_exit_dom __funcs_on_exit_entry p0 :=
    ⟨hpc, hx, by rw [Reg.ra, hra]; decide, by rw [Reg.ra, hra]; decide,
      by rw [Reg.sp, h2]; unfold aligned at *; bv_omega⟩
  refine VerifiedProc.call (VerifiedImg.toProcNoSys __funcs_on_exit_verified (noEcall_of (by decide +kernel))) () hent
    ⟨trivial, retSpec_le _ _⟩ (Dom.sub_of_ranges (by decide)) ?_
  rintro ⟨w, kw⟩ (⟨hx0, hpc0, hpres0, -, hk0, htr0, hm0⟩ | ⟨_, hex0⟩)
  · simp only at hx0 hpc0 hpres0 hk0 hm0 htr0
    rw [Reg.ra, hra] at hpc0
    have hwm : w.mem = p0.mem := funext fun x => hm0 x (retSpec_nowrite _ x)
    nocompiler_prun_n 2 [hpc0] using []
    refine exit_stage1b F X hFv hXv c s k hsp hFpre hXpre _ kw ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ (by rw [hk0])
    all_goals (try simp (config := { decide := true }) only [nocompiler_state, hx0, hwm, hm, htr0, htr])
    · rw [hpres0 2 (by decide), h2]
    · rw [hpres0 8 (by decide), h8]
    · intro r hr hr2 hr8
      have hr1 := not_one_of_preserved r hr
      simp only [State.setPc_reg, State.reg_setReg_other _ _ _ _ hr1]
      rw [hpres0 r hr, hpr r hr hr2 hr8]
  · exact hex0.1.elim

/-- `exit` as compiled, for any `F` (`__libc_exit_fini`) and `X` (`__stdio_exit`): it does not return;
    it ends the process where `F` or `X` do, else with status `c` after `X`, by `exit_group`. -/
theorem exit_verified (F X : SpecP Unit) (hFv : VerifiedProc code __libc_exit_fini_dom 0x11a54#64 F)
    (hXv : VerifiedProc code __stdio_exit_dom 0x11e24#64 X) :
    VerifiedProc code exit_dom exit_entry (exitProcSpec F X) := by
  intro c s k he ⟨ha0, hw8, hw16, hFpre, hXpre⟩
  have hpc := he.pc
  have hx := he.live
  have hsp := he.sp
  simp only [exit_entry] at hpc
  simp only [Reg.sp, Reg.a0] at ha0 hw8 hw16 hsp
  have e16 : s.reg 2 + 18446744073709551600#64 = s.reg 2 - 16#64 := by bv_omega
  have e8 : s.reg 2 - 16#64 + 8#64 = s.reg 2 - 8#64 := by bv_omega
  have al8 : aligned (s.reg 2 - 8#64) 8 := by unfold aligned at *; bv_omega
  have al16 : aligned (s.reg 2 - 16#64) 8 := by unfold aligned at *; bv_omega
  nocompiler_prun_n 6 [hpc, e8, e16, al8, al16] using [hw8, hw16]
  refine exit_stage0 F X hFv hXv c s k hsp hFpre hXpre _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals (try simp (config := { decide := true }) only [nocompiler_state, ha0, hx])
  intro r hr hr2 hr8
  have hr1 := not_one_of_preserved r hr
  simp only [State.setPc_reg, State.setMem_reg, State.reg_setReg_other _ _ _ _ hr1,
    State.reg_setReg_other _ _ _ _ hr2, State.reg_setReg_other _ _ _ _ hr8]

/-! ## `__syscall_ret` (musl src/internal/syscall_ret.c) -/

theorem errnoSpec_le (s : State) (P : Perm) : (errnoSpec.perm () s).le P :=
  perm_le_of_empty rfl rfl rfl P

theorem errnoSpec_nowrite (s : State) (x : Word) : ¬ (errnoSpec.perm () s).writable x := by
  rintro ⟨r, hr, hm⟩
  simp only [Spec.perm, errnoSpec, List.nil_append, List.mem_singleton] at hr
  subst hr
  unfold Region.mem Spec.stackRegion at hm; simp at hm

/-- `___errno_location()` at the process level, by hand: a0 = tp - 164; nothing else changes (no syscall,
    no store), the kernel and the trace included. -/
def errnoP : SpecP Unit where
  pre := fun _ _ _ => True
  post := fun _ x y => y.1.reg 10 = x.1.reg 4 + 18446744073709551452#64 ∧ y.2 = x.2 ∧
    y.1.trace = x.1.trace ∧ y.1.mem = x.1.mem

theorem ___errno_location_proc : VerifiedProc code ___errno_location_dom ___errno_location_entry errnoP := by
  intro _ s k he _
  have hpc := he.pc
  have hx := he.live
  have hra4 := he.retAligned
  have hret := he.ret
  simp only [___errno_location_entry] at hpc
  simp only [Reg.ra] at hra4 hret
  nocompiler_prun_n 3 [hpc, ret_mask hra4, hra4] using []
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
    PReachK code __syscall_ret_dom (SysRetQ r s k) (p0, k) := by
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
    nocompiler_prun_n 6 [hpc1, h10', hal, BitVec.add_zero, hw2, e8, al8, al16, hrd8, hrd16, ret_mask hra4, hra4] using [hwe, hr8, hr16]
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

/-- `__syscall_ret(r)` as compiled, at the process level: `r` if it is not an error code, else `-1` with
    errno (at `tp - 164`) set to `-r`; its frame and errno are all it writes. By hand (nocompiler_auto
    on it: STATUS-A). -/
theorem __syscall_ret_verified : VerifiedProc code __syscall_ret_dom __syscall_ret_entry syscallRetP := by
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

end Examples.Libc.Slen
