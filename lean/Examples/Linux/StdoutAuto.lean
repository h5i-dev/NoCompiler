import Examples.Libc.SlenProc
import NoCompiler.Linux.AutoP

/-!
# A's `__stdout_write` by `nocompiler_auto_p` (QUEUE-D C1 done-condition, part 1)

The same statement as `Examples.Libc.Slen.__stdout_write_verified` (Examples/Libc/SlenProc.lean, A's), proved
with the tactic in place of the hand steps (`nocompiler_pstep`, the ioctl by `ioctl_cases`): the ioctl is
stepped by the Linux layer, the tail call of `__stdio_write` goes through `calls [hWvf W hWv hWf]` (a callee whose
specification `W` is a variable).
-/
set_option maxRecDepth 200000

namespace Examples.Linux.StdoutAuto
open NoCompiler NoCompiler.Linux Examples.Libc.SlenImage Examples.Libc.Slen

/-- `W` with what its `StdioWriteFrame` gives a caller, as equations the tactic rewrites with after the call:
    the word at the callee's `sp + 8` (the caller's saved `ra`) and the kernel's permission unchanged. -/
def Wf (W : SpecP (Word × Word × Word)) : SpecP (Word × Word × Word) where
  pre := W.pre
  post := fun a x y => W.post a x y ∧ read64 y.1.mem (x.1.reg 2 + 8#64) = read64 x.1.mem (x.1.reg 2 + 8#64) ∧
    y.2.perm = x.2.perm
  onExit := W.onExit

theorem hWvf (W : SpecP (Word × Word × Word))
    (hWv : VerifiedProc code __stdio_write_dom 0x1247c#64 W) (hWf : StdioWriteFrame W) :
    VerifiedProc code __stdio_write_dom 0x1247c#64 (Wf W) := by
  refine VerifiedProc.post_mono hWv (fun _ _ _ h => h) ?_
  rintro a x y _ (⟨h1, h2, h3, hpost⟩ | ⟨h1, h2⟩)
  · obtain ⟨hfr, hperm⟩ := hWf _ _ _ hpost
    refine .inl ⟨h1, h2, h3, hpost, ?_, hperm⟩
    unfold read64
    rw [readLE_congr (m' := x.1.mem) (fun j hj => hfr _ (by simp only [Region.mem, Reg.sp]; bv_omega))]
  · exact .inr ⟨h1, h2⟩

set_option maxHeartbeats 4000000 in
theorem stdout_auto (W : SpecP (Word × Word × Word))
    (hWv : VerifiedProc code __stdio_write_dom 0x1247c#64 W) (hWf : StdioWriteFrame W) :
    VerifiedProc code __stdout_write_dom __stdout_write_entry (stdoutWriteSpec W) := by
  apply VerifiedProc.of_execP
  rintro ⟨f, buf, len⟩ s k he ⟨ha0, ha1, ha2, hal, hrf, hw72, hr120, hw144, hwsp, hrsp, hdisj, hW⟩
  -- the frame's permissions with the address in the step tactics' normal form (`sp + -8`, not `sp - 8`):
  -- given as an equation `sp + -8 = sp - 8` the rewrite and the normaliser undo each other
  have e8 : s.reg 2 - 8#64 = s.reg 2 + 18446744073709551608#64 := by bv_omega
  have hwsp' : k.perm.canWrite (s.reg 2 + 18446744073709551608#64) 8 := by rw [← e8]; exact hwsp
  have hrsp' : k.perm.canRead (s.reg 2 + 18446744073709551608#64) 8 := by rw [← e8]; exact hrsp
  clear e8
  -- FILE's first 152 bytes off the 16-byte frame, as the two facts the read-over-write closer's omega uses
  have hd1 : 152 ≤ ((s.reg 2 - 16#64) - f).toNat := hdisj.1
  have hd2 : 16 ≤ (f - (s.reg 2 - 16#64)).toNat := hdisj.2
  -- the saved ra, read back after the stores the run makes: each store's region is off the slot at sp - 8
  have hk72 : ∀ m v, read64 (writeLE m (f + 72#64) v 8) (s.reg 2 + 18446744073709551608#64) =
      read64 m (s.reg 2 + 18446744073709551608#64) := fun m v =>
    Auto.read64_writeLE_other' m _ _ v 8 (by bv_omega) (by bv_omega)
  have hk144 : ∀ m v, read64 (writeLE m (f + 144#64) v 4) (s.reg 2 + 18446744073709551608#64) =
      read64 m (s.reg 2 + 18446744073709551608#64) := fun m v =>
    Auto.read64_writeLE_other' m _ _ v 4 (by bv_omega) (by bv_omega)
  have hkw : ∀ m (ws : List Byte), ws.length = 8 →
      read64 (writeBytes m (s.reg 2 + 18446744073709551600#64) ws) (s.reg 2 + 18446744073709551608#64) =
      read64 m (s.reg 2 + 18446744073709551608#64) := by
    intro m ws hl; unfold read64; rw [readLE_writeBytes_above (fun j hj => by rw [hl]; bv_omega)]
  -- f's flags byte, read after the store of ra: f is off the frame
  have hflag : writeLE s.mem (s.reg 2 + 18446744073709551608#64) (s.reg 1).toNat 8 f = s.mem f :=
    writeLE_other _ _ _ _ _ (by bv_omega)
  have hsv : ∀ m, read64 (writeLE m (s.reg 2 + 18446744073709551608#64) (s.reg 1).toNat 8)
      (s.reg 2 + 18446744073709551608#64) = s.reg 1 := by
    intro m; rw [Auto.read64_writeLE_same']; simp
  nocompiler_auto_p __stdout_write_func s he [ha0, ha1, ha2, hal, hrf, hw72, hr120, hw144, hwsp', hrsp', hk72, hk144, hkw, hsv, hflag, sysIoctl, tiocgwinsz] calls [hWvf W hWv hWf]
  -- what is left is about the specification, not the code: each call state is a `stdoutCall` (A's) for the
  -- path's (wsz, lbf), and the callee's precondition is `hW` of it
  all_goals (try (refine hW _ ?_))
  all_goals (try (first
    | (refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, none, false, ?_, ?_, ?_⟩ <;>
        (try nocompiler_anorm [stdoutMem, ha0, ha1, ha2, hflag]) <;>
        first | exact he.live | nocompiler_same | (intro _; trivial) | (intro h; simp_all) | done)
    | (refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, none, true, ?_, ?_, ?_⟩ <;>
        (try nocompiler_anorm [stdoutMem, ha0, ha1, ha2, hflag]) <;>
        first | exact he.live | nocompiler_same | (intro _; trivial) | (intro h; simp_all) | done)
    | (refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, some sys_ws, false, ?_, ?_, ?_⟩ <;>
        (try nocompiler_anorm [stdoutMem, ha0, ha1, ha2, hflag]) <;>
        first | exact he.live | nocompiler_same | (intro _; trivial) | (intro h; simp_all) | done)))

end Examples.Linux.StdoutAuto
