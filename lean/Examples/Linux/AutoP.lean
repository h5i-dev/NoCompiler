import Examples.Linux.AutoPImg
import NoCompiler.Linux.AutoP

/-!
# `nocompiler_auto_p` on two leaf functions with a Linux-layer syscall (QUEUE-D C1)

examples/linux-autop/autop.s: `tiocg` is `ioctl(a0, a1, a2)` (a7 = 29) then `ret`; `wv` is
`writev(a0, a1, a2)` (a7 = 66) then `ret`. Each is proved at the process level by the tactic alone:
the ecall is stepped by the Linux layer (`ioctl_casesU`, `writev_casesU`), every outcome continues to
the return, and the kernel is the same at the end.
-/
namespace Examples.Linux.AutoP
open NoCompiler NoCompiler.Linux Examples.Linux.AutoPImg

/-- `tiocg` with a1 = TIOCGWINSZ: returns ENOTTY, EBADF or 0, the kernel unchanged. -/
def tiocgSpec : SpecP Unit where
  pre := fun _ s _ => s.reg Reg.a1 = tiocgwinsz
  post := fun _ x y => y.2 = x.2 ∧
    (y.1.reg Reg.a0 = enotty ∨ y.1.reg Reg.a0 = ebadf ∨ y.1.reg Reg.a0 = 0)

theorem tiocg_ok : VerifiedProc code tiocg_dom tiocg_entry tiocgSpec := by
  apply VerifiedProc.of_execP
  rintro _ s k he h1
  have h11 : s.reg 11 = tiocgwinsz := h1
  nocompiler_auto_p tiocg_func s he [h11]

/-- `wv`: returns, the kernel unchanged (what it wrote is in the trace). -/
def wvSpec : SpecP Unit where
  pre := fun _ _ _ => True
  post := fun _ x y => y.2 = x.2

theorem wv_ok : VerifiedProc code wv_dom wv_entry wvSpec := by
  apply VerifiedProc.of_execP
  rintro _ s k he _
  nocompiler_auto_p wv_func s he

/-- `rd`: `readv(a0, a1, a2)` then `ret`; the kernel may change (a file's offset), so the postcondition says
    nothing of it. -/
def rdSpec : SpecP Unit where
  pre := fun _ _ _ => True
  post := fun _ _ _ => True

theorem rd_ok : VerifiedProc code rd_dom rd_entry rdSpec := by
  apply VerifiedProc.of_execP
  rintro _ s k he _
  nocompiler_auto_p rd_func s he

/-- `ex`: `exit_group(a0)`: the process ends with status a0. -/
def exSpec : SpecP Unit where
  pre := fun _ _ _ => True
  post := fun _ _ _ => True
  onExit := fun _ x y => y.1.exit = some (x.1.reg Reg.a0)

theorem ex_ok : VerifiedProc code ex_dom ex_entry exSpec := by
  apply VerifiedProc.of_execP
  rintro _ s k he _
  nocompiler_auto_p ex_func s he

end Examples.Linux.AutoP
