import LPS.Bridge.Syscalls
import NoCompiler.Linux.SysSteps

/-!
# Bridge: NoCompiler's kernel model refines LPS's syscall specs

NoCompiler's function proofs step a syscall by NoCompiler's own kernel model (`procSpec7` over `Kern`,
lean/NoCompiler/Linux). For a NoCompiler theorem to say something in LPS's terms, every outcome NoCompiler's
model allows must be one LPS's `syscall_spec` admits, the two kernel states staying related. This file
proves that per syscall, starting with `exit_group`.

`InRel i j`: the syscall input NoCompiler sees (`SyscallInput.of s`) and LPS's (`sys_input segs ms x8`) have
the same number and arguments (from `sim_ecall`, `syscall_args_rel`); memory is related separately.
-/

namespace LPS.Bridge
open LPS.RiscvSemantics

structure InRel (i : NoCompiler.Linux.SyscallInput) (j : SyscallInput) : Prop where
  sysno : j.in_sysno = i.sysno
  args : ∀ k, in_arg j k = i.arg k

/-- `exit_group(c)`: NoCompiler's model ends the process with status `c` (all of a0); LPS's spec admits the
    halt with `c & 255`, the status a parent sees. -/
theorem exit_group_refines {k k' : NoCompiler.Linux.Kern} {i : NoCompiler.Linux.SyscallInput}
    {o : NoCompiler.Linux.Outcome} {j : SyscallInput} (hr : InRel i j) (h94 : i.sysno = NoCompiler.sysExitGroup)
    (hs : NoCompiler.Linux.procSpec7 k i o k') (m : Model) :
    ∃ c, o = .exit c ∧ k' = k ∧
      syscall_spec j m (Ok (mkEffect 0#64 [] []) (with_halted (bv_and c (Z_to_bv 64 255)) m) []) := by
  obtain ⟨rfl, rfl⟩ := (NoCompiler.Linux.procSpec7_exitGroup h94).1 hs
  refine ⟨_, rfl, rfl, ?_⟩
  have hn : bv_unsigned j.in_sysno = 94 := by rw [hr.sysno, h94]; rfl
  have := exit_group_admits j m hn
  rwa [hr.args 0] at this

end LPS.Bridge
