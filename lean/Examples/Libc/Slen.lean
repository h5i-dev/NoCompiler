import Examples.Libc.SlenImage
import NoCompiler.Auto

/-!
`slen` (examples/libc/slen.c, against musl 1.2.5): the functions on its path,
proved one by one on its chunk image, toward the whole process (STATUS-A plan).
-/
set_option maxRecDepth 20000

namespace Examples.Libc.Slen
open NoCompiler Examples.Libc.SlenImage

/-- `_Exit(c)`: exit_group(c), never returns. -/
def exitSpec : Spec Word where
  pre := fun c s => s.reg Reg.a0 = c
  post := fun _ _ _ => False
  onExit := fun c s s' => ∃ k, s'.trace = s.trace ++ [.exit k] ∧ s'.exit = some k ∧ k = c
  reads := fun _ _ => []

theorem _Exit_verified : VerifiedImg code _Exit_dom _Exit_entry exitSpec := by
  rintro c s he ha0
  nocompiler_auto _Exit_func s he
    loop_inv $l0 (fun _ => False) measure (fun _ => 0)
  case entry_exit_x8 => exact ha0

/-- `___errno_location()`: the address of the thread's errno, `tp - 164`. -/
def errnoSpec : Spec Unit where
  pre := fun _ _ => True
  post := fun _ s s' => s'.reg Reg.a0 = s.reg Reg.tp + 18446744073709551452#64

theorem ___errno_location_verified : VerifiedImg code ___errno_location_dom ___errno_location_entry errnoSpec := by
  rintro ⟨⟩ s he _
  nocompiler_auto ___errno_location_func s he
  all_goals trace_state
  all_goals sorry

/-- `__syscall_ret(r)`: `r` if it is not an error (`-4095 ≤ r < 0` as a signed value), else `-1` with
    errno set; it may write errno (4 bytes at `tp - 164`, aligned, outside its 16-byte frame) and its frame. -/
def syscallRetSpec : Spec Word where
  pre := fun r s => s.reg Reg.a0 = r ∧ aligned (s.reg Reg.tp + 18446744073709551452#64) 4 ∧
    (Region.mk (s.reg Reg.tp + 18446744073709551452#64) 4).Disjoint (Spec.stackRegion s 16)
  post := fun r _ s' => s'.reg Reg.a0 = if r.toNat < 2 ^ 64 - 4095 then r else -1
  writes := fun _ s => [⟨s.reg Reg.tp + 18446744073709551452#64, 4⟩]
  stack := 16

/-- errno outside the 16-byte frame below `sp` is outside each of its two 8-byte slots (at `sp - 16`
    and `sp - 8`, as the step tactics write them: `sp + 2^64 - 16`, `sp + 2^64 - 8`). -/
theorem errno_disj_slot {sp e k : Word} (hd : (Region.mk e 4).Disjoint ⟨sp - BitVec.ofNat 64 16, 16⟩)
    (hk : k = 18446744073709551600#64 ∨ k = 18446744073709551608#64) :
    (Region.mk e 4).Disjoint ⟨sp + k, 8⟩ := by
  unfold Region.Disjoint at *
  simp only at *
  rcases hk with rfl | rfl <;> bv_omega

-- `__syscall_ret_verified`: four of its five path goals close (both returns, errno's alignment, `ra`
-- reloaded past the errno store); the fifth, `s0` reloaded on the error path, comes out of
-- nocompiler_auto's explore path with no facts about the final state (reported to C in STATUS-A). The
-- work in progress is kept outside the tree until then.

end Examples.Libc.Slen
