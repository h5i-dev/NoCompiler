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

/-! ### musl's `FILE` (src/internal/stdio_impl.h): the fields the path touches, by byte offset -/
def F_flags : Word := 0#64
def F_rpos : Word := 8#64
def F_rend : Word := 16#64
def F_wend : Word := 32#64
def F_wpos : Word := 40#64
def F_wbase : Word := 56#64
def F_buf : Word := 88#64
def F_buf_size : Word := 96#64

/-- `__towrite(f)`: unless `f` cannot be written (flag 8, F_NOWR; then -1), the read pointers cleared and
    the write pointers at the buffer, 0. It writes the first 144 bytes of `*f` and no stack. -/
def towriteSpec : Spec Word where
  pre := fun f s => s.reg Reg.a0 = f ∧ aligned f 8
  post := fun f s s' =>
    (read32 s.mem f &&& 8#64 = 0 → s'.reg Reg.a0 = 0 ∧
      read64 s'.mem (f + F_wpos) = read64 s.mem (f + F_buf) ∧
      read64 s'.mem (f + F_wbase) = read64 s.mem (f + F_buf) ∧
      read64 s'.mem (f + F_wend) = read64 s.mem (f + F_buf) + read64 s.mem (f + F_buf_size) ∧
      read64 s'.mem (f + F_rpos) = 0 ∧ read64 s'.mem (f + F_rend) = 0) ∧
    (read32 s.mem f &&& 8#64 ≠ 0 → s'.reg Reg.a0 = -1)
  writes := fun f _ => [⟨f, 144⟩]

/-- An 8-byte load at `f + b` past a store at `f + a` that it does not overlap, the offsets constants. -/
theorem read64_writeLE_off (m : Word → Byte) (f a b : Word) (v w : Nat)
    (h1 : w ≤ (b - a).toNat) (h2 : 8 ≤ (a - b).toNat) :
    read64 (writeLE m (f + a) v w) (f + b) = read64 m (f + b) := by
  apply Auto.read64_writeLE_other'
  · have : f + b - (f + a) = b - a := by bv_omega
    rw [this]; exact h1
  · have : f + a - (f + b) = a - b := by bv_omega
    rw [this]; exact h2

theorem __towrite_verified : VerifiedImg code __towrite_dom __towrite_entry towriteSpec := by
  rintro f s he ⟨ha0, hal⟩
  nocompiler_auto __towrite_func s he [hal]
  case entry_ret_x50_0 => intro h; simp [h] at hb_12208
  case entry_ret_x50_1 => intro _; trivial
  case entry_ret_x40_1 => intro h; simp_all
  case entry_ret_x40_0 =>
    intro _
    refine ⟨trivial, ?_⟩
    simp only [F_wpos, F_wbase, F_wend, F_rpos, F_rend, F_buf, F_buf_size]
    simp (disch := decide) only [read64_writeLE_off, Auto.read64_writeLE_same', BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
    simp

/-! ### `__lock` while the process has one thread: no atomic instruction is fetched

`__lock` (src/thread/__lock.c) begins `if (!libc.need_locks) return;`: a load of the byte
`__libc.need_locks` (0x1419b: `__libc` at 0x14198 in `.bss`, offset 3) and a branch to its `ret` at
0x12cc0. Its later words are A-extension `lr.w`/`sc.w`, which have no semantics here (`decode` gives
none). `__lock_verified` proves that from `need_locks = 0` the run returns without reaching them: a
step needs a decoded instruction, so a proof that went past the branch could not be built. -/

/-- `__lock(l)` with `__libc.need_locks = 0`: returns, writing nothing. -/
def lockSpec : Spec Unit where
  pre := fun _ s => s.mem 0x1419b#64 = 0
  post := fun _ _ _ => True
  reads := fun _ _ => [⟨0x1419b#64, 1⟩]

theorem __lock_verified : VerifiedImg code __lock_dom __lock_entry lockSpec := by
  rintro ⟨⟩ s he h0
  nocompiler_auto __lock_func s he [h0]
    loop_inv 0x12afc#64 (fun _ => False) measure (fun _ => 0)
  -- The fall-through into the atomics: excluded by need_locks = 0 (the cut at 0x12afc has invariant False,
  -- so nothing past the branch is ever explored).
  case entry_to_x10 =>
    simp only [lockSpec] at h0
    simp [h0] at hb_12af8

/-- `__ofl_lock()`: locks the list of open files (a no-op with one thread, `__lock_verified`) and returns
    its head's address, `.sbss + 64` = 0x14010. -/
def oflLockSpec : Spec Unit where
  pre := fun _ s => s.mem 0x1419b#64 = 0 ∧ ¬ (Spec.stackRegion s 16).mem 0x1419b#64
  post := fun _ _ s' => s'.reg Reg.a0 = 0x14010#64
  reads := fun _ _ => [⟨0x1419b#64, 1⟩]
  stack := 16

theorem __ofl_lock_verified : VerifiedImg code __ofl_lock_dom __ofl_lock_entry oflLockSpec := by
  rintro ⟨⟩ s he ⟨h0, hs⟩
  nocompiler_auto __ofl_lock_func s he calls [__lock_verified]
  case entry_call___lock_verified_pre =>
    -- The `ra` save (8 bytes at sp - 8) is in the frame, which does not hold `need_locks`.
    rw [writeLE_of_not_mem (r := ⟨s.reg 2 + 18446744073709551608#64, 8⟩) (by simp [Region.covers])]
    · exact h0
    · intro hm; apply hs
      simp only [Region.mem, Spec.stackRegion, Reg.sp] at hm ⊢
      bv_omega

end Examples.Libc.Slen
