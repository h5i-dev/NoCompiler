import NoCompiler.Libc.Drain

/-!
# slen's fold for the drain shape (moved from NoCompiler/Libc/Drain.lean: binary-specific, round 9)

slen counts the bytes it reads: `procs` of `fun a _ => some (a + 1)` from `n` over `bs` is `n + bs.length`.
-/

namespace NoCompiler.Libc
open NoCompiler

/-- slen's fold: count the bytes. -/
theorem procs_count (n : Nat) (bs : List Byte) :
    procs (fun (a : Nat) (_ : Byte) => some (a + 1)) n bs = some (n + bs.length) := by
  induction bs generalizing n with
  | nil => rfl
  | cons b bs ih => simp only [procs, ih, List.length_cons]; congr 1; omega

end NoCompiler.Libc
