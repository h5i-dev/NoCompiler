import Examples.Libc.Flen.VmWaitImg
import Examples.Libc.Flen.UnlistLockedFileImg
import NoCompiler.Auto

/-!
# flen: its small musl functions, by hand (round 8, B)

Proofs over flen's own bytes (`examples/elf/libc-flen.elf`, images by `scripts/libc/fn_image.py`).
-/

/-- A function that returns at once and changes nothing a caller can see. -/
def Examples.Libc.Flen.nopSpec : NoCompiler.Spec Unit where
  pre := fun _ _ => True
  post := fun _ _ _ => True

namespace Examples.Libc.Flen.VmWait
open NoCompiler Examples.Libc.Flen.VmWaitImg

/-- `__vm_wait()`: single-threaded, a `ret`. -/
theorem __vm_wait_verified : VerifiedImg img dom base nopSpec := by
  rintro ⟨⟩ s he _
  nocompiler_auto __vm_wait_func s he

end Examples.Libc.Flen.VmWait

namespace Examples.Libc.Flen.UnlistLockedFile
open NoCompiler Examples.Libc.Flen.UnlistLockedFileImg

/-- `__unlist_locked_file(f)`: single-threaded, a `ret`. -/
theorem __unlist_locked_file_verified : VerifiedImg img dom base nopSpec := by
  rintro ⟨⟩ s he _
  nocompiler_auto __unlist_locked_file_func s he

end Examples.Libc.Flen.UnlistLockedFile
