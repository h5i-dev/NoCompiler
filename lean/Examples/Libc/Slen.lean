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

end Examples.Libc.Slen
