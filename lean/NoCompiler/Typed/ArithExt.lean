import NoCompiler.Typed.CheckBase

/-
Arithmetic rules beyond the ones in Check.lean (`Fn.arith`): what `Fn.arith` does for every
register-writing instruction it has no rule of its own for. Proved in
NoCompiler/Typed/Sound/ArithExt.lean (`Fn.arithExt_sound`), which `Fn.arith_sound` uses.

Owned by agent U (docs/typed, STATUS files): the rules the Rust checker has (I20/I23/I29/...).
The default is the note's last row: a fresh word `x` with `0 ≤ x < 2^64`.
-/
namespace NoCompiler.Typed

namespace Fn
variable (f : Fn)

def arithExt (S : STy) (i : Instr) : Option STy :=
  match writesReg i with
  | some rd => some (anyWord S rd (f.freshAt S))
  | none => none

end Fn

end NoCompiler.Typed
