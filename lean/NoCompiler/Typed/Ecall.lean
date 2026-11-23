import NoCompiler.Typed.ArithExt

/-
The `ecall` rule (syscalls, Lemma 9 of 健全性の証明.md; signatures I31). Proved in
NoCompiler/Typed/Sound/Ecall.lean (`Fn.ecall_step`), which the main induction uses.

Owned by agent U (STATUS.md). Until the rule exists every `ecall` is rejected.
-/
namespace NoCompiler.Typed

namespace Fn

/-- `ecall` at point `k` with type `S` (the successor edge is the rule's to check). -/
def ecallOk (_f : Fn) (_k : Nat) (_S : STy) : Bool := false

end Fn

end NoCompiler.Typed
