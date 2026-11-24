import NoCompiler.Typed.Check

/-
Theorem D's check (健全性の証明.md, 定理 D): a whole program, the functions in an order where
each one's callees come earlier (S5: no recursion) or are external, with a signature and a
domain assumed for them (U1). Each function's domain is its own code and its callees'.
Proved in NoCompiler/Typed/Sound/Prog.lean (`Prog.check_sound`).
-/
namespace NoCompiler.Typed

/-- Entries, signatures and domains of the functions a call may go to: verified ones, and
    external ones assumed to meet theirs. -/
abbrev Env := List (Word × Sig × Dom)

namespace Fn
variable (f : Fn)

/-- None of `f`'s instructions lies in `Dg` (each range of `Dg` ends before `f`'s code
    starts, counting around the address space from the range's base). -/
def apartFrom (Dg : Dom) : Bool :=
  Dg.all fun r => decide (r.2 ≤ (f.entry - r.1).toNat ∧ (f.entry - r.1).toNat + 4 * f.size ≤ 2 ^ 64)

/-- `f`'s domain in `E`: its own code and its callees' domains. -/
def domIn (E : Env) : Dom :=
  (f.entry, 4 * f.size) :: f.callees.flatMap fun p =>
    match E.lookup p.1 with
    | some (_, Dg) => Dg
    | none => []

/-- Every callee is in `E` with the signature `f` uses, aligned, and away from `f`'s code. -/
def callsOk (E : Env) : Bool :=
  f.callees.all fun p =>
    match E.lookup p.1 with
    | some (σ, Dg) => decide (σ = p.2) && f.apartFrom Dg && decide (p.1.toNat % 4 = 0)
    | none => false

end Fn

namespace Prog

/-- Check the functions in order; each one is added to the environment of the next. -/
def check (c : Code) : Env → List Fn → Bool
  | _, [] => true
  | E, f :: fs => f.check c && !f.sig.isPartial && f.callsOk E &&
      check c ((f.entry, f.sig, f.domIn E) :: E) fs

/-- The environment after the functions: theirs and the external ones. -/
def env : Env → List Fn → Env
  | E, [] => E
  | E, f :: fs => env ((f.entry, f.sig, f.domIn E) :: E) fs

end Prog

end NoCompiler.Typed
