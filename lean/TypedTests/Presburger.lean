import NoCompiler.Typed.Search
/-! Tests of the entailment procedure (not part of the core library), checked by the
    kernel (`decide`). -/
open NoCompiler.Typed

namespace TypedTests.Presburger
def v (x : Nat) : IExpr := .var x
def k (c : Int) : IExpr := .lit c
def two64 : Int := 2 ^ 64
def n := v 0
def ρ := v 1
def m := v 2
def a := (ρ.add (n.smul 8)).sub (m.smul 8)

/-- 0 ≤ n < 2^64, ¬ (2^64 ∣ n) ⊢ 1 ≤ n (the `beq` fall-through of the note's `sum`). -/
example : (Query.mk [.le (k 0) n, .lt n (k two64), .not (.dvd (2^64) n)] (.le (k 1) n)).decide = true := by
  decide
/-- The load check of `sum`'s loop. -/
example : (Query.mk [.le (k 1) m, .le m n, .dvd 8 ρ]
    (.and (.le ρ a) (.and (.le (a.add (k 8)) (ρ.add (n.smul 8))) (.dvd 8 a)))).decide = true := by
  decide
/-- Not valid, so not proved. -/
example : (Query.mk [.le (k 0) n] (.le (k 1) n)).decide = false := by decide
/-- Integer, not rational, infeasibility: 1 ≤ 2x ≤ 1. -/
example : (Query.mk [.le (k 1) (n.smul 2), .le (n.smul 2) (k 1)] .ff).decide = true := by decide
end TypedTests.Presburger
