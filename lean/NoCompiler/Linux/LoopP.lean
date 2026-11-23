import NoCompiler.Linux.ProcSpec
import NoCompiler.Auto

/-!
# Loops given an invariant (round 7, C's row: loops)

`PReachK.loop I μ` (NoCompiler/Linux/ProcSpec.lean) turns a loop into one trip: from a state where `I` holds,
reach the end `Q`, or `I` again with a smaller `μ`. These tactics write the three parts of a trip's proof:

* `nocompiler_loop I μ`: the goal `∀ x, I x → PReachK c D Q x` (or `PReachK c D Q x₀` with `I x₀` as a
  hypothesis `h`, by `nocompiler_loop I μ from h`) becomes one trip from an `x` with `hI : I x`;
* `nocompiler_back [facts]`: at the back edge, the goal becomes the invariant at the new state; the measure's
  decrease is closed by the step simp set, the facts and `omega` (left as a goal if that fails);
* `nocompiler_exit`: at a loop exit, the goal becomes `Q` at the exit state.
-/
namespace NoCompiler.Linux

syntax "nocompiler_loop" term:max term:max (" from " term)? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| nocompiler_loop $I $μ) => `(tactic| (
      refine NoCompiler.Linux.PReachK.loop $I $μ ?_
      intro x hI))
  | `(tactic| nocompiler_loop $I $μ from $h) => `(tactic| (
      refine NoCompiler.Linux.PReachK.loop $I $μ ?_ _ $h
      intro x hI))

syntax "nocompiler_back" (" [" Lean.Parser.Tactic.simpArg,* "]")? : tactic
macro_rules
  | `(tactic| nocompiler_back) => `(tactic| nocompiler_back [])
  | `(tactic| nocompiler_back [$ts,*]) => `(tactic| (
      refine NoCompiler.Linux.PReachK.done (Or.inr ⟨?_, ?_⟩)
      case' refine_2 => (try simp (disch := nocompiler_decide_closed) only [nocompiler_state, $ts,*]); (try omega)
      try rotate_left))

macro "nocompiler_exit" : tactic => `(tactic| refine NoCompiler.Linux.PReachK.done (Or.inl ?_))

section Test
open NoCompiler

/-- A trip that ends at once: the exit tactic leaves `Q`. -/
example (c : Code) (D : Dom) (Q : State × Kern → Prop) (x₀ : State × Kern) (h : Q x₀) :
    PReachK c D Q x₀ := by
  nocompiler_loop (fun x => Q x) (fun _ => 0) from h
  nocompiler_exit
  exact hI

/-- A trip that goes back with a smaller measure. -/
example (c : Code) (D : Dom) (Q : State × Kern → Prop) (I : State × Kern → Prop)
    (f : State × Kern → State × Kern) (μ : State × Kern → Nat) (hf : ∀ x, I x → I (f x) ∧ μ (f x) < μ x)
    (hstep : ∀ x, I x → (PReachK c D (fun y => Q y ∨ (I y ∧ μ y < μ x)) (f x) →
      PReachK c D (fun y => Q y ∨ (I y ∧ μ y < μ x)) x)) (x₀ : State × Kern) (h0 : I x₀) :
    PReachK c D Q x₀ := by
  nocompiler_loop I μ from h0
  refine hstep x hI ?_
  nocompiler_back [(hf x hI).2]
  exact (hf x hI).1

end Test
end NoCompiler.Linux
