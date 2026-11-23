import NoCompiler.Linux.RunMem

/-!
# Bounded runs (round 7, C's row)

`nocompiler_run` steps as far as it can. A proof cut at a point (to apply a lemma for the rest, a call's
specification, a loop's invariant) needs the run to stop there: `nocompiler_run_n N [facts] using [lemmas]`
takes exactly `N` steps, each with its access side goal closed as in `nocompiler_run`, and fails if one of them
does not go through. `nocompiler_runm_n` is the same over `nocompiler_pwstepm` (reads after disjoint writes), `nocompiler_prun_n`
over `nocompiler_pstep` (concrete states).
-/
namespace NoCompiler.Linux

syntax "nocompiler_run_n" num (" [" Lean.Parser.Tactic.simpArg,* "]")? (" using " "[" term,* "]")? : tactic
macro_rules
  | `(tactic| nocompiler_run_n $n) => `(tactic| nocompiler_run_n $n [] using [])
  | `(tactic| nocompiler_run_n $n [$ts,*]) => `(tactic| nocompiler_run_n $n [$ts,*] using [])
  | `(tactic| nocompiler_run_n $n using [$ls,*]) => `(tactic| nocompiler_run_n $n [] using [$ls,*])
  | `(tactic| nocompiler_run_n $n [$ts,*] using [$ls,*]) => `(tactic|
      iterate $n (nocompiler_pwstep [$ts,*]; try (with_reducible (show _ ∧ _); refine ⟨?_, ?_⟩; focus ((try simp (disch := nocompiler_decide_closed) only [$ts,*]); nocompiler_access using [$ls,*]))))

syntax "nocompiler_runm_n" num (" [" Lean.Parser.Tactic.simpArg,* "]")? (" using " "[" term,* "]")? : tactic
macro_rules
  | `(tactic| nocompiler_runm_n $n) => `(tactic| nocompiler_runm_n $n [] using [])
  | `(tactic| nocompiler_runm_n $n [$ts,*]) => `(tactic| nocompiler_runm_n $n [$ts,*] using [])
  | `(tactic| nocompiler_runm_n $n using [$ls,*]) => `(tactic| nocompiler_runm_n $n [] using [$ls,*])
  | `(tactic| nocompiler_runm_n $n [$ts,*] using [$ls,*]) => `(tactic|
      iterate $n (nocompiler_pwstepm [$ts,*]; try (with_reducible (show _ ∧ _); refine ⟨?_, ?_⟩; focus ((try simp (disch := nocompiler_decide_closed) only [$ts,*]); nocompiler_access using [$ls,*]))))

/-- `nocompiler_run_n` over `nocompiler_pstep` (a state given concretely, its words normalized by
    `nocompiler_norm`). -/
syntax "nocompiler_prun_n" num (" [" Lean.Parser.Tactic.simpArg,* "]")? (" using " "[" term,* "]")? : tactic
macro_rules
  | `(tactic| nocompiler_prun_n $n) => `(tactic| nocompiler_prun_n $n [] using [])
  | `(tactic| nocompiler_prun_n $n [$ts,*]) => `(tactic| nocompiler_prun_n $n [$ts,*] using [])
  | `(tactic| nocompiler_prun_n $n using [$ls,*]) => `(tactic| nocompiler_prun_n $n [] using [$ls,*])
  | `(tactic| nocompiler_prun_n $n [$ts,*] using [$ls,*]) => `(tactic|
      iterate $n (nocompiler_pstep [$ts,*]; try (with_reducible (show _ ∧ _); refine ⟨?_, ?_⟩; focus ((try simp (disch := nocompiler_decide_closed) only [$ts,*]); nocompiler_access using [$ls,*]))))

/-- One step in a region `D` given by its inclusion `hD` of a concrete one (A's `nocompiler_wstepD`,
    Libc/Musl/Tactic.lean): the pc's membership decided in the concrete region. -/
syntax "nocompiler_pwstepD" term:max " [" Lean.Parser.Tactic.simpArg,* "]" : tactic
macro_rules
  | `(tactic| nocompiler_pwstepD $hD [$ts,*]) => `(tactic| (
      refine NoCompiler.Linux.PReachK.exec_step ?hd ?hx ?h
      case hd => (try simp only [nocompiler_state, $ts,*]) <;> exact $hD _ (by decide)
      case hx => (try simp only [nocompiler_state, $ts,*]) <;> assumption
      case' h => (try simp only [nocompiler_state, nocompiler_image, $ts,*]); (try simp only [nocompiler_sem]); (try simp (disch := nocompiler_decide_closed) only [nocompiler_state, nocompiler_image, true_and, Bool.false_eq_true, $ts,*]); (try simp only [nocompiler_lit]); (try simp (disch := nocompiler_decide_closed) only [nocompiler_state, nocompiler_image, true_and, Bool.false_eq_true, $ts,*])
      rotate_left))

/-- `nocompiler_run_n` over `nocompiler_pwstepD hD`. -/
syntax "nocompiler_runD_n" num term:max " [" Lean.Parser.Tactic.simpArg,* "]" (" using " "[" term,* "]")? : tactic
macro_rules
  | `(tactic| nocompiler_runD_n $n $hD [$ts,*]) => `(tactic| nocompiler_runD_n $n $hD [$ts,*] using [])
  | `(tactic| nocompiler_runD_n $n $hD [$ts,*] using [$ls,*]) => `(tactic|
      iterate $n (nocompiler_pwstepD $hD [$ts,*]; try (with_reducible (show _ ∧ _); refine ⟨?_, ?_⟩; focus ((try simp (disch := nocompiler_decide_closed) only [$ts,*]); nocompiler_access using [$ls,*]))))

end NoCompiler.Linux
