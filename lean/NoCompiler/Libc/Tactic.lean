import NoCompiler.ImageSimp
import NoCompiler.Struct
import NoCompiler.Auto
import NoCompiler.Linux.ProcSpec
import NoCompiler.Linux.SysSteps
import NoCompiler.Linux.Writev
import NoCompiler.Libc.Mem
import NoCompiler.Libc.Word
import NoCompiler.Libc.Relocate
import NoCompiler.Linux.RunN

/-!
# Step tactics for process-level proofs over states given by facts

`nocompiler_vstep` and `nocompiler_wstep` take one instruction step of a `PReachK` goal (`PReachK.exec_step`),
with the given facts as rewrite rules, for states whose pc and registers are known only by hypotheses.
-/

/-- `nocompiler_pstep` without `decide := true` passes: for a state given only by facts (its pc and
    registers by hypotheses), where those passes hit maxRecDepth. -/
syntax "nocompiler_vstep" (" [" Lean.Parser.Tactic.simpArg,* "]")? : tactic
macro_rules
  | `(tactic| nocompiler_vstep) => `(tactic| nocompiler_vstep [])
  | `(tactic| nocompiler_vstep [$ts,*]) => `(tactic| (
      refine NoCompiler.Linux.PReachK.exec_step ?hd ?hx ?h
      case hd => (try simp only [nocompiler_state, $ts,*]) <;> decide
      case hx => (try simp only [nocompiler_state, $ts,*]) <;> assumption
      case' h => (try simp only [nocompiler_state, nocompiler_image, $ts,*]); (try nocompiler_vnorm [true_and, $ts,*]); (try nocompiler_vnorm [true_and, $ts,*])
      rotate_left))

/-- `nocompiler_vstep` without the word normal form (`nocompiler_nat`): addresses keep the form the
    rewrite facts give them (`sp - 72 + 8`, rewritten by an equation to `sp - 64`). -/
syntax "nocompiler_wstep" (" [" Lean.Parser.Tactic.simpArg,* "]")? : tactic
macro_rules
  | `(tactic| nocompiler_wstep) => `(tactic| nocompiler_wstep [])
  | `(tactic| nocompiler_wstep [$ts,*]) => `(tactic| (
      refine NoCompiler.Linux.PReachK.exec_step ?hd ?hx ?h
      case hd => (try simp only [nocompiler_state, $ts,*]) <;> decide
      case hx => (try simp only [nocompiler_state, $ts,*]) <;> assumption
      case' h => (try simp only [nocompiler_state, nocompiler_image, $ts,*]); (try simp only [nocompiler_sem]); (try simp (disch := nocompiler_decide_closed) only [nocompiler_state, nocompiler_image, true_and, Bool.false_eq_true, $ts,*]); (try simp only [nocompiler_lit]); (try simp (disch := nocompiler_decide_closed) only [nocompiler_state, nocompiler_image, true_and, Bool.false_eq_true, $ts,*])
      rotate_left))

/-- `nocompiler_wstep` in a region `D` given by its inclusion `hD` of a concrete one (the pc's membership is
    decided in the concrete one). -/
syntax "nocompiler_wstepD" term:max " [" Lean.Parser.Tactic.simpArg,* "]" : tactic
macro_rules
  | `(tactic| nocompiler_wstepD $hD [$ts,*]) => `(tactic| (
      refine NoCompiler.Linux.PReachK.exec_step ?hd ?hx ?h
      case hd => (try simp only [nocompiler_state, $ts,*]) <;> exact $hD _ (by decide)
      case hx => (try simp only [nocompiler_state, $ts,*]) <;> assumption
      case' h => (try simp only [nocompiler_state, nocompiler_image, $ts,*]); (try simp only [nocompiler_sem]); (try simp (disch := nocompiler_decide_closed) only [nocompiler_state, nocompiler_image, true_and, Bool.false_eq_true, $ts,*]); (try simp only [nocompiler_lit]); (try simp (disch := nocompiler_decide_closed) only [nocompiler_state, nocompiler_image, true_and, Bool.false_eq_true, $ts,*])
      rotate_left))
