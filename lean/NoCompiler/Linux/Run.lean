import NoCompiler.Linux.AutoP

/-!
# Running straight-line code at the process level (round 7, C's row: tactics)

A hand proof over `PReachK` steps one instruction per line (`nocompiler_wstep [facts]` in A's
Examples/Libc), and after each load or store gives the access's
permission by hand (`refine ⟨wF 136 4 (by omega), ?_⟩`). These tactics absorb that:

* `nocompiler_pwstep [facts]`: one step (the library's copy of A's `nocompiler_wstep`, unchanged).
* `nocompiler_run [facts] using [lemmas]`: steps until the next step does not apply (a branch whose
  condition the facts do not decide, a call, an ecall, the function's end); after every load and store,
  the permission (and alignment) side goal is closed from the hypotheses or from the `using` lemmas
  (each applied, its side conditions by `omega`, `rfl`, `decide` or, for a closed region's `covers`,
  unfolding it and `decide`; also through
  `Perm.canRead_of_canWrite`). A side goal none of them closes stops the run there, the goal left as it
  is for the hand proof. The split into side goal and rest is tried only when the goal is a conjunction up
  to reducible unfolding (`with_reducible (show _ ∧ _)`): unguarded, it reduces the state after every step
  (A's il_end: a timeout at the default heartbeats, against 5 s guarded).
-/
namespace NoCompiler.Linux

/-- One process-level step (A's `nocompiler_wstep`, Examples/Libc/StdioWrite.lean, as a library tactic). -/
syntax "nocompiler_pwstep" (" [" Lean.Parser.Tactic.simpArg,* "]")? : tactic
macro_rules
  | `(tactic| nocompiler_pwstep) => `(tactic| nocompiler_pwstep [])
  | `(tactic| nocompiler_pwstep [$ts,*]) => `(tactic| (
      refine NoCompiler.Linux.PReachK.exec_step ?hd ?hx ?h
      case hd => (try simp only [nocompiler_state, $ts,*]) <;> decide
      case hx => (try simp only [nocompiler_state, $ts,*]) <;> assumption
      case' h => (try simp only [nocompiler_state, nocompiler_image, $ts,*]); (try simp only [nocompiler_sem]); (try simp (disch := nocompiler_decide_closed) only [nocompiler_state, nocompiler_image, true_and, Bool.false_eq_true, $ts,*]); (try simp only [nocompiler_lit]); (try simp (disch := nocompiler_decide_closed) only [nocompiler_state, nocompiler_image, true_and, Bool.false_eq_true, $ts,*])
      rotate_left))

/-- An access's side goal (`P.canRead a n`, `P.canWrite a n`, `aligned a n`) from the hypotheses or a
    `using` lemma. -/
syntax "nocompiler_access" (" using " "[" term,* "]")? : tactic
macro_rules
  | `(tactic| nocompiler_access) => `(tactic| nocompiler_access using [])
  | `(tactic| nocompiler_access using [$ls,*]) => `(tactic| first
      | assumption
      | exact NoCompiler.Perm.canRead_of_canWrite (by assumption)
      | (first $[| (apply $ls <;> first | omega | rfl | decide | assumption | (simp only [NoCompiler.Region.covers]; decide))]*)
      | (apply NoCompiler.Perm.canRead_of_canWrite
         first $[| (apply $ls <;> first | omega | rfl | decide | assumption | (simp only [NoCompiler.Region.covers]; decide))]*))

/-- Step until the step does not apply, closing each access's side goal (see the module doc). -/
syntax "nocompiler_run" (" [" Lean.Parser.Tactic.simpArg,* "]")? (" using " "[" term,* "]")? : tactic
macro_rules
  | `(tactic| nocompiler_run) => `(tactic| nocompiler_run [] using [])
  | `(tactic| nocompiler_run [$ts,*]) => `(tactic| nocompiler_run [$ts,*] using [])
  | `(tactic| nocompiler_run using [$ls,*]) => `(tactic| nocompiler_run [] using [$ls,*])
  | `(tactic| nocompiler_run [$ts,*] using [$ls,*]) => `(tactic|
      -- a load or a store leaves `side ∧ rest`: the side goal closed, or the run stops there
      repeat (first
        | (nocompiler_pwstep [$ts,*]; try (with_reducible (show _ ∧ _); refine ⟨?_, ?_⟩; focus ((try simp (disch := nocompiler_decide_closed) only [$ts,*]); nocompiler_access using [$ls,*])))
        -- a branch's condition decided by the facts given here (an `if` left by an earlier step)
        | simp (disch := nocompiler_decide_closed) only [nocompiler_state, Bool.false_eq_true, ↓reduceIte, $ts,*]))

end NoCompiler.Linux
