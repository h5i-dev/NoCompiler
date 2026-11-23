import NoCompiler.Auto

/-!
# Register frames (round 7, C's row: frames)

Two blocks a hand proof writes at nearly every end of a run (A's Examples/Libc and Libc/Musl: 52 and 14 of
them):

* `nocompiler_reg_frame hq`: a goal `(… s.setReg r v …).reg q = s.reg q` (any chain of `setReg`,
  `setPc`, `setMem`) for a `q` given only by `hq : q ∉ [r₁, …, rₙ]`, the registers the code writes. In
  place of `obtain ⟨a12, a13, …⟩ := hne q hq; repeat (first | rw [State.setPc_reg] | …)`.
* `nocompiler_preserved [facts]`: a goal `Preserved s s'` (or its unfolding `∀ r ∈ preservedRegs, …`): the
  15 callee-saved registers one by one, each by the step simp set and the facts. In place of
  `intro q hq; simp only [preservedRegs, …] at hq; rcases hq with rfl | … ; all_goals …`.
-/
namespace NoCompiler.Linux

syntax "nocompiler_reg_frame" term : tactic
macro_rules
  | `(tactic| nocompiler_reg_frame $h) => `(tactic| (
      have hne := $h
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hne
      simp only [NoCompiler.State.setPc_reg, NoCompiler.State.setMem_reg, NoCompiler.State.reg_setReg_other,
        hne, ne_eq, not_false_eq_true]))

set_option hygiene false in
syntax "nocompiler_preserved" (" [" Lean.Parser.Tactic.simpArg,* "]")? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| nocompiler_preserved) => `(tactic| nocompiler_preserved [])
  | `(tactic| nocompiler_preserved [$ts,*]) => `(tactic| (
      (try unfold NoCompiler.Preserved)
      intro q hq
      simp only [NoCompiler.preservedRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals (first
        | (simp (disch := nocompiler_decide_closed) only [nocompiler_state, $ts,*]; done)
        | (simp (config := { decide := true }) only [nocompiler_state, $ts,*]; done))))

section Test
open NoCompiler

example (s : State) (q : Reg) (hq : q ∉ [(11 : Reg), 12, 5]) (v w : Word) (p : Word) (m : Word → Byte) :
    (((s.setReg 12 v).setPc p).setMem m |>.setReg 5 w).reg q = s.reg q := by
  nocompiler_reg_frame hq

example (s : State) (v : Word) (p : Word) : Preserved s ((s.setReg 10 v).setPc p) := by
  nocompiler_preserved

end Test
end NoCompiler.Linux
