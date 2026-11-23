import NoCompiler.Linux.DischargeP
import NoCompiler.Auto

/-!
# Calls to verified callees (round 7, C's row: callee specs from the library)

At a call a hand proof builds the callee's `Entry` field by field (pc, live, the return address outside the
callee and aligned, sp aligned) and the domain inclusion, then applies `VerifiedProc.call`. Here:

* `nocompiler_entry [facts]`: an `Entry D e s` goal, each field by the step simp set and the facts, then
  `rfl`, `assumption`, `decide`, or `bv_omega` for alignment;
* `nocompiler_call h a [facts]`: `VerifiedProc.call h a` with the entry and the domain inclusion
  (`Dom.sub_of_ranges` decided, or a hypothesis `hD : D'.sub D` composed with it) closed; left: the callee's
  precondition, then the run after every way the callee ends (and the inclusion, if neither closes it);
* `nocompiler_call h a via hi [facts]`: the same through `VerifiedProc.call_of_implies` (a library callee
  proved at a stronger specification, `hi : SpecP.Implies sp₁ sp₂ f`).
-/
namespace NoCompiler.Linux

syntax "nocompiler_entry" (" [" Lean.Parser.Tactic.simpArg,* "]")? : tactic
macro_rules
  | `(tactic| nocompiler_entry) => `(tactic| nocompiler_entry [])
  | `(tactic| nocompiler_entry [$ts,*]) => `(tactic| (
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      (try simp (disch := nocompiler_decide_closed) only [nocompiler_state, NoCompiler.Reg.ra, NoCompiler.Reg.sp, $ts,*]) <;>
      first
        | rfl
        | assumption
        | decide
        | (unfold NoCompiler.aligned at *; bv_omega)
        | fail "nocompiler_entry"))

/-- The domain inclusion of a call: decided over the two range lists, or from a hypothesis; left otherwise. -/
macro "nocompiler_dom_sub" : tactic => `(tactic| first
  | exact NoCompiler.Dom.sub_of_ranges (by decide)
  | assumption
  | (intro x hx; first
      | (apply_assumption; exact NoCompiler.Dom.sub_of_ranges (by decide) x hx)
      | fail "nocompiler_dom_sub"))

syntax "nocompiler_call" term:max term:max (" via " term:max)? (" [" Lean.Parser.Tactic.simpArg,* "]")? : tactic
macro_rules
  | `(tactic| nocompiler_call $h $a) => `(tactic| nocompiler_call $h $a [])
  | `(tactic| nocompiler_call $h $a via $hi) => `(tactic| nocompiler_call $h $a via $hi [])
  | `(tactic| nocompiler_call $h $a [$ts,*]) => `(tactic| (
      refine NoCompiler.Linux.VerifiedProc.call $h $a (by nocompiler_entry [$ts,*]) ?pre ?dom ?kont
      case dom => (try nocompiler_dom_sub)))
  | `(tactic| nocompiler_call $h $a via $hi [$ts,*]) => `(tactic| (
      refine NoCompiler.Linux.VerifiedProc.call_of_implies $h $hi $a (by nocompiler_entry [$ts,*]) ?pre ?dom ?kont
      case dom => (try nocompiler_dom_sub)))

end NoCompiler.Linux
