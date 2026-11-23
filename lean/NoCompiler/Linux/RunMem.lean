import NoCompiler.Linux.Run
import NoCompiler.Libc.Mem

/-!
# Reads after writes in a run (round 7, C's row: frames)

A hand proof states, per pair of objects, that a read does not see a store to the other
(A's `field_after_field`, `field_after_slot16`, `slot16_after_field`, ...: each the same two lines over a
different pair of regions). Here once, for any pair:

* `read{LE,16,32,64}_writeLE_disj`: a read of `⟨q, k⟩` after a store to `⟨p, w⟩` sees the memory
  before the store, when the two regions are disjoint;
* `nocompiler_disj`: closes a goal `Region.Disjoint r r'` (and only such a goal) by `bv_omega`
  over the `Region.Disjoint` hypotheses in context, unfolded (a FILE and a stack frame, two
  buffers, ...);
* `nocompiler_runm [facts] using [lemmas]`: `nocompiler_run` whose steps also rewrite reads after
  writes by these lemmas, the disjointness by `nocompiler_disj`.
-/
namespace NoCompiler.Linux
open NoCompiler

theorem readLE_writeLE_disj {m : Word → Byte} {p q : Word} {v w k : Nat}
    (hd : Region.Disjoint ⟨p, w⟩ ⟨q, k⟩) : readLE (writeLE m p v w) q k = readLE m q k :=
  NoCompiler.Libc.readLE_writeLE_disj hd m p v w (by simp [Region.covers])

theorem read64_writeLE_disj {m : Word → Byte} {p q : Word} {v w : Nat}
    (hd : Region.Disjoint ⟨p, w⟩ ⟨q, 8⟩) : read64 (writeLE m p v w) q = read64 m q := by
  unfold read64; rw [readLE_writeLE_disj hd]

theorem read32_writeLE_disj {m : Word → Byte} {p q : Word} {v w : Nat}
    (hd : Region.Disjoint ⟨p, w⟩ ⟨q, 4⟩) : read32 (writeLE m p v w) q = read32 m q := by
  unfold read32; rw [readLE_writeLE_disj hd]

theorem read16_writeLE_disj {m : Word → Byte} {p q : Word} {v w : Nat}
    (hd : Region.Disjoint ⟨p, w⟩ ⟨q, 2⟩) : read16 (writeLE m p v w) q = read16 m q := by
  unfold read16; rw [readLE_writeLE_disj hd]

/-- A `Region.Disjoint` goal from the `Region.Disjoint` hypotheses, by `bv_omega`; fails on any other goal. -/
syntax "nocompiler_disj" : tactic
macro_rules
  | `(tactic| nocompiler_disj) => `(tactic| (
      show NoCompiler.Region.Disjoint _ _
      simp only [NoCompiler.Region.Disjoint] at *
      bv_omega))

/-- One process-level step whose simp passes also rewrite reads after disjoint writes. -/
syntax "nocompiler_pwstepm" (" [" Lean.Parser.Tactic.simpArg,* "]")? : tactic
macro_rules
  | `(tactic| nocompiler_pwstepm) => `(tactic| nocompiler_pwstepm [])
  | `(tactic| nocompiler_pwstepm [$ts,*]) => `(tactic| (
      refine NoCompiler.Linux.PReachK.exec_step ?hd ?hx ?h
      case hd => (try simp only [nocompiler_state, $ts,*]) <;> decide
      case hx => (try simp only [nocompiler_state, $ts,*]) <;> assumption
      case' h => (try simp only [nocompiler_state, nocompiler_image, $ts,*]); (try simp only [nocompiler_sem]); (try simp (disch := first | nocompiler_decide_closed | nocompiler_disj | fail "nocompiler_disj") only [nocompiler_state, nocompiler_image, true_and, Bool.false_eq_true, NoCompiler.Linux.read64_writeLE_disj, NoCompiler.Linux.read32_writeLE_disj, NoCompiler.Linux.read16_writeLE_disj, NoCompiler.Linux.readLE_writeLE_disj, $ts,*]); (try simp only [nocompiler_lit]); (try simp (disch := first | nocompiler_decide_closed | nocompiler_disj | fail "nocompiler_disj") only [nocompiler_state, nocompiler_image, true_and, Bool.false_eq_true, NoCompiler.Linux.read64_writeLE_disj, NoCompiler.Linux.read32_writeLE_disj, NoCompiler.Linux.read16_writeLE_disj, NoCompiler.Linux.readLE_writeLE_disj, $ts,*])
      rotate_left))

/-- `nocompiler_run` with `nocompiler_pwstepm` steps. -/
syntax "nocompiler_runm" (" [" Lean.Parser.Tactic.simpArg,* "]")? (" using " "[" term,* "]")? : tactic
macro_rules
  | `(tactic| nocompiler_runm) => `(tactic| nocompiler_runm [] using [])
  | `(tactic| nocompiler_runm [$ts,*]) => `(tactic| nocompiler_runm [$ts,*] using [])
  | `(tactic| nocompiler_runm using [$ls,*]) => `(tactic| nocompiler_runm [] using [$ls,*])
  | `(tactic| nocompiler_runm [$ts,*] using [$ls,*]) => `(tactic|
      repeat (first
        | (nocompiler_pwstepm [$ts,*]; try (with_reducible (show _ ∧ _); refine ⟨?_, ?_⟩; focus ((try simp (disch := nocompiler_decide_closed) only [$ts,*]); nocompiler_access using [$ls,*])))
        | simp (disch := first | nocompiler_decide_closed | nocompiler_disj | fail "nocompiler_disj") only [nocompiler_state, Bool.false_eq_true, ↓reduceIte, $ts,*]))

end NoCompiler.Linux
