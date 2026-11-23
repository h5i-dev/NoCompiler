import NoCompiler.Linux.ProcSpec

/-!
# Libc library: behaviour shapes (port of LPS `theories/Common/ShapeAlg.v`)

Ported from LPS (rocq-linux-process-semantics, MIT licence, commit d3f3a701),
`theories/Common/ShapeAlg.v` lines 127-200 (the trace-set combinators `TSet`, `t_nil`, `t_emit`,
`t_alt`, `t_alt2`, `t_exit`) and 371-537 (`realizes` and its composition), restated for our semantics.

LPS: MIT License, Copyright (c) 2026 Theorem Labs, PBC (prior-art/lps/LICENSE): "Permission is hereby
granted, free of charge, to any person obtaining a copy of this software ... The above copyright notice
and this permission notice shall be included in all copies or substantial portions of the Software."

What changed in the port, and why:
* LPS's shapes denote PREFIX-CLOSED trace sets compared by an observational equivalence over a star-run
  semantics (`obs_iff`, `strong_equiv`, the omni variants), so that non-terminating behaviours are
  ordinary inhabitants. Our statements are total-correctness `PReachK` claims (every run, whatever the
  kernel chooses, reaches the end condition; Linux/ProcSpec.lean), so a shape here is a set of the
  events a run adds between two states, and `Phase` is LPS's `realizes` with an end condition `Q`
  on the state reached. Prefix closure, `obs_iff` and the omni layer are not ported: they say nothing
  more about a run that `PReachK` already forces to end.
* LPS's `node_ok` (one syscall node, an index type of its resolutions) is not needed as a separate
  notion: a node is any `Phase` lemma, e.g. a syscall's `_cases` lemma (Linux/SysSteps.lean) turned
  into one step.
-/

namespace NoCompiler.Libc
open NoCompiler NoCompiler.Linux

/-- A behaviour shape: the events a run may add (LPS `TSet`, ShapeAlg.v:127). -/
def TSet := List Event → Prop

/-- Two shapes with the same traces (LPS `t_eq`, ShapeAlg.v:129). -/
def t_eq (T T' : TSet) : Prop := ∀ tr, T tr ↔ T' tr

/-- No event (LPS `t_nil`, ShapeAlg.v:137). -/
def t_nil : TSet := fun tr => tr = []

/-- The events `evs`, then `T` (LPS `t_emit`, ShapeAlg.v:142). -/
def t_emit (evs : List Event) (T : TSet) : TSet := fun tr => ∃ tr', tr = evs ++ tr' ∧ T tr'

/-- Some `f i` (LPS `t_alt`, ShapeAlg.v:146): the kernel's choice, e.g. how many bytes a read returns. -/
def t_alt {I : Type} (f : I → TSet) : TSet := fun tr => ∃ i, f i tr

/-- `A` or `B` (LPS `t_alt2`, ShapeAlg.v:149). -/
def t_alt2 (A B : TSet) : TSet := fun tr => A tr ∨ B tr

/-- The exit event with status `code` (LPS `t_exit`, ShapeAlg.v:152, without its file-system argument:
    our exit event carries no file state). -/
def t_exit (code : Word) : TSet := fun tr => tr = [.exit code]

/-- `T`, then `U` (sequencing; LPS gets it by nesting `t_emit` under a continuation). -/
def t_seq (T U : TSet) : TSet := fun tr => ∃ a b, tr = a ++ b ∧ T a ∧ U b

/-- From `y`, every run reaches a state `y'` satisfying `Q`, having added to the trace events in `T`
    (LPS `realizes c T`, ShapeAlg.v:377, with an end condition on the state reached). -/
def Phase (c : Code) (D : Dom) (T : TSet) (Q : State × Kern → Prop) (y : State × Kern) : Prop :=
  PReachK c D (fun y' => (∃ evs, y'.1.trace = y.1.trace ++ evs ∧ T evs) ∧ Q y') y

theorem t_seq_nil_left {T : TSet} {tr : List Event} (h : T tr) : t_seq t_nil T tr := ⟨[], tr, rfl, rfl, h⟩

theorem t_seq_assoc {T U V : TSet} {tr : List Event} (h : t_seq (t_seq T U) V tr) : t_seq T (t_seq U V) tr := by
  obtain ⟨_, c, rfl, ⟨a, b, rfl, ha, hb⟩, hc⟩ := h
  exact ⟨a, b ++ c, by simp, ha, b, c, rfl, hb, hc⟩

namespace Phase
variable {c : Code} {D : Dom}

/-- Nothing to run (LPS `realizes` of `t_nil`). -/
theorem done {Q : State × Kern → Prop} {y : State × Kern} (h : Q y) : Phase c D t_nil Q y :=
  PReachK.done ⟨⟨[], by simp, rfl⟩, h⟩

/-- Weaker shape, weaker end. -/
theorem mono {T T' : TSet} {Q Q' : State × Kern → Prop} {y : State × Kern}
    (hT : ∀ tr, T tr → T' tr) (hQ : ∀ y, Q y → Q' y) (h : Phase c D T Q y) : Phase c D T' Q' y := by
  refine PReachK.bind (fun _ h => h) (fun y' ⟨⟨evs, he, ht⟩, hq⟩ => PReachK.done ⟨⟨evs, he, hT _ ht⟩, hQ _ hq⟩) h

/-- Composition (LPS: the continuation of a node is again `realizes`): a phase, then from every state
    it ends in a second one; the events add up. -/
theorem seq {T U : TSet} {Q R : State × Kern → Prop} {y : State × Kern}
    (h : Phase c D T Q y) (k : ∀ y', Q y' → Phase c D U R y') : Phase c D (t_seq T U) R y := by
  refine PReachK.bind (fun _ h => h) (fun y' ⟨⟨evs, he, ht⟩, hq⟩ => ?_) h
  refine PReachK.bind (fun _ h => h) (fun y'' ⟨⟨evs', he', hu⟩, hr⟩ => PReachK.done ⟨⟨evs ++ evs', ?_, evs, evs', rfl, ht, hu⟩, hr⟩)
    (k y' hq)
  rw [he', he, List.append_assoc]

/-- A choice: the end condition says which branch (LPS `t_alt`). -/
theorem alt {I : Type} {f : I → TSet} {Q : State × Kern → Prop} {y : State × Kern}
    (h : PReachK c D (fun y' => ∃ i, (∃ evs, y'.1.trace = y.1.trace ++ evs ∧ f i evs) ∧ Q y') y) :
    Phase c D (t_alt f) Q y :=
  PReachK.bind (fun _ h => h) (fun _ ⟨i, ⟨evs, he, hf⟩, hq⟩ => PReachK.done ⟨⟨evs, he, i, hf⟩, hq⟩) h

end Phase

/-- The bytes a list of events writes to `fd`. -/
def fdOut (fd : Word) (evs : List Event) : List Byte :=
  evs.flatMap fun | .write f bs => if f = fd then bs else [] | _ => []

@[simp] theorem fdOut_nil (fd : Word) : fdOut fd [] = [] := rfl
@[simp] theorem fdOut_append (fd : Word) (a b : List Event) : fdOut fd (a ++ b) = fdOut fd a ++ fdOut fd b := by
  simp [fdOut]

/-- The whole-process form: from a shape ending in `exit 0` whose writes to `fd` are `out`, the `PReach` claim
    (events after the start, the exit event last, the bytes written to `fd` are `out`). -/
theorem Phase.toExit {c : Code} {D : Dom} {T : TSet} {fd : Word} {out : List Byte} {y : State × Kern}
    (hy : y.1.trace = []) (hT : ∀ tr, T tr → fdOut fd tr = out)
    (h : Phase c D (t_seq T (t_exit 0)) (fun y => y.1.exit = some 0) y) :
    PReach c D (fun t => ∃ evs, t.trace = evs ++ [.exit 0] ∧ t.exit = some 0 ∧ fdOut fd evs = out) y := by
  refine PReachK.toPReach (Q := fun y' => (∃ evs, y'.1.trace = y.1.trace ++ evs ∧ _) ∧ _) ?_ h
  rintro y' ⟨⟨_, he, a, b, rfl, ha, rfl⟩, hx⟩
  exact ⟨a, by rw [he, hy]; rfl, hx, hT a ha⟩

end NoCompiler.Libc
