import LPS.LinuxProcessSem.Run3

/-!
# LPS `theories/LinuxProcessSem/OmniRun.v` (f1006fe8), part 1: outcomes, maximal executions, `exec`

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/OmniRun.v` at f1006fe8: omni-big-step judgments over `sstep`. This part:
the outcomes and the postconditions the statement families use, the maximal executions `mexec` (the
"may" side), and the terminating judgment `exec` (inductive). Part 2 (OmniRun2) has the coinductive
judgments `coexec`, `coexec_progress`, `cosafe`, the run-level judgments and the compat lemmas.

Rocq's `Section WithSegs` variable `segs` is the leading explicit argument of each definition and
lemma that uses it. Everything sits in namespace `LPS.OmniRun` (Rocq's module `OmniRun`), because
`outcome` and `exec` would otherwise clash with `LPS.outcome` (Monad.v) and `LPS.exec` (the RISC-V core).
The Run.v lemmas used here are in Run3.
-/

namespace LPS
namespace OmniRun
open RiscvSemantics

/-- How a maximal finite execution ends: halted, or erroring FROM the carried configuration. -/
inductive outcome where
  | OHalt (c : config)
  | OError (c : config)

export outcome (OHalt OError)

abbrev post := List event → outcome → Prop

def is_error (o : outcome) : Prop :=
  match o with
  | OHalt _ => False
  | OError _ => True

def errors : post := fun _ o => is_error o

def never_errors : post := fun _ o => ¬ is_error o

/-- `Equivalence.modeled`'s postcondition: an error is allowed, but not one taken from a
    configuration the model declines to interpret. -/
def covered (segs : List Segment) : post :=
  fun _ o => match o with
    | OHalt _ => True
    | OError c => ¬ unmodeled_at segs c

/-- Its existential dual, for `reaches_unmodeled`. -/
def uncovered (segs : List Segment) : post :=
  fun _ o => match o with
    | OHalt _ => False
    | OError c => unmodeled_at segs c

/-- `MustExit.must_exit_at`'s postcondition (a death by signal is not an exit). -/
def exits_with (code : word) : post :=
  fun _ o => match o with
    | OHalt c => m_halted c.cfg_model = some code ∧ m_killed c.cfg_model = none
    | OError _ => False

theorem never_errors_covered (segs : List Segment) : ∀ tr o, never_errors tr o → covered segs tr o
  | _, OHalt _, _ => trivial
  | _, OError _, h => fun _ => h trivial

theorem exits_with_never_errors : ∀ code tr o, exits_with code tr o → never_errors tr o
  | _, _, OHalt _, _ => fun h => h
  | _, _, OError _, h => h.elim

/-- Every `sstep` leaves a non-halted configuration. -/
theorem sstep_from_running (segs : List Segment) :
    ∀ c evs st, sstep segs c evs st → m_halted c.cfg_model = none := by
  intro c evs st h
  cases h <;> assumption

/-! ### Maximal executions: the "may" side -/

/-- One maximal finite execution: its trace and how it ended. -/
inductive mexec (segs : List Segment) : config → List event → outcome → Prop where
  | mexec_halt (c) : m_halted c.cfg_model ≠ none → mexec segs c [] (OHalt c)
  | mexec_error (c evs) : sstep segs c evs .SError → mexec segs c evs (OError c)
  | mexec_next (c evs c' tr o) :
      sstep segs c evs (.SNext c') → mexec segs c' tr o → mexec segs c (evs ++ tr) o

theorem star_mexec (segs : List Segment) :
    ∀ c tr c' tr' o, star segs c tr c' → mexec segs c' tr' o → mexec segs c (tr ++ tr') o := by
  intro c tr c' tr' o hstar hm
  induction hstar with
  | star_refl c => simpa using hm
  | star_step c1 evs c2 tr c3 hss _ ih =>
    rw [List.append_assoc]; exact .mexec_next _ _ _ _ _ hss (ih hm)

theorem mexec_halt_star (segs : List Segment) :
    ∀ c tr o, mexec segs c tr o →
      ∀ c', o = OHalt c' → star segs c tr c' ∧ m_halted c'.cfg_model ≠ none := by
  intro c tr o hm
  induction hm with
  | mexec_halt c hh => intro c' he; cases he; exact ⟨.star_refl _, hh⟩
  | mexec_error c evs _ => intro c' he; cases he
  | mexec_next c evs c1 tr o hss _ ih =>
    intro c' he
    obtain ⟨hstar, hh⟩ := ih c' he
    exact ⟨.star_step _ _ _ _ _ hss hstar, hh⟩

theorem mexec_error_star (segs : List Segment) :
    ∀ c tr o, mexec segs c tr o →
      ∀ c', o = OError c' → ∃ tr1 evs, tr = tr1 ++ evs ∧ star segs c tr1 c' ∧ sstep segs c' evs .SError := by
  intro c tr o hm
  induction hm with
  | mexec_halt c _ => intro c' he; cases he
  | mexec_error c evs hss => intro c' he; cases he; exact ⟨[], evs, rfl, .star_refl _, hss⟩
  | mexec_next c evs c1 tr o hss _ ih =>
    intro c' he
    obtain ⟨tr1, evs', rfl, hstar, hss'⟩ := ih c' he
    exact ⟨evs ++ tr1, evs', (List.append_assoc _ _ _).symm, .star_step _ _ _ _ _ hss hstar, hss'⟩

/-- `reaches_error` is "some maximal execution errors". -/
theorem reaches_error_iff_may (segs : List Segment) :
    ∀ c, reaches_error segs c ↔ ∃ tr o, mexec segs c tr o ∧ errors tr o := by
  intro c
  constructor
  · rintro ⟨tr, c2, evs, hstar, hss⟩
    exact ⟨tr ++ evs, OError c2, star_mexec segs _ _ _ _ _ hstar (.mexec_error _ _ hss), trivial⟩
  · rintro ⟨tr, o, hm, he⟩
    cases o with
    | OHalt c' => exact he.elim
    | OError c' =>
      obtain ⟨tr1, evs, _, hstar, hss⟩ := mexec_error_star segs _ _ _ hm c' rfl
      exact ⟨tr1, c', evs, hstar, hss⟩

/-- `reaches_unmodeled` is "some maximal execution errors from an uncovered configuration". -/
theorem reaches_unmodeled_iff_may (segs : List Segment) :
    ∀ c, reaches_unmodeled segs c ↔ ∃ tr o, mexec segs c tr o ∧ uncovered segs tr o := by
  intro c
  constructor
  · rintro ⟨tr, c', hstar, hun⟩
    obtain ⟨evs, hss⟩ := unmodeled_at_sstep_error segs _ hun
    exact ⟨tr ++ evs, OError c', star_mexec segs _ _ _ _ _ hstar (.mexec_error _ _ hss), hun⟩
  · rintro ⟨tr, o, hm, hun⟩
    cases o with
    | OHalt c' => exact hun.elim
    | OError c' =>
      obtain ⟨tr1, evs, _, hstar, _⟩ := mexec_error_star segs _ _ _ hm c' rfl
      exact ⟨tr1, c', hstar, hun⟩

/-! ### Terminating omni-exec (inductive) -/

inductive exec (segs : List Segment) : config → post → Prop where
  | exec_halt (c Q) : m_halted c.cfg_model ≠ none → Q [] (OHalt c) → exec segs c Q
  | exec_step (c Q) :
      m_halted c.cfg_model = none →
      (∃ evs st, sstep segs c evs st) →
      (∀ evs, sstep segs c evs .SError → Q evs (OError c)) →
      (∀ evs c', sstep segs c evs (.SNext c') → exec segs c' (fun tr o => Q (evs ++ tr) o)) →
      exec segs c Q

/-- Consequence: the postcondition may be weakened. -/
theorem exec_conseq (segs : List Segment) :
    ∀ c (Q Q' : post), exec segs c Q → (∀ tr o, Q tr o → Q' tr o) → exec segs c Q' := by
  intro c Q Q' h
  induction h generalizing Q' with
  | exec_halt c Q hh hq => intro himp; exact .exec_halt _ _ hh (himp _ _ hq)
  | exec_step c Q hh hprog herr _ ih =>
    intro himp
    exact .exec_step _ _ hh hprog (fun evs hss => himp _ _ (herr evs hss))
      (fun evs c' hss => ih evs c' hss _ (fun tr o => himp _ _))

/-- Halted configuration: the base case, as a lemma. -/
theorem exec_halted (segs : List Segment) :
    ∀ c (Q : post), m_halted c.cfg_model ≠ none → Q [] (OHalt c) → exec segs c Q :=
  fun c Q hh hq => .exec_halt c Q hh hq

/-- A configuration with exactly one transition. -/
theorem exec_step_only (segs : List Segment) :
    ∀ c (Q : post) evs1 c1,
      sstep segs c evs1 (.SNext c1) →
      (∀ evs st, sstep segs c evs st → evs = evs1 ∧ st = .SNext c1) →
      exec segs c1 (fun tr o => Q (evs1 ++ tr) o) →
      exec segs c Q := by
  intro c Q evs1 c1 hss honly hex
  refine .exec_step _ _ (sstep_from_running segs _ _ _ hss) ⟨evs1, _, hss⟩ ?_ ?_
  · intro evs herr
    exact nomatch (honly _ _ herr).2
  · intro evs c' hss'
    obtain ⟨rfl, he⟩ := honly _ _ hss'
    cases he
    exact hex

/-- Step closure: an omni judgment survives any `star` prefix, with the events already emitted
    prepended in the postcondition. -/
theorem exec_star (segs : List Segment) :
    ∀ c (Q : post) tr c', exec segs c Q → star segs c tr c' → exec segs c' (fun tr' o => Q (tr ++ tr') o) := by
  intro c Q tr c' hex hstar
  induction hstar generalizing Q with
  | star_refl c => exact exec_conseq segs _ _ _ hex (fun tr o h => by simpa using h)
  | star_step c1 evs c2 tr c3 hss _ ih =>
    cases hex with
    | exec_halt _ _ hh _ => exact absurd (sstep_from_running segs _ _ _ hss) hh
    | exec_step _ _ _ _ _ hnext =>
      exact exec_conseq segs _ _ _ (ih _ (hnext evs c2 hss)) (fun tr' o h => by simpa using h)

/-- Soundness: every maximal execution of an `exec` judgment satisfies its postcondition ... -/
theorem exec_sound (segs : List Segment) :
    ∀ c (Q : post), exec segs c Q → ∀ tr o, mexec segs c tr o → Q tr o := by
  intro c Q h
  induction h with
  | exec_halt c Q hh hq =>
    intro tr o hm
    cases hm with
    | mexec_halt => exact hq
    | mexec_error _ _ hss => exact absurd (sstep_from_running segs _ _ _ hss) hh
    | mexec_next _ _ _ _ _ hss _ => exact absurd (sstep_from_running segs _ _ _ hss) hh
  | exec_step c Q hh _ herr _ ih =>
    intro tr o hm
    cases hm with
    | mexec_halt _ hh0 => exact absurd hh hh0
    | mexec_error _ _ hss => exact herr _ hss
    | mexec_next _ _ _ _ _ hss hm' => exact ih _ _ hss _ _ hm'

/-- ... and at least one maximal execution exists: the progress premise is what keeps `exec` from
    holding vacuously. -/
theorem exec_realizes (segs : List Segment) :
    ∀ c (Q : post), exec segs c Q → ∃ tr o, mexec segs c tr o ∧ Q tr o := by
  intro c Q h
  induction h with
  | exec_halt c Q hh hq => exact ⟨[], OHalt c, .mexec_halt _ hh, hq⟩
  | exec_step c Q _ hprog herr _ ih =>
    obtain ⟨evs, st, hss⟩ := hprog
    cases st with
    | SNext c' =>
      obtain ⟨tr, o, hm, hq⟩ := ih _ _ hss
      exact ⟨evs ++ tr, o, .mexec_next _ _ _ _ _ hss hm, hq⟩
    | SError => exact ⟨evs, OError c, .mexec_error _ _ hss, herr _ hss⟩

/-- A stuck non-halted configuration satisfies no `exec`, whatever the postcondition. -/
theorem stuck_no_exec (segs : List Segment) :
    ∀ c, m_halted c.cfg_model = none → (∀ evs st, ¬ sstep segs c evs st) → ∀ Q, ¬ exec segs c Q := by
  intro c hh hstuck Q hex
  cases hex with
  | exec_halt _ _ hh0 _ => exact hh0 hh
  | exec_step _ _ _ hprog _ _ =>
    obtain ⟨evs, st, hss⟩ := hprog
    exact hstuck _ _ hss

/-- The omni reading of `all_traces_error`, right to left over a postcondition entailing an error. -/
theorem exec_errors_all_traces_error (segs : List Segment) :
    ∀ c (Q : post), exec segs c Q → (∀ tr o, Q tr o → is_error o) → all_traces_error segs c := by
  intro c Q h
  induction h with
  | exec_halt c Q _ hq => intro himp; exact (himp _ _ hq).elim
  | exec_step c Q _ hprog _ _ ih =>
    intro himp
    exact .all_traces_error_intro _ hprog (fun evs c' hss => ih evs c' hss (fun tr o hq => himp (evs ++ tr) o hq))

theorem all_traces_error_iff (segs : List Segment) : ∀ c, all_traces_error segs c ↔ exec segs c errors := by
  intro c
  constructor
  · intro h
    induction h with
    | all_traces_error_intro c hprog _ ih =>
      obtain ⟨evs, st, hss⟩ := hprog
      exact .exec_step _ _ (sstep_from_running segs _ _ _ hss) ⟨evs, st, hss⟩ (fun _ _ => trivial)
        (fun evs' c' hss' => ih evs' c' hss')
  · intro h
    exact exec_errors_all_traces_error segs _ _ h (fun _ _ h => h)

/-- No maximal execution errors: the `OError` outcome is refuted. -/
theorem exec_no_error (segs : List Segment) : ∀ c, exec segs c never_errors → ¬ reaches_error segs c := by
  rintro c hex ⟨tr, c2, evs, hstar, hss⟩
  exact exec_sound segs _ _ hex _ _ (star_mexec segs _ _ _ _ _ hstar (.mexec_error _ _ hss)) trivial

/-- An exact trace postcondition characterises the whole trace set. -/
theorem exec_obs_iff (segs : List Segment) :
    ∀ c (full : List event), exec segs c (fun tr o => tr = full ∧ ¬ is_error o) →
      ∀ tr, obs_trace segs c tr ↔ is_prefix tr full := by
  intro c full hex tr
  constructor
  · rintro ⟨tr', c', hstar, hp⟩
    obtain ⟨tr'', o, _, heq, _⟩ := exec_realizes segs _ _ (exec_star segs _ _ _ _ hex hstar)
    rw [← heq]
    exact is_prefix_trans _ _ _ hp (is_prefix_app _ _)
  · intro hp
    obtain ⟨tr', o, hm, heq, hno⟩ := exec_realizes segs _ _ hex
    cases o with
    | OError c' => exact (hno trivial).elim
    | OHalt c' =>
      subst heq
      obtain ⟨hstar, _⟩ := mexec_halt_star segs _ _ _ hm c' rfl
      exact ⟨tr', c', hstar, hp⟩

end OmniRun
end LPS
