import LPS.EquivalenceDefinition.Equivalence
import LPS.LinuxProcessSem.OmniRun2

/-!
# LPS `theories/EquivalenceDefinition/OmniEquivalence.v` (f1006fe8): the theorem families through OmniRun

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/EquivalenceDefinition/OmniEquivalence.v` at f1006fe8: each statement family of
`Equivalence` and `MustExit` gets an `omni_*` twin built from the judgments of OmniRun, with the two
proved equivalent. Section `Spec`'s variables `source_image target_image` are the leading explicit
arguments of the definitions and lemmas that use them. Namespace `LPS.OmniRun`, as OmniRun.

Not ported:
- the module types `OMNI_SPEC`, `OMNI_SPEC_ERROR_FREE` and the functors `OmniOfSpec`, `SpecOfOmni`,
  `OmniOfSpecErrorFree`, `SpecErrorFreeOfOmni`: Lean has no module types, and `Equivalence.SPEC` is not
  ported either (Equivalence.lean); each functor is one direction of `strong_universal_iff` /
  `strong_universal_error_free_iff`, which are ported.
- the classifier compat lemmas, which need `Classifier.v` and `FinInput.v` (not ported): `agree_iff`,
  `good_input_iff`, `omni_decides`, `decides_iff`, `omni_decides_spec_iff`, `omni_classifier_total_T`,
  `classifier_total_iff`, `omni_decides_implies_total`, `omni_classifies_patch_diff_T`,
  `classifies_patch_diff_iff`, `omni_classifies_good_inputs_T`, `classifies_good_inputs_iff`. Of that
  section, `ex_and_iff`, `omni_agree` and `omni_good_input` (which mention no classifier name) are ported.
-/

namespace LPS
namespace OmniRun
open RiscvSemantics

/-! ### Compat: `must_exit_at` / `must_exit_with` -/

/-- Right to left, over a postcondition entailing `exits_with`. -/
theorem exec_exits_must_exit_at :
    ∀ segs code c (Q : post), exec segs c Q → (∀ tr o, Q tr o → exits_with code tr o) → must_exit_at segs code c := by
  intro segs code c Q h
  induction h with
  | exec_halt c Q _ hq =>
    intro himp
    obtain ⟨hex, hk⟩ := himp _ _ hq
    exact .must_exit_at_halted _ hex hk
  | exec_step c Q hh hprog herr _ ih =>
    intro himp
    exact .must_exit_at_running _ hh hprog (fun evs hss => himp _ _ (herr evs hss))
      (fun evs c' hss => ih evs c' hss (fun tr o hq => himp (evs ++ tr) o hq))

theorem must_exit_at_iff : ∀ segs code c, must_exit_at segs code c ↔ exec segs c (exits_with code) := by
  intro segs code c
  constructor
  · intro h
    induction h with
    | must_exit_at_halted c hh hk => exact .exec_halt _ _ (by simp [hh]) ⟨hh, hk⟩
    | must_exit_at_running c hh hprog hnoerr _ ih =>
      exact .exec_step _ _ hh hprog (fun evs hss => (hnoerr evs hss).elim) (fun evs c' hss => ih evs c' hss)
  · intro h
    exact exec_exits_must_exit_at _ _ _ _ h (fun _ _ h => h)

theorem must_exit_with_iff :
    ∀ code img lim en inp, must_exit_with code img lim en inp ↔ omni_run img lim en inp (exits_with code)
  | code, ⟨segs, _, _⟩, _, ⟨_, _, _, _⟩, _ => must_exit_at_iff segs code _

/-! ### Compat: the behaviour-level predicates of `Equivalence` -/

theorem error_free_iff :
    ∀ img lim en inp, error_free (run img lim en inp) ↔ omni_corun img lim en inp never_errors :=
  fun img lim en inp => bh_errors_iff img lim en inp

theorem modeled_iff :
    ∀ img lim en inp, modeled (run img lim en inp) ↔ omni_corun img lim en inp (covered img.img_segments) :=
  fun img lim en inp => bh_unmodeled_iff img lim en inp

/-- Trace equivalence of two runs is agreement on every prefix-closed omni postcondition. -/
def omni_trace_equiv (img1 : Image) (lim1 : Int) (en1 : ExecEntry) (img2 : Image) (lim2 : Int) (en2 : ExecEntry)
    (inp : ProcInput) : Prop :=
  ∀ P, prefix_closed P → (omni_cosafe img1 lim1 en1 inp P ↔ omni_cosafe img2 lim2 en2 inp P)

theorem trace_equiv_iff_omni :
    ∀ img1 lim1 en1 img2 lim2 en2 inp,
      trace_equiv (run img1 lim1 en1 inp).bh_traces (run img2 lim2 en2 inp).bh_traces ↔
        omni_trace_equiv img1 lim1 en1 img2 lim2 en2 inp :=
  fun img1 lim1 en1 img2 lim2 en2 inp => bh_traces_iff img1 lim1 en1 img2 lim2 en2 inp

/-- The introduction rule: each run's trace set is a prefix postcondition the other run satisfies. -/
theorem omni_trace_equiv_refinement :
    ∀ img1 lim1 en1 img2 lim2 en2 inp,
      omni_trace_equiv img1 lim1 en1 img2 lim2 en2 inp ↔
        (omni_cosafe img1 lim1 en1 inp (run img2 lim2 en2 inp).bh_traces ∧
          omni_cosafe img2 lim2 en2 inp (run img1 lim1 en1 inp).bh_traces)
  | ⟨segs1, _, _⟩, _, ⟨_, _, _, _⟩, ⟨segs2, _, _⟩, _, ⟨_, _, _, _⟩, _ => by
    unfold omni_trace_equiv
    constructor
    · intro h
      exact (obs_equiv_iff_refinement segs1 _ segs2 _).1 ((obs_equiv_iff_cosafe segs1 _ segs2 _).2 h)
    · intro h
      exact (obs_equiv_iff_cosafe segs1 _ segs2 _).1 ((obs_equiv_iff_refinement segs1 _ segs2 _).2 h)

/-- `Equivalence.equiv` on two runs: the escape, or trace agreement with an error-free target. -/
def omni_equiv (imgS : Image) (limS : Int) (enS : ExecEntry) (imgT : Image) (limT : Int) (enT : ExecEntry)
    (inp : ProcInput) : Prop :=
  omni_run imgS limS enS inp errors ∨
    (omni_trace_equiv imgS limS enS imgT limT enT inp ∧ omni_corun imgT limT enT inp never_errors)

theorem equiv_iff :
    ∀ imgS limS enS imgT limT enT inp,
      equiv (run imgS limS enS inp) (run imgT limT enT inp) ↔ omni_equiv imgS limS enS imgT limT enT inp := by
  intro imgS limS enS imgT limT enT inp
  unfold equiv omni_equiv
  rw [bh_all_errors_iff imgS limS enS inp, trace_equiv_iff_omni imgS limS enS imgT limT enT inp,
    bh_errors_iff imgT limT enT inp]

/-- The two policy consequences, in omni form. -/
theorem omni_all_errors_equiv_any :
    ∀ imgS limS enS imgT limT enT inp,
      omni_run imgS limS enS inp errors → omni_equiv imgS limS enS imgT limT enT inp :=
  fun _ _ _ _ _ _ _ h => .inl h

theorem omni_equiv_target_never_errors :
    ∀ imgS limS enS imgT limT enT inp,
      omni_equiv imgS limS enS imgT limT enT inp → ¬ omni_run imgS limS enS inp errors →
        omni_corun imgT limT enT inp never_errors
  | _, _, _, _, _, _, _, .inl hall, hs => (hs hall).elim
  | _, _, _, _, _, _, _, .inr ⟨_, hno⟩, _ => hno

/-! ### The theorem statements, parameterised over the two images (Rocq's Section `Spec`) -/

/-- `Equivalence.strong_equiv`, with `modeled` as `covered` BESIDE the equivalence. -/
def omni_strong_equiv (source_image target_image : Image) (en_source en_target : ExecEntry) (inp : ProcInput) :
    Prop :=
  omni_corun source_image source_alloc_limit en_source inp (covered source_image.img_segments) ∧
    omni_equiv source_image source_alloc_limit en_source target_image target_alloc_limit en_target inp

theorem strong_equiv_iff (source_image target_image : Image) :
    ∀ en_source en_target inp,
      strong_equiv source_image target_image en_source en_target inp ↔
        omni_strong_equiv source_image target_image en_source en_target inp := by
  intro en_source en_target inp
  unfold strong_equiv omni_strong_equiv
  rw [modeled_iff source_image source_alloc_limit en_source inp,
    equiv_iff source_image source_alloc_limit en_source target_image target_alloc_limit en_target inp]

def omni_strong_universal_T (source_image target_image : Image) : Prop :=
  ∀ en_source en_target inp,
    valid_entry source_image en_source inp → valid_entry target_image en_target inp → valid_input inp →
      omni_strong_equiv source_image target_image en_source en_target inp

theorem strong_universal_iff (source_image target_image : Image) :
    strong_universal_T source_image target_image ↔ omni_strong_universal_T source_image target_image := by
  unfold strong_universal_T omni_strong_universal_T
  constructor
  · intro h en_source en_target inp hs ht hi
    exact (strong_equiv_iff source_image target_image _ _ _).1 (h _ _ _ hs ht hi)
  · intro h en_source en_target inp hs ht hi
    exact (strong_equiv_iff source_image target_image _ _ _).2 (h _ _ _ hs ht hi)

/-- `Equivalence.strong_equiv_error_free`: both runs never error, and the trace sets agree. -/
def omni_strong_equiv_error_free (source_image target_image : Image) (en_source en_target : ExecEntry)
    (inp : ProcInput) : Prop :=
  omni_corun source_image source_alloc_limit en_source inp never_errors ∧
    omni_corun target_image target_alloc_limit en_target inp never_errors ∧
    omni_trace_equiv source_image source_alloc_limit en_source target_image target_alloc_limit en_target inp

theorem strong_equiv_error_free_iff (source_image target_image : Image) :
    ∀ en_source en_target inp,
      strong_equiv_error_free source_image target_image en_source en_target inp ↔
        omni_strong_equiv_error_free source_image target_image en_source en_target inp := by
  intro en_source en_target inp
  unfold strong_equiv_error_free omni_strong_equiv_error_free
  rw [error_free_iff source_image source_alloc_limit en_source inp,
    error_free_iff target_image target_alloc_limit en_target inp,
    trace_equiv_iff_omni source_image source_alloc_limit en_source target_image target_alloc_limit en_target inp]

def omni_strong_universal_error_free_T (source_image target_image : Image) : Prop :=
  ∀ en_source en_target inp,
    valid_entry source_image en_source inp → valid_entry target_image en_target inp → valid_input inp →
      omni_strong_equiv_error_free source_image target_image en_source en_target inp

theorem strong_universal_error_free_iff (source_image target_image : Image) :
    strong_universal_error_free_T source_image target_image ↔
      omni_strong_universal_error_free_T source_image target_image := by
  unfold strong_universal_error_free_T omni_strong_universal_error_free_T
  constructor
  · intro h en_source en_target inp hs ht hi
    exact (strong_equiv_error_free_iff source_image target_image _ _ _).1 (h _ _ _ hs ht hi)
  · intro h en_source en_target inp hs ht hi
    exact (strong_equiv_error_free_iff source_image target_image _ _ _).2 (h _ _ _ hs ht hi)

/-- The error-free shape is the stronger one, proved in omni terms. -/
theorem omni_strong_equiv_error_free_implies (source_image target_image : Image) :
    ∀ en_source en_target inp,
      omni_strong_equiv_error_free source_image target_image en_source en_target inp →
        omni_strong_equiv source_image target_image en_source en_target inp := by
  rintro en_source en_target inp ⟨hsrc, htgt, htr⟩
  refine ⟨?_, .inr ⟨htr, htgt⟩⟩
  obtain ⟨segs, pc, ph⟩ := source_image
  obtain ⟨sp, brk0, mbase, rnd⟩ := en_source
  exact coexec_conseq segs _ _ _ hsrc (never_errors_covered segs)

theorem omni_strong_universal_error_free_implies (source_image target_image : Image) :
    omni_strong_universal_error_free_T source_image target_image →
      omni_strong_universal_T source_image target_image :=
  fun h _ _ _ hs ht hi =>
    omni_strong_equiv_error_free_implies source_image target_image _ _ _ (h _ _ _ hs ht hi)

/-- Where the two shapes diverge: the escape is inconsistent with the error-free shape. -/
theorem omni_strong_equiv_error_free_no_all_errors_escape (source_image target_image : Image) :
    ∀ en_source en_target inp,
      omni_run source_image source_alloc_limit en_source inp errors →
        ¬ omni_strong_equiv_error_free source_image target_image en_source en_target inp := by
  rintro en_source en_target inp hall ⟨hsrc, _, _⟩
  obtain ⟨segs, pc, ph⟩ := source_image
  obtain ⟨sp, brk0, mbase, rnd⟩ := en_source
  obtain ⟨tr, o, hm, herr⟩ := exec_realizes segs _ _ hall
  exact coexec_sound segs _ _ _ hm _ hsrc herr

/-- One erroring maximal execution at one valid triple refutes the whole error-free universal statement. -/
theorem omni_strong_universal_error_free_refuted_by_source_error (source_image target_image : Image) :
    ∀ en_source en_target inp,
      valid_entry source_image en_source inp → valid_entry target_image en_target inp → valid_input inp →
        omni_may source_image source_alloc_limit en_source inp errors →
          ¬ omni_strong_universal_error_free_T source_image target_image := by
  intro en_source en_target inp hs ht hi hmay h
  obtain ⟨hsrc, _, _⟩ := h en_source en_target inp hs ht hi
  obtain ⟨segs, pc, ph⟩ := source_image
  obtain ⟨sp, brk0, mbase, rnd⟩ := en_source
  obtain ⟨tr, o, hm, herr⟩ := hmay
  exact coexec_sound segs _ _ _ hm _ hsrc herr

/-! ### The classifier section: the parts that mention no `Classifier`/`FinInput` name -/

theorem ex_and_iff :
    ∀ (A : Type) (V P P' : A → Prop), (∀ x, P x ↔ P' x) → ((∃ x, V x ∧ P x) ↔ (∃ x, V x ∧ P' x)) := by
  intro A V P P' h
  exact ⟨fun ⟨x, hv, hp⟩ => ⟨x, hv, (h x).1 hp⟩, fun ⟨x, hv, hp⟩ => ⟨x, hv, (h x).2 hp⟩⟩

/-- `Classifier.agree`'s omni form: trace agreement at every valid entry pair, and the three per-entry
    existential facts matched across the two images. -/
def omni_agree (X Y : Image) (lim : Int) (inp : ProcInput) : Prop :=
  (∀ enX enY, valid_entry X enX inp → valid_entry Y enY inp → omni_trace_equiv X lim enX Y lim enY inp) ∧
    ((∃ en, valid_entry X en inp ∧ omni_may X lim en inp errors) ↔
      (∃ en, valid_entry Y en inp ∧ omni_may Y lim en inp errors)) ∧
    ((∃ en, valid_entry X en inp ∧ omni_run X lim en inp errors) ↔
      (∃ en, valid_entry Y en inp ∧ omni_run Y lim en inp errors)) ∧
    ((∃ en, valid_entry X en inp ∧ omni_may X lim en inp (uncovered X.img_segments)) ↔
      (∃ en, valid_entry Y en inp ∧ omni_may Y lim en inp (uncovered Y.img_segments)))

/-- `Classifier.good_input`'s omni form. -/
def omni_good_input (O1 O2 : Image) (inp : ProcInput) : Prop :=
  ∀ en1 en2, valid_entry O1 en1 inp → valid_entry O2 en2 inp → omni_strong_equiv_error_free O1 O2 en1 en2 inp

end OmniRun
end LPS
