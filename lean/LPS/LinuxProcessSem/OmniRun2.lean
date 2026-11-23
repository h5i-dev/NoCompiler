import LPS.LinuxProcessSem.OmniRun1

/-!
# LPS `theories/LinuxProcessSem/OmniRun.v` (f1006fe8), part 2: the coinductive judgments, the run level

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/LinuxProcessSem/OmniRun.v` at f1006fe8, from `coexec` to the end: the possibly-diverging
judgment `coexec` (no progress premise), its progress-carrying variant `coexec_progress`, the prefix-safety
judgment `cosafe`, the run-level judgments `omni_run`/`omni_corun`/`omni_cosafe`/`omni_may`, and the
compat lemmas `bh_*_iff` against the fields of `run`.

Rocq's `CoInductive` predicates are Lean `coinductive` predicates (Lean's greatest-fixed-point command:
the constructors are the Rocq constructors, `cases` destructs, and `X.coinduct` is the coinduction
principle; Rocq's `cofix` proofs become `X.coinduct` with an explicit invariant). Namespace and section
conventions as in OmniRun1.
-/

namespace LPS
namespace OmniRun
open RiscvSemantics

/-! ### Possibly-diverging omni-exec (coinductive), no progress premise -/

coinductive coexec (segs : List Segment) : config → post → Prop where
  | coexec_halt (c Q) : m_halted c.cfg_model ≠ none → Q [] (OHalt c) → coexec segs c Q
  | coexec_step (c Q) :
      m_halted c.cfg_model = none →
      (∀ evs, sstep segs c evs .SError → Q evs (OError c)) →
      (∀ evs c', sstep segs c evs (.SNext c') → coexec segs c' (fun tr o => Q (evs ++ tr) o)) →
      coexec segs c Q

theorem exec_coexec (segs : List Segment) : ∀ c Q, exec segs c Q → coexec segs c Q := by
  intro c Q h
  induction h with
  | exec_halt c Q hh hq => exact .coexec_halt segs _ _ hh hq
  | exec_step c Q hh _ herr _ ih => exact .coexec_step segs _ _ hh herr (fun evs c' hss => ih evs c' hss)

theorem coexec_conseq (segs : List Segment) :
    ∀ c (Q Q' : post), coexec segs c Q → (∀ tr o, Q tr o → Q' tr o) → coexec segs c Q' := by
  intro c Q Q' h himp
  refine coexec.coinduct segs (fun c Q' => ∃ Q, coexec segs c Q ∧ ∀ tr o, Q tr o → Q' tr o) ?_ c Q'
    ⟨Q, h, himp⟩
  rintro c Q' ⟨Q, h, himp⟩
  cases h with
  | coexec_halt _ _ hh hq => exact .inl ⟨hh, himp _ _ hq⟩
  | coexec_step _ _ hh herr hnext =>
    exact .inr ⟨hh, fun evs hss => himp _ _ (herr evs hss),
      fun evs c' hss => ⟨_, hnext evs c' hss, fun tr o => himp _ _⟩⟩

/-- The single-transition rule, as for `exec_step_only`. -/
theorem coexec_step_only (segs : List Segment) :
    ∀ c (Q : post) evs1 c1,
      sstep segs c evs1 (.SNext c1) →
      (∀ evs st, sstep segs c evs st → evs = evs1 ∧ st = .SNext c1) →
      coexec segs c1 (fun tr o => Q (evs1 ++ tr) o) →
      coexec segs c Q := by
  intro c Q evs1 c1 hss honly hco
  refine .coexec_step segs _ _ (sstep_from_running segs _ _ _ hss) ?_ ?_
  · intro evs herr
    exact nomatch (honly _ _ herr).2
  · intro evs c' hss'
    obtain ⟨rfl, he⟩ := honly _ _ hss'
    cases he
    exact hco

theorem coexec_star (segs : List Segment) :
    ∀ c (Q : post) tr c', coexec segs c Q → star segs c tr c' →
      coexec segs c' (fun tr' o => Q (tr ++ tr') o) := by
  intro c Q tr c' hex hstar
  induction hstar generalizing Q with
  | star_refl c => exact coexec_conseq segs _ _ _ hex (fun tr o h => by simpa using h)
  | star_step c1 evs c2 tr c3 hss _ ih =>
    cases hex with
    | coexec_halt _ _ hh _ => exact absurd (sstep_from_running segs _ _ _ hss) hh
    | coexec_step _ _ _ _ hnext =>
      exact coexec_conseq segs _ _ _ (ih _ (hnext evs c2 hss)) (fun tr' o h => by simpa using h)

/-- Soundness: every maximal execution that ends satisfies the postcondition. -/
theorem coexec_sound (segs : List Segment) :
    ∀ c tr o, mexec segs c tr o → ∀ Q, coexec segs c Q → Q tr o := by
  intro c tr o hm
  induction hm with
  | mexec_halt c hh =>
    intro Q hco
    cases hco with
    | coexec_halt _ _ _ hq => exact hq
    | coexec_step _ _ hh0 _ _ => exact absurd hh0 hh
  | mexec_error c evs hss =>
    intro Q hco
    cases hco with
    | coexec_halt _ _ hh0 _ => exact absurd (sstep_from_running segs _ _ _ hss) hh0
    | coexec_step _ _ _ herr _ => exact herr _ hss
  | mexec_next c evs c1 tr o hss _ ih =>
    intro Q hco
    cases hco with
    | coexec_halt _ _ hh0 _ => exact absurd (sstep_from_running segs _ _ _ hss) hh0
    | coexec_step _ _ _ _ hnext => exact ih _ (hnext _ _ hss)

/-- The silent reading of a stuck configuration: it satisfies every `coexec`. -/
theorem stuck_coexec_any (segs : List Segment) :
    ∀ c, m_halted c.cfg_model = none → (∀ evs st, ¬ sstep segs c evs st) → ∀ Q, coexec segs c Q :=
  fun _ hh hstuck _ =>
    .coexec_step segs _ _ hh (fun _ hss => (hstuck _ _ hss).elim) (fun _ _ hss => (hstuck _ _ hss).elim)

/-- Safety direction: `error_free` from the judgment ... -/
theorem coexec_no_error (segs : List Segment) : ∀ c, coexec segs c never_errors → ¬ reaches_error segs c := by
  rintro c hco ⟨tr, c2, evs, hstar, hss⟩
  exact coexec_sound segs _ _ _ (star_mexec segs _ _ _ _ _ hstar (.mexec_error _ _ hss)) _ hco trivial

/-- ... and the converse, unconditional because a stuck configuration is silent on both sides. -/
theorem no_error_coexec (segs : List Segment) : ∀ c, ¬ reaches_error segs c → coexec segs c never_errors := by
  intro c hno
  refine coexec.coinduct segs
    (fun c Q => ¬ reaches_error segs c ∧ ∀ tr o, ¬ is_error o → Q tr o) ?_ c never_errors
    ⟨hno, fun _ _ h => h⟩
  rintro c Q ⟨hno, hQ⟩
  cases hh : m_halted c.cfg_model with
  | some code => exact .inl ⟨by simp, hQ _ _ id⟩
  | none =>
    refine .inr ⟨rfl, ?_, ?_⟩
    · intro evs hss
      exact (hno ⟨[], c, evs, .star_refl _, hss⟩).elim
    · intro evs c' hss
      refine ⟨?_, fun tr o h => hQ _ _ h⟩
      rintro ⟨tr, c2, evs2, hstar, hss2⟩
      exact hno ⟨evs ++ tr, c2, evs2, .star_step _ _ _ _ _ hss hstar, hss2⟩

theorem never_errors_iff (segs : List Segment) : ∀ c, ¬ reaches_error segs c ↔ coexec segs c never_errors :=
  fun c => ⟨no_error_coexec segs c, coexec_no_error segs c⟩

/-- `Equivalence.modeled`, the same way. -/
theorem coexec_covered (segs : List Segment) : ∀ c, coexec segs c (covered segs) → ¬ reaches_unmodeled segs c := by
  rintro c hco ⟨tr, c', hstar, hun⟩
  obtain ⟨evs, hss⟩ := unmodeled_at_sstep_error segs _ hun
  exact coexec_sound segs _ _ _ (star_mexec segs _ _ _ _ _ hstar (.mexec_error _ _ hss)) _ hco hun

theorem no_unmodeled_coexec (segs : List Segment) :
    ∀ c, ¬ reaches_unmodeled segs c → coexec segs c (covered segs) := by
  intro c hno
  refine coexec.coinduct segs
    (fun c Q => ¬ reaches_unmodeled segs c ∧ ∀ tr o, covered segs tr o → Q tr o) ?_ c (covered segs)
    ⟨hno, fun _ _ h => h⟩
  rintro c Q ⟨hno, hQ⟩
  cases hh : m_halted c.cfg_model with
  | some code => exact .inl ⟨by simp, hQ _ _ trivial⟩
  | none =>
    refine .inr ⟨rfl, ?_, ?_⟩
    · intro evs _
      exact hQ _ _ (fun hun => hno ⟨[], c, .star_refl _, hun⟩)
    · intro evs c' hss
      refine ⟨?_, fun tr o h => hQ _ _ h⟩
      rintro ⟨tr, c2, hstar, hun⟩
      exact hno ⟨evs ++ tr, c2, .star_step _ _ _ _ _ hss hstar, hun⟩

theorem covered_iff (segs : List Segment) : ∀ c, ¬ reaches_unmodeled segs c ↔ coexec segs c (covered segs) :=
  fun c => ⟨no_unmodeled_coexec segs c, coexec_covered segs c⟩

/-! ### The progress-carrying alternative, kept for a local reversal -/

/-- `coexec` with the progress premise of `exec`: a stuck configuration REFUTES it. -/
coinductive coexec_progress (segs : List Segment) : config → post → Prop where
  | coexec_progress_halt (c Q) : m_halted c.cfg_model ≠ none → Q [] (OHalt c) → coexec_progress segs c Q
  | coexec_progress_step (c Q) :
      m_halted c.cfg_model = none →
      (∃ evs st, sstep segs c evs st) →
      (∀ evs, sstep segs c evs .SError → Q evs (OError c)) →
      (∀ evs c', sstep segs c evs (.SNext c') → coexec_progress segs c' (fun tr o => Q (evs ++ tr) o)) →
      coexec_progress segs c Q

theorem coexec_progress_implies (segs : List Segment) : ∀ c Q, coexec_progress segs c Q → coexec segs c Q := by
  intro c Q h
  refine coexec.coinduct segs (fun c Q => coexec_progress segs c Q) ?_ c Q h
  intro c Q h
  cases h with
  | coexec_progress_halt _ _ hh hq => exact .inl ⟨hh, hq⟩
  | coexec_progress_step _ _ hh _ herr hnext => exact .inr ⟨hh, herr, hnext⟩

/-- Where the two readings differ: a stuck configuration. -/
theorem stuck_not_coexec_progress (segs : List Segment) :
    ∀ c, m_halted c.cfg_model = none → (∀ evs st, ¬ sstep segs c evs st) → ∀ Q, ¬ coexec_progress segs c Q := by
  intro c hh hstuck Q hco
  cases hco with
  | coexec_progress_halt _ _ hh0 _ => exact hh0 hh
  | coexec_progress_step _ _ _ hprog _ _ =>
    obtain ⟨evs, st, hss⟩ := hprog
    exact hstuck _ _ hss

/-! ### Prefix safety (coinductive): what `obs_trace` is -/

/-- Every finite prefix of every execution satisfies `P`. -/
coinductive cosafe (segs : List Segment) : config → (List event → Prop) → Prop where
  | cosafe_intro (c P) :
      P [] → (∀ evs c', sstep segs c evs (.SNext c') → cosafe segs c' (fun tr => P (evs ++ tr))) →
      cosafe segs c P

theorem cosafe_star (segs : List Segment) : ∀ c P tr c', cosafe segs c P → star segs c tr c' → P tr := by
  intro c P tr c' hsafe hstar
  induction hstar generalizing P with
  | star_refl c => cases hsafe with | cosafe_intro _ _ hnil _ => exact hnil
  | star_step c1 evs c2 tr c3 hss _ ih =>
    cases hsafe with | cosafe_intro _ _ _ hnext => exact ih _ (hnext evs c2 hss)

theorem star_cosafe (segs : List Segment) : ∀ c P, (∀ tr c', star segs c tr c' → P tr) → cosafe segs c P := by
  intro c P hall
  refine cosafe.coinduct segs (fun c P => ∀ tr c', star segs c tr c' → P tr) ?_ c P hall
  intro c P hall
  exact ⟨hall [] c (.star_refl _), fun evs c' hss tr c'' hstar => hall (evs ++ tr) c'' (.star_step _ _ _ _ _ hss hstar)⟩

def prefix_closed (P : List event → Prop) : Prop := ∀ tr tr', P tr → is_prefix tr' tr → P tr'

theorem obs_trace_is_prefix_closed (segs : List Segment) : ∀ c, prefix_closed (obs_trace segs c) :=
  fun _ _ _ ht hp => obs_trace_prefix_closed segs _ _ _ ht hp

/-- `obs_trace`'s universal dual: on a prefix-closed `P`, "every observable trace satisfies `P`" is
    exactly `cosafe`. -/
theorem cosafe_obs_iff (segs : List Segment) :
    ∀ c P, prefix_closed P → (cosafe segs c P ↔ ∀ tr, obs_trace segs c tr → P tr) := by
  intro c P hpc
  constructor
  · rintro hsafe tr ⟨tr', c', hstar, hp⟩
    exact hpc _ _ (cosafe_star segs _ _ _ _ hsafe hstar) hp
  · intro hall
    exact star_cosafe segs _ _ (fun tr c' hstar => hall _ ⟨tr, c', hstar, is_prefix_refl _⟩)

/-- The refinement pair: each side's trace set is a prefix postcondition the other side satisfies. -/
theorem obs_equiv_iff_refinement :
    ∀ segs1 c1 segs2 c2,
      (∀ tr, obs_trace segs1 c1 tr ↔ obs_trace segs2 c2 tr) ↔
        (cosafe segs1 c1 (obs_trace segs2 c2) ∧ cosafe segs2 c2 (obs_trace segs1 c1)) := by
  intro segs1 c1 segs2 c2
  rw [cosafe_obs_iff segs1 c1 _ (obs_trace_is_prefix_closed segs2 c2),
    cosafe_obs_iff segs2 c2 _ (obs_trace_is_prefix_closed segs1 c1)]
  constructor
  · intro heq
    exact ⟨fun tr ht => (heq tr).1 ht, fun tr ht => (heq tr).2 ht⟩
  · rintro ⟨h12, h21⟩ tr
    exact ⟨h12 tr, h21 tr⟩

/-- Trace-set equality is "the two configurations satisfy the same prefix postconditions". -/
theorem obs_equiv_iff_cosafe :
    ∀ segs1 c1 segs2 c2,
      (∀ tr, obs_trace segs1 c1 tr ↔ obs_trace segs2 c2 tr) ↔
        (∀ P, prefix_closed P → (cosafe segs1 c1 P ↔ cosafe segs2 c2 P)) := by
  intro segs1 c1 segs2 c2
  constructor
  · intro heq P hpc
    rw [cosafe_obs_iff segs1 c1 P hpc, cosafe_obs_iff segs2 c2 P hpc]
    exact ⟨fun hall tr hobs => hall tr ((heq tr).2 hobs), fun hall tr hobs => hall tr ((heq tr).1 hobs)⟩
  · intro hall
    apply (obs_equiv_iff_refinement segs1 c1 segs2 c2).2
    constructor
    · apply (hall _ (obs_trace_is_prefix_closed segs2 c2)).2
      exact star_cosafe segs2 _ _ (fun tr c' hstar => ⟨tr, c', hstar, is_prefix_refl _⟩)
    · apply (hall _ (obs_trace_is_prefix_closed segs1 c1)).1
      exact star_cosafe segs1 _ _ (fun tr c' hstar => ⟨tr, c', hstar, is_prefix_refl _⟩)

/-! ### Run-level judgments: the three argument groups of `run` -/

def omni_run (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) (Q : post) : Prop :=
  match img, en with
  | ⟨segs, pc, ph⟩, ⟨sp, brk0, mbase, rnd⟩ => exec segs (init_config segs pc ph sp brk0 mbase rnd lim inp) Q

def omni_corun (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) (Q : post) : Prop :=
  match img, en with
  | ⟨segs, pc, ph⟩, ⟨sp, brk0, mbase, rnd⟩ => coexec segs (init_config segs pc ph sp brk0 mbase rnd lim inp) Q

def omni_cosafe (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) (P : List event → Prop) : Prop :=
  match img, en with
  | ⟨segs, pc, ph⟩, ⟨sp, brk0, mbase, rnd⟩ => cosafe segs (init_config segs pc ph sp brk0 mbase rnd lim inp) P

/-- SOME maximal execution satisfies `Q`: the existential twin. -/
def omni_may (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) (Q : post) : Prop :=
  match img, en with
  | ⟨segs, pc, ph⟩, ⟨sp, brk0, mbase, rnd⟩ =>
    ∃ tr o, mexec segs (init_config segs pc ph sp brk0 mbase rnd lim inp) tr o ∧ Q tr o

/-! ### Compat: the four fields of `run`, each unconditional -/

theorem bh_all_errors_iff : ∀ img lim en inp, (run img lim en inp).bh_all_errors ↔ omni_run img lim en inp errors
  | ⟨segs, _, _⟩, _, ⟨_, _, _, _⟩, _ => all_traces_error_iff segs _

theorem bh_errors_iff : ∀ img lim en inp, ¬ (run img lim en inp).bh_errors ↔ omni_corun img lim en inp never_errors
  | ⟨segs, _, _⟩, _, ⟨_, _, _, _⟩, _ => never_errors_iff segs _

theorem bh_errors_may_iff : ∀ img lim en inp, (run img lim en inp).bh_errors ↔ omni_may img lim en inp errors
  | ⟨segs, _, _⟩, _, ⟨_, _, _, _⟩, _ => reaches_error_iff_may segs _

theorem bh_unmodeled_iff :
    ∀ img lim en inp, ¬ (run img lim en inp).bh_unmodeled ↔ omni_corun img lim en inp (covered img.img_segments)
  | ⟨segs, _, _⟩, _, ⟨_, _, _, _⟩, _ => covered_iff segs _

theorem bh_unmodeled_may_iff :
    ∀ img lim en inp, (run img lim en inp).bh_unmodeled ↔ omni_may img lim en inp (uncovered img.img_segments)
  | ⟨segs, _, _⟩, _, ⟨_, _, _, _⟩, _ => reaches_unmodeled_iff_may segs _

/-- Trace-set equality of two runs is agreement on every prefix-closed postcondition. -/
theorem bh_traces_iff :
    ∀ img1 lim1 en1 img2 lim2 en2 inp,
      (∀ tr, (run img1 lim1 en1 inp).bh_traces tr ↔ (run img2 lim2 en2 inp).bh_traces tr) ↔
        (∀ P, prefix_closed P → (omni_cosafe img1 lim1 en1 inp P ↔ omni_cosafe img2 lim2 en2 inp P))
  | ⟨segs1, _, _⟩, _, ⟨_, _, _, _⟩, ⟨segs2, _, _⟩, _, ⟨_, _, _, _⟩, _ => obs_equiv_iff_cosafe segs1 _ segs2 _

end OmniRun
end LPS
