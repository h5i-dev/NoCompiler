import LPS.EquivalenceDefinition.MustExit

/-!
# LPS `theories/EquivalenceDefinition/Equivalence.v` (f1006fe8): the statement shapes

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/EquivalenceDefinition/Equivalence.v` at f1006fe8 (TRUST BOUNDARY there): all of its
Definitions. Its `Module Type SPEC*` interfaces (a `Parameter` stating one shape for two `MemImage`s) are
not ported: in Lean a statement is the shape applied to two images, as ovp's Statements.v already writes
it. The `strong_*` family (from `strong_equiv` to `strong_universal_error_free_T_scfg_budgets_either`) was
translated by a script (session scratchpad rocq2lean.py) from the Rocq sentences: `forall`/`->`/`/\`/`\/`/
`~` to `∀`/`→`/`∧`/`∨`/`¬`, each Section's Variables turned into the leading arguments of the definitions
that use them (directly or through a section constant), in declaration order, as Rocq's section closing
does, and inserted at those constants' call sites inside the section. The rest by hand.
-/

namespace LPS
open RiscvSemantics

def trace_equiv (T1 T2 : List event → Prop) : Prop := ∀ tr, T1 tr ↔ T2 tr
def equiv (source target : behavior) : Prop :=
  source.bh_all_errors ∨ (trace_equiv source.bh_traces target.bh_traces ∧ ¬ target.bh_errors)
def modeled (b : behavior) : Prop := ¬ b.bh_unmodeled
def error_free (b : behavior) : Prop := ¬ b.bh_errors
def dies_by_signal (b : behavior) : Prop := ∃ tr sig fs, b.bh_traces tr ∧ event.KillEv sig fs ∈ tr
def error_free_unkilled (b : behavior) : Prop := error_free b ∧ ¬ dies_by_signal b
def quiet_behavior : behavior :=
  { bh_traces := fun tr => tr = [], bh_errors := False, bh_all_errors := False, bh_unmodeled := False }
def crashing_behavior : behavior :=
  { bh_traces := fun tr => tr = [], bh_errors := True, bh_all_errors := True, bh_unmodeled := False }
def basic_argv : List (List byte) := [[]]

def image_entry_fetchable (segs : List Segment) (pc : Nat) : Bool :=
  let addr := Z_to_bv 64 (pc : Int)
  match fetch_word segs addr with
  | some _ => true
  | none =>
    match fetch_word_wx segs addr with
    | some _ => true
    | none =>
      match fetch_tail_any segs (fun _ => none) addr with
      | some _ => true
      | none => false

def image_phdrs_readable (segs : List Segment) (ph : PhdrInfo) : Bool :=
  decide (0 < ph.ph_num) && decide (0 < ph.ph_ent) &&
    match memory_read segs (Z_to_bv 64 (ph.ph_addr : Int)) (ph.ph_num * ph.ph_ent) with
    | some _ => true
    | none => false

def image_brk_witness (segs : List Segment) : Int :=
  page_size * Z.div (reserved_top (segments_reserved segs) + (page_size - 1)) page_size

def image_brk_satisfiable (segs : List Segment) : Bool := decide (image_brk_witness segs < 2 ^ 64)

-- Definitions generated from Equivalence.v's Sections Spec .. SpecBudgetsScfg:

def strong_equiv (source_image : Image) (target_image : Image) (en_source en_target : ExecEntry) (inp : ProcInput) : Prop :=
  modeled (run source_image source_alloc_limit en_source inp) ∧ equiv (run source_image source_alloc_limit en_source inp) (run target_image target_alloc_limit en_target inp)

def strong_universal_T (source_image : Image) (target_image : Image) : Prop :=
  ∀ en_source en_target inp, valid_entry source_image en_source inp → valid_entry target_image en_target inp → valid_input inp → (strong_equiv source_image target_image) en_source en_target inp

def strong_equiv_error_free (source_image : Image) (target_image : Image) (en_source en_target : ExecEntry) (inp : ProcInput) : Prop :=
  error_free (run source_image source_alloc_limit en_source inp) ∧ error_free (run target_image target_alloc_limit en_target inp) ∧ trace_equiv (behavior.bh_traces (run source_image source_alloc_limit en_source inp)) (behavior.bh_traces (run target_image target_alloc_limit en_target inp))

def strong_universal_error_free_T (source_image : Image) (target_image : Image) : Prop :=
  ∀ en_source en_target inp, valid_entry source_image en_source inp → valid_entry target_image en_target inp → valid_input inp → (strong_equiv_error_free source_image target_image) en_source en_target inp

def strong_universal_T_abort (source_image : Image) (target_image : Image) : Prop :=
  ∀ en_source en_target inp, valid_entry source_image en_source inp → valid_entry target_image en_target inp → valid_input_abort inp → (strong_equiv source_image target_image) en_source en_target inp

def strong_universal_T_either (source_image : Image) (target_image : Image) : Prop :=
  ∀ en_source en_target inp, valid_entry source_image en_source inp → valid_entry target_image en_target inp → valid_input_either inp → (strong_equiv source_image target_image) en_source en_target inp

def strong_equiv_error_free_abort (source_image : Image) (target_image : Image) (en_source en_target : ExecEntry) (inp : ProcInput) : Prop :=
  error_free_unkilled (run source_image source_alloc_limit en_source inp) ∧ error_free_unkilled (run target_image target_alloc_limit en_target inp) ∧ trace_equiv (behavior.bh_traces (run source_image source_alloc_limit en_source inp)) (behavior.bh_traces (run target_image target_alloc_limit en_target inp))

def strong_universal_error_free_T_abort (source_image : Image) (target_image : Image) : Prop :=
  ∀ en_source en_target inp, valid_entry source_image en_source inp → valid_entry target_image en_target inp → valid_input_abort inp → (strong_equiv_error_free_abort source_image target_image) en_source en_target inp

def strong_universal_error_free_T_either (source_image : Image) (target_image : Image) : Prop :=
  (strong_universal_error_free_T source_image target_image) ∧ (strong_universal_error_free_T_abort source_image target_image)

def strong_equiv_va (source_image : Image) (target_image : Image) (en_source en_target : ExecEntry) (inp : ProcInput) : Prop :=
  inp.in_va_size = .Sv48 ∧ strong_equiv source_image target_image en_source en_target inp

def strong_universal_T_sv39 (source_image : Image) (target_image : Image) : Prop :=
  ∀ en_source en_target inp, valid_entry source_image en_source inp → valid_entry target_image en_target inp → valid_input_sv39 inp → (strong_equiv_va source_image target_image) en_source en_target inp

def strong_universal_T_sv57 (source_image : Image) (target_image : Image) : Prop :=
  ∀ en_source en_target inp, valid_entry source_image en_source inp → valid_entry target_image en_target inp → valid_input_sv57 inp → (strong_equiv_va source_image target_image) en_source en_target inp

def strong_universal_T_va_any (source_image : Image) (target_image : Image) : Prop :=
  ∀ en_source en_target inp, valid_entry source_image en_source inp → valid_entry target_image en_target inp → valid_input_va_any inp → (strong_equiv_va source_image target_image) en_source en_target inp

def strong_universal_T_hwcap_rv64gc (source_image : Image) (target_image : Image) : Prop :=
  ∀ en_source en_target inp, valid_entry source_image en_source inp → valid_entry target_image en_target inp → valid_input_hwcap_rv64gc inp → strong_equiv source_image target_image en_source en_target inp

def strong_universal_T_hwcap_rv64gcv (source_image : Image) (target_image : Image) : Prop :=
  ∀ en_source en_target inp, valid_entry source_image en_source inp → valid_entry target_image en_target inp → valid_input_hwcap_rv64gcv inp → strong_equiv source_image target_image en_source en_target inp

def strong_universal_error_free_T_hwcap_rv64gc (source_image : Image) (target_image : Image) : Prop :=
  ∀ en_source en_target inp, valid_entry source_image en_source inp → valid_entry target_image en_target inp → valid_input_hwcap_rv64gc inp → strong_equiv_error_free source_image target_image en_source en_target inp

def strong_universal_error_free_T_hwcap_rv64gcv (source_image : Image) (target_image : Image) : Prop :=
  ∀ en_source en_target inp, valid_entry source_image en_source inp → valid_entry target_image en_target inp → valid_input_hwcap_rv64gcv inp → strong_equiv_error_free source_image target_image en_source en_target inp

def strong_equiv_scfg (cfg : SpuriousCfg) (source_image : Image) (target_image : Image) (en_source en_target : ExecEntry) (inp : ProcInput) : Prop :=
  modeled (run_scfg cfg source_image source_alloc_limit en_source inp) ∧ equiv (run_scfg cfg source_image source_alloc_limit en_source inp) (run_scfg cfg target_image target_alloc_limit en_target inp)

def strong_universal_T_scfg (cfg : SpuriousCfg) (source_image : Image) (target_image : Image) : Prop :=
  ∀ en_source en_target inp, valid_entry source_image en_source inp → valid_entry target_image en_target inp → valid_input inp → (strong_equiv_scfg cfg source_image target_image) en_source en_target inp

def strong_equiv_error_free_scfg (cfg : SpuriousCfg) (source_image : Image) (target_image : Image) (en_source en_target : ExecEntry) (inp : ProcInput) : Prop :=
  error_free (run_scfg cfg source_image source_alloc_limit en_source inp) ∧ error_free (run_scfg cfg target_image target_alloc_limit en_target inp) ∧ trace_equiv (behavior.bh_traces (run_scfg cfg source_image source_alloc_limit en_source inp)) (behavior.bh_traces (run_scfg cfg target_image target_alloc_limit en_target inp))

def strong_universal_error_free_T_scfg (cfg : SpuriousCfg) (source_image : Image) (target_image : Image) : Prop :=
  ∀ en_source en_target inp, valid_entry source_image en_source inp → valid_entry target_image en_target inp → valid_input inp → (strong_equiv_error_free_scfg cfg source_image target_image) en_source en_target inp

def strong_universal_T_scfg_abort (cfg : SpuriousCfg) (source_image : Image) (target_image : Image) : Prop :=
  ∀ en_source en_target inp, valid_entry source_image en_source inp → valid_entry target_image en_target inp → valid_input_abort inp → (strong_equiv_scfg cfg source_image target_image) en_source en_target inp

def strong_universal_T_scfg_either (cfg : SpuriousCfg) (source_image : Image) (target_image : Image) : Prop :=
  ∀ en_source en_target inp, valid_entry source_image en_source inp → valid_entry target_image en_target inp → valid_input_either inp → (strong_equiv_scfg cfg source_image target_image) en_source en_target inp

def strong_equiv_error_free_scfg_abort (cfg : SpuriousCfg) (source_image : Image) (target_image : Image) (en_source en_target : ExecEntry) (inp : ProcInput) : Prop :=
  error_free_unkilled (run_scfg cfg source_image source_alloc_limit en_source inp) ∧ error_free_unkilled (run_scfg cfg target_image target_alloc_limit en_target inp) ∧ trace_equiv (behavior.bh_traces (run_scfg cfg source_image source_alloc_limit en_source inp)) (behavior.bh_traces (run_scfg cfg target_image target_alloc_limit en_target inp))

def strong_universal_error_free_T_scfg_abort (cfg : SpuriousCfg) (source_image : Image) (target_image : Image) : Prop :=
  ∀ en_source en_target inp, valid_entry source_image en_source inp → valid_entry target_image en_target inp → valid_input_abort inp → (strong_equiv_error_free_scfg_abort cfg source_image target_image) en_source en_target inp

def strong_universal_error_free_T_scfg_either (cfg : SpuriousCfg) (source_image : Image) (target_image : Image) : Prop :=
  (strong_universal_error_free_T_scfg cfg source_image target_image) ∧ (strong_universal_error_free_T_scfg_abort cfg source_image target_image)

def strong_universal_T_cfg (alloc_may_fail : Bool) (s t : Image) : Prop :=
  strong_universal_T_scfg (alloc_only_cfg alloc_may_fail) s t

def strong_universal_error_free_T_cfg (alloc_may_fail : Bool) (s t : Image) : Prop :=
  strong_universal_error_free_T_scfg (alloc_only_cfg alloc_may_fail) s t

def source_within_budget (lim_source : Int) (source_image : Image) (en_source : ExecEntry) (inp : ProcInput) : Prop :=
  ¬ run_budget_refused source_image lim_source en_source inp

def strong_equiv_budgets (lim_source : Int) (lim_target : Int) (source_image : Image) (target_image : Image) (en_source en_target : ExecEntry) (inp : ProcInput) : Prop :=
  modeled (run source_image lim_source en_source inp) ∧ equiv (run source_image lim_source en_source inp) (run target_image lim_target en_target inp)

def strong_equiv_error_free_budgets (lim_source : Int) (lim_target : Int) (source_image : Image) (target_image : Image) (en_source en_target : ExecEntry) (inp : ProcInput) : Prop :=
  error_free (run source_image lim_source en_source inp) ∧ error_free (run target_image lim_target en_target inp) ∧ trace_equiv (behavior.bh_traces (run source_image lim_source en_source inp)) (behavior.bh_traces (run target_image lim_target en_target inp))

def strong_equiv_error_free_budgets_abort (lim_source : Int) (lim_target : Int) (source_image : Image) (target_image : Image) (en_source en_target : ExecEntry) (inp : ProcInput) : Prop :=
  error_free_unkilled (run source_image lim_source en_source inp) ∧ error_free_unkilled (run target_image lim_target en_target inp) ∧ trace_equiv (behavior.bh_traces (run source_image lim_source en_source inp)) (behavior.bh_traces (run target_image lim_target en_target inp))

def strong_universal_T_budgets (lim_source : Int) (lim_target : Int) (source_image : Image) (target_image : Image) : Prop :=
  ∀ en_source en_target inp, valid_entry source_image en_source inp → valid_entry target_image en_target inp → valid_input inp → (source_within_budget lim_source source_image) en_source inp → (strong_equiv_budgets lim_source lim_target source_image target_image) en_source en_target inp

def strong_universal_T_budgets_abort (lim_source : Int) (lim_target : Int) (source_image : Image) (target_image : Image) : Prop :=
  ∀ en_source en_target inp, valid_entry source_image en_source inp → valid_entry target_image en_target inp → valid_input_abort inp → (source_within_budget lim_source source_image) en_source inp → (strong_equiv_budgets lim_source lim_target source_image target_image) en_source en_target inp

def strong_universal_error_free_T_budgets (lim_source : Int) (lim_target : Int) (source_image : Image) (target_image : Image) : Prop :=
  ∀ en_source en_target inp, valid_entry source_image en_source inp → valid_entry target_image en_target inp → valid_input inp → (source_within_budget lim_source source_image) en_source inp → (strong_equiv_error_free_budgets lim_source lim_target source_image target_image) en_source en_target inp

def strong_universal_error_free_T_budgets_abort (lim_source : Int) (lim_target : Int) (source_image : Image) (target_image : Image) : Prop :=
  ∀ en_source en_target inp, valid_entry source_image en_source inp → valid_entry target_image en_target inp → valid_input_abort inp → (source_within_budget lim_source source_image) en_source inp → (strong_equiv_error_free_budgets_abort lim_source lim_target source_image target_image) en_source en_target inp

def strong_universal_T_budgets_hwcap_rv64gc (lim_source : Int) (lim_target : Int) (source_image : Image) (target_image : Image) : Prop :=
  ∀ en_source en_target inp, valid_entry source_image en_source inp → valid_entry target_image en_target inp → valid_input_hwcap_rv64gc inp → (source_within_budget lim_source source_image) en_source inp → (strong_equiv_budgets lim_source lim_target source_image target_image) en_source en_target inp

def strong_universal_T_budgets_hwcap_rv64gcv (lim_source : Int) (lim_target : Int) (source_image : Image) (target_image : Image) : Prop :=
  ∀ en_source en_target inp, valid_entry source_image en_source inp → valid_entry target_image en_target inp → valid_input_hwcap_rv64gcv inp → (source_within_budget lim_source source_image) en_source inp → (strong_equiv_budgets lim_source lim_target source_image target_image) en_source en_target inp

def strong_universal_error_free_T_budgets_hwcap_rv64gc (lim_source : Int) (lim_target : Int) (source_image : Image) (target_image : Image) : Prop :=
  ∀ en_source en_target inp, valid_entry source_image en_source inp → valid_entry target_image en_target inp → valid_input_hwcap_rv64gc inp → (source_within_budget lim_source source_image) en_source inp → (strong_equiv_error_free_budgets lim_source lim_target source_image target_image) en_source en_target inp

def strong_universal_error_free_T_budgets_hwcap_rv64gcv (lim_source : Int) (lim_target : Int) (source_image : Image) (target_image : Image) : Prop :=
  ∀ en_source en_target inp, valid_entry source_image en_source inp → valid_entry target_image en_target inp → valid_input_hwcap_rv64gcv inp → (source_within_budget lim_source source_image) en_source inp → (strong_equiv_error_free_budgets lim_source lim_target source_image target_image) en_source en_target inp

def strong_universal_T_budgets_abort_hwcap_rv64gc (lim_source : Int) (lim_target : Int) (source_image : Image) (target_image : Image) : Prop :=
  ∀ en_source en_target inp, valid_entry source_image en_source inp → valid_entry target_image en_target inp → valid_input_abort_hwcap_rv64gc inp → (source_within_budget lim_source source_image) en_source inp → (strong_equiv_budgets lim_source lim_target source_image target_image) en_source en_target inp

def strong_universal_T_budgets_abort_hwcap_rv64gcv (lim_source : Int) (lim_target : Int) (source_image : Image) (target_image : Image) : Prop :=
  ∀ en_source en_target inp, valid_entry source_image en_source inp → valid_entry target_image en_target inp → valid_input_abort_hwcap_rv64gcv inp → (source_within_budget lim_source source_image) en_source inp → (strong_equiv_budgets lim_source lim_target source_image target_image) en_source en_target inp

def strong_universal_error_free_T_budgets_abort_hwcap_rv64gc (lim_source : Int) (lim_target : Int) (source_image : Image) (target_image : Image) : Prop :=
  ∀ en_source en_target inp, valid_entry source_image en_source inp → valid_entry target_image en_target inp → valid_input_abort_hwcap_rv64gc inp → (source_within_budget lim_source source_image) en_source inp → (strong_equiv_error_free_budgets_abort lim_source lim_target source_image target_image) en_source en_target inp

def strong_universal_error_free_T_budgets_abort_hwcap_rv64gcv (lim_source : Int) (lim_target : Int) (source_image : Image) (target_image : Image) : Prop :=
  ∀ en_source en_target inp, valid_entry source_image en_source inp → valid_entry target_image en_target inp → valid_input_abort_hwcap_rv64gcv inp → (source_within_budget lim_source source_image) en_source inp → (strong_equiv_error_free_budgets_abort lim_source lim_target source_image target_image) en_source en_target inp

def source_within_budget_scfg (cfg : SpuriousCfg) (lim_source : Int) (source_image : Image) (en_source : ExecEntry) (inp : ProcInput) : Prop :=
  ¬ run_scfg_budget_refused cfg source_image lim_source en_source inp

def strong_equiv_budgets_scfg (cfg : SpuriousCfg) (lim_source : Int) (lim_target : Int) (source_image : Image) (target_image : Image) (en_source en_target : ExecEntry) (inp : ProcInput) : Prop :=
  modeled (run_scfg cfg source_image lim_source en_source inp) ∧ equiv (run_scfg cfg source_image lim_source en_source inp) (run_scfg cfg target_image lim_target en_target inp)

def strong_equiv_error_free_budgets_scfg (cfg : SpuriousCfg) (lim_source : Int) (lim_target : Int) (source_image : Image) (target_image : Image) (en_source en_target : ExecEntry) (inp : ProcInput) : Prop :=
  error_free (run_scfg cfg source_image lim_source en_source inp) ∧ error_free (run_scfg cfg target_image lim_target en_target inp) ∧ trace_equiv (behavior.bh_traces (run_scfg cfg source_image lim_source en_source inp)) (behavior.bh_traces (run_scfg cfg target_image lim_target en_target inp))

def strong_universal_T_scfg_budgets (cfg : SpuriousCfg) (lim_source : Int) (lim_target : Int) (source_image : Image) (target_image : Image) : Prop :=
  ∀ en_source en_target inp, valid_entry source_image en_source inp → valid_entry target_image en_target inp → valid_input inp → (source_within_budget_scfg cfg lim_source source_image) en_source inp → (strong_equiv_budgets_scfg cfg lim_source lim_target source_image target_image) en_source en_target inp

def strong_universal_error_free_T_scfg_budgets (cfg : SpuriousCfg) (lim_source : Int) (lim_target : Int) (source_image : Image) (target_image : Image) : Prop :=
  ∀ en_source en_target inp, valid_entry source_image en_source inp → valid_entry target_image en_target inp → valid_input inp → (source_within_budget_scfg cfg lim_source source_image) en_source inp → (strong_equiv_error_free_budgets_scfg cfg lim_source lim_target source_image target_image) en_source en_target inp

def strong_universal_T_scfg_budgets_hwcap_rv64gc (cfg : SpuriousCfg) (lim_source : Int) (lim_target : Int) (source_image : Image) (target_image : Image) : Prop :=
  ∀ en_source en_target inp, valid_entry source_image en_source inp → valid_entry target_image en_target inp → valid_input_hwcap_rv64gc inp → (source_within_budget_scfg cfg lim_source source_image) en_source inp → (strong_equiv_budgets_scfg cfg lim_source lim_target source_image target_image) en_source en_target inp

def strong_universal_T_scfg_budgets_hwcap_rv64gcv (cfg : SpuriousCfg) (lim_source : Int) (lim_target : Int) (source_image : Image) (target_image : Image) : Prop :=
  ∀ en_source en_target inp, valid_entry source_image en_source inp → valid_entry target_image en_target inp → valid_input_hwcap_rv64gcv inp → (source_within_budget_scfg cfg lim_source source_image) en_source inp → (strong_equiv_budgets_scfg cfg lim_source lim_target source_image target_image) en_source en_target inp

def strong_universal_error_free_T_scfg_budgets_hwcap_rv64gc (cfg : SpuriousCfg) (lim_source : Int) (lim_target : Int) (source_image : Image) (target_image : Image) : Prop :=
  ∀ en_source en_target inp, valid_entry source_image en_source inp → valid_entry target_image en_target inp → valid_input_hwcap_rv64gc inp → (source_within_budget_scfg cfg lim_source source_image) en_source inp → (strong_equiv_error_free_budgets_scfg cfg lim_source lim_target source_image target_image) en_source en_target inp

def strong_universal_error_free_T_scfg_budgets_hwcap_rv64gcv (cfg : SpuriousCfg) (lim_source : Int) (lim_target : Int) (source_image : Image) (target_image : Image) : Prop :=
  ∀ en_source en_target inp, valid_entry source_image en_source inp → valid_entry target_image en_target inp → valid_input_hwcap_rv64gcv inp → (source_within_budget_scfg cfg lim_source source_image) en_source inp → (strong_equiv_error_free_budgets_scfg cfg lim_source lim_target source_image target_image) en_source en_target inp

def strong_equiv_error_free_budgets_scfg_abort (cfg : SpuriousCfg) (lim_source : Int) (lim_target : Int) (source_image : Image) (target_image : Image) (en_source en_target : ExecEntry) (inp : ProcInput) : Prop :=
  error_free_unkilled (run_scfg cfg source_image lim_source en_source inp) ∧ error_free_unkilled (run_scfg cfg target_image lim_target en_target inp) ∧ trace_equiv (behavior.bh_traces (run_scfg cfg source_image lim_source en_source inp)) (behavior.bh_traces (run_scfg cfg target_image lim_target en_target inp))

def strong_universal_T_scfg_budgets_abort (cfg : SpuriousCfg) (lim_source : Int) (lim_target : Int) (source_image : Image) (target_image : Image) : Prop :=
  ∀ en_source en_target inp, valid_entry source_image en_source inp → valid_entry target_image en_target inp → valid_input_abort inp → (source_within_budget_scfg cfg lim_source source_image) en_source inp → (strong_equiv_budgets_scfg cfg lim_source lim_target source_image target_image) en_source en_target inp

def strong_universal_error_free_T_scfg_budgets_abort (cfg : SpuriousCfg) (lim_source : Int) (lim_target : Int) (source_image : Image) (target_image : Image) : Prop :=
  ∀ en_source en_target inp, valid_entry source_image en_source inp → valid_entry target_image en_target inp → valid_input_abort inp → (source_within_budget_scfg cfg lim_source source_image) en_source inp → (strong_equiv_error_free_budgets_scfg_abort cfg lim_source lim_target source_image target_image) en_source en_target inp

def strong_universal_T_scfg_budgets_abort_hwcap_rv64gc (cfg : SpuriousCfg) (lim_source : Int) (lim_target : Int) (source_image : Image) (target_image : Image) : Prop :=
  ∀ en_source en_target inp, valid_entry source_image en_source inp → valid_entry target_image en_target inp → valid_input_abort_hwcap_rv64gc inp → (source_within_budget_scfg cfg lim_source source_image) en_source inp → (strong_equiv_budgets_scfg cfg lim_source lim_target source_image target_image) en_source en_target inp

def strong_universal_T_scfg_budgets_abort_hwcap_rv64gcv (cfg : SpuriousCfg) (lim_source : Int) (lim_target : Int) (source_image : Image) (target_image : Image) : Prop :=
  ∀ en_source en_target inp, valid_entry source_image en_source inp → valid_entry target_image en_target inp → valid_input_abort_hwcap_rv64gcv inp → (source_within_budget_scfg cfg lim_source source_image) en_source inp → (strong_equiv_budgets_scfg cfg lim_source lim_target source_image target_image) en_source en_target inp

def strong_universal_error_free_T_scfg_budgets_abort_hwcap_rv64gc (cfg : SpuriousCfg) (lim_source : Int) (lim_target : Int) (source_image : Image) (target_image : Image) : Prop :=
  ∀ en_source en_target inp, valid_entry source_image en_source inp → valid_entry target_image en_target inp → valid_input_abort_hwcap_rv64gc inp → (source_within_budget_scfg cfg lim_source source_image) en_source inp → (strong_equiv_error_free_budgets_scfg_abort cfg lim_source lim_target source_image target_image) en_source en_target inp

def strong_universal_error_free_T_scfg_budgets_abort_hwcap_rv64gcv (cfg : SpuriousCfg) (lim_source : Int) (lim_target : Int) (source_image : Image) (target_image : Image) : Prop :=
  ∀ en_source en_target inp, valid_entry source_image en_source inp → valid_entry target_image en_target inp → valid_input_abort_hwcap_rv64gcv inp → (source_within_budget_scfg cfg lim_source source_image) en_source inp → (strong_equiv_error_free_budgets_scfg_abort cfg lim_source lim_target source_image target_image) en_source en_target inp

def strong_universal_T_budgets_either (ls lt : Int) (s t : Image) : Prop :=
  strong_universal_T_budgets ls lt s t ∧ strong_universal_T_budgets_abort ls lt s t

def strong_universal_error_free_T_budgets_either (ls lt : Int) (s t : Image) : Prop :=
  strong_universal_error_free_T_budgets ls lt s t ∧ strong_universal_error_free_T_budgets_abort ls lt s t

def asan_fixed_overhead : Int := 261 * 1048576
def sanitizer_source_limit : Int := 0x80000000
def budget_headroom_ok (lim_source lim_target : Int) : Bool :=
  decide (page_size ≤ lim_source) && decide (9 * lim_source + 8 * asan_fixed_overhead ≤ 8 * lim_target)

-- Equivalence.v's `Module Type BUDGETS` instances, as namespaces.
namespace ShippedBudgets
def lim_source : Int := source_alloc_limit
def lim_target : Int := target_alloc_limit
theorem headroom : budget_headroom_ok lim_source lim_target = true := by decide
end ShippedBudgets

namespace SanitizerBudgets
def lim_source : Int := sanitizer_source_limit
def lim_target : Int := target_alloc_limit
theorem headroom : budget_headroom_ok lim_source lim_target = true := by decide
end SanitizerBudgets

end LPS
