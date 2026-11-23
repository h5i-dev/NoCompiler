import LPS.EquivalenceDefinition.HaltsAllowed
import LPS.OSSVerify.Core.Images

/-!
# oss-verify-proofs `theories/Shapes.v`: what every statement says

Port of `theories/Shapes.v` of theorem-labs/oss-verify-proofs (at 90e648c1; MIT License, Copyright (c) 2026 Theorem Labs, PBC), the
parameters (`Budgets`, `Env`, `Exits`) and statement shapes, for any image (the ones ported are those
fuzz_qdisc's statements use, `Examples/LPS/FuzzQdisc`): `agrees`, `agrees_in`,
`halts_within_budget`, `halts_may_fail`. As in Shapes.v, each is proved EQUAL by `rfl` to the LPS
definition it corresponds to (`*_is_lps`), so it means exactly what LPS means. Not ported yet:
`agrees_abort_modelled*`, the `_rv64gc` variants, `disagrees_at_most`, `classifies`,
`classifier_rejects_at_most`, `agreement_decidable*` (they need EquivalenceDefinition/{FinInput,Classifier,
Measure}, not ported).
-/

namespace LPS.OSSVerify
open LPS

namespace Budgets
-- 16 GiB for the plain build, 512 GiB for the sanitizer build (LPS's `ShippedBudgets`).
namespace Standard
def lim_source : Int := ShippedBudgets.lim_source
def lim_target : Int := ShippedBudgets.lim_target
end Standard
-- 2 GiB / 512 GiB (LPS's `SanitizerBudgets`).
namespace Asan
def lim_source : Int := SanitizerBudgets.lim_source
def lim_target : Int := SanitizerBudgets.lim_target
end Asan
end Budgets

theorem standard_budgets : Budgets.Standard.lim_source = 0x400000000 ∧ Budgets.Standard.lim_target = 0x8000000000 :=
  ⟨rfl, rfl⟩
theorem asan_budgets : Budgets.Asan.lim_source = 0x80000000 ∧ Budgets.Asan.lim_target = 0x8000000000 := ⟨rfl, rfl⟩

namespace Env
def may_fail : SpuriousCfg := may_fail_cfg
def alloc_forced_only : SpuriousCfg := alloc_only_cfg false
def forced_only : SpuriousCfg := forced_only_cfg
end Env

theorem may_fail_is : Env.may_fail = mkSpuriousCfg true true true true true true := rfl
theorem alloc_forced_only_is : Env.alloc_forced_only = mkSpuriousCfg false true true true true true := rfl
theorem forced_only_is : Env.forced_only = mkSpuriousCfg false false false false false false := rfl

namespace Exits
/-- 0..255: the statement says only that the process exits. -/
def any : List word := AnyExit.codes
/-- 0 or 2. -/
def ok_or_refused : List word := [Z_to_bv 64 0, Z_to_bv 64 2]
end Exits

/-- Shape 1: agreement of a sanitizer build with the plain build (Shapes.v's `agrees`). -/
def agrees (lim_plain lim_san : Int) (plain san : Image) : Prop :=
  ∀ (en_plain en_san : ExecEntry) (inp : ProcInput),
    valid_entry plain en_plain inp → valid_entry san en_san inp → valid_input inp →
    ¬ run_budget_refused plain lim_plain en_plain inp →
    error_free (run plain lim_plain en_plain inp) ∧ error_free (run san lim_san en_san inp) ∧
      trace_equiv (run plain lim_plain en_plain inp).bh_traces (run san lim_san en_san inp).bh_traces

theorem agrees_is_lps (lp ls : Int) (p s : Image) : agrees lp ls p s = strong_universal_error_free_T_budgets lp ls p s := rfl

/-- `agrees` when the environment refuses only what `env` allows (Shapes.v's `agrees_in`). -/
def agrees_in (env : SpuriousCfg) (lim_plain lim_san : Int) (plain san : Image) : Prop :=
  ∀ (en_plain en_san : ExecEntry) (inp : ProcInput),
    valid_entry plain en_plain inp → valid_entry san en_san inp → valid_input inp →
    ¬ run_scfg_budget_refused env plain lim_plain en_plain inp →
    error_free (run_scfg env plain lim_plain en_plain inp) ∧ error_free (run_scfg env san lim_san en_san inp) ∧
      trace_equiv (run_scfg env plain lim_plain en_plain inp).bh_traces (run_scfg env san lim_san en_san inp).bh_traces

theorem agrees_in_is_lps (env : SpuriousCfg) (lp ls : Int) (p s : Image) :
    agrees_in env lp ls p s = strong_universal_error_free_T_scfg_budgets env lp ls p s := rfl

/-- Every execution ends by exit_group with a status in `allowed`, on every input on which it is never refused
    memory for exceeding `lim`, the environment refusing nothing it is not forced to (Shapes.v). -/
def halts_within_budget (lim : Int) (allowed : List word) (img : Image) : Prop :=
  ∀ (en : ExecEntry) (inp : ProcInput), valid_entry img en inp → valid_input inp →
    ¬ run_scfg_budget_refused forced_only_cfg img lim en inp → must_exit_in_scfg forced_only_cfg allowed img lim en inp

theorem halts_within_budget_is_lps (lim : Int) (allowed : List word) (img : Image) :
    halts_within_budget lim allowed img = halts_allowed_T_scfg_budgets forced_only_cfg lim allowed img := rfl

/-- As above with no budget premise, whatever the environment refuses, at LPS's single-binary budget. -/
def halts_may_fail (allowed : List word) (img : Image) : Prop :=
  ∀ (en : ExecEntry) (inp : ProcInput), valid_entry img en inp → valid_input inp →
    must_exit_in_scfg may_fail_cfg allowed img source_alloc_limit en inp

theorem halts_may_fail_is_lps (allowed : List word) (img : Image) :
    halts_may_fail allowed img = halts_allowed_T_scfg may_fail_cfg allowed img := rfl

end LPS.OSSVerify
