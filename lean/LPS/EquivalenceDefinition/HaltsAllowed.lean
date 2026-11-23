import LPS.EquivalenceDefinition.Equivalence

/-!
# LPS `theories/EquivalenceDefinition/HaltsAllowed.v` (f1006fe8): every run exits with an allowed status

Port of LPS (theorem-labs/rocq-linux-process-semantics, MIT License, Copyright (c) 2026 Theorem Labs,
PBC), `theories/EquivalenceDefinition/HaltsAllowed.v` at f1006fe8, its Definitions. Its `Module Type`s
(`ALLOWED_EXITS`, `SPEC_HALTS_ALLOWED*`) are interfaces, not ported (see Equivalence.lean); the one module
instance `AnyExit` is the namespace `AnyExit` with `codes`.
-/

namespace LPS

def halts_allowed_T (S : List word) (img : Image) : Prop :=
  ∀ en inp, valid_entry img en inp → valid_input inp → must_exit_in S img source_alloc_limit en inp

def halts_allowed_T_scfg (cfg : SpuriousCfg) (S : List word) (img : Image) : Prop :=
  ∀ en inp, valid_entry img en inp → valid_input inp → must_exit_in_scfg cfg S img source_alloc_limit en inp

def halts_allowed_T_scfg_budgets (cfg : SpuriousCfg) (lim : Int) (S : List word) (img : Image) : Prop :=
  ∀ en inp, valid_entry img en inp → valid_input inp → source_within_budget_scfg cfg lim img en inp →
    must_exit_in_scfg cfg S img lim en inp

def status_allowed (S : List word) (code : word) : Bool := S.any fun c => bv_eqb c code

def byte_codes : List word := (List.range 256).map fun (n : Nat) => Z_to_bv 64 (n : Int)

namespace AnyExit
def codes : List word := byte_codes
end AnyExit

end LPS
