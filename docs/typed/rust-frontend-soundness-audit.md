# Rust frontend soundness audit

This audit compares `origin/main` at `3509a906` with PR #19 at
`8fbb923`. The scope is the machine-level theorem and how the Rust
verification path supplies its linked ELF and contracts to Lean.

## Semantic definitions and theorem types

`Meets` and `MeetsP` have identical source in both revisions. The full
repository-local import closure of their defining modules is also identical.

- `Typed/Sem`, `Typed/SemPartial`, and `Typed/Lang`
- `Spec`, `Adequacy`, `Env`, and `Lemmas`
- `Isa`, `Machine`, and `Step`

This comparison covers the entry and return contracts, permitted memory
accesses, machine steps, and total and partial execution judgments. It also
covers how the model fetches and decodes words. Both revisions use the same
Lean toolchain and dependency manifest.

Building both revisions and running the following in each produced identical
theorem types and dependency lists.

```lean
import NoCompiler.Typed.Sound.Prog
#check @NoCompiler.Typed.Fn.check_sound
#check @NoCompiler.Typed.Prog.check_sound
#print axioms NoCompiler.Typed.Fn.check_sound
#print axioms NoCompiler.Typed.Prog.check_sound
```

Both theorems depend on `propext`, `Classical.choice`, and `Quot.sound`.
The declarations and `Typed/Prog.lean` are unchanged. The modified
checker rules and the local lemmas for call effects, capability retention,
and indirect calls are checked inside this theorem boundary. The
[axiom regression test](../../lean/TypedTests/SoundnessAudit.lean) runs
as part of the default Lean build.

## Linked ELF and generated proof

The ELF word reader in `nocompiler-typed/src/object.rs` is unchanged. The
checker obtains the section address and little-endian words from the same
ELF byte buffer. The single-file exporter can now use a contiguous slice
of those words at its original virtual addresses. It computes the span
from the selected function domains and the external callee domains,
falling back to the full section if it cannot form the slice. The
multi-file exporter retains the full section. Chunking the literals
changes how Lean elaborates the array.

The Rust proof path can propose register-call targets from the ELF. Lean
decodes the exported instructions and checks either the computed constant
target or coverage of the possible register values by the checked target
cases. Compiled Lean evaluation now collects certificate hints through the
Rust frontend. The generated proof uses `decide +kernel` to validate
the entry and instruction checks and derives the result from the existing
program soundness theorem. External callee contracts still appear as an
explicit `Meets` premise of `prog_meets_rel` and as `proved_assuming` in
the ledger. The closed theorem uses an empty external environment.

For a separate byte check, 54 successful certificate exports from the Rust
integration runs were compared against their corresponding `verified.elf`
files. All 7,009 exported words matched `.text` at their stated addresses.
The sample included 52 closed proofs and two proofs with external contracts.
This is a regression check of the exporter. The existing artifact boundary
still requires correct ELF extraction, an accurate machine and environment
model, and caller satisfaction of the recorded contracts. The frontend can
compare the verification input with the deployment ELF by SHA-256.
