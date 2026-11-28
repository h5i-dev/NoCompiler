---
name: nocompiler
description: Write, check, and prove NoCompiler Typed Assembly for RV64. Use for function contracts, memory capabilities, loop invariants, Rust-generated annotations, and Lean 4 verification of linked ELF code.
---

# NoCompiler Typed Assembly

NoCompiler checks machine-level memory safety for RV64 assembly under explicit
contracts. Use the Rust checker for fast diagnostics and the Lean 4 checker for
formal verification. The ELF used for the linked proof must match the intended
deployment artifact.

## Check an assembly function

```sh
cargo build --locked --release -p nocompiler-typed
target/release/nocompiler-typed check examples/typed/sum.s
```

Read the [annotation grammar](../../docs/typed/syntax.md) before writing or
changing contracts. Describe the function's entry registers, accessible regions
and permissions, and stack use. Add invariants at loop entries and a decreases
measure when the proof requires termination. Check call-site obligations
against the callee's contract. For a failed check, inspect the first outstanding
obligation before revising an annotation. Preserve the API's valid inputs
when choosing entry conditions.

## Prove the linked code

```sh
(cd lean && lake build NoCompiler)
target/release/nocompiler-typed check annotated.s --image program.elf \
  --export-lean Proof.lean --prove --certs --ledger ledger.json
```

Use `nocompiler-typed link` to check across assembly files. Read the
[proof export and linking guide](../../docs/typed/export.md) for whole-program
proofs and [the Lean checker guide](../../docs/typed/lean-checker.md) for the
machine model and theorems. Report Rust checker acceptance (`checked`), Lean
proof (`proved`), and Lean proof with external callee contracts
(`proved_assuming`) explicitly. All three are conditional on the function's
entry contract.

## Generate annotations for Rust

Use `cargo-nocompiler check` for the supported Rust-to-RV64 pipeline. It
generates annotations from compiler and machine-code information and checks
them against the final linked ELF. Follow the
[Rust integration guide](../../examples/rust-typed/README.md) for the pinned
toolchain, function selectors, and proof artifacts. Treat MIR and LLVM facts as
annotation candidates. Check public entry conditions and any external
assumptions before using a generated proof. Source-level Rust soundness,
including aliasing and provenance, requires separate reasoning. Use the
[Rust-100 benchmark](../../benchmarks/rust/README.md) to measure coverage and
timing on the recorded cohort.

## Optional development toolkit

Use the disassembler, decompiler, and binary-inspection commands under the
separate `nocompiler` CLI when debugging code generation or inspecting a binary.
Use the [toolkit manual](../../docs/toolkit/MANUAL.md) for commands and the
[project workspace guide](../../docs/toolkit/dashboard.md) for shared
investigation records. Pseudocode and recovered control flow are development
aids. Use the typed checker and proof ledger as verification evidence.
