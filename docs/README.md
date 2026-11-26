# Documentation

## Typed RISC-V

- [typed/decisions.md](typed/decisions.md): readings taken where the note is silent, as
  implemented.
- [typed/musl-trial.md](typed/musl-trial.md): the trial on musl functions as compiled, with
  its verdicts fixed in advance.
- [ROADMAP.md](ROADMAP.md): the order of work.

## The machine model

- [isa/spec.md](isa/spec.md): `Reach`, `Exec`, `Spec`, `VerifiedImg`, adequacy to the
  hardware step, and ⟦σ⟧ as a `Spec`.
- [isa/trust.md](isa/trust.md): what a result depends on.
- [isa/environment.md](isa/environment.md): the Linux syscall model.

## Repository layout

| Path | What |
| --- | --- |
| `lean/NoCompiler/` | the machine semantics (`Isa`, `Machine`, `Env`, `Step`), `Spec`, `Adequacy`, lemmas, and `Typed/` (type language, ⟦σ⟧, Presburger entailment, the Lean checker as it lands) |
| `lean/TypedTests/` | kernel-checked tests of `Typed/`, kept out of the core library |
| `crates/nocompiler-typed` | the Rust checker (being written) |
| `crates/nocompiler-*` (the rest) | the binary analysis toolkit: loaders, decoders, SLEIGH, IR, analysis, decompiler, differ, annotation store; `nocompiler-cli` is the `nocompiler` binary |
| `tests/typed/corpus/` | typed programs and their expected verdicts, shared by both checkers |
| `examples/musl/` | annotated musl functions for the trial |
| `fixtures/` | the toolkit's test corpus (sources; `scripts/toolkit/build-fixtures.sh` builds it) |
| `scripts/ci/local.sh` | the CI jobs, run locally |
| `scripts/toolkit/` | toolkit corpus, benchmark, comparison and release scripts |
| `skills/` | an agent skill for the toolkit commands |

Some of these paths appear as the agents land their work; a path that is not in the tree
yet is in progress.

## Binary analysis toolkit

[toolkit/README.md](toolkit/README.md), with the command reference
[toolkit/MANUAL.md](toolkit/MANUAL.md), the [design notes](toolkit/design/README.md), the
[scorecard](toolkit/scorecard.md), the [benchmarks](toolkit/benchmarks.md) and its
[milestone record](toolkit/ROADMAP-toolkit.md).
