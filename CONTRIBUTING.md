# Contributing

## The rule that matters: clean room

This project reimplements ideas that other reverse engineering tools also
implement. Ideas are not the problem; copied code is.

**Work from public specifications and from observed behaviour, never from
another tool's source.** In practice:

- Read the published specification: the ELF gABI and the processor supplements,
  the DWARF standard, the PE/COFF specification, the Itanium C++ ABI, the ARM
  and Intel architecture reference manuals, the public documentation of the PDB
  format.
- Observe what an existing tool *does* as much as you like. Running `objdump`
  and comparing its output against ours is how the decoders are tested, and
  that is fine: the output is a fact about the input, not a piece of someone's
  program.
- Do not read another tool's implementation and then write the same thing here.
  If you have read it, say so in the pull request, and expect the reviewer to
  ask someone who has not to write that part.
- One exception, deliberately narrow: the SLEIGH *language definitions* under
  Ghidra's processor tree are data, and loading them is the point of M2. Their
  format is specified. The decompiler's source is not to be consulted.

If a fixture or a test case comes from another project, say where it came from
and under what licence, in the file that uses it.

## What a change has to come with

Every claim this tool makes is measured, and a change that makes a claim has to
bring its measurement. For the typed checkers, the measurements are the shared corpus
(`tests/typed/corpus/`) and the trial results (`docs/typed/musl-trial.md`).
`docs/toolkit/ROADMAP-toolkit.md` says what each part of the toolkit is gated on. The
short version:

- **An external oracle wherever one exists.** A decoder is compared against
  `objdump` and `llvm-objdump`; a lifter against what a processor produced when
  the same program was run; a demangler against `c++filt`; debug information
  against `readelf`; a merge against `git merge`. Numbers that only compare the
  tool against itself are not evidence.
- **Wrong and missing are different.** A wrong answer is a bug with no
  allowance and the test asserts zero of them. A missing answer is a gap with a
  floor or a ceiling that only moves one way, and the number stays in
  `docs/toolkit/scorecard.md` even when it is unflattering.
- **A test that cannot fail is not a test.** After writing one, break the code
  it covers on purpose and check that it goes red.

## Style

- Comments are concise and explain *why*. The code says what it does. A comment
  that restates the line above it is noise, and a banner is worse.
- Say what is not known. An analysis that cannot work something out reports
  that rather than guessing, and the type system should make the difference
  visible: `Option`, an explicit `Unresolved`, a strength on the evidence.
- No emoji, no em dashes.
- `cargo clippy --release --all-targets` leaves no warnings.

## Building

The shared development machine is small, so build the release profile and cap the jobs:

```
CARGO_BUILD_JOBS=4 cargo build --release
CARGO_BUILD_JOBS=4 cargo test --release
(cd lean && lake build)                          # the Lean library and its tests (TypedTests)
bash scripts/toolkit/build-fixtures.sh           # the toolkit corpus its gates measure against
bash scripts/toolkit/check-determinism.sh        # the same input must give the same output
```

Lean proofs use only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`):
no `sorry`, no `native_decide`. Check a new theorem with `#print axioms`.

The machine model's oracle tests compare decoding against llvm-mc and semantics against
qemu-riscv64 and the Sail RISC-V emulator. They are being restored as
`crates/nocompiler-rv`, and need llvm-mc, clang, ld.lld, qemu-riscv64, lake and the Sail
emulator. A test whose tool is missing prints `SKIPPED` and its reason.

Where things go:
- The core is the Lean library `lean/NoCompiler/` and the typed checker crate.
- Tests, examples, the shared corpus `tests/typed/corpus/` and benchmarks live outside
  the core and only use it. Nothing in the core is shaped around a particular example or
  benchmark.
- The toolkit is the other `crates/nocompiler-*` crates (docs in `docs/toolkit/`, corpus
  in `fixtures/`). The core depends on nothing in it.

CI runs on disposable runners and builds the dev profile on purpose. Do not add
`--release` there. Dev profile panics on an overflowing `-` where release wraps
it and returns a wrong answer quietly, so an arithmetic bug can be invisible
locally and show up only on CI. A red CI is worth reading before assuming it is
about the runner.

Fixtures are built, not committed. A test whose fixture or tool is missing
returns early rather than failing, so a fresh checkout on a different machine
still runs the suite it can.

## Reporting something wrong

A decoding that disagrees with `objdump`, a lifting that disagrees with the
processor, or a recovered fact that is untrue are the most valuable reports
this project can get. Include the bytes, the architecture, and what the other
tool said.

## Checks before pushing

CI on GitHub runs only for pull requests. Before pushing, run its jobs here:

```sh
scripts/ci/local.sh check   # always: fmt, clippy
scripts/ci/local.sh core    # lean/**, the typed checker, examples/**
scripts/ci/local.sh test    # any crate: the whole suite with the fixture corpus, in a container
```

A job that was not run is said to be not run, in the commit message.
