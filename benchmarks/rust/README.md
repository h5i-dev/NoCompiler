# NoCompiler Rust-100

[manifest.json](manifest.json) lists 100 candidates in nine categories
and marks the 20 development priorities. Category difficulty bands and
operation tags are estimates from the evaluation design. The candidate
registry is a sampling frame. Each executable run separately specifies
its pinned crate, fixture, track, source entries, and concrete function
names. Candidate source, enabled unsafe operations, and RV64 support
require screening before inclusion in a measured cohort.

## Run the pinned selection

Build the frontend, benchmark runner, and typed checker from the repository
root. The compiler capture uses the toolchain installed for the existing
RV64 Rust integration. The runner uses GNU `timeout` for a per-run deadline.

```sh
cargo build --locked --release -p cargo-nocompiler -p nocompiler-typed
target/release/nocompiler-rust-bench --artifacts /var/tmp/rust100-baseline
```

Use a fresh artifact directory for each run. Repeat `--run ID` to select
runs for local iteration. Use `--profile` to select a Cargo profile,
`--no-mir-hints`, `--llvm-hints`, or `--chc-solver /path/to/z3` for
separate configurations. Compare results with identical selected runs
and lockfiles. `--jobs` changes parallelism and affects wall time.

The default selection includes direct dependency targets, wrappers over
pinned OSS crates and standalone controls for the allocator, Box ABI,
and buffer analysis. The Cargo lockfiles pin dependencies and the
probe manifest disables default features. The runner saves the input
manifest, per-run logs, linked images, and checker reports. The aggregate
report also records the frontend, lockfile and ELF digests where available.

## Interpret the report

- Use requested targets as the proof-rate denominator. Selection failures,
  unsupported functions, rejections and timeouts remain in it.
- `built_runs` and `requested_targets_in_linked_builds` describe the build
  of the fixture. `unique_symbols_in_images` counts identified function
  symbols recorded in the ledger, keyed by ELF hash.
- `unique_source_entries` deduplicates source entries within the same
  crate and kind. Wrapper and direct dependency entries have separate kinds.
- `rust_checker_passed` includes `checked`, `proved`, and
  `proved_assuming`. The last two are reported separately. Every proof is
  conditional on its entry contract.
- A checker error records the first reported rule and diagnostic. A missing
  signature or unproved bound alone cannot distinguish an inference limit
  from a type system limit or a genuinely unsafe access.
- `elapsed_ms` measures the complete run, including the build and Lean.
  The runner reports no isolated annotation time or peak-memory metric.

Read `coverage.json` for grouped counts and individual results. A benchmark
rejection is a result. The runner returns a failing exit code on infrastructure
errors. The current manifest measures a curated slice of the candidate
registry. The independent screening cohort and vulnerability comparisons
require their own manifests and denominators.

## Baseline on `608c193`

[Recorded baseline and ablation](results/608c193.json) use locked release
builds with MIR hints. The selected 26 targets cover 24 distinct source
entries and 23 identified symbols across linked images. All 12 fixture runs
produced RV64 ELFs. The selected crate sources contain explicit unsafe blocks
by a lexical check, which does not establish which operations are enabled
in each monomorphization. The scalar `byteorder` read serves as a basic
memory-access control.

| Kind | Requested | Lean proved | Lean proved with external assumptions | Rejected | Unsupported |
| --- | ---: | ---: | ---: | ---: | ---: |
| Direct OSS dependency entries | 7 | 3 | 0 | 1 | 3 |
| OSS wrappers | 13 | 5 | 0 | 8 | 0 |
| Local controls | 6 | 4 | 2 | 0 | 0 |
| Total | 26 | 12 | 2 | 9 | 3 |

The Rust checker passed 14 of 26 targets. Lean proved the same 14, including
two external allocator assumptions. The rate without external assumptions
was 46.2% over all targets and 40.0% over the 20 OSS dependency entries and
wrappers. These rates use the fixed selection.

The nine rejections comprised six unproved memory-access obligations,
two missing callee contracts, and one missing loop invariant. The missing
callee contracts were in the `itoa` and `httparse` wrappers. The reverse
`memchr` wrapper lacked an invariant. The `heapless` length method and the
two direct `memchr` entries were unsupported by function selection.

For the 12 identical targets in `heapless`, `arrayvec`, and `bytemuck`,
disabling MIR hints left every verdict unchanged. Both runs proved 6 of 12.
No vulnerability rejection rate was measured.

## Screen the 100 candidates

The screening runner checks the exact registry archive against its SHA-256,
parses the crate's own Rust source, and builds the library on
`riscv64imac-unknown-none-elf`. It tries both the crate defaults and
`default-features = false`. The optional feature map additionally tries
`glam` with `nostd-libm` and `serde_json` with `alloc`.

```sh
cargo build --locked -p cargo-nocompiler --bin nocompiler-rust-screen
target/debug/nocompiler-rust-screen \
  --versions benchmarks/rust/results/screening-2026-11-28.json \
  --feature-overrides benchmarks/rust/screening-features.json \
  --artifacts /var/tmp/rust100-screen-replay
```

Omit `--versions` to discover the latest stable release for each candidate
except crates already pinned by the fixture manifest. Use a new artifact
directory per run. Each build directory keeps the generated manifest,
resolved Cargo.lock when available, and Cargo log. The report records
lockfile hashes for comparison. Replaying the screening pins direct crate
versions. Exact transitive dependency reproduction requires the saved
Cargo.lock for that probe.

The source scan counts explicit unsafe blocks separately from unsafe
function definitions, traits, impls, and extern blocks. It does not expand
macros or evaluate conditional compilation. A positive count and a
successful library build identify a candidate for function-level evaluation.
That intersection does not establish which blocks were compiled, which
function instances can be linked, or whether Lean can prove them. Disabling
default features alone does not establish that a crate is heap-free.

The [100-candidate screening report](results/screening-2026-11-28.json)
keeps all candidates in the denominator. The crate name `bytecast` returned
HTTP 404 from the sparse registry index. Source scanning recorded parse
failures for files in `staticvec` and `wee_alloc`.

| Screening result | Candidates |
| --- | ---: |
| Registry release resolved | 99 / 100 |
| Explicit unsafe block in own source | 90 / 100 |
| RV64 library built with default features | 38 / 100 |
| RV64 library built with defaults disabled | 84 / 100 |
| RV64 library built in any tested configuration | 86 / 100 |
| Explicit unsafe block and an RV64 library build | 78 / 100 |
| Development priorities meeting both criteria | 19 / 20 |

## Function-level cohort after screening

The manifest adds eight targets from six screened crates. The new selectors
exercise fixed-capacity deque and ring-buffer updates, a generic array
instantiation, alignment-checked byte reinterpretation, a zero-copy
little-endian load, and floating-point formatting. The full cohort has 28
OSS targets from 14 crates and six local controls. Wrapper outcomes apply
to their linked machine code under its entry contract. The selection was
made from the screening results and is a curated development cohort.

Run both configurations from the repository root with the same release
binaries and the checked-in Cargo.lock files.

```sh
target/release/nocompiler-rust-bench --artifacts /var/tmp/rust100-cohort-mir
target/release/nocompiler-rust-bench --artifacts /var/tmp/rust100-cohort-llvm --llvm-hints
```

The `byteorder` control exposes a regression with LLVM hints. The
`read_u32` symbol's 44 machine-code bytes were identical in both ELFs.
LLVM hints narrowed the return contract to `0 <= llvm_result < 4294967296`.
All four byte loads passed the capability checks, but the Rust checker
could not prove the return bound after the bitwise OR instructions
(`ret-out`). The baseline return contract allowed a general integer.

All 18 runs in each configuration produced linked RV64 ELFs.

| Configuration | Rust checker passed | Lean proved without external assumptions | Lean proved with external assumptions | Rejected | Unsupported |
| --- | ---: | ---: | ---: | ---: | ---: |
| MIR hints | 17 | 15 | 2 | 12 | 5 |
| MIR and LLVM hints | 16 | 14 | 2 | 13 | 5 |

Among the 28 OSS targets, 11 passed Lean without external assumptions
with MIR hints, and 10 passed with both hint sources. Three of the eight
new targets passed in both configurations. Both new push wrappers were
unsupported because their return type was `bool`. The rejected pop
wrappers exposed an unproved access bound in `arraydeque` and a missing
bounds-panic contract in `circular-buffer`. The `ryu` formatting wrapper
lacked a callee signature for `format64`.

The [cohort report](results/function-cohort-2026-11-28.json) includes each
target verdict and the changes between runs. Use the runner's artifact
directory for the full checker traces.

## Element type and capacity comparisons

The manifest also includes matched variants for five OSS APIs. The same
function selectors are used across hint configurations. Compare the labeled
variant outcomes within each API. The runner reports `source_coverage`
grouped by crate, source entry, and kind, along with the individual
`variant` labels. The manifest now has 40 requested machine-level targets
across 32 source entries.

For the matched subset, select `arrayvec`, `arraydeque`, `circular-buffer`,
`bytemuck`, `plain`, and the `byteorder` control with repeated `--run`
arguments. Run once with the default hint settings and once with
`--llvm-hints`. The 34-target cohort above is a historical measurement
from before these variants and the LLVM return-contract fallback.

In the [matched subset results](results/type-capacity-variants.json),
both configurations linked all six runs and produced identical verdicts
for 15 targets over nine source entries. Five targets reached Lean without
external assumptions, seven were rejected, and three were unsupported.
`ArrayVec::try_push` proved for `u64` at capacities 32 and 128. The
`u8` variant stopped at ABI extraction because the wrapper's second
argument is `u8`. Both widths of `plain::from_bytes` proved, and both
widths of the `bytemuck::try_cast_slice` wrapper failed the access-bound
check. The `byteorder` control proved with LLVM hints enabled.

## Full 40-target timing run

Run the two configurations sequentially on the same machine. Use the
same worker count, release binaries, and lockfiles.

```sh
cargo build --locked --release -p cargo-nocompiler -p nocompiler-typed
target/release/nocompiler-rust-bench --jobs 3 --artifacts /var/tmp/rust100-full-mir
target/release/nocompiler-rust-bench --jobs 3 --llvm-hints --artifacts /var/tmp/rust100-full-llvm
```

`suite_elapsed_ms` is wall time across the parallel workers. Each run
records `elapsed_ms`, its end-to-end wall time, plus
`timing_ms.build_and_capture` and `timing_ms.checker_attempts`.
The checker attempt times include linked-image processing, Rust checking,
Lean export and proof, and any LLVM result-contract retries.
The final ledger's per-function `micros` measures the Rust checker's
recorded function analysis. It excludes Lean and does not include earlier
attempts replaced by a retry. A median by run uses the 18 manifest runs.
A median by machine-code target uses only targets with a timing in the
final ledger.

The [full timing report](results/full-40-timing.json) records a single
sequential comparison on an AMD EPYC 9R14 with three benchmark workers
per configuration and artifacts on tmpfs. Both configurations linked all
18 runs and agreed on all 40 verdicts. Neither timed out.

| Metric | MIR | MIR + LLVM |
| --- | ---: | ---: |
| Lean proved without external assumptions | 17 | 17 |
| Lean proved with external assumptions | 2 | 2 |
| Rejected | 15 | 15 |
| Unsupported | 6 | 6 |
| Suite wall time | 156.67 s | 157.03 s |
| End-to-end median per run | 7.30 s | 7.59 s |
| Build and compiler capture median per run | 5.56 s | 5.80 s |
| Checker pipeline median per run | 2.41 s | 2.40 s |
| Rust checker median per timed function | 0.641 ms | 0.627 ms |

The forward `memchr` run dominated the suite wall time. Its checker
pipeline took 153.10 s with MIR and 153.74 s with MIR and LLVM. The LLVM
return-contract retry preserved the `byteorder` result. The wall times
describe one run of each configuration.
