# Verify a Rust buffer write on RV64

`set.rs` is a `no_std` Rust function with an explicit C ABI. It takes a
buffer pointer and length in `a0` and `a1`, and an index and value in `a2`
and `a3`. The handwritten contract in `set.ann` grants write access to
the buffer's `8*n` bytes and requires an 8-byte-aligned base. It admits
zero-length buffers and indices at or beyond the length.

From the repository root, with Rust (edition 2024), Lean, Python 3 and
`ld.lld` installed, run:

```sh
rustup target add riscv64imac-unknown-none-elf
cargo build --release -p nocompiler-typed
(cd lean && lake build NoCompiler)
scripts/rust-typed-trial/check.sh
```

The script prints the artifact directory. You can also provide a directory
as its first argument. It compiles both variants directly with rustc,
prepends the same contract to both assembly files and links the original
objects. Compressed instructions and linker relaxation are disabled for
the checker's fixed-width instruction image. The ELF entry symbol is
used for linking this function-only fixture. The ELF is meant for
verification.

The normal build must produce a `proved` ledger entry for `set` against
the linked ELF. The control build uses `nocompiler_unchecked` to remove
the bounds check and must be rejected by the Rust checker at the store
with `mem-bounds`. Both ledgers and the normal build's generated Lean
module are retained.

The proof covers the compiled function under its entry contract. The
caller supplies the buffer permissions. This example uses a handwritten
contract and leaves Rust ABI extraction and contract inference to future
work.

## Compiler-driven annotation with Cargo

The Rust binary in `crates/cargo-nocompiler` captures argument and return layouts during compilation,
generates entry contracts, and checks the resulting linked RV64 ELF.
It supports a selected binary and named functions or compiled instances.
Supported inputs include register-sized integers, thin raw pointers,
references to integers and integer arrays, and slices of those element types.
A raw pointer contributes a register value. Accesses in the emitted code
can generate explicit caller obligations for that pointer.
The subcommand can generate invariants for constant-stride slice loops and
frame annotations for fixed RV64 stack frames with direct stack accesses.

With the checker and Lean library built as above, install the pinned compiler
and make `llvm-symbolizer` available on your PATH. Then register the subcommand:

```sh
rustup toolchain install nightly-2026-09-17 --component rustc-dev,llvm-tools
rustup target add --toolchain nightly-2026-09-17 riscv64imac-unknown-none-elf
cargo build --release -p cargo-nocompiler -p nocompiler-typed
export PATH="$PWD/target/release:$PATH"

cargo nocompiler check \
    --manifest-path examples/rust-typed/fixtures/buffer_ops/Cargo.toml \
    --bin buffer_ops \
    --function buffer_ops::read_at \
    --function buffer_ops::copy_byte
```

The subcommand uses a release verification build. It disables compressed
instructions, linker relaxation, and LTO for the selected binary. It enables
`link-dead-code` and requires external linkage in the optimized assembly
before using rustc's entry ABI. LLVM can specialize an internal function's
calling convention, including by removing arguments. Proofs refer to the
`verified.elf` emitted by this build, identified by SHA-256 in the report.

The frontend and annotation passes use Rust and share the RV64 parser and
control-flow analysis with `nocompiler-typed`. Rust collects certificates
from Lean and invokes the kernel check. Outside a repository checkout, provide the built
Lean library via `--lean-dir` or `NOCOMPILER_LEAN_DIR`. Use `--checker` if
the `nocompiler-typed` binary is installed in a different directory.

The printed artifact directory contains `abi.tsv`, `contracts.s`,
`report.json`, and the checker's ledger and Lean files when the functions
reach that stage. The command returns 0 when every selected function is
proved, 1 for verification failures or unsupported selections, and 2 for
build or tool invocation errors. Generated contracts describe assumptions at
function entry, including the caller's buffer permissions.

Run `scripts/rust-typed-trial/check-auto.sh` to exercise both fixture crates.
The fixtures use Rust ABI functions with mangled symbols, including a
two-buffer copy and a deliberately unchecked read.

## Loop evaluation

The analyzer builds a control-flow graph from optimized RV64 assembly and
finds natural loops using dominance. It tracks affine register updates along
paths to each back edge. It proposes an invariant when the initial distance to
the exit equals the stride times a slice length and all back edges agree on
the recurrence. For nested loops it forgets registers modified by inner loops
when inferring an outer recurrence. When incoming branches establish a common
nonzero slice length, it can preserve that fact with a `join` annotation.
The checker validates every proposed annotation against the machine code.

The stack analyzer recognizes a fixed `addi sp, sp, -F` prologue and derives
8-byte slots or byte ranges from direct `offset(sp)` loads and stores. It
computes the stack budget transitively for direct calls to selected functions.
Dynamic frames and accesses through derived stack pointers are outside these
rules. A proved stack budget is conditional on the caller having that amount of
space available.

Run the evaluation with `scripts/rust-typed-trial/check-loops.sh`. The
`--no-infer-loops` flag runs the signature-only baseline.

| Function | Signature only | Inference on |
| --- | --- | --- |
| `buffer_ops::sum` | Missing invariant | Proved |
| `buffer_ops::fill` | Missing invariant | Proved |
| `buffer_ops::contains` | Missing invariant | Proved |
| `buffer_ops::sum_two` | Missing invariant | Proved with two sequential loops |
| `buffer_ops::fill_rows` | Missing invariant | Proved with two nested loops |
| `buffer_ops::stack_word`, `stack_byte`, `stack_call` | — | Proved with generated frames and stack budgets |
| `buffer_ops::sum_shifted` | — | Rejected at the out-of-bounds load |
| `memchr_probe::find` | Missing invariant | Proved with five loop invariants |

The last case calls upstream `memchr` 2.8.3 with default features disabled.
The linked wrapper includes byte scans, an aligned word scan, and a tail
scan. In a diagnostic run, handwritten invariants advanced past the missing
annotation errors. With the original signature, the word-loop back edge
could not establish that another 16 bytes fit: that signature admitted a
slice endpoint equal to `2^64`. Adding the no-wrap endpoint condition for a
valid Rust slice let the handwritten version pass both checkers. The default
pipeline now generates this condition for slices and infers the word-loop
alignment, remaining-byte bound, and tail join from the assembly.

## Raw pointers and relational joins

At a merge of paths that consume different prefixes of a slice, the tool can
retain a common symbolic prefix instead of forgetting the cursor and length
independently. The resulting join keeps the cursor's stride alignment and
the relationship to the end of the slice. A later loop can express its
invariant using that endpoint and its own remaining count.

For acyclic functions, direct loads, stores, and already inferred direct
callees can generate fixed-size `ro` or `rw` raw-pointer requirements. The
checker validates the callee body and checks that callers can lend each
required range. The stack analyzer can make a fixed local range available
to such a call. Standalone raw-pointer entry points still require callers
to satisfy the inferred conditions. The report lists these conditions by
symbol and input register. Variable-length raw-pointer footprints and
indirect calls are outside these inference rules.

Run `scripts/rust-typed-trial/check-relations.sh` for the prefix join, calls
using a sub-slice or a local stack buffer, and a too-short buffer that the
checker rejects at the call site.

## Fixed-capacity collections and allocation lifetimes

`scripts/rust-typed-trial/check-aggregates.sh` verifies unmodified
`heapless` 0.9.3 methods and callers. It selects `read::<4>`, `read::<8>`,
append and copy callers, and the dependency's concrete `as_slice` and
`push` methods. The compiler records the layout and field offsets for each
concrete struct reference. `instances.tsv` lists compiled instances and
their symbols. The report includes direct MIR callees and inlining recorded
by rustc's MIR inliner. The report also records linked instruction ranges and inline stacks from LLVM
DWARF, including functions that still appear as direct calls in MIR.
Register-pair returns are checked as machine words, with no inferred
contract linking a returned reference to its source region.

`--invariants FILE.json` maps a Rust type to length fields and their
backing array fields. For example:

```json
{"heapless::vec::VecInner": {"len": "buffer.buffer"}}
```

The mapping is an override. The default inference looks for a word-sized
length field, a unique backing array, and an emitted mutator that compares
the length with capacity before increasing it. The report names the inferred
candidate and the method that suggested it. The numeric capacity and length
offset come from rustc's concrete layout. For a mutable borrow, the checker
verifies the bound on return, including when paths update the field
differently. The entry bound is a semantic requirement on incoming
collection values. It remains an assumption for constructors and methods
outside the verification scope.

The evaluation also exercises raw-pointer footprint discovery across a
stack spill and reload, disjoint mutable sub-slices borrowed from one buffer,
and a byte-record scan whose stride depends on data read during the loop.

`--allocator-contracts FILE.json` supplies assumptions for linked
allocator symbols. The supported register interfaces are:

| Operation | Arguments |
| --- | --- |
| `allocate` | Byte count in `a0`. Returns a nullable pointer in `a0`. |
| `deallocate` | Pointer and original byte count in `a0`, `a1`. |
| `reallocate` | Old pointer, old byte count, new byte count in `a0`–`a2`. A null return preserves the old allocation. |
| `reallocate_nonnull` | Old pointer, old byte count, new byte count in `a0`–`a2`. Returns a nonnull replacement in `a0`. |

Each entry supplies a `stack` budget and optionally a power-of-two
`alignment` for returned pointers. NoCompiler infers which selected
callers need the heap token. A deallocation or successful reallocation
consumes the old capability. The fixtures check use after release, use
after replacement, and double release. These proofs assume the allocator
contracts, so they are reported as `proved_assuming` and require
`--allow-assumptions` for a successful CLI exit. The fixture allocator
only exercises the caller rules.

The tool also recognizes linked rustc global allocator shims and simple
register-move forwarding from those shims to the implementation. It
generates assumptions for allocation, zeroed allocation, sized release, and
reallocation with a null failure result. Alignment arguments of 1, 2, 4, 8,
16, 32 or 64 bytes are supported. The allocator's stack budget is an
assumption, configurable with `--global-allocator-stack` (default 4096 bytes).
The report records every generated assumption. An allocator implementation
inlined directly into the selected body is checked as machine code under
that body's capabilities.

A `Box<T>` using Rust's global allocator acquires `take` and `give` ownership
clauses automatically for nonzero-sized integer and integer-array pointees.
The probe covers ownership transfer and dropping a box through the allocator.
Other allocator types and dynamically sized or zero-sized pointees are
outside these rules.

## Automatic proof coverage

Run `scripts/rust-typed-trial/measure.py` to reproduce the fixed selection.
It uses `heapless` 0.9.3 and `memchr` 2.8.3, plus local fixtures for Rust's
allocator/Box ABI and buffer analysis. It supplies no manual annotation or
invariant file. Each selected target contributes to the denominator,
including targets the current compiler integration cannot select. The
`coverage.json` output and per-run logs distinguish dependency functions,
wrappers that include dependency code, and standalone fixtures.

`proved` means the linked machine code meets its generated entry contract.
A generated collection invariant is visible in the per-run report and
remains an entry requirement. `proved_assuming` additionally requires the
listed external allocator contracts. This is a fixed capability benchmark;
its rates describe these targets.

The measured selection had 19 targets:

| Group | Proved | Proved with external assumptions | Rejected | Unsupported |
| --- | ---: | ---: | ---: | ---: |
| Dependency functions | 3/7 (42.9%) | 0 | 1 | 3 |
| Wrappers over dependency code | 5/6 (83.3%) | 0 | 1 | 0 |
| Standalone fixtures | 4/6 (66.7%) | 2 | 0 | 0 |
| Total | 12/19 (63.2%) | 2 | 2 | 3 |

The forward `memchr` proof was retried on the same ELF using the exported
code span of the selected function. `push_unchecked` and the reverse scan
were rejected. `Vec::len` and the two upstream `memchr` entry points could
not be selected as independent functions in the current build pipeline.
