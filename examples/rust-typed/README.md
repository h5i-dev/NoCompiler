# Verify a Rust buffer write on RV64

The Rust frontend is experimental. Its proofs cover the linked RV64 code
under the recorded entry contracts and any listed external assumptions.

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

The printed artifact directory contains `abi.tsv`, `contracts.json`, `contracts.s`,
`report.json`, and the checker's ledger and Lean files when the functions
reach that stage. The command returns 0 when every selected function is
proved, 1 for verification failures or unsupported selections, and 2 for
build or tool invocation errors. Generated contracts describe assumptions at
function entry, including the caller's buffer permissions.

For a public entry, review the exact generated signature in
`entry-contracts.json` and pass that JSON map as `--entry-contracts FILE`
on subsequent runs. The map must cover exactly the requested Rust function
paths. The comparison includes requirements and guarantees and excludes
the linker symbol and inferred frame. A difference prevents verification and is
reported as `entry_contract_mismatch`. An exact match checks contract stability.
The review establishes whether the contract describes the public API.
The report records review status per requested entry. Internal calls are
checked against callee contracts by the typed checker. The frontend rejects
a proven contradiction among the resolved arithmetic entry conditions.
The arithmetic check includes ABI register ranges and can report an unknown
result. Its satisfiable result concerns arithmetic constraints and leaves
the existence of required memory capabilities to the caller.

Use `--deployment-elf FILE` to require the existing deployment ELF to match
the checker input by SHA-256. The proof report includes the digest. A mismatch
ends the command before Lean runs.

`--features`, `--all-features`, `--no-default-features`, and `--locked`
are forwarded to Cargo for the checked build. `cargo-build.json` records
the package IDs, resolved feature lists, and profiles reported by Cargo for
the built artifacts. The target is RV64. Use `--profile` to select a Cargo profile (default: release).
The report's `proof_attempt` field records whether the Lean proof was
produced, blocked before proof generation, or failed, with a reason when
available. Per-function statuses still distinguish a function checked by
the Rust checker from one with a completed proof.

`static_call_scope` traces the direct call graph among the selected optimized
assembly bodies for each entry. It lists selected bodies, declared external
contracts, linked symbols without selected bodies or contracts, missing linked
symbols, and unresolved indirect sites. This diagnostic can include statically
present calls on infeasible paths. The linked-image proof determines the
verified scope.

The rustc adapter extracts argument-relative effects from concrete optimized MIR.
`contracts.json` records the candidate contracts using argument indices and
symbolic byte ranges. The RV64 lowering maps those arguments to ABI registers
and emits the clauses in `contracts.s`. The linked-image checker verifies the
emitted contracts, including whether a caller can supply a callee's inferred
buffer permissions. Use `--no-mir-hints` to measure which results rely on these
candidates. The candidate report remains available in this mode.

`scripts/rust-typed-trial/check-mir.sh` exercises a run-time length on raw
pointers, a shifted call that supplies enough memory, a call that cannot
supply it, and return guarantees for a sub-slice and a field write. The MIR
analysis keeps up to four distinct states per block, including the pairing
between a pointer and its length. At wider joins it intersects the exact facts
and retains a common slice-end relation even when the component values differ.
Taking a subslice that trims a known number of elements from the end
adjusts that relation by the number of bytes removed.
If every analyzed return path for a slice has the same end address,
the tool can emit a relation between the returned pointer and length even
when each value differs across paths. A field-write postcondition can be
proved on the callee and used by a caller such as `reset_and_read` when the
borrow contract identifies a contained constant-offset range. The
`scripts/rust-typed-trial/check-borrowed-fields.sh` regression verifies this
on a linked RV64 image with and without the inferred guarantee. The
analysis covers the declared machine-level field values.

For a resolved, selected direct MIR callee, the analyzer substitutes the
actual arguments into the callee's effects, field writes, scalar result, and
returned slice. A call-graph worklist stabilizes these summaries. With a known write span,
disjoint tracked fields in the same input region survive a call. Unknown
effects or calls with an unwind successor invalidate the caller's field
facts. MIR moves consume the source binding and invalidate overlapping
projected field values. Complete scalar stores also record initialization
when the stored value has no affine expression. At a successful return the
generated contract gives such an initialized word a fresh output variable.
Known drop effects invalidate aliases derived from the dropped argument. A finite set of function-pointer targets contributes
the union of possible effects and the intersection of guaranteed field
values and initialization. Linked AUIPC/ADDI materialization of known
function addresses and finite register merges supply candidates for JALR.
The Lean checker validates every possible callee against the linked image. The linked-image proof still checks the resulting contracts.

For ownership transfer with `take` and `give`, the Lean call rule carries
the fields promised on the returned capability into the caller's state.
`scripts/rust-typed-trial/check-owned-fields.sh` verifies an owned word
initialized by the callee and read by the caller on a linked RV64 image.

## LLVM-derived candidates

Pass `--llvm-hints` to also emit the optimized LLVM IR and run pinned LLVM
`opt` and `llc`. This produces `rustc.ll`, `llvm-scev.txt`, and
`llvm-machine.mir`. The tool reads LLVM functions, SSA operands, and block
successors through the pinned LLVM C API. It reads Machine IR function and
frame records as YAML. ScalarEvolution's text report still supplies trip
count candidates for the diagnostics. Symbolic counts naming an argument
are associated with the integer ABI register using the structured LLVM
signature. Loop annotations use RV64 branch predicates and register
transitions, including with LLVM hints disabled.

LLVM-derived return expressions and ranges are tried as output contract
candidates. If a return obligation is rejected or Lean cannot prove the
candidate, the tool can restore the original output contract and rerun both
checkers on the same linked ELF. Reviewed contracts are matched exactly and
are used directly when they match the original contract. The final artifacts
record the contract actually checked. The report's `llvm_result_fallbacks`
map identifies retried symbols and their initial failure reason.

Machine stack object ranges are reported alongside CFG-derived frame
annotations. The linked ELF supplies the instructions for the proof.
Machine IR is generated in a separate backend run. General mapping of
LLVM SSA values and non-affine recurrence inference are outside the
supported subset.

For scalar functions with word arguments, the tool can also reconstruct a
common affine result across LLVM returns from `add`, `sub`, and constant
`mul` or `shl` definitions. It can keep equal affine inputs at a `phi`, and
follow stores and reloads through a recognized local word-sized stack slot.
For acyclic control flow a slot value survives a join only if every incoming
path has the same affine value. Unknown stores and calls invalidate those
slot facts. Cyclic LLVM functions leave the affine return candidate unset.
Machine IR checks the `a0` return location, and the linked-image proof
checks the resulting postcondition. The `llvm_affine_locations` report
records RV64 registers and entry-SP-relative stack slots that compute the
same affine value as an LLVM SSA definition, including after a spill or
reload. The location analysis also runs for void functions and functions
with pointer parameters. Equal expressions may have multiple SSA names.
`scripts/rust-typed-trial/check-llvm-affine.sh` verifies a caller that needs
that equality to prove a buffer access, with MIR hints disabled.

`scripts/rust-typed-trial/check-compiler-hints.sh` compares an LLVM-derived
return bound used by a caller, a register-relative stack access, and a
MIR-derived slice-end relation with a run that disables the compiler-derived
candidates. The same test checks a fixed-trip loop with and without hints.

Run `scripts/rust-typed-trial/check-auto.sh` to exercise both fixture crates.
The fixtures use Rust ABI functions with mangled symbols, including a
two-buffer copy and a deliberately unchecked read.

## RV64 dataflow analysis

The annotation generator evaluates the reachable RV64 control-flow graph with
a worklist. The state combines exact affine register and word-memory facts,
unsigned intervals, upper bounds on register differences, power-of-two
congruences, and intervals for offsets from an input address. Equality and
unsigned branches refine the state on each edge, as do signed branches when
operand signs are known. A join retains bounds implied on every incoming edge.
Widening drops growing bounds at repeatedly updated targets of retreating
edges in reverse postorder, including in irreducible CFGs. Two narrowing
sweeps recover bounds by recomputing all incoming edges after widening. When
an add may wrap, the interval transfer drops the ordinary integer bound and
the congruence continues to hold modulo 2^64.

Memory and frame inference consume stabilized pre-instruction facts, including
in cyclic CFGs. Loop annotation generation also uses stabilized facts to retain
affine expressions at headers. Termination measures and the `inv` parameters
continue to use the recurrence analysis described below. The linked-image
checker validates the generated annotations.

With the release binary built, run
`scripts/rust-typed-trial/check-flow-fixedpoint.sh` to check that an access in
a cyclic CFG yields a raw-pointer requirement and a Lean proof, and that an
unchecked read behind a safe Rust signature is rejected as a bounds error,
for both a slice and a raw-pointer argument. It also checks that a bounded
register-derived offset yields the required byte range and alignment for
byte and word accesses without MIR hints.

### Horn reachability refinement

Pass `--chc-solver /path/to/z3` to refine raw-pointer requirements with bounded
Horn queries over the numerical RV64 CFG. Supported arithmetic is modeled as
64-bit bitvectors. Unknown register writes yield unconstrained values.
The generator excludes a conditional edge only when its query returns
`unsat`. It uses the ordinary CFG when the solver times out or its output
cannot be read. Reports include `chc_pruned_edges`, keyed by linker symbol.
Both checkers still verify the annotations against the original executable.
Run `scripts/rust-typed-trial/check-chc.sh /path/to/z3` to compare the verified
contracts with refinement, with the default analysis, and with an unavailable
solver.

## Loop evaluation

The analyzer builds a control-flow graph from optimized RV64 assembly and
finds natural loops using dominance. It projects the continuing branch
predicate through the entry and latch register states, including predicates
computed in temporary registers and guards before an unconditional back edge.
Fixed affine progress can yield a measure without LLVM hints. For a loop
with several back edges, the analyzer substitutes each candidate's register
equations into every latch transition and checks that the equations hold
after the transition and the measure decreases by a positive constant.
Different latches can have different positive decrements. For nested loops it forgets registers modified by inner loops
when inferring an outer recurrence. When incoming branches establish a common
nonzero slice length, it can preserve that fact with a `join` annotation.
The checker validates every proposed annotation against the machine code.

The stack analyzer tracks `sp` relative to its entry value on the CFG.
It recognizes one fixed nonzero allocation depth and translates both
direct and derived stack addresses into offsets in that frame. Direct
aligned word accesses can use slots. Aliased accesses and ranges lent to
direct callees use addressable byte ranges. The stack budget includes
selected direct callees. A proved stack budget is conditional on the
caller having that amount of space available.

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
invariant using that endpoint and its own remaining count. Backward
dataflow identifies incoming registers used in addresses, including through
copies and affine computations between the join and the access. At a labeled
join the generator can retain a varying address, along with a relation to
another register when all incoming value pairs lie on the same integer line.

Direct loads, stores, and already inferred direct
callees can generate fixed-size `ro` or `rw` raw-pointer requirements. The
checker validates the callee body and checks that callers can lend each
required range. The stack analyzer can make a fixed local range available
to such a call. Standalone raw-pointer entry points still require callers
to satisfy the inferred conditions. These conditions are emitted for Rust
`unsafe fn` entry points. A safe function taking a raw pointer receives an
address without a borrowed region. The report lists candidate requirements
by symbol and input register. Both the MIR adapter and the RV64 analysis can propose an affine footprint
with a runtime length. The RV64 analysis preserves branch bounds on entry
values when the registers holding them are overwritten, and substitutes
actual arguments when propagating demands through known direct calls.
An affine address can use several bounded inputs. The analysis keeps
unsigned comparison facts through boolean conjunctions and uses a
symbolic upper bound only when the CFG facts order the alternatives.
If one observed access endpoint covers the other endpoints for all
nonnegative inputs, the generator uses that endpoint. The checker still
validates every access and call. Incomparable symbolic endpoints and
indirect-call effects are outside these inference rules.

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
For a returned slice with an affine offset and length derived from an argument,
the tool proposes register-pair postconditions. When MIR cannot determine that
relation, the return is checked using unrefined machine words.

`--invariants FILE.json` maps a Rust type to length fields and their
backing array fields. For example:

```json
{"heapless::vec::VecInner": {"len": "buffer.buffer"}}
```

Discovery uses rustc's concrete field offsets and array capacities. For each
candidate word field it looks for a reachable store that increments the
original field value and whose CFG facts bound the stored value by the array
capacity. Field names carry no semantic meaning. The report records the
candidate and its witness method. Only mappings supplied with `--invariants`
produce entry and return conditions. For a mutable borrow, the checker
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

See [NoCompiler Rust-100](../../benchmarks/rust/README.md) for the
manifest-driven Rust benchmark and its pinned runnable selection.

Run `scripts/rust-typed-trial/measure.py` to reproduce the fixed selection.
It uses `heapless` 0.9.3 and `memchr` 2.8.3, plus local fixtures for Rust's
allocator/Box ABI and buffer analysis. It supplies no manual annotation or
invariant file. Each selected target contributes to the denominator,
including targets the current compiler integration cannot select. The
`coverage.json` output and per-run logs distinguish dependency functions,
wrappers that include dependency code, and standalone fixtures.
Pass `--no-mir-hints` to the benchmark to rerun the same target selection
with MIR candidates disabled.
Use `--llvm-hints` to compare LLVM candidate generation, or
`--entry-contracts DIR` to supply reviewed `<run>.json` signatures for every
run. The benchmark records the settings in `coverage.json`.

`proved` means the linked machine code meets its generated entry contract.
A generated collection invariant is visible in the per-run report and
remains an entry requirement. `proved_assuming` additionally requires the
listed external allocator contracts. This is a fixed capability benchmark;
its rates describe these targets.

The earlier fixed selection had 19 targets:

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
