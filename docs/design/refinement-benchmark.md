# Refinement benchmark: make a rustc-built function faster, and prove it (design; no runs)

**Status:** design only (QUEUE-B item 6). Nothing here has been run. Choices
that need the lead are listed at the end.

## The task

An episode gives the agent a RISC-V binary A built by rustc
(`examples/refine/targets`, docs/isa/refine-targets.md) and one function `f`
in it. The agent submits:

1. **A patch stack** (docs/toolkit/patch-stack.md) with `base` = A and patches
   that replace `f` (and nothing else, in this version). `nocompiler link
   STACK --check` rebuilds B byte for byte from the submission.
2. **A proof** `Refines sp A.f B.f`: on every entry `sp` allows, B's `f`
   behaves as A's `f`. A is the specification, and nobody writes a
   postcondition (docs/isa/refine.md). `Refines` includes `ARuns`, so A is
   known to run from those entries.

The score is A's simulated cycles over B's on the task's workloads, paid only
when the proof checks. A faster B with no proof scores 0, as does a proof of
an unchanged B.

## What `sp` is, and who writes it

- **Proposed: the task gives it.** Every task comes with A's `Verified M f
  spec` theorem (from `nocompiler_auto` or a committed proof). `sp` is that
  spec's `pre` and permission, and `ARuns.of_verified` gives `runs`. The agent
  proves only `rel`.
- This differs from swe-bin's proof bonus, where the agent writes the
  precondition (bench/swe-bin/README.md, option (b)). In an optimisation task
  the precondition is the attack surface: a narrower `pre` makes any B
  "correct". A fixed `pre` removes that, and with it the spec-mutation check.

## How the patch stack fits

- **Unchanged functions are free.** B differs from A only in `f`, which sits in
  `.swb`, with a jump at its old entry. Every other function keeps its `RFunc`.
  `Refines.of_sub_verified` and the chunked `Refines.of_groups` carry them
  with no stepping (docs/isa/ledger.md: 1234 of 1235 on the 7' artifact,
  about 55 s for the whole file).
- **What remains to prove.** `nocompiler status B --proofs A.nocompiler-proofs
  --lean OUT --form refines` (Q-VC3, docs/design/proof-status.md) writes the
  carried part and lists what remains: `f`, `edited`, plus its callers as
  `callee f` if they are in scope. In this version only `f` is scored.
- **The statement** relates A's `f` at its entry to B's `f` at its entry in
  `.swb`, on `f`'s domain (`_dom`: `f` and what it calls), as the swe-bin
  proof bonus does. The images are exported trimmed to the domain, since
  whole-binary exports do not fit 6 GB.

## Scoring

| step | tool | fails when |
| --- | --- | --- |
| rebuild | `nocompiler link STACK --check` | the result's SHA-256 differs |
| profile | `nocompiler check` on B | `f` is below L1 (the refinement tools work on trees) |
| differential | `nocompiler sim` A and B on the workloads | any output, exit status or trace differs (cheap, not a proof) |
| proof | swe-bin's `proofcheck.py` rules, with the statement restated by the checker and `sp` fixed by the task | it does not compile, or uses a forbidden construct or axiom |
| speed | `nocompiler sim --function f`, cycles (inorder5, labelled simulated) | B is not faster on the visible workloads |

Score = cycles(A) / cycles(B), summed over visible and hidden workloads,
when every step passes. Otherwise 0. The hidden workloads guard against a B
that special-cases the visible ones. The proof already rules that out on
`pre`, but the speed score would still reward it.

## Tasks: where they come from

Candidates are the L1+ functions in refine-targets.md's "For choosing
tasks" list: cobs decoders, httparse parsers, bytecount's naive loops,
crc32fast's small-update path, and the compiler-builtins `mem` functions.
The filter, to be measured (prep, not done):

1. `f` at L1 or above in A.
2. A `Verified` theorem for `f`'s domain exists or `nocompiler_auto` proves
   it. This is the binding constraint. swe-bin found no real task whose
   domain `nocompiler_auto` proves whole.
3. A workload that calls `f` enough for the cycle count to be stable, plus
   one simple known speed-up (by hand) as a sanity check that the task is
   solvable.

**Measured (2026-11-22)** on the 7' artifact, rebuilt with
`scripts/core/bench-scale-build.sh`, by `nocompiler check`. The domain is the
callees, transitively; loops are counted from `disasm`'s tree.

- Candidates: 22 (the `w_*` wrappers and the five `mem` functions).
- Fail (1), "`f` at L1+": 6 (`w_base64_encode` and the five memchr/memmem
  wrappers are L0).
- Pass (1) but not the domain: 11 of the other 16 reach an L0 callee.
  Examples: `memcpy`/`memmove` reach compiler-builtins' L0 copy helper,
  `w_cobs_*`, `w_httparse_request` and `w_crc32` reach L0 code. So
  refine-targets.md's "L1 or above" holds for the function but not for its
  domain.
- Domain all L1+: 5.
  - `bcmp` (leaf, 1 loop);
  - `memset` (leaf, 3 loops);
  - `w_cmp` and `w_eq` (call `bcmp`; 1 loop in the domain);
  - `w_fill` (calls `memset`; 3).
- (2) today: none of the 5 has a `Verified` theorem. lean/Examples/Libc's
  `memset_verified` is musl's, not this one. Each has loops, so
  `nocompiler_auto` needs an invariant per loop: a hand-written proof per
  task, not a run.

So a first task set is at most these 5, after proving `bcmp` and `memset`.
`w_cmp`/`w_eq`/`w_fill` then follow by the callee-spec pattern. Either way,
decision (c)'s fallback (`ARuns` as a hypothesis) is what would open the
other 11.

**Workloads as patch stacks; a sanity check (2026-11-22, simulated).** A
workload replaces `_start` by a patch (structured text with its own data
section). Every other function of A, `f` included, stays in place, so the
same patch goes on top of A and of B's stack.
- Example: `_start` calls `bcmp` 200 times on 256 equal bytes. B's `bcmp` is
  unrolled by two, with the same result on every input.
- inorder5 cycles in `bcmp`: A 410,803, B 334,403 (A/B = 1.23). Both exit 0.
  Instructions: 359,000 vs 282,600.
- `nocompiler status` on B against A's proofs: `bcmp` edited; its 5 direct
  callers are `callee bcmp`; 37 more name the nearest changed function they
  reach; 1192 carry.
- `nocompiler refine` refuses B ("a region has one exit"). The unrolled loop
  is not lockstep with A's, so this speed-up needs a hand proof of
  `Refines`. RefineAuto covers only edits that keep the loop's shape.
- On the way, two toolkit bugs were fixed. `refine` panicked on a change at
  a function's first instruction. `link` kept a replaced function's old
  `.nocompiler.struct` record, so B came out below L1 on bases that have a
  table.

A task file holds: A (built reproducibly by
`scripts/core/bench-scale-build.sh`), `f`, the spec name, A's proofs file,
the workloads, and the hidden workloads (outside the sandbox).

## The agent's tools

The swe-bin set, with `refine` added:
- `disasm` / `decompile` / `check` / `sim` on A and B;
- `link` (the stack);
- `nocompiler refine A B f --images IMG_A IMG_B`, which writes a certificate
  and a proof for lockstep-shaped edits (RefineAuto);
- `check_proof`;
- `submit`.

Limits are as in swe-bin (output 48 KiB, `check_proof` 3600 s).

## Decisions asked of the lead

- (a) `sp` fixed by the task, from A's `Verified` theorem (proposed), or
  written by the agent as in swe-bin's bonus.
- (b) The speed measure: simulated cycles (`inorder5`), reported as
  simulated, as the only measure for now.
- (c) Scope: one function per task, callers not scored. Task availability
  rests on (2) above. If too few functions pass it, the fallback is to give
  `ARuns` as a hypothesis, the way the ledger's reuse theorems take
  `Verified`. That changes what a score means, so it is the lead's call.
