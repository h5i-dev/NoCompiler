# The generator: design analysis (round 6)

**Status (round 9, 2026-11-23): a design document, not a description of the code.** What it proposes and
what exists on next:
- Implemented: the discharge lemma of section 2, item 3 (`VerifiedImg.of_implies`, NoCompiler/Discharge.lean,
  D 098a3a9; its process-level twin `VerifiedProc.of_implies`, NoCompiler/Linux/DischargeP.lean). In
  `Prove.py`: `--image`/`--lib` (library theorems as callee specs), the process route for functions with an
  `ecall` (`nocompiler_auto_p`), loops nested two deep and loops closed by a jump, and speed fix 1 of
  section 4 (no larger spec retried when the failure had no permission goal) (8e394ed and the commits before
  it). `nocompiler_auto_l2` (NoCompiler/AutoL2.lean) covers L2 functions without loops and without syscalls only.
- Not implemented (plans): the assume mode of section 2 (callee specs as hypotheses, per-caller assumptions),
  speed fixes 2-4 of section 4, the L2 route for loop functions and the loop templates of section 3, and
  the order of implementation at the end. The numbers are from the round-5 runs listed below (`--jobs 2`,
  before the one-Lean-process rule).

Owner: C. Reviewer: D. The lead reads this before implementation (round6.md item 1).

The generator turns a binary into per-function theorems: `Prove.py` (`lean/NoCompiler/VC/Bench`)
emits one Lean module per attempt, each proved by a tactic (`nocompiler_auto` on the machine,
`nocompiler_auto_l2` for L2 functions through T2/T3, `nocompiler_auto_p` at the process level),
trying a ladder of safety specifications. `nocompiler prove` (B) wraps check, export, the
generator and a report.

All numbers below are from these runs, taken locally (their logs are not in the repository):

| run | binary | generator | result |
| --- | --- | --- | --- |
| r5-slen | examples/elf/libc-slen.elf (40 functions, 21 L1+) | Prove.py on next 231837c | 6 proved |
| r5b-slen | same | every caller attempted (fix/Prove.py) | 6 proved, 31 attempted |
| r5c-slen | same, on A's `SlenImage` | A's library theorems as callee specs | 6 proved |
| r5-qdisc | fuzz_qdisc plain (111 functions, 68 L1+; sha256 a7ed3fa9...) | Prove.py on next 231837c | 27 proved |
| B's `nocompiler prove` | both | same generator, debug build | slen 6 of 40 (7 m 59 s), fuzz_qdisc 27 of 111 (94 min) |

Per-function outcomes were recorded per run (one row per function: outcome, reason, the profile check's
first violation), with each attempt's log; those files are local, not in the repository.

## 1. Every failure, by bucket

A failure is a **root** when the function fails for a reason of its own, and **cascade** when it
fails or is skipped only because a callee is not proved. Roots first; the cascade is section 2.

### fuzz_qdisc plain: 27 proved, 28 roots, 56 cascade

| bucket (root) | functions | example | what blocks it |
| --- | --- | --- | --- |
| unsolved goals, L1+ | 7 | `__syscall_ret` | callee postcondition needed (errno's address), then a register restored from the frame after a store through a pointer (needs the store to miss the frame) |
| outside the profile, R1 (floating point; atomics) | 8 (4 floating point attempted, 4 lock functions not attempted; 6 more above them in the cascade) | `scalbn` (`0xd105b787`), `__lockfile` (atomics) | no semantics for F/D and A instructions: explore ends `⊢ False` |
| timeout (300 s) | 5 | `get_meta`, `memcpy` | path count (joins) and per-attempt cap |
| (of the 7 above) syscall without a step in the model | 3 (+ callers) | `__block_all_sigs` (`rt_sigprocmask`) | `Env.Sys` has read/write/exit only; lead 16:14: process route (`nocompiler_auto_p`), which needs the syscall's spec |
| call to a size-0 assembly symbol (R2) | 2 + 2 not attempted | `__do_init` | loader (B's branch `b-loader-size0`) |
| indirect call (R2) | 1 + 11 in the cascade | `call` (`jr`) | calls through pointers (branch wip-dyn: vtable hypotheses) |
| unstructured loop (R3) | 2 | `memchr`, `__divtf3` | jump into a loop: no tree; explore over the CFG with cut points works when the loop heads are found |
| loops and calls together, nested loops | 2 + (bucket 21 loop functions) | `main`, `alloc_slot` | generator selection; landed by B (loops+calls), nested loops on next-c |
| loop closed by `j` (exit syscall) | 1 | `_Exit` | next-c: invariant True, measure 0 |

The rows sum to 28 (the syscall row is a subset of the unsolved-goals row).

### slen: 6 proved, 12 roots, 22 cascade (r5b)

| bucket (root) | functions | example |
| --- | --- | --- |
| R1 atomics (`__lock`, `__unlock`, `__lockfile`, `__unlockfile`) | 4 | `__lockfile` (`0x1607a52f`, `lr.w`) |
| unsolved goals | 4 | `__syscall_ret` (as above), `__libc_start_init` (indirect call) |
| timeout | 2 | `memcpy` (261 instructions, R3), `__libc_exit_fini` |
| `_Exit` (loop closed by `j`, exit syscall) | 1 | `_Exit`: next-c admits it (invariant True, measure 0) |
| `__init_tp` (call to `__set_thread_area`, size 0) | 1 | loader |

Same roots, smaller binary. slen has no floating point; its indirect calls are in stdio and the
init/fini arrays (`__libc_start_init`, `__stdio_exit`, `fread`, `__fwritex`).

## 2. The cascade: prove a caller assuming its callees' specs

Section written with D (D owns its implementation: Prove.py's assume mode and the discharge).

The two counts of roots differ by definition, not data: section 1 classifies C's r5 runs, where
every caller is attempted (r5b) or the generator selects callers whose callees it attempts, so a
"loops and calls" or "nested" function is cascade when its callee failed; B's runs did not attempt
those, so D counts them as roots. Either way the cascade is about half the unproved functions and
a handful of roots block it.

### Measured (D, scripts/gen/cascade.py on B's `nocompiler prove` runs)

`scripts/gen/cascade.py ART.lean REPORT.md` on B's `nocompiler prove` runs (tmp-b/np-qdisc, tmp-b/np-slen):
a function's call closure is its export `_dom`; a failure is a ROOT if its outcome is its own, CASCADE if
the outcome is about a callee.

| binary | functions | proved | unproved | roots (own failure) | cascade (a callee) |
| --- | --- | --- | --- | --- | --- |
| fuzz_qdisc plain | 111 | 27 | 84 | 47 | 37 |
| slen | 40 | 6 | 34 | 20 | 14 |

Every cascade function has a root below it. A few roots block most of them (count = unproved functions
whose closure holds the root):

| fuzz_qdisc root | own outcome | blocks | | slen root | own outcome | blocks |
| --- | --- | --- | --- | --- | --- | --- |
| `__syscall_ret` | unsolved goals | 26 | | `memcpy` | timeout 300 s | 9 |
| `memcpy` | unsolved goals | 22 | | `__lockfile` | loops nested / 2 back edges | 8 |
| `__lock` | loops nested / 2 back edges | 19 | | `__syscall_ret` | unsolved goals | 6 |
| `__unlock` | loops nested / 2 back edges | 15 | | `__lock` | loops nested / 2 back edges | 6 |
| `memset` | unsolved goals | 14 | | `__stdio_exit` | loops and calls | 4 |
| `__lockfile` | loops nested / 2 back edges | 11 | | `__init_tls` | loops and calls | 3 |
| `__fe_getround`, `__fe_raise_inexact`, `__extenddftf2` | unsolved goals | 10 each | | `__unlockfile`, `memset` | | 3 each |

Six functions (`__syscall_ret`, `memcpy`, `memset`, `__lock`, `__unlock`, `__lockfile`) block most of the
cascade on both binaries; A proved all six by hand for slen (Examples/Libc). C's r5c (slen with A's library
theorems as callee specs) gained nothing, for a tactic reason (ra/s0 restored after the store to errno,
STATUS-C 17:18), not for lack of specs.

### Design (D)

1. **Assume, then discharge.** Today a caller is attempted only when every callee already has a theorem
   (`Prove.py`: `done`, `--lib`). Instead: for a callee `g` with no theorem, the caller's theorem takes
   `(hg : VerifiedImg code g_dom g_entry sp_g)` as a hypothesis and passes it in `calls [hg]` (the form of
   `_start_c_verified`, Examples/Libc/Slen.lean). The run records, per function, the assumptions it was
   proved under. A theorem with no remaining assumption counts as proved; one with assumptions counts as
   "proved assuming callees" (round6.md's second metric).
2. **Which `sp_g`.** (a) The library's spec, where the library has `g` (functional: `memcpySpec`, `errnoSpec`,
   ...): strongest for the caller. (b) Otherwise the generated safety rung (`safe`, `anyread`, `anymem`,
   `alignargs`, ...), the strictest the caller's own spec allows (a callee's permission must lie in its
   caller's, as today). A rung says nothing about results, so a caller whose safety depends on what a callee
   returns (a pointer from `__errno_location`, a buffer from `malloc`) needs (a): this is where a missing
   library spec shows up as a caller failure, and the doc should count those separately.
3. **Discharge.** When `g` is later proved at `sp'`, a caller's assumption at `sp_g` is discharged if `sp'`
   implies `sp_g` (weaker precondition, stronger postcondition and permission inside). Needs one lemma,
   `VerifiedImg.of_implies`, and its process-level twin (both on next since round 7: see the status above).
   The call graph is acyclic in v1, so discharging bottom-up terminates; a cycle (recursion) is out of reach
   of this scheme and reported as such.
4. **Per build.** On fuzz_qdisc (another musl build than slen), library specs are usable as assumptions
   unchanged; their discharge needs a proof of the same function in this build (lead 16:25: spec reuse,
   proof regenerated per build; byte-identical functions reuse the proof).

### To measure before implementing (D)

Assume mode on both binaries: (i) functions proved assuming callees, with rungs only; (ii) the same with A's
library specs for the six roots above; (iii) how many of (i)/(ii) fail because the caller needs a callee's
result (rung insufficient). This is D's side of the implementation (round6.md 2).

### What the checkpoint can count

Whole automatic proofs <= proved + cascade functions whose every root below is proved. Assume mode makes
the cascade attemptable, but a cascade function counts as whole only when its roots are. The six roots
that block most of both cascades (`__syscall_ret`, `memcpy`, `memset`, `__lock`, `__unlock`, `__lockfile`)
all have A's hand proofs on slen. **Question for the lead:** does a callee assumption discharged by a
library theorem (a hand proof of the same build) count as "automatic" for the checkpoint? If not, slen's
whole proofs stay below the functions above `__lock`/`__unlock`/`__lockfile` (atomics, R1: the generator
cannot prove them), whatever the generator does elsewhere.

### Spec choice (C)

A caller can only use what its callee's spec says. The caller's unsolved goals name what it needs:
a `perm_` goal at a call means the callee's permission is not inside the caller's (pick a smaller
rung for the callee and re-prove it there); a goal about a register after the call (an alignment,
a bound) means the caller needs the callee's result (a library spec, D's 2a, or a generated
postcondition, none today). r5c is that second case: errnoSpec was there, and the caller then
failed on the frame (section 3, item 1).

## 3. Loops

**Today.** An invariant per loop head guessed from its back edge: the branch's condition
(`a ≠ b`, `a < b`) or True, and a measure from the compared registers (four variants: direction
x invariant). Nested loops (next-c): lexicographic measure over two levels. The frame (saved
registers, sp) is added by `nocompiler_auto` itself; for L2 functions it comes from T2 for free.

**Measured.** fuzz_qdisc: 29 functions with loops; 21 of them were outside the selection
(nested, or more than one back edge; next-c admits 12 of them, test r5n queued). Of the loop
functions attempted, the failures are: `memset` (alignment after rounding the pointer up:
lemmas `aligned_roundup4w/8w` proved, closer on wip-dyn, test r5m queued), `memchr` (a saved
register through a loop with a word-at-a-time load: frame), `memcpy` (timeout, 16 attempts x
~200 s: the variants are retried at every rung). No loop failed for want of a better arithmetic
invariant so far: the failures are frame, alignment and cost.

**Next, in order of measured need:**
1. the frame from T2 (the L2 route) for loop functions that store through pointers (`memchr`,
   `__syscall_ret`'s family): no symbolic memory reasoning about the frame at all;
2. invariant templates from the loop's induction registers: `p = p0 + 8*i`, `n = n0 - i`
   (memset/memcpy/memchr shape), from the back edge's register updates (a small analysis of the
   loop body, not abstract interpretation yet);
3. abstract interpretation over the CFG (intervals and congruences of the induction registers)
   only if 1-2 leave loop functions failing on invariants; to be measured after them.

## 4. Speed

**Measured.** Wall time: slen 7 min, fuzz_qdisc 36 min in my runs (`--jobs 2`; B's 94 min was a
debug build with the 300 s cap). fuzz_qdisc: 98 attempts on 48 functions; elaboration (from the
attempts' profiles) 21.2 min, of which 17.8 min on functions that failed; plus 5 timeouts (25 min
of wall at the cap). Import per attempt: median 1.9 s (3.0 min in all). Peak memory 1.5-1.7 GB,
3.4-3.6 GB for `__do_init`/`__do_fini`.

So the time is failures retried: `memchr` 507 s over 16 attempts, `memset` 289 s over 16 (4
measures x 4 rungs), `memcpy` 16 attempts.

**One configuration for the metric's time** (from now on, every change): release build of `nocompiler`,
`Prove.py 0 --calls --loops --specs safe,anyread,anymem,alignargs` (the default `--jobs 1`: since round 7 an
agent runs one Lean process at a time; the round-5 runs used `--jobs 2`), 6 GB and 300 s per Lean run, one
job per agent in a slot, wall time from the run's first to last timestamp. B's 94 min (debug
build) and my 36 min are not comparable; the baseline is re-run in this configuration with the first
change.

**Fix.**
1. Do not climb the ladder when the failure has no permission goal (a larger spec cannot help):
   next-c (the `perm_` case check).
2. One Lean process per function, not per attempt: the attempts as `first | ... | ...`
   alternatives inside one module, with heartbeat budgets, or the attempts as separate theorems in
   one file (saves the import and image load, 2 s each).
3. Timeouts: a lower first cap (60 s), and the 300 s cap only for a function whose first attempt
   was cut off with goals left that a rung could change.
4. With the cascade broken (section 2) every function's attempts are independent: `--jobs` scales
   to the machine (the 15 GB machine fits 6 at 1.7 GB).

## 5. Out of reach of a per-function generator

- **R1 instructions without semantics** (F/D floating point: 4 of fuzz_qdisc's functions and 6
  callers above them; A atomics: the 4 lock functions in each binary). Nothing to prove against until
  the ISA model has them. Alternative: model the A instructions used (`lr`/`sc`, `amoswap`) for one
  hart (A's `__lock` proof already avoids them on its path by `need_locks = 0`), and floating point
  as opaque values (registers and fcsr), which most of these functions only move around.
  Or take the Lean LPS port's executor for those instructions (lean/LPS/Riscv, RV64GC, tested against
  qemu; docs/design/lps-bridge.md) into NoCompiler's machine: a trusted-base change for the lead, and the
  bridge's simulation then needs those cases too (D).
- **Calls through pointers without a known callee**: a per-function theorem can only assume a spec
  for the target (wip-dyn); which function is called is a property of the whole program (the
  vtable's contents), discharged by A's composition, not here.
- **Syscalls the model does not step**: the process route is per function, but each new syscall is
  a spec to port (D, LPS).
- **Specifications**: everything above is safety (returns, ABI, memory). Functional properties
  (what `memchr` returns) are the composition's job; the generator's specs are what the composition
  can use only when they are the library's.

## Order of implementation (proposal)

1. The cascade (section 2): callee specs as hypotheses, discharge step; metric both numbers.
2. Speed 1-3 (section 4): needed to run 1 often.
3. The L2 route for every L2 function, with an off-stack rung (frame from T2): `__syscall_ret`'s
   family, `memchr`.
4. Loop templates (section 3, item 2), then re-measure loops.
5. Calls through pointers (wip-dyn) and the process route's syscall specs (D). The user's decision (4)(a)
   (fd arguments as the low 32 bits in NoCompiler/Linux, branch next-d-fd32, not built yet) may require
   re-checking process-route proofs built before it lands.
   The assume mode keeps assumptions per caller, not one spec per callee: re-proving a callee at a
   smaller rung for one caller must not invalidate another caller's (D).

Split: C the tactic side (3, 4, the L2 route), D the spec/cascade side (1, the discharge step,
syscall specs); 2 whoever is free.
