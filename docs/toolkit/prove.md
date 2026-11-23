# `nocompiler prove`: from a binary to its theorems, and a report of the rest

```
nocompiler prove ELF --work DIR [--spec safe,anyread,anymem,rodata,offframe,alignargs] [--jobs N]
    [--only NAME,...] [--root REPO]
```

`--only` proves just the named functions and their callees, each caller needing its callees'
theorems; the report still lists every function.

One command (round 5, item 5). It runs what already exists, in order, and writes everything
into `DIR`:

0. **library**: `lake build NoCompiler` in the repository's `lean/` (nothing to do when it is
   current; `lake.log`).
1. **check**: the profile check of every function, giving its level and, for one below L1,
   its first violation.
2. **export**: the chunk image of the whole binary, compiled once
   (`lean/NoCompiler/VC/Bench/Art.py ELF DIR 0`: `Art.lean`, `ArtImg.olean`).
3. **generator** (`Prove.py DIR 0 --specs LIST --calls --loops`): for each function it can
   take, one module `Q<k>_<spec>.lean` with a `VerifiedImg` theorem proved by
   `nocompiler_auto`, at the first specification of `LIST` that proves it. Callees come before
   their callers, and a caller uses its callees' theorems. Each Lean run is capped at 6 GB and
   300 s.
4. **report**: `REPORT.md` (totals, outcomes by reason, every function) and `report.json`
   (one object per function: `name`, `instructions`, `level`, `outcome` = `proved` /
   `failed` / `not_attempted`, `detail` = the specification, or the reason).

The exit status is 0 when every function is proved, and 1 otherwise. A step that fails stops
the command and names its log (`art.log`, `prove.log`).

## What "proved" means

A row `proved (safe)` means the module `Q<k>_safe.lean` compiled. That module proves
`VerifiedImg code F_dom F_entry specSafe` about the binary's own image. The specifications are
safety specifications (Prove.py's header gives each one): from any entry the specification
allows, the function returns, preserves the ABI, and touches only the memory the
specification names. They say nothing about the function's result. A property of the whole
program (A's composition, round 5 item 2) is not a step yet. `--spec` chooses among the
safety specifications only.

## Reasons a function is not proved

- **not attempted**, with the generator's reason (the strings `Prove.py` writes):
  - "no _dom (a callee failed the profile check)";
  - "a callee is not one the generator attempts";
  - "loops nested, or a loop with more than one back edge to its head";
  - "not among the N largest leaves" (when the generator is told to take only the largest);
  - "loops (run without --loops)" or "calls (run without --calls)" when those options are off.
  Loops and calls together are attempted (callees first, the loop's back edges with invariants).
- **failed**: the generator tried every specification. The reason is Lean's first error for
  the last one, or `timeout (300 s)`.

## Measured

`examples/elf/libc-slen.elf` (40 functions, 1,785 instructions; 21 at L1 or above), `--jobs 2`,
2026-11-22, load about 5: 7 m 59 s. 6 functions are proved (28 instructions): 5 at `safe`, 1 at
`alignargs` (`__towrite`).

| outcome | functions |
| --- | --- |
| proved | 6 |
| not attempted: a callee is not one the generator attempts | 10 |
| not attempted: loops and calls together | 10 |
| not attempted: nested loops, or a loop with more than one back edge | 5 |
| failed: a callee is not proved | 4 |
| failed: unsolved goals (e.g. `memset`: writes through a0 under `safe`; `offframe`, added to the default since, is the specification for it) | 3 |
| failed: `decide` (`__init_tp`) | 1 |
| failed: timeout (300 s, `memcpy`) | 1 |

`fuzz_qdisc.plain.elf` (examples/qdisc, a7ed3fa9...; 111 functions, 8,951 instructions; 68 at L1
or above), `--jobs 2`, load 4 to 9 (another agent's Lean jobs alongside): 94 min. 27 functions
are proved (799 instructions): 23 at `safe`, 2 at `anymem`, 1 at `anyread`
(`reac_qdisc_etf_catchup_slots`), 1 at `alignargs`. C's own measurement of the same build gives
27 too (STATUS-C, 15:58).

| outcome | functions |
| --- | --- |
| proved | 27 |
| not attempted: a callee is not one the generator attempts | 21 |
| not attempted: loops and calls together | 21 |
| failed: a callee is not proved | 16 |
| failed: unsolved goals | 16 |
| not attempted: nested loops, or a loop with more than one back edge | 5 |
| failed: timeout (300 s) | 4 |
| failed: killed (exit -15, `__divtf3`) | 1 |

Both runs predate the loops-and-calls selection (C's, in its own Prove.py) and the `offframe`
default.
