# Tactics for process-level hand proofs: `lean/NoCompiler/Linux`

What a hand proof over `PReachK` (a function's run at the process level) writes mechanically, absorbed. All
of it is in namespace `NoCompiler.Linux`, imported by `import NoCompiler`. Round 7, C's row; companion of
[library.md](library.md) (the generic lemmas of `NoCompiler/Lib`, B's row). Written by hand (C); the measurements were taken locally on next (their logs are not in the repository), each converted proof checked.

## Stepping

| Tactic | Module | What it does |
| --- | --- | --- |
| `nocompiler_pwstep [facts]` | Run | one step (`PReachK.exec_step`), the facts as rewrite rules |
| `nocompiler_access using [lemmas]` | Run | a load's or store's side goal (`canRead`, `canWrite`, `aligned`): an assumption, a `using` lemma applied (its side conditions by `omega`, `rfl`, `decide`, or `Region.covers` unfolded and `decide`), also through `Perm.canRead_of_canWrite` |
| `nocompiler_run [facts] using [lemmas]` | Run | steps while a step applies, each access's side goal closed by `nocompiler_access`; an `if` a step left is reduced once the facts decide it |
| `nocompiler_run_n N [facts] using [lemmas]` | RunN | exactly `N` steps: for a proof cut at a point (a lemma, a call, an invariant applied there) |
| `nocompiler_prun_n N …` | RunN | the same over `nocompiler_pstep` (concrete states) |
| `nocompiler_runm …`, `nocompiler_runm_n N …` | RunMem, RunN | the steps also rewrite reads after disjoint writes (below) |

`scripts/gen/runify.py FILE.lean OUTDIR [THM…] --bounded [--step=pstep] [--whole=OUT --skip=THM…]` rewrites a
proof's `nocompiler_wstep`/`nocompiler_pstep` lines and permission `refine ⟨…, ?_⟩` lines into these calls (a
test file per theorem, or the whole file in place). Every output must be checked: merging gives each step its
block's facts, which can change the form a later tactic sees.

## Frames

| | Module | What it does |
| --- | --- | --- |
| `read{LE,16,32,64}_writeLE_disj` | RunMem | a read of `⟨q, k⟩` after a store to `⟨p, w⟩` sees the memory before, when the two are disjoint (any two regions: in place of per-pair helpers) |
| `nocompiler_disj` | RunMem | a `Region.Disjoint` goal (only such a goal) by `bv_omega` over the context's `Region.Disjoint` hypotheses |
| `nocompiler_reg_frame hq` | RegFrame | `(… setReg/setPc/setMem …).reg q = s.reg q` from `hq : q ∉ [written registers]` |
| `nocompiler_preserved [facts]` | RegFrame | `Preserved s s'`, the 15 callee-saved registers one by one |

For rewrites outside a run (`rw`, an epilogue's `simp`), B's `lib_rw` (`Lib/Rw`, `@[nocompiler_rw]`) closes
its side conditions by `decide`.

## Syscalls, calls, loops

| | Module | What it does |
| --- | --- | --- |
| `PReachK.writev`, `PReachK.readv`, `PReachK.read` | SysRun | an `ecall` with its progress, cases and `SysOk` inside; left: the run after each outcome (bytes accepted or stored; an error code), the kernel unchanged |
| `nocompiler_entry [facts]` | CallP | a callee's `Entry`, field by field |
| `nocompiler_call h a [facts]`, `… via hi` | CallP | `VerifiedProc.call` with the entry and the domain inclusion closed; left `?pre`, `?kont`. `via hi` uses `VerifiedProc.call_of_implies` (a library callee proved at a stronger spec) |
| `SpecP.Implies` (`.refl`, `.trans`, `.of_post`), `VerifiedProc.of_implies` | DischargeP | a theorem at one specification used at a weaker one (process level; D's `Discharge` is the machine level) |
| `nocompiler_loop I μ [from h]`, `nocompiler_back [facts]`, `nocompiler_exit` | LoopP | `PReachK.loop`: one trip from `x` with `hI : I x`; the back edge (the measure's decrease tried by the step simp set and `omega`); an exit |

## Measured (2026-11-22, in place: each converted theorem checked under its source file's own options, no `sorry`)

| | A's lines | converted |
| --- | --- | --- |
| 90 of 109 step theorems of 26 files of Examples/Libc (Libc/Musl's then at lean/NoCompiler/Libc/Musl, now Examples/Libc/Musl) (`runify.py --bounded`, `--step=pstep` for SlenProc and StdioWrite1) | 5194 | 4343 |
| after the guard (ea08523): 31 of 35 step theorems of Examples/Libc/Musl Memcpy3, StdioRead3, Fread1-3 and Examples/Libc Main, StdioExit, Stage2, StartC, StartMain, InitFini, InitLibc, InitTlsLoop | 2070 | 1657 |
| Examples/Libc/Musl Memcpy1-4, StdioWrite2-4, whole files (A landed them, 3b2e281, then under lean/NoCompiler/Libc/Musl) | 2728 | 2359 |
| `sw_ecall` with `PReachK.writev` | 57 | 49 |
| Memcpy2's register frames with `nocompiler_reg_frame` (4 theorems) | 311 | 293 |

Cost: until ea08523 the run tactics tried the permission split `refine ⟨?_, ?_⟩` after every step; on a goal
that is not a conjunction that attempt reduces the whole state (`il_end` step by step: a timeout at the default
heartbeats, against 5 s with `with_reducible (show _ ∧ _)` first). Since the guard, il_end, tl_iter4, mc_sloop1
and StdioRead3's `__stdio_read_verified` check at their files' default limits.

What did not convert before the guard (19 of the 109), and why: a merged run over the default heartbeats or recursion depth
(`__toread_verified`, `__stdio_read_verified`, `mc_sloop1-3`, `il_end`, `tl_iter4`: they check with the
limit raised, so `--heartbeats=THM:N` can bring them in); a later tactic that relied on the exact form of a
state (an epilogue `rw` that the merged facts already did: `sr_pos`); a branch whose condition the merged
facts leave undecided (`fr_mid`, `fr_sread`); and a few others (`il_aux_iter`: a side condition needing
`bv_omega` over unfolded definitions; `__syscall_ret_verified`: max recursion even with the limit raised).
The per-file lists were local run logs, not in the repository.
