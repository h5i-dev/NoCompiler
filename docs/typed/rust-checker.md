# The Rust checker (`crates/nocompiler-typed`)

What it is, how it maps onto the design note (`docs/Tab 1.md`) and the soundness proof
(`docs/健全性の証明.md`), and how it is tested. It is **trusted** until the Lean-verified
checker exists (decisions.md I2): "safe" means "accepted by this checker", and the ledger
says `checked`, never `proved`.

## Pipeline

```
FILE.s ──asm.rs──▶ functions, labels, annotations, data symbols
        ──sig.rs──▶ signatures with numbered variables (Var = index into one name table)
        ──check.rs─▶ per safe function: structure (S1–S5), one pass of the typing rules
        ──object.rs▶ (optional) the assembled object's words and data = what was checked (I15)
        ──ledger.rs / export.rs ▶ JSON ledger; Lean/JSON export for the Lean checker
```

`nocompiler-typed check FILE.s [--object FILE.o] [--ledger L.json] [--export-lean X.lean]
[--export-json X.json] [--states] [--loops natural]`. Exit 0 iff every safe function passes.

## The pass (check.rs)

- **Structure.** S1: the instruction set is what `isa.rs` (a copy of `Isa.lean`'s) parses;
  only `jalr zero, 0(ra)` among indirect jumps; branches stay in the function; calls go to
  functions with signatures. S2 (default): back edges = edges to a lower or equal address, to
  `inv` labels; loops = intervals, nested, entered at the head. P1 (`--loops natural`, a
  proposal): dominator back edges, reducibility, natural loops. S3: `sp` only by
  `addi sp, sp, ∓F` at the declared frame size; depth 0/F tracked in the state. S4: the
  `frame` clause's slots and address-taken ranges are checked when the signature is read.
  S5: no cycle among safe functions' calls.
- **State type** (the proof's D6): every register has an index expression (`Lin`, a fresh
  variable for `int`); facts Ψ with identities; slots Φ; capabilities C with identities
  (I12), guards, fields; frame depth. Capability validity facts (D2: `0 ≤ b`, `0 ≤ n`,
  `b + n ≤ 2^64`, field positions) are added to every query from C.
- **Order.** Points are visited in address order (S2) or a topological order (P1); a point's
  type is the join of its forward in-edges (I16), or, at an `inv`/`join` label, the
  annotation, which every in-edge is checked against (D7, `subtype`). Back edges are checked
  against the head with the edge's instantiation θ and the measure (T2). Loop-head fields
  and slots the body breaks are dropped by re-running (I13).
- **Rules → lemmas.**

| rule (check.rs) | note section | proof |
| --- | --- | --- |
| arithmetic, `urep`/`srep`, I23, I29 | 算術 | Lemma 1, 2 |
| branches (`2^64 ∣ e1 − e2`, representatives), contradictory edges dropped (I24) | 分岐 | Lemma 3 |
| `find_cap`, `load`, `store`, fields, I20 (u(a) retry) | メモリ | Lemma 5, 6 |
| `frame_move`, slots | フレームの能力 | Lemma 7 |
| `apply_call`, `match_caps`, `check_rw_disjoint`, exit fields, give/take | 呼出し | Lemma 8 |
| `ecall` with `syscall_sig` (I17, I31) | システムコール | Lemma 9 |
| `ret`, `tail_call` | 戻り, 末尾呼出し | Lemma 10 |
| `subtype` (D7), `build_point`, `back_edge`, measures | 合流とループ | Lemma 4, Theorem C |
| static data: implicit `ro` capabilities, `auipc`/`%pcrel_lo` (I30) | 静的データ | S6 |

- **Queries.** Every side condition is `Ψ ⊢ goal`, decided by `presburger.rs` (lazy DNF +
  Omega test over checked `i128`; overflow or budget = "not proved"). Syntactically equal
  expressions skip the solver.

## Tests

| test | what it checks |
| --- | --- |
| unit tests (`cargo test -p nocompiler-typed --lib`) | the solver against brute force on random small systems; parser, encoder (against llvm-mc encodings) |
| `tests/corpus.rs` | every `tests/typed/corpus/**/*.s` gets its `#! expect` verdict and rule (110 verdicts) |
| `tests/object.rs` | every corpus file assembled by clang equals the checked instructions and data (encoder cross-check) |
| `tests/exec.rs` | every accepted function (also under P1) runs 300× on an interpreter enforcing the signature's permissions from random signature-satisfying states, with contracts modelled at calls; no fault may occur. `tester_finds_the_known_holes`: the same interpreter faults on 7 rejected functions |
| `scripts/typed-trial/check.sh`, `scripts/musl-trial/check.sh` | the trial files against the objects compiled from C, then run under qemu |

What the tests cannot show: that no hole exists. The Lean checker (T) is to replace this
trust by a proof; until then `docs/typed/disagreements.md` records any case where the two
checkers differ.

## Speed (the note's failure condition 3, "検査が遅い")

Release build, one core, 2026-11-23, all 38 functions of `tests/typed/corpus` the checker
accepts: 46.9 ms in total, median 0.4 ms, slowest musl `memset` at 14 ms (80 solver queries).
Rejections are faster (they stop at the first failure). No query has hit the solver's budget
or `i128` overflow on the corpus. The 2^64 coefficients the note worried about (fresh
`u = e − 2^64·k`) have not been a problem at this size.
