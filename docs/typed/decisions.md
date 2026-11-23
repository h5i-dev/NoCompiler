# Typed RISC-V: implementation decisions

The spec is `docs/Tab 1.md` (design note v0, "the note") and `docs/健全性の証明.md`
("the proof"). This file records every reading the implementation takes where the two
are silent, ambiguous or disagree, and every place it departs from them. Where the
note and the proof differ, the proof's reading is taken. Numbered I1, I2, ... so code
comments can cite them.

## Scope and trust

- **I1 Solver.** Note decision 5 says the Rust checker uses an existing SMT solver.
  The implementation brief asks for no external solver dependency unless clearly
  justified, so the checker has its own decision procedure for quantifier-free
  Presburger arithmetic (`crates/nocompiler-typed/src/presburger.rs`): DNF of the
  negated goal, divisibility and non-divisibility turned into equations with fresh
  variables, exact equality elimination, and the Omega test (real and dark shadow,
  splinters) for inequalities. Arithmetic is on `i128`; any overflow answers
  "not proved", which is sound (the checker rejects). The procedure is trusted until
  the Lean-verified checker exists; every query is written to the ledger so it can be
  replayed (by `omega` in Lean, later).
- **I2 The checker is trusted.** Until the Lean-verified checker exists, "safe" means
  "accepted by `nocompiler-typed`". The ledger says `checked`, never `proved`, for such
  a function.
- **I3 Structural rules.** The note says "control and stack shape use the current
  R1–R6". The old structured profile (block/loop trees, `.nocompiler.struct`) was
  removed with the old core crate. The typed checker checks the properties the proof
  actually uses, S1–S6, directly on the assembly text:
  - S1: only instructions of the profile (RV64IM + Zba + Zbb, no C); jumps and branches
    go to labels of the same function or to function entries.
  - S2: an edge to a lower address must go to a label annotated with `inv`; for each such
    head L, its loop is the address interval from L to its last back edge; loop intervals
    are properly nested; no edge enters a loop interval except at its head.
  - S3: `sp` is written only by `addi sp, sp, k`; the first such write is the prologue
    `addi sp, sp, -F` with F the declared frame size, a multiple of 16; the depth at each
    point is 0 or F, unique; returns and tail calls happen at depth 0.
  - S4: the frame declaration (I8) lists 8-byte slots at multiples of 8 and address-taken
    ranges; they do not overlap and lie in `[0, F)`.
  - S5: the call graph of the checked file (safe functions) has no cycle.
  - S6: static data is not in v0 of the implementation (I14).

## Syntax (provisional, note decision 6)

- **I4 Where annotations go.** Annotations are assembler comments starting with `#:` so
  the same file goes unchanged to `clang`/`llvm-mc`. Note decision 6 wanted directives
  lowered by the assembler into `.nocompiler.struct`; that needs an assembler of our own
  and is postponed. The checker then compares the assembled object's `.text` with its
  own encoding of the instructions it checked (I15), so what is checked is what runs.
- **I5 ASCII and Unicode.** `↦`/`|->`, `∣`/`|` (divides), `≤`/`<=`, `≥`/`>=`, `≠`/`!=`,
  `∧`/`&&`/`,` in `where`, `∨`/`||`, `¬`/`!`, `⇒`/`=>`, `−`/`-`, `·`/`*`, Greek letters in
  identifiers. `2^64` and other powers of two are literals.

## Signatures and their meaning

- **I6 Exit fields of a borrow.** The proof's Q3 speaks of "the fields of the signature's
  exit side" without giving syntax. A borrow may write `{…} -> {…}`: entry fields, then
  exit fields. Without `->` the exit fields are the entry fields (the same thing comes
  back).
- **I7 Preserved registers.** The note's return rule lists `ra`, `sp`, `s0`–`s11`. The
  Lean `Preserved` (used by `VerifiedImg`) also has `gp` and `tp`. The checker requires
  `gp` and `tp` unchanged too, so ⟦σ⟧ can be stated with the existing `Spec.Done`.
- **I8 Frame declaration.** R6's metadata is replaced by a signature clause
  `frame F slots k1, k2, … addr [o1, l1), …`: the prologue lowers `sp` by F; slots are
  8-byte save slots at offsets from the lowered `sp`; `addr` ranges become `rw`
  capabilities right after the prologue (note, "フレームの能力"). Without the clause the
  function has no frame (F = 0).
- **I9 Exit on `exit`.** "exit で終了した場合は…終了したことだけを言う": `onExit` is
  `True` in the Lean meaning.
- **I10 Tokens in Lean.** A token's footprint is a finite list of regions (not an
  arbitrary set), so that it can be part of a `Perm` (which is lists of regions). Its
  invariant is a predicate on (footprint, memory), with a proof that it depends only on
  the bytes in the footprint (U1). Footprints of entry tokens are parameters of ⟦σ⟧ (chosen
  with the valuation); footprints of returned tokens are existential.
- **I11 Valuation.** Index variables are natural numbers (cheap to compare when the Lean
  kernel evaluates the checker); a valuation is `Nat → Int`. Names are for display only.
  `int` without an index in a signature is sugar for a fresh variable.
- **I12 Capability identity in the checker.** The return check matches each `borrow`
  obligation to the capability that came from that clause at entry (by identity), not to
  any capability with a provably equal range. This is stronger than the proof's
  one-to-one matching and makes Lemma 10's Pool argument immediate.
- **I13 Loop heads.** The head's state: annotated registers take the annotated types;
  registers written anywhere in the loop interval (including caller-saved registers
  clobbered by a call in it) and not annotated become `int`; other registers keep their
  entry expressions. Facts: those of the entry edge plus the annotation's `where`.
  Capabilities: those of the entry edge. Fields and slots that the body may change are
  dropped at the head: the checker first tries with all of them and drops those the back
  edge cannot re-establish, until it is stable (only drops, so it terminates). This only
  affects which programs pass, not soundness: every back edge is still checked against
  the head's type (D7).
- **I14 Static data** (`auipc`/`addi` to a symbol, `ℓ_sym`) is postponed; a function using
  it is rejected for now.
- **I15 Text versus object.** `nocompiler-typed check --object FILE.o` compares the
  object's `.text` words with the encodings of the checked instructions (relocations
  for `jal` to other functions resolved by the object's relocation entries, when present).
- **I16 Join.** Forward joins keep a register's expression when it is syntactically equal
  (after normalisation) on every incoming edge, and a fact when every incoming edge has
  it (facts carry identities). Capabilities are kept when every incoming edge has the
  same capability (identity); fields when equal on all edges. Note decision 2.
- **I17 Syscalls.** `ecall` needs `a7` provably constant and one of 63, 64, 93, 94. The
  signatures are the note's. `93`/`94` have no successor in the checker (the run ends).
  Registers other than `a0` are unchanged.

## Lean side

- **I18 Decision 10** is implemented by redefining `Perm.canRead`/`canWrite` byte by byte
  (`∀ i < n, readable (a + i)`); the old one-region form is kept as a lemma
  (`canRead_of_covers`), so proofs that used it only change the name of the lemma.
- **I19 Total meaning first.** ⟦σ⟧ is `VerifiedImg c D entry (σ.spec Tok)`: the existing
  total judgment. The partial judgment is added only when a `partial` function is needed
  (note decision 1).

## Rust checker (agent U)

- **I20 Access address modulo 2^64.** The memory rule asks `b ≤ a ∧ a + w ≤ b + n ∧ w ∣ a`
  for `a = e_rs + c`. When that fails, the checker retries with `u(a)`, the unsigned
  representative (fresh `x`, `k`, `a = x + 2^64·k`, `0 ≤ x < 2^64`), which is the actual
  address by the proof's Lemma 1. Needed for `bgeu i, n` bounds checks on an index `i`
  about which nothing else is known: `ρ + i` is then only known modulo 2^64. Sound: Lemma 5
  only uses that the word's unsigned value lies in the capability.
- **I21 `call`/`tail` pairs.** clang emits `call f` / `tail f` as `auipc t, %pcrel_hi(f)`
  + `jalr rd, %pcrel_lo(f)(t)` (two words, `R_RISCV_CALL_PLT`). With `-mno-relax` this pair
  is what runs. The checker types the pair as one call (`rd = ra`) or tail call
  (`rd = zero`, `t = t1`) of `f`, with `t` clobbered; the Lean side sees two instructions
  whose combined effect is a jump to `f`'s address after linking. The object comparison
  (I15) checks the pair against the relocation's symbol. Hand-written `jal ra, f` is the
  one-word form.
- **I22 The note's `read_sum` and S2.** As written in the note, `fail:` jumps back to `out:`,
  a backward edge to a label that is not a loop head. S2 (note and proof) forbids it, so the
  checker rejects the literal example (`tests/typed/corpus/note_read_sum.s`, rule `cfg`); with
  the error block before the join it is accepted (`note_read_sum_fwd.s`). S2 is kept: it is
  what Theorem C's termination argument uses.
- **I23 Arithmetic rules beyond the note's table** (all instances of "any register may be
  weakened", so they only widen what passes): constant folding with the reference
  evaluator when every operand is a syntactic constant; `xori rd, rs, -1` is `int(−1 − e)`;
  `andi` with `c = 2^k−1` gives `e = x + 2^k·j` (note), with `c = −2^k` gives
  `x = u(e) − (u(e) mod 2^k)`, with a single bit `c = 2^k` gives `x = 2^k·bit` where `bit` is
  bit k of `e`; `and` with a constant operand is `andi`; `slt[i][u]` give `x ∈ {0,1}` with
  `x = 1 ⇔` the comparison of the representatives; `min[u]`/`max[u]` also give
  `x = u1 ∨ x = u2`; `divu`/`remu` by a constant `c > 0` give `u(e) = c·q + r`;
  `srai` uses `s(e)`; `slliw`, `mulw` by a constant, `addiw` use the 32-bit rule;
  `add.uw`/`shNadd.uw`/`slli.uw`/`zext.h` use zero-extension facts; `clz`/`ctz`/`cpop` give
  `x ≤ 64` (or 32); `lui` is a constant.
- **I24 Contradictory edges.** A branch edge whose facts are contradictory is not followed
  (it is never taken). Sound: no state satisfies the edge's type.
- **I25 Conditional capabilities.** A guarded capability `ψ ⇒ c` is used where Ψ ⊢ ψ and
  then held unguarded from that point. At a join where guards differ, the guard becomes the
  conjunction (a weaker capability, valid on every edge).
- **I26 Stack default.** A signature without `stack` has `stack 0`.
- **I27 Lending.** A held capability can serve several `ro` clauses of one call; a `rw`
  clause served by the same capability as another clause must be provably disjoint from it
  (note step 3). `take` and token clauses use a capability exclusively. A clause whose
  length is a bare unknown variable takes the length of a held capability with the same
  base (the note: "n は能力の照合から決まる").
- **I28 Loop-head constraints on back edges.** The back-edge check proves θ(fact) for every
  fact of the head that mentions a variable bound at the head, even when the edge inherited
  the fact itself: the inherited one is about the current iteration. (An early version
  skipped them — unsound; regression test `neg_loop_inv_back.s`.)
- **I29 Bitwise operations** (asked for by the musl trial; facts about the operations, not
  about musl): `and`/`or`/`xor` of two values provably in {0, 1} are exact (a four-case
  disjunction); `or`/`xor` with a constant `c` are `u(e) + c` when Ψ proves the other
  operand's bits disjoint from `c`'s (`u(e) < 2^tz(c)`, or `2^bitlen(c) ∣ u(e)`); the fresh
  result `x` of `xor a, b` remembers `(a, b)`, and `andi x, 2^k − 1` then also gives
  `r = 0 ⇔ a ≡ b (mod 2^k)`. Sound: (a xor b) mod 2^k = (a mod 2^k) xor (b mod 2^k), which is
  0 exactly when the two residues are equal.
- **I30 Read-only static data** (replaces I14 for read-only symbols; the note's 静的データ).
  Every label in a read-only data section (`.rodata*`, `.srodata*`, or a `.section` whose
  flags lack `w`) is a data symbol with a variable ℓ_sym (its address after linking, S6) and
  the bytes the source gives (`.quad`, `.word`, `.half`, `.byte`, `.zero`, `.ascii`, …; a
  symbol reference is an unknown byte). Every function implicitly holds
  `ℓ_sym ↦ bytes[size] ro` with a field for each known 8-byte word at a multiple of 8 (when
  the symbol is 8-aligned), and `align ∣ ℓ_sym` (the offset's alignment, capped by the
  section's). `auipc rd, %pcrel_hi(sym)` gives `int(ℓ_sym − L)` and an instruction with
  `%pcrel_lo(label)` (addi, loads, stores) uses the variable `L` of the auipc at `label` as
  its immediate, so the pair yields exactly ℓ_sym whatever the linker's split; `L` has no
  facts. Writable data (`.data`, `.bss`, …) stays unsupported (the note passes it through
  signatures from `_start`): an auipc to it is rejected (`static-data`), as are other
  relocation operators. The object comparison (I15) also compares the data bytes.
  **For ⟦σ⟧ (T):** the meaning must then include, on entry, that each read-only symbol's
  range is readable in the permission, holds its bytes, and is disjoint from every `rw`
  capability and token footprint (P4/P5 extended to the implicit capabilities).
- **I32 Writable static data through signatures** (the note: "書込み可能なデータの能力は
  `_start` の署名に現れ、そこから署名を通して受け渡す"). Every data symbol, read-only or not,
  has its address variable ℓ_sym, written `@sym` in annotations; every function may assume
  `0 ≤ ℓ_sym`, `ℓ_sym + size ≤ 2^64` and `align ∣ ℓ_sym` (S6). `auipc %pcrel_hi(sym)` works for
  writable symbols too, but they have no implicit capability: an access needs one lent by the
  signature, e.g. `borrow @data ↦ bytes[40] rw`, passed on to callees as any other.
  **For ⟦σ⟧ (T):** `@sym` in a signature is the linked address (a constant of the image, not
  a parameter); P4/P5 apply to such capabilities as to any other.

## Proposals (not adopted: the default checker does not use them)

- **P1 Natural loops instead of address intervals** (from the musl trial, docs/typed/musl-trial.md
  "Stage 2"). S2 asks that every edge to a lower address goes to an `inv` head and that loops
  be nested address intervals entered at the head. clang's block layout breaks this in 8 of 29
  musl files (backward jumps to return blocks; interleaved loops) although every compiled CFG
  is reducible. Proposal: a back edge is an edge u → h where h dominates u, and goes to an `inv`
  head; the CFG without back edges must be acyclic; a loop is h's natural loop; points are
  checked in a topological order of the acyclic graph; an `inv` on a label that heads no loop
  acts as a `join`. What Theorem C uses still holds: every cycle contains a back edge (the rest
  is acyclic), natural loops of a reducible graph are nested or disjoint, and a loop is entered
  only through its head (it dominates the body), so the outermost-loop argument goes through
  with "an edge into L's body from outside L" replaced by "an edge into the natural loop",
  which only the head receives. Lemmas 2–10 do not mention addresses.
  Implemented in the Rust checker as an opt-in (`--loops natural`, `Options::natural_loops`).
  With it, all 8 musl files move past `cfg` to an ordinary typing obligation (an `inv`
  constraint, a call's lent length, a missing measure, …) where V's annotations, written for
  S2, stop. Adopting it needs: T's agreement (the Lean checker uses S2), the proof's S2 and
  Theorem C text updated, and the export to carry the back-edge set instead of intervals.
- **I31 Syscall signatures follow Env.lean.** `read` and `write` return
  `int(r)` with `−4095 ≤ r ≤ −1 ∨ (0 ≤ r ≤ n ∧ r ≤ 0x7ffff000)`, and for `write` also
  `n ≥ 1 ⇒ r ≥ 1` in the success case: this is `Sys.writeOk`/`writeErr`/`readOk`/`readErr`
  read as a signature (E1), and it implies the note's weaker `−4095 ≤ r ≤ n, r ≤ 0x7ffff000`.
  Without `r ≥ 1`, a write loop cannot be shown to terminate (`write_all`, note-trial.md).
  The assumption is Env.lean's (docs/isa/environment.md lists it as a kernel assumption).
