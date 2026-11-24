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
  **Partial meaning added (2026-11-23, U, at T's hand-over):** `Typed.MeetsP` (Typed/SemPartial.lean):
  `VerifiedImgP`, every prefix of every run is safe and stops only where the exit conditions
  hold (step-indexed `ReachP`); a total proof is a partial one (`Meets.toP`). `Sig.isPartial`
  (Lang.lean); a partial signature's back edges need no measure (edgeOk); a non-partial function
  calls no partial one (structOk); `Fn.check_soundP` gives `MeetsP`, `Fn.check_sound` needs
  `partial = false`, and theorem D's `Prog.check` admits only non-partial functions for now. The
  run is proved once over a `Runner` (Sound/Runner.lean): `Reach` with the rank for total runs,
  `ReachP` with fuel for partial ones.

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
  (it is never taken). Sound: no state satisfies the edge's type. Asked as `Ψ ⊢ ¬cond` (so
  the relevance filter applies) with a smaller solver budget: an unanswered query only keeps
  the edge, which costs precision, not soundness.
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
- **I33 Findings of an independent soundness review (2026-11-23), fixed.** Regression cases in
  `tests/typed/corpus/review/`.
  1. *Fields of a lent sub-range.* The call rule checked that a clause's fields exist in the
     held capability with equal values, but not that they lie inside the **lent** length; the
     callee then assumed `k + 8 ≤ n` (D2) and could write outside everything the caller
     held. Now every field the clause names, on entry or exit, needs `Ψ ⊢ k + 8 ≤ θn`.
     **For T:** the proof's Lemma 8 P4 has the same gap ("フィールドは、検査が求める一致と I4
     から" — I4 only covers the held capability's offsets); the check above closes it.
     **T (2026-11-23):** agreed; the Lean call rule has the same check (`Fn.fieldsLent`: each
     clause field is a field of the held capability at the same address with an entailed-equal
     type, and `k + 8 ≤ θn`), and there the proof cannot skip it: the callee's entry condition
     is `Field.holds`, which contains `k + 8 ≤ n`. 健全性の証明 Lemma 8 P4 should cite the check
     rather than I4 (to fix in the proof text with the other call updates).
  2. *`in ra`.* A contract could require `ra` on entry; the call rule compared it before
     `jal` overwrites it. `in` and `out` may not type `zero`, `ra`, `sp` in any signature.
  3. *Directives.* `.pushsection`, `.org`, `.uleb128`, … were ignored; now any directive
     outside a known list is an error. `.p2align`'s fill byte is used in data and refused in
     code; a maximum skip is refused; `.fill` is implemented; `.ascii "a", "b"` is a list.
  4. *Section flags* decide read-only-ness when given (`.rodata` with `"aw"` is writable).
  5. *Mergeable sections.* The linker deduplicates `M` sections piece by piece: a symbol in
     one is usable only if it is exactly one entry-size piece; in `MS` (strings) never.
  **S5 sees one file**: two files that each check (`f: tail g` with `g` declared, and
  `g: tail f`) together recurse forever. Closed by I34.
- **I34 Whole program (`nocompiler-typed link A.s B.s …`).** Theorem D for a program made of
  several files: every safe function declared (signature without body) in one file must be
  defined in exactly one file with the identical signature (as parsed); unsafe/extern
  declarations stay contracts; S5 is checked on the call graph of all files together. A
  program is safe when every file checks and `link` reports no error.
- **I35 More arithmetic** (asked by the musl trial; facts about the operations): the fresh
  result x of `xor a, b` also gets `x = 0 ⇔ 2^64 ∣ a − b` (so `snez` of it is `a ≠ b`);
  `srliw rd, rs, c` and `srlw` by a constant c (mod 32) ≥ 1 give `zext32(e) = 2^c·x + r`,
  `0 ≤ r < 2^c` (the shifted low word is below 2^31, so its sign extension is itself).
  Under P1 an `inv` on a label that heads no loop needs no measure (it is a `join`).
- **I36 P1 adopted (user decision 2026-11-23): natural loops are the default**, in T's τ form.
  The checker computes back edges (to a dominating label), requires the CFG without them to be
  acyclic, takes each head's natural loop, and builds τ per region of the loop-nesting forest
  (inner loops collapsed to their head, topological order with address order among ready
  points, inner loops expanded in place). It then checks the τ conditions itself — every edge
  but a back edge goes up in τ, every loop is a τ-interval, no edge enters an interval except
  at its head — and checks the points in τ order. τ is in the export (export.md). The old
  address-interval rule stays as `--loops interval`; corpus files keep its verdicts in
  `#! expect-interval` lines where they differ. An `inv` on a label that heads no loop is a
  `join`. T updates the proof's S2/Theorem C and the design note.
- **I37 Witness-free facts in the record.** Every fact the Rust checker records mentions only
  variables that some register, slot or field of the state (or the signature, or an
  annotation) also mentions, wherever the rule allows: `u(e) = x` is `2^64 ∣ e − x` (not
  `e = x + 2^64·k`), the 32-bit rule `2^32 ∣ e − x`, a quotient result `0 ≤ e − c·q < c`, a
  remainder result `c ∣ e − r, 0 ≤ r < c`. Equivalent to the earlier forms (the solver
  introduces the quotient itself), and it lets the Lean checker instantiate every variable of
  the next point's type on an edge (its θ is found from registers). Exception left: the
  single-bit `andi` rule still has a fact-only quotient.

- **I38 The `heap` mark (T, 2026-11-23).** In the Lean ⟦σ⟧ the mark `heap` has no meaning
  (Sem.lean does not mention it), so the assumption U1 for `free` (`take p ↦ bytes[n] rw heap`)
  promises that `free` accepts any byte range, which a real allocator does not. Two parts:
  (1) the call rule now lends a `heap` clause only from a held `heap` capability with the same
  base and length (the note's "free が受け取れるのはこの印が付いた全体だけ"); sound, as it only
  rejects more. (2) Open, for the user: give `heap` a meaning in ⟦σ⟧, e.g. "the range is an
  allocation unit of the `Heap` token's invariant" (the token definition would expose its set of
  live units), so that an unsafe allocator's U1 is a true statement. Until then a `heap` clause in
  an unsafe signature is a promise of the ledger's assumption only.
  **Part 2 adopted (user decision 2026-11-23), design (T):**
  * `TokDef.unit : List Region → Region → Prop`, the live allocation units, a function of the
    token's footprint only. The allocator's token is the one named `Heap`.
  * A `heap` byte capability is valid only if its range is a unit of `Heap` (under its guard).
  * Post gains Q5, the unit frame: every unit of `Heap` at entry that misses the Pool and the
    function's stack region is still a unit at exit. So a true allocator contract reads: `malloc`
    gives a fresh unit (it lies in the Pool, the borrowed `Heap`), `free` takes a whole live unit
    (its take clause is valid at entry), and units of others survive both.
  * Caller side: a held heap block not lent to the callee misses the callee's Pool (`Inv.sep`
    with the lent take capabilities and tokens), so the callee's Q5 keeps it valid.
  * Own Q5, by induction over the run, with the token footprint relative to the entry. Two
    call-rule conditions make it go through: a `take` clause is never lent from a capability that
    came from one of the function's own borrows, and every borrow of the function is still held
    at a call. The invariant gains "the capability of borrow i covers borrow i's entry range".

## Proposals (not adopted: the default checker does not use them)

- **P1 Natural loops instead of address intervals** (adopted as I36, 2026-11-23, user; docs/Tab 1.md decision 11, docs/健全性の証明.md S2 and Theorem C) (from the musl trial, docs/typed/musl-trial.md
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
  With it, all 8 musl files move past `cfg` to an ordinary typing obligation. With V's
  annotations as of 2026-11-23 18:50 UTC, of the 38 files of `tests/typed/corpus/musl`
  (functions + variants) the default rules accept 19 and P1 accepts 25 (`memcpy`, `memmove`,
  `__stpncpy` and the `-x` variants of `memcpy`, `memccpy`, `stpncpy`); every function P1
  accepts also passes tests/exec.rs (300 random runs each, no fault). Adopting it needs: T's agreement (the Lean checker uses S2), the proof's S2 and
  Theorem C text updated, and the export to carry the back-edge set instead of intervals.
- **T on P1 (2026-11-23): agree, with one amendment.** The Lean checker's termination proof
  (`lean/NoCompiler/Typed/Sound/Rank.lean`) needs loops to be intervals of *some* order in
  which every edge other than a back edge goes up, not necessarily the address order. So:
  the record carries an order τ of the function's points (a permutation of the word
  indices); the checker checks S2 with τ in place of addresses (forward edges increase τ,
  each back edge goes to an `inv` head from inside the head's τ-interval, the intervals
  nest, and no edge enters an interval except at its head). For a reducible CFG an order
  in which every natural loop is contiguous always exists (e.g. a reverse postorder that
  finishes a loop's body before leaving it); the Rust checker can emit it. The proof's S2 and
  Theorem C then hold with τ for addresses, and nothing else changes. Until the export carries
  τ, the Lean checker keeps addresses (τ = identity).
- **T on I30 (2026-11-23): no change to ⟦σ⟧ needed.** An implicit read-only data capability
  is a `borrow ℓ_sym ↦ bytes[size] ro {fields}` clause with `ℓ_sym` a parameter and
  `align ∣ ℓ_sym` in the entry constraint: P4/P5 then say exactly "readable, holds its bytes,
  disjoint from every `rw` capability and token". The export should list them as ordinary
  borrow clauses of each function's signature (the call rule lends them `ro`, which may
  overlap). Program level (Theorem D): `_start`'s caller is the loader, which must establish
  them (the image's data loaded, the permission including it).
- **I31 Syscall signatures follow Env.lean.** `read` and `write` return
  `int(r)` with `−4095 ≤ r ≤ −1 ∨ (0 ≤ r ≤ n ∧ r ≤ 0x7ffff000)`, and for `write` also
  `n ≥ 1 ⇒ r ≥ 1` in the success case: this is `Sys.writeOk`/`writeErr`/`readOk`/`readErr`
  read as a signature (E1), and it implies the note's weaker `−4095 ≤ r ≤ n, r ≤ 0x7ffff000`.
  Without `r ≥ 1`, a write loop cannot be shown to terminate (`write_all`, note-trial.md).
  The assumption is Env.lean's (docs/isa/environment.md lists it as a kernel assumption).

The following come from the v0 rejections in the trials (note-trial.md, musl-trial.md). Each
is a design proposal only: nothing is implemented, and the user decides. Each would be a
general extension of the type language or the profile; none is a rule for a particular
function.

- **P2 Per-byte content facts at joins** (musl `memchr`, `memchr-x`). clang joins the head
  loop's "byte found" exit (`p` unaligned) with its aligned exits, re-reads `b[p]`, and enters
  the word loop only if it is not the target. `8 ∣ p` there holds only because "`p` unaligned ⇒
  `b[p] = c`": a fact about memory contents at a symbolic offset, carried across a join.
  v0 has fields only for 8-byte words at constant offsets, and decision 2 drops path
  conditions at joins. Options: (a) *indexed fields* `{[e]: u8(x)}` — a byte at offset `e`, an
  index expression, with the same invalidation rules as fields (a store that may overlap drops
  it); a `join where` could then state `8 ∣ p ∨ b[p − b] = c` with `[p − b]` named;
  (b) fields of width 1/2/4 at constant offsets only (cheaper; does not cover memchr). Cost:
  (a) adds a memory-content sort to Ψ and makes field invalidation a query per store.
- **P3 NUL-terminated strings** (musl `strlen`, and `a64l` through `strchr`'s missing
  contract). "There is a NUL inside readable memory" is not a v0 signature (note item 5). A
  *string capability* `s ↦ str[n] ro` would mean `s ↦ bytes[n + 1] ro`, the byte at `n` is 0
  and none before it is: then `strlen [s, n] in a0: int(s) borrow s ↦ str[n] ro out a0: int(n)`
  is expressible and its body checkable (the loop reads `b[i]` for `i ≤ n`; reading 0 at `i`
  gives `i = n`). It needs: the per-byte "is not 0 before n" fact (an indexed fact as in P2,
  quantified over `i < n`, i.e. the first quantified fact in v0) and a way to create such
  capabilities (string literals in `.rodata`, whose bytes are known; or a check loop that
  establishes it). Alternative without quantifiers: keep strings as pointer + length in safe
  code (`strnlen` form, as the note suggests) and give `strlen`/`strchr` only unsafe contracts
  with a length bound — which is what v0 already allows.
- **P4 Function pointers** (musl `bsearch`'s comparator, `__fwritex`'s `f->write`). Calls
  through a register are outside the profile (S1). A value type `fn σ` — "the word is the
  entry of a function meeting σ" — would let `jalr ra, 0(rs)` be typed as a call of σ when
  `rs : fn σ`. Values of the type come from `auipc`/`addi` of a function symbol whose
  signature is σ, from signature `in` clauses, and from fields typed `fn σ` (`f->write`).
  Needs: the profile to admit `jalr ra, 0(rs)` (a change to S1 and to T's Lean model, where the
  jump target must be shown to be such an entry), and Theorem D's induction to range over the
  functions whose address is taken (S5 with indirect edges: a conservative call graph that
  links every `fn σ` call to every function of signature σ).
- **P5 Products of two variables** (musl `fwrite`: `__fwritex` is lent `size·nmemb` bytes).
  `mul` of two non-constant values gives `int` today, and lengths must be linear. Proposal:
  *product terms* — `mul rd, a, b` gives `int(a ⋆ b)` where `a ⋆ b` is an uninterpreted atom
  (a fresh variable remembered with its two factors), with the facts the representatives allow
  (`0 ≤ u(a)·u(b)` is not linear, so only sign facts and `mulhu = 0 ⇒ a ⋆ b < 2^64`), matched
  syntactically against a callee's `bytes[size ⋆ nmemb]`. Signatures could then state
  `borrow b ↦ bytes[size ⋆ nmemb] ro`. Cost: Ψ stays linear (the atom is a variable); the
  matching rule must keep atoms identical across the call.
- **P6 Writable static data in signatures beyond `_start`** is in (I32); no proposal.
- **P8 Splitting and joining a held capability** (T, 2026-11-24; the design note's "足す順" lists it
  as the cheapest v1 addition; needs the user's choice). Annotations without instructions:
  `split κ at k` turns a held `b ↦ bytes[n] m` into `b ↦ bytes[k] m` and `b+k ↦ bytes[n−k] m`
  (fields go to the part they lie in), and `join κ1 κ2` turns two held adjacent capabilities of
  the same mode back into one. Uses: lending one half of a buffer `rw` and keeping the other, or
  giving back part of a taken block. Lean side: the edge rule's subtyping already lets a target
  capability shrink only to an equal range, so split/join become part of `sub`: a target capability
  may be covered by one source capability (split: several targets from one source, pairwise
  provably disjoint when exclusive) or a `join` target by two adjacent sources (both exclusive or
  both `ro`, with the same guard). Soundness: footprints only move between capabilities the
  function already held, so `Inv.perm`, `Inv.stack` and the Pool argument carry over; separation
  needs the pairwise disjointness of split parts, which the rule asks for. `heap` capabilities
  are not split or joined (an allocation unit stays whole, I38). Cost: the record names the split
  points (untrusted hints); Rust: the two annotations.
- **P7 The ledger across files: canonical signatures** (U, 2026-11-24; needs the user's choice).
  `--prove` proves theorem D for one file's functions on the linked image. For a program whose
  functions are in several files (`link`), the caller's copy of a callee's signature must be
  `=` to the callee's own (`Prog.callsOk`), and today it is not: each file's export numbers
  variables in its own name table, and adds every data symbol of its own file to every
  signature (I30's implicit `borrow ℓ_sym` clauses). Proposal: (1) export each signature in a
  canonical form, its parameters numbered 0.. in order, then its `out` variables, then the
  rest of the function's variables (the record renumbered consistently); (2) a signature lists
  only the data symbols it uses (its own clauses' and, transitively, its callees'), named by
  symbol, not by file-local variable; (3) `link --prove` writes one Lean module for the linked
  image with every file's functions and proves `Prog.check code [] prog` over all of them.
  Cost: export-side only (untrusted); the Lean checker re-checks everything as now. Without it
  the ledger says `proved` only within a file whose callees are all in the same file.
  **T (2026-11-24), Lean side:** no Lean change needed. `Prog.callsOk` keeps comparing
  signatures by `=` (the trusted check stays syntactic and simple); canonical numbering and
  per-signature data symbols are the export's job, which is untrusted. Data symbols that a
  signature uses as parameters fixed by `ℓ_sym = address` in `pre` are already instantiated at
  calls (`Fn.pinned`), so (2) works with the Lean call rule as it is.
