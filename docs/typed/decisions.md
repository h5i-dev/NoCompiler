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
