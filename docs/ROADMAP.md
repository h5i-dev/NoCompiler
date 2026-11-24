# Roadmap

nocompiler restarted on 2026-11-23 around typed RISC-V assembly ([design note](Tab%201.md),
[soundness proof](健全性の証明.md)). This page is the order of work, not a schedule. What
exists today is in the README's status table. Implementation choices are recorded in
[typed/decisions.md](typed/decisions.md).

## Now: v0 end to end

Three streams run in parallel. They meet in a shared corpus, `tests/typed/corpus/`: typed
programs with their expected verdicts, which every checker must agree on.

**Lean (agent T)**
- Done:
  - the machine model with byte-wise permissions (decision 10);
  - the type language and ⟦σ⟧, total (`Typed/Lang.lean`, `Typed/Sem.lean`);
  - Presburger entailment with checked cutting-plane certificates (`Typed/Lin.lean`,
    `Typed/Presburger.lean`, untrusted search in `Typed/Search.lean`).
- Next: a checker written in Lean over the decoded image. It takes per-point state types
  from untrusted hints and applies the local typing rules, with ranking functions for
  termination.
- Then:
  - its soundness against ⟦σ⟧, which is lemmas 2–10 and theorems A–C of the soundness
    proof, mechanized;
  - theorem D (a whole program, given its unsafe and external contracts) with the ledger.
- After that, a checked function's guarantee is a kernel-checked `Meets` and the Rust
  checker is no longer trusted.

**Rust (agent U)**
- The checker in `crates/nocompiler-typed`:
  - a parser for the provisional syntax;
  - the typing rules;
  - quantifier-free Presburger decision;
  - ledger output.
- The note's examples (`sum`, stack buffer and call, `malloc`/`free` contracts) and one
  rejected case per rule.
- The export of parsed programs for the Lean checker ([typed/](typed/)).
- Restoring the machine model's oracle tests (decoding against llvm-mc, semantics against
  qemu and Sail) as `crates/nocompiler-rv`.
- Keeping the binary analysis toolkit and decompiler building and tested.

**Trial set (agent V)**
- musl 1.2.5 functions as compiled, with signatures and loop annotations added. No hand
  edits to the instructions.
- Verdicts predicted before annotating ([typed/musl-trial.md](typed/musl-trial.md)), then
  run through both checkers.
- Results recorded against the predictions, including failures.

## The tests the design has to pass

The note lists five outcomes that would send v0 back for redesign:
1. Most of the trial functions fall to unsafe.
2. Annotations cannot be written reliably.
3. Checking is too slow to use interactively.
4. A soundness hole cannot be fixed locally.
5. Contracts cannot be stated in the type language.

The musl trial is the first measurement for 1 and 5. Checking time (3) is measured once
the checkers run.

## After v0, in the order the trials ask for

From the note's "v0 に入れないものと、足す順". The order is decided by real examples. The cheap
ones come first, and unbounded pointer structures are the next big design step.

| Feature | Needs |
| --- | --- |
| Splitting and joining owned capabilities | `split` / `join` annotations with no instruction |
| Block-level unsafe | state types at the block's entry and exit |
| `partial` functions | the partial version of ⟦σ⟧ (a new judgment beside `Exec`) |
| Unbounded pointer structures: arrays of pointers, linked lists, trees | recursive types or quantified capabilities, with fold/unfold annotations |
| Recursive data types | the above |
| Recursion | `stack` as an index expression (decision 8 deferred it) |
| Function pointers | a change to the indirect-jump rule |
| Concurrency, floating point | an extension of the machine model |

Other work that waits for v0:
- Hand proofs that existing compiled code (for example musl's `memcpy`) meets an unsafe
  contract, as ledger entries of the "proved" kind.
- A rebuilt axiom audit over every declaration.
- Proving the semantics equal to Sail's generated Lean model.

The binary analysis toolkit has its own milestone record,
[toolkit/ROADMAP-toolkit.md](toolkit/ROADMAP-toolkit.md).
