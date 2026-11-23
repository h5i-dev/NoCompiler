# The Lean checker

`lean/NoCompiler/Typed/Check.lean` is the type checker for safe functions, written in Lean
and run on the **decoded code image** (`Code`, the `.text` words of the binary).
`lean/NoCompiler/Typed/Sound/` proves it sound:

```lean
theorem NoCompiler.Typed.Fn.check_sound (f : Fn) (c : Code) (T : TokEnv)
    (h : f.check c = true) : Meets c [(f.entry, 4 * f.size)] f.entry T f.sig
```

`Meets` is ⟦σ⟧, total (`lean/NoCompiler/Typed/Sem.lean`): from every entry satisfying the
signature, every run stays in the function, faults never, accesses only the signature's
capabilities and its stack (byte by byte, decision 10), terminates, and returns with sp,
gp, tp, s0–s11 and ra as on entry, the `out` registers and exit constraint, and the borrowed
capabilities back with their exit fields. Axioms: `propext`, `Classical.choice`,
`Quot.sound` only. `VerifiedImg.hw` (Adequacy.lean) carries this to the machine (`HwStep`)
when the image is loaded and the writable memory does not overlap the code.

## What is trusted, what is not

- Trusted (read to believe the theorem): the machine model and `Step`, `Spec`/`VerifiedImg`,
  `Typed/Lang.lean`, `Typed/Sem.lean`. Nothing else.
- Not trusted: everything the checker is given besides the image. `Fn` carries the
  signature (the claim), the loops with their measures and the **record of state types per
  instruction** (D8). The record is a hint: a wrong one makes the check fail, never makes
  a false theorem. The Presburger entailments are decided by an untrusted search whose
  cutting-plane certificates are checked (`Query.check_sound`).
- The proof follows docs/健全性の証明.md: Lemma 2 (`Fn.arith_sound`), 3 (`Fn.branch_sound`),
  4 (`Inv.sub`), 5 (`Fn.load_sound`), 6 (`Fn.store_sound`), 10 (`Fn.retOk_sound`), entry T0
  (`Fn.entry_inv`), Theorems A–C together in `Fn.run`. Termination uses a ranking function
  (`Sound/Rank.lean`: one lexicographic component per loop, by increasing head) instead of
  the proof's outermost-loop argument.

## Scope (milestone 1), stated as what the checker rejects

Calls (`jal ra`), frames (`sp` writes), `ecall`, tokens, `take`/`give`, `partial`, static
data: a function using any of them is rejected (`Fn.structOk`, `Fn.instrAt`). The code
region `D` of the theorem is the function's own instructions. These are the next steps,
in that order (calls and frames are what the note's `read_sum` needs).

## Example

`lean/TypedTests/Sum.lean` (outside the core library): the note's `sum`, assembled by
clang, with a hand-written record; `sum_meets` is `Meets` for it, from `check_sound` and a
kernel `decide` of `fn.check code = true` (about 15 s). Six broken variants are rejected.
Performance on larger functions is not measured; kernel evaluation of the checker may need
the certificates and instantiations to be supplied in the record (docs/typed/export.md)
instead of searched.
