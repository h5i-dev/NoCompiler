# The Lean checker

`lean/NoCompiler/Typed/Check.lean` is the type checker for safe functions, written in Lean
and run on the **decoded code image** (`Code`, the `.text` words of the binary).
`lean/NoCompiler/Typed/Sound/` proves it sound:

```lean
theorem NoCompiler.Typed.Fn.check_sound (f : Fn) (c : Code) (T : TokEnv) (h : f.check c = true)
    {D : Dom} (hDf : ∀ k < f.size, D.mem (f.pcOf k))
    (hcall : ∀ p ∈ f.callees, aligned p.1 4 ∧ ∃ Dg, Meets c Dg p.1 T p.2 ∧ Dg.sub D ∧
      ∀ j < f.size, ¬ Dg.mem (f.pcOf j)) :
    Meets c D f.entry T f.sig
```

`D` holds the function's code and its callees' domains; each callee (entry address and
signature in `f.callees`) meets its signature on its own domain, away from `f`'s code.
Without calls this is `Fn.check_sound_leaf`: `Meets c [(f.entry, 4 * f.size)] f.entry T f.sig`.

**Theorem D** (`lean/NoCompiler/Typed/Prog.lean`, `Sound/Prog.lean`): `Prog.check c E fs`
checks the functions `fs` in order, each one's callees earlier in `fs` or in `E`, the
external functions with their signature and domain (assumed or proved by hand: `U1`).
`Prog.check_sound`: if everything in `E` meets its signature, so does every function in
`fs`, on the domain `Fn.domIn` (its code plus its callees' domains). The order is S5 (no
recursion).

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
  4 (`Inv.sub`), 5 (`Fn.load_sound`), 6 (`Fn.store_sound`), 7 (`Sound/Frame.lean`),
  8 (`Sound/Call.lean`: `Fn.callee_pre`, `Fn.afterCall_inv`, `Fn.callAt_step` over
  `VerifiedImg.call`), 10 (`Fn.retOk_sound`), tail calls (`Fn.tail_step`), entry T0
  (`Fn.entry_inv`), Theorems A–C together in `Fn.run`. Termination uses a ranking function
  (`Sound/Rank.lean`: one lexicographic component per loop, by increasing head) instead of
  the proof's outermost-loop argument.

## Scope, stated as what the checker rejects

Frames are covered (Lemma 7, `Sound/Frame.lean`): the prologue `addi sp, sp, -F`, the
address-taken ranges as `rw` capabilities, 8-byte save slots, the epilogue; see
`lean/TypedTests/Frame.lean`. Calls are covered (Lemma 8): `jal ra, f` and clang's
`call f` = `auipc t, hi` + `jalr ra, lo(t)` (I21; `auipc` gets its exact value, since the
checked image fixes the address of each instruction), and `tail f` = `auipc t1` +
`jalr zero, lo(t1)` at depth 0 with `ra` the entry's. The callee's `borrow` and `take` clauses are
lent from held capabilities; the fields of capabilities lent `rw` are forgotten after the call;
a capability a `take` clause was lent from (it must be exclusive) is gone after the call, and
the callee's `give` capabilities (bytes, no fields) are added. In a function's own signature,
`take` capabilities are held from the entry and each `give` must be covered at the return (depth
0) by a distinct held exclusive capability not returned for a borrow; the Pool condition follows
from the invariant (such a capability lies in the entry permission, misses the stack and the
returned borrows). Syscalls are covered (Lemma 9, `Typed/Ecall.lean`, `Sound/Ecall.lean`):
`a7` a known constant; `exit`/`exit_group` end the run; `write`/`read` of `[b, b + n)` need a
held capability covering it (`rw` for `read`), then `a0` is a fresh value with Env.lean's
relation (I31) and `read` drops the fields of the capability it wrote into; any other number is
rejected (`lean/TypedTests/Ecall.lean`). Static data
(I30/I32) needs no rule of its own on the linked image: `auipc` gives the exact address, a data
symbol is a `borrow ℓ_sym ↦ bytes[n]` clause with `ℓ_sym = address` in the entry constraint
(the export's `--image`, export.md "Linked image"; `lean/TypedTests/Static.lean`), and
at a call such a parameter is instantiated from that equation (`Fn.pinned`). Callee clauses may
carry fields: each must be a field of the held capability at the same address with an equal
type, inside the lent length (`Fn.fieldsLent`, I33.1). The arithmetic beyond `arith`
(`Typed/ArithExt.lean`, `Sound/ArithExt.lean`: comparisons, min/max, the `.uw` forms, division
and remainder by constants and by positive divisors, shifts, masks, single bits, disjoint
`or`/`xor`, 0/1 bit tables, bit counts) follows decisions.md I23/I29/I35, as the Rust checker
(`lean/TypedTests/ArithExt.lean`). Tokens are covered: a function may borrow tokens (unguarded), returns them at depth 0 (their footprint lies in the Pool), and lends a held token to a callee whose clause names it (the name held by one capability only); after the call the token's footprint is the callee's (`callF`); a callee may also give tokens, whose name no other held capability may carry (`Fn.tokHeldOk`), and the proof's run is over the changing footprints (`Fn.run` quantifies over them). `partial` functions (I19): no measure on back edges, a non-partial function calls no partial one, and `Fn.check_soundP` gives the partial meaning `MeetsP` (Typed/SemPartial.lean); theorem D (`Prog.check`) admits non-partial functions only.

## Example

`lean/TypedTests/Sum.lean` (outside the core library): the note's `sum`, assembled by
clang, with a hand-written record; `sum_meets` is `Meets` for it, from `check_sound` and a
kernel `decide` of `fn.check code = true` (about 15 s). Six broken variants are rejected.
Performance on larger functions is not measured; kernel evaluation of the checker may need
the certificates and instantiations to be supplied in the record (docs/typed/export.md)
instead of searched.
