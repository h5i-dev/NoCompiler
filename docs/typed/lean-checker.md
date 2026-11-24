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
(`lean/TypedTests/ArithExt.lean`). Xor then mask: the Rust checker's xor rule writes `2^k ∣ x ⇔ 2^k ∣ a − b` into the record for each mask width `2^k − 1` among the function's `andi` immediates and `li` constants, so the fact survives to the mask's point. There a mask `x = y mod 2^k` of a `y` with such a fact gets the zero test `x = 0 ⇔ 2^k ∣ a − b` (`Fn.xorBitOf`, `Fn.xorZeroFact`) directly, without the solver. The fast path of `STy.ent` compares facts up to linear normal form through `∧`, `∨` and `¬` (`STy.coversS`), so the Rust record's compound facts are found as they are. Tokens are covered: a function may borrow tokens (unguarded), returns them at depth 0 (their footprint lies in the Pool), and lends a held token to a callee whose clause names it (the name held by one capability only); after the call the token's footprint is the callee's (`callF`); a callee may also give tokens, whose name no other held capability may carry (`Fn.tokHeldOk`), and the proof's run is over the changing footprints (`Fn.run` quantifies over them). `partial` functions (I19): no measure on back edges, a non-partial function calls no partial one, and `Fn.check_soundP` gives the partial meaning `MeetsP` (Typed/SemPartial.lean); theorem D (`Prog.check`) admits non-partial functions only. The `heap` mark has a meaning (decisions.md I38): a `heap` capability is a live unit of the `Heap` token (`TokDef.unit`), and Post's Q5 keeps every unit that misses the Pool and the stack. A call lends a `heap` clause only from a whole held heap unit, never lends a `take` clause from one of the function's own borrows, and needs every borrow still held (`Fn.callHeldOk`); the caller's other heap blocks survive by the callee's Q5, and the function's own Q5 follows by induction over the run (`Fn.UnitFrame`, `Fn.unitFrame_call`).

## Example

`lean/TypedTests/Sum.lean` (outside the core library): the note's `sum`, assembled by
clang, with a hand-written record; `sum_meets` is `Meets` for it, from `check_sound` and a
kernel `decide` of `fn.check code = true` (about 15 s). Six broken variants are rejected.
Kernel cost (2026-11-24, the linked `note-trial/sum.s`): an entailment whose goal is already
a fact of the type skips the search (`STy.ent`), and `capSub` skips the guard entailment for
two unguarded capabilities; the whole ledger module (three functions, theorem D, `#print
axioms`) went from 185 s / 7.7 GB to 33 s / 2.2 GB. Certificates in the record were not
needed for this.

Instantiation (untrusted, `sub` re-checks it): `solveFrom` solves a target register's
expression `c + a·y + rest` against the source's expression `e` as `a·y = e − θ rest`; `θ`
applies to `rest` only, because at a backward edge a loop variable is a variable of both
types. The `andi` mask rule names the quotient (`e = 2^k·q + x`, next to `2^k ∣ e − x`), so a
target type that names it matches through the equations.

Entailment (`STy.ent`, 2026-11-24), in order, each sound by its own lemma (Sound/Inv.lean):
1. the goal is a fact of the type, as it is or up to linear normal form (`covers`, U's
   `coversS` through ∧/∨/¬);
2. the goal with its constant atoms folded (`Constr.fold`: `0 = 0` is `tt`, `0 = 1` is `ff`,
   ∧/∨/¬ fold with them) goes to the decision procedure conjunct by conjunct (the negation
   of a conjunction doubles every branch of the normal form);
3. by cases (`entCaseN`, one level): a fact relevant to the goal that is a disjunction whose
   every disjunct pins variables to constants (an invariant's case table
   `k = 0 ∨ (k = 1 ∧ …) ∨ …`, a bit table's rows) is split; in each case the constants go
   into the goal and into the facts, which fold (a table over pinned variables collapses to
   its row), and each conjunct is queried as `c ∨ ¬d`, which keeps the disjunct's variables
   so an impossible case (goal `ff`) is refuted from the relevant hypotheses.
The search (untrusted) eliminates a variable exactly through an equality with a unit
coefficient before pairwise Fourier–Motzkin (the Omega test's equality step), and retries a
branch with a larger budget when the small one fails.

Running the checker (2026-11-24): the NoCompiler lib is built with `precompileModules`, and
the corpus harness runs each generated module with `lake lean` (which loads the native
libraries), so `#eval fn.check code` runs compiled code: on musl memcpy (linked image) 7 s
instead of 157 s in the interpreter. Proofs are unaffected: the kernel never runs native
code, and nothing uses `native_decide`.
