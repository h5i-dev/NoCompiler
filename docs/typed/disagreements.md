# Disagreements between the Rust and the Lean checker

TWO-AGENTS.md: both checkers must agree on every corpus case (`tests/typed/corpus/`); a
disagreement is a bug in one of them or in the spec. Each entry: the case, each checker's
verdict, which one is wrong and why, and the fix (commit).


## musl trial, v0 (agent V, origin/typed c3f64fad, re-run at 998ae0df)

Run: `lean/scripts/corpus.py tests/typed/corpus/musl` (and `--why` on the Lean rejections). Every
disagreement is **Rust accepts, Lean rejects or gives no verdict**; there is none the other way.
So no soundness question arises, only Lean-side incompleteness (the Rust checker is trusted, I2).
Details and the full table: `docs/typed/musl-trial.md`, "v0 summary".

| case(s) | Rust | Lean | which side and why |
|---------|------|------|--------------------|
| musl/bcmp, bzero, strncpy, strnlen | accept | accept since 9e168d85 (was: reject at the `call`/`tail` pair's `auipc`) | resolved, the harness: `corpus.py --link` links each file with a `ret` stub for every callee it only declares, so the pair's `auipc` has the callee's real address and Lean checks the caller on the linked image |
| musl/ffsl | accept | accept since 9e168d85 (was: reject at the `%pcrel_lo` `addi`) | resolved, the export: the I30 `ro` capabilities were there; the constant pool `.LCPI0_0` has no symbol-table entry, so its address is now recovered from the linked `auipc`/`%pcrel_lo` pair |
| musl/l64a | accept | accept since 5a9707df, linked image (U's local data addresses 9e168d85; T's fold + case split on the invariant's table) | resolved |
| musl/memrchr, wmemcpy, wmemset | accept | accept since f4c553c7 (was: reject at the back edge) | resolved: Lean's instantiation applied θ to the source expression (double-shifted loop variables); `andi` mask now names its quotient |
| musl/memmove, stpncpy-x | accept | accept since 3ee59fd6, linked image (was: reject at xor then `andi 7`, stpncpy-x also `struct=false`) | resolved: loops exported in τ order (9e168d85); the record carries `2^k ∣ x ⇔ 2^k ∣ a − b` at each xor and Lean's mask rules give the zero test (3ee59fd6); T's search (5a9707df) |
| musl/strncmp | accept | accept since 2a00c908, linked image (was: reject at the I29 `and`, word 12) | resolved: bit table in the record's normal form, `coversS`, and `pinsBit` (a fact pinning the operand to 0/1 in every disjunct gives its range without search) |
| musl/memccpy-x | accept | reject at the loop's alignment exit `beq t0` (word 31, taken) | Lean: a divisibility chain through the addw, the mask and the entry's xor zero test; all facts in the record (search, T) |
| musl/memset | accept | accept since 5a9707df, linked image (was: reject at `andi −4`, then at word 54) | resolved: the search eliminates through unit equalities (Omega test's equality step) |
| musl/memcpy | accept | accept since a41b63a3, linked image; within the limit since 460e1054 (precompiled modules: #eval 157 s → 7 s, module 63 s) | was: heartbeats (record as one literal, fixed by per-point defs 9e168d85), then the back edge and loop exit (conjunct-by-conjunct goals, case split with pinned facts) |
| musl/memcpy-x, memmove, memccpy, memccpy-ic; stpncpy | accept | verdicts within the limit since 9e168d85 (per-point defs); rejects in the arith rules, see U's rows | |
