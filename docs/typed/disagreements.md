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
| musl/strncmp, memccpy-x, stpncpy-x (stpncpy at c3f64fad) | accept | reject at I29 boolean ops / xor then andi (memccpy, stpncpy builds also `struct=false`) | Lean: I29 rules missing |
| musl/memset | accept | accept since 5a9707df, linked image (was: reject at `andi −4`, then at word 54) | resolved: the search eliminates through unit equalities (Omega test's equality step) |
| musl/memcpy | accept | accept since a41b63a3, linked image; within the limit since 460e1054 (precompiled modules: #eval 157 s → 7 s, module 63 s) | was: heartbeats (record as one literal, fixed by per-point defs 9e168d85), then the back edge and loop exit (conjunct-by-conjunct goals, case split with pinned facts) |
| musl/memcpy-x, memmove, memccpy, memccpy-ic; stpncpy | accept | verdicts within the limit since 9e168d85 (per-point defs); rejects in the arith rules, see U's rows | |
