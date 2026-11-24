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
| musl/bcmp, bzero, strncpy, strnlen | accept | reject at the `call`/`tail` pair's `auipc` | Lean (or the harness: code at address 0, `R_RISCV_CALL` unresolved) |
| musl/ffsl, l64a | accept | reject at the `%pcrel_lo` `addi` | Lean: the export lacks I30's implicit `ro` capabilities (T's open item) |
| musl/memrchr, wmemcpy, wmemset | accept | reject at the back edge | Lean: `inv` re-establishment on these loops |
| musl/strncmp, memccpy-x, stpncpy-x (stpncpy at c3f64fad) | accept | reject at I29 boolean ops / xor then andi (memccpy, stpncpy builds also `struct=false`) | Lean: I29 rules missing |
| musl/memset | accept | reject at `andi −4` | Lean: `andi` with −2^k (I23) |
| musl/memcpy, memcpy-x, memmove, memccpy, memccpy-ic; stpncpy | accept | no verdict (heartbeats; 180 s, load-dependent) | resource limit in the harness |
