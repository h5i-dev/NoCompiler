# The note's own trial functions (agent U)

The note ("この設計が間違いだと分かる条件", item 1) names `sum`, `cobs_decode`, `write_all` and
musl's `mem*`/`str*` as the functions to try. musl is agent V's trial (docs/typed/musl-trial.md).
This file covers the other three, plus `hello` (the caller of `write_all` in the same source),
compiled as-is from the repository's own C sources of bcb19fed (`examples/sum.c`,
`examples/demo/src/cobs.c`, `examples/hello.c`), with V's pinned flags (musl-trial.md).

## Predictions (fixed 2026-11-23, before compiling)

Written from the C sources and the rules only. Not edited afterwards; results go below.

| function | predicted | why |
| --- | --- | --- |
| `sum` | accept | the note's own example; one `inv`, no extra instructions. |
| `cobs_decode` | accept, at risk | `r ↦ bytes[24] rw` and `buf ↦ bytes[len] rw`; three loops with measures `len − n`, `n − src`, `end − src`; needs `dst ≤ src ≤ n ≤ len` in the invariants. Risks: `n < len && buf[n] != 0` compiled branch-free (as V saw in strncmp), and block layout against S2. |
| `write_all` | reject `loop-decreases` with the note's `write` signature; accept if the signature says a `write` of n ≥ 1 bytes returns r ≥ 1 or an error | the loop decreases `n` by r; the note's signature allows r = 0. `Env.lean` (environment.md) assumes "r ≥ 1 when n ≥ 1". |
| `hello` | accept | reads `msg` from .rodata (I30), calls `write_all`, exits with 93. |
