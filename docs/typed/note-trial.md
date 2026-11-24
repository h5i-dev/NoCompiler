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

## Results (Rust checker, trusted, I2; 2026-11-23)

Built by `scripts/typed-trial/build.sh` (V's pinned flags but `-std=gnu99`: the sources use
inline `asm` for `ecall`), annotated by `scripts/typed-trial/annotate.sh` from
`examples/typed/ann/*.ann` (instructions unchanged; `check.sh` checks every file with
`--object` against the object compiled from C, I15). Corpus copies in
`tests/typed/corpus/note-trial/`.

| function | predicted | S2 (default) | P1 (`--loops natural`) | notes |
| --- | --- | --- | --- | --- |
| `sum` | accept | **accept** | accept | one `inv`, as the note said |
| `sum2` (not in the list; same source) | — | **accept** | accept | two `call` pairs (I21), frame with 4 slots |
| `_start` (not in the list) | — | reject `static-data` | same | writes through writable `data` (I30) |
| `cobs_decode` | accept, at risk | **reject `cfg`** | **accept** (73 queries, 18 ms) | clang enters the outer loop in the middle of its address interval (`j .LBB0_8` past `.LBB0_7`): the S2 risk. `code != 0xff && src < n` is branch-free (`snez`/`sltu`/`and`), handled by I29. 7 annotations (3 `inv`, 3 `join`, signature). |
| `write_all` | reject `loop-decreases` (note's `write`) | **reject `loop-decreases`** | same | as predicted: the note's `write` signature allows `r = 0` for `n ≥ 1` |
| `hello` | accept | **accept** | accept | `msg` from `.rodata` (I30), call of `write_all`, `exit` |

Predictions: 3 of 4 as predicted outright; `cobs_decode` was predicted "accept, at risk" and
the named risk (S2 block layout) is what rejects it with the default rules.
`tests/exec.rs` runs every function accepted in either mode (incl. `cobs_decode`) 300 times
from random signature-satisfying states: no fault.

### After I31 (syscall signatures as Env.lean states them)

With `write`'s signature as `Env.lean`'s relation (`n ≥ 1 ⇒ r ≥ 1` on success, decision I31),
`write_all` is **accepted** (default rules). This is the second half of its prediction. The
change only strengthens what the checker may assume after a `write`, to exactly the trusted
environment model; the other results are unchanged.

### Running them

`check.sh` links the objects (`ld.lld -static -e _start`) and runs them under
qemu-riscv64: `hello` prints `nocompiler` and exits 0 (through `write_all` and `exit`); `sum`'s
`_start` exits 24 = (1+2+3+4+5) + (2+3+4), through `sum2` and `sum`. A sanity check of the
compiled code, not part of any guarantee.

### After I32 (writable data through signatures)

`_start` (sum.c) with `borrow @data ↦ bytes[40] rw` in its signature is **accepted**.

### After I36 (natural loops the default)

`cobs_decode` is **accepted** with the default rules (it was rejected by the address-interval
rule, still available as `--loops interval`, which the corpus copy keeps as `#! expect-interval`).
All six functions of the trial are now accepted as compiled.
