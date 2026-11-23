# musl trial: real compiler output against the typed-RISC-V rules

Agent V. Question: does the v0 type system (`docs/Tab 1.md`, decisions in
`docs/typed/decisions.md`) accept musl libc functions **as compiled** (no hand edits to the
instructions), given signatures and loop annotations only?

The note (section 「この設計が間違いだと分かる条件」, item 1) asks for the trial list to be fixed
before looking at results. This section was written and committed **before any of these
functions was compiled with the trial flags or annotated** — the predictions come from reading
the C source of musl 1.2.5 and the rule tables of the note only. They are not edited afterwards;
actual results go in the "Results" section below, next to the predictions.

## Material and flags (pinned)

- Source: musl 1.2.5 (MIT, see `examples/musl/COPYRIGHT`), unmodified.
- Compiler: clang 15.0.7, `--target=riscv64-linux-musl -march=rv64im_zba_zbb -mabi=lp64 -O2`.
  - `rv64im_zba_zbb`, no `c`: the machine model (`lean/NoCompiler/Isa.lean`) decodes RV64IM +
    Zba + Zbb and nothing else; no compressed, no `a` (the older libc-a build used `rv64ima`,
    and `a` is outside the model), no F/D.
  - `-mno-relax -mcmodel=medany -fno-pic`: no linker relaxation, so the bytes in the object
    are the bytes that run.
  - `-fno-jump-tables`: computed jumps are outside the profile (S1).
  - `-ffreestanding -fno-builtin -nostdinc -std=c99 -fno-stack-protector -fomit-frame-pointer
    -fno-unwind-tables -fno-asynchronous-unwind-tables -ffunction-sections`: musl's own
    freestanding flags; `-fno-builtin` keeps clang from turning loops into calls to memcpy/memset.
- Exactly what was run is in `scripts/musl-trial/build.sh`.

## Verdict vocabulary

- **accept**: a safe signature + annotations exist and the v0 rules accept the compiled code.
- **reject (v0 rules)**: a natural safe signature exists, but some v0 rule is too coarse for
  what the compiler emitted; the reason names the rule. This is a finding for v1, not an
  "unsafe" function.
- **unsafe contract**: the body cannot be safe in v0, but its contract is a v0 signature.
- **not expressible**: even the contract cannot be written as a v0 signature.

## Trial list and predictions (fixed 2026-11-23, before compiling)

| # | function | predicted | why (from the C source and the note's rules) |
|---|----------|-----------|-----------------------------------------------|
| 1 | `labs` | accept | no memory; `a>0 ? a : -a` is `blt`/`sub`. Baseline control. |
| 2 | `memcmp` | accept | `borrow l ↦ bytes[n] ro`, `borrow r ↦ bytes[n] ro`; one byte loop, `inv` with m = remaining n. |
| 3 | `bcmp` | accept | tail call `memcmp` (call + return rule), given memcmp's signature. |
| 4 | `memrchr` | accept | `while (n--) if (s[n]==c) …`; index loop, returns `int`. |
| 5 | `memchr` | accept | alignment head loop via `andi s,7` (c = 2^3−1 gives `s = x + 8j`), then aligned 8-byte loads with `n ≥ 8`; HASZERO arithmetic only produces `int`. Expect a join annotation after the head loop. |
| 6 | `strnlen` | accept | calls `memchr(s, 0, n)`, then `p ? p-s : n`. Signature borrows `s ↦ bytes[n] ro`: **stronger precondition than C** (C allows a shorter readable string if a NUL comes first). |
| 7 | `strncmp` | accept | reads only `l[i]`, `r[i]` for i < n; signature borrows both with length n: same strengthening as strnlen. |
| 8 | `swab` | accept | `ssize_t n`, signed loop `n > 1`; `where 0 ≤ n < 2^63`; byte loads/stores at +0/+1. |
| 9 | `bzero` | accept | tail call `memset(s, 0, n)`, given memset's signature (even if memset itself is rejected). |
| 10 | `memset` | reject (v0 rules) | `n &= -4` is `andi` with a negative constant (table only has c ≥ 0 → result unrelated to n), and `k = 24 + (s & 4)` is `andi` with a single-bit constant (only `0 ≤ x ≤ 4`, no link to s). The tail stores `s+n-4…` then cannot be bounded. |
| 11 | `memcpy` | reject (v0 rules) | tail `if (n&8)`, `if (n&4)`, … are `andi n, 2^k` + branch: the table gives `0 ≤ x ≤ 2^k` only, so `x ≠ 0` does not give `n ≥ 2^k` and the tail copies cannot be bounded. Also needs join annotations after the `switch (d%4)` cases. Signature itself fine (`restrict` ↔ rw/ro disjoint at entry). |
| 12 | `memccpy` | reject (v0 rules) | `(s & 7) == (d & 7)`: expect clang to fold this to `((s ^ d) & 7) == 0`; `xor` is not in the table, so the fact s ≡ d (mod 8) is lost and the aligned 8-byte store to d fails `8 ∣ a`. If clang keeps two `andi`, it would be accepted. |
| 13 | `memmove` | reject (v0 rules) | overlap is the point, so the signature is one region: `borrow ρ ↦ bytes[m] rw` with `a0: int(ρ+i)`, `a1: int(ρ+j)`, `i+n ≤ m`, `j+n ≤ m` (expressible). Calling memcpy borrows two disjoint sub-ranges of it (allowed, disjointness from the `s-d-n ≤ -2n` test, a mod-2^64 fact). Expected failure: alignment fact `s%8 == d%8` through `xor`, as in memccpy. |
| 14 | `strlen` | not expressible | precondition "a NUL exists in readable memory" is not a v0 signature (note, item 5). |
| 15 | `malloc` (mallocng) | unsafe contract | the note's malloc contract with `Heap` is a v0 signature; the body uses atomics (`lr/sc` inline asm) and `brk`/`mmap` syscalls outside the four. Expect it not to even compile under `rv64im` (no `a`) → "external" in the ledger. |
| 16 | `free` (mallocng) | unsafe contract | as malloc; note's `take p ↦ bytes[n] rw heap` contract. |
| 17 | `fwrite` | unsafe contract | calls through `f->write` (a function pointer, computed `jalr`, outside S1) and `__lockfile`. A contract with the FILE struct as a capability with fields and its buffer is writable in v0, but must be assumed. |

Predicted totals: 9 accept, 4 reject (v0 rules), 3 unsafe contract, 1 not expressible.
Predicted v1 asks: `andi` with single-bit and negative (low-bit-clearing) constants, `xor` modulo
2^k for alignment tests.

## Results

(Not yet: filled in as annotations are written and when a checker exists. Each row gets
"actual" next to "predicted"; a wrong prediction stays visible.)
